import Numlib.Approximation.OrthogonalPolynomial.LegendreBounds
import NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section02

/-!
# Quarteroni–Sacco–Saleri §10.4: Legendre integration and interpolation

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §10.4.

For the Legendre weight `w ≡ 1` the Gauss nodes are the zeros of `L_{n+1}` with weights
`αⱼ = 2/((1 - xⱼ²) L'_{n+1}(xⱼ)²)` (10.32), and the Gauss–Lobatto nodes are `x̄₀ = -1`, `x̄_n = 1`
and the zeros of `L_n'` (10.33) with weights `ᾱⱼ = 2/(n(n + 1) L_n(x̄ⱼ)²)` (10.34). The section
quotes bounds on the Lobatto weights (proved here from `Numlib/Approximation/OrthogonalPolynomial/
LegendreBounds`) and the Legendre forms of the spectral estimates
((10.36)–(10.37), with the norm (10.35)), and derives the discrete Legendre transform: the
interpolant at the Gauss–Lobatto nodes is `∑_{k ≤ n} f̃_k L_k` (10.38), with
`f(x̄ⱼ) = ∑_k f̃_k L_k(x̄ⱼ)` (10.39) and the coefficients (10.40).

The backbone is `Numlib/Approximation/GaussLobatto`: `Quadrature.legendreGaussWeight_eq` and
`Quadrature.legendreLobattoWeight_eq` for the weights, `Quadrature.derivative_legendre_eq_family`
for the identification of the interior Lobatto nodes with the zeros of `L_n'`,
`Quadrature.discreteInner_legendre_legendre` and `Quadrature.interpolate_eq_sum_dlt` for the
transform; the Gauss and Gauss–Lobatto rules themselves are (10.16) and (10.17)–(10.18) of §10.2
for `OrthogonalPolynomial.legendreMeasure`, with `OrthogonalPolynomial.family_eq_legendre`.

## Main definitions

* `legendreDiscreteCoeff n x f k` — the coefficients `f̃_k` of the discrete Legendre transform
  (10.40).

## Main results

* `equation_10_32` — the Legendre–Gauss formula: the `n + 1` zeros of `L_{n+1}` exist, and at
  them the weights `2/((1 - xⱼ²) L'_{n+1}(xⱼ)²)` are positive and give degree of exactness
  `2n + 1`.
* `legendreLobatto_nodal_eq`, `equation_10_34` — the Legendre–Gauss–Lobatto formula: nodes
  `-1`, `1` and the zeros of `L_n'` exist; for any such family the weights
  `2/(n(n + 1) L_n(x̄ⱼ)²)` are well defined, positive and give degree of exactness `2n - 1`, and
  every zero of `L_n'` in `(-1, 1)` is a node.
* `legendreLobattoWeight_bounds` — the bounds `2/(n(n + 1)) ≤ ᾱⱼ ≤ C/n` quoted after (10.34),
  with the explicit constant `C = 8`.
* `equation_10_40` — the discrete Legendre transform (10.38)–(10.40), the discrete norms of the
  Legendre polynomials (the hint of Exercise 6), and the identification of the interpolant with
  the discrete truncation `f_n^*` of (10.4).

## Not formalized here

* **(10.36)–(10.37)**, together with the Legendre forms of (10.22) and (10.24) stated in the norm
  (10.35): `|(f, v_n) - (f, v_n)_n| ≤ C n^{-s} ‖f‖_s ‖v_n‖_{L²(-1,1)}` for every `v_n ∈ ℙ_n`,
  and `|∫_{-1}^1 f - I^{GL}_n f| ≤ C n^{-s} ‖f‖_s` at `v_n = 1` with `‖1‖ = √2`. Quoted from
  [CHQZ88] without proof. This is the Legendre member of the spectral-approximation cluster
  whose three missing layers — the weighted Sobolev seminorms on `(-1, 1)`, the coefficient decay
  by the Sturm–Liouville symmetry, and the aliasing step from the projection to the interpolant —
  are written out in `## Not formalized here` of §10.3
  (`NumlibSurface/QuarteroniSaccoSaleri/Chapter10/Section03.lean`), together with the inventory of
  what the library already has. Two things are specific to this side, and both make it the
  better-prepared one. The **reduction** is that of (10.27) with the Legendre–Gauss–Lobatto rule
  (`equation_10_34`, exact on `ℙ_{2n-1}`): `(f, v_n) - (f, v_n)_n = (g, v_n) - (g, v_n)_n` for
  `g = f - P_{n-1} f`, with `‖v_n‖_n ≤ √3 ‖v_n‖` by the proved norm equivalence and
  `‖g‖_n ≤ √2 ‖g‖_∞` because the weights sum to `2`; (10.37) is then the case `v_n = 1`. And the
  **coefficient identity** the projection layer runs on is `f̂_k = -(k(k+1))⁻¹ ((1-x²) f')'^_k`,
  from `Polynomial.legendre_ode` and one integration by parts on `[-1, 1]` whose boundary terms
  vanish with `1 - x²`; Parseval in `L²(-1,1)` is `IsWeight.hilbertBasis` with
  `OrthogonalPolynomial.family_eq_legendre`. Estimate: the Legendre forms of (10.22), (10.24) and
  (10.36)–(10.37) at the rate `n^{1/2-s}` are some 1000 lines away with no missing theory; at the
  printed rate `n^{-s}`, some 2000 lines and a plan of their own.

## Conventions

Nodes are `x : Fin (n + 1) → ℝ`, injective; "the zeros of `L_{n+1}`" is `∀ j, L_{n+1}(xⱼ) = 0`
for such a family, which by counting is the full set of zeros. The Gauss–Lobatto nodes are
described as the book describes them — `x̄₀ = -1`, `x̄_n = 1`, `L_n'(x̄ⱼ) = 0` for `0 < j < n` — and
`legendreLobatto_nodal_eq` identifies their nodal polynomial with the backbone's
`Quadrature.lobattoNodal legendreMeasure n`. Integrals are `∫_{-1}^1`, the Legendre weight being
Lebesgue measure on `(-1, 1)`.
-/

open MeasureTheory Polynomial OrthogonalPolynomial Quadrature Real Set Filter Topology

namespace QuarteroniSaccoSaleri.Chapter10

variable {n : ℕ}

/-! ### The Legendre–Gauss formula (10.32) -/

/-- **(10.32), the Legendre–Gauss formula.** For `n ≥ 0` the Gauss nodes are the `n + 1` zeros
`x₀, …, x_n` of `L_{n+1}`, which exist, and the coefficients are

`αⱼ = 2 / ((1 - xⱼ²) [L'_{n+1}(xⱼ)]²)`, `j = 0, …, n`,

positive, with degree of exactness `2n + 1`: `∑ⱼ αⱼ p(xⱼ) = ∫_{-1}^1 p` for every `p ∈ ℙ_{2n+1}`.
The zeros are those of the monic orthogonal polynomial of the Legendre weight
(`OrthogonalPolynomial.family_eq_legendre`), so the nodes are the Gauss nodes (10.16); the closed
form of the interpolatory weights is `Quadrature.legendreGaussWeight_eq`. -/
theorem equation_10_32 (n : ℕ) :
    (∃ x : Fin (n + 1) → ℝ, Function.Injective x ∧ ∀ j, (legendre (n + 1)).eval (x j) = 0) ∧
      ∀ x : Fin (n + 1) → ℝ, Function.Injective x → (∀ j, (legendre (n + 1)).eval (x j) = 0) →
        (∀ j, 0 < 2 / ((1 - x j ^ 2) * (derivative (legendre (n + 1))).eval (x j) ^ 2)) ∧
        ∀ p : ℝ[X], p.degree ≤ ((2 * n + 1 : ℕ) : WithBot ℕ) →
          ∑ j, 2 / ((1 - x j ^ 2) * (derivative (legendre (n + 1))).eval (x j) ^ 2) * p.eval (x j) =
            ∫ t in (-1 : ℝ)..1, p.eval t := by
  have hw := isWeight_legendreMeasure
  have hfam : ∀ x : ℝ, (family legendreMeasure (n + 1)).eval x = 0 ↔
      (legendre (n + 1)).eval x = 0 := fun x => by
    rw [family_eq_legendre, eval_mul, eval_C, mul_eq_zero, or_iff_right
      (inv_ne_zero (leadingCoeff_ne_zero.mpr (legendre_ne_zero (n + 1))))]
  refine ⟨?_, fun x hx hroot => ?_⟩
  · obtain ⟨x, hx, hroot⟩ := exists_gauss_nodes hw n
    exact ⟨x, hx, fun j => (hfam _).mp (hroot j)⟩
  set α : Fin (n + 1) → ℝ := fun j => ∫ t, (Lagrange.basis Finset.univ x j).eval t ∂legendreMeasure
    with hα
  have hint : IsInterpolatoryMeasure legendreMeasure α x := fun j => rfl
  have hexact : IsExactOnMeasure legendreMeasure α x (2 * n + 1) :=
    (equation_10_16 hw hx α).mpr ⟨fun j => (hfam _).mpr (hroot j), hint⟩
  have hform : ∀ j, α j = 2 / ((1 - x j ^ 2) * (derivative (legendre (n + 1))).eval (x j) ^ 2) :=
    fun j => legendreGaussWeight_eq hx hint hroot j
  refine ⟨fun j => hform j ▸ pos_of_isExactOnMeasure_of_le hw hx (by omega) hexact j,
    fun p hp => ?_⟩
  rw [← integral_legendreMeasure, ← hexact p hp]
  exact Finset.sum_congr rfl fun j _ => by rw [hform j]

/-! ### The Legendre–Gauss–Lobatto formula (10.33)–(10.34) -/

/-- **The nodal polynomial of the Legendre–Gauss–Lobatto nodes.** A family of `n + 1` distinct
points with `x̄₀ = -1`, `x̄_n = 1` and `L_n'(x̄ⱼ) = 0` at the interior indices — the description
(10.33) — has the backbone's Lobatto nodal polynomial `Quadrature.lobattoNodal legendreMeasure n`
as nodal polynomial: that polynomial is `(x² - 1) q_{n-1}` with `L_n'` a nonzero multiple of
`q_{n-1}` (`Quadrature.derivative_legendre_eq_family`), so it vanishes at every node. -/
theorem legendreLobatto_nodal_eq (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (h0 : x 0 = -1) (hl : x (Fin.last n) = 1)
    (hint : ∀ j : Fin (n + 1), 0 < (j : ℕ) → (j : ℕ) < n →
      (derivative (legendre n)).eval (x j) = 0) :
    Lagrange.nodal Finset.univ x = lobattoNodal legendreMeasure n := by
  have hder := derivative_legendre_eq_family hn
  have hc : (n : ℝ) * (legendre n).leadingCoeff ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (by omega : n ≠ 0))
      (leadingCoeff_ne_zero.mpr (legendre_ne_zero n))
  refine Lagrange.nodal_eq_of_forall_eval_eq_zero hx (lobattoNodal_monic _ _)
    (natDegree_eq_of_degree_eq_some (degree_lobattoNodal _ hn)) fun j => ?_
  rw [lobattoNodal, eval_mul, eval_sub, eval_pow, eval_X, eval_one]
  rcases eq_or_ne j 0 with rfl | hj0
  · rw [h0]
    norm_num
  rcases eq_or_ne j (Fin.last n) with rfl | hjl
  · rw [hl]
    norm_num
  have hq : (family (lobattoMeasure legendreMeasure) (n - 1)).eval (x j) = 0 := by
    have h := hint j (Nat.pos_of_ne_zero (fun h => hj0 (Fin.ext h)))
      (lt_of_le_of_ne (Nat.lt_succ_iff.mp j.2) (fun h => hjl (Fin.ext h)))
    rw [hder, eval_mul, eval_C, mul_eq_zero] at h
    exact h.resolve_left hc
  rw [hq, mul_zero]

/-- **(10.33)–(10.34), the Legendre–Gauss–Lobatto formula.** For `n ≥ 1` the Gauss–Lobatto nodes
are `x̄₀ = -1`, `x̄_n = 1` and the zeros of `L_n'` for `j = 1, …, n - 1` (10.33) — such a family of
`n + 1` distinct points exists — and the weights are

`ᾱⱼ = 2 / (n(n + 1)) · 1 / [L_n(x̄ⱼ)]²`, `j = 0, …, n` (10.34),

where `L_n` is the `n`-th Legendre polynomial (10.12): for any such family, every zero of `L_n'`
in `(-1, 1)` is one of the nodes, `L_n(x̄ⱼ) ≠ 0`, the weights are positive, and the formula has
degree of exactness `2n - 1`: `∑ⱼ ᾱⱼ p(x̄ⱼ) = ∫_{-1}^1 p` for every `p ∈ ℙ_{2n-1}`. Existence is
(10.17)–(10.18) for the Legendre weight with `Quadrature.derivative_legendre_eq_family`; the
weights are `Quadrature.legendreLobattoWeight_eq`. -/
theorem equation_10_34 (hn : 1 ≤ n) :
    (∃ x : Fin (n + 1) → ℝ, Function.Injective x ∧ x 0 = -1 ∧ x (Fin.last n) = 1 ∧
      ∀ j : Fin (n + 1), 0 < (j : ℕ) → (j : ℕ) < n → (derivative (legendre n)).eval (x j) = 0) ∧
    ∀ x : Fin (n + 1) → ℝ, Function.Injective x → x 0 = -1 → x (Fin.last n) = 1 →
      (∀ j : Fin (n + 1), 0 < (j : ℕ) → (j : ℕ) < n → (derivative (legendre n)).eval (x j) = 0) →
      (∀ t ∈ Ioo (-1 : ℝ) 1, (derivative (legendre n)).eval t = 0 → ∃ j, x j = t) ∧
      (∀ j, (legendre n).eval (x j) ≠ 0) ∧
      (∀ j, 0 < 2 / ((n : ℝ) * ((n : ℝ) + 1) * (legendre n).eval (x j) ^ 2)) ∧
      ∀ p : ℝ[X], p.degree ≤ ((2 * n - 1 : ℕ) : WithBot ℕ) →
        ∑ j, 2 / ((n : ℝ) * ((n : ℝ) + 1) * (legendre n).eval (x j) ^ 2) * p.eval (x j) =
          ∫ t in (-1 : ℝ)..1, p.eval t := by
  have hw := isWeight_legendreMeasure
  have hsupp := legendreMeasure_compl_Icc
  have hder := derivative_legendre_eq_family hn
  have hc : (n : ℝ) * (legendre n).leadingCoeff ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (by omega : n ≠ 0))
      (leadingCoeff_ne_zero.mpr (legendre_ne_zero n))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · obtain ⟨x, α, hxinj, hx0, hxlast, -, -, -, hnodal, -⟩ := exists_gaussLobatto hw hsupp hn
    refine ⟨x, hxinj, hx0, hxlast, fun j hj0 hjn => ?_⟩
    have hroot : (lobattoNodal legendreMeasure n).eval (x j) = 0 := by
      rw [← hnodal]
      exact Lagrange.eval_nodal_at_node (Finset.mem_univ j)
    have hne : x j ^ 2 - 1 ≠ 0 := by
      intro h
      have h' : (x j - 1) * (x j + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h' with h1 | h1
      · exact absurd (hxinj (hxlast.trans (by linarith) : x (Fin.last n) = x j))
          (fun h => by have := congrArg Fin.val h; simp at this; omega)
      · exact absurd (hxinj (hx0.trans (by linarith) : x 0 = x j))
          (fun h => by have := congrArg Fin.val h; simp at this; omega)
    rw [lobattoNodal, eval_mul, eval_sub, eval_pow, eval_X, eval_one, mul_eq_zero] at hroot
    rw [hder, eval_mul, hroot.resolve_left hne, mul_zero]
  · intro x hx h0 hl hint
    have hnodal := legendreLobatto_nodal_eq hn hx h0 hl hint
    set α : Fin (n + 1) → ℝ :=
      fun j => ∫ t, (Lagrange.basis Finset.univ x j).eval t ∂legendreMeasure with hα
    have hintα : IsInterpolatoryMeasure legendreMeasure α x := fun j => rfl
    have hexact := isExactOnMeasure_of_nodal_eq_lobattoNodal hw hsupp hn hx hintα hnodal
    have hform : ∀ j, α j = 2 / ((n : ℝ) * ((n : ℝ) + 1) * (legendre n).eval (x j) ^ 2) := fun j =>
      legendreLobattoWeight_eq hn hx hintα hnodal j
    have hLn : ∀ j, (legendre n).eval (x j) ≠ 0 := fun j =>
      legendre_eval_ne_zero_of_nodal_eq_lobattoNodal hn hx hnodal j
    refine ⟨fun t ht hroot => ?_, hLn, fun j => by have := hLn j; positivity, fun p hp => ?_⟩
    · rw [Lagrange.exists_eq_iff_eval_nodal_eq_zero, hnodal, lobattoNodal, eval_mul]
      rw [hder, eval_mul, eval_C, mul_eq_zero] at hroot
      rw [hroot.resolve_left hc, mul_zero]
    · rw [← integral_legendreMeasure, ← hexact p hp]
      exact Finset.sum_congr rfl fun j _ => by rw [hform j]

/-! ### The bounds on the Gauss–Lobatto weights -/

/-- **A Legendre–Gauss–Lobatto node lies in `[-1, 1]`, and `(1 - x̄ⱼ²) L_n'(x̄ⱼ) = 0` there.** The
two endpoints kill the factor `1 - x²`; an interior node is a zero of `L_n'`, hence a zero of the
`(n-1)`-st orthogonal polynomial of the modified weight `(1 - x²) dx`
(`Quadrature.derivative_legendre_eq_family`), and the zeros of an orthogonal polynomial lie inside
the interval carrying its weight. -/
theorem legendreLobattoNode_mem_Icc (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ} (h0 : x 0 = -1)
    (hl : x (Fin.last n) = 1)
    (hint : ∀ j : Fin (n + 1), 0 < (j : ℕ) → (j : ℕ) < n →
      (derivative (legendre n)).eval (x j) = 0) (j : Fin (n + 1)) :
    x j ∈ Icc (-1 : ℝ) 1 ∧ (1 - x j ^ 2) * (derivative (legendre n)).eval (x j) = 0 := by
  rcases eq_or_ne (j : ℕ) 0 with hj0 | hj0
  · rw [show j = 0 from Fin.ext hj0, h0]
    norm_num
  rcases eq_or_ne (j : ℕ) n with hjn | hjn
  · rw [show j = Fin.last n from Fin.ext (by simpa using hjn), hl]
    norm_num
  have hroot := hint j (Nat.pos_of_ne_zero hj0)
    (lt_of_le_of_ne (Nat.lt_succ_iff.mp j.2) hjn)
  refine ⟨?_, by rw [hroot, mul_zero]⟩
  have hw := isWeight_legendreMeasure
  have hsupp := legendreMeasure_compl_Icc
  have hc : (n : ℝ) * (legendre n).leadingCoeff ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (by omega : n ≠ 0))
      (leadingCoeff_ne_zero.mpr (legendre_ne_zero n))
  have hfam : (family (lobattoMeasure legendreMeasure) (n - 1)).eval (x j) = 0 := by
    rw [derivative_legendre_eq_family hn, eval_mul, eval_C, mul_eq_zero] at hroot
    exact hroot.resolve_left hc
  exact Ioo_subset_Icc_self
    (root_family_mem_Ioo (isWeight_lobattoMeasure hw hsupp) (lobattoMeasure_compl_Icc hsupp) hfam)

/-- **The bounds on the Legendre–Gauss–Lobatto weights** quoted after (10.34): there is a constant
`C` independent of `n` with

`2 / (n(n + 1)) ≤ ᾱⱼ ≤ C / n`, `j = 0, …, n`,

for the weights `ᾱⱼ = 2/(n(n + 1) L_n(x̄ⱼ)²)` of (10.34) at any family of Gauss–Lobatto nodes
(10.33). The book quotes this from Bernardi and Maday; it is proved here with the explicit
constant `C = 8` from the two bounds of
`Numlib/Approximation/OrthogonalPolynomial/LegendreBounds`: `L_n(x̄ⱼ)² ≤ 1` on `[-1, 1]` gives the
lower bound, and `L_n(x̄ⱼ)² ≥ 1/(4n)` at a point where `(1 - x²) L_n'` vanishes gives the upper
one. Injectivity of the nodes is not needed. -/
theorem legendreLobattoWeight_bounds :
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ x : Fin (n + 1) → ℝ, x 0 = -1 → x (Fin.last n) = 1 →
      (∀ j : Fin (n + 1), 0 < (j : ℕ) → (j : ℕ) < n →
        (derivative (legendre n)).eval (x j) = 0) →
      ∀ j : Fin (n + 1),
        2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
            2 / ((n : ℝ) * ((n : ℝ) + 1) * (legendre n).eval (x j) ^ 2) ∧
          2 / ((n : ℝ) * ((n : ℝ) + 1) * (legendre n).eval (x j) ^ 2) ≤ c / n := by
  refine ⟨8, fun n hn x h0 hl hint j => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hmem, hcrit⟩ := legendreLobattoNode_mem_Icc hn h0 hl hint j
  have hup : (legendre n).eval (x j) ^ 2 ≤ 1 := eval_legendre_sq_le_one n hmem
  have hlow : 1 / (4 * (n : ℝ)) ≤ (legendre n).eval (x j) ^ 2 :=
    inv_le_eval_legendre_sq hn hmem hcrit
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (n : ℝ))] at hlow
  have hpos : 0 < (legendre n).eval (x j) ^ 2 := by nlinarith [hnR, hlow]
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((n : ℝ) * ((n : ℝ) + 1)))
      (by linarith : (0 : ℝ) ≤ 1 - (legendre n).eval (x j) ^ 2)]
  · rw [div_le_div_iff₀ (by positivity) hnR]
    nlinarith [hnR, hlow,
      mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((n : ℝ) + 1))
        (by linarith : (0 : ℝ) ≤ (legendre n).eval (x j) ^ 2 * (4 * (n : ℝ)) - 1)]

/-! ### The discrete Legendre transform (10.38)–(10.40) -/

/-- **(10.40), the discrete coefficients** of the discrete Legendre transform (DLT) at the
Gauss–Lobatto nodes `x̄`:

`f̃_k = ((2k + 1)/(n(n + 1))) ∑ⱼ L_k(x̄ⱼ) f(x̄ⱼ) / L_n(x̄ⱼ)²` for `k = 0, …, n - 1`, and
`f̃_n = (1/(n + 1)) ∑ⱼ f(x̄ⱼ) / L_n(x̄ⱼ)`. -/
noncomputable def legendreDiscreteCoeff (n : ℕ) (x : Fin (n + 1) → ℝ) (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  if k = n then 1 / ((n : ℝ) + 1) * ∑ j, f (x j) / (legendre n).eval (x j)
  else (2 * k + 1) / ((n : ℝ) * ((n : ℝ) + 1)) *
    ∑ j, (legendre k).eval (x j) * f (x j) / (legendre n).eval (x j) ^ 2

/-- **(10.38)–(10.40), the discrete Legendre transform (Exercise 6).** For the Legendre–Gauss–
Lobatto nodes `x̄` of (10.33) with the weights `ᾱⱼ` of (10.34), the interpolating polynomial at the
nodes is

`Π^{GL}_n f = ∑_{k=0}^n f̃_k L_k` (10.38), with the coefficients `f̃_k` of (10.40),

so that `f(x̄ⱼ) = ∑_{k=0}^n f̃_k L_k(x̄ⱼ)` (10.39), the inverse transform; `Π^{GL}_n f` coincides
with the discrete truncation `f_n^*` of (10.4) for the discrete scalar product (10.28) of the rule;
and the Legendre polynomials are orthogonal for that discrete scalar product, with
`(L_k, L_k)_n = 2/(2k + 1)` for `k < n` and `(L_n, L_n)_n = 2/n` (the hint of Exercise 6). The
backbone's `Quadrature.interpolate_eq_sum_dlt` and `Quadrature.discreteInner_legendre_legendre`. -/
theorem equation_10_40 (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (h0 : x 0 = -1) (hl : x (Fin.last n) = 1)
    (hint : ∀ j : Fin (n + 1), 0 < (j : ℕ) → (j : ℕ) < n → (derivative (legendre n)).eval (x j) = 0)
    (f : ℝ → ℝ) :
    (Lagrange.interpolate Finset.univ x fun j => f (x j)) =
        ∑ k ∈ Finset.range (n + 1), C (legendreDiscreteCoeff n x f k) * legendre k ∧
      (∀ j, f (x j) = ∑ k ∈ Finset.range (n + 1),
        legendreDiscreteCoeff n x f k * (legendre k).eval (x j)) ∧
      (Lagrange.interpolate Finset.univ x fun j => f (x j)) =
        discreteTruncation legendreMeasure
          (fun j => 2 / ((n : ℝ) * ((n : ℝ) + 1) * (legendre n).eval (x j) ^ 2)) x n f ∧
      ∀ k l, k ≤ n → l ≤ n →
        discreteInner (fun j => 2 / ((n : ℝ) * ((n : ℝ) + 1) * (legendre n).eval (x j) ^ 2)) x
            (fun t => (legendre k).eval t) (fun t => (legendre l).eval t) =
          if k = l then (if k = n then (2 : ℝ) / n else 2 / (2 * (k : ℝ) + 1)) else 0 := by
  have hw := isWeight_legendreMeasure
  have hsupp := legendreMeasure_compl_Icc
  have hnodal := legendreLobatto_nodal_eq hn hx h0 hl hint
  set α : Fin (n + 1) → ℝ := fun j => 2 / ((n : ℝ) * ((n : ℝ) + 1) * (legendre n).eval (x j) ^ 2)
    with hα
  have hintα : IsInterpolatoryMeasure legendreMeasure α x := fun j =>
    (legendreLobattoWeight_eq hn hx (fun _ => rfl) hnodal j).symm
  have hexact := isExactOnMeasure_of_nodal_eq_lobattoNodal hw hsupp hn hx hintα hnodal
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : ∀ j, 0 < α j := fun j => by
    have := legendre_eval_ne_zero_of_nodal_eq_lobattoNodal hn hx hnodal j
    positivity
  have hdlt := interpolate_eq_sum_dlt hn hx hpos hintα hnodal hexact f
  refine ⟨hdlt, fun j => ?_, ?_, fun k l hk hl => ?_⟩
  · have hev := Lagrange.eval_interpolate_at_node (fun j => f (x j)) hx.injOn (Finset.mem_univ j)
    rw [hdlt, eval_finsetSum] at hev
    rw [← hev]
    exact Finset.sum_congr rfl fun k _ => by rw [eval_mul, eval_C, legendreDiscreteCoeff]
  · exact interpolate_eq_sum_discreteInner_smul hw hn hx hpos hexact f
  · exact discreteInner_legendre_legendre hn hx hintα hnodal hexact hk hl

end QuarteroniSaccoSaleri.Chapter10
