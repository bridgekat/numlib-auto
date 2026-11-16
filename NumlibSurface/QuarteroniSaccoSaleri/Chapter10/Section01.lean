/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Numlib.Approximation.GaussLobatto

/-!
# Quarteroni, Sacco and Saleri, Section 10.1: Approximation by generalized Fourier series

This module formalizes Section 10.1 of [quarteroni2000numerical]. Let $w$ be a weight function on
$(-1, 1)$, and let $\{p_k\}$ be a system of polynomials, $p_k$ of degree $k$, that are mutually
orthogonal for the scalar product $(f, g)_w = \int_{-1}^1 f g w \, dx$. The section introduces the
space $L^2_w(-1, 1)$ (10.1), the generalized Fourier series $Sf = \sum_k \hat f_k p_k$ with
$\hat f_k = (f, p_k)_w / \|p_k\|_w^2$, and its truncation $f_n = \sum_{k=0}^n \hat f_k p_k$ of order
$n$ (10.2). It proves that $\|f - f_n\|_w \to 0$, Parseval's equality, and the minimization property
(10.3). It then introduces the discrete truncation $f_n^*$ (10.4)–(10.5) for the discrete scalar
product of a quadrature rule, with its own minimization property (10.6), and the three-term
recurrence (10.7)–(10.8) of the monic orthogonal family.

The subsections treat two classical families: the Chebyshev polynomials $T_k$ (Section 10.1.1), with
their orthogonality and minimax property, and the Legendre polynomials $L_k$ (Section 10.1.2), with
the explicit sum (10.12) and their orthogonality. Remark 10.1 places both among the Jacobi
polynomials. The proofs specialize the backbone modules `Numlib.Approximation.OrthogonalPolynomial`,
`Numlib.Approximation.OrthogonalPolynomial.Classical` and `Numlib.Approximation.Quadrature`.

## Main definitions

* Equation (10.1), `QuarteroniSaccoSaleri.Chapter10.weightMeasure`: the measure $w(x)\,dx$ on
  $(-1, 1)$, whose $L^2$ space is $L^2_w(-1, 1)$.
* Section 10.1, `QuarteroniSaccoSaleri.Chapter10.fourierCoeff`: the Fourier coefficient
  $\hat f_k = (f, p_k)_w / \|p_k\|_w^2$.
* Equation (10.2), `QuarteroniSaccoSaleri.Chapter10.truncation`: the truncation
  $f_n = \sum_{k=0}^n \hat f_k p_k$.
* Equation (10.5), `QuarteroniSaccoSaleri.Chapter10.discreteCoeff`: the discrete coefficient
  $\tilde f_k = (f, p_k)_n / \|p_k\|_n^2$.
* Equation (10.4), `QuarteroniSaccoSaleri.Chapter10.discreteTruncation`: the discrete truncation
  $f_n^* = \sum_{k=0}^n \tilde f_k p_k$.
* Section 10.1, `QuarteroniSaccoSaleri.Chapter10.discreteNorm`: the discrete seminorm
  $\|g\|_n = \sqrt{(g, g)_n}$.

## Main results

* Equation (10.3), `QuarteroniSaccoSaleri.Chapter10.equation_10_3`: $f_n \in \mathbb{P}_n$ and
  $\|f - f_n\|_w = \min_{q \in \mathbb{P}_n} \|f - q\|_w$.
* Section 10.1, `QuarteroniSaccoSaleri.Chapter10.truncation_tendsto`: for a weight carried by a
  compact interval, $\|f - f_n\|_w \to 0$ and $\|f\|_w^2 = \sum_k \hat f_k^2 \|p_k\|_w^2$.
* Equations (10.4)–(10.6), `QuarteroniSaccoSaleri.Chapter10.equation_10_6`: $\|f - f_n^*\|_n =
  \min_{q \in \mathbb{P}_n} \|f - q\|_n$ for a rule with $n + 1$ distinct nodes, positive weights
  and degree of exactness $2n - 1$.
* Equations (10.7)–(10.8), `QuarteroniSaccoSaleri.Chapter10.equation_10_7`: the three-term
  recurrence of the monic orthogonal family, with the formulas for its coefficients.
* Equation (10.10), `QuarteroniSaccoSaleri.Chapter10.equation_10_10`: $T_k(x) = \cos(k \arccos x)$
  on $[-1, 1]$.
* Equation (10.11) and Exercise 10.1, `QuarteroniSaccoSaleri.Chapter10.equation_10_11`: the
  recurrence of the Chebyshev polynomials, and $\deg T_k = k$.
* Section 10.1.1, `QuarteroniSaccoSaleri.Chapter10.chebyshev_inner`: the orthogonality relations of
  the Chebyshev polynomials, and $\|T_n\|_\infty = 1$.
* Section 10.1.1, `QuarteroniSaccoSaleri.Chapter10.chebyshev_minimax`: the minimax property of
  $2^{1-n} T_n$ among the monic polynomials of degree $n$.
* Equation (10.12), `QuarteroniSaccoSaleri.Chapter10.equation_10_12`: the explicit sum and the
  recurrence of the Legendre polynomials.
* Section 10.1.2, `QuarteroniSaccoSaleri.Chapter10.legendre_inner`:
  $(L_k, L_m) = \delta_{km} (k + 1/2)^{-1}$.
* Remark 10.1, `QuarteroniSaccoSaleri.Chapter10.remark_10_1`: the Jacobi weights
  $(1 - x)^\alpha (1 + x)^\beta$, with the Legendre and Chebyshev weights as the cases
  $\alpha = \beta = 0$ and $\alpha = \beta = -1/2$.

## Conventions

* The polynomials $p_k$ of the book are the monic orthogonal polynomials, because (10.7)–(10.8) hold
  as stated only for them. So $\hat f_k$ and $f_n$ are defined with `OrthogonalPolynomial.family μ`.
  The Chebyshev and Legendre series of Sections 10.1.1–10.1.2 use the classical normalizations $T_k$
  and $L_k$ instead. The identities `OrthogonalPolynomial.family_chebyshevMeasure_eq` and
  `OrthogonalPolynomial.family_eq_legendre` relate them to the monic family.
* A weight is a measure $\mu$ on $\mathbb{R}$ that satisfies `OrthogonalPolynomial.IsWeight` (finite
  moments, and positive mass outside every finite set). The weight $w(x)\,dx$ on $(-1, 1)$ of the
  book is `QuarteroniSaccoSaleri.Chapter10.weightMeasure w`. The space $L^2_w$ is `Lp ℝ 2 μ`, and
  the polynomials are embedded in it by `OrthogonalPolynomial.IsWeight.toLpₗ`.
* The space $\mathbb{P}_n$ inside $L^2_w$ is `(Polynomial.degreeLE ℝ n).map hw.toLpₗ`.
* The sup norm of a polynomial $p$ on $[-1, 1]$ is `sSup ((fun x => |p.eval x|) '' Icc (-1) 1)`.
* The Chebyshev and Legendre weights are `OrthogonalPolynomial.chebyshevMeasure` (which is Mathlib's
  `Polynomial.Chebyshev.measureT`) and `OrthogonalPolynomial.legendreMeasure`. The discrete scalar
  product is `Quadrature.discreteInner`.

## Implementation notes

* The coefficients of (10.8) have an index shift: the coefficient $\beta_{k+1} = (p_{k+1},
  p_{k+1})_w / (p_k, p_k)_w$ of the book is `OrthogonalPolynomial.beta μ k`.

## Deviations from the source

* **Section 10.1, the weight function** (reading). The book leaves implicit that $w$ is not almost
  everywhere zero. The library assumes $\int_{-1}^1 w \neq 0$, without which $\|\cdot\|_w$ is not a
  norm. See `QuarteroniSaccoSaleri.Chapter10.isWeight_weightMeasure`.
-/

open MeasureTheory Polynomial OrthogonalPolynomial Real Set Filter Topology

open scoped Nat

namespace QuarteroniSaccoSaleri.Chapter10

variable {μ : Measure ℝ} {n : ℕ}

/-! ### The weighted space $L^2_w(-1, 1)$ (10.1) -/

/-- **Equation (10.1)** of [quarteroni2000numerical], the weight. Let $w : (-1, 1) \to \mathbb{R}$
be a weight function, that is, a nonnegative integrable function. The weight defines the measure
$w(x)\,dx$ on $(-1, 1)$. The space $L^2_w(-1, 1)$ of the book is the $L^2$ space of this
measure, with the scalar product $(f, g)_w = \int_{-1}^1 f g w \, dx$.

The measure is the Lebesgue measure on $(-1, 1)$ with the density $\max(w, 0)$, so negative
values of `w` count as $0$. The space $L^2_w(-1, 1)$ is `Lp ℝ 2 (weightMeasure w)`. -/
noncomputable def weightMeasure (w : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity fun x => ENNReal.ofReal (w x)

/-- Supports equation (10.1). Let $w$ be measurable and nonnegative on $(-1, 1)$. Then for every
$f : \mathbb{R} \to \mathbb{R}$,
$$\int f \, d(w\,dx) = \int_{-1}^1 w(x) f(x) \, dx.$$
-/
theorem integral_weightMeasure {w : ℝ → ℝ} (hmeas : Measurable w)
    (hnn : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 ≤ w x) (f : ℝ → ℝ) :
    ∫ x, f x ∂weightMeasure w = ∫ x in Ioo (-1 : ℝ) 1, w x * f x := by
  refine integral_withDensity_ofReal hmeas ?_ f
  rw [ae_restrict_iff' measurableSet_Ioo]
  exact Eventually.of_forall hnn

/-- Supports equation (10.1). Let $w$ be measurable, nonnegative and integrable on $(-1, 1)$, with
$\int_{-1}^1 w \, dx \neq 0$. Then the measure $w(x)\,dx$ is a weight in the sense of
`OrthogonalPolynomial.IsWeight`: it has finite moments of all orders and gives positive mass to
the complement of every finite set. So the orthogonal family $\{p_k\}$ of Section 10.1 exists.

**Reading.** The book does not state the condition $\int_{-1}^1 w \neq 0$, which says that $w$
is not almost everywhere zero. Without it $\|\cdot\|_w$ is not a norm on the polynomials. -/
theorem isWeight_weightMeasure {w : ℝ → ℝ} (hmeas : Measurable w)
    (hnn : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 ≤ w x) (hint : IntegrableOn w (Ioo (-1 : ℝ) 1))
    (hne : ∫ x in Ioo (-1 : ℝ) 1, w x ≠ 0) : IsWeight (weightMeasure w) := by
  have hnn' : ∀ᵐ x ∂(volume.restrict (Ioo (-1 : ℝ) 1)), 0 ≤ w x := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall hnn
  refine isWeight_of_absolutelyContinuous ((withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self))
    (ne_zero_of_integral_ne_zero (f := fun _ => (1 : ℝ)) ?_) fun k => ?_
  · rw [integral_weightMeasure hmeas hnn]
    simpa using hne
  · rw [weightMeasure, integrable_withDensity_ofReal_iff hmeas hnn']
    refine hint.mul_bdd (c := 1) (continuous_pow k).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun x hx => ?_
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_one₀ (abs_nonneg x) (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)

/-! ### The generalized Fourier series and its truncation (10.2) -/

/-- **Section 10.1** of [quarteroni2000numerical], the generalized Fourier coefficient. Let $\mu$ be
a weight with monic orthogonal family $\{p_k\}$, and let $f \in L^2_w$. The **Fourier
coefficient** of $f$ of index $k$ is
$$\hat f_k = \frac{(f, p_k)_w}{\|p_k\|_w^2}.$$

The norm $\|p_k\|_w^2$ is `OrthogonalPolynomial.normSq μ k`. The lemma
`QuarteroniSaccoSaleri.Chapter10.fourierCoeff_eq` writes $\hat f_k$ as a quotient of integrals. -/
noncomputable def fourierCoeff (hw : IsWeight μ) (f : Lp ℝ 2 μ) (k : ℕ) : ℝ :=
  inner ℝ f (hw.toLpₗ (family μ k)) / normSq μ k

/-- Supports the definition of the Fourier coefficient in Section 10.1. Let $\mu$ be a weight with
monic orthogonal family $\{p_k\}$, and let $f \in L^2_w$. Then
$$\hat f_k = \frac{\int f p_k \, d\mu}{\int p_k^2 \, d\mu}.$$
-/
theorem fourierCoeff_eq (hw : IsWeight μ) (f : Lp ℝ 2 μ) (k : ℕ) :
    fourierCoeff hw f k =
      (∫ x, f x * (family μ k).eval x ∂μ) / ∫ x, (family μ k).eval x ^ 2 ∂μ := by
  rw [fourierCoeff, normSq, L2.inner_def]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hw.coeFn_toLpₗ (family μ k)] with x hx
  rw [hx]
  simp [RCLike.inner_apply, mul_comm]

/-- **Equation (10.2)** of [quarteroni2000numerical]. Let $\mu$ be a weight with monic orthogonal
family $\{p_k\}$, and let $f \in L^2_w$. The **truncation of order $n$** of the generalized
Fourier series of $f$ is
$$f_n = \sum_{k=0}^n \hat f_k p_k,$$
an element of $\mathbb{P}_n \subseteq L^2_w$. -/
noncomputable def truncation (hw : IsWeight μ) (n : ℕ) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  ∑ k : Fin (n + 1), fourierCoeff hw f k • hw.toLpₗ (family μ k)

/-- Supports equation (10.2). The truncation $f_n$ equals
$\sum_{k=0}^n ((p_k, f)_w / \|p_k\|_w^2)\, p_k$, the form of the best approximation in
`OrthogonalPolynomial.isBestApprox_truncation`, with the arguments of the scalar product in the
other order. -/
theorem truncation_eq (hw : IsWeight μ) (n : ℕ) (f : Lp ℝ 2 μ) :
    truncation hw n f =
      ∑ k : Fin (n + 1), (inner ℝ (hw.toLpₗ (family μ k)) f / normSq μ k) • hw.toLpₗ (family μ k) :=
  Finset.sum_congr rfl fun k _ => by rw [fourierCoeff, real_inner_comm]

/-- **Equation (10.3)** of [quarteroni2000numerical]. Let $\mu$ be a weight, let $f \in L^2_w$ and
let $n \ge 0$. Then the truncation $f_n$ lies in $\mathbb{P}_n$, and
$$\|f - f_n\|_w = \min_{q \in \mathbb{P}_n} \|f - q\|_w.$$
So $f_n$ is the orthogonal projection of $f$ onto $\mathbb{P}_n$ in $L^2_w$.

The space $\mathbb{P}_n$ is its image in `Lp ℝ 2 μ`, and the minimum is `IsLeast`. The proof
specializes `OrthogonalPolynomial.isBestApprox_truncation`. -/
theorem equation_10_3 (hw : IsWeight μ) (n : ℕ) (f : Lp ℝ 2 μ) :
    truncation hw n f ∈ (degreeLE ℝ n).map hw.toLpₗ ∧
      IsLeast (Set.range fun q : (degreeLE ℝ n).map hw.toLpₗ => ‖f - (q : Lp ℝ 2 μ)‖)
        ‖f - truncation hw n f‖ := by
  have h := isBestApprox_truncation hw n f
  rw [← truncation_eq] at h
  exact ⟨h.1, ⟨⟨_, h.1⟩, rfl⟩, by rintro _ ⟨q, rfl⟩; exact h.2 q q.2⟩

/-- The term of index $k$ of the expansion of $f$ in the Hilbert basis of orthonormal polynomials is
$\hat f_k p_k$. -/
private theorem coe_hilbertBasis_inner_smul (hw : IsWeight μ) {a b : ℝ}
    (hsupp : μ (Icc a b)ᶜ = 0) (f : Lp ℝ 2 μ) (k : ℕ) :
    (hilbertBasis hw hsupp).repr f k • hilbertBasis hw hsupp k =
      fourierCoeff hw f k • hw.toLpₗ (family μ k) := by
  have hpos := normOf_pos hw k
  rw [HilbertBasis.repr_apply_apply]
  simp only [coe_hilbertBasis]
  rw [orthonormalFamily, ← smul_eq_C_mul, map_smul, inner_smul_left, smul_smul, fourierCoeff,
    real_inner_comm, ← sq_normOf hw k]
  congr 1
  simp only [RCLike.conj_to_real]
  field_simp

/-- **Section 10.1** of [quarteroni2000numerical], the convergence of the generalized Fourier series
and Parseval's equality. Let $\mu$ be a weight with $\mu(\mathbb{R} \setminus [a, b]) = 0$ for
some $a, b \in \mathbb{R}$, and let $f \in L^2_w$. Then the series $Sf$ converges to $f$ in the
mean,
$$\lim_{n \to \infty} \|f - f_n\|_w = 0,$$
and
$$\|f\|_w^2 = \sum_{k=0}^\infty \hat f_k^2 \|p_k\|_w^2.$$

The orthonormal polynomials form a Hilbert basis of $L^2_w$
(`OrthogonalPolynomial.hilbertBasis`), and $f_n$ is the partial sum of index $n$ of the
expansion of $f$ in it. -/
theorem truncation_tendsto (hw : IsWeight μ) {a b : ℝ} (hsupp : μ (Icc a b)ᶜ = 0)
    (f : Lp ℝ 2 μ) :
    Tendsto (fun n => ‖f - truncation hw n f‖) atTop (𝓝 0) ∧
      ‖f‖ ^ 2 = ∑' k, fourierCoeff hw f k ^ 2 * normSq μ k := by
  set e := hilbertBasis hw hsupp with he
  constructor
  · have hrev : (fun n => ‖f - truncation hw n f‖) = fun n => ‖truncation hw n f - f‖ :=
      funext fun n => norm_sub_rev _ _
    rw [hrev, ← tendsto_iff_norm_sub_tendsto_zero]
    have h := (e.hasSum_repr f).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, truncation, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun k _ => coe_hilbertBasis_inner_smul hw hsupp f k
  · rw [← real_inner_self_eq_norm_sq, ← e.tsum_inner_mul_inner f f]
    refine tsum_congr fun k => ?_
    have hk := normSq_ne_zero hw k
    have hpos := normOf_pos hw k
    rw [he]
    simp only [coe_hilbertBasis]
    rw [orthonormalFamily, ← smul_eq_C_mul, map_smul, inner_smul_left, inner_smul_right,
      real_inner_comm, fourierCoeff, real_inner_comm f]
    simp only [RCLike.conj_to_real]
    rw [← sq_normOf hw k] at hk ⊢
    field_simp

/-! ### The discrete truncation (10.4)–(10.6) -/

/-- **Equation (10.5)** of [quarteroni2000numerical]. Let $\mu$ be a weight with monic orthogonal
family $\{p_k\}$, and let a quadrature rule have weights $\alpha_i$ and nodes $x_i$. Its
discrete scalar product is $(f, g)_n = \sum_i \alpha_i f(x_i) g(x_i)$. The **discrete
coefficient** of $f : \mathbb{R} \to \mathbb{R}$ of index $k$ is
$$\tilde f_k = \frac{(f, p_k)_n}{\|p_k\|_n^2}.$$

The discrete scalar product is `Quadrature.discreteInner`. The quotient uses the Lean convention
$x / 0 = 0$. -/
noncomputable def discreteCoeff {m : ℕ} (μ : Measure ℝ) (w x : Fin m → ℝ) (f : ℝ → ℝ) (k : ℕ) :
    ℝ :=
  Quadrature.discreteInner w x f (fun t => (family μ k).eval t) /
    Quadrature.discreteInner w x (fun t => (family μ k).eval t) (fun t => (family μ k).eval t)

/-- **Equation (10.4)** of [quarteroni2000numerical]. With the discrete coefficients $\tilde f_k$ of
(10.5), the **discrete truncation of order $n$** of the Fourier series of $f$ is the polynomial
$$f_n^* = \sum_{k=0}^n \tilde f_k p_k.$$
-/
noncomputable def discreteTruncation {m : ℕ} (μ : Measure ℝ) (w x : Fin m → ℝ) (n : ℕ)
    (f : ℝ → ℝ) : ℝ[X] :=
  ∑ k : Fin (n + 1), C (discreteCoeff μ w x f k) * family μ k

/-- **Section 10.1** of [quarteroni2000numerical], the discrete seminorm. For a quadrature rule with
weights $\alpha_i$ and nodes $x_i$, the **discrete seminorm** of $g$ is
$\|g\|_n = \sqrt{(g, g)_n}$.

The square root is `Real.sqrt`, which is $0$ at negative arguments. -/
noncomputable def discreteNorm {m : ℕ} (w x : Fin m → ℝ) (g : ℝ → ℝ) : ℝ :=
  √(Quadrature.discreteInner w x g g)

/-- Supports equation (10.4). The discrete truncation $f_n^*$ has degree at most $n$. -/
theorem degree_discreteTruncation_le {m : ℕ} (μ : Measure ℝ) (w x : Fin m → ℝ) (n : ℕ)
    (f : ℝ → ℝ) : (discreteTruncation μ w x n f).degree ≤ n := by
  refine (degree_sum_le _ _).trans (Finset.sup_le fun k _ => (degree_mul_le _ _).trans ?_)
  rw [degree_family]
  calc (C (discreteCoeff μ w x f k)).degree + ((k : ℕ) : WithBot ℕ)
      ≤ 0 + ((k : ℕ) : WithBot ℕ) := by gcongr; exact degree_C_le
    _ ≤ n := by rw [zero_add]; exact_mod_cast Nat.lt_succ_iff.mp k.2

/-- **Equations (10.4)–(10.6)** of [quarteroni2000numerical]. Let $\mu$ be a weight and let
$n \ge 1$. Let a quadrature rule have $n + 1$ distinct nodes $x_i$ and positive weights
$\alpha_i$, and let it be exact for $\mu$ on all polynomials of degree at most $2n - 1$, as the
Gauss and Gauss–Lobatto rules of Section 10.2 are. Let $(\cdot, \cdot)_n$ be its discrete scalar
product. Then for every $f : \mathbb{R} \to \mathbb{R}$ the discrete truncation $f_n^*$ lies in
$\mathbb{P}_n$, and
$$\|f - f_n^*\|_n = \min_{q \in \mathbb{P}_n} \|f - q\|_n.$$
So $f_n^*$ is the approximation of $f$ in $\mathbb{P}_n$ in the least-squares sense.

In fact $f_n^*$ is the interpolant of $f$ at the nodes
(`Quadrature.interpolate_eq_sum_discreteInner_smul`), so $\|f - f_n^*\|_n = 0$. The exactness is
`Quadrature.IsExactOnMeasure μ w x (2 * n - 1)`. -/
theorem equation_10_6 (hw : IsWeight μ) (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) {w : Fin (n + 1) → ℝ} (hwpos : ∀ i, 0 < w i)
    (hexact : Quadrature.IsExactOnMeasure μ w x (2 * n - 1)) (f : ℝ → ℝ) :
    (discreteTruncation μ w x n f).degree ≤ n ∧
      IsLeast (Set.range fun q : degreeLE ℝ n =>
          discreteNorm w x (f - fun t => (q : ℝ[X]).eval t))
        (discreteNorm w x (f - fun t => (discreteTruncation μ w x n f).eval t)) := by
  have hdeg := degree_discreteTruncation_le μ w x n f
  have hinterp : discreteTruncation μ w x n f =
      Lagrange.interpolate Finset.univ x fun i => f (x i) :=
    (Quadrature.interpolate_eq_sum_discreteInner_smul hw hn hx hwpos hexact f).symm
  have hzero : discreteNorm w x (f - fun t => (discreteTruncation μ w x n f).eval t) = 0 := by
    rw [discreteNorm, Real.sqrt_eq_zero', Quadrature.discreteInner]
    refine le_of_eq (Finset.sum_eq_zero fun i _ => ?_)
    rw [hinterp, Pi.sub_apply, Lagrange.eval_interpolate_at_node _ hx.injOn (Finset.mem_univ i),
      sub_self, mul_zero]
  refine ⟨hdeg, ⟨⟨_, mem_degreeLE.mpr hdeg⟩, rfl⟩, ?_⟩
  rintro _ ⟨q, rfl⟩
  rw [hzero]
  exact Real.sqrt_nonneg _

/-! ### The three-term recurrence (10.7)–(10.8) -/

/-- **Equations (10.7)–(10.8)** of [quarteroni2000numerical], the three-term recurrence. Let $\mu$
be a weight with monic orthogonal family $\{p_k\}$. Then
$p_{k+1} = (x - \alpha_k) p_k - \beta_k p_{k-1}$ for $k \ge 0$, with $p_{-1} = 0$ and $p_0 = 1$,
where
$$\alpha_k = \frac{(x p_k, p_k)_w}{(p_k, p_k)_w}, \qquad \beta_{k+1} = \frac{(p_{k+1},
  p_{k+1})_w}{(p_k, p_k)_w}, \qquad k \ge 0.$$

The statement has five parts: $p_0 = 1$; $p_1 = x - \alpha_0$, which is the step $k = 0$ where
$\beta_0 p_{-1}$ vanishes; $p_{k+2} = (x - \alpha_{k+1}) p_{k+1} - \beta_{k+1} p_k$; and the two
formulas for the coefficients. The coefficient $\alpha_k$ is `OrthogonalPolynomial.alpha μ k`,
and the coefficient $\beta_{k+1}$ of the book is `OrthogonalPolynomial.beta μ k`. The proof
specializes `OrthogonalPolynomial.three_term_recurrence`. -/
theorem equation_10_7 (hw : IsWeight μ) (k : ℕ) :
    family μ 0 = 1 ∧ family μ 1 = X - C (alpha μ 0) ∧
      family μ (k + 2) =
        (X - C (alpha μ (k + 1))) * family μ (k + 1) - C (beta μ k) * family μ k ∧
      alpha μ k = (∫ x, x * (family μ k).eval x * (family μ k).eval x ∂μ) /
        ∫ x, (family μ k).eval x * (family μ k).eval x ∂μ ∧
      beta μ k = (∫ x, (family μ (k + 1)).eval x * (family μ (k + 1)).eval x ∂μ) /
        ∫ x, (family μ k).eval x * (family μ k).eval x ∂μ := by
  have hsq : ∀ j : ℕ, ∫ x, (family μ j).eval x * (family μ j).eval x ∂μ = normSq μ j :=
    fun j => integral_congr_ae (Eventually.of_forall fun x => (sq _).symm)
  refine ⟨family_zero μ, family_one μ, three_term_recurrence hw k, ?_, ?_⟩
  · rw [alpha, hsq]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  · rw [beta, hsq, hsq]

/-! ### Section 10.1.1: The Chebyshev polynomials -/

/-- **Equation (10.10)** of [quarteroni2000numerical]. For $k = 0, 1, 2, \dots$ and $x \in [-1, 1]$,
the Chebyshev polynomial $T_k$ satisfies
$$T_k(x) = \cos(k\theta), \qquad \theta = \arccos x.$$

The polynomial $T_k$ is Mathlib's `Polynomial.Chebyshev.T ℝ k`. The proof specializes
`Polynomial.Chebyshev.T_real_cos` at $\theta = \arccos x$. -/
theorem equation_10_10 (k : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (Chebyshev.T ℝ k).eval x = cos (k * arccos x) := by
  have h := Chebyshev.T_real_cos (θ := arccos x) (n := k)
  rw [cos_arccos hx.1 hx.2] at h
  rw [h]
  push_cast
  rfl

/-- **Equation (10.11)** and **Exercise 10.1** of [quarteroni2000numerical]. The Chebyshev
polynomials satisfy $T_0(x) = 1$, $T_1(x) = x$ and
$$T_{k+1}(x) = 2x T_k(x) - T_{k-1}(x), \qquad k = 1, 2, \dots$$
So $T_k$ is a polynomial of degree $k$.

The recurrence is stated as $T_{k+2} = 2x T_{k+1} - T_k$ for $k \ge 0$. The proof uses Mathlib's
`Polynomial.Chebyshev.T_add_two`, `Polynomial.Chebyshev.T_zero`, `Polynomial.Chebyshev.T_one`
and `Polynomial.Chebyshev.degree_T`. -/
theorem equation_10_11 (k : ℕ) :
    Chebyshev.T ℝ 0 = 1 ∧ Chebyshev.T ℝ 1 = X ∧
      Chebyshev.T ℝ (k + 2) = 2 * X * Chebyshev.T ℝ (k + 1) - Chebyshev.T ℝ k ∧
      (Chebyshev.T ℝ k).degree = k :=
  ⟨Chebyshev.T_zero ℝ, Chebyshev.T_one ℝ, Chebyshev.T_add_two ℝ k, by
    rw [Chebyshev.degree_T]; simp⟩

/-- **Section 10.1.1** of [quarteroni2000numerical], the orthogonality of the Chebyshev polynomials.
Let $w(x) = (1 - x^2)^{-1/2}$ be the Chebyshev weight. For $k, n \ge 0$,
$$(T_k, T_n)_w = \begin{cases} 0 & k \neq n, \\ \pi & k = n = 0, \\ \pi/2 & k = n \neq 0.
  \end{cases}$$
Moreover $\|T_n\|_\infty = 1$ on $[-1, 1]$ for every $n$.

The scalar product is the interval integral $\int_{-1}^1 T_k T_n / \sqrt{1 - x^2} \, dx$. The
proof uses `Polynomial.Chebyshev.integral_T_mul_T_div_sqrt`, and Mathlib's
`Polynomial.Chebyshev.abs_eval_T_real_le_one` together with $T_n(1) = 1$. -/
theorem chebyshev_inner (k n : ℕ) :
    (∫ x in (-1 : ℝ)..1, (Chebyshev.T ℝ k).eval x * (Chebyshev.T ℝ n).eval x / √(1 - x ^ 2)) =
        (if k ≠ n then 0 else if n = 0 then π else π / 2) ∧
      sSup ((fun x => |(Chebyshev.T ℝ n).eval x|) '' Icc (-1 : ℝ) 1) = 1 := by
  refine ⟨Chebyshev.integral_T_mul_T_div_sqrt k n, IsGreatest.csSup_eq ⟨⟨1, ⟨by norm_num, le_rfl⟩,
    by simp [Chebyshev.T_eval_one]⟩, ?_⟩⟩
  rintro _ ⟨x, hx, rfl⟩
  exact Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr hx)

/-- For $n \ge 1$, $2^{1-n} = (2^{n-1})^{-1}$. -/
private theorem two_zpow_one_sub (hn : 1 ≤ n) :
    (2 : ℝ) ^ (1 - (n : ℤ)) = ((2 : ℝ) ^ (n - 1))⁻¹ := by
  rw [show (1 - (n : ℤ)) = -((n - 1 : ℕ) : ℤ) by push_cast [Nat.cast_sub hn]; ring, zpow_neg,
    zpow_natCast]

/-- **Section 10.1.1** of [quarteroni2000numerical], the minimax property of the Chebyshev
polynomials. Let $n \ge 1$, and let $\mathbb{P}_n^1 = \{p = \sum_{k=0}^n a_k x^k : a_n = 1\}$ be
the set of monic polynomials of degree $n$. Then $\|2^{1-n} T_n\|_\infty = 2^{1-n}$, and
$$\|2^{1-n} T_n\|_\infty \le \|p\|_\infty \quad \text{for every } p \in \mathbb{P}_n^1,$$
where $\|\cdot\|_\infty$ is the sup norm on $[-1, 1]$.

The idea of the proof: if $\|p\|_\infty < 2^{1-n}$ for a monic $p$ of degree $n$, then
$p / \|p\|_\infty$ is bounded by $1$ on $[-1, 1]$ and has leading coefficient greater than
$2^{n-1}$. This contradicts Mathlib's
`Polynomial.Chebyshev.leadingCoeff_le_of_forall_abs_le_one`. -/
theorem chebyshev_minimax (hn : 1 ≤ n) :
    sSup ((fun x => |(C ((2 : ℝ) ^ (1 - (n : ℤ))) * Chebyshev.T ℝ n).eval x|) '' Icc (-1 : ℝ) 1) =
        (2 : ℝ) ^ (1 - (n : ℤ)) ∧
      ∀ p : ℝ[X], p.Monic → p.natDegree = n →
        (2 : ℝ) ^ (1 - (n : ℤ)) ≤ sSup ((fun x => |p.eval x|) '' Icc (-1 : ℝ) 1) := by
  have hc : (0 : ℝ) < 2 ^ (1 - (n : ℤ)) := zpow_pos (by norm_num) _
  constructor
  · refine IsGreatest.csSup_eq ⟨⟨1, ⟨by norm_num, le_rfl⟩, ?_⟩, ?_⟩
    · simp [Chebyshev.T_eval_one, abs_of_pos hc]
    · rintro _ ⟨x, hx, rfl⟩
      simp only [eval_mul, eval_C, abs_mul, abs_of_pos hc]
      exact mul_le_of_le_one_right hc.le (Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr hx))
  · intro p hp hpn
    obtain ⟨M, hM⟩ : ∃ M, IsGreatest ((fun t => |p.eval t|) '' Icc (-1 : ℝ) 1) M :=
      (isCompact_Icc.image p.continuous.abs).exists_isGreatest
        ((nonempty_Icc.mpr (by norm_num)).image _)
    rw [hM.csSup_eq]
    by_contra hlt
    push Not at hlt
    have hM0 : 0 < M := by
      rcases hM.1 with ⟨x, -, hx⟩
      refine lt_of_le_of_ne (hx ▸ abs_nonneg _) fun h0 => ?_
      -- `p` would vanish on `[-1, 1]`, an infinite set
      have hroots : ∀ t ∈ Icc (-1 : ℝ) 1, p.IsRoot t := fun t ht => by
        have h1 : |p.eval t| ≤ M := hM.2 ⟨t, ht, rfl⟩
        rw [← h0] at h1
        exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
      have : (Icc (-1 : ℝ) 1).Finite :=
        (p.finite_setOfPred_isRoot hp.ne_zero).subset fun t ht => hroots t ht
      exact this.not_infinite (Icc_infinite (by norm_num))
    have hbnd : ∀ x ∈ Icc (-1 : ℝ) 1, |(C M⁻¹ * p).eval x| ≤ 1 := fun x hx => by
      rw [eval_mul, eval_C, abs_mul, abs_of_pos (inv_pos.mpr hM0),
        inv_mul_le_iff₀ hM0, mul_one]
      exact hM.2 ⟨x, hx, rfl⟩
    have hdeg : (C M⁻¹ * p).degree ≤ n := by
      rw [degree_C_mul (inv_ne_zero hM0.ne'), degree_eq_natDegree hp.ne_zero, hpn]
    have hlc := Chebyshev.leadingCoeff_le_of_forall_abs_le_one hdeg hbnd
    rw [leadingCoeff_mul, leadingCoeff_C, hp.leadingCoeff, mul_one] at hlc
    rw [two_zpow_one_sub hn] at hlt
    have := (inv_lt_inv₀ (by positivity) hM0).mpr hlt
    rw [inv_inv] at this
    exact absurd hlc (not_le.mpr this)

/-! ### Section 10.1.2: The Legendre polynomials -/

/-- **Equation (10.12)** of [quarteroni2000numerical] and the Legendre recurrence. The Legendre
polynomials are
$$L_k(x) = \frac{1}{2^k} \sum_{l=0}^{[k/2]} (-1)^l \binom{k}{l} \binom{2k - 2l}{k} x^{k - 2l},
  \qquad k = 0, 1, \dots$$
They satisfy $L_0 = 1$, $L_1 = x$ and
$$L_{k+1}(x) = \frac{2k + 1}{k + 1} x L_k(x) - \frac{k}{k + 1} L_{k-1}(x), \qquad k = 1, 2,
  \dots,$$
and $L_k$ has degree $k$.

The polynomial $L_k$ is `Polynomial.legendre k`, which is defined by Rodrigues' formula. The
recurrence is stated with the index shifted, as $L_{k+2} = \frac{2k + 3}{k + 2} x L_{k+1} -
\frac{k + 1}{k + 2} L_k$ for $k \ge 0$. The proof uses `Polynomial.legendre_eq_sum` and
`Polynomial.legendre_recurrence`. -/
theorem equation_10_12 (k : ℕ) :
    legendre k = C ((2 : ℝ) ^ k)⁻¹ * ∑ l ∈ Finset.range (k / 2 + 1),
        C ((-1) ^ l * (k.choose l : ℝ) * ((2 * k - 2 * l).choose k : ℝ)) * X ^ (k - 2 * l) ∧
      legendre 0 = 1 ∧ legendre 1 = X ∧
      legendre (k + 2) = C ((2 * (k : ℝ) + 3) / ((k : ℝ) + 2)) * X * legendre (k + 1) -
        C (((k : ℝ) + 1) / ((k : ℝ) + 2)) * legendre k ∧
      (legendre k).degree = k := by
  refine ⟨legendre_eq_sum k, legendre_zero, legendre_one, ?_, degree_legendre k⟩
  have hk : ((k : ℝ) + 2) ≠ 0 := by positivity
  have h := legendre_recurrence k
  rw [show ((k : ℝ[X]) + 2) = C ((k : ℝ) + 2) by rw [map_add, map_natCast, map_ofNat],
    show (2 * (k : ℝ[X]) + 3) = C (2 * (k : ℝ) + 3) by
      rw [map_add, map_mul, map_natCast, map_ofNat, map_ofNat],
    show ((k : ℝ[X]) + 1) = C ((k : ℝ) + 1) by rw [map_add, map_natCast, map_one]] at h
  calc legendre (k + 2) = C ((k : ℝ) + 2)⁻¹ * (C ((k : ℝ) + 2) * legendre (k + 2)) := by
        rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hk, C_1, one_mul]
    _ = C ((k : ℝ) + 2)⁻¹ * (C (2 * (k : ℝ) + 3) * X * legendre (k + 1) -
          C ((k : ℝ) + 1) * legendre k) := by rw [h]
    _ = _ := by
        rw [mul_sub, ← mul_assoc, ← mul_assoc, ← C_mul, ← mul_assoc, ← C_mul, div_eq_inv_mul,
          div_eq_inv_mul]

/-- **Section 10.1.2** of [quarteroni2000numerical], the orthogonality of the Legendre polynomials.
For $k, m = 0, 1, 2, \dots$,
$$(L_k, L_m) = \int_{-1}^1 L_k L_m \, dx = \delta_{km} \left(k + \tfrac{1}{2}\right)^{-1}.$$

The proof specializes `Polynomial.integral_legendre_mul_legendre`. -/
theorem legendre_inner (k m : ℕ) :
    ∫ x in (-1 : ℝ)..1, (legendre k).eval x * (legendre m).eval x =
      if k = m then ((k : ℝ) + 1 / 2)⁻¹ else 0 := by
  rw [integral_legendre_mul_legendre]
  split_ifs with h
  · subst h
    field_simp
  · rfl

/-! ### Remark 10.1: The Jacobi polynomials -/

/-- **Remark 10.1** of [quarteroni2000numerical] (the Jacobi polynomials). Let $\alpha, \beta > -1$.
The Jacobi weight $w(x) = (1 - x)^\alpha (1 + x)^\beta$ on $(-1, 1)$ defines a measure $\mu$
with
$$\int f \, d\mu = \int_{-1}^1 (1 - x)^\alpha (1 + x)^\beta f(x) \, dx$$
for every $f$, and $\mu$ is a weight in the sense of `OrthogonalPolynomial.IsWeight`. The
Legendre and Chebyshev polynomials belong to the Jacobi family:

* for $\alpha = \beta = 0$ the Jacobi weight is the Legendre weight, and its monic orthogonal
  polynomials are $L_k / \operatorname{lc}(L_k)$, where $\operatorname{lc}$ is the leading
  coefficient;
* for $\alpha = \beta = -1/2$ the Jacobi weight is the Chebyshev weight, and its monic
  orthogonal polynomials are $(2^{k-1})^{-1} T_k$ for $k \ge 1$, and $1$ for $k = 0$.

The measure of the Jacobi weight is `OrthogonalPolynomial.jacobiMeasure α β`. Its weight
property is `OrthogonalPolynomial.isWeight_jacobiMeasure`. In the Lean statement the exponent
$k - 1$ is a natural number, so it is $0$ at $k = 0$, and $(2^0)^{-1} T_0 = 1$. -/
theorem remark_10_1 {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    (∀ f : ℝ → ℝ, ∫ x, f x ∂jacobiMeasure α β =
        ∫ x in Ioo (-1 : ℝ) 1, (1 - x) ^ α * (1 + x) ^ β * f x) ∧
      IsWeight (jacobiMeasure α β) ∧
      jacobiMeasure 0 0 = legendreMeasure ∧
      (∀ k, family legendreMeasure k = C ((legendre k).leadingCoeff)⁻¹ * legendre k) ∧
      jacobiMeasure (-1 / 2) (-1 / 2) = chebyshevMeasure ∧
      ∀ k, family chebyshevMeasure k = C ((2 : ℝ) ^ (k - 1))⁻¹ * Chebyshev.T ℝ k :=
  ⟨integral_jacobiMeasure α β, isWeight_jacobiMeasure hα hβ, jacobiMeasure_zero_zero,
    family_eq_legendre, jacobiMeasure_neg_half_neg_half, family_chebyshevMeasure_eq⟩

end QuarteroniSaccoSaleri.Chapter10
