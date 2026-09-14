import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Numlib.Approximation.GaussLobatto

/-!
# Quarteroni–Sacco–Saleri §10.1: approximation by generalized Fourier series

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §10.1.

For a weight function `w` on `(-1, 1)` and a system `{p_k}` of polynomials, `p_k` of degree `k`,
mutually orthogonal for `(f, g)_w = ∫_{-1}^1 f g w`, the section introduces the space `L²_w`
(10.1), the generalized Fourier series `Sf = ∑ f̂_k p_k` with `f̂_k = (f, p_k)_w / ‖p_k‖_w²`, its
truncation `f_n` of order `n` (10.2), the convergence `‖f - f_n‖_w → 0` with Parseval's equality,
the minimization property (10.3), the discrete truncation `f_n^*` (10.4)–(10.5) with its own
minimization property (10.6), the three-term recurrence (10.7)–(10.8) of the monic family, and the
Chebyshev (§10.1.1) and Legendre (§10.1.2) families with Remark 10.1 on the Jacobi weights.

The backbone is `Numlib/Approximation/OrthogonalPolynomial` and its child `Classical`: a weight
is a measure `μ` on `ℝ` satisfying `OrthogonalPolynomial.IsWeight` (finite moments, infinite
support), the book's `w(x) dx` on `(-1, 1)` being `weightMeasure w`; `{p_k}` is the monic family
`OrthogonalPolynomial.family μ`, `L²_w` is `Lp ℝ 2 μ`, and the polynomials sit inside it through
`OrthogonalPolynomial.IsWeight.toLpₗ`. The Chebyshev and Legendre weights are
`OrthogonalPolynomial.chebyshevMeasure` (Mathlib's `Polynomial.Chebyshev.measureT`) and
`OrthogonalPolynomial.legendreMeasure`; the discrete truncation rests on the discrete inner product
`Quadrature.discreteInner` of `Numlib/Approximation/Quadrature`.

## Main definitions

* `weightMeasure w` — the measure `w(x) dx` on `(-1, 1)`, with `integral_weightMeasure` and
  `isWeight_weightMeasure` (a nonnegative integrable weight with `∫ w ≠ 0` is a weight in the
  backbone's sense).
* `fourierCoeff hw f k` — the Fourier coefficient `f̂_k = (f, p_k)_w / ‖p_k‖_w²`, spelled out as a
  quotient of integrals by `fourierCoeff_eq`; `truncation hw n f` — the truncation `f_n` (10.2).
* `discreteCoeff μ w x f k`, `discreteTruncation μ w x n f`, `discreteNorm w x g` — the discrete
  coefficients (10.5), the discrete truncation (10.4) and the discrete seminorm `‖g‖_n` of a
  quadrature rule with weights `w` and nodes `x`.

## Main results

* `equation_10_3` — `‖f - f_n‖_w = min_{q ∈ ℙ_n} ‖f - q‖_w`.
* `truncation_tendsto` — `‖f - f_n‖_w → 0` and Parseval's equality `‖f‖_w² = ∑ f̂_k² ‖p_k‖_w²`,
  for a weight carried by a compact interval.
* `equation_10_6` — `‖f - f_n^*‖_n = min_{q ∈ ℙ_n} ‖f - q‖_n` for the discrete scalar product of a
  rule with `n + 1` distinct nodes, positive weights and degree of exactness `2n - 1`.
* `equation_10_7` — the three-term recurrence (10.7) with the coefficients (10.8).
* `equation_10_10`, `equation_10_11`, `chebyshev_inner`, `chebyshev_minimax` — the Chebyshev
  polynomials: `T_k(x) = cos (k arccos x)`, the recurrence (10.11) (Exercise 1), the
  orthogonality relations with `‖T_n‖_∞ = 1`, and the minimax property of `2^{1-n} T_n`.
* `equation_10_12`, `legendre_inner` — the Legendre polynomials: the explicit sum (10.12), the
  recurrence, and `(L_k, L_m) = δ_{km} (k + 1/2)⁻¹`.
* `remark_10_1` — the Jacobi weights `(1 - x)^α (1 + x)^β`, `α, β > -1`, with the Legendre and
  Chebyshev families as the cases `α = β = 0` and `α = β = -1/2`.

## Conventions

The book's `p_k` are the *monic* orthogonal polynomials (they must be, for (10.7)–(10.8) to hold as
stated), so `f̂_k` and `f_n` are defined through `OrthogonalPolynomial.family μ`; the Chebyshev and
Legendre series of §10.1.1–10.1.2 use the classical normalizations `T_k`, `L_k` instead, which the
identities `OrthogonalPolynomial.family_chebyshevMeasure_eq` and `family_eq_legendre` relate to the
monic family. `ℙ_n` inside `L²_w` is `(Polynomial.degreeLE ℝ n).map hw.toLpₗ`. The sup norm of a
polynomial on `[-1, 1]` is `sSup ((fun x => |p.eval x|) '' Icc (-1) 1)`, as in
`Numlib/RingTheory/Polynomial/ChebyshevMinimax`. Note the index shift in (10.8): the book's
`β_{k+1} = (p_{k+1}, p_{k+1})_w / (p_k, p_k)_w` is the backbone's `OrthogonalPolynomial.beta μ k`.
-/

open MeasureTheory Polynomial OrthogonalPolynomial Real Set Filter Topology

open scoped Nat

namespace QuarteroniSaccoSaleri.Chapter10

variable {μ : Measure ℝ} {n : ℕ}

/-! ### The weighted space `L²_w(-1, 1)` (10.1) -/

/-- **(10.1), the weight.** A weight function `w` on `(-1, 1)` — a nonnegative integrable
function there — gives the measure `w(x) dx` on `(-1, 1)`, of which the book's `L²_w(-1, 1)` is the
`L²` space `Lp ℝ 2 (weightMeasure w)` and `(f, g)_w = ∫_{-1}^1 f g w` the inner product. -/
noncomputable def weightMeasure (w : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity fun x => ENNReal.ofReal (w x)

/-- An integral against `weightMeasure w` is the weighted integral `∫_{-1}^1 w f`. -/
theorem integral_weightMeasure {w : ℝ → ℝ} (hmeas : Measurable w)
    (hnn : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 ≤ w x) (f : ℝ → ℝ) :
    ∫ x, f x ∂weightMeasure w = ∫ x in Ioo (-1 : ℝ) 1, w x * f x := by
  refine integral_withDensity_ofReal hmeas ?_ f
  rw [ae_restrict_iff' measurableSet_Ioo]
  exact Eventually.of_forall hnn

/-- **A weight function in the book's sense is a weight in the backbone's sense**: for `w`
measurable, nonnegative and integrable on `(-1, 1)` and not almost everywhere zero
(`∫_{-1}^1 w ≠ 0`, which the book leaves implicit — without it `‖·‖_w` is not a norm),
`weightMeasure w` has finite moments and infinite support, so the orthogonal family `{p_k}` of
§10.1 exists. -/
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

/-- **The Fourier coefficient** `f̂_k = (f, p_k)_w / ‖p_k‖_w²` of `f ∈ L²_w` in the monic
orthogonal family `{p_k}` of the weight `μ`; `fourierCoeff_eq` writes it as the quotient of
integrals of the book. -/
noncomputable def fourierCoeff (hw : IsWeight μ) (f : Lp ℝ 2 μ) (k : ℕ) : ℝ :=
  inner ℝ f (hw.toLpₗ (family μ k)) / normSq μ k

/-- The Fourier coefficient written out: `f̂_k = ∫ f p_k ∂μ / ∫ p_k² ∂μ`. -/
theorem fourierCoeff_eq (hw : IsWeight μ) (f : Lp ℝ 2 μ) (k : ℕ) :
    fourierCoeff hw f k =
      (∫ x, f x * (family μ k).eval x ∂μ) / ∫ x, (family μ k).eval x ^ 2 ∂μ := by
  rw [fourierCoeff, normSq, L2.inner_def]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hw.coeFn_toLpₗ (family μ k)] with x hx
  rw [hx]
  simp [RCLike.inner_apply, mul_comm]

/-- **(10.2), the truncation of order `n`** of the generalized Fourier series of `f ∈ L²_w`:
`f_n = ∑_{k=0}^n f̂_k p_k`, an element of `ℙ_n ⊆ L²_w`. -/
noncomputable def truncation (hw : IsWeight μ) (n : ℕ) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  ∑ k : Fin (n + 1), fourierCoeff hw f k • hw.toLpₗ (family μ k)

/-- The truncation is the backbone's best approximation
`OrthogonalPolynomial.isBestApprox_truncation`, the inner products written in the other order. -/
theorem truncation_eq (hw : IsWeight μ) (n : ℕ) (f : Lp ℝ 2 μ) :
    truncation hw n f =
      ∑ k : Fin (n + 1), (inner ℝ (hw.toLpₗ (family μ k)) f / normSq μ k) • hw.toLpₗ (family μ k) :=
  Finset.sum_congr rfl fun k _ => by rw [fourierCoeff, real_inner_comm]

/-- **(10.3).** The truncation `f_n ∈ ℙ_n` of the generalized Fourier series of `f ∈ L²_w`
satisfies the minimization property `‖f - f_n‖_w = min_{q ∈ ℙ_n} ‖f - q‖_w`: `f_n` is the
orthogonal projection of `f` over `ℙ_n` in the sense of `L²_w`. The backbone's
`OrthogonalPolynomial.isBestApprox_truncation`. -/
theorem equation_10_3 (hw : IsWeight μ) (n : ℕ) (f : Lp ℝ 2 μ) :
    truncation hw n f ∈ (degreeLE ℝ n).map hw.toLpₗ ∧
      IsLeast (Set.range fun q : (degreeLE ℝ n).map hw.toLpₗ => ‖f - (q : Lp ℝ 2 μ)‖)
        ‖f - truncation hw n f‖ := by
  have h := isBestApprox_truncation hw n f
  rw [← truncation_eq] at h
  exact ⟨h.1, ⟨⟨_, h.1⟩, rfl⟩, by rintro _ ⟨q, rfl⟩; exact h.2 q q.2⟩

/-- The Hilbert basis of the orthonormal polynomials, term by term: `⟪e_k, f⟫ e_k = f̂_k p_k`. -/
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

/-- **The convergence of the generalized Fourier series, and Parseval's equality.** For a weight
carried by a compact interval `[a, b]` and `f ∈ L²_w`, the series `Sf` converges in average to `f`,
`lim_{n → ∞} ‖f - f_n‖_w = 0`, and `‖f‖_w² = ∑_{k=0}^∞ f̂_k² ‖p_k‖_w²`. The orthonormal polynomials
are a Hilbert basis of `L²_w` (`OrthogonalPolynomial.hilbertBasis`), and `f_n` is the `n`-th
partial sum of the expansion in it. -/
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

/-- **(10.5), the discrete coefficients** `f̃_k = (f, p_k)_n / ‖p_k‖_n²` of `f` for the discrete
scalar product `(f, g)_n = ∑ᵢ αᵢ f(xᵢ) g(xᵢ)` (`Quadrature.discreteInner`) of a quadrature rule
with weights `w` and nodes `x`, and the monic orthogonal family `{p_k}` of the weight `μ`. -/
noncomputable def discreteCoeff {m : ℕ} (μ : Measure ℝ) (w x : Fin m → ℝ) (f : ℝ → ℝ) (k : ℕ) :
    ℝ :=
  Quadrature.discreteInner w x f (fun t => (family μ k).eval t) /
    Quadrature.discreteInner w x (fun t => (family μ k).eval t) (fun t => (family μ k).eval t)

/-- **(10.4), the discrete truncation of order `n`** of the Fourier series of `f`:
`f_n^* = ∑_{k=0}^n f̃_k p_k`, a polynomial of degree at most `n`. -/
noncomputable def discreteTruncation {m : ℕ} (μ : Measure ℝ) (w x : Fin m → ℝ) (n : ℕ)
    (f : ℝ → ℝ) : ℝ[X] :=
  ∑ k : Fin (n + 1), C (discreteCoeff μ w x f k) * family μ k

/-- **The discrete seminorm** `‖g‖_n = √(g, g)_n` associated with the discrete scalar product of
a rule with weights `w` and nodes `x`. -/
noncomputable def discreteNorm {m : ℕ} (w x : Fin m → ℝ) (g : ℝ → ℝ) : ℝ :=
  √(Quadrature.discreteInner w x g g)

/-- The discrete truncation has degree at most `n`. -/
theorem degree_discreteTruncation_le {m : ℕ} (μ : Measure ℝ) (w x : Fin m → ℝ) (n : ℕ)
    (f : ℝ → ℝ) : (discreteTruncation μ w x n f).degree ≤ n := by
  refine (degree_sum_le _ _).trans (Finset.sup_le fun k _ => (degree_mul_le _ _).trans ?_)
  rw [degree_family]
  calc (C (discreteCoeff μ w x f k)).degree + ((k : ℕ) : WithBot ℕ)
      ≤ 0 + ((k : ℕ) : WithBot ℕ) := by gcongr; exact degree_C_le
    _ ≤ n := by rw [zero_add]; exact_mod_cast Nat.lt_succ_iff.mp k.2

/-- **(10.6).** Let the discrete scalar product `(·, ·)_n` be that of a quadrature rule with
`n + 1` distinct nodes, positive weights and degree of exactness at least `2n - 1` with respect to
`μ` — the Gauss or Gauss–Lobatto rules of §10.2. Then the discrete truncation `f_n^* ∈ ℙ_n` of
(10.4) is the approximation to `f` in `ℙ_n` in the least-squares sense:
`‖f - f_n^*‖_n = min_{q ∈ ℙ_n} ‖f - q‖_n`. Indeed `f_n^*` is the interpolant of `f` at the nodes
(`Quadrature.interpolate_eq_sum_discreteInner_smul`), so `‖f - f_n^*‖_n = 0`. -/
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

/-- **(10.7)–(10.8), the recursive three-term formula.** For the monic orthogonal family `{p_k}`
of a weight, `p_{k+1} = (x - α_k) p_k - β_k p_{k-1}` for `k ≥ 0` with `p_{-1} = 0`, `p_0 = 1`,
where

`α_k = (x p_k, p_k)_w / (p_k, p_k)_w`, `β_{k+1} = (p_{k+1}, p_{k+1})_w / (p_k, p_k)_w`, `k ≥ 0`;

stated as `p_0 = 1`, `p_1 = x - α_0` (the step `k = 0`, where `β_0 p_{-1}` vanishes) and
`p_{k+2} = (x - α_{k+1}) p_{k+1} - β_{k+1} p_k`, with the two coefficient formulas. The backbone's
`OrthogonalPolynomial.three_term_recurrence`; its `beta μ k` is the book's `β_{k+1}`. -/
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

/-! ### §10.1.1: the Chebyshev polynomials -/

/-- **(10.10).** The Chebyshev polynomials are `T_k(x) = cos (kθ)`, `θ = arccos x`, for
`x ∈ [-1, 1]` and `k = 0, 1, 2, …`: Mathlib's `Polynomial.Chebyshev.T_real_cos` at `θ = arccos x`.
-/
theorem equation_10_10 (k : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (Chebyshev.T ℝ k).eval x = cos (k * arccos x) := by
  have h := Chebyshev.T_real_cos (θ := arccos x) (n := k)
  rw [cos_arccos hx.1 hx.2] at h
  rw [h]
  push_cast
  rfl

/-- **(10.11) (Exercise 1).** The Chebyshev polynomials are generated recursively by
`T_{k+1}(x) = 2x T_k(x) - T_{k-1}(x)`, `k = 1, 2, …`, `T_0(x) = 1`, `T_1(x) = x`; so `T_k` is an
algebraic polynomial of degree `k`. Mathlib's `Polynomial.Chebyshev.T_add_two`, `T_zero`, `T_one`
and `degree_T`. -/
theorem equation_10_11 (k : ℕ) :
    Chebyshev.T ℝ 0 = 1 ∧ Chebyshev.T ℝ 1 = X ∧
      Chebyshev.T ℝ (k + 2) = 2 * X * Chebyshev.T ℝ (k + 1) - Chebyshev.T ℝ k ∧
      (Chebyshev.T ℝ k).degree = k :=
  ⟨Chebyshev.T_zero ℝ, Chebyshev.T_one ℝ, Chebyshev.T_add_two ℝ k, by
    rw [Chebyshev.degree_T]; simp⟩

/-- **§10.1.1, the orthogonality of the Chebyshev polynomials** for the Chebyshev weight
`w(x) = (1 - x²)^{-1/2}`: `(T_k, T_n)_w = 0` if `k ≠ n`, `(T_n, T_n)_w = c_n` with `c_0 = π` and
`c_n = π/2` for `n ≠ 0`; and `‖T_n‖_∞ = 1` on `[-1, 1]` for every `n`. The backbone's
`Polynomial.Chebyshev.integral_T_mul_T_div_sqrt` and Mathlib's `abs_eval_T_real_le_one` with
`T_n(1) = 1`. -/
theorem chebyshev_inner (k n : ℕ) :
    (∫ x in (-1 : ℝ)..1, (Chebyshev.T ℝ k).eval x * (Chebyshev.T ℝ n).eval x / √(1 - x ^ 2)) =
        (if k ≠ n then 0 else if n = 0 then π else π / 2) ∧
      sSup ((fun x => |(Chebyshev.T ℝ n).eval x|) '' Icc (-1 : ℝ) 1) = 1 := by
  refine ⟨Chebyshev.integral_T_mul_T_div_sqrt k n, IsGreatest.csSup_eq ⟨⟨1, ⟨by norm_num, le_rfl⟩,
    by simp [Chebyshev.T_eval_one]⟩, ?_⟩⟩
  rintro _ ⟨x, hx, rfl⟩
  exact Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr hx)

/-- `2^{1-n} = (2^{n-1})⁻¹` for `n ≥ 1`. -/
private theorem two_zpow_one_sub (hn : 1 ≤ n) :
    (2 : ℝ) ^ (1 - (n : ℤ)) = ((2 : ℝ) ^ (n - 1))⁻¹ := by
  rw [show (1 - (n : ℤ)) = -((n - 1 : ℕ) : ℤ) by push_cast [Nat.cast_sub hn]; ring, zpow_neg,
    zpow_natCast]

/-- The modulus of a polynomial attains its maximum over `[-1, 1]`. -/
private theorem exists_isGreatest_abs_eval (p : ℝ[X]) :
    ∃ M, IsGreatest ((fun t => |p.eval t|) '' Icc (-1 : ℝ) 1) M :=
  (isCompact_Icc.image p.continuous.abs).exists_isGreatest
    ((nonempty_Icc.mpr (by norm_num)).image _)

/-- **§10.1.1, the minimax property of the Chebyshev polynomials.** For `n ≥ 1`,
`‖2^{1-n} T_n‖_∞ = 2^{1-n}` and `‖2^{1-n} T_n‖_∞ ≤ min_{p ∈ ℙ_n^1} ‖p‖_∞`, where
`ℙ_n^1 = {p = ∑_{k ≤ n} a_k x^k, a_n = 1}` is the set of monic polynomials of degree `n`. If
`‖p‖_∞ < 2^{1-n}` for a monic `p` of degree `n`, then `p / ‖p‖_∞` is bounded by `1` on `[-1, 1]`
with leading coefficient `> 2^{n-1}`, contradicting Mathlib's
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
    obtain ⟨M, hM⟩ := exists_isGreatest_abs_eval p
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

/-! ### §10.1.2: the Legendre polynomials -/

/-- **(10.12) and the Legendre recurrence.** The Legendre polynomials are

`L_k(x) = 2^{-k} ∑_{l=0}^{[k/2]} (-1)^l C(k, l) C(2k - 2l, k) x^{k-2l}`, `k = 0, 1, …`,

or, recursively, `L_{k+1} = ((2k+1)/(k+1)) x L_k - (k/(k+1)) L_{k-1}` for `k = 1, 2, …` with
`L_0 = 1`, `L_1 = x`; and `L_k ∈ ℙ_k`. The backbone's `Polynomial.legendre_eq_sum` and
`Polynomial.legendre_recurrence` (there in the form `(k+2) L_{k+2} = (2k+3) x L_{k+1} - (k+1) L_k`).
-/
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

/-- **§10.1.2, the orthogonality of the Legendre polynomials**: for `k, m = 0, 1, 2, …`,
`(L_k, L_m) = δ_{km} (k + 1/2)^{-1}` in `L²(-1, 1)`. The backbone's
`Polynomial.integral_legendre_mul_legendre`. -/
theorem legendre_inner (k m : ℕ) :
    ∫ x in (-1 : ℝ)..1, (legendre k).eval x * (legendre m).eval x =
      if k = m then ((k : ℝ) + 1 / 2)⁻¹ else 0 := by
  rw [integral_legendre_mul_legendre]
  split_ifs with h
  · subst h
    field_simp
  · rfl

/-! ### Remark 10.1: the Jacobi polynomials -/

/-- **Remark 10.1 (the Jacobi polynomials).** The Legendre and Chebyshev polynomials belong to the
family of Jacobi polynomials, orthogonal with respect to the weight `w(x) = (1 - x)^α (1 + x)^β`
on `(-1, 1)`, `α, β > -1` — a weight in the backbone's sense
(`OrthogonalPolynomial.isWeight_jacobiMeasure`). Setting `α = β = 0` recovers the Legendre
weight, whose monic orthogonal polynomials are the rescaled `L_n`, and `α = β = -1/2` gives the
Chebyshev weight, whose monic orthogonal polynomials are `2^{1-n} T_n` (`1` for `n = 0`). -/
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
