import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Numlib.Analysis.Fourier.Aliasing
import Numlib.Analysis.Sobolev.Periodic
import Numlib.Analysis.Sobolev.Periodic.Smooth
import Numlib.Approximation.MvPolynomial

/-!
# Atkinson–Han §7.5: periodic Sobolev spaces

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §7.5.1–§7.5.3, together with
Definition 7.5.8 and the minimax error (7.5.30) of §7.5.5.

§7.5 is the one section of chapter 7 that needs no theory of Sobolev spaces on a domain.  The book
defines `H^s(2π)` by the decay of the Fourier coefficients: a formal series `φ = ∑_m a_m ψ_m` with
`ψ_m x = (2π)^{-1/2} e^{i m x}` belongs to it when

`‖φ‖²_{*,s} = |a₀|² + ∑_{|m| > 0} |m|^{2 s} |a_m|² < ∞`,

which is a weighted `ℓ²(ℤ, ℂ)` and nothing more.  That space is `PeriodicSobolev s` in the backbone,
and this module is the book's numbered statements about it.

## The normalization

The backbone reads a series against the *unnormalized* characters `periodicChar T m x =
exp (2 π i m x / T)`, whereas the book uses `ψ_m = (2π)^{-1/2} e^{i m x}`.  The two differ by the
constant `(2π)^{-1/2}`, which the norm `‖·‖_{*,s}` does not see — it is a norm on the coefficient
sequence — but which every statement about the *function* does.  `AtkinsonHan.Chapter07.eval`
carries that constant, so `eval φ` is the book's `φ(x)` on the nose, and the bounds below are the
book's with the book's constants.

## Main results

* `definition_7_5_1_norm`, `definition_7_5_1_inner` — (7.5.2) and the inner product that induces it.
* `theorem_7_5_2` — `H^s(2π)` is exactly the set of series (7.5.1) with `‖φ‖_{*,s} < ∞`.
* `theorem_7_5_2_norm_equiv` — for an integer `k ≥ 0` the norm `‖·‖_{*,k}` is equivalent to the
  classical `‖φ‖²_{H^k} = ∑_{j ≤ k} ‖φ^{(j)}‖²_{L²}`, with the constants `1` and `k + 1`;
  `classicalNormSq_ofSmooth` and `theorem_7_5_2_smooth` are the same statement on the function
  side, for a `2π`-periodic `C^k` function `f` and its coefficient sequence
  `PeriodicSobolev.ofSmooth`.
* `proposition_7_5_4`, `proposition_7_5_4_bound` — the Sobolev embedding for `s > 1/2`: the series
  converges to a continuous `2π`-periodic function, with (7.5.10) and (7.5.11).
* `proposition_7_5_5` — for `s > t` the space `H^s(2π)` is dense in `H^t(2π)` and the inclusion is
  compact.  This is also Exercise 7.5.1, which asks for its proof.
* `proposition_7_5_6` — **the trapezoidal rule is exponentially accurate on smooth periodic
  integrands**: `|I(φ) − T_k(φ)| ≤ √(4 π ζ(2 s)) k^{-s} ‖φ‖_{*,s}`, the bound (7.5.13).
* `theorem_7_5_7` — the trigonometric interpolant `𝓘_n φ` of degree `≤ n` at the `2n + 1`
  equispaced nodes satisfies `‖φ − 𝓘_n φ‖_{*,r} ≤ √(1 + 2 ζ(2 s)) n^{r − s} ‖φ‖_{*,s}` for
  `0 ≤ r ≤ s`, `s > 1/2`, the bound (7.5.15) with an explicit constant.
* `exercise_7_5_2` — the trigonometric polynomials `𝕋` of (7.5.4) are dense in `H^s(2π)` for every
  real `s`.
* `exercise_7_5_3` — Simpson's rule obeys the same bound, with the constant `(5/3) √(4 π ζ(2 s))`.
  The proof is that `S_{2k} = (4 T_{2k} − T_k)/3` on any function, so the two trapezoidal bounds
  combine.
* `exercise_7_5_4` — every element of `H^{-t}(2π)` is a bounded linear functional on `H^t(2π)`
  under the pairing (7.5.6), with `‖ℓ‖ ≤ ‖η‖_{*,-t}`.

* `definition_7_5_8` — §7.5.5's **spherical polynomials** `𝕊_N`, the restrictions to the unit
  sphere `U ⊆ ℝ³` of the polynomials in `(x, y, z)` of degree `≤ N`, with `equation_7_5_30`, the
  minimax error `ρ_N(g)`, and `equation_7_5_30_tendsto_zero`, the book's remark that `ρ_N(g) → 0`
  by Stone–Weierstraß. Nothing else of §7.5.5 is formalized; see below.

## Not formalized here

* **(7.5.3)–(7.5.5), the distributional derivative `𝒟`.**  Its coefficient description `𝒟 φ =
  i ∑ m a_m ψ_m` is what `theorem_7_5_2_norm_equiv` uses, in the form of the classical norm written
  on the Fourier side; the operator itself, its norm `1` and its unique extension from `𝕋` are not
  built, because nothing else here consumes them.

* **Example 7.5.3, the square wave and its Dirac comb.**  The `2π`-periodic square wave `φ`, equal
  to `0` on `((2k − 1)π, 2kπ)` and to `1` on `(2kπ, (2k + 1)π)`, has the Fourier series
  `1/2 − (i/π) ∑_{k ≥ 0} (2k + 1)^{-1} [e^{(2k+1)it} − e^{-(2k+1)it}]`, and its distributional
  derivative is the Dirac comb `∑_j (−1)^j δ(t − πj)`, where `δ` acts on `H^s(2π)` for `s > 1/2` by
  `δ[φ] = φ(0)`.  Half of the vocabulary is here: `PeriodicSobolev.dualPairing` reads `H^{-t}(2π)`
  as functionals on `H^t(2π)` (Exercise 7.5.4 above) and `PeriodicSobolev.eval` gives the point
  evaluation for `s > 1/2`, so `δ` is representable as the element of `H^{-t}(2π)` all of whose
  coefficients are `(2π)^{-1/2}`, and the square wave's coefficients come from `fourierCoeffOn` of
  a step function.  What is missing is the operator `𝒟 : H^s(2π) → H^{s-1}(2π)` of the bullet
  above and then the identity `𝒟 φ = ∑_j (−1)^j δ(· − πj)` in `H^{-t}(2π)`.  A coefficient-level
  statement — that `(i m) a_m` is the coefficient sequence of the comb — would be 150–250 lines
  once `𝒟` exists; the example is illustrative and nothing in the corpus depends on it.  Mathlib's
  `TemperedDistribution` lives on `ℝ^d` and gives no distributions on the circle.

* **§7.5.4**, the logarithmic-kernel operator `𝒜` of (7.5.16): the book obtains its symbol
  `a_m/|m|` from complex function theory that it does not reproduce.

* **Definition 7.5.9, the spherical harmonics, and (7.5.20)–(7.5.22).**  A spherical harmonic of
  degree `n` is the restriction to `U` of a polynomial in `(x, y, z)` that is harmonic and
  homogeneous of degree `n`; there are `2n + 1` linearly independent ones, the span `𝕊̂_N` of those
  of degree `n ≤ N` equals the `𝕊_N` of `definition_7_5_8` (7.5.20), `dim 𝕊_N = (N + 1)²`
  (7.5.21), and the standard `L²(U)`-orthonormal basis (7.5.22) is `S_n^1 = c_n L_n(cos θ)`,
  `S_n^{2m} = c_{n,m} L_n^m(cos θ) cos(m φ)` and `S_n^{2m+1} = c_{n,m} L_n^m(cos θ) sin(m φ)`, in
  terms of the Legendre polynomials `L_n` and the associated Legendre functions `L_n^m`.  The book
  quotes (7.5.20) and (7.5.21) from MacRobert [161, Chap. 7] without proof.  A faithful statement
  needs the space of homogeneous harmonic polynomials of degree `n` restricted to the sphere
  together with its dimension count `2n + 1`, the associated Legendre functions, and a surface
  measure on `S²` for the `L²(U)` orthonormality.  What exists:
  `Numlib/Analysis/HarmonicPolynomial` for the harmonic polynomials themselves, and
  `Numlib/Approximation/OrthogonalPolynomial` with the Legendre polynomials on `[−1, 1]` but no
  associated Legendre functions; `sphericalHarmonic` has zero occurrences in Mathlib and in
  `Numlib/`, and there is no surface measure on `S²` anywhere in the corpus — the boundary round's
  `Numlib/Analysis/Sobolev/Boundary/` builds one on `C¹` graph domains of `ℝ^d` and on polygons,
  not on a sphere.  That measure with its integration formula, the spherical harmonics and a
  convolution on the sphere are one shared harmonic-analysis project, two to three thousand lines,
  which `AtkinsonHan.Chapter14`'s Theorem 14.1.1 waits on as well.

* **Theorem 7.5.10, Ragozin's rate, and (7.5.32)–(7.5.33).**  For `g ∈ C^{k,γ}(U)` there are
  spherical polynomials `p_N` with `‖g − p_N‖_∞ = ρ_N(g)` and
  `ρ_N(g) ≤ c_k H_{k,γ}(g) N^{-(k+γ)}` for `N ≥ 1` (7.5.31), the constant `c_k` depending only on
  `k`; here `H_{k,γ}(g)` is the Hölder constant, uniform over the `k`-th order derivatives of `g`
  in local surface coordinates.  The `L²(U)` rate (7.5.32) and the uniform rate
  `‖g − P_N g‖_∞ ≤ c N^{-(k+γ-1/2)}` (7.5.33) follow at once, the latter through the projection
  norm `‖P_N‖ = (√(8/π) + δ_N) √N` of (7.5.29).  The book states all of this without proof, citing
  Gronwall [100] for `k = 0` and Ragozin [190, Theorem 3.3] in general.  Beyond Definition 7.5.9 it
  needs the Hölder spaces `C^{k,γ}(U)` on a sphere, which the corpus does not have either
  (`Numlib/Analysis/Sobolev/Slobodeckij` is on domains of `ℝ^d`; the local-coordinate setup the
  book itself declines to write out is Definition 7.2.13's atlas), and then Ragozin's Jackson-type
  argument, several pages of convolution on the sphere.  What *is* here is the book's own
  qualitative remark after (7.5.30), `equation_7_5_30_tendsto_zero`: `ρ_N(g) → 0` for every
  `g ∈ C(U)`, by Stone–Weierstraß.

* **The rest of §7.5.5** — the Laplace expansion (7.5.23)–(7.5.28), its orthogonal projection
  `P_N : L²(U) → 𝕊_N` and the norm (7.5.29), and the Sobolev spaces `H^r(U)` that close the
  subsection — rests on the same missing surface measure and spherical harmonics.

## References

[han2009theoretical] §7.5.
-/

open Filter Metric Set Topology Quadrature
open scoped ComplexConjugate ENNReal InnerProductSpace Real

namespace AtkinsonHan.Chapter07

/-! ### The normalization constant -/

/-- `1 ≤ √(2 π)`, so the book's `ψ_m` are bounded by `1` and the bounds below can be read either
with or without the normalization. -/
theorem one_le_sqrt_two_pi : (1 : ℝ) ≤ √(2 * π) := by
  rw [show (1 : ℝ) = √1 by simp]
  exact Real.sqrt_le_sqrt (by nlinarith [Real.two_le_pi])

theorem sqrt_two_pi_pos : 0 < √(2 * π) := by linarith [one_le_sqrt_two_pi]

theorem inv_sqrt_two_pi_le_one : (√(2 * π))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ one_le_sqrt_two_pi

/-- The book's orthonormal system `ψ_m x = (2 π)^{-1/2} e^{i m x}`. -/
noncomputable def psi (m : ℤ) (x : ℝ) : ℂ := (√(2 * π))⁻¹ * periodicChar (2 * π) m x

@[simp]
theorem norm_psi (m : ℤ) (x : ℝ) : ‖psi m x‖ = (√(2 * π))⁻¹ := by
  rw [psi, norm_mul, norm_periodicChar, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

variable {s t : ℝ}

/-- The sum of the book's series (7.5.1), `φ(x) = ∑_m a_m ψ_m(x)`. -/
noncomputable def eval (φ : PeriodicSobolev s) (x : ℝ) : ℂ :=
  (√(2 * π))⁻¹ * PeriodicSobolev.eval (2 * π) φ x

/-- `eval` is the book's series (7.5.1) against the book's orthonormal system. -/
theorem eval_eq_tsum (φ : PeriodicSobolev s) (x : ℝ) :
    eval φ x = ∑' m : ℤ, φ.coeff m * psi m x := by
  rw [eval, PeriodicSobolev.eval, ← tsum_mul_left]
  exact tsum_congr fun m => by rw [psi]; ring

/-! ### Definition 7.5.1 and Theorem 7.5.2 -/

/-- **Definition 7.5.1, the norm (7.5.2)**: `‖φ‖²_{*,s} = |a₀|² + ∑_{|m| > 0} |m|^{2 s} |a_m|²`. -/
theorem definition_7_5_1_norm (s : ℝ) (φ : PeriodicSobolev s) :
    HasSum (fun m : ℤ => if m = 0 then ‖φ.coeff 0‖ ^ 2
      else |(m : ℝ)| ^ (2 * s) * ‖φ.coeff m‖ ^ 2) (‖φ‖ ^ 2) := by
  refine (PeriodicSobolev.hasSum_norm_sq φ).congr_fun fun m => ?_
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [ite_eq_right hm, mul_pow, periodicSobolevWeight_sq s hm]

/-- **Definition 7.5.1, the inner product**: `(φ, ρ)_{*,s} = a₀ conj b₀ +
∑_{|m| > 0} |m|^{2 s} a_m conj b_m`. Mathlib's inner product is conjugate-linear in its *first*
argument, the opposite of the book's convention, so the book's `(φ, ρ)_{*,s}` is `⟪ρ, φ⟫`. -/
theorem definition_7_5_1_inner (s : ℝ) (φ ρ : PeriodicSobolev s) :
    (inner ℂ ρ φ : ℂ) = ∑' m : ℤ, (if m = 0 then φ.coeff 0 * conj (ρ.coeff 0)
      else (|(m : ℝ)| ^ (2 * s) : ℝ) * (φ.coeff m * conj (ρ.coeff m))) := by
  rw [PeriodicSobolev.inner_eq_tsum]
  refine tsum_congr fun m => ?_
  rcases eq_or_ne m 0 with rfl | hm
  · simp [mul_comm]
  · rw [ite_eq_right hm, ← Complex.ofReal_pow, periodicSobolevWeight_sq s hm]
    ring

/-- **Theorem 7.5.2, the characterization**: `H^s(2π)` is exactly the set of formal series (7.5.1)
whose coefficients make (7.5.2) finite. -/
theorem theorem_7_5_2 (s : ℝ) (a : ℤ → ℂ) :
    (∃ φ : PeriodicSobolev s, φ.coeff = a) ↔
      Summable fun m : ℤ => (periodicSobolevWeight s m * ‖a m‖) ^ 2 := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact (PeriodicSobolev.hasSum_norm_sq φ).summable
  · intro ha
    refine ⟨PeriodicSobolev.ofCoeff s a (memℓp_two_iff.2 (ha.congr fun m => ?_)),
      PeriodicSobolev.coeff_ofCoeff _ _ _⟩
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (periodicSobolevWeight_pos s m).le]

/-- The classical Sobolev norm of Definition 7.5.1, `‖φ‖²_{H^k} = ∑_{j ≤ k} ‖φ^{(j)}‖²_{L²}`,
written on the Fourier side.  Differentiation multiplies the `m`-th coefficient by `i m`, by
(7.5.3), and Parseval turns each `‖φ^{(j)}‖²_{L²}` into `∑_m |m|^{2 j} |a_m|²`; summing over
`j ≤ k` gives the expression below. -/
noncomputable def classicalNormSq (k : ℕ) (φ : PeriodicSobolev (k : ℝ)) : ℝ :=
  ∑' m : ℤ, (∑ j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * j)) * ‖φ.coeff m‖ ^ 2

/-- The symbol inequality behind the equivalence: `w_k(m)² ≤ ∑_{j ≤ k} |m|^{2 j} ≤ (k+1) w_k(m)²`,
where `w_k` is the weight of (7.5.2). -/
theorem weight_sq_le_sum_le (k : ℕ) (m : ℤ) :
    periodicSobolevWeight (k : ℝ) m ^ 2 ≤ ∑ j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * j) ∧
      ∑ j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * j)
        ≤ ((k : ℝ) + 1) * periodicSobolevWeight (k : ℝ) m ^ 2 := by
  rcases eq_or_ne m 0 with rfl | hm
  · have hone : ∑ j ∈ Finset.range (k + 1), |((0 : ℤ) : ℝ)| ^ (2 * j) = 1 := by
      rw [Finset.sum_eq_single 0]
      · norm_num
      · intro b _ hb
        have h2b : 2 * b ≠ 0 := by omega
        simp [h2b]
      · intro h
        exact absurd (Finset.mem_range.2 (Nat.succ_pos k)) h
    rw [hone, periodicSobolevWeight_zero, one_pow]
    exact ⟨le_rfl, by linarith [Nat.cast_nonneg (α := ℝ) k]⟩
  · have habs : (1 : ℝ) ≤ |(m : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast h1
        _ = |(m : ℝ)| := by rw [Int.cast_abs]
    have hw : periodicSobolevWeight (k : ℝ) m ^ 2 = |(m : ℝ)| ^ (2 * k) := by
      rw [periodicSobolevWeight_sq _ hm,
        show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    have hmono : ∀ j ∈ Finset.range (k + 1),
        |(m : ℝ)| ^ (2 * j) ≤ |(m : ℝ)| ^ (2 * k) := by
      intro j hj
      rw [Finset.mem_range] at hj
      exact pow_le_pow_right₀ habs (by omega)
    rw [hw]
    constructor
    · exact Finset.single_le_sum (f := fun j => |(m : ℝ)| ^ (2 * j))
        (fun j _ => by positivity) (Finset.self_mem_range_succ k)
    · calc ∑ j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * j)
          ≤ ∑ _j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * k) := Finset.sum_le_sum hmono
        _ = ((k : ℝ) + 1) * |(m : ℝ)| ^ (2 * k) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring

/-- **Theorem 7.5.2, the norm equivalence** for an integer `k ≥ 0`: `‖·‖_{*,k}` and the classical
`‖·‖_{H^k}` are equivalent, with the constants `1` and `k + 1`. -/
theorem theorem_7_5_2_norm_equiv (k : ℕ) (φ : PeriodicSobolev (k : ℝ)) :
    ‖φ‖ ^ 2 ≤ classicalNormSq k φ ∧ classicalNormSq k φ ≤ ((k : ℝ) + 1) * ‖φ‖ ^ 2 := by
  have hns := PeriodicSobolev.hasSum_norm_sq φ
  have hterm : ∀ m : ℤ, (periodicSobolevWeight (k : ℝ) m * ‖φ.coeff m‖) ^ 2
      = periodicSobolevWeight (k : ℝ) m ^ 2 * ‖φ.coeff m‖ ^ 2 := fun m => by ring
  have hns' : HasSum (fun m : ℤ => periodicSobolevWeight (k : ℝ) m ^ 2 * ‖φ.coeff m‖ ^ 2)
      (‖φ‖ ^ 2) := hns.congr_fun fun m => (hterm m).symm
  have hupper : HasSum (fun m : ℤ => (((k : ℝ) + 1) * periodicSobolevWeight (k : ℝ) m ^ 2)
      * ‖φ.coeff m‖ ^ 2) (((k : ℝ) + 1) * ‖φ‖ ^ 2) :=
    (hns'.mul_left ((k : ℝ) + 1)).congr_fun fun m => by ring
  have hnn : ∀ m : ℤ, (0 : ℝ) ≤ (∑ j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * j))
      * ‖φ.coeff m‖ ^ 2 := fun m =>
    mul_nonneg (Finset.sum_nonneg fun j _ => by positivity) (by positivity)
  have hmid : Summable fun m : ℤ =>
      (∑ j ∈ Finset.range (k + 1), |(m : ℝ)| ^ (2 * j)) * ‖φ.coeff m‖ ^ 2 := by
    refine Summable.of_nonneg_of_le hnn (fun m => ?_) hupper.summable
    exact mul_le_mul_of_nonneg_right (weight_sq_le_sum_le k m).2 (by positivity)
  refine ⟨?_, ?_⟩
  · rw [classicalNormSq, ← hns'.tsum_eq]
    refine hns'.summable.tsum_le_tsum (fun m => ?_) hmid
    exact mul_le_mul_of_nonneg_right (weight_sq_le_sum_le k m).1 (by positivity)
  · rw [classicalNormSq, ← hupper.tsum_eq]
    refine hmid.tsum_le_tsum (fun m => ?_) hupper.summable
    exact mul_le_mul_of_nonneg_right (weight_sq_le_sum_le k m).2 (by positivity)

/-- **The classical norm of a smooth periodic function on the Fourier side.** For a `2π`-periodic
`f` of class `C^k` with coefficient sequence `φ = PeriodicSobolev.ofSmooth hf hd`, the Fourier-side
expression `classicalNormSq k φ` is `(1/2π) ∑_{j ≤ k} ‖f^{(j)}‖²_{L²(0,2π)}`: Parseval for each
derivative, `f̂^{(j)}_m = (i m)^j f̂_m`. The factor `1/2π` is the book's normalization `ψ_m =
(2π)^{-1/2} e^{imx}`, under which `‖f‖²_{L²} = 2π ∑ |a_m|²`. -/
theorem classicalNormSq_ofSmooth {f : ℝ → ℂ} (hf : Function.Periodic f (2 * π)) {k : ℕ}
    (hd : ContDiff ℝ k f) :
    classicalNormSq k (PeriodicSobolev.ofSmooth hf hd)
      = (2 * π)⁻¹ * PeriodicSobolev.derivNormSq k f := by
  rw [classicalNormSq, PeriodicSobolev.coeff_ofSmooth]
  exact (PeriodicSobolev.hasSum_sum_abs_pow_mul_norm_fourierCoeff_lift_sq hf hd).tsum_eq

/-- **Theorem 7.5.2 on the function side**: for a `2π`-periodic `f` of class `C^k`, the norm
`‖·‖_{*,k}` of its coefficient sequence and the classical norm `‖f‖²_{H^k} = ∑_{j ≤ k}
‖f^{(j)}‖²_{L²(0,2π)}` are equivalent, `‖φ‖²_{*,k} ≤ (1/2π) ‖f‖²_{H^k} ≤ (k + 1) ‖φ‖²_{*,k}`. -/
theorem theorem_7_5_2_smooth {f : ℝ → ℂ} (hf : Function.Periodic f (2 * π)) {k : ℕ}
    (hd : ContDiff ℝ k f) :
    ‖PeriodicSobolev.ofSmooth hf hd‖ ^ 2 ≤ (2 * π)⁻¹ * PeriodicSobolev.derivNormSq k f ∧
      (2 * π)⁻¹ * PeriodicSobolev.derivNormSq k f
        ≤ ((k : ℝ) + 1) * ‖PeriodicSobolev.ofSmooth hf hd‖ ^ 2 := by
  rw [← classicalNormSq_ofSmooth hf hd]
  exact theorem_7_5_2_norm_equiv k _

/-! ### §7.5.2, the embedding results -/

/-- **The bound (7.5.10)**: `|φ(x)| ≤ |a₀| + √(2 ζ(2 s)) ‖φ‖_{*,s}` for `s > 1/2`. -/
theorem proposition_7_5_4_bound (hs : 1 / 2 < s) (φ : PeriodicSobolev s) (x : ℝ) :
    ‖eval φ x‖ ≤ ‖φ.coeff 0‖ + √(2 * zetaReal (2 * s)) * ‖φ‖ := by
  have hb := PeriodicSobolev.norm_eval_le_tsum_norm_coeff hs (2 * π) φ x
  have hle := PeriodicSobolev.tsum_norm_coeff_le hs φ
  rw [eval, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h1 : (√(2 * π))⁻¹ * ‖PeriodicSobolev.eval (2 * π) φ x‖
      ≤ 1 * ‖PeriodicSobolev.eval (2 * π) φ x‖ :=
    mul_le_mul_of_nonneg_right inv_sqrt_two_pi_le_one (norm_nonneg _)
  rw [one_mul] at h1
  linarith [hb.trans hle]

/-- **Proposition 7.5.4 at `k = 0`, with the bound (7.5.11)**: for `s > 1/2` the series (7.5.1)
converges to a continuous function of period `2 π`, and `‖φ‖_∞ ≤ [1 + √(2 ζ(2 s))] ‖φ‖_{*,s}`. -/
theorem proposition_7_5_4 (hs : 1 / 2 < s) (φ : PeriodicSobolev s) :
    Continuous (eval φ) ∧ Function.Periodic (eval φ) (2 * π) ∧
      ∀ x, ‖eval φ x‖ ≤ (1 + √(2 * zetaReal (2 * s))) * ‖φ‖ := by
  refine ⟨continuous_const.mul (PeriodicSobolev.continuous_eval hs (2 * π) φ),
    fun x => by rw [eval, eval, PeriodicSobolev.eval_periodic (by positivity) φ x], fun x => ?_⟩
  rw [eval, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h1 : (√(2 * π))⁻¹ * ‖PeriodicSobolev.eval (2 * π) φ x‖
      ≤ 1 * ‖PeriodicSobolev.eval (2 * π) φ x‖ :=
    mul_le_mul_of_nonneg_right inv_sqrt_two_pi_le_one (norm_nonneg _)
  rw [one_mul] at h1
  linarith [PeriodicSobolev.norm_eval_le hs (2 * π) φ x]

/-- **Proposition 7.5.5** (= Exercise 7.5.1): for `s > t` the identity map `H^s(2π) → H^t(2π)` has
dense range and is a compact operator. -/
theorem proposition_7_5_5 (h : t < s) :
    DenseRange (PeriodicSobolev.inclL h.le) ∧
      IsCompactOperator (PeriodicSobolev.inclL h.le) :=
  ⟨PeriodicSobolev.denseRange_inclL h.le, PeriodicSobolev.isCompactOperator_inclL h⟩

/-- **Exercise 7.5.1** asks for the proof of Proposition 7.5.5. -/
theorem exercise_7_5_1 (h : t < s) :
    DenseRange (PeriodicSobolev.inclL h.le) ∧
      IsCompactOperator (PeriodicSobolev.inclL h.le) :=
  proposition_7_5_5 h

/-- **Exercise 7.5.2**: the trigonometric polynomials `𝕋` of (7.5.4) — the finite linear
combinations of the `ψ_m`, equivalently the span of the coordinate series — are dense in
`H^s(2π)` for every real `s`. -/
theorem exercise_7_5_2 (s : ℝ) :
    Dense ((Submodule.span ℂ (Set.range (PeriodicSobolev.basisElt s)) :
      Submodule ℂ (PeriodicSobolev s)) : Set (PeriodicSobolev s)) :=
  PeriodicSobolev.dense_span_basisElt s

/-! ### §7.5.3, the approximation results -/

/-- `I(φ) = ∫_0^{2π} φ(x) dx`. -/
noncomputable def integral (φ : PeriodicSobolev s) : ℂ := ∫ x in (0 : ℝ)..(2 * π), eval φ x

/-- **(7.5.12)**, the trapezoidal rule `T_k(φ) = h ∑_{j=1}^{k} φ(j h)` with `h = 2π/k`. -/
noncomputable def trapezoid (k : ℕ) (φ : PeriodicSobolev s) : ℂ :=
  PeriodicSobolev.trapezoidSum (2 * π) k (eval φ)

private theorem trapezoidSum_const_mul (T : ℝ) (k : ℕ) (c : ℂ) (f : ℝ → ℂ) :
    PeriodicSobolev.trapezoidSum T k (fun x => c * f x)
      = c * PeriodicSobolev.trapezoidSum T k f := by
  rw [PeriodicSobolev.trapezoidSum, PeriodicSobolev.trapezoidSum, ← Finset.mul_sum]
  ring

/-- The quadrature error in the book's normalization is `(2 π)^{-1/2}` times the backbone's. -/
theorem integral_sub_trapezoid (φ : PeriodicSobolev s) (k : ℕ) :
    integral φ - trapezoid k φ = (√(2 * π))⁻¹ *
      ((∫ x in (0 : ℝ)..(2 * π), PeriodicSobolev.eval (2 * π) φ x)
        - PeriodicSobolev.trapezoidSum (2 * π) k (PeriodicSobolev.eval (2 * π) φ)) := by
  have h1 : integral φ = (√(2 * π))⁻¹ * ∫ x in (0 : ℝ)..(2 * π),
      PeriodicSobolev.eval (2 * π) φ x := by
    rw [integral]
    simp only [eval]
    rw [intervalIntegral.integral_const_mul]
  have h2 : trapezoid k φ = (√(2 * π))⁻¹ *
      PeriodicSobolev.trapezoidSum (2 * π) k (PeriodicSobolev.eval (2 * π) φ) := by
    rw [trapezoid, show eval φ = fun x => (√(2 * π))⁻¹ *
      PeriodicSobolev.eval (2 * π) φ x from rfl, trapezoidSum_const_mul]
  rw [h1, h2, mul_sub]

/-- **Proposition 7.5.6, the bound (7.5.13)**: the trapezoidal rule converges at the rate `k^{-s}`
on `H^s(2π)`, so for a smooth periodic integrand it is spectrally accurate.

`|I(φ) − T_k(φ)| ≤ √(4 π ζ(2 s)) k^{-s} ‖φ‖_{*,s}`.

This is the reason the trapezoidal rule is the method of choice for periodic integrands. -/
theorem proposition_7_5_6 (hs : 1 / 2 < s) {k : ℕ} (hk : 0 < k) (φ : PeriodicSobolev s) :
    ‖integral φ - trapezoid k φ‖ ≤ √(4 * π * zetaReal (2 * s)) * (k : ℝ) ^ (-s) * ‖φ‖ := by
  have hbb := PeriodicSobolev.norm_intervalIntegral_sub_trapezoidSum_le hs
    (by positivity : (0 : ℝ) < 2 * π) hk φ
  have hsq : √(2 * π) * √(2 * π) = 2 * π := Real.mul_self_sqrt (by positivity)
  have h4 : √(4 * π * zetaReal (2 * s)) = √(2 * π) * √(2 * zetaReal (2 * s)) := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * π)]
    congr 1
    ring
  rw [integral_sub_trapezoid, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  refine le_trans (mul_le_mul_of_nonneg_left hbb (by positivity)) (le_of_eq ?_)
  calc (√(2 * π))⁻¹ * (2 * π * ((k : ℝ) ^ (-s) * √(2 * zetaReal (2 * s)) * ‖φ‖))
      = ((√(2 * π))⁻¹ * (√(2 * π) * √(2 * π)))
        * ((k : ℝ) ^ (-s) * √(2 * zetaReal (2 * s)) * ‖φ‖) := by rw [hsq]; ring
    _ = √(2 * π) * ((k : ℝ) ^ (-s) * √(2 * zetaReal (2 * s)) * ‖φ‖) := by
        rw [inv_mul_cancel_left₀ (ne_of_gt sqrt_two_pi_pos)]
    _ = √(4 * π * zetaReal (2 * s)) * (k : ℝ) ^ (-s) * ‖φ‖ := by rw [h4]; ring

/-- **Theorem 7.5.7, the trigonometric interpolation bound (7.5.15).** For `s > 1/2`,
`φ ∈ H^s(2π)`, `0 ≤ r ≤ s` and `n ≥ 1`, the trigonometric interpolant `𝓘_n φ` — the
trigonometric polynomial of degree `≤ n` that agrees with `φ` at the `2n + 1` equispaced nodes
`t_j = 2πj/(2n+1)` of §3.7, here `PeriodicSobolev.trigInterp r n φ`, read in `H^r(2π)` — satisfies

`‖φ − 𝓘_n φ‖_{*,r} ≤ c n^{r − s} ‖φ‖_{*,s}` with `c = √(1 + 2 ζ(2 s))`.

The first conjunct is the interpolation property that defines `𝓘_n φ`; the second is (7.5.15).
The book refers to Kress for the proof, which is the aliasing argument of
`Numlib/Analysis/Fourier/Aliasing`: the Fourier coefficients of `𝓘_n φ` on the window `-n, …, n`
are `a_m + ∑_{j ≠ 0} a_{m + j(2n+1)}` and vanish outside it, and Cauchy–Schwarz against
`∑_{j ≠ 0} |m + j(2n+1)|^{-2s}` bounds the aliasing tails. The book's constant `c` depends on
`s` and `r` only; ours depends on `s` alone. -/
theorem theorem_7_5_7 (hs : 1 / 2 < s) {r : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) {n : ℕ} (hn : 1 ≤ n)
    (φ : PeriodicSobolev s) :
    (∀ j < 2 * n + 1, eval (PeriodicSobolev.trigInterp r n φ) (angleNode (2 * n + 1) j)
        = eval φ (angleNode (2 * n + 1) j)) ∧
      ‖PeriodicSobolev.incl hrs φ - PeriodicSobolev.trigInterp r n φ‖
        ≤ √(1 + 2 * zetaReal (2 * s)) * (n : ℝ) ^ (r - s) * ‖φ‖ :=
  ⟨fun j hj => by rw [eval, eval, PeriodicSobolev.eval_trigInterp_angleNode r n φ hj],
    PeriodicSobolev.norm_incl_sub_trigInterp_le hs hr hrs hn φ⟩

/-- **Simpson's rule** on one period at `2 k` equally spaced points, `h = π / k`:
`S_{2k}(φ) = (h/3) [4 ∑_{j=1}^{k} φ(x_{2j-1}) + 2 ∑_{j=1}^{k} φ(x_{2j})]` with `x_i = i h`. For a
periodic integrand the two endpoints coincide, so the end weights `1` merge into the weight `2` at
`x_{2k}` and the rule is the plain alternating pattern below. -/
noncomputable def simpson (k : ℕ) (φ : PeriodicSobolev s) : ℂ :=
  ((π / k : ℝ) / 3 : ℝ) *
    (4 * ∑ j ∈ Finset.range k, eval φ ((2 * (j : ℝ) + 1) * (π / k))
      + 2 * ∑ j ∈ Finset.range k, eval φ ((2 * (j : ℝ) + 2) * (π / k)))

private theorem sum_range_two_mul (f : ℕ → ℂ) (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k), f i = ∑ j ∈ Finset.range k, (f (2 * j) + f (2 * j + 1)) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

/-- Simpson's rule on a period is the Richardson combination `(4 T_{2k} − T_k)/3` of the two
trapezoidal rules it refines. This identity holds for any function whatever; it is what turns the
trapezoidal bound (7.5.13) into the Simpson bound. -/
theorem simpson_eq (k : ℕ) (hk : 0 < k) (φ : PeriodicSobolev s) :
    simpson k φ = (4 * trapezoid (2 * k) φ - trapezoid k φ) / 3 := by
  have hkR : ((k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hstep2 : 2 * π / ((2 * k : ℕ) : ℝ) = π / (k : ℝ) := by push_cast; field_simp
  have hstep1 : 2 * π / ((k : ℕ) : ℝ) = 2 * (π / (k : ℝ)) := by ring
  have hT2 : trapezoid (2 * k) φ
      = ((π / (k : ℝ) : ℝ) : ℂ)
        * ∑ i ∈ Finset.range (2 * k), eval φ (((i : ℝ) + 1) * (π / (k : ℝ))) := by
    rw [trapezoid, PeriodicSobolev.trapezoidSum, hstep2]
  have hT1 : trapezoid k φ
      = ((2 * (π / (k : ℝ)) : ℝ) : ℂ)
        * ∑ j ∈ Finset.range k, eval φ ((2 * (j : ℝ) + 2) * (π / (k : ℝ))) := by
    rw [trapezoid, PeriodicSobolev.trapezoidSum, hstep1]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => congrArg (eval φ) (by ring))
  have hsplit : ∑ i ∈ Finset.range (2 * k), eval φ (((i : ℝ) + 1) * (π / (k : ℝ)))
      = (∑ j ∈ Finset.range k, eval φ ((2 * (j : ℝ) + 1) * (π / (k : ℝ))))
        + ∑ j ∈ Finset.range k, eval φ ((2 * (j : ℝ) + 2) * (π / (k : ℝ))) := by
    rw [sum_range_two_mul (fun i => eval φ (((i : ℝ) + 1) * (π / (k : ℝ)))) k,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ((2 * j : ℕ) : ℝ) + 1 = 2 * (j : ℝ) + 1 by push_cast; ring,
      show ((2 * j + 1 : ℕ) : ℝ) + 1 = 2 * (j : ℝ) + 2 by push_cast; ring]
  rw [simpson, hT2, hT1, hsplit]
  push_cast
  ring

/-- **Exercise 7.5.3**: Simpson's rule obeys the same `k^{-s}` bound as the trapezoidal rule, with
the constant `(5/3) √(4 π ζ(2 s))`. Since `S_{2k} = (4 T_{2k} − T_k)/3`, the error is
`(4 (I − T_{2k}) − (I − T_k))/3`, and `(2k)^{-s} ≤ k^{-s}`. -/
theorem exercise_7_5_3 (hs : 1 / 2 < s) {k : ℕ} (hk : 0 < k) (φ : PeriodicSobolev s) :
    ‖integral φ - simpson k φ‖ ≤ 5 / 3 * √(4 * π * zetaReal (2 * s)) * (k : ℝ) ^ (-s) * ‖φ‖ := by
  have hspos : (0 : ℝ) < s := by linarith
  have h2k : (0 : ℕ) < 2 * k := by omega
  have hb1 := proposition_7_5_6 hs hk φ
  have hb2 := proposition_7_5_6 hs h2k φ
  have hrate : ((2 * k : ℕ) : ℝ) ^ (-s) ≤ (k : ℝ) ^ (-s) := by
    have hkp : (0 : ℝ) < (k : ℝ) ^ s :=
      Real.rpow_pos_of_pos (by exact_mod_cast hk) s
    have hle : (k : ℝ) ^ s ≤ ((2 * k : ℕ) : ℝ) ^ s :=
      Real.rpow_le_rpow (by positivity)
        (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]) hspos.le
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), inv_eq_one_div,
      inv_eq_one_div]
    exact one_div_le_one_div_of_le hkp hle
  have hb2' : ‖integral φ - trapezoid (2 * k) φ‖
      ≤ √(4 * π * zetaReal (2 * s)) * (k : ℝ) ^ (-s) * ‖φ‖ := by
    refine hb2.trans ?_
    have := mul_le_mul_of_nonneg_left hrate (Real.sqrt_nonneg (4 * π * zetaReal (2 * s)))
    exact mul_le_mul_of_nonneg_right this (norm_nonneg φ)
  have hsplit : integral φ - simpson k φ
      = (4 * (integral φ - trapezoid (2 * k) φ) - (integral φ - trapezoid k φ)) / 3 := by
    rw [simpson_eq k hk φ]
    ring
  rw [hsplit, norm_div, Complex.norm_ofNat]
  have hnum : ‖4 * (integral φ - trapezoid (2 * k) φ) - (integral φ - trapezoid k φ)‖
      ≤ 4 * ‖integral φ - trapezoid (2 * k) φ‖ + ‖integral φ - trapezoid k φ‖ := by
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [norm_mul]
    norm_num
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
  linarith

/-- **Exercise 7.5.4**: for `t > 0` every element `η` of `H^{-t}(2π)` is a bounded linear functional
on `H^t(2π)` under the pairing (7.5.6), `ℓ[φ] = ∑_m a_m conj (b_m)`, with `‖ℓ‖ ≤ ‖η‖_{*,-t}`. -/
theorem exercise_7_5_4 (t : ℝ) (η : PeriodicSobolev (-t)) :
    (∀ φ : PeriodicSobolev t,
        PeriodicSobolev.dualPairing t η φ = ∑' m : ℤ, φ.coeff m * conj (η.coeff m)) ∧
      ‖PeriodicSobolev.dualPairing t η‖ ≤ ‖η‖ :=
  ⟨fun _ => rfl, PeriodicSobolev.norm_dualPairing_le t η⟩

/-! ### §7.5.5: spherical polynomials

Definition 7.5.8 and the minimax error (7.5.30), and nothing else of §7.5.5.  What follows them in
the book — the spherical harmonics of Definition 7.5.9, the identity `𝕊̂_N = 𝕊_N` (7.5.20), the
dimension count `dim 𝕊_N = (N + 1)²` (7.5.21), the orthonormal basis (7.5.22) and Ragozin's rate
(7.5.31) — is **not** formalized; the module doc says what each would need.  What *is* here is the
definition as the book writes it and the one thing the book proves about it, that `ρ_N(g) → 0` by
Stone–Weierstraß.

The machinery of that convergence is general — the polynomial functions on a compact `D ⊆ ℝ^ι`
form a subalgebra of `C(D, ℝ)` separating points — and belongs in
`Numlib/Approximation/MvPolynomial` beside `Approximation.mvPolyLE`; it is private here because
§7.5.5 is its only consumer so far.
-/

section StoneWeierstrass

variable {ι : Type*} (D : Set (ι → ℝ))

/-- Restriction to `D` is multiplicative.  `Approximation.toContinuousMapOn` is packaged as a
linear map, so this is the one algebra fact the subalgebra below needs. -/
private theorem toContinuousMapOn_mul (p q : MvPolynomial ι ℝ) :
    Approximation.toContinuousMapOn D (p * q) =
      Approximation.toContinuousMapOn D p * Approximation.toContinuousMapOn D q := by
  ext x; simp

/-- The polynomial functions on `D` as a subalgebra of `C(D, ℝ)`: the union of the subspaces
`Approximation.mvPolyLE D N`, which is a subspace because the family is monotone and closed under
multiplication because `totalDegree (p q) ≤ totalDegree p + totalDegree q`. -/
private noncomputable def polyAlgebra : Subalgebra ℝ C(D, ℝ) where
  carrier := {f | ∃ N, f ∈ Approximation.mvPolyLE D N}
  mul_mem' := by
    rintro f g ⟨N, hf⟩ ⟨M, hg⟩
    rw [Approximation.mem_mvPolyLE_iff] at hf hg
    obtain ⟨p, hp, rfl⟩ := hf
    obtain ⟨q, hq, rfl⟩ := hg
    refine ⟨N + M, Approximation.mem_mvPolyLE_iff.2
      ⟨p * q, ?_, toContinuousMapOn_mul D p q⟩⟩
    exact (MvPolynomial.totalDegree_mul p q).trans (Nat.add_le_add hp hq)
  add_mem' := by
    rintro f g ⟨N, hf⟩ ⟨M, hg⟩
    exact ⟨max N M, Submodule.add_mem _ (Approximation.mvPolyLE_mono (le_max_left N M) hf)
      (Approximation.mvPolyLE_mono (le_max_right N M) hg)⟩
  algebraMap_mem' r := ⟨0, Approximation.mem_mvPolyLE_iff.2
    ⟨MvPolynomial.C r, by simp, by ext x; simp⟩⟩

/-- The polynomial functions separate the points of `D`: two distinct points differ in some
coordinate, and the coordinate is a polynomial of degree one. -/
private theorem polyAlgebra_separatesPoints : (polyAlgebra D).SeparatesPoints := by
  rintro x y hxy
  have hne : (x : ι → ℝ) ≠ (y : ι → ℝ) := fun h => hxy (Subtype.ext h)
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  refine ⟨_, ⟨Approximation.toContinuousMapOn D (MvPolynomial.X i), ⟨1, ?_⟩, rfl⟩, ?_⟩
  · exact Approximation.mem_mvPolyLE_iff.2 ⟨MvPolynomial.X i, by simp, rfl⟩
  · simpa using hi

/-- **Stone–Weierstraß on a compact `D ⊆ ℝ^ι`**: every continuous function on `D` is uniformly
within `ε` of a polynomial of some degree. -/
private theorem exists_mem_mvPolyLE_near [CompactSpace D] (g : C(D, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∃ f ∈ Approximation.mvPolyLE D N, ‖f - g‖ < ε := by
  obtain ⟨f, hf⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    (polyAlgebra D) (polyAlgebra_separatesPoints D) g ε hε
  obtain ⟨N, hN⟩ := f.2
  exact ⟨N, f, hN, hf⟩

end StoneWeierstrass

/-- The book's unit sphere `U = {(x, y, z) : x² + y² + z² = 1} ⊆ ℝ³` of §7.5.5, written as a set of
coordinate vectors so that `MvPolynomial.eval` applies to its points directly.  The sup norm of
`Fin 3 → ℝ` induces the same topology as the Euclidean one, so `C(U, ℝ)` is the book's `C(U)`. -/
def unitSphere : Set (Fin 3 → ℝ) := {x | ∑ i, x i ^ 2 = 1}

theorem mem_unitSphere_iff {x : Fin 3 → ℝ} : x ∈ unitSphere ↔ ∑ i, x i ^ 2 = 1 := Iff.rfl

theorem isClosed_unitSphere : IsClosed unitSphere :=
  isClosed_eq (by fun_prop) continuous_const

theorem unitSphere_subset_closedBall : unitSphere ⊆ closedBall 0 1 := by
  intro x hx
  have hx' : ∑ j, x j ^ 2 = 1 := hx
  rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have hle : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  rw [hx'] at hle
  rw [Real.norm_eq_abs]
  nlinarith [abs_nonneg (x i), sq_abs (x i)]

/-- `U` is compact: it is closed, and contained in the unit cube. -/
theorem isCompact_unitSphere : IsCompact unitSphere :=
  Metric.isCompact_of_isClosed_isBounded isClosed_unitSphere
    (Metric.isBounded_closedBall.subset unitSphere_subset_closedBall)

instance compactSpace_unitSphere : CompactSpace unitSphere :=
  isCompact_iff_compactSpace.1 isCompact_unitSphere

/-- **Definition 7.5.8**: `𝕊_N`, the **spherical polynomials of degree `≤ N`** — the restrictions
to the unit sphere `U ⊆ ℝ³` of the polynomials (7.5.19) in `(x, y, z)` of total degree at most `N`.
It is a subspace of `C(U, ℝ)` because restriction is linear, and this is
`Approximation.mvPolyLE` at `D = U`, the same construction that gives `Π_n^d ⊆ C(D, ℝ)` in
chapter 14.

Only the definition and the minimax error (7.5.30) below are formalized.  The rest of §7.5.5 is
not: **Definition 7.5.9** (the spherical harmonics, the span `𝕊̂_N` of those of degree `≤ N`, the
identity `𝕊̂_N = 𝕊_N` of (7.5.20) and the count `dim 𝕊_N = (N + 1)²` of (7.5.21), which the book
quotes from MacRobert without proof) and **Theorem 7.5.10** (Ragozin's rate
`ρ_N(g) ≤ c_k H_{k,γ}(g) N^{-(k+γ)}`, also quoted without proof).  `finrank_definition_7_5_8_le`
is therefore an inequality where the book has the equality (7.5.21): the bound is the dimension of
the polynomials upstairs, and the gap between the two is exactly the harmonic decomposition that
is missing.  See the module doc. -/
noncomputable def definition_7_5_8 (N : ℕ) : Submodule ℝ C(unitSphere, ℝ) :=
  Approximation.mvPolyLE unitSphere N

/-- Definition 7.5.8 read out: `f ∈ 𝕊_N` exactly when `f` is the restriction to `U` of a polynomial
in `(x, y, z)` of total degree at most `N`. -/
theorem mem_definition_7_5_8 {N : ℕ} {f : C(unitSphere, ℝ)} :
    f ∈ definition_7_5_8 N ↔ ∃ p : MvPolynomial (Fin 3) ℝ, p.totalDegree ≤ N ∧
      ∀ x : unitSphere, f x = MvPolynomial.eval (x : Fin 3 → ℝ) p := by
  rw [definition_7_5_8, Approximation.mem_mvPolyLE_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, fun _ => rfl⟩
  · rintro ⟨p, hp, hf⟩
    exact ⟨p, hp, by ext x; exact (hf x).symm⟩

/-- `𝕊_N ⊆ 𝕊_M` for `N ≤ M`. -/
theorem definition_7_5_8_mono : Monotone definition_7_5_8 := fun _ _ h =>
  Approximation.mvPolyLE_mono h

/-- The constants belong to every `𝕊_N`, `𝕊_0` being exactly the constants. -/
theorem const_mem_definition_7_5_8 (c : ℝ) (N : ℕ) :
    ContinuousMap.const unitSphere c ∈ definition_7_5_8 N :=
  mem_definition_7_5_8.2 ⟨MvPolynomial.C c, by simp, by simp⟩

instance finiteDimensional_definition_7_5_8 (N : ℕ) :
    FiniteDimensional ℝ (definition_7_5_8 N) :=
  inferInstanceAs (Module.Finite ℝ ((MvPolynomial.restrictTotalDegree (Fin 3) ℝ N).map
    (Approximation.toContinuousMapOn unitSphere)))

/-- `dim 𝕊_N ≤ C(N + 3, 3)`, the dimension of the polynomials of degree `≤ N` in three variables,
because `𝕊_N` is their image under restriction.  The book's (7.5.21) is the *equality*
`dim 𝕊_N = (N + 1)²`, which is smaller — restriction to `U` has a large kernel, by
`not_injective_toContinuousMapOn_unitSphere` — and is not formalized: it needs the decomposition
into spherical harmonics of Definition 7.5.9. -/
theorem finrank_definition_7_5_8_le (N : ℕ) :
    Module.finrank ℝ (definition_7_5_8 N) ≤ (N + 3).choose 3 := by
  have h := Submodule.finrank_map_le (Approximation.toContinuousMapOn unitSphere)
    (MvPolynomial.restrictTotalDegree (Fin 3) ℝ N)
  have he := MvPolynomial.finrank_restrictTotalDegree (Fin 3) N ℝ
  simp only [Fintype.card_fin] at he
  rw [he] at h
  exact h

/-- The book's remark after Definition 7.5.8: `x² + y² + z²` reduces to `1` on `U`, so a polynomial
of degree `N` may restrict to a spherical polynomial of lower degree. -/
theorem toContinuousMapOn_normSq_unitSphere :
    Approximation.toContinuousMapOn unitSphere
      (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 + MvPolynomial.X 2 ^ 2) = 1 := by
  ext x
  have hx : ∑ i, (x : Fin 3 → ℝ) i ^ 2 = 1 := x.2
  rw [Fin.sum_univ_three] at hx
  change MvPolynomial.eval (x : Fin 3 → ℝ)
      (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 + MvPolynomial.X 2 ^ 2) = 1
  simp only [map_add, map_pow, MvPolynomial.eval_X]
  linarith

/-- The same remark as a statement about the map: restriction to `U` is **not** injective, since
`x² + y² + z² − 1` is a nonzero polynomial that restricts to `0`.  This is why
`Approximation.finrank_mvPolyLE`, which needs `D` to have nonempty interior, does not apply to `U`
and why `finrank_definition_7_5_8_le` is an inequality. -/
theorem not_injective_toContinuousMapOn_unitSphere :
    ¬ Function.Injective (Approximation.toContinuousMapOn unitSphere) := by
  intro h
  have key : (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 + MvPolynomial.X 2 ^ 2
      : MvPolynomial (Fin 3) ℝ) = MvPolynomial.C 1 := by
    apply h
    rw [toContinuousMapOn_normSq_unitSphere]
    ext x
    simp
  have h0 := congrArg (MvPolynomial.eval (fun _ => (0 : ℝ))) key
  simp at h0

/-- **(7.5.30)**: the **minimax error** `ρ_N(g) = inf_{p ∈ 𝕊_N} ‖g − p‖_∞` of the approximation of
`g ∈ C(U)` by spherical polynomials of degree `≤ N`, as the distance from `g` to `𝕊_N` in
`C(U, ℝ)`. -/
noncomputable def equation_7_5_30 (N : ℕ) (g : C(unitSphere, ℝ)) : ℝ :=
  Metric.infDist g (definition_7_5_8 N : Set C(unitSphere, ℝ))

theorem equation_7_5_30_nonneg (N : ℕ) (g : C(unitSphere, ℝ)) : 0 ≤ equation_7_5_30 N g :=
  Metric.infDist_nonneg

/-- `ρ_N(g)` decreases in `N`, the spaces `𝕊_N` increasing. -/
theorem equation_7_5_30_antitone (g : C(unitSphere, ℝ)) :
    Antitone fun N => equation_7_5_30 N g := fun _ _ h =>
  Metric.infDist_le_infDist_of_subset (definition_7_5_8_mono h) ⟨0, Submodule.zero_mem _⟩

/-- **The convergence the book records after (7.5.30)**: `ρ_N(g) → 0` as `N → ∞` for every
`g ∈ C(U)`, "using the Stone-Weierstraß theorem, Theorem 3.1.2".  The polynomial functions on `U`
form a subalgebra of `C(U, ℝ)` that contains the constants and separates points, so it is dense;
each of its elements lies in some `𝕊_N`, and `ρ_N(g)` is antitone.

This is the qualitative half of **Theorem 7.5.10**, whose rate `ρ_N(g) ≤ c_k H_{k,γ}(g)
N^{-(k+γ)}` for `g ∈ C^{k,γ}(U)` is *not* formalized: the book quotes it from Gronwall and Ragozin
without proof, and it needs both the Hölder spaces `C^{k,γ}(U)` on a sphere and the spherical
harmonics of Definition 7.5.9.  See the module doc. -/
theorem equation_7_5_30_tendsto_zero (g : C(unitSphere, ℝ)) :
    Tendsto (fun N => equation_7_5_30 N g) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, f, hfN, hf⟩ := exists_mem_mvPolyLE_near unitSphere g hε
  refine ⟨N, fun n hn => ?_⟩
  have h1 : equation_7_5_30 N g ≤ ‖f - g‖ := by
    have hmem : f ∈ (definition_7_5_8 N : Set C(unitSphere, ℝ)) := hfN
    have := Metric.infDist_le_dist_of_mem (x := g) hmem
    rwa [dist_eq_norm, norm_sub_rev] at this
  have h2 : equation_7_5_30 n g ≤ equation_7_5_30 N g := equation_7_5_30_antitone g hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (equation_7_5_30_nonneg n g)]
  linarith

end AtkinsonHan.Chapter07
