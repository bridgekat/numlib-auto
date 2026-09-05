/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.RingTheory.Polynomial.Chebyshev`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Numlib.RingTheory.Polynomial.ChebyshevMinimax

/-!
# Chebyshev polynomials on circles and ellipses

Zarantonello's lemma and the complex min–max estimates on an ellipse.

The Joukowski map `J w = (w + w⁻¹)/2` carries the circle of radius `ρ` about the origin onto an
ellipse with foci `±1` and semi-axes `(ρ ± ρ⁻¹)/2`, and carries `w ↦ w^k` to the Chebyshev
polynomial: `T_k (J w) = (w^k + w^{-k})/2`. Everything here follows from that identity and from
the maximum modulus principle.

* `Polynomial.zarantonello`: among the complex polynomials of degree at most `k` normalized by
  `p γ = 1`, the least attainable maximum modulus on the circle of radius `ρ < ‖γ‖` is
  `(ρ/‖γ‖)^k`, attained by `(X/γ)^k`.
* `Polynomial.Chebyshev.sSup_norm_eval_T_ellipse`: the maximum of `|T_k|` on the ellipse
  `Set.ellipse 0 1 ρ` is `(ρ^k + ρ^{-k})/2`.
* `Polynomial.Chebyshev.ellipse_minimax_bounds`: the two-sided estimate of the same min–max value
  on an ellipse, which is the source of the Chebyshev convergence bound for a Krylov method whose
  spectrum is enclosed in an ellipse.
* `Polynomial.Chebyshev.sSup_norm_eval_shiftedComplex_ellipse`: the maximum on the ellipse
  `Set.ellipse c d ρ` of the shifted, normalized Chebyshev polynomial
  `Ĉ_k(z) = T_k((c - z)/d) / T_k((c - γ)/d)`, namely `T_k(a/d)/|T_k((c - γ)/d)|` where
  `a = d (ρ + ρ⁻¹)/2` is the semi-major axis.

## References

* Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003,
  §6.11.2 (Lemma 6.26, Theorem 6.27, (6.115)–(6.121)).
* Yousef Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition, SIAM, 2011,
  §4.4 (Lemma 4.3, Theorem 4.9).
-/

open Polynomial Polynomial.Chebyshev

namespace Complex

/-- The Joukowski map `w ↦ (w + w⁻¹)/2`. It carries the circle of radius `ρ` about the origin
onto the ellipse with foci `±1` and semi-axes `(ρ + ρ⁻¹)/2` and `(ρ - ρ⁻¹)/2`, and it is the
change of variable that turns the Chebyshev polynomial `T_k` into `w ↦ (w^k + w^{-k})/2`. -/
noncomputable def joukowski (w : ℂ) : ℂ := (w + w⁻¹) / 2

theorem joukowski_def (w : ℂ) : joukowski w = (w + w⁻¹) / 2 := rfl

/-- The Joukowski map identifies `w` with `w⁻¹`; this is why the inside of an ellipse is covered
twice by the annulus of the parameters. -/
@[simp]
theorem joukowski_inv (w : ℂ) : joukowski w⁻¹ = joukowski w := by
  rw [joukowski_def, joukowski_def, inv_inv, add_comm]

/-- `J w = (w² + 1)/(2w)` away from the origin: the form that exhibits `w^k · p(J w)` as a
polynomial in `w`. -/
theorem joukowski_eq_div {w : ℂ} (hw : w ≠ 0) : joukowski w = (w ^ 2 + 1) / (2 * w) := by
  rw [joukowski_def]
  field_simp

/-- The Joukowski map is continuous away from the origin, its only singularity. -/
theorem continuousAt_joukowski {w : ℂ} (hw : w ≠ 0) : ContinuousAt joukowski w := by
  have h : ContinuousAt (fun z : ℂ => (z + z⁻¹) / 2) w :=
    (continuousAt_id.add (continuousAt_inv₀ hw)).div_const 2
  exact h

end Complex

/-- The ellipse with centre `c`, focal semi-distance `d` and Joukowski parameter `ρ`: the image
of the circle of radius `ρ` about the origin under `w ↦ c + d · J w`. For `d ≠ 0` and `ρ ≥ 1` it
is the ellipse with foci `c ± d`, semi-major axis `d (ρ + ρ⁻¹)/2` and semi-minor axis
`d (ρ - ρ⁻¹)/2`; `Set.ellipse 0 1 ρ` is the ellipse `E_ρ` with foci `±1`. -/
noncomputable def Set.ellipse (c d : ℂ) (ρ : ℝ) : Set ℂ :=
  (fun w => c + d * Complex.joukowski w) '' Metric.sphere 0 ρ

theorem Set.ellipse_def (c d : ℂ) (ρ : ℝ) :
    Set.ellipse c d ρ = (fun w => c + d * Complex.joukowski w) '' Metric.sphere 0 ρ := rfl

theorem Set.mem_ellipse {c d z : ℂ} {ρ : ℝ} :
    z ∈ Set.ellipse c d ρ ↔ ∃ w : ℂ, ‖w‖ = ρ ∧ z = c + d * Complex.joukowski w := by
  simp only [Set.ellipse_def, Set.mem_image, mem_sphere_zero_iff_norm]
  exact ⟨fun ⟨w, hw, h⟩ => ⟨w, hw, h.symm⟩, fun ⟨w, hw, h⟩ => ⟨w, hw, h.symm⟩⟩

/-- An ellipse is compact, being the image of a circle under a map continuous away from the
origin. -/
theorem Set.isCompact_ellipse (c d : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    IsCompact (Set.ellipse c d ρ) := by
  refine (isCompact_sphere (0 : ℂ) ρ).image_of_continuousOn (fun w hw => ?_)
  rw [mem_sphere_zero_iff_norm] at hw
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    exact absurd hw.symm hρ.ne'
  exact (continuousAt_const.add
    (continuousAt_const.mul (Complex.continuousAt_joukowski hw0))).continuousWithinAt

/-- The vertex `c + d (ρ + ρ⁻¹)/2` of the ellipse, the point at which the Chebyshev maxima
below are attained. -/
theorem Set.vertex_mem_ellipse (c d : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    c + d * Complex.joukowski (ρ : ℂ) ∈ Set.ellipse c d ρ :=
  ⟨(ρ : ℂ), by simp [abs_of_nonneg hρ], rfl⟩

namespace Polynomial

/-- The set of the maxima over `K` of the moduli of the complex polynomials of degree at most `k`
that are normalized to take the value `1` at `γ`: the competitors in the Chebyshev min–max
problem on `K`. -/
def normalizedSupNorms (k : ℕ) (γ : ℂ) (K : Set ℂ) : Set ℝ :=
  {M | ∃ p : ℂ[X], p.degree ≤ k ∧ p.eval γ = 1 ∧ M = sSup ((fun z => ‖p.eval z‖) '' K)}

theorem mem_normalizedSupNorms {k : ℕ} {γ : ℂ} {K : Set ℂ} {M : ℝ} :
    M ∈ normalizedSupNorms k γ K ↔
      ∃ p : ℂ[X], p.degree ≤ k ∧ p.eval γ = 1 ∧ M = sSup ((fun z => ‖p.eval z‖) '' K) :=
  Iff.rfl

/-! ### The maximum modulus principle for polynomials -/

/-- The maximum modulus principle for a polynomial on a disc: a bound valid on the circle of
radius `r` is valid on the whole closed disc. -/
theorem norm_eval_le_of_forall_mem_sphere {q : ℂ[X]} {r C : ℝ} (hr : 0 < r)
    (hC : ∀ w ∈ Metric.sphere (0 : ℂ) r, ‖q.eval w‖ ≤ C) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖q.eval z‖ ≤ C := by
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.ball 0 r)
    Metric.isBounded_ball q.differentiable.diffContOnCl (fun w hw => ?_) ?_
  · exact hC w (by rwa [frontier_ball _ hr.ne'] at hw)
  · rw [closure_ball _ hr.ne']
    simpa [Metric.mem_closedBall] using hz

/-! ### Zarantonello's lemma -/

/-- The reversal of `p` at degree `k`, `∑_{j ≤ k} p_j X^{k-j}`, whose value at `w ≠ 0` is
`w^k p(w⁻¹)`. -/
private noncomputable def reverseAt (k : ℕ) (p : ℂ[X]) : ℂ[X] :=
  ∑ j ∈ Finset.range (k + 1), Polynomial.C (p.coeff j) * X ^ (k - j)

private theorem reverseAt_degree_le (k : ℕ) (p : ℂ[X]) : (reverseAt k p).degree ≤ (k : ℕ) := by
  rw [reverseAt, ← Polynomial.mem_degreeLE]
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [Polynomial.mem_degreeLE]
  have hjk : k - j ≤ k := Nat.sub_le k j
  refine Polynomial.degree_le_of_natDegree_le ?_
  compute_degree
  omega

private theorem reverseAt_eval {k : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ k) {w : ℂ} (hw : w ≠ 0) :
    (reverseAt k p).eval w = w ^ k * p.eval w⁻¹ := by
  rw [reverseAt, Polynomial.eval_finsetSum,
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [pow_sub₀ w hw hjk, inv_pow]
  ring

/-- **Zarantonello's lemma**. Among the complex polynomials `p` of degree at most `k` normalized
by `p γ = 1`, the least attainable maximum of `|p|` on the circle of radius `ρ < ‖γ‖` about the
origin is `(ρ/‖γ‖)^k`, and it is attained by `(X/γ)^k`.

This is the complex counterpart of the Chebyshev min–max theorem on an interval, and the source
of the lower bound in the ellipse estimate `Polynomial.Chebyshev.ellipse_minimax_bounds`.

Reference: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003,
Lemma 6.26; Yousef Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition,
SIAM, 2011, Lemma 4.3. -/
theorem zarantonello (k : ℕ) {ρ : ℝ} (hρ : 0 < ρ) {γ : ℂ} (hγ : ρ < ‖γ‖) :
    IsLeast (normalizedSupNorms k γ (Metric.sphere 0 ρ)) ((ρ / ‖γ‖) ^ k) := by
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    simp only [norm_zero] at hγ
    linarith
  have hnorm : 0 < ‖γ‖ := hρ.trans hγ
  have hmem : (ρ : ℂ) ∈ Metric.sphere (0 : ℂ) ρ := by
    simp [abs_of_pos hρ]
  have hne : (Metric.sphere (0 : ℂ) ρ).Nonempty := ⟨(ρ : ℂ), hmem⟩
  constructor
  · refine ⟨(Polynomial.C γ⁻¹ * X) ^ k, ?_, ?_, ?_⟩
    · refine Polynomial.degree_le_of_natDegree_le (Polynomial.natDegree_pow_le.trans ?_)
      have h1 : (Polynomial.C γ⁻¹ * X : ℂ[X]).natDegree ≤ 1 := by compute_degree
      simpa using Nat.mul_le_mul_left k h1
    · simp [inv_mul_cancel₀ hγ0]
    · have himg : (fun z => ‖((Polynomial.C γ⁻¹ * X) ^ k).eval z‖) '' Metric.sphere (0 : ℂ) ρ
          = {(ρ / ‖γ‖) ^ k} := by
        rw [← hne.image_const ((ρ / ‖γ‖) ^ k)]
        refine Set.image_congr fun z hz => ?_
        rw [mem_sphere_zero_iff_norm] at hz
        simp only [Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
          norm_pow, norm_mul, norm_inv, hz]
        rw [div_eq_mul_inv, mul_comm]
      rw [himg, csSup_singleton]
  · rintro M ⟨p, hpdeg, hpγ, rfl⟩
    have hpn : p.natDegree ≤ k := Polynomial.natDegree_le_of_degree_le hpdeg
    set S := (fun z => ‖p.eval z‖) '' Metric.sphere (0 : ℂ) ρ with hS
    have hSbdd : BddAbove S :=
      ((isCompact_sphere (0 : ℂ) ρ).image p.continuous.norm).bddAbove
    have hSle : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, ‖p.eval z‖ ≤ sSup S := fun z hz =>
      le_csSup hSbdd ⟨z, hz, rfl⟩
    -- the reversed polynomial is bounded by `ρ⁻¹ ^ k * sSup S` on the circle of radius `ρ⁻¹`
    have hbnd : ∀ w ∈ Metric.sphere (0 : ℂ) ρ⁻¹,
        ‖(reverseAt k p).eval w‖ ≤ (ρ⁻¹) ^ k * sSup S := by
      intro w hw
      rw [mem_sphere_zero_iff_norm] at hw
      have hw0 : w ≠ 0 := by
        intro h
        rw [h, norm_zero] at hw
        exact absurd hw.symm (inv_ne_zero hρ.ne')
      rw [reverseAt_eval hpn hw0, norm_mul, norm_pow, hw]
      refine mul_le_mul_of_nonneg_left (hSle _ ?_) (by positivity)
      rw [mem_sphere_zero_iff_norm, norm_inv, hw, inv_inv]
    -- evaluate the maximum modulus principle at `γ⁻¹`
    have hkey : ‖(reverseAt k p).eval γ⁻¹‖ ≤ (ρ⁻¹) ^ k * sSup S :=
      norm_eval_le_of_forall_mem_sphere (inv_pos.mpr hρ) hbnd
        (by rw [norm_inv]; exact inv_anti₀ hρ hγ.le)
    rw [reverseAt_eval hpn (inv_ne_zero hγ0), inv_inv, hpγ, mul_one, norm_pow, norm_inv] at hkey
    calc (ρ / ‖γ‖) ^ k = ρ ^ k * (‖γ‖⁻¹) ^ k := by rw [div_eq_mul_inv, mul_pow]
      _ ≤ ρ ^ k * (ρ⁻¹ ^ k * sSup S) := mul_le_mul_of_nonneg_left hkey (pow_nonneg hρ.le k)
      _ = sSup S := by
          rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hρ.ne', one_pow, one_mul]

/-- The polynomial `w ↦ w^k · p(J w)` of degree at most `2k`, used to transport Zarantonello's
lemma from a circle to an ellipse. -/
private noncomputable def joukowskiLift (k : ℕ) (p : ℂ[X]) : ℂ[X] :=
  ∑ j ∈ Finset.range (k + 1), Polynomial.C (p.coeff j / 2 ^ j) * (X ^ 2 + 1) ^ j * X ^ (k - j)

private theorem joukowskiLift_degree_le (k : ℕ) (p : ℂ[X]) :
    (joukowskiLift k p).degree ≤ (2 * k : ℕ) := by
  rw [joukowskiLift, ← Polynomial.mem_degreeLE]
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [Polynomial.mem_degreeLE]
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  refine Polynomial.degree_le_of_natDegree_le ?_
  have h1 : (((X : ℂ[X]) ^ 2 + 1) ^ j).natDegree ≤ 2 * j := by
    refine Polynomial.natDegree_pow_le.trans ?_
    have h2 : ((X : ℂ[X]) ^ 2 + 1).natDegree ≤ 2 := by compute_degree
    calc j * ((X : ℂ[X]) ^ 2 + 1).natDegree ≤ j * 2 := Nat.mul_le_mul_left j h2
      _ = 2 * j := by ring
  calc (Polynomial.C (p.coeff j / 2 ^ j) * ((X : ℂ[X]) ^ 2 + 1) ^ j * X ^ (k - j)).natDegree
      ≤ (Polynomial.C (p.coeff j / 2 ^ j) * ((X : ℂ[X]) ^ 2 + 1) ^ j).natDegree +
          ((X : ℂ[X]) ^ (k - j)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ 2 * j + (k - j) := by
        gcongr
        · exact Polynomial.natDegree_mul_le.trans (by simpa using h1)
        · simp
    _ ≤ 2 * k := by omega

private theorem joukowskiLift_eval {k : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ k) {w : ℂ}
    (hw : w ≠ 0) : (joukowskiLift k p).eval w = w ^ k * p.eval (Complex.joukowski w) := by
  rw [joukowskiLift, Polynomial.eval_finsetSum,
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_one]
  rw [Complex.joukowski_eq_div hw, div_pow, mul_pow, pow_sub₀ w hw hjk]
  field_simp

end Polynomial

namespace Polynomial.Chebyshev

/-! ### The Chebyshev polynomial in the Joukowski variable -/

/-- The Joukowski form of the Chebyshev polynomial: `T_k(J w) = (w^k + w^{-k})/2`. -/
theorem eval_T_joukowski (k : ℤ) {w : ℂ} (hw : w ≠ 0) :
    (T ℂ k).eval (Complex.joukowski w) = (w ^ k + w ^ (-k)) / 2 := by
  have hlog : Complex.exp (Complex.log w) = w := Complex.exp_log hw
  have hcosh : Complex.joukowski w = Complex.cosh (Complex.log w) := by
    rw [Complex.cosh, Complex.exp_neg, hlog, Complex.joukowski_def]
  calc (T ℂ k).eval (Complex.joukowski w)
      = Complex.cosh ((k : ℂ) * Complex.log w) := by rw [hcosh, T_complex_cosh]
    _ = (w ^ k + w ^ (-k)) / 2 := by
        rw [Complex.cosh, Complex.exp_int_mul, hlog,
          show -((k : ℂ) * Complex.log w) = ((-k : ℤ) : ℂ) * Complex.log w by push_cast; ring,
          Complex.exp_int_mul, hlog]

/-- The Joukowski form of the Chebyshev polynomial at a natural index. -/
theorem eval_T_joukowski_nat (k : ℕ) {w : ℂ} (hw : w ≠ 0) :
    (T ℂ (k : ℤ)).eval (Complex.joukowski w) = (w ^ k + (w ^ k)⁻¹) / 2 := by
  rw [eval_T_joukowski (k : ℤ) hw, zpow_neg, zpow_natCast]

/-- `|T_k|` is unchanged by a sign change of its argument. -/
theorem norm_eval_T_neg (k : ℤ) (x : ℂ) : ‖(T ℂ k).eval (-x)‖ = ‖(T ℂ k).eval x‖ := by
  rw [T_eval_neg, norm_mul]
  rcases Int.units_eq_one_or k.negOnePow with h | h <;> rw [h] <;> simp

/-- Outside the unit circle the Chebyshev polynomial does not vanish on the Joukowski image;
this is what makes the normalization `T_k(z)/T_k(γ)` legitimate for `γ` outside an ellipse. -/
theorem eval_T_joukowski_ne_zero (k : ℕ) {w : ℂ} (hw : 1 < ‖w‖) :
    (T ℂ (k : ℤ)).eval (Complex.joukowski w) ≠ 0 := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    linarith
  have hwk : w ^ k ≠ 0 := pow_ne_zero k hw0
  rw [eval_T_joukowski_nat k hw0]
  intro hzero
  rw [div_eq_zero_iff] at hzero
  have hsum : w ^ k + (w ^ k)⁻¹ = 0 := by
    rcases hzero with h | h
    · exact h
    · norm_num at h
  have hsq : (w ^ k) ^ 2 = -1 := by
    have h := congrArg (fun z => z * w ^ k) hsum
    simp only [add_mul, inv_mul_cancel₀ hwk, zero_mul] at h
    linear_combination h
  have hnorm : ‖w‖ ^ k = 1 := by
    have h1 : ‖(w ^ k) ^ 2‖ = 1 := by rw [hsq]; simp
    rw [norm_pow, norm_pow] at h1
    nlinarith [norm_nonneg w, pow_nonneg (norm_nonneg w) k]
  have hk : k = 0 := by
    by_contra hk0
    have := one_lt_pow₀ hw hk0
    rw [hnorm] at this
    exact lt_irrefl 1 this
  rw [hk] at hsq
  have := congrArg Complex.re hsq
  norm_num at this

/-- The real Chebyshev polynomial at the Joukowski point `(ρ + ρ⁻¹)/2`, which for the ellipse
`Set.ellipse c d ρ` is the ratio `a/d` of the semi-major axis to the focal semi-distance. -/
theorem eval_T_joukowski_real (k : ℕ) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    (T ℝ (k : ℤ)).eval ((ρ + ρ⁻¹) / 2) = (ρ ^ k + (ρ ^ k)⁻¹) / 2 := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ
  have hinv : ρ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hρ
  have key : 2 ≤ ρ + ρ⁻¹ := by
    have h : ρ + ρ⁻¹ - 2 = (ρ - 1) ^ 2 / ρ := by field_simp; ring
    have h2 : 0 ≤ (ρ - 1) ^ 2 / ρ := div_nonneg (sq_nonneg _) hρ0.le
    linarith
  have hx : 1 ≤ (ρ + ρ⁻¹) / 2 := by linarith
  have hsq : Real.sqrt (((ρ + ρ⁻¹) / 2) ^ 2 - 1) = (ρ - ρ⁻¹) / 2 := by
    rw [show ((ρ + ρ⁻¹) / 2) ^ 2 - 1 = ((ρ - ρ⁻¹) / 2) ^ 2 by
      field_simp
      ring]
    exact Real.sqrt_sq (by linarith)
  rw [eval_T_eq_half_add_pow hx k, hsq,
    show (ρ + ρ⁻¹) / 2 + (ρ - ρ⁻¹) / 2 = ρ by ring,
    show (ρ + ρ⁻¹) / 2 - (ρ - ρ⁻¹) / 2 = ρ⁻¹ by ring, inv_pow]

/-! ### The maximum of `|T_k|` on an ellipse -/

/-- The maximum of `w ↦ |T_k(J w)|` on the circle of radius `ρ ≥ 1`, attained at `w = ρ`. -/
private theorem isGreatest_norm_eval_T_sphere (k : ℕ) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    IsGreatest ((fun w => ‖(T ℂ (k : ℤ)).eval (Complex.joukowski w)‖) '' Metric.sphere 0 ρ)
      ((ρ ^ k + (ρ ^ k)⁻¹) / 2) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ
  constructor
  · refine ⟨(ρ : ℂ), by simp [abs_of_pos hρ0], ?_⟩
    have hne : (ρ : ℂ) ≠ 0 := by
      simpa using hρ0.ne'
    dsimp only
    rw [eval_T_joukowski_nat k hne,
      show ((ρ : ℂ) ^ k + ((ρ : ℂ) ^ k)⁻¹) / 2 = (((ρ ^ k + (ρ ^ k)⁻¹) / 2 : ℝ) : ℂ) by
        push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  · rintro _ ⟨w, hw, rfl⟩
    rw [mem_sphere_zero_iff_norm] at hw
    have hw0 : w ≠ 0 := by
      intro h
      rw [h, norm_zero] at hw
      exact absurd hw.symm hρ0.ne'
    have hnk : ‖w ^ k‖ = ρ ^ k := by rw [norm_pow, hw]
    dsimp only
    rw [eval_T_joukowski_nat k hw0, norm_div, Complex.norm_ofNat]
    have h := norm_add_le (w ^ k) ((w ^ k)⁻¹)
    rw [norm_inv, hnk] at h
    linarith

/-- The image of an ellipse under `z ↦ |T_k((c - z)/d)|` is the image of the parameter circle
under `w ↦ |T_k(J w)|`: the sign introduced by `(c - z)/d = -J w` is invisible to the modulus. -/
private theorem image_norm_eval_T_ellipse (k : ℕ) {c d : ℂ} (hd : d ≠ 0) (ρ : ℝ) :
    (fun z => ‖(T ℂ (k : ℤ)).eval ((c - z) / d)‖) '' Set.ellipse c d ρ
      = (fun w => ‖(T ℂ (k : ℤ)).eval (Complex.joukowski w)‖) '' Metric.sphere 0 ρ := by
  rw [Set.ellipse_def, Set.image_image]
  refine Set.image_congr' fun w => ?_
  have hcz : (c - (c + d * Complex.joukowski w)) / d = -Complex.joukowski w := by
    field_simp
    ring
  rw [hcz, norm_eval_T_neg]

/-- The maximum of `|T_k|` on the ellipse `E_ρ` with foci `±1` and semi-axes `(ρ ± ρ⁻¹)/2` is
`(ρ^k + ρ^{-k})/2`, attained at the vertex `J ρ = (ρ + ρ⁻¹)/2`.

Reference: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003,
(6.117). -/
theorem sSup_norm_eval_T_ellipse (k : ℕ) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    sSup ((fun z => ‖(T ℂ (k : ℤ)).eval z‖) '' Set.ellipse 0 1 ρ) = (ρ ^ k + (ρ ^ k)⁻¹) / 2 := by
  have himg : (fun z => ‖(T ℂ (k : ℤ)).eval z‖) '' Set.ellipse 0 1 ρ
      = (fun w => ‖(T ℂ (k : ℤ)).eval (Complex.joukowski w)‖) '' Metric.sphere 0 ρ := by
    rw [Set.ellipse_def, Set.image_image]
    refine Set.image_congr' fun w => ?_
    rw [zero_add, one_mul]
  rw [himg]
  exact (isGreatest_norm_eval_T_sphere k hρ).csSup_eq

/-! ### The min–max value on an ellipse -/

/-- The two-sided estimate of the Chebyshev min–max value on the ellipse `E_ρ`.

For `ρ ≥ 1` and a normalization point `γ = J w_γ` lying outside `E_ρ`, that is with
`‖w_γ‖ > ρ`, every polynomial `p` of degree at most `k` with `p γ = 1` has maximum modulus at
least `(ρ/‖w_γ‖)^k` on `E_ρ`, and the normalized Chebyshev polynomial `T_k(z)/T_k(γ)` attains
the value `(ρ^k + ρ^{-k})/‖w_γ^k + w_γ^{-k}‖`.

Reference: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003,
Theorem 6.27; Yousef Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition,
SIAM, 2011, Theorem 4.9. -/
theorem ellipse_minimax_bounds (k : ℕ) {ρ : ℝ} (hρ : 1 ≤ ρ) {wγ : ℂ} (hw : ρ < ‖wγ‖) :
    (ρ / ‖wγ‖) ^ k ∈
        lowerBounds (normalizedSupNorms k (Complex.joukowski wγ) (Set.ellipse 0 1 ρ)) ∧
      (ρ ^ k + (ρ ^ k)⁻¹) / ‖wγ ^ k + (wγ ^ k)⁻¹‖ ∈
        normalizedSupNorms k (Complex.joukowski wγ) (Set.ellipse 0 1 ρ) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ
  have hw1 : 1 < ‖wγ‖ := lt_of_le_of_lt hρ hw
  have hw0 : wγ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw1
    linarith
  have hwk : wγ ^ k ≠ 0 := pow_ne_zero k hw0
  have hEimg : ∀ q : ℂ[X], (fun z => ‖q.eval z‖) '' Set.ellipse 0 1 ρ
      = (fun w => ‖q.eval (Complex.joukowski w)‖) '' Metric.sphere 0 ρ := by
    intro q
    rw [Set.ellipse_def, Set.image_image]
    refine Set.image_congr' fun w => ?_
    rw [zero_add, one_mul]
  constructor
  · rintro M ⟨p, hpdeg, hpγ, rfl⟩
    have hpn : p.natDegree ≤ k := Polynomial.natDegree_le_of_degree_le hpdeg
    set S := (fun z => ‖p.eval z‖) '' Set.ellipse 0 1 ρ with hS
    have hSbdd : BddAbove S := by
      rw [hS]
      exact ((Set.isCompact_ellipse 0 1 hρ0).image p.continuous.norm).bddAbove
    have hSle : ∀ w ∈ Metric.sphere (0 : ℂ) ρ, ‖p.eval (Complex.joukowski w)‖ ≤ sSup S := by
      intro w hw'
      refine le_csSup hSbdd ?_
      rw [hS, hEimg p]
      exact ⟨w, hw', rfl⟩
    -- the lifted polynomial, normalized at `wγ`
    obtain ⟨r, hr⟩ : ∃ r : ℂ[X],
        r = Polynomial.C ((wγ ^ k)⁻¹) * Polynomial.joukowskiLift k p := ⟨_, rfl⟩
    have hrdeg : r.degree ≤ (2 * k : ℕ) := by
      rw [hr]
      refine Polynomial.degree_le_of_natDegree_le ?_
      refine Polynomial.natDegree_mul_le.trans ?_
      rw [Polynomial.natDegree_C, zero_add]
      exact Polynomial.natDegree_le_of_degree_le (Polynomial.joukowskiLift_degree_le k p)
    have hreval : ∀ w : ℂ, w ≠ 0 →
        r.eval w = (wγ ^ k)⁻¹ * (w ^ k * p.eval (Complex.joukowski w)) := by
      intro w hwne
      rw [hr, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.joukowskiLift_eval hpn hwne]
    have hrγ : r.eval wγ = 1 := by
      rw [hreval wγ hw0, hpγ, mul_one, inv_mul_cancel₀ hwk]
    -- Zarantonello on the circle of radius `ρ`
    have hzar := Polynomial.zarantonello (2 * k) hρ0 hw
    have hmem : sSup ((fun z => ‖r.eval z‖) '' Metric.sphere 0 ρ) ∈
        Polynomial.normalizedSupNorms (2 * k) wγ (Metric.sphere 0 ρ) := ⟨r, hrdeg, hrγ, rfl⟩
    have hlow := hzar.2 hmem
    -- but that supremum is at most `‖wγ‖⁻¹ ^ k * ρ ^ k * sSup S`
    have hup : sSup ((fun z => ‖r.eval z‖) '' Metric.sphere 0 ρ)
        ≤ (‖wγ‖ ^ k)⁻¹ * ρ ^ k * sSup S := by
      refine csSup_le ⟨_, ⟨(ρ : ℂ), by simp [abs_of_pos hρ0], rfl⟩⟩ ?_
      rintro _ ⟨w, hw', rfl⟩
      have hwnorm : ‖w‖ = ρ := by rwa [mem_sphere_zero_iff_norm] at hw'
      have hwne : w ≠ 0 := by
        intro h
        rw [h, norm_zero] at hwnorm
        exact absurd hwnorm.symm hρ0.ne'
      dsimp only
      rw [hreval w hwne, norm_mul, norm_mul, norm_inv, norm_pow, norm_pow, hwnorm, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (hSle w hw') (by positivity)
    have hchain : (ρ / ‖wγ‖) ^ (2 * k) ≤ (‖wγ‖ ^ k)⁻¹ * ρ ^ k * sSup S := hlow.trans hup
    have hApos : (0 : ℝ) < ρ ^ k := pow_pos hρ0 k
    have hBpos : (0 : ℝ) < ‖wγ‖ ^ k := pow_pos (hρ0.trans hw) k
    have hq : (0 : ℝ) < ρ ^ k / ‖wγ‖ ^ k := div_pos hApos hBpos
    have hsq : (ρ / ‖wγ‖) ^ (2 * k) = (ρ ^ k / ‖wγ‖ ^ k) * (ρ ^ k / ‖wγ‖ ^ k) := by
      rw [two_mul, pow_add, div_pow]
    have hrhs : (‖wγ‖ ^ k)⁻¹ * ρ ^ k * sSup S = (ρ ^ k / ‖wγ‖ ^ k) * sSup S := by
      rw [div_eq_mul_inv]
      ring
    rw [hsq, hrhs] at hchain
    rw [div_pow]
    exact le_of_mul_le_mul_left hchain hq
  · refine ⟨Polynomial.C ((T ℂ (k : ℤ)).eval (Complex.joukowski wγ))⁻¹ * T ℂ (k : ℤ), ?_, ?_, ?_⟩
    · refine Polynomial.degree_le_of_natDegree_le ?_
      refine Polynomial.natDegree_mul_le.trans ?_
      rw [Polynomial.natDegree_C, zero_add, natDegree_T, Int.natAbs_natCast]
    · rw [Polynomial.eval_mul, Polynomial.eval_C,
        inv_mul_cancel₀ (eval_T_joukowski_ne_zero k hw1)]
    · have hTne := eval_T_joukowski_ne_zero k hw1
      have himg : (fun z => ‖(Polynomial.C ((T ℂ (k : ℤ)).eval (Complex.joukowski wγ))⁻¹ *
            T ℂ (k : ℤ)).eval z‖) '' Set.ellipse 0 1 ρ
          = (fun t => ‖(T ℂ (k : ℤ)).eval (Complex.joukowski wγ)‖⁻¹ * t) ''
              ((fun z => ‖(T ℂ (k : ℤ)).eval z‖) '' Set.ellipse 0 1 ρ) := by
        rw [Set.image_image]
        refine Set.image_congr' fun z => ?_
        rw [Polynomial.eval_mul, Polynomial.eval_C, norm_mul, norm_inv]
      rw [himg]
      have hgreat : IsGreatest ((fun z => ‖(T ℂ (k : ℤ)).eval z‖) '' Set.ellipse 0 1 ρ)
          ((ρ ^ k + (ρ ^ k)⁻¹) / 2) := by
        have h : (fun z => ‖(T ℂ (k : ℤ)).eval z‖) '' Set.ellipse 0 1 ρ
            = (fun w => ‖(T ℂ (k : ℤ)).eval (Complex.joukowski w)‖) '' Metric.sphere 0 ρ :=
          hEimg _
        rw [h]
        exact isGreatest_norm_eval_T_sphere k hρ
      have hscaled : IsGreatest ((fun t => ‖(T ℂ (k : ℤ)).eval (Complex.joukowski wγ)‖⁻¹ * t) ''
          ((fun z => ‖(T ℂ (k : ℤ)).eval z‖) '' Set.ellipse 0 1 ρ))
          (‖(T ℂ (k : ℤ)).eval (Complex.joukowski wγ)‖⁻¹ * ((ρ ^ k + (ρ ^ k)⁻¹) / 2)) := by
        refine ⟨⟨_, hgreat.1, rfl⟩, ?_⟩
        rintro _ ⟨t, ht, rfl⟩
        exact mul_le_mul_of_nonneg_left (hgreat.2 ht) (by positivity)
      have hne2 : ‖wγ ^ k + (wγ ^ k)⁻¹‖ ≠ 0 := by
        rw [norm_ne_zero_iff]
        intro h
        exact hTne (by rw [eval_T_joukowski_nat k hw0, h, zero_div])
      rw [hscaled.csSup_eq, eval_T_joukowski_nat k hw0, norm_div, Complex.norm_ofNat]
      field_simp

/-! ### The shifted, normalized Chebyshev polynomial on a general ellipse -/

/-- The shifted, normalized complex Chebyshev polynomial
`Ĉ_k(z) = T_k((c - z)/d) / T_k((c - γ)/d)`, which takes the value `1` at `γ`. It is the complex
counterpart of `Polynomial.Chebyshev.shifted`.

Reference: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003,
(6.119). -/
noncomputable def shiftedComplex (k : ℕ) (c d γ : ℂ) : ℂ[X] :=
  Polynomial.C ((T ℂ (k : ℤ)).eval ((c - γ) / d))⁻¹ *
    (T ℂ (k : ℤ)).comp (Polynomial.C (c / d) - Polynomial.C d⁻¹ * X)

/-- The evaluation of `shiftedComplex` as a ratio of Chebyshev values. -/
theorem shiftedComplex_eval (k : ℕ) {c d : ℂ} (hd : d ≠ 0) (γ z : ℂ) :
    (shiftedComplex k c d γ).eval z =
      (T ℂ (k : ℤ)).eval ((c - z) / d) / (T ℂ (k : ℤ)).eval ((c - γ) / d) := by
  rw [shiftedComplex, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
  simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
  rw [show c / d - d⁻¹ * z = (c - z) / d by field_simp]
  ring

/-- `shiftedComplex k c d γ` has degree at most `k`. -/
theorem shiftedComplex_degree_le (k : ℕ) (c d γ : ℂ) :
    (shiftedComplex k c d γ).degree ≤ k := by
  refine Polynomial.degree_le_of_natDegree_le ?_
  rw [shiftedComplex]
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_C, zero_add]
  refine Polynomial.natDegree_comp_le.trans ?_
  have hlin : (Polynomial.C (c / d) - Polynomial.C d⁻¹ * X : ℂ[X]).natDegree ≤ 1 := by
    compute_degree
  rw [natDegree_T, Int.natAbs_natCast]
  simpa using Nat.mul_le_mul_left k hlin

/-- `shiftedComplex k c d γ` takes the value `1` at the normalization point `γ`. -/
theorem shiftedComplex_eval_self (k : ℕ) {c d γ : ℂ} (hd : d ≠ 0)
    (hγ : (T ℂ (k : ℤ)).eval ((c - γ) / d) ≠ 0) : (shiftedComplex k c d γ).eval γ = 1 := by
  rw [shiftedComplex_eval k hd, div_self hγ]

/-- The maximum on the ellipse `E(c, d, a)` of the shifted, normalized Chebyshev polynomial
`Ĉ_k(z) = T_k((c - z)/d)/T_k((c - γ)/d)` is `T_k(a/d)/|T_k((c - γ)/d)|`, where
`a/d = (ρ + ρ⁻¹)/2` is the ratio of the semi-major axis to the focal semi-distance.

Reference: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003,
(6.119)–(6.120). -/
theorem sSup_norm_eval_shiftedComplex_ellipse (k : ℕ) {ρ : ℝ} (hρ : 1 ≤ ρ) {c d γ : ℂ}
    (hd : d ≠ 0) (hγ : (T ℂ (k : ℤ)).eval ((c - γ) / d) ≠ 0) :
    sSup ((fun z => ‖(shiftedComplex k c d γ).eval z‖) '' Set.ellipse c d ρ) =
      (T ℝ (k : ℤ)).eval ((ρ + ρ⁻¹) / 2) / ‖(T ℂ (k : ℤ)).eval ((c - γ) / d)‖ := by
  have himg : (fun z => ‖(shiftedComplex k c d γ).eval z‖) '' Set.ellipse c d ρ
      = (fun t => ‖(T ℂ (k : ℤ)).eval ((c - γ) / d)‖⁻¹ * t) ''
          ((fun z => ‖(T ℂ (k : ℤ)).eval ((c - z) / d)‖) '' Set.ellipse c d ρ) := by
    rw [Set.image_image]
    refine Set.image_congr' fun z => ?_
    rw [shiftedComplex_eval k hd, norm_div, div_eq_inv_mul]
  rw [himg, image_norm_eval_T_ellipse k hd ρ]
  have hgreat := isGreatest_norm_eval_T_sphere k hρ
  have hscaled : IsGreatest ((fun t => ‖(T ℂ (k : ℤ)).eval ((c - γ) / d)‖⁻¹ * t) ''
      ((fun w => ‖(T ℂ (k : ℤ)).eval (Complex.joukowski w)‖) '' Metric.sphere 0 ρ))
      (‖(T ℂ (k : ℤ)).eval ((c - γ) / d)‖⁻¹ * ((ρ ^ k + (ρ ^ k)⁻¹) / 2)) := by
    refine ⟨⟨_, hgreat.1, rfl⟩, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact mul_le_mul_of_nonneg_left (hgreat.2 ht) (by positivity)
  rw [hscaled.csSup_eq, eval_T_joukowski_real k hρ]
  ring

end Polynomial.Chebyshev
