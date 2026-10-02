import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Numlib.Analysis.Matrix.Function.Sqrt

/-!
# The principal logarithm of a matrix

The principal logarithm ([golub2013matrix] §9.4.4; Higham, *Functions of Matrices*, Ch. 11)
`log(A) = pfc Complex.log A`, with Mathlib's principal branch `Complex.log` (analytic on
`Complex.slitPlane`). For `A` with no eigenvalue on `(-∞, 0]` it is a logarithm of `A`,
`e^{log A} = A`, with eigenvalues in the strip `|Im z| < π` (`Matrix.exp_principalLog`).

## Main results

* `Matrix.exp_principalLog`: `e^{log A} = A` and the spectrum of `log A` lies in the strip.
* `Matrix.hasSum_principalLog`: the Maclaurin series `log A = ∑_{k ≥ 1} (-1)^{k+1} (A - I)^k / k`
  when every eigenvalue lies in the unit disk around `1`.
* `Matrix.principalLog_principalSqrt`, `Matrix.principalLog_eq_two_pow_smul`: the inverse
  scaling-and-squaring identity `log A = 2^k log A^{1/2^k}`.
* `Matrix.existsUnique_exp_eq_of_abs_im_lt`, `Matrix.existsUnique_real_exp_eq`: the principal
  logarithm is the only logarithm with eigenvalues in the strip, and it is real for a real matrix
  (read in `ℂ` through `Matrix.complexify`, with `Matrix.complexify_exp`).

The Banach-algebra facts about Mathlib's series logarithm `NormedSpace.log` (`exp (log x) = x` for
`‖x - 1‖ < 1`) are `Numlib/Analysis/Normed/Algebra/Logarithm`; the agreement of the two logarithms
near the identity is `pfc_log_eq_normedSpace_log`.
-/

open Polynomial Filter Topology Complex

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The principal logarithm** ([golub2013matrix] §9.4.4's `log(A)`): `pfc Complex.log A`. -/
noncomputable def principalLog (A : Matrix n n ℂ) : Matrix n n ℂ :=
  pfc Complex.log A

/-- Functions agreeing on the slit plane agree at a matrix with spectrum in it. -/
private theorem pfc_congr_of_slitPlane {A : Matrix n n ℂ} (hA : spectrum ℂ A ⊆ slitPlane)
    {f g : ℂ → ℂ} (h : ∀ z ∈ slitPlane, f z = g z) : pfc f A = pfc g A :=
  pfc_congr_of_eqOn isOpen_slitPlane hA h

/-- **The principal logarithm is a logarithm** ([golub2013matrix] §9.4.4): with no eigenvalue on
`(-∞, 0]`, `e^{log A} = A`, and every eigenvalue of `log A` has `|Im μ| < π`. -/
theorem exp_principalLog {A : Matrix n n ℂ} (hA : spectrum ℂ A ⊆ slitPlane) :
    NormedSpace.exp (principalLog A) = A ∧ ∀ μ ∈ spectrum ℂ (principalLog A), |μ.im| < Real.pi := by
  have hI : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral _
  refine ⟨?_, ?_⟩
  · rw [← pfc_exp_eq_normedSpace_exp (Algebra.IsIntegral.isIntegral _), principalLog,
      ← pfc_comp hI (IsAlgClosed.splits _)
        (fun μ hμ => (analyticAt_clog (hA (spectrum.mem_of_mem_roots_minpoly hμ))).contDiffAt)
        (fun μ _ => Complex.contDiff_exp.contDiffAt),
      pfc_congr_of_slitPlane hA (f := Complex.exp ∘ Complex.log) (g := fun z => z)
        fun z hz => Complex.exp_log (slitPlane_ne_zero hz),
      pfc_id hI (IsAlgClosed.splits _)]
  · rw [principalLog, spectrum_pfc hI (IsAlgClosed.splits _)]
    rintro _ ⟨μ, hμ, rfl⟩
    rw [log_im, abs_lt]
    exact ⟨neg_pi_lt_arg μ, lt_of_le_of_ne (arg_le_pi μ) (slitPlane_arg_ne_pi (hA hμ))⟩

/-- **The Maclaurin series of the logarithm** ([golub2013matrix] §9.4.4, `M_q(A)`): if every
eigenvalue satisfies `|λ - 1| < 1`, then `log A = ∑_{k ≥ 0} (-1)^k (A - I)^{k+1} / (k + 1)`. -/
theorem hasSum_principalLog {A : Matrix n n ℂ} (hA : ∀ μ ∈ spectrum ℂ A, ‖μ - 1‖ < 1) :
    HasSum (fun k : ℕ => ((-1) ^ k / (k + 1) : ℂ) • (A - 1) ^ (k + 1)) (principalLog A) := by
  have hI : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral _
  have hσ : spectrum ℂ A ⊆ Metric.eball (1 : ℂ) 1 := fun μ hμ => by
    rw [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_one, dist_eq_norm]
    exact hA μ hμ
  have h := hasSum_pfc Complex.hasFPowerSeriesOnBall_log_one hI (IsAlgClosed.splits _) hσ
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.range_one, Finset.sum_singleton, FormalMultilinearSeries.coeff_ofScalars,
    Nat.cast_zero, div_zero, zero_smul, sub_zero, map_one] at h
  refine h.congr_fun fun k => ?_
  congr 1
  push_cast
  ring

/-! ### Uniqueness of the principal logarithm -/

/-- `(e^z - 1)/z`, completed by `1` at `0`, is analytic at `0`. -/
private theorem contDiffAt_dslope_exp : ContDiffAt ℂ ⊤ (dslope Complex.exp 0) 0 := by
  obtain ⟨p, hp⟩ := (analyticAt_cexp (z := 0))
  exact (hp.has_fpower_series_dslope_fslope).analyticAt.contDiffAt

/-- A matrix with spectrum `{0}` and exponential `1` is `0`: `e^N - 1 = N u` with
`u = pfc ((e^z - 1)/z) N` invertible. -/
private theorem eq_zero_of_exp_eq_one {N : Matrix n n ℂ} (hN : spectrum ℂ N ⊆ {0})
    (h1 : NormedSpace.exp N = 1) : N = 0 := by
  have hI : IsIntegral ℂ N := Algebra.IsIntegral.isIntegral _
  have hs := IsAlgClosed.splits (minpoly ℂ N)
  have hroot : ∀ μ ∈ (minpoly ℂ N).roots, μ = 0 := fun μ hμ =>
    hN (spectrum.mem_of_mem_roots_minpoly hμ)
  have hg : ∀ μ ∈ (minpoly ℂ N).roots,
      ContDiffAt ℂ ((minpoly ℂ N).rootMultiplicity μ - 1 : ℕ) (dslope Complex.exp 0) μ :=
    fun μ hμ => by rw [hroot μ hμ]; exact contDiffAt_dslope_exp.of_le le_top
  have hg0 : ∀ μ ∈ (minpoly ℂ N).roots, dslope Complex.exp 0 μ ≠ 0 := fun μ hμ => by
    rw [hroot μ hμ, dslope_same, Complex.deriv_exp, Complex.exp_zero]
    exact one_ne_zero
  have hu := (pfc_inv hI hs hg hg0).1
  have hmul : NormedSpace.exp N - 1 = N * pfc (dslope Complex.exp 0) N := by
    have hfun : (Complex.exp - fun _ => (1 : ℂ)) = (fun z : ℂ => z) * dslope Complex.exp 0 := by
      funext z
      have := sub_smul_dslope Complex.exp 0 z
      simp only [sub_zero, smul_eq_mul, Complex.exp_zero] at this
      simp [this]
    have h2 := congrArg (fun f => pfc f N) hfun
    rw [pfc_sub (f := Complex.exp) (g := fun _ => (1 : ℂ))
        (fun μ _ => Complex.contDiff_exp.contDiffAt) (fun μ _ => contDiffAt_const),
      pfc_mul (f := fun z : ℂ => z) hI hs (fun μ _ => contDiffAt_id) hg, pfc_const hI hs,
      pfc_id hI hs, map_one, pfc_exp_eq_normedSpace_exp hI] at h2
    exact h2
  rw [h1, sub_self] at hmul
  exact (hu.mul_left_eq_zero).mp hmul.symm

/-- **Uniqueness of the principal logarithm** ([golub2013matrix] §9.4.4): with no eigenvalue on
`(-∞, 0]`, `log A` is the only logarithm of `A` with eigenvalues in the strip `|Im z| < π`. Any
such `X` has `log A = q(X)` for a polynomial with `q(μ) = log (e^μ) = μ` on the spectrum of `X`, so
`X - log A` has spectrum `{0}` and exponential `e^X e^{-log A} = 1`, hence vanishes. -/
theorem existsUnique_exp_eq_of_abs_im_lt {A : Matrix n n ℂ} (hA : spectrum ℂ A ⊆ slitPlane) :
    ∃! X : Matrix n n ℂ, NormedSpace.exp X = A ∧ ∀ μ ∈ spectrum ℂ X, |μ.im| < Real.pi := by
  classical
  obtain ⟨hexpL, hL⟩ := exp_principalLog hA
  refine ⟨principalLog A, ⟨hexpL, hL⟩, fun X ⟨hX, hXs⟩ => ?_⟩
  have hI : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral _
  have hXI : IsIntegral ℂ X := Algebra.IsIntegral.isIntegral _
  set r := Hermite.interpolateJet (minpoly ℂ X).roots (Hermite.taylorJet Complex.exp)
  set p := Hermite.interpolateJet (minpoly ℂ A).roots (Hermite.taylorJet Complex.log)
  set q := p.comp r
  have hr : NormedSpace.exp X = aeval X r := by
    rw [← pfc_exp_eq_normedSpace_exp hXI, pfc_def]
  have hLq : principalLog A = aeval X q := by
    rw [principalLog, pfc_def, aeval_comp, ← hr, hX]
  have hspecX : ∀ μ ∈ spectrum ℂ X, Complex.exp μ ∈ spectrum ℂ A := fun μ hμ => by
    rw [← hX, ← pfc_exp_eq_normedSpace_exp hXI, spectrum_pfc hXI (IsAlgClosed.splits _)]
    exact ⟨μ, hμ, rfl⟩
  have hq : ∀ μ ∈ spectrum ℂ X, q.eval μ = μ := fun μ hμ => by
    have hμ' : μ ∈ (minpoly ℂ X).roots := (spectrum.mem_iff_mem_roots_minpoly hXI).1 hμ
    have he : Complex.exp μ ∈ (minpoly ℂ A).roots :=
      (spectrum.mem_iff_mem_roots_minpoly hI).1 (hspecX μ hμ)
    have him := abs_lt.mp (hXs μ hμ)
    rw [eval_comp, Hermite.eval_interpolateJet_taylorJet hμ',
      Hermite.eval_interpolateJet_taylorJet he, Complex.log_exp him.1 him.2.le]
  set N := X - principalLog A
  have hN : N = pfc (fun z => (Polynomial.X - q).eval z) X := by
    rw [pfc_polynomial hXI (IsAlgClosed.splits _), map_sub, aeval_X, ← hLq]
  have hNs : spectrum ℂ N ⊆ {0} := by
    rw [hN, spectrum_pfc hXI (IsAlgClosed.splits _)]
    rintro _ ⟨μ, hμ, rfl⟩
    simp [hq μ hμ]
  have hc : Commute X (principalLog A) := by
    rw [hLq]
    simpa using commute_aeval_aeval X Polynomial.X q
  have hexpN : NormedSpace.exp N = 1 := by
    rw [show N = X + -principalLog A from sub_eq_add_neg _ _,
      Matrix.exp_add_of_commute _ _ hc.neg_right, Matrix.exp_neg, hX, hexpL,
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).mp ?_)]
    rw [← hX]
    exact Matrix.isUnit_exp X
  have := eq_zero_of_exp_eq_one hNs hexpN
  exact (sub_eq_zero.mp this)

/-- **Complexification commutes with the exponential**: `complexify (e^X) = e^{complexify X}` for a
real square matrix `X`, the exponential series being mapped term by term. -/
theorem complexify_exp (X : Matrix n n ℝ) :
    complexify (NormedSpace.exp X) = NormedSpace.exp (complexify X) := by
  have hL : Function.LeftInverse (fun M : Matrix n n ℂ => M.map Complex.re)
      (Complex.ofRealHom.mapMatrix : Matrix n n ℝ →+* Matrix n n ℂ) := fun M => by
    ext i j
    simp
  have h := Function.LeftInverse.map_tsum (L := SummationFilter.unconditional ℕ)
    (fun k : ℕ => ((k.factorial : ℚ)⁻¹) • X ^ k)
    (g := (Complex.ofRealHom.mapMatrix : Matrix n n ℝ →+* Matrix n n ℂ))
    (continuous_id.matrix_map Complex.continuous_ofReal)
    (continuous_id.matrix_map Complex.continuous_re) hL
  rw [NormedSpace.exp_eq_tsum_rat, NormedSpace.exp_eq_tsum_rat]
  change Complex.ofRealHom.mapMatrix _ = _
  rw [h]
  congr 1
  funext k
  rw [map_rat_smul, map_pow]
  rfl

/-- **Real logarithms** ([golub2013matrix] §9.4.4): if every real eigenvalue of a real matrix `B` is
positive (no eigenvalue on `(-∞, 0]`), then `B` has a unique real logarithm with eigenvalues in the
strip `|Im z| < π`, the complex principal logarithm being real. -/
theorem existsUnique_real_exp_eq {B : Matrix n n ℝ}
    (hB : spectrum ℂ (complexify B) ⊆ slitPlane) :
    ∃! X : Matrix n n ℝ, NormedSpace.exp X = B ∧
      ∀ μ ∈ spectrum ℂ (complexify X), |μ.im| < Real.pi := by
  obtain ⟨L, ⟨hLexp, hLs⟩, hLuniq⟩ := existsUnique_exp_eq_of_abs_im_lt hB
  -- the principal logarithm is real
  obtain ⟨C, hC⟩ := pfc_complexify_of_conj (f := Complex.log) B fun μ hμ => by
    filter_upwards [isOpen_slitPlane.mem_nhds (hB hμ)] with z hz
    simp only [Function.comp_apply]
    rw [Complex.log_conj _ (slitPlane_arg_ne_pi hz), Complex.conj_conj]
  have hLC : principalLog (complexify B) = complexify C := hC
  obtain ⟨hexp, hs⟩ := exp_principalLog hB
  refine ⟨C, ⟨complexify_injective ?_, ?_⟩, fun X ⟨hX, hXs⟩ => complexify_injective ?_⟩
  · rw [complexify_exp, ← hLC, hexp]
  · rw [← hLC]
    exact hs
  · have h1 := hLuniq _ ⟨by rw [← complexify_exp, hX], hXs⟩
    have h2 := hLuniq _ ⟨hexp, hs⟩
    rw [h1, ← h2, hLC]

/-! ### The Gregory series -/

/-- The coefficients `-2/n` (odd `n`), `0` (even `n`) of `log ((1 - w)/(1 + w))`. -/
private noncomputable def gregoryCoeff (n : ℕ) : ℂ := if Odd n then -2 / n else 0

/-- The function `log (1 - w) - log (1 + w)`, which is `log ((1 - w)/(1 + w))` on the unit disk. -/
private noncomputable def gregoryFun (w : ℂ) : ℂ := Complex.log (1 - w) - Complex.log (1 + w)

private theorem norm_gregoryCoeff_le (n : ℕ) : ‖gregoryCoeff n‖ ≤ 2 := by
  unfold gregoryCoeff
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    rw [norm_div, norm_neg, Complex.norm_two, Complex.norm_natCast]
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  · simp

private theorem hasFPowerSeriesOnBall_gregoryFun :
    HasFPowerSeriesOnBall gregoryFun (FormalMultilinearSeries.ofScalars ℂ gregoryCoeff) 0 1 where
  r_le := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    refine FormalMultilinearSeries.le_radius_of_bound _ 2 fun k => ?_
    rw [FormalMultilinearSeries.ofScalars_norm]
    have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr
    calc ‖gregoryCoeff k‖ * (r : ℝ) ^ k ≤ 2 * 1 :=
          mul_le_mul (norm_gregoryCoeff_le k) (pow_le_one₀ r.coe_nonneg hr1.le) (by positivity)
            (by norm_num)
      _ = 2 := mul_one 2
  r_pos := one_pos
  hasSum {y} hy := by
    have hy1 : ‖y‖ < 1 := by
      rw [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_one] at hy
      exact hy
    rw [FormalMultilinearSeries.ofScalars_apply_eq', zero_add, gregoryFun]
    have h := (hasSum_taylorSeries_neg_log hy1).neg.sub (hasSum_taylorSeries_log hy1)
    rw [neg_neg] at h
    refine h.congr_fun fun k => ?_
    unfold gregoryCoeff
    rcases Nat.even_or_odd k with he | ho
    · rw [ite_eq_right (Nat.not_odd_iff_even.mpr he), zero_smul, pow_succ, he.neg_one_pow]
      ring
    · rw [ite_eq_left ho, smul_eq_mul, pow_succ, ho.neg_one_pow]
      ring

/-- `log z = log (1 - c) - log (1 + c)` for `c = (1 - z)/(1 + z)` and `Re z > 0`: both sides have
imaginary part in `(-π, π)` and exponential `z`. -/
private theorem gregoryFun_cayley {z : ℂ} (hz : 0 < z.re) :
    gregoryFun ((1 - z) * (1 + z)⁻¹) = Complex.log z := by
  have h1z : 1 + z ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz; exact lt_irrefl _ hz
  have hzi : 0 < (1 + z⁻¹).re := by
    rw [Complex.add_re, Complex.one_re, Complex.inv_re]
    have := Complex.normSq_nonneg z
    positivity
  have hzi0 : 1 + z⁻¹ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hzi; exact lt_irrefl _ hzi
  have h1z' : z + 1 ≠ 0 := by rwa [add_comm]
  have h2re : ∀ w : ℂ, (2 * w).re = 2 * w.re := fun w => by simp [Complex.mul_re]
  set c := (1 - z) * (1 + z)⁻¹
  have hc1 : 1 - c = 2 * (1 + z⁻¹)⁻¹ := by
    simp only [c]
    field_simp
    ring
  have hc2 : 1 + c = 2 * (1 + z)⁻¹ := by
    simp only [c]
    field_simp
    ring
  have hpos1 : 0 < (1 - c).re := by
    rw [hc1, h2re, Complex.inv_re]
    exact mul_pos two_pos (div_pos hzi (Complex.normSq_pos.mpr hzi0))
  have hpos2 : 0 < (1 + c).re := by
    rw [hc2, h2re, Complex.inv_re]
    have : 0 < (1 + z).re := by rw [Complex.add_re, Complex.one_re]; linarith
    exact mul_pos two_pos (div_pos this (Complex.normSq_pos.mpr h1z))
  have hne1 : 1 - c ≠ 0 := fun h => by rw [h, Complex.zero_re] at hpos1; exact lt_irrefl _ hpos1
  have hne2 : 1 + c ≠ 0 := fun h => by rw [h, Complex.zero_re] at hpos2; exact lt_irrefl _ hpos2
  have ha1 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hpos1)
  have ha2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hpos2)
  have hexp : Complex.exp (gregoryFun c) = z := by
    rw [gregoryFun, Complex.exp_sub, Complex.exp_log hne1, Complex.exp_log hne2, hc1, hc2]
    field_simp
    ring
  have him : (gregoryFun c).im ∈ Set.Ioo (-Real.pi) Real.pi := by
    rw [gregoryFun, Complex.sub_im, Complex.log_im, Complex.log_im]
    constructor <;> linarith [abs_lt.mp ha1, abs_lt.mp ha2]
  rw [← hexp, Complex.log_exp him.1 him.2.le]

/-- **The Gregory series** ([golub2013matrix] §9.4.4, `G_q(A)`): if every eigenvalue of `A` has
positive real part, then with `C = (I - A)(I + A)⁻¹`,
`log A = -2 ∑_{k ≥ 0} C^{2k+1}/(2k + 1)`. -/
theorem hasSum_principalLog_gregory {A : Matrix n n ℂ} (hA : ∀ μ ∈ spectrum ℂ A, 0 < μ.re) :
    HasSum (fun k : ℕ => (-2 / (2 * k + 1) : ℂ) • ((1 - A) * (1 + A)⁻¹) ^ (2 * k + 1))
      (principalLog A) := by
  have hI : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral _
  have hs := IsAlgClosed.splits (minpoly ℂ A)
  have hroot : ∀ μ ∈ (minpoly ℂ A).roots, 0 < μ.re := fun μ hμ =>
    hA μ (spectrum.mem_of_mem_roots_minpoly hμ)
  have h1z : ∀ μ : ℂ, 0 < μ.re → 1 + μ ≠ 0 := fun μ hμ h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  set c : ℂ → ℂ := fun z => (1 - z) * (1 + z)⁻¹
  have hc : ∀ μ ∈ (minpoly ℂ A).roots, ContDiffAt ℂ ⊤ c μ := fun μ hμ =>
    (contDiffAt_const.sub contDiffAt_id).mul ((contDiffAt_const.add contDiffAt_id).inv
      (h1z μ (hroot μ hμ)))
  have hnorm : ∀ μ : ℂ, 0 < μ.re → ‖c μ‖ < 1 := fun μ hμ => by
    simp only [c, norm_mul, norm_inv]
    rw [← div_eq_mul_inv, div_lt_one (norm_pos_iff.mpr (h1z μ hμ)), ← sq_lt_sq₀ (norm_nonneg _)
      (norm_nonneg _), Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, Complex.add_re,
      Complex.add_im]
    nlinarith
  -- `C = c(A)`
  have hC : (1 - A) * (1 + A)⁻¹ = pfc c A := by
    have hinv := pfc_inv hI hs (f := fun z => 1 + z)
      (fun μ _ => contDiffAt_const.add contDiffAt_id) fun μ hμ => h1z μ (hroot μ hμ)
    rw [show c = (fun z => 1 - z) * fun z => (1 + z)⁻¹ from rfl,
      pfc_mul (f := fun z : ℂ => 1 - z) (g := fun z : ℂ => (1 + z)⁻¹) hI hs
        (fun μ _ => contDiffAt_const.sub contDiffAt_id)
        (fun μ hμ => (contDiffAt_const.add contDiffAt_id).inv (h1z μ (hroot μ hμ))), hinv.2,
      show (fun z : ℂ => 1 + z) = (fun _ => (1 : ℂ)) + fun z => z from rfl,
      show (fun z : ℂ => 1 - z) = (fun _ => (1 : ℂ)) - fun z => z from rfl,
      pfc_add (f := fun _ => (1 : ℂ)) (g := fun z : ℂ => z) (fun μ _ => contDiffAt_const)
        (fun μ _ => contDiffAt_id),
      pfc_sub (f := fun _ => (1 : ℂ)) (g := fun z : ℂ => z) (fun μ _ => contDiffAt_const)
        (fun μ _ => contDiffAt_id), pfc_const hI hs,
      pfc_id hI hs, map_one, nonsing_inv_eq_ringInverse]
  have hCI : IsIntegral ℂ (pfc c A) := Algebra.IsIntegral.isIntegral _
  have hσ : spectrum ℂ (pfc c A) ⊆ Metric.eball (0 : ℂ) 1 := by
    rw [spectrum_pfc hI hs]
    rintro _ ⟨μ, hμ, rfl⟩
    rw [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_one]
    exact hnorm μ (hA μ hμ)
  have h := hasSum_pfc hasFPowerSeriesOnBall_gregoryFun hCI (IsAlgClosed.splits _) hσ
  have hcomp : pfc gregoryFun (pfc c A) = principalLog A := by
    rw [← pfc_comp hI hs (fun μ hμ => (hc μ hμ).of_le le_top) fun μ hμ => ?_]
    · exact pfc_congr_of_eqOn (isOpen_lt continuous_const Complex.continuous_re) hA
        fun z hz => gregoryFun_cayley hz
    · have hmem : c μ ∈ Metric.eball (0 : ℂ) 1 := by
        rw [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_one]
        exact hnorm μ (hroot μ hμ)
      exact (hasFPowerSeriesOnBall_gregoryFun.analyticAt_of_mem hmem).contDiffAt.of_le le_top
  rw [hcomp, map_zero, sub_zero, ← hC] at h
  simp only [FormalMultilinearSeries.coeff_ofScalars] at h
  have hinj2 : Function.Injective fun k : ℕ => 2 * k + 1 := fun a b h => by
    simp only at h; omega
  rw [← hinj2.hasSum_iff
    fun k hk => ?_] at h
  · refine h.congr_fun fun k => ?_
    simp only [Function.comp_apply, gregoryCoeff, ite_eq_left (odd_two_mul_add_one k)]
    push_cast
    rfl
  · rw [gregoryCoeff, ite_eq_right, zero_smul]
    rintro ⟨m, rfl⟩
    exact hk ⟨m, rfl⟩

/-- **Taking square roots halves the logarithm** ([golub2013matrix] §9.4.4): with no eigenvalue on
`(-∞, 0]`, `log A^{1/2} = ½ log A`. -/
theorem principalLog_principalSqrt {A : Matrix n n ℂ} (hA : spectrum ℂ A ⊆ slitPlane) :
    principalLog (principalSqrt A) = (2⁻¹ : ℂ) • principalLog A := by
  have hI : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral _
  have hsq : ∀ z ∈ slitPlane, Complex.sqrt z ∈ slitPlane := fun _ hz =>
    Complex.sqrt_mem_slitPlane hz
  rw [principalLog, principalSqrt, ← pfc_comp (f := Complex.sqrt) (g := Complex.log) hI
      (IsAlgClosed.splits _) (fun μ hμ => (analyticAt_id.cpow analyticAt_const
        (hA (spectrum.mem_of_mem_roots_minpoly hμ))).contDiffAt)
      (fun μ hμ =>
        (analyticAt_clog (hsq μ (hA (spectrum.mem_of_mem_roots_minpoly hμ)))).contDiffAt),
    principalLog, ← pfc_const_smul]
  refine pfc_congr_of_slitPlane hA fun z hz => ?_
  have hz0 := slitPlane_ne_zero hz
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
  rw [sqrt_eq_exp hz0, Complex.log_exp]
  · ring
  · rw [div_ofNat_im, log_im]
    linarith [neg_pi_lt_arg z, arg_le_pi z, Real.pi_pos]
  · rw [div_ofNat_im, log_im]
    linarith [neg_pi_lt_arg z, arg_le_pi z, Real.pi_pos]

/-- **Inverse scaling and squaring** ([golub2013matrix] §9.4.4): with no eigenvalue on `(-∞, 0]`,
`log A = 2^k log A_k` for the repeated square roots `A_0 = A`, `A_{k+1} = A_k^{1/2}`. -/
theorem principalLog_eq_two_pow_smul {A : Matrix n n ℂ} (hA : spectrum ℂ A ⊆ slitPlane) (k : ℕ) :
    principalLog A = (2 ^ k : ℂ) • principalLog (principalSqrt^[k] A) := by
  have hspec : ∀ k, spectrum ℂ (principalSqrt^[k] A) ⊆ slitPlane := by
    intro k
    induction k with
    | zero => exact hA
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact fun μ hμ => mem_slitPlane_iff.mpr (Or.inl ((principalSqrt_sq ih).2.2 μ hμ))
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih, Function.iterate_succ_apply', principalLog_principalSqrt (hspec k), smul_smul,
      pow_succ, mul_assoc, mul_inv_cancel₀ (two_ne_zero), mul_one]

end Matrix
