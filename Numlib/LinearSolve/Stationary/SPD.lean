import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Operator.Banach
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearSolve.Stationary.Splitting

/-!
# Stationary iterations for symmetric positive definite systems

The convergence theory of the classical splittings when the matrix is symmetric positive
definite, stated at the operator level wherever the proof allows.

* `Stationary.Splitting.spectralRadius_lt_one_of_isSymmetricCoercive` is the
  **Householder–John / Ostrowski–Reich theorem** (Saad[^saad-iterative] Thm 4.10;
  Kress[^kress] Thm 4.12): for a symmetric coercive `A` on a
  finite-dimensional complex inner product space and a splitting `A = M - N` whose
  `Q = M + Mᴴ - A` is coercive, the iteration operator `M⁻¹ N` has spectral radius `< 1`.
  `Stationary.Splitting.isCoercive_of_spectralRadius_lt_one` is its converse: with `Q` coercive,
  convergence forces `A` to be positive definite.
  `Matrix.sorSplitting_complexSpectralRadius_lt_one_iff_posDef` assembles the two into the SOR
  equivalence for a real symmetric matrix with positive diagonal and `0 < ω < 2`.
* `Stationary.Splitting.richardson_complexSpectralRadius_eq` and its companions compute the
  spectral radius of Richardson's iteration `G_α = 1 - α A`, characterize convergence as
  `0 < α < 2/λmax` and minimize the radius at `α = 2/(λmin + λmax)` (Saad[^saad-iterative]
  Example 4.1; Atkinson–Han[^atkinson-han] Exercise 5.2.3).
* `Matrix.jorSplitting` is Jacobi over-relaxation, `M = ω⁻¹ D`, whose optimal parameter is
  `2/(2 - λmax - λmin)` for a Jacobi matrix with real eigenvalues (Kress[^kress] Thm 4.9).
* `Matrix.det_sorSplitting_iterationOperator` computes `det G_ω = (1 - ω)ⁿ`, from which
  `Matrix.lt_two_of_sorSplitting_complexSpectralRadius_lt_one` reads off **Kahan's necessary
  condition** `0 < ω < 2` for SOR to converge (Kress[^kress] Thm 4.11).

Everything spectral is stated over `ℂ`, because the real spectrum of a real matrix is the wrong
object: `Matrix.complexSpectralRadius` is the spectral radius of the complexification, and the
operator statements are for a complex inner product space, which a real matrix reaches through
`Matrix.complexify` and `Matrix.toEuclideanCLM`.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
[^kress]: Rainer Kress, *Numerical Analysis*, Graduate Texts in Mathematics 181, Springer, 1998.
[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
-/

open Filter Topology
open scoped ENNReal NNReal ComplexOrder

namespace Stationary

namespace Splitting

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The quadratic form of `Q = M + Mᴴ - A` is `2 re ⟪M x, x⟫ - re ⟪A x, x⟫`: the adjoint
contributes the conjugate of the form of `M`. -/
private theorem re_inner_hermitianSum (M A : E →L[ℂ] E) (x : E) :
    (inner ℂ ((M + ContinuousLinearMap.adjoint M - A) x) x : ℂ).re
      = 2 * (inner ℂ (M x) x : ℂ).re - (inner ℂ (A x) x : ℂ).re := by
  have h1 : (inner ℂ (ContinuousLinearMap.adjoint M x) x : ℂ)
      = starRingEnd ℂ (inner ℂ (M x) x : ℂ) := by
    rw [ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm]
  rw [sub_apply, add_apply, inner_sub_left, inner_add_left, h1, Complex.sub_re, Complex.add_re,
    Complex.conj_re]
  ring

omit [FiniteDimensional ℂ E] in
/-- `M (x - G x) = A x` for the iteration operator `G = 1 - M⁻¹ A`: the increment of one step is
the preconditioned residual. -/
private theorem apply_sub_iterationOperator {A : E →L[ℂ] E} (s : Splitting A) (e : E) :
    s.m (e - s.iterationOperator e) = A e := by
  have hop : s.iterationOperator e = e - (Ring.inverse s.m) (A e) := by
    rw [Splitting.iterationOperator, sub_apply, one_apply_eq_self, mul_apply_eq_comp]
  have hd : e - s.iterationOperator e = (Ring.inverse s.m) (A e) := by rw [hop]; abel
  rw [hd, ← mul_apply_eq_comp, Ring.mul_inverse_cancel _ s.isUnit, one_apply_eq_self]

/-- **The energy identity of a splitting.**  For symmetric `A` the `A`-form drops in one step of
the iteration by exactly the `Q`-form of the increment, `Q = M + Mᴴ - A`:
`⟪A e, e⟫ - ⟪A G e, G e⟫ = ⟪Q (e - G e), e - G e⟫`.  Both halves of the Householder–John
theorem are read off this identity. -/
private theorem energy_identity {A : E →L[ℂ] E} (s : Splitting A)
    (hA : (A : E →ₗ[ℂ] E).IsSymmetric) (e : E) :
    (inner ℂ (A e) e : ℂ) - (inner ℂ (A (s.iterationOperator e)) (s.iterationOperator e) : ℂ)
      = (inner ℂ ((s.m + ContinuousLinearMap.adjoint s.m - A) (e - s.iterationOperator e))
          (e - s.iterationOperator e) : ℂ) := by
  set d : E := e - s.iterationOperator e with hd
  have hmd : s.m d = A e := apply_sub_iterationOperator s e
  have hGe : s.iterationOperator e = e - d := by rw [hd]; abel
  rw [hGe]
  have h1 : (inner ℂ (A (e - d)) (e - d) : ℂ)
      = inner ℂ (A e) e - inner ℂ (A e) d - inner ℂ (A d) e + inner ℂ (A d) d := by
    simp only [map_sub, inner_sub_left, inner_sub_right]
    ring
  have h2 : (inner ℂ (A e) d : ℂ) = inner ℂ (s.m d) d := by rw [hmd]
  have h3 : (inner ℂ (A d) e : ℂ) = inner ℂ (ContinuousLinearMap.adjoint s.m d) d := by
    rw [ContinuousLinearMap.adjoint_inner_left, hmd]
    exact hA d e
  rw [h1, h2, h3, sub_apply, add_apply, inner_sub_left, inner_add_left]
  ring

/-- **The Householder–John / Ostrowski–Reich theorem**, in operator form.  If `A` is symmetric
coercive on a finite-dimensional complex inner product space and `A = M - N` is a splitting whose
`Q = M + Mᴴ - A` is coercive, then the iteration operator `M⁻¹ N` has spectral radius `< 1`, so
the stationary iteration converges (Saad, *Iterative Methods for Sparse Linear Systems*, Thm 4.10;
Kress, *Numerical Analysis*, Thm 4.12 is the case `M = ω⁻¹ D - E`).

The proof is the Rayleigh-quotient identity at an eigenpair `M⁻¹ N x = μ x`: it gives
`A x = (1 - μ) M x`, and comparing the `A`- and `Q`-forms at `x` yields
`(1 - |μ|²) ⟪A x, x⟫ = |1 - μ|² ⟪Q x, x⟫`, where both forms are positive. -/
theorem spectralRadius_lt_one_of_isSymmetricCoercive {A : E →L[ℂ] E} (s : Splitting A)
    (hA : (A : E →ₗ[ℂ] E).IsSymmetricCoercive)
    (hQ : ((s.m + ContinuousLinearMap.adjoint s.m - A : E →L[ℂ] E) : E →ₗ[ℂ] E).IsCoercive) :
    spectralRadius ℂ s.iterationOperator < 1 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : Subsingleton (E →L[ℂ] E) := ⟨fun _ _ => by ext x; exact Subsingleton.elim _ _⟩
    simp [spectralRadius]
  · suffices h : ∀ μ ∈ spectrum ℂ s.iterationOperator, ‖μ‖₊ < (1 : ℝ≥0) by
      simpa using spectrum.spectralRadius_lt_of_forall_lt _ h
    intro μ hμ
    rw [ContinuousLinearMap.spectrum_eq] at hμ
    obtain ⟨x, hxmem, hx0⟩ :=
      (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ).exists_hasEigenvector
    rw [Module.End.mem_eigenspace_iff] at hxmem
    have hGx : s.iterationOperator x = μ • x := hxmem
    have hAx : A x = (1 - μ) • s.m x := by
      have hop : s.iterationOperator x = x - (Ring.inverse s.m) (A x) := by
        rw [Splitting.iterationOperator, sub_apply, one_apply_eq_self, mul_apply_eq_comp]
      have h1 : (Ring.inverse s.m) (A x) = (1 - μ) • x := by
        rw [sub_smul, one_smul, ← hGx, hop]
        abel
      calc A x = s.m ((Ring.inverse s.m) (A x)) := by
            rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel _ s.isUnit, one_apply_eq_self]
        _ = (1 - μ) • s.m x := by rw [h1, map_smul]
    have hp : 0 < (inner ℂ (A x) x : ℂ).re := hA.isCoercive.inner_self_pos hx0
    have hQpos : 0 < (inner ℂ ((s.m + ContinuousLinearMap.adjoint s.m - A) x) x : ℂ).re :=
      hQ.inner_self_pos hx0
    rw [re_inner_hermitianSum] at hQpos
    have hz0 : (1 : ℂ) - μ ≠ 0 := by
      intro h
      rw [hAx, h, zero_smul] at hp
      simp at hp
    have haw : (inner ℂ (A x) x : ℂ)
        = starRingEnd ℂ (1 - μ) * (inner ℂ (s.m x) x : ℂ) := by
      rw [hAx, inner_smul_left]
    have hconj : starRingEnd ℂ (inner ℂ (A x) x : ℂ) = (inner ℂ (A x) x : ℂ) := by
      rw [inner_conj_symm]
      exact (hA.isSymmetric x x).symm
    have hre : (inner ℂ (A x) x : ℂ).re
        = (1 - μ).re * (inner ℂ (s.m x) x : ℂ).re
          + (1 - μ).im * (inner ℂ (s.m x) x : ℂ).im := by
      rw [haw, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    have him : (1 - μ).re * (inner ℂ (s.m x) x : ℂ).im
        = (1 - μ).im * (inner ℂ (s.m x) x : ℂ).re := by
      have h : (starRingEnd ℂ (1 - μ) * (inner ℂ (s.m x) x : ℂ)).im = 0 := by
        rw [← haw]
        exact Complex.conj_eq_iff_im.mp hconj
      rw [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h
      linarith
    have hnormz : (0 : ℝ) < (1 - μ).re ^ 2 + (1 - μ).im ^ 2 := by
      have h := Complex.normSq_pos.mpr hz0
      rw [Complex.normSq_apply] at h
      nlinarith
    have key : (1 - μ).re * (inner ℂ (A x) x : ℂ).re
        = ((1 - μ).re ^ 2 + (1 - μ).im ^ 2) * (inner ℂ (s.m x) x : ℂ).re := by
      calc (1 - μ).re * (inner ℂ (A x) x : ℂ).re
          = (1 - μ).re ^ 2 * (inner ℂ (s.m x) x : ℂ).re
            + (1 - μ).im * ((1 - μ).re * (inner ℂ (s.m x) x : ℂ).im) := by
            rw [hre]; ring
        _ = ((1 - μ).re ^ 2 + (1 - μ).im ^ 2) * (inner ℂ (s.m x) x : ℂ).re := by
            rw [him]; ring
    have hprodpos : 0 < (inner ℂ (A x) x : ℂ).re
        * (2 * (1 - μ).re - ((1 - μ).re ^ 2 + (1 - μ).im ^ 2)) := by
      have h : ((1 - μ).re ^ 2 + (1 - μ).im ^ 2)
          * (2 * (inner ℂ (s.m x) x : ℂ).re - (inner ℂ (A x) x : ℂ).re)
          = (inner ℂ (A x) x : ℂ).re
            * (2 * (1 - μ).re - ((1 - μ).re ^ 2 + (1 - μ).im ^ 2)) := by
        linear_combination (-2 : ℝ) * key
      rw [← h]
      exact mul_pos hnormz hQpos
    have hlast : 0 < 2 * (1 - μ).re - ((1 - μ).re ^ 2 + (1 - μ).im ^ 2) := by
      rcases le_or_gt (2 * (1 - μ).re - ((1 - μ).re ^ 2 + (1 - μ).im ^ 2)) 0 with hcon | hcon
      · nlinarith [mul_nonneg hp.le (neg_nonneg.mpr hcon)]
      · exact hcon
    have hmu : ‖μ‖ < 1 := by
      have hn : ‖μ‖ ^ 2 = μ.re ^ 2 + μ.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        ring
      have hs : (1 - μ).re = 1 - μ.re := by simp
      have hi : (1 - μ).im = -μ.im := by simp
      rw [hs, hi] at hlast
      nlinarith [norm_nonneg μ]
    exact_mod_cast hmu

/-- **The converse of the Householder–John theorem** (Saad, *Iterative Methods for Sparse Linear
Systems*, Thm 4.10, "only if").  For symmetric `A` and a splitting with coercive
`Q = M + Mᴴ - A`, convergence of the iteration forces `A` to be coercive, i.e. positive definite.

Along the error sequence `e_{k+1} = M⁻¹ N e_k` the energy identity makes `k ↦ ⟪A e_k, e_k⟫`
nonincreasing, and it tends to `0` because `e_k → 0`; so `⟪A e₀, e₀⟫ ≥ ⟪A e₁, e₁⟫ ≥ 0`, with the
first inequality strict unless `e₁ = e₀`, which would contradict `e_k → 0`. -/
theorem isCoercive_of_spectralRadius_lt_one {A : E →L[ℂ] E} (s : Splitting A)
    (hA : (A : E →ₗ[ℂ] E).IsSymmetric)
    (hQ : ((s.m + ContinuousLinearMap.adjoint s.m - A : E →L[ℂ] E) : E →ₗ[ℂ] E).IsCoercive)
    (hρ : spectralRadius ℂ s.iterationOperator < 1) :
    (A : E →ₗ[ℂ] E).IsCoercive := by
  rw [LinearMap.isCoercive_iff_forall_pos]
  intro e₀ he₀
  change 0 < (inner ℂ (A e₀) e₀ : ℂ).re
  have hQ0 : ∀ e : E,
      0 ≤ (inner ℂ ((s.m + ContinuousLinearMap.adjoint s.m - A) e) e : ℂ).re := by
    intro e
    rcases eq_or_ne e 0 with rfl | he
    · simp
    · exact (hQ.inner_self_pos he).le
  have htend0 : Tendsto (fun k => (s.iterationOperator ^ k) e₀) atTop (𝓝 0) := by
    have hfix : s.iterationOperator 0 + (0 : E) = 0 := by simp
    have h := Stationary.tendsto_of_spectralRadius_lt_one s.iterationOperator hρ 0 e₀
    rw [show Ring.inverse ((1 : E →L[ℂ] E) - s.iterationOperator) (0 : E) = 0 from map_zero _] at h
    have hiter : ∀ k, (Stationary.step s.iterationOperator (0 : E))^[k] e₀
        = (s.iterationOperator ^ k) e₀ := fun k => by
      simpa using Stationary.step_iterate_sub s.iterationOperator (0 : E) hfix e₀ k
    simpa only [hiter] using h
  have hcont : Continuous fun y : E => (inner ℂ (A y) y : ℂ).re :=
    Complex.continuous_re.comp (A.continuous.inner continuous_id)
  have htendf : Tendsto
      (fun k => (inner ℂ (A ((s.iterationOperator ^ k) e₀)) ((s.iterationOperator ^ k) e₀) : ℂ).re)
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using (hcont.tendsto 0).comp htend0
  have hstep : ∀ e : E,
      (inner ℂ (A (s.iterationOperator e)) (s.iterationOperator e) : ℂ).re
        ≤ (inner ℂ (A e) e : ℂ).re := by
    intro e
    have hre := congrArg Complex.re (energy_identity s hA e)
    rw [Complex.sub_re] at hre
    linarith [hQ0 (e - s.iterationOperator e)]
  have hanti : ∀ k,
      (inner ℂ (A ((s.iterationOperator ^ (k + 1)) e₀)) ((s.iterationOperator ^ (k + 1)) e₀) :
          ℂ).re
        ≤ (inner ℂ (A ((s.iterationOperator ^ k) e₀)) ((s.iterationOperator ^ k) e₀) : ℂ).re := by
    intro k
    rw [show (s.iterationOperator ^ (k + 1)) e₀ = s.iterationOperator ((s.iterationOperator ^ k) e₀)
      from by rw [pow_succ', mul_apply_eq_comp]]
    exact hstep _
  have hanti' : Antitone fun k =>
      (inner ℂ (A ((s.iterationOperator ^ k) e₀)) ((s.iterationOperator ^ k) e₀) : ℂ).re :=
    antitone_nat_of_succ_le hanti
  have hnonneg : ∀ k,
      0 ≤ (inner ℂ (A ((s.iterationOperator ^ k) e₀)) ((s.iterationOperator ^ k) e₀) : ℂ).re := by
    intro k
    refine le_of_tendsto htendf (eventually_atTop.2 ⟨k, fun j hj => ?_⟩)
    exact hanti' hj
  rcases eq_or_ne (e₀ - s.iterationOperator e₀) 0 with hd0 | hd0
  · exfalso
    have hGe : s.iterationOperator e₀ = e₀ := by
      rw [sub_eq_zero] at hd0
      exact hd0.symm
    have hpow : ∀ k, (s.iterationOperator ^ k) e₀ = e₀ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, mul_apply_eq_comp, hGe, ih]
    exact he₀ (tendsto_nhds_unique tendsto_const_nhds (by simpa only [hpow] using htend0))
  · have hre := congrArg Complex.re (energy_identity s hA e₀)
    rw [Complex.sub_re] at hre
    have h1 := hnonneg 1
    rw [pow_one] at h1
    have hpos : 0 < (inner ℂ ((s.m + ContinuousLinearMap.adjoint s.m - A)
        (e₀ - s.iterationOperator e₀)) (e₀ - s.iterationOperator e₀) : ℂ).re :=
      hQ.inner_self_pos hd0
    linarith

end Operator

end Splitting

end Stationary

namespace Matrix

open Stationary

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectral radius of a real matrix is `K` as soon as every complex eigenvalue has modulus
at most `K` and one of them attains it. -/
private theorem complexSpectralRadius_eq_of_forall_le {X : Matrix n n ℝ} {K : ℝ}
    (hle : ∀ μ ∈ spectrum ℂ (complexify X), ‖μ‖ ≤ K)
    (hmem : ∃ μ ∈ spectrum ℂ (complexify X), ‖μ‖ = K) :
    complexSpectralRadius X = ENNReal.ofReal K := by
  obtain ⟨μ₀, hμ₀, hμ₀K⟩ := hmem
  rw [complexSpectralRadius, spectralRadius]
  refine le_antisymm (iSup₂_le fun μ hμ => ?_) ?_
  · calc (‖μ‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖μ‖ := by rw [ofReal_norm]; rfl
      _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal (hle μ hμ)
  · calc ENNReal.ofReal K = (‖μ₀‖₊ : ℝ≥0∞) := by rw [← hμ₀K, ofReal_norm]; rfl
      _ ≤ _ := le_iSup₂ (α := ℝ≥0∞) μ₀ hμ₀

/-- A nonzero scalar multiple is a unit exactly when the matrix is. -/
private theorem isUnit_smul_iff {c : ℂ} (hc : c ≠ 0) (M : Matrix n n ℂ) :
    IsUnit (c • M) ↔ IsUnit M := by
  rw [isUnit_iff_isUnit_det, isUnit_iff_isUnit_det, det_smul, isUnit_iff_ne_zero,
    isUnit_iff_ne_zero, mul_ne_zero_iff, and_iff_right (pow_ne_zero _ hc)]

/-- The spectrum of an affine function `c + d t` of a complex matrix, `d ≠ 0`. -/
private theorem mem_spectrum_affine_iff {Y : Matrix n n ℂ} {c d : ℂ} (hd : d ≠ 0) (μ : ℂ) :
    μ ∈ spectrum ℂ (c • 1 + d • Y) ↔ (μ - c) / d ∈ spectrum ℂ Y := by
  have key : algebraMap ℂ (Matrix n n ℂ) μ - (c • 1 + d • Y)
      = d • (algebraMap ℂ (Matrix n n ℂ) ((μ - c) / d) - Y) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul,
      mul_div_cancel₀ _ hd]
    module
  rw [spectrum.mem_iff, spectrum.mem_iff, key, isUnit_smul_iff hd]

/-- The complex spectrum of `c • 1 + d • X` for a real matrix `X`. -/
private theorem mem_spectrum_complexify_affine_iff (X : Matrix n n ℝ) {c d : ℝ} (hd : d ≠ 0)
    (μ : ℂ) :
    μ ∈ spectrum ℂ (complexify (c • 1 + d • X)) ↔
      ∃ ν ∈ spectrum ℂ (complexify X), μ = (c : ℂ) + (d : ℂ) * ν := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  rw [complexify_add, complexify_smul, complexify_smul, complexify_one,
    mem_spectrum_affine_iff hd']
  refine ⟨fun h => ⟨_, h, by rw [mul_div_cancel₀ _ hd']; ring⟩, ?_⟩
  rintro ⟨ν, hν, rfl⟩
  have hcancel : ((c : ℂ) + (d : ℂ) * ν - (c : ℂ)) / (d : ℂ) = ν := by
    field_simp
    ring
  rwa [hcancel]

/-- The spectral radius of an affine function of a real matrix whose spectrum is real and fills
`[lmin, lmax]`: the absolute value is convex, so the largest `|c + d t|` sits at an endpoint. -/
private theorem complexSpectralRadius_affine {X : Matrix n n ℝ} {lmin lmax : ℝ}
    (hsub : spectrum ℂ (complexify X) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ X) (hmax : lmax ∈ spectrum ℝ X) {c d : ℝ} (hd : d ≠ 0) :
    complexSpectralRadius (c • 1 + d • X)
      = ENNReal.ofReal (max |c + d * lmin| |c + d * lmax|) := by
  have hminC : ((lmin : ℝ) : ℂ) ∈ spectrum ℂ (complexify X) :=
    (ofReal_mem_spectrum_complexify_iff X lmin).mpr hmin
  have hmaxC : ((lmax : ℝ) : ℂ) ∈ spectrum ℂ (complexify X) :=
    (ofReal_mem_spectrum_complexify_iff X lmax).mpr hmax
  have hmem : ∀ r : ℝ, ((r : ℝ) : ℂ) ∈ spectrum ℂ (complexify X) →
      ((c + d * r : ℝ) : ℂ) ∈ spectrum ℂ (complexify (c • 1 + d • X)) := by
    intro r hr
    rw [mem_spectrum_complexify_affine_iff X hd]
    exact ⟨(r : ℂ), hr, by push_cast; ring⟩
  refine complexSpectralRadius_eq_of_forall_le (fun μ hμ => ?_) ?_
  · rw [mem_spectrum_complexify_affine_iff X hd] at hμ
    obtain ⟨ν, hν, rfl⟩ := hμ
    obtain ⟨r, hr, rfl⟩ := hsub hν
    have h : ((c : ℂ) + (d : ℂ) * (r : ℂ)) = ((c + d * r : ℝ) : ℂ) := by push_cast; ring
    rw [h, Complex.norm_real, Real.norm_eq_abs]
    rcases le_or_gt 0 d with hd0 | hd0
    · exact abs_le_max_abs_abs (by nlinarith [hr.1]) (by nlinarith [hr.2])
    · rw [max_comm]
      exact abs_le_max_abs_abs (by nlinarith [hr.2]) (by nlinarith [hr.1])
  · rcases max_cases |c + d * lmin| |c + d * lmax| with ⟨he, -⟩ | ⟨he, -⟩
    · exact ⟨_, hmem lmin hminC, by rw [he, Complex.norm_real, Real.norm_eq_abs]⟩
    · exact ⟨_, hmem lmax hmaxC, by rw [he, Complex.norm_real, Real.norm_eq_abs]⟩

/-- A real symmetric matrix has real spectrum: its complex eigenvalues are the real ones. -/
private theorem IsHermitian.spectrum_complexify_eq {X : Matrix n n ℝ} (hX : X.IsHermitian) :
    spectrum ℂ (complexify X) = Complex.ofReal '' spectrum ℝ X := by
  have hC : (complexify X).IsHermitian := (isHermitian_complexify_iff X).mpr hX
  refine Set.Subset.antisymm (fun μ hμ => ?_) ?_
  · obtain ⟨r, rfl⟩ : ∃ r : ℝ, (r : ℂ) = μ := by
      have := hμ
      rw [hC.spectrum_eq_image_range] at this
      obtain ⟨r, -, rfl⟩ := this
      exact ⟨r, rfl⟩
    exact ⟨r, (ofReal_mem_spectrum_complexify_iff X r).mp hμ, rfl⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact (ofReal_mem_spectrum_complexify_iff X r).mpr hr

/-- Coercivity of a real symmetric matrix with a given constant is coercivity of its
complexification with the same constant: both say that the eigenvalues are at least that
constant, and the two spectra correspond under `Matrix.complexify`. -/
private theorem isCoerciveWith_toEuclideanLin_complexify_iff {X : Matrix n n ℝ}
    (hX : X.IsHermitian) (c : ℝ) :
    (toEuclideanLin (complexify X)).IsCoerciveWith c ↔ (toEuclideanLin X).IsCoerciveWith c := by
  have hC : (complexify X).IsHermitian := (isHermitian_complexify_iff X).mpr hX
  rw [LinearMap.IsSymmetric.isCoerciveWith_iff_forall_hasEigenvalue
      (isSymmetric_toEuclideanLin_iff.mpr hC) c,
    LinearMap.IsSymmetric.isCoerciveWith_iff_forall_hasEigenvalue
      (isSymmetric_toEuclideanLin_iff.mpr hX) c]
  simp only [hasEigenvalue_toEuclideanLin_iff]
  constructor
  · intro hc μ hμ
    simpa using hc (μ : ℂ) ((ofReal_mem_spectrum_complexify_iff X μ).mpr hμ)
  · intro hc μ hμ
    rw [hX.spectrum_complexify_eq] at hμ
    obtain ⟨r, hr, rfl⟩ := hμ
    simpa using hc r hr

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- A real matrix is positive definite exactly when its complexification is. -/
private theorem posDef_complexify_iff {X : Matrix n n ℝ} :
    (complexify X).PosDef ↔ X.PosDef := by
  constructor
  · intro hP
    have hX : X.IsHermitian := (isHermitian_complexify_iff X).mp hP.isHermitian
    rw [posDef_iff_isSymmetricCoercive] at hP
    obtain ⟨c, hc, hcw⟩ := hP.isCoercive
    rw [posDef_iff_isSymmetricCoercive]
    exact ⟨isSymmetric_toEuclideanLin_iff.mpr hX, c, hc,
      (isCoerciveWith_toEuclideanLin_complexify_iff hX c).mp hcw⟩
  · intro hP
    have hX : X.IsHermitian := hP.isHermitian
    rw [posDef_iff_isSymmetricCoercive] at hP
    obtain ⟨c, hc, hcw⟩ := hP.isCoercive
    rw [posDef_iff_isSymmetricCoercive]
    exact ⟨isSymmetric_toEuclideanLin_iff.mpr ((isHermitian_complexify_iff X).mpr hX), c, hc,
      (isCoerciveWith_toEuclideanLin_complexify_iff hX c).mpr hcw⟩

/-- A splitting transported along a ring homomorphism: the iteration operator goes along. -/
private theorem iterationOperator_map {R S F : Type*} [Ring R] [Ring S] [FunLike F R S]
    [RingHomClass F R S] (f : F) {a : R} (s : Stationary.Splitting a)
    (t : Stationary.Splitting (f a)) (hm : t.m = f s.m) :
    t.iterationOperator = f s.iterationOperator := by
  obtain ⟨u, hu⟩ := s.isUnit
  have hinv : Ring.inverse (f s.m) = f (Ring.inverse s.m) := by
    rw [← hu, show f (u : R) = ((Units.map (f : R →* S) u : Sˣ) : S) from rfl, Ring.inverse_unit,
      Ring.inverse_unit, Units.coe_map_inv]
    rfl
  rw [Stationary.Splitting.iterationOperator, Stationary.Splitting.iterationOperator, hm, hinv,
    map_sub, map_one, map_mul]

/-- `Matrix.complexify` as a ring homomorphism. -/
private def complexifyRingHom : Matrix n n ℝ →+* Matrix n n ℂ where
  toFun := complexify
  map_one' := complexify_one
  map_mul' := complexify_mul
  map_zero' := complexify_zero
  map_add' := complexify_add

/-- A splitting of a real matrix, carried to the corresponding operator on `EuclideanSpace ℂ n`
by `Matrix.complexify` and `Matrix.toEuclideanCLM`.  This is the bridge that lets the operator
form of the Householder–John theorem be applied to a real matrix. -/
private noncomputable def complexSplitting {a : Matrix n n ℝ} (s : Stationary.Splitting a) :
    Stationary.Splitting (toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify a)) where
  m := toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify s.m)
  isUnit := ((isUnit_complexify_iff _).mpr s.isUnit).map _

private theorem complexSplitting_iterationOperator {a : Matrix n n ℝ}
    (s : Stationary.Splitting a) :
    (complexSplitting s).iterationOperator
      = toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify s.iterationOperator) := by
  have h1 : (Stationary.Splitting.mk (complexify s.m)
      ((isUnit_complexify_iff _).mpr s.isUnit) : Stationary.Splitting
        (complexifyRingHom a)).iterationOperator = complexify s.iterationOperator :=
    iterationOperator_map complexifyRingHom s _ rfl
  rw [← h1]
  exact iterationOperator_map (toEuclideanCLM (n := n) (𝕜 := ℂ)) _ _ rfl

private theorem spectralRadius_complexSplitting {a : Matrix n n ℝ}
    (s : Stationary.Splitting a) :
    spectralRadius ℂ (complexSplitting s).iterationOperator
      = complexSpectralRadius s.iterationOperator := by
  rw [complexSplitting_iterationOperator, complexSpectralRadius]
  simp only [spectralRadius]
  rw [AlgEquiv.spectrum_eq (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))]

/-- An attained lower endpoint of an enclosing interval is below the upper one. -/
private theorem le_of_spectrum_subset {X : Matrix n n ℝ} {lmin lmax : ℝ}
    (hsub : spectrum ℂ (complexify X) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ X) : lmin ≤ lmax := by
  obtain ⟨r, hr, hre⟩ := hsub ((ofReal_mem_spectrum_complexify_iff X lmin).mpr hmin)
  rw [Complex.ofReal_inj] at hre
  exact hre ▸ hr.2

/-- `t ↦ max |1 - t a| |1 - t b|` is bounded below by `(b - a)/(b + a)` for `0 < a ≤ b`: the
convex combination with weights `b/(a+b)`, `a/(a+b)` of `1 - t a` and `-(1 - t b)` is that
constant, whatever `t` is. -/
private theorem le_max_abs_one_sub_mul {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    (b - a) / (b + a) ≤ max |1 - t * a| |1 - t * b| := by
  have hb : 0 < b := ha.trans_le hab
  have hA : 1 - t * a ≤ max |1 - t * a| |1 - t * b| := (le_abs_self _).trans (le_max_left _ _)
  have hB : -(1 - t * b) ≤ max |1 - t * a| |1 - t * b| := (neg_le_abs _).trans (le_max_right _ _)
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < b + a)]
  nlinarith [mul_le_mul_of_nonneg_left hA hb.le, mul_le_mul_of_nonneg_left hB ha.le]

/-- At `t = 2/(a + b)` the two branches of `max |1 - t a| |1 - t b|` are equal, and the common
value `(b - a)/(b + a)` is the lower bound of `le_max_abs_one_sub_mul`: the minimum is attained
there. -/
private theorem max_abs_one_sub_mul_optimal {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    max |1 - 2 / (a + b) * a| |1 - 2 / (a + b) * b| = (b - a) / (b + a) := by
  have hb : 0 < b := ha.trans_le hab
  have hsum : (0 : ℝ) < a + b := by linarith
  have h1 : 1 - 2 / (a + b) * a = (b - a) / (b + a) := by field_simp; ring
  have h2 : 1 - 2 / (a + b) * b = -((b - a) / (b + a)) := by field_simp; ring
  rw [h1, h2, abs_neg, abs_of_nonneg (div_nonneg (by linarith) (by linarith)), max_self]

/-- The spectral radius of `1 - α A` for a real symmetric `A` whose eigenvalues fill
`[lmin, lmax]`. -/
private theorem complexSpectralRadius_one_sub_smul {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {lmin lmax : ℝ} (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ A)
    (hmax : lmax ∈ spectrum ℝ A) {α : ℝ} (hα : α ≠ 0) :
    complexSpectralRadius (1 - α • A) = ENNReal.ofReal (max |1 - α * lmin| |1 - α * lmax|) := by
  have hsub' : spectrum ℂ (complexify A) ⊆ Complex.ofReal '' Set.Icc lmin lmax := by
    rw [hA.spectrum_complexify_eq]
    exact Set.image_mono hsub
  have hrw : (1 : Matrix n n ℝ) - α • A = (1 : ℝ) • 1 + (-α) • A := by module
  rw [hrw, complexSpectralRadius_affine hsub' hmin hmax (neg_ne_zero.mpr hα)]
  ring_nf

end Matrix

/-! ### Richardson's iteration -/

namespace Stationary

namespace Splitting

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Richardson's iteration** `G_α = 1 - α A` for a real symmetric `A` whose eigenvalues fill
`[lmin, lmax]`: `ρ(G_α) = max |1 - α lmin| |1 - α lmax|`.  The spectrum of `G_α` is the image of
that of `A` under `t ↦ 1 - α t`, and `|·|` is convex, so the largest value sits at an endpoint
(Saad, *Iterative Methods for Sparse Linear Systems*, Example 4.1). -/
theorem richardson_complexSpectralRadius_eq {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {lmin lmax : ℝ} (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ A)
    (hmax : lmax ∈ spectrum ℝ A) {α : ℝ} (hα : α ≠ 0) :
    complexSpectralRadius (richardson A hα).iterationOperator
      = ENNReal.ofReal (max |1 - α * lmin| |1 - α * lmax|) := by
  rw [richardson_iterationOperator, complexSpectralRadius_one_sub_smul hA hsub hmin hmax hα]

/-- Richardson's iteration for a symmetric positive definite `A` converges exactly for
`0 < α < 2/λmax` (Saad, *Iterative Methods for Sparse Linear Systems*, Example 4.1;
Atkinson–Han, *Theoretical Numerical Analysis*, Exercise 5.2.3). -/
theorem richardson_complexSpectralRadius_lt_one_iff {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {lmin lmax : ℝ} (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ A)
    (hmax : lmax ∈ spectrum ℝ A) (hpos : 0 < lmin) {α : ℝ} (hα : α ≠ 0) :
    complexSpectralRadius (richardson A hα).iterationOperator < 1 ↔ 0 < α ∧ α < 2 / lmax := by
  have hle : lmin ≤ lmax := (hsub hmin).2
  have hmaxpos : 0 < lmax := hpos.trans_le hle
  rw [richardson_complexSpectralRadius_eq hA hsub hmin hmax hα, ENNReal.ofReal_lt_one, max_lt_iff,
    abs_lt, abs_lt, lt_div_iff₀ hmaxpos]
  constructor
  · rintro ⟨-, h3, h4⟩
    constructor
    · nlinarith
    · nlinarith
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

/-- **The optimal Richardson parameter** is `α = 2/(λmin + λmax)`: it minimizes the spectral
radius of `G_α = 1 - α A` over `α > 0` (Saad, *Iterative Methods for Sparse Linear Systems*,
Example 4.1).  The iteration operator is `Stationary.Splitting.richardson_iterationOperator`;
the minimum value is `richardson_complexSpectralRadius_optimal_eq`. -/
theorem isMinOn_richardson_complexSpectralRadius {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {lmin lmax : ℝ} (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ A)
    (hmax : lmax ∈ spectrum ℝ A) (hpos : 0 < lmin) :
    IsMinOn (fun α : ℝ => complexSpectralRadius (1 - α • A)) (Set.Ioi 0)
      (2 / (lmin + lmax)) := by
  have hle : lmin ≤ lmax := (hsub hmin).2
  have hsum : (0 : ℝ) < lmin + lmax := by linarith
  refine isMinOn_iff.2 fun α hα => ?_
  rw [complexSpectralRadius_one_sub_smul hA hsub hmin hmax (ne_of_gt (div_pos two_pos hsum)),
    complexSpectralRadius_one_sub_smul hA hsub hmin hmax (ne_of_gt hα),
    max_abs_one_sub_mul_optimal hpos hle]
  exact ENNReal.ofReal_le_ofReal (le_max_abs_one_sub_mul hpos hle α)

/-- The value of the optimal Richardson spectral radius, `(λmax - λmin)/(λmax + λmin)` (Saad,
*Iterative Methods for Sparse Linear Systems*, Example 4.1): one less two over the condition
number plus one. -/
theorem richardson_complexSpectralRadius_optimal_eq {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {lmin lmax : ℝ} (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ A)
    (hmax : lmax ∈ spectrum ℝ A) (hpos : 0 < lmin) :
    complexSpectralRadius (1 - (2 / (lmin + lmax)) • A)
      = ENNReal.ofReal ((lmax - lmin) / (lmax + lmin)) := by
  have hle : lmin ≤ lmax := (hsub hmin).2
  have hsum : (0 : ℝ) < lmin + lmax := by linarith
  rw [complexSpectralRadius_one_sub_smul hA hsub hmin hmax (ne_of_gt (div_pos two_pos hsum)),
    max_abs_one_sub_mul_optimal hpos hle]

end Splitting

end Stationary

/-! ### Jacobi over-relaxation, SOR determinant, Kahan -/

namespace Matrix

open Stationary

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The inverse of a nonzero scalar multiple of a unit. -/
private theorem ringInverse_smul {R 𝕜 : Type*} [Ring R] [Field 𝕜] [Algebra 𝕜 R] {c : 𝕜}
    (hc : c ≠ 0) {m : R} (hm : IsUnit m) :
    Ring.inverse (c • m) = c⁻¹ • Ring.inverse m := by
  have h1 : (c • m) * (c⁻¹ • Ring.inverse m) = 1 := by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hc, Ring.mul_inverse_cancel _ hm, one_smul]
  have h2 : (c⁻¹ • Ring.inverse m) * (c • m) = 1 := by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, Ring.inverse_mul_cancel _ hm, one_smul]
  exact Ring.inverse_unit ⟨c • m, c⁻¹ • Ring.inverse m, h1, h2⟩

/-- **Jacobi over-relaxation**: the splitting with `M = ω⁻¹ D` of a matrix with invertible
diagonal.  Its iteration operator is the relaxation `(1 - ω) + ω B` of the Jacobi one
(`Matrix.jorSplitting_iterationOperator`), so `ω = 1` is Jacobi itself. -/
noncomputable def jorSplitting {𝕜 : Type*} [Field 𝕜] (A : Matrix n n 𝕜)
    (h : IsUnit (diagPart A)) {ω : 𝕜} (hω : ω ≠ 0) : Splitting A :=
  ⟨ω⁻¹ • diagPart A, by
    rw [Algebra.smul_def]
    exact ((isUnit_iff_ne_zero.mpr (inv_ne_zero hω)).map (algebraMap 𝕜 (Matrix n n 𝕜))).mul h⟩

/-- The JOR iteration matrix `(1 - ω) 1 + ω B` is the relaxation of the Jacobi iteration matrix
`B = -D⁻¹ (E + F)` towards the identity. -/
theorem jorSplitting_iterationOperator {𝕜 : Type*} [Field 𝕜] (A : Matrix n n 𝕜)
    (h : IsUnit (diagPart A)) {ω : 𝕜} (hω : ω ≠ 0) :
    (jorSplitting A h hω).iterationOperator
      = (1 - ω) • 1 + ω • (jacobiSplitting A h).iterationOperator := by
  have hm : (jorSplitting A h hω).m = ω⁻¹ • diagPart A := rfl
  have hj : (jacobiSplitting A h).m = diagPart A := rfl
  rw [Splitting.iterationOperator, Splitting.iterationOperator, hm, hj,
    ringInverse_smul (inv_ne_zero hω) h, inv_inv, smul_mul_assoc]
  module

/-- **The optimal relaxation parameter of JOR** is `ω = 2/(2 - λmax - λmin)`, where `λmin` and
`λmax` are the extreme eigenvalues of the Jacobi matrix `B`, assumed real (Kress, *Numerical
Analysis*, Thm 4.9).  Only `λmax < 1` is used, which is half of the convergence of the Jacobi
iteration; the JOR iteration operator is `Matrix.jorSplitting_iterationOperator`. -/
theorem jorSplitting_isMinOn_complexSpectralRadius {A : Matrix n n ℝ} (h : IsUnit (diagPart A))
    {lmin lmax : ℝ}
    (hsub : spectrum ℂ (complexify (jacobiSplitting A h).iterationOperator) ⊆
      Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ (jacobiSplitting A h).iterationOperator)
    (hmax : lmax ∈ spectrum ℝ (jacobiSplitting A h).iterationOperator) (hlt : lmax < 1) :
    IsMinOn (fun ω : ℝ => complexSpectralRadius
        ((1 - ω) • 1 + ω • (jacobiSplitting A h).iterationOperator)) (Set.Ioi 0)
      (2 / (2 - lmax - lmin)) := by
  have hle : lmin ≤ lmax := le_of_spectrum_subset hsub hmin
  have ha : (0 : ℝ) < 1 - lmax := by linarith
  have hab : 1 - lmax ≤ 1 - lmin := by linarith
  have key : ∀ ω : ℝ, ω ≠ 0 →
      complexSpectralRadius ((1 - ω) • 1 + ω • (jacobiSplitting A h).iterationOperator)
        = ENNReal.ofReal (max |1 - ω * (1 - lmax)| |1 - ω * (1 - lmin)|) := by
    intro ω hω
    have e1 : 1 - ω + ω * lmin = 1 - ω * (1 - lmin) := by ring
    have e2 : 1 - ω + ω * lmax = 1 - ω * (1 - lmax) := by ring
    rw [complexSpectralRadius_affine hsub hmin hmax hω, e1, e2, max_comm]
  have hopt : (2 : ℝ) - lmax - lmin = 1 - lmax + (1 - lmin) := by ring
  have hoptpos : (0 : ℝ) < 2 / (2 - lmax - lmin) := div_pos two_pos (by linarith)
  refine isMinOn_iff.2 fun ω hω => ?_
  rw [key _ (ne_of_gt hoptpos), key _ (ne_of_gt hω), hopt,
    max_abs_one_sub_mul_optimal ha hab]
  exact ENNReal.ofReal_le_ofReal (le_max_abs_one_sub_mul ha hab ω)

variable [LinearOrder n]

/-- **The determinant of the SOR iteration matrix** is `(1 - ω)ⁿ`: it is the inverse of the lower
triangular `D - ωE`, whose diagonal is that of `A`, times the upper triangular
`(1 - ω) D + ωF`, whose diagonal is `(1 - ω)` times that of `A` (Kress, *Numerical Analysis*,
proof of Thm 4.11). -/
theorem det_sorSplitting_iterationOperator {𝕜 : Type*} [Field 𝕜] (A : Matrix n n 𝕜)
    (h : IsUnit (diagPart A)) {ω : 𝕜} (hω : ω ≠ 0) :
    (A.sorSplitting h hω).iterationOperator.det = (1 - ω) ^ Fintype.card n := by
  have hne : ∀ i, A i i ≠ 0 := (isUnit_diagPart_iff A).mp h
  have hprod : (∏ i, A i i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  have hL : (diagPart A + ω • strictLower A).IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp [hij'.ne, asymm hij']
  have hU : ((1 - ω) • diagPart A - ω • strictUpper A).IsUpperTriangular := by
    intro i j hij
    have hij' : j < i := hij
    simp [hij'.ne', asymm hij']
  rw [sorSplitting_iterationOperator, det_mul, det_nonsing_inv, Ring.inverse_eq_inv,
    det_of_isLowerTriangular _ hL, det_of_isUpperTriangular hU]
  have hLd : ∀ i, (diagPart A + ω • strictLower A) i i = A i i := fun i => by simp
  have hUd : ∀ i, ((1 - ω) • diagPart A - ω • strictUpper A) i i = (1 - ω) * A i i :=
    fun i => by simp
  simp only [hLd, hUd, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  field_simp

/-- **Kahan's necessary condition**: the SOR iteration can converge only for `0 < ω < 2`
(Kress, *Numerical Analysis*, Thm 4.11).  The powers of the iteration matrix tend to `0`, so its
determinant `(1 - ω)ⁿ` has modulus `< 1`, which for a nonempty index type forces
`|1 - ω| < 1`. -/
theorem lt_two_of_sorSplitting_complexSpectralRadius_lt_one [Nonempty n] {A : Matrix n n ℝ}
    (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0)
    (hρ : complexSpectralRadius (A.sorSplitting h hω).iterationOperator < 1) :
    0 < ω ∧ ω < 2 := by
  have hpow : Tendsto (fun k => (A.sorSplitting h hω).iterationOperator ^ k) atTop (𝓝 0) :=
    (tendsto_pow_iff_complexSpectralRadius_lt_one _).mpr hρ
  have hcont : Continuous fun M : Matrix n n ℝ => M.det := continuous_id.matrix_det
  have hdet := (hcont.tendsto 0).comp hpow
  rw [det_zero] at hdet
  simp only [Function.comp_def, det_pow, det_sorSplitting_iterationOperator,
    tendsto_pow_atTop_nhds_zero_iff, abs_pow] at hdet
  rw [pow_lt_one_iff_of_nonneg (abs_nonneg _) Fintype.card_ne_zero, abs_lt] at hdet
  exact ⟨by linarith [hdet.2], by linarith [hdet.1]⟩

/-- The Householder–John matrix `Q = M + Mᴴ - A` of the SOR splitting of a symmetric `A` is
`(2/ω - 1) D`: the strictly lower part of `M` and the strictly upper part of `Mᴴ` reassemble
`A - D`. -/
private theorem sorSplitting_m_add_conjTranspose_sub {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    (A.sorSplitting h hω).m + ((A.sorSplitting h hω).m)ᴴ - A = (2 / ω - 1) • diagPart A := by
  have hm : (A.sorSplitting h hω).m = ω⁻¹ • diagPart A + strictLower A := rfl
  have hsymm : ∀ i j, A j i = A i j := fun i j => by
    have := congrFun (congrFun hA.eq i) j
    simpa using this
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp [hm, hij, hij.ne, hij.ne', asymm hij, hsymm i j]
  · have hMii : (A.sorSplitting h hω).m i i = ω⁻¹ * A i i := by simp [hm]
    have hlhs : ((A.sorSplitting h hω).m + ((A.sorSplitting h hω).m)ᴴ - A) i i
        = ω⁻¹ * A i i + ω⁻¹ * A i i - A i i := by
      rw [sub_apply, add_apply, conjTranspose_apply, hMii, star_trivial]
    have hrhs : ((2 / ω - 1) • diagPart A) i i = (2 / ω - 1) * A i i := by simp
    rw [hlhs, hrhs, show (2 / ω - 1) = 2 * ω⁻¹ - 1 from by rw [div_eq_mul_inv]]
    ring
  · simp [hm, hij, hij.ne, hij.ne', asymm hij, hsymm j i]

/-- **The Ostrowski–Reich theorem for SOR** (Saad, *Iterative Methods for Sparse Linear Systems*,
Thm 4.10; Kress, *Numerical Analysis*, Thm 4.12).  For a real symmetric `A` with positive diagonal
and a relaxation parameter `0 < ω < 2`, the SOR iteration converges exactly when `A` is positive
definite.

Both directions are the operator statements
`Stationary.Splitting.spectralRadius_lt_one_of_isSymmetricCoercive` and
`Stationary.Splitting.isCoercive_of_spectralRadius_lt_one`, applied on `EuclideanSpace ℂ n` to the
complexification, whose Householder–John matrix is `M + Mᴴ - A = (2/ω - 1) D`, positive definite
precisely because `0 < ω < 2`. -/
theorem sorSplitting_complexSpectralRadius_lt_one_iff_posDef {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (hd : ∀ i, 0 < A i i) (h : IsUnit (diagPart A)) {ω : ℝ}
    (hω0 : 0 < ω) (hω2 : ω < 2) :
    complexSpectralRadius (A.sorSplitting h hω0.ne').iterationOperator < 1 ↔ A.PosDef := by
  set s := A.sorSplitting h hω0.ne' with hs
  -- the Householder–John matrix is a positive multiple of the diagonal
  have hcpos : 0 < 2 / ω - 1 := by
    rw [sub_pos, lt_div_iff₀ hω0]
    linarith
  have hQpd : ((2 / ω - 1) • diagPart A).PosDef := by
    have hdiag : (2 / ω - 1) • diagPart A = diagonal fun i => (2 / ω - 1) * A i i := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [hdiag, posDef_diagonal_iff]
    exact fun i => mul_pos hcpos (hd i)
  have hQeq : (complexSplitting s).m + ContinuousLinearMap.adjoint (complexSplitting s).m
      - toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A)
      = toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify ((2 / ω - 1) • diagPart A)) := by
    have hm : (complexSplitting s).m
        = toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify s.m) := rfl
    rw [hm, ← ContinuousLinearMap.star_eq_adjoint, ← map_star, ← map_add, ← map_sub,
      ← sorSplitting_m_add_conjTranspose_sub hA h hω0.ne', complexify_sub, complexify_add,
      complexify_conjTranspose]
    rfl
  have hQ : (((complexSplitting s).m + ContinuousLinearMap.adjoint (complexSplitting s).m
      - toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A) :
        EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
      EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).IsCoercive := by
    rw [hQeq, coe_toEuclideanCLM_eq_toEuclideanLin]
    exact ((posDef_iff_isSymmetricCoercive _).mp (posDef_complexify_iff.mpr hQpd)).isCoercive
  have hsym : ((toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A) :
      EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
      EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).IsSymmetric := by
    rw [coe_toEuclideanCLM_eq_toEuclideanLin]
    exact isSymmetric_toEuclideanLin_iff.mpr ((isHermitian_complexify_iff A).mpr hA)
  rw [← spectralRadius_complexSplitting s]
  constructor
  · intro hlt
    have hco := Stationary.Splitting.isCoercive_of_spectralRadius_lt_one
      (complexSplitting s) hsym hQ hlt
    rw [← posDef_complexify_iff, posDef_iff_isSymmetricCoercive]
    rw [coe_toEuclideanCLM_eq_toEuclideanLin] at hsym hco
    exact ⟨hsym, hco⟩
  · intro hP
    refine Stationary.Splitting.spectralRadius_lt_one_of_isSymmetricCoercive
      (complexSplitting s) ?_ hQ
    rw [coe_toEuclideanCLM_eq_toEuclideanLin]
    exact (posDef_iff_isSymmetricCoercive _).mp (posDef_complexify_iff.mpr hP)

end Matrix
