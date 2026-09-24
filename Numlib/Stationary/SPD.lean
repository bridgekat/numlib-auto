import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Operator.Banach
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Eigen.Pencil
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Stationary.Splitting

/-!
# Stationary iterations for symmetric positive definite systems

The convergence theory of the classical splittings when the matrix is symmetric positive definite,
stated at the operator level wherever the proof allows.

* `Stationary.Splitting.spectralRadius_lt_one_of_isSymmetricCoercive` is the **Householder–John /
  Ostrowski–Reich theorem** ([saad2003iterative] Thm 4.10; [kress1998numerical] Thm 4.12;
  [quarteroni2000numerical] Property 4.2): for a symmetric coercive `A` on a finite-dimensional
  complex inner product space and a splitting `A = M - N` whose `Q = M + Mᴴ - A` is coercive, the
  iteration operator `M⁻¹ N` has spectral radius `< 1`.
  `Stationary.Splitting.isCoercive_of_spectralRadius_lt_one` is its converse: with `Q` coercive,
  convergence forces `A` to be positive definite.  For a real matrix the two directions are
  `Stationary.Splitting.complexSpectralRadius_lt_one_of_posDef` and
  `Stationary.Splitting.posDef_of_complexSpectralRadius_lt_one`, with `Q = M + Mᵀ - A`; the Jacobi
  (`2D - A` positive definite, [quarteroni2000numerical] Theorem 4.3), Gauss–Seidel (Theorem 4.5),
  SOR (Property 4.3, as the equivalence `Matrix.sorSplitting_complexSpectralRadius_lt_one_iff`) and
  SSOR (`Matrix.ssorSplitting_complexSpectralRadius_lt_one`, §4.2.6) criteria are its instances.
* **The energy-norm theory.**  The energy identity `‖G e‖_A² = ‖e‖_A² - ⟪Q y, y⟫`, `y = M⁻¹ A e`
  (`Stationary.Splitting.energyNorm_sq_iterationOperator_apply`) gives the strict decrease of the
  `A`-norm of the error in one step (`Stationary.Splitting.energyNorm_iterationOperator_apply_lt`)
  and, by compactness, a uniform contraction factor `q < 1`
  (`Stationary.Splitting.exists_energyNorm_iterationOperator_apply_le`).  When `M` is symmetric the
  iteration operator is self-adjoint in the `A`- and in the `M`-inner product
  (`Stationary.Splitting.energyInner_iterationOperator_comm`,
  `Stationary.Splitting.inner_m_iterationOperator_comm`), and then its `A`- and `M`-operator norms
  are the spectral radius: `‖G e‖_A ≤ ρ(G) ‖e‖_A`, attained at an eigenvector
  (`Stationary.Splitting.energyNorm_iterationOperator_apply_le_spectralRadius`,
  `Stationary.Splitting.norm_m_iterationOperator_apply_le_spectralRadius`,
  `Stationary.Splitting.exists_energyNorm_iterationOperator_apply_eq_spectralRadius`), which is
  [quarteroni2000numerical] Property 4.1 and the engine of its Corollary 4.1.  The real-matrix forms
  are `Stationary.Splitting.energyNorm_mulVec_iterationOperator_lt`,
  `Stationary.Splitting.exists_energyNorm_mulVec_iterationOperator_le` and
  `Stationary.Splitting.energyNorm_mulVec_iterationOperator_le_complexSpectralRadius`.
* **Richardson's iteration** `G_α = 1 - α M` for a real matrix `M` with real spectrum in
  `[lmin, lmax]`: `ρ(G_α) = max |1 - α lmin| |1 - α lmax|`
  (`Stationary.Splitting.complexSpectralRadius_one_sub_smul_eq`), convergence exactly for
  `0 < α < 2/lmax` (`Stationary.Splitting.complexSpectralRadius_one_sub_smul_lt_one_iff`), and the
  optimal parameter `α = 2/(lmin + lmax)` with radius `(lmax - lmin)/(lmax + lmin)`
  (`Stationary.Splitting.isMinOn_complexSpectralRadius_one_sub_smul`,
  `Stationary.Splitting.complexSpectralRadius_one_sub_smul_optimal_eq`), [quarteroni2000numerical]
  Theorem 4.9; the Hermitian case `M = A` is
  `Stationary.Splitting.richardson_complexSpectralRadius_eq` and its companions
  ([saad2003iterative] Example 4.1; [han2009theoretical] Exercise 5.2.3).
* `Matrix.jorSplitting` is Jacobi over-relaxation, `M = ω⁻¹ D`, whose optimal parameter is
  `2/(2 - λmax - λmin)` for a Jacobi matrix with real eigenvalues ([kress1998numerical] Thm 4.9);
  it converges for `0 < ω ≤ 1` whenever Jacobi does ([quarteroni2000numerical] Theorem 4.6) and,
  for a positive
  definite `A`, exactly for `0 < ω < 2/ρ(D⁻¹ A)` (Theorem 4.4,
  `Matrix.jorSplitting_complexSpectralRadius_lt_one_iff_of_posDef`, through the real positive
  spectrum of the pencil `D⁻¹ A`, `Matrix.spectrum_inv_mul_subset_of_posDef`).
* `Matrix.det_sorSplitting_iterationOperator` computes `det G_ω = (1 - ω)ⁿ`, from which
  **Kahan's bound** `|1 - ω| ≤ ρ(G_ω)` ([quarteroni2000numerical] Theorem 4.7,
  `Matrix.abs_one_sub_le_sorSplitting_complexSpectralRadius`) and the necessary condition
  `0 < ω < 2` for SOR to converge ([kress1998numerical] Thm 4.11,
  `Matrix.lt_two_of_sorSplitting_complexSpectralRadius_lt_one`) follow.
* **SSOR.**  The SSOR preconditioner is symmetric (`Matrix.ssorSplitting_m_isSymm`), positive
  definite for `0 < ω < 2` as soon as `A` is symmetric with positive diagonal
  (`Matrix.ssorSplitting_m_posDef_of_diag_pos`, [golub2013matrix] (11.2.24); for positive definite
  `A`, `Matrix.ssorSplitting_m_posDef`) and dominates `A`
  (`Matrix.ssorSplitting_m_sub_posSemidef`, the factorization `P - A = c ((1-ω)D - ωL) D⁻¹ ((1-ω)D -
  ωU)`); hence SSOR converges for a positive definite `A` and `0 < ω < 2`, and its iteration matrix
  is `A`-self-adjoint and `A`-positive semidefinite
  (`Matrix.ssorSplitting_iterationOperator_posSemidef_energy`), which is the correct reading of
  [quarteroni2000numerical] Property 4.5 ("`B_SGS` is symmetric positive definite" is false as
  printed: for a diagonal `A`, `B_SGS = 0`).

Everything spectral is stated over `ℂ`, because the real spectrum of a real matrix is the wrong
object: `Matrix.complexSpectralRadius` is the spectral radius of the complexification, and the
operator statements are for a complex inner product space, which a real matrix reaches through
`Stationary.Splitting.euclidean`, the splitting of `Matrix.toEuclideanCLM (Matrix.complexify A)`
induced by a real splitting.
-/

open Filter Topology
open scoped ENNReal NNReal ComplexOrder

namespace Stationary

namespace Splitting

section Comm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {A : E →L[ℂ] E}
  (s : Splitting A)

/-- One step of the iteration operator subtracts the preconditioned residual:
`G x = x - M⁻¹ A x`. -/
theorem iterationOperator_apply (x : E) :
    s.iterationOperator x = x - Ring.inverse s.m (A x) := by
  rw [iterationOperator, sub_apply, one_apply_eq_self, mul_apply_eq_comp]

/-- `M (M⁻¹ w) = w`. -/
theorem m_ringInverse_apply (w : E) : s.m (Ring.inverse s.m w) = w := by
  rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel _ s.isUnit, one_apply_eq_self]

/-- `M⁻¹ (M w) = w`. -/
theorem ringInverse_m_apply (w : E) : Ring.inverse s.m (s.m w) = w := by
  rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ s.isUnit, one_apply_eq_self]

/-- `⟪M⁻¹ u, v⟫ = ⟪u, M⁻¹ v⟫` for a symmetric unit `M`. -/
private theorem inner_ringInverse_m_comm (hM : (s.m : E →ₗ[ℂ] E).IsSymmetric) (u v : E) :
    inner ℂ (Ring.inverse s.m u) v = inner ℂ u (Ring.inverse s.m v) := by
  have hM' : ∀ x y, inner ℂ (s.m x) y = inner ℂ x (s.m y) := fun x y => hM x y
  conv_lhs => rw [← m_ringInverse_apply s v]
  rw [← hM', m_ringInverse_apply]

/-- **The iteration operator is self-adjoint in the `A`-inner product** when `A` and `M` are
symmetric: `⟪A (G x), y⟫ = ⟪A x, G y⟫`, because `A G = A - A M⁻¹ A` is symmetric.  This is what
makes the `A`-operator norm of `G` its spectral radius ([quarteroni2000numerical] Property 4.1). -/
theorem energyInner_iterationOperator_comm (hA : (A : E →ₗ[ℂ] E).IsSymmetric)
    (hM : (s.m : E →ₗ[ℂ] E).IsSymmetric) (x y : E) :
    inner ℂ (A (s.iterationOperator x)) y = inner ℂ (A x) (s.iterationOperator y) := by
  have hA' : ∀ u v, inner ℂ (A u) v = inner ℂ u (A v) := fun u v => hA u v
  rw [iterationOperator_apply, iterationOperator_apply, map_sub, inner_sub_left, inner_sub_right,
    hA' (Ring.inverse s.m (A x)) y, inner_ringInverse_m_comm s hM, hA']

/-- **The iteration operator is self-adjoint in the `M`-inner product** when `A` and `M` are
symmetric: `⟪M (G x), y⟫ = ⟪M x, G y⟫`, because `M G = M - A` is symmetric. -/
theorem inner_m_iterationOperator_comm (hA : (A : E →ₗ[ℂ] E).IsSymmetric)
    (hM : (s.m : E →ₗ[ℂ] E).IsSymmetric) (x y : E) :
    inner ℂ (s.m (s.iterationOperator x)) y = inner ℂ (s.m x) (s.iterationOperator y) := by
  have hA' : ∀ u v, inner ℂ (A u) v = inner ℂ u (A v) := fun u v => hA u v
  have hM' : ∀ u v, inner ℂ (s.m u) v = inner ℂ u (s.m v) := fun u v => hM u v
  rw [iterationOperator_apply, iterationOperator_apply, map_sub, m_ringInverse_apply,
    inner_sub_left, inner_sub_right, hM' x y, hA' x y, ← inner_ringInverse_m_comm s hM,
    ringInverse_m_apply]

/-- The increment `e - G e = M⁻¹ A e` of a step is nonzero for `e ≠ 0` when `A` is coercive. -/
theorem sub_iterationOperator_apply_ne_zero (hA : (A : E →ₗ[ℂ] E).IsCoercive) {e : E}
    (he : e ≠ 0) : e - s.iterationOperator e ≠ 0 := by
  rw [iterationOperator_apply, sub_sub_cancel]
  intro h
  have hAe : A e = 0 := by
    have := congrArg s.m h
    rwa [m_ringInverse_apply, map_zero] at this
  exact he (hA.injective (by simp [hAe]))

end Comm

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The quadratic form of `Q = M + Mᴴ - A` is `2 re ⟪M x, x⟫ - re ⟪A x, x⟫`: the adjoint contributes
the conjugate of the form of `M`. -/
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
/-- `M (x - G x) = A x` for the iteration operator `G = 1 - M⁻¹ A`: the increment of one step is the
preconditioned residual. -/
private theorem apply_sub_iterationOperator {A : E →L[ℂ] E} (s : Splitting A) (e : E) :
    s.m (e - s.iterationOperator e) = A e := by
  have hop : s.iterationOperator e = e - (Ring.inverse s.m) (A e) := by
    rw [Splitting.iterationOperator, sub_apply, one_apply_eq_self, mul_apply_eq_comp]
  have hd : e - s.iterationOperator e = (Ring.inverse s.m) (A e) := by rw [hop]; abel
  rw [hd, ← mul_apply_eq_comp, Ring.mul_inverse_cancel _ s.isUnit, one_apply_eq_self]

/-- **The energy identity of a splitting.**  For symmetric `A` the `A`-form drops in one step of the
iteration by exactly the `Q`-form of the increment, `Q = M + Mᴴ - A`: `⟪A e, e⟫ - ⟪A G e, G e⟫ = ⟪Q
(e - G e), e - G e⟫`.  Both halves of the Householder–John theorem are read off this identity. -/
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
coercive on a finite-dimensional complex inner product space and `A = M - N` is a splitting whose `Q
= M + Mᴴ - A` is coercive, then the iteration operator `M⁻¹ N` has spectral radius `< 1`, so the
stationary iteration converges ([saad2003iterative], Thm 4.10; [kress1998numerical], Thm 4.12 is the
case `M = ω⁻¹ D - E`).

The proof is the Rayleigh-quotient identity at an eigenpair `M⁻¹ N x = μ x`: it gives `A x = (1 - μ)
M x`, and comparing the `A`- and `Q`-forms at `x` yields `(1 - |μ|²) ⟪A x, x⟫ = |1 - μ|² ⟪Q x, x⟫`,
where both forms are positive. -/
theorem spectralRadius_lt_one_of_isSymmetricCoercive {A : E →L[ℂ] E} (s : Splitting A)
    (hA : (A : E →ₗ[ℂ] E).IsSymmetricCoercive)
    (hQ : ((s.m + ContinuousLinearMap.adjoint s.m - A : E →L[ℂ] E) : E →ₗ[ℂ] E).IsCoercive) :
    spectralRadius ℂ s.iterationOperator < 1 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : Subsingleton (E →L[ℂ] E) := ⟨fun _ _ => by ext x; exact Subsingleton.elim _ _⟩
    simp
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

/-- **The converse of the Householder–John theorem** ([saad2003iterative], Thm 4.10, "only if").
For symmetric `A` and a splitting with coercive `Q = M + Mᴴ - A`, convergence of the iteration
forces `A` to be coercive, i.e. positive definite.

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


/-- **The energy identity of a splitting**, made public: for symmetric `A` and `G = M⁻¹ N`,
`re ⟪A (G e), G e⟫ = re ⟪A e, e⟫ - re ⟪Q (e - G e), e - G e⟫` with `Q = M + Mᴴ - A`; since
`e - G e = M⁻¹ A e`, this is `‖G e‖_A² = ‖e‖_A² - ⟪Q y, y⟫` with `y = M⁻¹ A e`.  Both halves of the
Householder–John theorem and the monotonicity of the energy norm are read off it. -/
theorem energyNorm_sq_iterationOperator_apply {A : E →L[ℂ] E} (s : Splitting A)
    (hA : (A : E →ₗ[ℂ] E).IsSymmetric) (e : E) :
    (inner ℂ (A (s.iterationOperator e)) (s.iterationOperator e)).re =
      (inner ℂ (A e) e).re -
        (inner ℂ ((s.m + ContinuousLinearMap.adjoint s.m - A) (e - s.iterationOperator e))
          (e - s.iterationOperator e)).re := by
  have h := congrArg Complex.re (energy_identity s hA e)
  rw [Complex.sub_re] at h
  linarith

/-- **Monotone convergence in the energy norm** ([quarteroni2000numerical] Property 4.2 and Theorem
4.5, monotonicity clause): if `A` is symmetric coercive and `Q = M + Mᴴ - A` is coercive, one step
strictly decreases the `A`-norm of a nonzero error.  From the energy identity, since `⟪Q y, y⟫ > 0`
for `y = M⁻¹ A e ≠ 0`. -/
theorem energyNorm_iterationOperator_apply_lt {A : E →L[ℂ] E} (s : Splitting A)
    (hA : (A : E →ₗ[ℂ] E).IsSymmetricCoercive)
    (hQ : ((s.m + ContinuousLinearMap.adjoint s.m - A : E →L[ℂ] E) : E →ₗ[ℂ] E).IsCoercive)
    {e : E} (he : e ≠ 0) :
    energyNorm (A : E →ₗ[ℂ] E) (s.iterationOperator e) < energyNorm (A : E →ₗ[ℂ] E) e := by
  have hQpos := hQ.inner_self_pos (sub_iterationOperator_apply_ne_zero s hA.isCoercive he)
  have hid : RCLike.re (inner ℂ ((A : E →ₗ[ℂ] E) (s.iterationOperator e)) (s.iterationOperator e))
      = RCLike.re (inner ℂ ((A : E →ₗ[ℂ] E) e) e) -
        RCLike.re (inner ℂ (((s.m + ContinuousLinearMap.adjoint s.m - A : E →L[ℂ] E) : E →ₗ[ℂ] E)
          (e - s.iterationOperator e)) (e - s.iterationOperator e)) :=
    energyNorm_sq_iterationOperator_apply s hA.isSymmetric e
  have h0 : 0 ≤ RCLike.re (inner ℂ ((A : E →ₗ[ℂ] E) (s.iterationOperator e))
      (s.iterationOperator e)) := hA.isPositive.re_inner_nonneg_left _
  unfold energyNorm
  exact Real.sqrt_lt_sqrt h0 (by linarith)

section EnergySpace

variable {A : E →L[ℂ] E} (s : Splitting A) {B : E →ₗ[ℂ] E} (hB : B.IsSymmetricCoercive)

/-- The iteration operator transported to the energy space `WithEnergy B hB` of a symmetric
coercive `B`, along `WithEnergy.equiv`; it is continuous by finite dimension. -/
noncomputable def energyIterationOperator :
    WithEnergy B hB →L[ℂ] WithEnergy B hB :=
  LinearMap.toContinuousLinearMap
    ((WithEnergy.equiv B hB).conjAlgEquiv (R := ℂ) (s.iterationOperator : E →ₗ[ℂ] E))

/-- The transported operator acts on a transported vector as `G` does. -/
theorem energyIterationOperator_apply (x : E) :
    energyIterationOperator s hB (WithEnergy.equiv B hB x)
      = WithEnergy.equiv B hB (s.iterationOperator x) := by
  simp [energyIterationOperator]

/-- Transport does not change the spectrum. -/
theorem spectrum_energyIterationOperator :
    spectrum ℂ (energyIterationOperator s hB) = spectrum ℂ s.iterationOperator := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ _
  rw [ContinuousLinearMap.spectrum_eq, ContinuousLinearMap.spectrum_eq, energyIterationOperator,
    LinearMap.coe_toContinuousLinearMap, AlgEquiv.spectrum_eq]

/-- Transport does not change the spectral radius. -/
theorem spectralRadius_energyIterationOperator :
    spectralRadius ℂ (energyIterationOperator s hB) = spectralRadius ℂ s.iterationOperator := by
  simp only [spectralRadius_eq_of_unital, spectrum_energyIterationOperator]

/-- The transported operator is self-adjoint on the energy space as soon as `G` is symmetric in the
`B`-inner product. -/
theorem isSelfAdjoint_energyIterationOperator
    (hcomm : ∀ x y, inner ℂ (B (s.iterationOperator x)) y = inner ℂ (B x) (s.iterationOperator y)) :
    IsSelfAdjoint (energyIterationOperator s hB) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  obtain ⟨x, rfl⟩ := (WithEnergy.equiv B hB).surjective u
  obtain ⟨y, rfl⟩ := (WithEnergy.equiv B hB).surjective v
  change inner ℂ (energyIterationOperator s hB (WithEnergy.equiv B hB x)) (WithEnergy.equiv B hB y)
    = inner ℂ (WithEnergy.equiv B hB x) (energyIterationOperator s hB (WithEnergy.equiv B hB y))
  rw [energyIterationOperator_apply, energyIterationOperator_apply, WithEnergy.inner_equiv,
    WithEnergy.inner_equiv]
  exact hcomm x y

include hB in
/-- **The `B`-operator norm of a `B`-symmetric iteration operator is its spectral radius**: for
every `e`, `‖G e‖_B ≤ ρ(G) ‖e‖_B`.  On the energy space `G` is self-adjoint, and a self-adjoint
operator on a Hilbert space has norm equal to its spectral radius
(`IsSelfAdjoint.spectralRadius_eq_nnnorm`). -/
theorem energyNorm_iterationOperator_apply_le_spectralRadius_of_comm
    (hcomm : ∀ x y, inner ℂ (B (s.iterationOperator x)) y = inner ℂ (B x) (s.iterationOperator y))
    (e : E) :
    energyNorm B (s.iterationOperator e) ≤
      (spectralRadius ℂ s.iterationOperator).toReal * energyNorm B e := by
  have hρ : (spectralRadius ℂ s.iterationOperator).toReal = ‖energyIterationOperator s hB‖ := by
    rw [← spectralRadius_energyIterationOperator s hB,
      (isSelfAdjoint_energyIterationOperator s hB hcomm).spectralRadius_eq_nnnorm]
    simp
  rw [hρ, ← WithEnergy.norm_equiv, ← WithEnergy.norm_equiv, ← energyIterationOperator_apply]
  exact (energyIterationOperator s hB).le_opNorm _

include hB in
/-- **The spectral radius is attained in every energy norm**: on a nontrivial space there is `e ≠ 0`
with `‖G e‖_B = ρ(G) ‖e‖_B`, namely an eigenvector for an eigenvalue of maximal modulus.  No
symmetry is needed. -/
theorem exists_energyNorm_iterationOperator_apply_eq_spectralRadius [Nontrivial E] :
    ∃ e : E, e ≠ 0 ∧ energyNorm B (s.iterationOperator e) =
      (spectralRadius ℂ s.iterationOperator).toReal * energyNorm B e := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ _
  obtain ⟨μ, hμ, hμρ⟩ := spectrum.exists_nnnorm_eq_spectralRadius s.iterationOperator
  rw [ContinuousLinearMap.spectrum_eq] at hμ
  obtain ⟨e, he, he0⟩ :=
    (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ).exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at he
  have hGe : s.iterationOperator e = μ • e := he
  refine ⟨e, he0, ?_⟩
  rw [hGe, ← WithEnergy.norm_equiv B hB, ← WithEnergy.norm_equiv B hB, map_smul, norm_smul, ← hμρ]
  simp

end EnergySpace

/-- **The uniform energy contraction** `‖G‖_A < 1` ([quarteroni2000numerical] Property 4.2,
`ρ(B) ≤ ‖B‖_A < 1`): under the hypotheses of `energyNorm_iterationOperator_apply_lt` there is
`q < 1` with `‖G e‖_A ≤ q ‖e‖_A` for every `e`.  The pointwise strict decrease becomes uniform on
the compact unit sphere of the energy space, where the `A`-norm of `G e` attains its maximum. -/
theorem exists_energyNorm_iterationOperator_apply_le {A : E →L[ℂ] E} (s : Splitting A)
    (hA : (A : E →ₗ[ℂ] E).IsSymmetricCoercive)
    (hQ : ((s.m + ContinuousLinearMap.adjoint s.m - A : E →L[ℂ] E) : E →ₗ[ℂ] E).IsCoercive) :
    ∃ q : ℝ, q < 1 ∧ ∀ e : E, energyNorm (A : E →ₗ[ℂ] E) (s.iterationOperator e) ≤
      q * energyNorm (A : E →ₗ[ℂ] E) e := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact ⟨0, zero_lt_one, fun e => by simp [Subsingleton.elim e 0, energyNorm]⟩
  set T := energyIterationOperator s hA with hT
  have hne : (Metric.sphere (0 : WithEnergy (A : E →ₗ[ℂ] E) hA) 1).Nonempty := by
    obtain ⟨e₀, he₀⟩ := exists_ne (0 : E)
    have h0 : ‖WithEnergy.equiv (A : E →ₗ[ℂ] E) hA e₀‖ ≠ 0 := by
      rw [WithEnergy.norm_equiv]
      exact (hA.energyNorm_pos he₀).ne'
    refine ⟨‖WithEnergy.equiv (A : E →ₗ[ℂ] E) hA e₀‖⁻¹ • WithEnergy.equiv (A : E →ₗ[ℂ] E) hA e₀, ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h0]
  obtain ⟨u₀, hu₀, hmax⟩ := (isCompact_sphere (0 : WithEnergy (A : E →ₗ[ℂ] E) hA) 1).exists_isMaxOn
    hne (continuous_norm.comp T.continuous).continuousOn
  have hu₀' : ‖u₀‖ = 1 := mem_sphere_zero_iff_norm.mp hu₀
  refine ⟨‖T u₀‖, ?_, fun e => ?_⟩
  · obtain ⟨x₀, rfl⟩ := (WithEnergy.equiv (A : E →ₗ[ℂ] E) hA).surjective u₀
    have hx₀ : x₀ ≠ 0 := by
      rintro rfl
      simp at hu₀'
    have := energyNorm_iterationOperator_apply_lt s hA hQ hx₀
    rwa [← WithEnergy.norm_equiv (A : E →ₗ[ℂ] E) hA, ← WithEnergy.norm_equiv (A : E →ₗ[ℂ] E) hA,
      ← energyIterationOperator_apply, hu₀'] at this
  · rcases eq_or_ne e 0 with rfl | he
    · simp [energyNorm]
    · set u := WithEnergy.equiv (A : E →ₗ[ℂ] E) hA e with hu
      have hu0 : ‖u‖ ≠ 0 := by
        rw [hu, WithEnergy.norm_equiv]
        exact (hA.energyNorm_pos he).ne'
      have hnc : ‖((‖u‖⁻¹ : ℝ) : ℂ)‖ = ‖u‖⁻¹ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
      have hv : ((‖u‖⁻¹ : ℝ) : ℂ) • u ∈ Metric.sphere (0 : WithEnergy (A : E →ₗ[ℂ] E) hA) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, hnc, inv_mul_cancel₀ hu0]
      have h1 : ‖T (((‖u‖⁻¹ : ℝ) : ℂ) • u)‖ ≤ ‖T u₀‖ := hmax hv
      rw [map_smul, norm_smul, hnc] at h1
      have h2 : ‖T u‖ ≤ ‖T u₀‖ * ‖u‖ := by
        have := mul_le_mul_of_nonneg_left h1 (norm_nonneg u)
        rwa [← mul_assoc, mul_inv_cancel₀ hu0, one_mul, mul_comm] at this
      rwa [hu, energyIterationOperator_apply, WithEnergy.norm_equiv, WithEnergy.norm_equiv] at h2

/-- **`ρ(G) = ‖G‖_A`** ([quarteroni2000numerical] Property 4.1, the `A`-norm clause, as the
inequality `‖G e‖_A ≤ ρ(G) ‖e‖_A` for every `e`;
`exists_energyNorm_iterationOperator_apply_eq_spectralRadius` is the attainment): for a symmetric
coercive `A` and a splitting with symmetric `M`, the `A`-operator norm of `G` is its spectral
radius. -/
theorem energyNorm_iterationOperator_apply_le_spectralRadius {A : E →L[ℂ] E} (s : Splitting A)
    (hA : (A : E →ₗ[ℂ] E).IsSymmetricCoercive) (hM : (s.m : E →ₗ[ℂ] E).IsSymmetric) (e : E) :
    energyNorm (A : E →ₗ[ℂ] E) (s.iterationOperator e) ≤
      (spectralRadius ℂ s.iterationOperator).toReal * energyNorm (A : E →ₗ[ℂ] E) e :=
  energyNorm_iterationOperator_apply_le_spectralRadius_of_comm s hA
    (energyInner_iterationOperator_comm s hA.isSymmetric hM) e

/-- **`ρ(G) = ‖G‖_M`** ([quarteroni2000numerical] Property 4.1, the `P`-norm clause): for a
symmetric `A` and a splitting with symmetric coercive `M`, `‖G e‖_M ≤ ρ(G) ‖e‖_M` for every `e`. -/
theorem norm_m_iterationOperator_apply_le_spectralRadius {A : E →L[ℂ] E} (s : Splitting A)
    (hA : (A : E →ₗ[ℂ] E).IsSymmetric) (hM : (s.m : E →ₗ[ℂ] E).IsSymmetricCoercive) (e : E) :
    energyNorm (s.m : E →ₗ[ℂ] E) (s.iterationOperator e) ≤
      (spectralRadius ℂ s.iterationOperator).toReal * energyNorm (s.m : E →ₗ[ℂ] E) e :=
  energyNorm_iterationOperator_apply_le_spectralRadius_of_comm s hM
    (inner_m_iterationOperator_comm s hA hM.isSymmetric) e

end Operator

section Euclidean

/-! ### Real matrices

A real splitting reaches the operator statements through `Stationary.Splitting.euclidean`, the
splitting of `Matrix.toEuclideanCLM (Matrix.complexify A)` on `EuclideanSpace ℂ n` obtained by
complexifying and transporting along the star algebra equivalence `Matrix.toEuclideanCLM`. -/

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (s : Splitting A)

/-- The splitting of the operator `toEuclideanCLM (complexify A)` on `EuclideanSpace ℂ n` induced
by a real splitting of `A`. -/
noncomputable def euclidean : Splitting (toEuclideanCLM (n := n) (𝕜 := ℂ) (Matrix.complexify A)) :=
  s.complexify.map (toEuclideanCLM (n := n) (𝕜 := ℂ))

/-- The `m` of the induced Euclidean splitting. -/
theorem euclidean_m :
    s.euclidean.m = toEuclideanCLM (n := n) (𝕜 := ℂ) (Matrix.complexify s.m) := rfl

/-- The iteration operator of the induced Euclidean splitting is the operator of the complexified
iteration matrix. -/
theorem euclidean_iterationOperator :
    s.euclidean.iterationOperator
      = toEuclideanCLM (n := n) (𝕜 := ℂ) (Matrix.complexify s.iterationOperator) := by
  rw [euclidean, map_iterationOperator, Splitting.complexify_iterationOperator]

/-- The spectral radius of the induced Euclidean splitting's iteration operator is the complex
spectral radius of the real iteration matrix. -/
theorem spectralRadius_euclidean_iterationOperator :
    spectralRadius ℂ s.euclidean.iterationOperator = complexSpectralRadius s.iterationOperator := by
  rw [euclidean_iterationOperator, complexSpectralRadius_eq_iSup, spectralRadius_eq_of_unital,
    AlgEquiv.spectrum_eq (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))]

/-- The Householder–John operator `M + Mᴴ - A` of the induced Euclidean splitting is the operator
of the real matrix `M + Mᵀ - A`. -/
theorem euclidean_m_add_adjoint_sub :
    s.euclidean.m + ContinuousLinearMap.adjoint s.euclidean.m
      - toEuclideanCLM (n := n) (𝕜 := ℂ) (Matrix.complexify A)
      = toEuclideanCLM (n := n) (𝕜 := ℂ) (Matrix.complexify (s.m + s.mᵀ - A)) := by
  rw [euclidean_m, ← ContinuousLinearMap.star_eq_adjoint, ← map_star, ← map_add, ← map_sub,
    Matrix.complexify_sub, Matrix.complexify_add, ← conjTranspose_eq_transpose_of_trivial s.m,
    Matrix.complexify_conjTranspose, Matrix.star_eq_conjTranspose]

/-- **Householder–John for real matrices** ([saad2003iterative] Thm 4.10; [quarteroni2000numerical]
Properties 4.1–4.2): for a positive definite `A` and a splitting with `M + Mᵀ - A` positive
definite, `ρ(M⁻¹ N) < 1`.  It is `spectralRadius_lt_one_of_isSymmetricCoercive` for the induced
Euclidean splitting. -/
theorem complexSpectralRadius_lt_one_of_posDef (hA : A.PosDef) (hQ : (s.m + s.mᵀ - A).PosDef) :
    complexSpectralRadius s.iterationOperator < 1 := by
  rw [← spectralRadius_euclidean_iterationOperator]
  refine spectralRadius_lt_one_of_isSymmetricCoercive s.euclidean
    hA.isSymmetricCoercive_toEuclideanCLM_complexify ?_
  rw [euclidean_m_add_adjoint_sub]
  exact hQ.isSymmetricCoercive_toEuclideanCLM_complexify.isCoercive

/-- **The converse of Householder–John for real matrices** ([saad2003iterative] Thm 4.10, "only
if"): for a symmetric `A` and a splitting with `M + Mᵀ - A` positive definite, convergence forces
`A` to be positive definite. -/
theorem posDef_of_complexSpectralRadius_lt_one (hA : A.IsHermitian) (hQ : (s.m + s.mᵀ - A).PosDef)
    (hρ : complexSpectralRadius s.iterationOperator < 1) : A.PosDef := by
  rw [← spectralRadius_euclidean_iterationOperator] at hρ
  have hco := isCoercive_of_spectralRadius_lt_one s.euclidean
    hA.isSymmetric_toEuclideanCLM_complexify
    (by rw [euclidean_m_add_adjoint_sub]
        exact hQ.isSymmetricCoercive_toEuclideanCLM_complexify.isCoercive) hρ
  rw [← posDef_complexify_iff, posDef_iff_isSymmetricCoercive]
  have hsym := hA.isSymmetric_toEuclideanCLM_complexify
  rw [coe_toEuclideanCLM_eq_toEuclideanLin] at hsym hco
  exact ⟨hsym, hco⟩

end Euclidean

end Splitting

end Stationary

namespace Matrix

open Stationary

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectral radius of a real matrix is `K` as soon as every complex eigenvalue has modulus at
most `K` and one of them attains it. -/
private theorem complexSpectralRadius_eq_of_forall_le {X : Matrix n n ℝ} {K : ℝ}
    (hle : ∀ μ ∈ spectrum ℂ (complexify X), ‖μ‖ ≤ K)
    (hmem : ∃ μ ∈ spectrum ℂ (complexify X), ‖μ‖ = K) :
    complexSpectralRadius X = ENNReal.ofReal K := by
  obtain ⟨μ₀, hμ₀, hμ₀K⟩ := hmem
  rw [complexSpectralRadius_eq_iSup]
  refine le_antisymm (iSup₂_le fun μ hμ => ?_) ?_
  · calc (‖μ‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖μ‖ := by rw [ofReal_norm]; rfl
      _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal (hle μ hμ)
  · calc ENNReal.ofReal K = (‖μ₀‖₊ : ℝ≥0∞) := by rw [← hμ₀K, ofReal_norm]; rfl
      _ ≤ _ := le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ (complexify X)) => (‖k‖₊ : ℝ≥0∞)) μ₀ hμ₀

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

/-- **The spectral radius of an affine function of a real matrix** whose spectrum is real and fills
`[lmin, lmax]`: `ρ(c 1 + d X) = max |c + d lmin| |c + d lmax|`.  The absolute value is convex, so
the largest `|c + d t|` sits at an endpoint.  This is the tool behind every relaxation-parameter
computation (Richardson, JOR). -/
theorem complexSpectralRadius_affine {X : Matrix n n ℝ} {lmin lmax : ℝ}
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
/-- An attained lower endpoint of an enclosing interval is below the upper one. -/
private theorem le_of_spectrum_subset {X : Matrix n n ℝ} {lmin lmax : ℝ}
    (hsub : spectrum ℂ (complexify X) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ X) : lmin ≤ lmax := by
  obtain ⟨r, hr, hre⟩ := hsub ((ofReal_mem_spectrum_complexify_iff X lmin).mpr hmin)
  rw [Complex.ofReal_inj] at hre
  exact hre ▸ hr.2

/-- `t ↦ max |1 - t a| |1 - t b|` is bounded below by `(b - a)/(b + a)` for `0 < a ≤ b`: the convex
combination with weights `b/(a+b)`, `a/(a+b)` of `1 - t a` and `-(1 - t b)` is that constant,
whatever `t` is. -/
theorem le_max_abs_one_sub_mul {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    (b - a) / (b + a) ≤ max |1 - t * a| |1 - t * b| := by
  have hb : 0 < b := ha.trans_le hab
  have hA : 1 - t * a ≤ max |1 - t * a| |1 - t * b| := (le_abs_self _).trans (le_max_left _ _)
  have hB : -(1 - t * b) ≤ max |1 - t * a| |1 - t * b| := (neg_le_abs _).trans (le_max_right _ _)
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < b + a)]
  nlinarith [mul_le_mul_of_nonneg_left hA hb.le, mul_le_mul_of_nonneg_left hB ha.le]

/-- At `t = 2/(a + b)` the two branches of `max |1 - t a| |1 - t b|` are equal, and the common value
`(b - a)/(b + a)` is the lower bound of `le_max_abs_one_sub_mul`: the minimum is attained there. -/
theorem max_abs_one_sub_mul_optimal {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    max |1 - 2 / (a + b) * a| |1 - 2 / (a + b) * b| = (b - a) / (b + a) := by
  have hb : 0 < b := ha.trans_le hab
  have hsum : (0 : ℝ) < a + b := by linarith
  have h1 : 1 - 2 / (a + b) * a = (b - a) / (b + a) := by field_simp; ring
  have h2 : 1 - 2 / (a + b) * b = -((b - a) / (b + a)) := by field_simp; ring
  rw [h1, h2, abs_neg, abs_of_nonneg (div_nonneg (by linarith) (by linarith)), max_self]

end Matrix

/-! ### Richardson's iteration -/

namespace Stationary

namespace Splitting

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The spectral radius of Richardson's iteration matrix** `1 - α M` for a real matrix `M` whose
complex spectrum is real and fills `[lmin, lmax]`: `ρ(1 - α M) = max |1 - α lmin| |1 - α lmax|`
([quarteroni2000numerical] Theorem 4.9, first step, for `M = P⁻¹ A`).  The spectrum of `1 - α M` is
the image of that of `M` under `t ↦ 1 - α t`, and `|·|` is convex. -/
theorem complexSpectralRadius_one_sub_smul_eq {M : Matrix n n ℝ} {lmin lmax : ℝ}
    (hsub : spectrum ℂ (Matrix.complexify M) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ M) (hmax : lmax ∈ spectrum ℝ M) {α : ℝ} (hα : α ≠ 0) :
    complexSpectralRadius (1 - α • M) = ENNReal.ofReal (max |1 - α * lmin| |1 - α * lmax|) := by
  have hrw : (1 : Matrix n n ℝ) - α • M = (1 : ℝ) • 1 + (-α) • M := by module
  rw [hrw, complexSpectralRadius_affine hsub hmin hmax (neg_ne_zero.mpr hα)]
  ring_nf

/-- **Richardson's iteration converges exactly for `0 < α < 2/lmax`** ([quarteroni2000numerical]
Theorem 4.9, convergence clause), for a real matrix `M` with real positive spectrum filling
`[lmin, lmax]`; with `M = P⁻¹ A` this is the preconditioned statement of the book. -/
theorem complexSpectralRadius_one_sub_smul_lt_one_iff {M : Matrix n n ℝ} {lmin lmax : ℝ}
    (hsub : spectrum ℂ (Matrix.complexify M) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ M) (hmax : lmax ∈ spectrum ℝ M) (hpos : 0 < lmin) (α : ℝ) :
    complexSpectralRadius (1 - α • M) < 1 ↔ 0 < α ∧ α < 2 / lmax := by
  have hle : lmin ≤ lmax := le_of_spectrum_subset hsub hmin
  have hmaxpos : 0 < lmax := hpos.trans_le hle
  rcases eq_or_ne α 0 with rfl | hα
  · simp only [zero_smul, sub_zero, lt_self_iff_false, false_and, iff_false, not_lt]
    have h1 : ((1 : ℝ) : ℂ) ∈ spectrum ℂ (Matrix.complexify (1 : Matrix n n ℝ)) := by
      have hne : (spectrum ℂ (Matrix.complexify M)).Nonempty :=
        ⟨_, (ofReal_mem_spectrum_complexify_iff M lmin).mpr hmin⟩
      have : Nontrivial (Matrix n n ℂ) := by
        obtain ⟨z, hz⟩ := hne
        by_contra hcon
        rw [not_nontrivial_iff_subsingleton] at hcon
        exact spectrum.mem_iff.mp hz (isUnit_of_subsingleton _)
      rw [Matrix.complexify_one, Complex.ofReal_one, spectrum.mem_iff, map_one, sub_self]
      exact not_isUnit_zero
    calc (1 : ℝ≥0∞) = (‖((1 : ℝ) : ℂ)‖₊ : ℝ≥0∞) := by simp
      _ ≤ complexSpectralRadius (1 : Matrix n n ℝ) := Matrix.nnnorm_le_complexSpectralRadius h1
  rw [complexSpectralRadius_one_sub_smul_eq hsub hmin hmax hα, ENNReal.ofReal_lt_one, max_lt_iff,
    abs_lt, abs_lt, lt_div_iff₀ hmaxpos]
  constructor
  · rintro ⟨-, h3, h4⟩
    constructor
    · nlinarith
    · nlinarith
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

/-- **The optimal Richardson parameter** `α = 2/(lmin + lmax)` minimizes `ρ(1 - α M)` over `α > 0`
([quarteroni2000numerical] (4.27); [saad2003iterative] Example 4.1), for a real matrix `M` with real
positive spectrum filling `[lmin, lmax]`.  The minimum value is
`Stationary.Splitting.complexSpectralRadius_one_sub_smul_optimal_eq`. -/
theorem isMinOn_complexSpectralRadius_one_sub_smul {M : Matrix n n ℝ} {lmin lmax : ℝ}
    (hsub : spectrum ℂ (Matrix.complexify M) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ M) (hmax : lmax ∈ spectrum ℝ M) (hpos : 0 < lmin) :
    IsMinOn (fun α : ℝ => complexSpectralRadius (1 - α • M)) (Set.Ioi 0)
      (2 / (lmin + lmax)) := by
  have hle : lmin ≤ lmax := le_of_spectrum_subset hsub hmin
  have hsum : (0 : ℝ) < lmin + lmax := by linarith
  refine isMinOn_iff.2 fun α hα => ?_
  rw [complexSpectralRadius_one_sub_smul_eq hsub hmin hmax (ne_of_gt (div_pos two_pos hsum)),
    complexSpectralRadius_one_sub_smul_eq hsub hmin hmax (ne_of_gt hα),
    max_abs_one_sub_mul_optimal hpos hle]
  exact ENNReal.ofReal_le_ofReal (le_max_abs_one_sub_mul hpos hle α)

/-- **The optimal Richardson spectral radius** is `(lmax - lmin)/(lmax + lmin)`
([quarteroni2000numerical] (4.28)). -/
theorem complexSpectralRadius_one_sub_smul_optimal_eq {M : Matrix n n ℝ} {lmin lmax : ℝ}
    (hsub : spectrum ℂ (Matrix.complexify M) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ M) (hmax : lmax ∈ spectrum ℝ M) (hpos : 0 < lmin) :
    complexSpectralRadius (1 - (2 / (lmin + lmax)) • M)
      = ENNReal.ofReal ((lmax - lmin) / (lmax + lmin)) := by
  have hle : lmin ≤ lmax := le_of_spectrum_subset hsub hmin
  have hsum : (0 : ℝ) < lmin + lmax := by linarith
  rw [complexSpectralRadius_one_sub_smul_eq hsub hmin hmax (ne_of_gt (div_pos two_pos hsum)),
    max_abs_one_sub_mul_optimal hpos hle]

/-- A real symmetric matrix whose real spectrum lies in `[lmin, lmax]` has its complex spectrum in
the image of `[lmin, lmax]`. -/
theorem _root_.Matrix.IsHermitian.spectrum_complexify_subset {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {lmin lmax : ℝ} (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax) :
    spectrum ℂ (Matrix.complexify A) ⊆ Complex.ofReal '' Set.Icc lmin lmax := by
  rw [hA.spectrum_complexify_eq]
  exact Set.image_mono hsub

/-- **Richardson's iteration** `G_α = 1 - α A` for a real symmetric `A` whose eigenvalues fill
`[lmin, lmax]`: `ρ(G_α) = max |1 - α lmin| |1 - α lmax|`
([saad2003iterative], Example 4.1); the Hermitian case of
`Stationary.Splitting.complexSpectralRadius_one_sub_smul_eq`. -/
theorem richardson_complexSpectralRadius_eq {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {lmin lmax : ℝ} (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ A)
    (hmax : lmax ∈ spectrum ℝ A) {α : ℝ} (hα : α ≠ 0) :
    complexSpectralRadius (richardson A hα).iterationOperator
      = ENNReal.ofReal (max |1 - α * lmin| |1 - α * lmax|) := by
  rw [richardson_iterationOperator,
    complexSpectralRadius_one_sub_smul_eq (hA.spectrum_complexify_subset hsub) hmin hmax hα]

/-- Richardson's iteration for a symmetric positive definite `A` converges exactly for `0 < α <
2/λmax` ([saad2003iterative], Example 4.1; [han2009theoretical], Exercise 5.2.3). -/
theorem richardson_complexSpectralRadius_lt_one_iff {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {lmin lmax : ℝ} (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ A)
    (hmax : lmax ∈ spectrum ℝ A) (hpos : 0 < lmin) {α : ℝ} (hα : α ≠ 0) :
    complexSpectralRadius (richardson A hα).iterationOperator < 1 ↔ 0 < α ∧ α < 2 / lmax := by
  rw [richardson_iterationOperator]
  exact complexSpectralRadius_one_sub_smul_lt_one_iff (hA.spectrum_complexify_subset hsub) hmin
    hmax hpos α

/-- **The optimal Richardson parameter** is `α = 2/(λmin + λmax)`: it minimizes the spectral radius
of `G_α = 1 - α A` over `α > 0` ([saad2003iterative], Example 4.1).  The iteration operator is
`Stationary.Splitting.richardson_iterationOperator`; the minimum value is
`richardson_complexSpectralRadius_optimal_eq`. -/
theorem isMinOn_richardson_complexSpectralRadius {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {lmin lmax : ℝ} (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ A)
    (hmax : lmax ∈ spectrum ℝ A) (hpos : 0 < lmin) :
    IsMinOn (fun α : ℝ => complexSpectralRadius (1 - α • A)) (Set.Ioi 0)
      (2 / (lmin + lmax)) :=
  isMinOn_complexSpectralRadius_one_sub_smul (hA.spectrum_complexify_subset hsub) hmin hmax hpos

/-- The value of the optimal Richardson spectral radius, `(λmax - λmin)/(λmax + λmin)`
([saad2003iterative], Example 4.1): one less two over the condition number plus one. -/
theorem richardson_complexSpectralRadius_optimal_eq {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {lmin lmax : ℝ} (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ A)
    (hmax : lmax ∈ spectrum ℝ A) (hpos : 0 < lmin) :
    complexSpectralRadius (1 - (2 / (lmin + lmax)) • A)
      = ENNReal.ofReal ((lmax - lmin) / (lmax + lmin)) :=
  complexSpectralRadius_one_sub_smul_optimal_eq (hA.spectrum_complexify_subset hsub) hmin hmax hpos

end Splitting

end Stationary

/-! ### Jacobi over-relaxation, SOR determinant, Kahan -/

namespace Matrix

open Stationary

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The optimal relaxation parameter of JOR** is `ω = 2/(2 - λmax - λmin)`, where `λmin` and
`λmax` are the extreme eigenvalues of the Jacobi matrix `B`, assumed real ([kress1998numerical], Thm
4.9).  Only `λmax < 1` is used, which is half of the convergence of the Jacobi iteration; the JOR
iteration operator is `Matrix.jorSplitting_iterationOperator`. -/
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
triangular `D - ωE`, whose diagonal is that of `A`, times the upper triangular `(1 - ω) D + ωF`,
whose diagonal is `(1 - ω)` times that of `A` ([kress1998numerical], proof of Thm 4.11). -/
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
([kress1998numerical], Thm 4.11).  The powers of the iteration matrix tend to `0`, so its
determinant `(1 - ω)ⁿ` has modulus `< 1`, which for a nonempty index type forces `|1 - ω| < 1`. -/
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

/-- **The SOR matrix of a lower triangular matrix has the single eigenvalue `1 - ω`**, so
`ρ(B(ω)) = |1 - ω|` for every `ω ≠ 0`, the equality case of Kahan's bound: with `F = 0`,
`B(ω) = (D - ωE)⁻¹ (1 - ω) D` is lower triangular with diagonal `1 - ω`, and its characteristic
polynomial is `(λ - (1 - ω))ⁿ`. -/
theorem complexSpectralRadius_sorSplitting_of_isLowerTriangular [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.IsLowerTriangular) (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    complexSpectralRadius (sorSplitting A h hω).iterationOperator = ENNReal.ofReal |1 - ω| := by
  set M : Matrix n n ℝ := diagPart A + ω • strictLower A with hMdef
  set B := (sorSplitting A h hω).iterationOperator with hBdef
  have hd := (isUnit_diagPart_iff A).mp h
  have hU : strictUpper A = 0 := by
    ext i j
    rw [strictUpper_apply, Matrix.zero_apply]
    split_ifs with hij
    · exact hA (OrderDual.toDual_lt_toDual.mpr hij)
    · rfl
  have hMtri : M.IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp [hMdef, diagPart_apply, strictLower_apply, hij'.ne, asymm hij']
  have hMii : ∀ i, M i i = A i i := fun i => by simp [hMdef, diagPart_apply, strictLower_apply]
  have hMunit : IsUnit M := isUnit_diagPart_add_smul_strictLower h ω
  have hMinv : M⁻¹.IsLowerTriangular := hMtri.inv
  have hMinvii : ∀ i, M⁻¹ i i = (A i i)⁻¹ := fun i => by
    have h1 := hMinv.mul_apply_self hMtri i
    rw [nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hMunit), one_apply_eq, hMii] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  have hDtri : ((1 - ω) • diagPart A).IsLowerTriangular := by
    rw [diagPart, ← diagonal_smul]
    exact blockTriangular_diagonal _
  have hB : B = M⁻¹ * ((1 - ω) • diagPart A) := by
    rw [hBdef, sorSplitting_iterationOperator, hU, smul_zero, sub_zero]
  have hBtri : B.IsLowerTriangular := by
    rw [hB]
    exact hMinv.mul hDtri
  have hBii : ∀ i, B i i = 1 - ω := fun i => by
    rw [hB, hMinv.mul_apply_self hDtri i, hMinvii]
    simp only [Matrix.smul_apply, diagPart_apply, ite_true, smul_eq_mul]
    rw [mul_comm (1 - ω), ← mul_assoc, inv_mul_cancel₀ (hd i), one_mul]
  have hchar : B.charpoly = (Polynomial.X - Polynomial.C (1 - ω)) ^ Fintype.card n := by
    rw [charpoly_of_isLowerTriangular B hBtri]
    simp only [hBii, Finset.prod_const, Finset.card_univ]
  refine complexSpectralRadius_eq_of_forall_mem_spectrum_iff fun μ => ?_
  rw [mem_spectrum_complexify_iff, hchar, Polynomial.IsRoot.def]
  simp only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    pow_eq_zero_iff Fintype.card_ne_zero, sub_eq_zero]
  push_cast
  rfl

/-- The Householder–John matrix `Q = M + Mᵀ - A` of the SOR splitting of a symmetric `A` is `(2/ω -
1) D`: the strictly lower part of `M` and the strictly upper part of `Mᵀ` reassemble `A - D`. -/
theorem sorSplitting_m_add_transpose_sub {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    (A.sorSplitting h hω).m + ((A.sorSplitting h hω).m)ᵀ - A = (2 / ω - 1) • diagPart A := by
  have hm : (A.sorSplitting h hω).m = ω⁻¹ • diagPart A + strictLower A := rfl
  have hsymm : ∀ i j, A j i = A i j := fun i j => by
    have := congrFun (congrFun hA.eq i) j
    simpa using this
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp [hm, hij, hij.ne, hij.ne', asymm hij, hsymm i j]
  · have hMii : (A.sorSplitting h hω).m i i = ω⁻¹ * A i i := by simp [hm]
    have hlhs : ((A.sorSplitting h hω).m + ((A.sorSplitting h hω).m)ᵀ - A) i i
        = ω⁻¹ * A i i + ω⁻¹ * A i i - A i i := by
      rw [sub_apply, add_apply, transpose_apply, hMii]
    have hrhs : ((2 / ω - 1) • diagPart A) i i = (2 / ω - 1) * A i i := by simp
    rw [hlhs, hrhs, show (2 / ω - 1) = 2 * ω⁻¹ - 1 from by rw [div_eq_mul_inv]]
    ring
  · simp [hm, hij, hij.ne, hij.ne', asymm hij, hsymm j i]

/-- The Householder–John matrix of the SOR splitting of a symmetric matrix with positive diagonal
is positive definite exactly because `0 < ω < 2`. -/
theorem sorSplitting_m_add_transpose_sub_posDef {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (hd : ∀ i, 0 < A i i) (h : IsUnit (diagPart A)) {ω : ℝ} (hω0 : 0 < ω) (hω2 : ω < 2) :
    ((A.sorSplitting h hω0.ne').m + ((A.sorSplitting h hω0.ne').m)ᵀ - A).PosDef := by
  rw [sorSplitting_m_add_transpose_sub hA h hω0.ne']
  have hcpos : 0 < 2 / ω - 1 := by
    rw [sub_pos, lt_div_iff₀ hω0]
    linarith
  have hdiag : (2 / ω - 1) • diagPart A = diagonal fun i => (2 / ω - 1) * A i i := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hdiag, posDef_diagonal_iff]
  exact fun i => mul_pos hcpos (hd i)

/-- **The Ostrowski–Reich theorem for SOR** ([saad2003iterative], Thm 4.10; [kress1998numerical],
Thm 4.12).  For a real symmetric `A` with positive diagonal and a relaxation parameter `0 < ω < 2`,
the SOR iteration converges exactly when `A` is positive definite.

Both directions are `Stationary.Splitting.complexSpectralRadius_lt_one_of_posDef` and
`Stationary.Splitting.posDef_of_complexSpectralRadius_lt_one`, whose Householder–John matrix is
`M + Mᵀ - A = (2/ω - 1) D`, positive definite precisely because `0 < ω < 2`. -/
theorem sorSplitting_complexSpectralRadius_lt_one_iff_posDef {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (hd : ∀ i, 0 < A i i) (h : IsUnit (diagPart A)) {ω : ℝ}
    (hω0 : 0 < ω) (hω2 : ω < 2) :
    complexSpectralRadius (A.sorSplitting h hω0.ne').iterationOperator < 1 ↔ A.PosDef :=
  ⟨Splitting.posDef_of_complexSpectralRadius_lt_one _ hA
      (sorSplitting_m_add_transpose_sub_posDef hA hd h hω0 hω2),
    fun hP => Splitting.complexSpectralRadius_lt_one_of_posDef _ hP
      (sorSplitting_m_add_transpose_sub_posDef hA hd h hω0 hω2)⟩

/-- **Ostrowski's theorem as the book states it** ([quarteroni2000numerical] Property 4.3): for a
positive definite `A`, SOR converges exactly for `0 < ω < 2`.  `←` is
`Matrix.sorSplitting_complexSpectralRadius_lt_one_iff_posDef`, `→` is Kahan's condition
`Matrix.lt_two_of_sorSplitting_complexSpectralRadius_lt_one`, which needs a nonempty index type. -/
theorem sorSplitting_complexSpectralRadius_lt_one_iff [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.PosDef) (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    complexSpectralRadius (sorSplitting A h hω).iterationOperator < 1 ↔ 0 < ω ∧ ω < 2 := by
  refine ⟨lt_two_of_sorSplitting_complexSpectralRadius_lt_one h hω, fun ⟨h0, h2⟩ => ?_⟩
  exact (sorSplitting_complexSpectralRadius_lt_one_iff_posDef hA.1 (fun i => hA.diag_pos) h h0
    h2).mpr hA

/-- **Gauss–Seidel converges for a positive definite matrix** ([quarteroni2000numerical] Theorem
4.5, convergence clause; the monotonicity clause is
`Stationary.Splitting.energyNorm_mulVec_iterationOperator_lt`): SOR at `ω = 1`. -/
theorem gaussSeidelSplitting_complexSpectralRadius_lt_one_of_posDef {A : Matrix n n ℝ}
    (hA : A.PosDef) (h : IsUnit (diagPart A)) :
    complexSpectralRadius (gaussSeidelSplitting A h).iterationOperator < 1 := by
  rw [← sorSplitting_one]
  exact (sorSplitting_complexSpectralRadius_lt_one_iff_posDef hA.1 (fun i => hA.diag_pos) h
    one_pos one_lt_two).mpr hA

omit [LinearOrder n] in
/-- **Jacobi converges when `A` and `2D - A` are positive definite** ([quarteroni2000numerical]
Theorem 4.3): Householder–John with `M = D`, whose `M + Mᵀ - A` is `2D - A`. -/
theorem jacobiSplitting_complexSpectralRadius_lt_one_of_posDef {A : Matrix n n ℝ} (hA : A.PosDef)
    (h2 : (2 • diagPart A - A).PosDef) (h : IsUnit (diagPart A)) :
    complexSpectralRadius (jacobiSplitting A h).iterationOperator < 1 := by
  refine Splitting.complexSpectralRadius_lt_one_of_posDef _ hA ?_
  have hm : (jacobiSplitting A h).m = diagPart A := rfl
  rw [hm, diagPart, diagonal_transpose, ← diagPart, ← two_smul ℕ (diagPart A)]
  exact h2

omit [LinearOrder n] in
/-- **JOR converges for `0 < ω ≤ 1` whenever Jacobi does** ([quarteroni2000numerical] Theorem 4.6),
for any real matrix with invertible diagonal: the JOR matrix `(1 - ω) 1 + ω B_J` has spectral
radius at most `(1 - ω) + ω ρ(B_J) < 1` (`Matrix.complexSpectralRadius_affine_lt_one`). -/
theorem jorSplitting_complexSpectralRadius_lt_one_of_le_one {A : Matrix n n ℝ}
    (h : IsUnit (diagPart A))
    (hJ : complexSpectralRadius (jacobiSplitting A h).iterationOperator < 1) {ω : ℝ}
    (hω0 : 0 < ω) (hω1 : ω ≤ 1) :
    complexSpectralRadius (jorSplitting A h hω0.ne').iterationOperator < 1 := by
  rw [jorSplitting_iterationOperator]
  exact complexSpectralRadius_affine_lt_one _ hω0 hω1 hJ


/-- **Kahan's bound** `|1 - ω| ≤ ρ(G_ω)` ([quarteroni2000numerical] Theorem 4.7): the determinant
of the SOR iteration matrix is `(1 - ω)ⁿ` (`Matrix.det_sorSplitting_iterationOperator`) and the
product of the `n` complex eigenvalues, each of modulus at most `ρ(G_ω)`.  The corollary
`0 < ω < 2` for a convergent SOR is `Matrix.lt_two_of_sorSplitting_complexSpectralRadius_lt_one`. -/
theorem abs_one_sub_le_sorSplitting_complexSpectralRadius [Nonempty n] {A : Matrix n n ℝ}
    (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    ENNReal.ofReal |1 - ω| ≤ complexSpectralRadius (sorSplitting A h hω).iterationOperator := by
  set G := (sorSplitting A h hω).iterationOperator with hG
  set ρ := complexSpectralRadius G with hρ
  have hρtop : ρ ≠ ⊤ := complexSpectralRadius_ne_top G
  have hdet : (complexify G).det = (complexify G).charpoly.roots.prod :=
    det_eq_prod_roots_charpoly _
  have hcard : Multiset.card (complexify G).charpoly.roots = Fintype.card n := by
    rw [← (IsAlgClosed.splits (complexify G).charpoly).natDegree_eq_card_roots,
      charpoly_natDegree_eq_dim]
  have hle : ∀ μ ∈ (complexify G).charpoly.roots, ‖μ‖₊ ≤ ρ.toNNReal := by
    intro μ hμ
    have hmem : μ ∈ spectrum ℂ (complexify G) :=
      mem_spectrum_iff_isRoot_charpoly.mpr ((Polynomial.mem_roots (charpoly_monic _).ne_zero).mp hμ)
    have : (‖μ‖₊ : ℝ≥0∞) ≤ ρ := Matrix.nnnorm_le_complexSpectralRadius hmem
    rwa [← ENNReal.coe_toNNReal hρtop, ENNReal.coe_le_coe] at this
  have hprod : ‖(complexify G).det‖₊ ≤ ρ.toNNReal ^ Fintype.card n := by
    rw [hdet, ← nnnormHom_apply, map_multiset_prod]
    refine (Multiset.prod_le_pow_card (α := NNReal) _ ρ.toNNReal fun x hx => ?_).trans_eq ?_
    · obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hx
      exact hle μ hμ
    · rw [Multiset.card_map, hcard]
  rw [det_complexify, det_sorSplitting_iterationOperator, Complex.nnnorm_real, nnnorm_pow] at hprod
  have hcardne : Fintype.card n ≠ 0 := Fintype.card_ne_zero
  have h1 : ‖1 - ω‖₊ ≤ ρ.toNNReal :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) hcardne).mp hprod
  calc ENNReal.ofReal |1 - ω| = (‖1 - ω‖₊ : ℝ≥0∞) := by
        rw [← Real.norm_eq_abs, ofReal_norm, enorm_eq_nnnorm]
    _ ≤ (ρ.toNNReal : ℝ≥0∞) := ENNReal.coe_le_coe.mpr h1
    _ = ρ := ENNReal.coe_toNNReal hρtop

end Matrix


/-! ### The energy norms of a real matrix -/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The energy norm of a real vector in the Euclidean energy space of a positive definite `A` is
the real energy norm: `‖e‖_A² = (A e) ⬝ e`. -/
theorem energyNorm_toEuclideanCLM_complexify_sq {A : Matrix n n ℝ} (hA : A.PosDef) (e : n → ℝ) :
    energyNorm ((toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A) :
      EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n)
        (toEuclideanComplex e) ^ 2 = (A *ᵥ e) ⬝ᵥ e := by
  rw [hA.isSymmetricCoercive_toEuclideanCLM_complexify.energyNorm_sq, ContinuousLinearMap.coe_coe,
    re_inner_toEuclideanCLM_complexify_toEuclideanComplex]

end Matrix

namespace Stationary.Splitting

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (s : Splitting A)

/-- **Monotone convergence in the energy norm, for real matrices** ([quarteroni2000numerical]
Properties 4.1–4.2, Theorem 4.5 and Property 4.3, monotonicity clauses): for a positive definite `A`
and a splitting with `M + Mᵀ - A` positive definite, `‖G e‖_A < ‖e‖_A` for every real `e ≠ 0`,
written with the real energy form `‖e‖_A² = (A e) ⬝ e`. -/
theorem energyNorm_mulVec_iterationOperator_lt (hA : A.PosDef) (hQ : (s.m + s.mᵀ - A).PosDef)
    {e : n → ℝ} (he : e ≠ 0) :
    (A *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e) < (A *ᵥ e) ⬝ᵥ e := by
  have hA' := hA.isSymmetricCoercive_toEuclideanCLM_complexify
  have hQ' := hQ.isSymmetricCoercive_toEuclideanCLM_complexify.isCoercive
  rw [← euclidean_m_add_adjoint_sub] at hQ'
  have he' : toEuclideanComplex e ≠ 0 := fun h => he (toEuclideanComplex_eq_zero_iff.mp h)
  have h := energyNorm_iterationOperator_apply_lt s.euclidean hA' hQ' he'
  rw [euclidean_iterationOperator, toEuclideanCLM_complexify_toEuclideanComplex] at h
  have h2 := pow_lt_pow_left₀ h (energyNorm_nonneg _ _) two_ne_zero
  rwa [energyNorm_toEuclideanCLM_complexify_sq hA, energyNorm_toEuclideanCLM_complexify_sq hA] at h2

/-- **The uniform energy contraction, for real matrices**: under the hypotheses of
`energyNorm_mulVec_iterationOperator_lt` there is `q < 1` with `‖G e‖_A² ≤ q² ‖e‖_A²` for every
real `e`. -/
theorem exists_energyNorm_mulVec_iterationOperator_le (hA : A.PosDef)
    (hQ : (s.m + s.mᵀ - A).PosDef) :
    ∃ q : ℝ, q < 1 ∧ ∀ e : n → ℝ, (A *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e)
      ≤ q ^ 2 * ((A *ᵥ e) ⬝ᵥ e) := by
  have hA' := hA.isSymmetricCoercive_toEuclideanCLM_complexify
  have hQ' := hQ.isSymmetricCoercive_toEuclideanCLM_complexify.isCoercive
  rw [← euclidean_m_add_adjoint_sub] at hQ'
  obtain ⟨q, hq1, hq⟩ := exists_energyNorm_iterationOperator_apply_le s.euclidean hA' hQ'
  refine ⟨max q 0, max_lt hq1 zero_lt_one, fun e => ?_⟩
  have h := hq (toEuclideanComplex e)
  rw [euclidean_iterationOperator, toEuclideanCLM_complexify_toEuclideanComplex] at h
  have h' := h.trans (mul_le_mul_of_nonneg_right (le_max_left q 0) (energyNorm_nonneg _ _))
  have h2 := pow_le_pow_left₀ (energyNorm_nonneg _ _) h' 2
  rwa [energyNorm_toEuclideanCLM_complexify_sq hA, mul_pow,
    energyNorm_toEuclideanCLM_complexify_sq hA] at h2

/-- **The uniform energy contraction dominates the spectral radius**: under the hypotheses of
`exists_energyNorm_mulVec_iterationOperator_le` there is `q < 1` with both `ρ(G) ≤ q` and
`‖G e‖_A² ≤ q² ‖e‖_A²` for every real `e`. The operator-norm bound `‖G‖_A ≤ q` on the complex energy
space (`exists_energyNorm_iterationOperator_apply_le`) gives `ρ(G) ≤ ‖G‖_A ≤ q`, and the bound on
real vectors is read off it as in `exists_energyNorm_mulVec_iterationOperator_le`. -/
theorem exists_complexSpectralRadius_le_and_energyNorm_mulVec_le (hA : A.PosDef)
    (hQ : (s.m + s.mᵀ - A).PosDef) :
    ∃ q : ℝ, q < 1 ∧ (complexSpectralRadius s.iterationOperator).toReal ≤ q ∧
      ∀ e : n → ℝ, (A *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e) ≤
        q ^ 2 * ((A *ᵥ e) ⬝ᵥ e) := by
  have hA' := hA.isSymmetricCoercive_toEuclideanCLM_complexify
  have hQ' := hQ.isSymmetricCoercive_toEuclideanCLM_complexify.isCoercive
  rw [← euclidean_m_add_adjoint_sub] at hQ'
  obtain ⟨q, hq1, hq⟩ := exists_energyNorm_iterationOperator_apply_le s.euclidean hA' hQ'
  set T := energyIterationOperator s.euclidean hA' with hT
  have hTle : ‖T‖ ≤ max q 0 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun u => ?_
    obtain ⟨x, rfl⟩ := (WithEnergy.equiv _ hA').surjective u
    rw [hT, energyIterationOperator_apply, WithEnergy.norm_equiv, WithEnergy.norm_equiv]
    exact (hq x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (energyNorm_nonneg _ _))
  have hρ : (complexSpectralRadius s.iterationOperator).toReal ≤ max q 0 := by
    rw [← spectralRadius_euclidean_iterationOperator,
      ← spectralRadius_energyIterationOperator s.euclidean hA', ← hT]
    rcases subsingleton_or_nontrivial (WithEnergy _ hA') with hsub | hnt
    · have : Subsingleton (WithEnergy _ hA' →L[ℂ] WithEnergy _ hA') :=
        ⟨fun f g => by ext x; exact Subsingleton.elim _ _⟩
      rw [spectrum.SpectralRadius.of_subsingleton, ENNReal.toReal_zero]
      exact le_max_right _ _
    · refine le_trans ?_ hTle
      refine ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) ?_
      rw [ofReal_norm, enorm_eq_nnnorm]
      exact spectralRadius_le_nnnorm T
  refine ⟨max q 0, max_lt hq1 zero_lt_one, hρ, fun e => ?_⟩
  have h := hq (toEuclideanComplex e)
  rw [euclidean_iterationOperator, toEuclideanCLM_complexify_toEuclideanComplex] at h
  have h' := h.trans (mul_le_mul_of_nonneg_right (le_max_left q 0) (energyNorm_nonneg _ _))
  have h2 := pow_le_pow_left₀ (energyNorm_nonneg _ _) h' 2
  rwa [energyNorm_toEuclideanCLM_complexify_sq hA, mul_pow,
    energyNorm_toEuclideanCLM_complexify_sq hA] at h2

/-- **`‖G e‖_A ≤ ρ(G) ‖e‖_A` for real matrices** ([quarteroni2000numerical] Property 4.1 and
Corollary 4.1 in the generality of its closing remark: `A` positive definite and `M` symmetric,
no hypothesis on `M⁻¹ A`), in the squared form `(A (G e)) ⬝ (G e) ≤ ρ(G)² ((A e) ⬝ e)`. -/
theorem energyNorm_mulVec_iterationOperator_le_complexSpectralRadius (hA : A.PosDef)
    (hM : s.m.IsHermitian) (e : n → ℝ) :
    (A *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e)
      ≤ (complexSpectralRadius s.iterationOperator).toReal ^ 2 * ((A *ᵥ e) ⬝ᵥ e) := by
  have hA' := hA.isSymmetricCoercive_toEuclideanCLM_complexify
  have hM' : (s.euclidean.m : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).IsSymmetric := by
    rw [euclidean_m]
    exact hM.isSymmetric_toEuclideanCLM_complexify
  have h := energyNorm_iterationOperator_apply_le_spectralRadius s.euclidean hA' hM'
    (toEuclideanComplex e)
  rw [spectralRadius_euclidean_iterationOperator, euclidean_iterationOperator,
    toEuclideanCLM_complexify_toEuclideanComplex] at h
  have h2 := pow_le_pow_left₀ (energyNorm_nonneg _ _) h 2
  rwa [energyNorm_toEuclideanCLM_complexify_sq hA, mul_pow,
    energyNorm_toEuclideanCLM_complexify_sq hA] at h2

/-- **`‖G e‖_M ≤ ρ(G) ‖e‖_M` for real matrices** ([quarteroni2000numerical] Property 4.1, the
`P`-norm clause): for a symmetric `A` and a positive definite `M`,
`(M (G e)) ⬝ (G e) ≤ ρ(G)² ((M e) ⬝ e)`. -/
theorem energyNorm_m_mulVec_iterationOperator_le_complexSpectralRadius (hA : A.IsHermitian)
    (hM : s.m.PosDef) (e : n → ℝ) :
    (s.m *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e)
      ≤ (complexSpectralRadius s.iterationOperator).toReal ^ 2 * ((s.m *ᵥ e) ⬝ᵥ e) := by
  have hA' := hA.isSymmetric_toEuclideanCLM_complexify
  have hM' : (s.euclidean.m : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).IsSymmetricCoercive := by
    rw [euclidean_m]
    exact hM.isSymmetricCoercive_toEuclideanCLM_complexify
  have h := norm_m_iterationOperator_apply_le_spectralRadius s.euclidean hA' hM'
    (toEuclideanComplex e)
  rw [spectralRadius_euclidean_iterationOperator, euclidean_iterationOperator,
    toEuclideanCLM_complexify_toEuclideanComplex, euclidean_m] at h
  have h2 := pow_le_pow_left₀ (energyNorm_nonneg _ _) h 2
  rwa [energyNorm_toEuclideanCLM_complexify_sq hM, mul_pow,
    energyNorm_toEuclideanCLM_complexify_sq hM] at h2

/-- For `A` positive definite and `M` symmetric, the iteration matrix `G = M⁻¹ N` has a real
eigenvector `e ≠ 0` for a real eigenvalue of modulus `ρ(G)`: `G` is self-adjoint in the
`A`-inner product, so an eigenvalue of maximal modulus is real, and a real eigenvalue of a real
matrix has a real eigenvector. -/
theorem exists_mulVec_iterationOperator_eq_smul [Nonempty n] (hA : A.PosDef)
    (hM : s.m.IsHermitian) :
    ∃ e : n → ℝ, e ≠ 0 ∧ ∃ μ : ℝ, |μ| = (complexSpectralRadius s.iterationOperator).toReal ∧
      s.iterationOperator *ᵥ e = μ • e := by
  set G := s.iterationOperator with hG
  obtain ⟨μ, v, hv, hμv, hμρ⟩ := exists_eigenvector_norm_eq_complexSpectralRadius G
  have hμmem : μ ∈ spectrum ℂ (Matrix.complexify G) :=
    (mem_spectrum_iff_exists_mulVec_eq_smul _ _).mpr ⟨v, hv, hμv⟩
  have hA' := hA.isSymmetricCoercive_toEuclideanCLM_complexify
  have hM' : (s.euclidean.m : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).IsSymmetric := by
    rw [euclidean_m]
    exact hM.isSymmetric_toEuclideanCLM_complexify
  have hsa := isSelfAdjoint_energyIterationOperator s.euclidean hA'
    (energyInner_iterationOperator_comm s.euclidean hA'.isSymmetric hM')
  have hμmem' : μ ∈ spectrum ℂ (energyIterationOperator s.euclidean hA') := by
    rw [spectrum_energyIterationOperator, euclidean_iterationOperator,
      AlgEquiv.spectrum_eq (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))]
    exact hμmem
  have hreal : μ = (μ.re : ℂ) := hsa.mem_spectrum_eq_re hμmem'
  have hmemR : μ.re ∈ spectrum ℝ G := by
    rw [← ofReal_mem_spectrum_complexify_iff, ← hreal]
    exact hμmem
  rw [spectrum.mem_iff, isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← exists_mulVec_eq_zero_iff] at hmemR
  obtain ⟨e, he, hGe⟩ := hmemR
  rw [sub_mulVec, Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec, sub_eq_zero] at hGe
  refine ⟨e, he, μ.re, ?_, hGe.symm⟩
  rw [← hμρ, hreal, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]

/-- **The spectral radius is attained in the real energy norm** ([quarteroni2000numerical] Property
4.1, the equality `ρ(B) = ‖B‖_A` read on real vectors): for a positive definite `A` and a splitting
with symmetric `M`, some real `e ≠ 0` has `(A (G e)) ⬝ (G e) = ρ(G)² ((A e) ⬝ e)`, namely the
real eigenvector of `Stationary.Splitting.exists_mulVec_iterationOperator_eq_smul`. -/
theorem exists_energyNorm_mulVec_iterationOperator_eq_complexSpectralRadius [Nonempty n]
    (hA : A.PosDef) (hM : s.m.IsHermitian) :
    ∃ e : n → ℝ, e ≠ 0 ∧ (A *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e)
      = (complexSpectralRadius s.iterationOperator).toReal ^ 2 * ((A *ᵥ e) ⬝ᵥ e) := by
  obtain ⟨e, he, μ, hμ, hGe⟩ := s.exists_mulVec_iterationOperator_eq_smul hA hM
  refine ⟨e, he, ?_⟩
  rw [hGe, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← hμ, sq_abs]
  ring

end Stationary.Splitting


/-! ### The pencil `P⁻¹ A` and Jacobi over-relaxation for a positive definite matrix -/

namespace Matrix

open Stationary

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- A complex vector with zero real and imaginary parts is zero. -/
private theorem re_ne_zero_or_im_ne_zero {z : n → ℂ} (hz : z ≠ 0) :
    (fun i => (z i).re) ≠ 0 ∨ (fun i => (z i).im) ≠ 0 := by
  by_contra h
  rw [not_or, not_not, not_not] at h
  exact hz (funext fun i => Complex.ext (by simpa using congrFun h.1 i)
    (by simpa using congrFun h.2 i))

/-- The generalized Rayleigh quotient of an eigenvalue of `P⁻¹ A`: every eigenvalue `μ` of
`P⁻¹ A`, for `A` real symmetric and `P` positive definite, is the real number
`(x ⬝ A x + y ⬝ A y) / (x ⬝ P x + y ⬝ P y)` for the real and imaginary parts `x`, `y` of an
eigenvector. -/
private theorem exists_eq_div_of_mem_spectrum_inv_mul {A P : Matrix n n ℝ} (hA : A.IsHermitian)
    (hP : P.PosDef) {μ : ℂ} (hμ : μ ∈ spectrum ℂ (complexify (P⁻¹ * A))) :
    ∃ x y : n → ℝ, (x ≠ 0 ∨ y ≠ 0) ∧ 0 < x ⬝ᵥ (P *ᵥ x) + y ⬝ᵥ (P *ᵥ y) ∧
      μ = ((x ⬝ᵥ (A *ᵥ x) + y ⬝ᵥ (A *ᵥ y)) / (x ⬝ᵥ (P *ᵥ x) + y ⬝ᵥ (P *ᵥ y)) : ℝ) := by
  obtain ⟨z, hz, hAz⟩ := (mem_spectrum_inv_mul_iff_exists_mulVec_eq_smul A hP.isUnit μ).mp hμ
  have hform := congrArg (fun w => star z ⬝ᵥ w) hAz
  simp only [dotProduct_smul] at hform
  rw [star_dotProduct_complexify_mulVec_of_isHermitian hA,
    star_dotProduct_complexify_mulVec_of_isHermitian hP.1] at hform
  set x : n → ℝ := fun i => (z i).re
  set y : n → ℝ := fun i => (z i).im
  have hxy := re_ne_zero_or_im_ne_zero hz
  have hPx : 0 ≤ x ⬝ᵥ (P *ᵥ x) := by simpa using hP.posSemidef.dotProduct_mulVec_nonneg x
  have hPy : 0 ≤ y ⬝ᵥ (P *ᵥ y) := by simpa using hP.posSemidef.dotProduct_mulVec_nonneg y
  have hp : 0 < x ⬝ᵥ (P *ᵥ x) + y ⬝ᵥ (P *ᵥ y) := by
    rcases hxy with hx | hy
    · have := hP.dotProduct_mulVec_pos hx
      simp only [star_trivial] at this
      linarith
    · have := hP.dotProduct_mulVec_pos hy
      simp only [star_trivial] at this
      linarith
  refine ⟨x, y, hxy, hp, ?_⟩
  rw [Complex.ofReal_div, eq_div_iff (by exact_mod_cast hp.ne'), hform, smul_eq_mul, mul_comm]

/-- The eigenvalues of `P⁻¹ A` are real and positive when `A` and `P` are both positive definite. -/
theorem exists_pos_ofReal_eq_of_mem_spectrum_inv_mul {A P : Matrix n n ℝ} (hA : A.PosDef)
    (hP : P.PosDef) {μ : ℂ} (hμ : μ ∈ spectrum ℂ (complexify (P⁻¹ * A))) :
    ∃ t : ℝ, 0 < t ∧ μ = t := by
  obtain ⟨x, y, hxy, hp, rfl⟩ := exists_eq_div_of_mem_spectrum_inv_mul hA.1 hP hμ
  refine ⟨_, div_pos ?_ hp, rfl⟩
  have hAx : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by simpa using hA.posSemidef.dotProduct_mulVec_nonneg x
  have hAy : 0 ≤ y ⬝ᵥ (A *ᵥ y) := by simpa using hA.posSemidef.dotProduct_mulVec_nonneg y
  rcases hxy with hx | hy
  · have := hA.dotProduct_mulVec_pos hx
    simp only [star_trivial] at this
    linarith
  · have := hA.dotProduct_mulVec_pos hy
    simp only [star_trivial] at this
    linarith

omit [Fintype n] in
/-- The diagonal part of a positive definite matrix is positive definite. -/
theorem _root_.Matrix.PosDef.diagPart {A : Matrix n n ℝ} (hA : A.PosDef) :
    (diagPart A).PosDef := by
  rw [Matrix.diagPart, posDef_diagonal_iff]
  exact fun i => hA.diag_pos

/-- **JOR converges for a positive definite matrix exactly for `0 < ω < 2/ρ(D⁻¹ A)`**
([quarteroni2000numerical] Theorem 4.4).  The JOR matrix is Richardson's `1 - ω D⁻¹ A`
(`Matrix.jorSplitting_iterationOperator_eq_one_sub`), the eigenvalues of `D⁻¹ A` are real and
positive (`Matrix.exists_pos_ofReal_eq_of_mem_spectrum_inv_mul`), the largest of them is
`ρ(D⁻¹ A)`, and `|1 - ω t| < 1` for every eigenvalue `t` exactly when `0 < ω t < 2`.  The index type
must be nonempty: for an empty one the left side holds and the right side does not. -/
theorem jorSplitting_complexSpectralRadius_lt_one_iff_of_posDef [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.PosDef) (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    complexSpectralRadius (jorSplitting A h hω).iterationOperator < 1 ↔
      0 < ω ∧ ω < 2 / (complexSpectralRadius ((diagPart A)⁻¹ * A)).toReal := by
  set M := (diagPart A)⁻¹ * A with hM
  have hpos : ∀ μ ∈ spectrum ℂ (complexify M), ∃ t : ℝ, 0 < t ∧ μ = t := fun μ hμ =>
    exists_pos_ofReal_eq_of_mem_spectrum_inv_mul hA hA.diagPart hμ
  obtain ⟨μ₀, v, hv, hμ₀v, hμ₀⟩ := exists_eigenvector_norm_eq_complexSpectralRadius M
  have hμ₀mem : μ₀ ∈ spectrum ℂ (complexify M) :=
    (mem_spectrum_iff_exists_mulVec_eq_smul _ _).mpr ⟨v, hv, hμ₀v⟩
  obtain ⟨t₀, ht₀, rfl⟩ := hpos μ₀ hμ₀mem
  have hρ : (complexSpectralRadius M).toReal = t₀ := by
    rw [← hμ₀, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht₀]
  have hle : ∀ t : ℝ, (t : ℂ) ∈ spectrum ℂ (complexify M) →
      t ≤ (complexSpectralRadius M).toReal := fun t ht => by
    have h1 : (‖(t : ℂ)‖₊ : ℝ≥0∞) ≤ complexSpectralRadius M :=
      Matrix.nnnorm_le_complexSpectralRadius ht
    have h2 := ENNReal.toReal_mono (complexSpectralRadius_ne_top M) h1
    rw [ENNReal.coe_toReal, coe_nnnorm, Complex.norm_real, Real.norm_eq_abs] at h2
    exact (le_abs_self t).trans h2
  have hnorm : ∀ t : ℝ, ‖((1 : ℝ) : ℂ) + ((-ω : ℝ) : ℂ) * (t : ℂ)‖ = |1 - ω * t| := by
    intro t
    rw [show ((1 : ℝ) : ℂ) + ((-ω : ℝ) : ℂ) * (t : ℂ) = ((1 - ω * t : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  have hspec : spectrum ℂ (complexify (1 - ω • M)) =
      (fun μ : ℂ => ((1 : ℝ) : ℂ) + ((-ω : ℝ) : ℂ) * μ) '' spectrum ℂ (complexify M) := by
    rw [← spectrum_complexify_affine M (neg_ne_zero.mpr hω)]
    congr 2
    module
  rw [jorSplitting_iterationOperator_eq_one_sub, complexSpectralRadius_lt_one_iff_forall_norm_lt,
    hspec]
  constructor
  · intro hall
    have h1 := hall _ ⟨_, hμ₀mem, rfl⟩
    rw [hnorm, abs_lt] at h1
    have hω0 : 0 < ω := by nlinarith
    refine ⟨hω0, ?_⟩
    rw [hρ, lt_div_iff₀ ht₀]
    linarith
  · rintro ⟨hω0, hω2⟩ μ ⟨ν, hν, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hpos ν hν
    have htρ := hle t hν
    rw [hρ, lt_div_iff₀ ht₀] at hω2
    rw [hnorm, abs_lt]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left htρ hω0.le]
    · nlinarith

end Matrix

/-! ### The symmetric successive over-relaxation -/

namespace Matrix

open Stationary

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

section Parts

variable {𝕜 : Type*} [Field 𝕜]

omit [Fintype n] in
/-- For a symmetric `A`, `(D + ω L)ᵀ = D + ω U`. -/
theorem diagPart_add_smul_strictLower_transpose {A : Matrix n n 𝕜} (hA : A.IsSymm) (ω : 𝕜) :
    (diagPart A + ω • strictLower A)ᵀ = diagPart A + ω • strictUpper A := by
  rw [transpose_add, transpose_smul, diagPart_transpose, strictLower_transpose, hA.eq]

/-- **The SSOR preconditioner is symmetric** for a symmetric `A` ([quarteroni2000numerical] (4.22)
and (4.21) at `ω = 1`): `(D + ωL)ᵀ = D + ωU`, so `(D + ωL) D⁻¹ (D + ωU)` is symmetric. -/
theorem ssorSplitting_m_isSymm {A : Matrix n n 𝕜} (hA : A.IsSymm) (h : IsUnit (diagPart A))
    {ω : 𝕜} (hω : ω ≠ 0) (hω2 : ω ≠ 2) : (ssorSplitting A h hω hω2).m.IsSymm := by
  have hU : (diagPart A + ω • strictUpper A)ᵀ = diagPart A + ω • strictLower A := by
    rw [← diagPart_add_smul_strictLower_transpose hA ω, transpose_transpose]
  change ((ω * (2 - ω))⁻¹ • ((diagPart A + ω • strictLower A) * (diagPart A)⁻¹ *
    (diagPart A + ω • strictUpper A)))ᵀ = (ω * (2 - ω))⁻¹ • ((diagPart A + ω • strictLower A) *
      (diagPart A)⁻¹ * (diagPart A + ω • strictUpper A))
  rw [transpose_smul, transpose_mul, transpose_mul, transpose_nonsing_inv, diagPart_transpose,
    hA.eq, hU, diagPart_add_smul_strictLower_transpose hA ω, Matrix.mul_assoc]

end Parts

variable {A : Matrix n n ℝ}

/-- **The SSOR preconditioner is positive definite** for a symmetric `A` with positive diagonal
(not necessarily positive definite) and `0 < ω < 2` ([golub2013matrix] §11.2.7, after (11.2.24)):
it is the positive multiple `(ω (2 - ω))⁻¹` of the congruence `X D⁻¹ Xᵀ` of the positive definite
`D⁻¹` by the invertible `X = D + ωL`. -/
theorem ssorSplitting_m_posDef_of_diag_pos (hA : A.IsHermitian) (hd : ∀ i, 0 < A i i)
    (h : IsUnit (diagPart A)) {ω : ℝ} (hω0 : 0 < ω) (hω2 : ω < 2) :
    (ssorSplitting A h hω0.ne' hω2.ne).m.PosDef := by
  have hsymm : A.IsSymm := isHermitian_iff_isSymm.mp hA
  have hX : IsUnit (diagPart A + ω • strictLower A) := isUnit_diagPart_add_smul_strictLower h ω
  have hDi : (diagPart A)⁻¹.PosDef := by
    refine PosDef.inv ?_
    rw [diagPart, posDef_diagonal_iff]
    exact hd
  change ((ω * (2 - ω))⁻¹ • ((diagPart A + ω • strictLower A) * (diagPart A)⁻¹ *
    (diagPart A + ω • strictUpper A))).PosDef
  rw [← diagPart_add_smul_strictLower_transpose hsymm, ← conjTranspose_eq_transpose_of_trivial]
  refine PosDef.smul (hDi.mul_mul_conjTranspose_same ?_) ?_
  · exact (vecMul_injective_iff_isUnit).mpr hX
  · exact inv_pos.mpr (mul_pos hω0 (by linarith))

/-- **The SSOR preconditioner is positive definite** for a positive definite `A` and `0 < ω < 2`,
the case of `Matrix.ssorSplitting_m_posDef_of_diag_pos` where the diagonal is positive because `A`
is positive definite. -/
theorem ssorSplitting_m_posDef (hA : A.PosDef) (h : IsUnit (diagPart A)) {ω : ℝ} (hω0 : 0 < ω)
    (hω2 : ω < 2) : (ssorSplitting A h hω0.ne' hω2.ne).m.PosDef :=
  ssorSplitting_m_posDef_of_diag_pos hA.1 (fun _ => hA.diag_pos) h hω0 hω2

/-- The two triangular factors of the SSOR preconditioner, expanded. -/
private theorem expand_mul_inv_mul (h : IsUnit (diagPart A)) (a b : ℝ) :
    (a • diagPart A + b • strictLower A) * (diagPart A)⁻¹ * (a • diagPart A + b • strictUpper A)
      = (a * a) • diagPart A + (a * b) • strictLower A + (a * b) • strictUpper A
        + (b * b) • (strictLower A * (diagPart A)⁻¹ * strictUpper A) := by
  have hdet : IsUnit (diagPart A).det := (isUnit_iff_isUnit_det _).mp h
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hdet, nonsing_inv_mul _ hdet, Matrix.mul_one]
  module

/-- **The SSOR preconditioner dominates `A`**: for a symmetric `A` with positive diagonal and
`0 < ω < 2`, `P_SSOR - A` is positive semidefinite, by the factorization
`P_SSOR - A = (ω (2 - ω))⁻¹ ((1 - ω) D - ωL) D⁻¹ ((1 - ω) D - ωU)`; at `ω = 1` it reads
`P_SGS - A = L D⁻¹ U`.  This is the "`P ≥ A`" that makes the SSOR iteration matrix positive
semidefinite in the `A`-inner product. -/
theorem ssorSplitting_m_sub_posSemidef (hA : A.IsHermitian) (hd : ∀ i, 0 < A i i)
    (h : IsUnit (diagPart A)) {ω : ℝ} (hω0 : 0 < ω) (hω2 : ω < 2) :
    ((ssorSplitting A h hω0.ne' hω2.ne).m - A).PosSemidef := by
  have hsymm : A.IsSymm := isHermitian_iff_isSymm.mp hA
  have hc : 0 < ω * (2 - ω) := mul_pos hω0 (by linarith)
  have hDi : (diagPart A)⁻¹.PosDef := by
    refine PosDef.inv ?_
    rw [diagPart, posDef_diagonal_iff]
    exact hd
  have hkey : (ssorSplitting A h hω0.ne' hω2.ne).m - A =
      (ω * (2 - ω))⁻¹ • (((1 - ω) • diagPart A - ω • strictLower A) * (diagPart A)⁻¹ *
        ((1 - ω) • diagPart A - ω • strictUpper A)) := by
    change (ω * (2 - ω))⁻¹ • ((diagPart A + ω • strictLower A) * (diagPart A)⁻¹ *
      (diagPart A + ω • strictUpper A)) - A = _
    have e1 := expand_mul_inv_mul h 1 ω
    have e2 := expand_mul_inv_mul h (1 - ω) (-ω)
    simp only [one_smul, neg_smul, ← sub_eq_add_neg] at e1 e2
    have hAeq : A = diagPart A + strictLower A + strictUpper A :=
      (diagPart_add_strictLower_add_strictUpper A).symm
    have hc' : (ω * (2 - ω))⁻¹ * (ω * (2 - ω)) = 1 := inv_mul_cancel₀ hc.ne'
    have hdiff : (diagPart A + ω • strictLower A) * (diagPart A)⁻¹ *
        (diagPart A + ω • strictUpper A) - ((1 - ω) • diagPart A - ω • strictLower A) *
          (diagPart A)⁻¹ * ((1 - ω) • diagPart A - ω • strictUpper A) = (ω * (2 - ω)) • A := by
      rw [e1, e2]
      conv_rhs => rw [hAeq]
      module
    calc (ω * (2 - ω))⁻¹ • ((diagPart A + ω • strictLower A) * (diagPart A)⁻¹ *
          (diagPart A + ω • strictUpper A)) - A
        = (ω * (2 - ω))⁻¹ • ((diagPart A + ω • strictLower A) * (diagPart A)⁻¹ *
            (diagPart A + ω • strictUpper A)) - (ω * (2 - ω))⁻¹ • ((ω * (2 - ω)) • A) := by
          rw [smul_smul, hc', one_smul]
      _ = _ := by rw [← smul_sub, ← hdiff, sub_sub_cancel]
  rw [hkey]
  have hYt : ((1 - ω) • diagPart A - ω • strictLower A)ᴴ
      = (1 - ω) • diagPart A - ω • strictUpper A := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_smul, transpose_smul,
      diagPart_transpose, strictLower_transpose, hsymm.eq]
  rw [← hYt]
  exact (hDi.posSemidef.mul_mul_conjTranspose_same _).smul (inv_pos.mpr hc).le

/-- **SSOR converges for a positive definite matrix and `0 < ω < 2`** ([quarteroni2000numerical]
§4.2.6, and Property 4.5 at `ω = 1`): Householder–John with `M = P_SSOR`, whose
`M + Mᵀ - A = M + (M - A)` is positive definite as the sum of `Matrix.ssorSplitting_m_posDef` and
`Matrix.ssorSplitting_m_sub_posSemidef`. -/
theorem ssorSplitting_complexSpectralRadius_lt_one (hA : A.PosDef) (h : IsUnit (diagPart A))
    {ω : ℝ} (hω0 : 0 < ω) (hω2 : ω < 2) :
    complexSpectralRadius (ssorSplitting A h hω0.ne' hω2.ne).iterationOperator < 1 := by
  refine Splitting.complexSpectralRadius_lt_one_of_posDef _ hA ?_
  have hsymm : A.IsSymm := isHermitian_iff_isSymm.mp hA.1
  rw [(ssorSplitting_m_isSymm hsymm h hω0.ne' hω2.ne).eq, add_sub_assoc]
  exact (ssorSplitting_m_posDef hA h hω0 hω2).add_posSemidef
    (ssorSplitting_m_sub_posSemidef hA.1 (fun i => hA.diag_pos) h hω0 hω2)

end Matrix

namespace Stationary.Splitting

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (s : Splitting A)

omit [DecidableEq n] in
/-- The bilinear form of a symmetric matrix is symmetric. -/
private theorem dotProduct_mulVec_comm {X : Matrix n n ℝ} (hX : X.IsSymm) (x y : n → ℝ) :
    x ⬝ᵥ (X *ᵥ y) = y ⬝ᵥ (X *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hX.eq, dotProduct_comm]

/-- `A G = A - A M⁻¹ A` for the iteration matrix `G = 1 - M⁻¹ A` of a splitting. -/
theorem mul_iterationOperator_eq : A * s.iterationOperator = A - A * s.m⁻¹ * A := by
  rw [iterationOperator, Matrix.mul_sub, Matrix.mul_one, nonsing_inv_eq_ringInverse,
    Matrix.mul_assoc]

/-- **The iteration matrix is `A`-self-adjoint** when `A` and `M` are symmetric: `A G = A - A M⁻¹ A`
is symmetric. -/
theorem mul_iterationOperator_isSymm (hA : A.IsSymm) (hm : s.m.IsSymm) :
    (A * s.iterationOperator).IsSymm := by
  rw [mul_iterationOperator_eq, IsSymm, transpose_sub, transpose_mul, transpose_mul,
    transpose_nonsing_inv, hA.eq, hm.eq, Matrix.mul_assoc]

/-- **The iteration matrix is `A`-positive semidefinite** when `A` is positive definite, `M` is
symmetric and `M - A` is positive semidefinite: with `y = M⁻¹ A x`, `x ⬝ A G x = x ⬝ A x - y ⬝ M y ≥
(x - y) ⬝ A (x - y) ≥ 0`, because `y ⬝ A y ≤ y ⬝ M y` and `x ⬝ A y = y ⬝ M y`. -/
theorem mul_iterationOperator_posSemidef (hA : A.PosDef) (hm : s.m.IsSymm)
    (hsub : (s.m - A).PosSemidef) : (A * s.iterationOperator).PosSemidef := by
  have hsymm : A.IsSymm := isHermitian_iff_isSymm.mp hA.1
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact mul_iterationOperator_isSymm s hsymm hm
  · rw [star_trivial, mul_iterationOperator_eq, sub_mulVec, dotProduct_sub, ← mulVec_mulVec,
      ← mulVec_mulVec]
    set y := s.m⁻¹ *ᵥ (A *ᵥ x) with hy
    have hmy : s.m *ᵥ y = A *ᵥ x := mulVec_nonsing_inv_mulVec s.isUnit _
    have h1 : x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (s.m *ᵥ y) := by
      rw [dotProduct_mulVec_comm hsymm, ← hmy]
    have h2 : 0 ≤ y ⬝ᵥ ((s.m - A) *ᵥ y) := by simpa using hsub.dotProduct_mulVec_nonneg y
    have h3 : 0 ≤ (x - y) ⬝ᵥ (A *ᵥ (x - y)) := by
      simpa using hA.posSemidef.dotProduct_mulVec_nonneg (x - y)
    rw [sub_mulVec, dotProduct_sub] at h2
    rw [mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct,
      dotProduct_mulVec_comm hsymm y x] at h3
    linarith

end Stationary.Splitting

namespace Matrix

open Stationary

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] {A : Matrix n n ℝ}

/-- **Property 4.5 of [quarteroni2000numerical], read correctly**: for a positive definite `A` and
`0 < ω < 2`, the SSOR iteration matrix `B_s(ω)` (at `ω = 1`, `B_SGS`) satisfies `(A B).PosSemidef`,
i.e. it is self-adjoint and positive semidefinite in the `A`-inner product, so its eigenvalues are
real and lie in `[0, 1)`.  The book prints "`B_SGS` is symmetric positive definite", which is false
as printed (for a diagonal `A`, `B_SGS = 0`, and `B_SGS` is not Euclidean-symmetric in general). -/
theorem ssorSplitting_iterationOperator_posSemidef_energy (hA : A.PosDef) (h : IsUnit (diagPart A))
    {ω : ℝ} (hω0 : 0 < ω) (hω2 : ω < 2) :
    (A * (ssorSplitting A h hω0.ne' hω2.ne).iterationOperator).PosSemidef := by
  have hsymm : A.IsSymm := isHermitian_iff_isSymm.mp hA.1
  exact Splitting.mul_iterationOperator_posSemidef _ hA (ssorSplitting_m_isSymm hsymm h _ _)
    (ssorSplitting_m_sub_posSemidef hA.1 (fun i => hA.diag_pos) h hω0 hω2)

end Matrix
