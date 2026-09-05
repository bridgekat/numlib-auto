import Numlib.LinearSolve.Projection.Basic
import Numlib.Analysis.InnerProductSpace.Energy

/-!
# Optimality properties of projection methods

* Saad[^saad-iterative] Prop 5.2 / Hestenes–Stiefel[^hestenes-stiefel] Thm 4:3: for symmetric
  coercive `A`, Galerkin iterates are exactly the minimizers of the energy norm of the error
  over `x₀ + K`.
* Saad Prop 5.5: the Galerkin error is the `A`-orthogonal projection of `d₀ = x* - x₀`.
* Nested subspaces give monotone residual / error norms.
* Fong–Saunders[^fong-saunders] §2.1: the Galerkin iterate minimizes the quadratic
  `½⟪A x, x⟫ - re⟪b, x⟫`.
* Saad §8.3 and Choi[^choi]: the minimal-error method over `x₀ + A† K` is Petrov–Galerkin
  with `L = K`.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
[^hestenes-stiefel]: Magnus R. Hestenes and Eduard Stiefel, *Methods of conjugate gradients for
  solving linear systems*, Journal of Research of the National Bureau of Standards 49 (1952),
  409–436.
[^fong-saunders]: David Chin-Lung Fong and Michael Saunders, *CG versus MINRES: an empirical
  comparison*, SQU Journal for Science 17 (2012), 44–62.
[^choi]: Sou-Cheng Choi, *Iterative Methods for Singular Linear Equations and Least-Squares
  Problems*, PhD thesis, Stanford University, 2006.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {A : E →ₗ[𝕜] E} {b x₀ : E} {K : Submodule 𝕜 E} {x xstar : E}


/-- Comparison of energy norms may be checked on the squares. -/
theorem energyNorm_le_of_sq_le {u v : E} (h : energyNorm A u ^ 2 ≤ energyNorm A v ^ 2) :
    energyNorm A u ≤ energyNorm A v := by
  have h2 := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (energyNorm_nonneg A u), Real.sqrt_sq (energyNorm_nonneg A v)] at h2

/-- Pythagoras for the energy inner product. -/
theorem energyNorm_add_sq (hA : A.IsSymmetricCoercive) {u v : E} (h : energyInner A u v = 0) :
    energyNorm A (u + v) ^ 2 = energyNorm A u ^ 2 + energyNorm A v ^ 2 := by
  have huv : inner 𝕜 (A u) v = (0 : 𝕜) := h
  have hvu : inner 𝕜 (A v) u = (0 : 𝕜) := by
    rw [hA.isSymmetric v u, ← inner_conj_symm, huv, map_zero]
  rw [hA.energyNorm_sq, hA.energyNorm_sq, hA.energyNorm_sq, map_add, inner_add_left,
    inner_add_right, inner_add_right, huv, hvu]
  simp

namespace IsGalerkin

-- `hA` is part of the stated interface (the hypothesis of Saad, *Iterative Methods*, Prop 5.2)
-- but the identity
-- `⟪A (x* - x), z⟫ = ⟪b - A x, z⟫` needs neither symmetry nor coercivity.
set_option linter.unusedVariables false in
/-- Galerkin error is energy-orthogonal to `K`. -/
theorem energyInner_error_eq_zero (hA : A.IsSymmetricCoercive) (hx : IsGalerkin A b x₀ K x)
    (hstar : A xstar = b) {z : E} (hz : z ∈ K) : energyInner A (xstar - x) z = 0 := by
  have h : energyInner A (xstar - x) z = inner 𝕜 (A (xstar - x)) z := rfl
  rw [h, map_sub, hstar]
  exact inner_eq_zero_symm.1 (hx.inner_residual_eq_zero hz)

/-- Pythagoras in the energy norm: `‖x* - y‖_A² = ‖x* - x‖_A² + ‖x - y‖_A²` for `y ∈ x₀ + K`. -/
theorem energyNorm_sq_add (hA : A.IsSymmetricCoercive) (hx : IsGalerkin A b x₀ K x)
    (hstar : A xstar = b) {y : E} (hy : y - x₀ ∈ K) :
    energyNorm A (xstar - y) ^ 2 = energyNorm A (xstar - x) ^ 2 + energyNorm A (x - y) ^ 2 := by
  have hxy : x - y ∈ K := by
    have h : x - y = (x - x₀) - (y - x₀) := by abel
    rw [h]; exact K.sub_mem hx.mem hy
  have hsum : xstar - y = (xstar - x) + (x - y) := by abel
  rw [hsum]
  exact energyNorm_add_sq hA (energyInner_error_eq_zero hA hx hstar hxy)

/-- Saad, *Iterative Methods*, Prop 5.2 (⇒): Galerkin iterates minimize the energy norm of the
error over `x₀ + K`. -/
theorem energyNorm_le (hA : A.IsSymmetricCoercive) (hx : IsGalerkin A b x₀ K x)
    (hstar : A xstar = b) {y : E} (hy : y - x₀ ∈ K) :
    energyNorm A (xstar - x) ≤ energyNorm A (xstar - y) := by
  refine energyNorm_le_of_sq_le ?_
  rw [energyNorm_sq_add hA hx hstar hy]
  nlinarith [energyNorm_nonneg A (x - y)]

/-- Saad, *Iterative Methods*, Prop 5.2 (⇔), for finite-dimensional `K`: an iterate is Galerkin
iff it lies in `x₀ + K` and minimizes the energy norm of the error there. -/
theorem iff_energyNorm_min (hA : A.IsSymmetricCoercive) (hstar : A xstar = b)
    [FiniteDimensional 𝕜 K] :
    IsGalerkin A b x₀ K x ↔
      x - x₀ ∈ K ∧ ∀ y, y - x₀ ∈ K → energyNorm A (xstar - x) ≤ energyNorm A (xstar - y) := by
  refine ⟨fun hx => ⟨hx.mem, fun y hy => energyNorm_le hA hx hstar hy⟩, ?_⟩
  rintro ⟨hmem, hmin⟩
  obtain ⟨x', hx', -⟩ :=
    existsUnique_isGalerkin_of_isCoercive (A := A) b x₀ K hA.isCoercive
  have heq : energyNorm A (xstar - x) = energyNorm A (xstar - x') :=
    le_antisymm (hmin x' hx'.mem) (energyNorm_le hA hx' hstar hmem)
  have hpy := energyNorm_sq_add hA hx' hstar hmem
  rw [← heq] at hpy
  have hzero : energyNorm A (x' - x) = 0 := by
    nlinarith [energyNorm_nonneg A (x' - x), energyNorm_nonneg A (xstar - x)]
  have : x' = x := sub_eq_zero.1 (hA.energyNorm_eq_zero_iff.1 hzero)
  rwa [this] at hx'

/-- Nested subspaces: energy-norm errors are nonincreasing. -/
theorem energyNorm_le_of_le (hA : A.IsSymmetricCoercive) {K' : Submodule 𝕜 E} {x' : E}
    (hx : IsGalerkin A b x₀ K x) (hx' : IsGalerkin A b x₀ K' x') (hKK' : K ≤ K')
    (hstar : A xstar = b) : energyNorm A (xstar - x') ≤ energyNorm A (xstar - x) :=
  energyNorm_le hA hx' hstar (hKK' hx.mem)

/-- Fong–Saunders (2.1): the Galerkin iterate minimizes `φ(x) = ½ re⟪A x, x⟫ - re⟪b, x⟫`
over `x₀ + K`. -/
theorem quadratic_le (hA : A.IsSymmetricCoercive) (hx : IsGalerkin A b x₀ K x) {y : E}
    (hy : y - x₀ ∈ K) :
    RCLike.re (inner 𝕜 (A x) x) / 2 - RCLike.re (inner 𝕜 b x) ≤
      RCLike.re (inner 𝕜 (A y) y) / 2 - RCLike.re (inner 𝕜 b y) := by
  have hd : y - x ∈ K := by
    have h : y - x = (y - x₀) - (x - x₀) := by abel
    rw [h]; exact K.sub_mem hy hx.mem
  obtain ⟨d, hdK, rfl⟩ : ∃ d, d ∈ K ∧ y = x + d := ⟨y - x, hd, by abel⟩
  have hbd : inner 𝕜 (b - A x) d = (0 : 𝕜) :=
    inner_eq_zero_symm.1 (hx.inner_residual_eq_zero hdK)
  have hbd' : RCLike.re (inner 𝕜 b d) = RCLike.re (inner 𝕜 (A x) d) := by
    rw [inner_sub_left, sub_eq_zero] at hbd
    rw [hbd]
  have hsymd : RCLike.re (inner 𝕜 (A d) x) = RCLike.re (inner 𝕜 (A x) d) := by
    rw [hA.isSymmetric d x, ← inner_conj_symm]
    exact RCLike.conj_re _
  obtain ⟨c, hc, hAc⟩ := hA.isCoercive
  have hpos : 0 ≤ RCLike.re (inner 𝕜 (A d) d) :=
    le_trans (by positivity) (hAc d)
  simp only [map_add, inner_add_left, inner_add_right]
  rw [hsymd, hbd']
  linarith

/-- Saad, *Iterative Methods*, Prop 5.5: the Galerkin error is the energy-orthogonal projection
of `d₀ = x* - x₀` onto the energy-orthogonal complement of `K`. -/
theorem error_eq_starProjection (hA : A.IsSymmetricCoercive) (hx : IsGalerkin A b x₀ K x)
    (hstar : A xstar = b) [FiniteDimensional 𝕜 K] :
    WithEnergy.equiv A hA (xstar - x) =
      (WithEnergy.submoduleMap A hA K)ᗮ.starProjection (WithEnergy.equiv A hA (xstar - x₀)) := by
  have hM : WithEnergy.submoduleMap A hA K = K.map (WithEnergy.equiv A hA).toLinearMap := rfl
  have hmem : WithEnergy.equiv A hA (xstar - x) ∈ (WithEnergy.submoduleMap A hA K)ᗮ := by
    refine (Submodule.mem_orthogonal _ _).2 fun u hu => ?_
    rw [hM] at hu
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hu
    have hzero : inner 𝕜 (A (xstar - x)) z = (0 : 𝕜) :=
      energyInner_error_eq_zero hA hx hstar hz
    have hgoal : inner 𝕜 (A z) (xstar - x) = (0 : 𝕜) := by
      rw [hA.isSymmetric z (xstar - x), ← inner_conj_symm, hzero, map_zero]
    exact hgoal
  have hdiff : WithEnergy.equiv A hA (xstar - x₀) - WithEnergy.equiv A hA (xstar - x)
      ∈ (WithEnergy.submoduleMap A hA K)ᗮᗮ := by
    have h : WithEnergy.equiv A hA (xstar - x₀) - WithEnergy.equiv A hA (xstar - x)
        = WithEnergy.equiv A hA (x - x₀) := by
      rw [← map_sub]; congr 1; abel
    rw [h]
    exact Submodule.le_orthogonal_orthogonal _
      ((WithEnergy.equiv_mem_submoduleMap_iff A hA).2 hx.mem)
  exact (Submodule.eq_starProjection_of_mem_orthogonal hmem hdiff).symm

end IsGalerkin

namespace IsMinError

/-- Minimal-error iterates on nested subspaces have nonincreasing error. -/
theorem norm_error_le_of_le {K' : Submodule 𝕜 E} {x' : E} (hx : IsMinError xstar x₀ K x)
    (hx' : IsMinError xstar x₀ K' x') (hKK' : K ≤ K') : ‖xstar - x'‖ ≤ ‖xstar - x‖ :=
  hx'.min x (hKK' hx.mem)

/-- The error is orthogonal to `K`. -/
theorem sub_mem_orthogonal (hx : IsMinError xstar x₀ K x) : xstar - x ∈ Kᗮ := by
  refine (Submodule.mem_orthogonal' _ _).2 fun w hw => ?_
  have h1 : xstar - x = (xstar - x₀) - (x - x₀) := by abel
  rw [h1]
  refine Submodule.inner_eq_zero_of_forall_norm_sub_le hx.mem (fun z hz => ?_) hw
  have h2 := hx.min (x₀ + z) (by simpa using hz)
  rwa [show xstar - (x₀ + z) = (xstar - x₀) - z by abel, h1] at h2

/-- The minimal-error iterate is the orthogonal projection of `x*` onto `x₀ + K`. -/
theorem eq_starProjection [K.HasOrthogonalProjection] (hx : IsMinError xstar x₀ K x) :
    x - x₀ = K.starProjection (xstar - x₀) := by
  refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero hx.mem fun w hw => ?_).symm
  rw [show (xstar - x₀) - (x - x₀) = xstar - x by abel]
  exact (Submodule.mem_orthogonal' _ _).1 hx.sub_mem_orthogonal w hw

theorem unique {x' : E} (hx : IsMinError xstar x₀ K x) (hx' : IsMinError xstar x₀ K x') :
    x = x' := by
  have hmem : (x₀ + (2 : 𝕜)⁻¹ • ((x - x₀) + (x' - x₀))) - x₀ ∈ K := by
    rw [add_sub_cancel_left]
    exact K.smul_mem _ (K.add_mem hx.mem hx'.mem)
  have hd : ‖xstar - x‖ = ‖xstar - x'‖ := le_antisymm (hx.min x' hx'.mem) (hx'.min x hx.mem)
  have hsplit : (xstar - x) + (xstar - x')
      = (2 : 𝕜) • (xstar - (x₀ + (2 : 𝕜)⁻¹ • ((x - x₀) + (x' - x₀)))) := by
    match_scalars <;> norm_num
  have hnorm : ‖(xstar - x) + (xstar - x')‖ = 2 * ‖xstar - (x₀ + (2 : 𝕜)⁻¹ •
      ((x - x₀) + (x' - x₀)))‖ := by
    rw [hsplit, norm_smul, RCLike.norm_two]
  have hge : ‖xstar - x‖ ≤ ‖xstar - (x₀ + (2 : 𝕜)⁻¹ • ((x - x₀) + (x' - x₀)))‖ :=
    hx.min _ hmem
  have hpar := parallelogram_law_with_norm 𝕜 (xstar - x) (xstar - x')
  rw [show (xstar - x) - (xstar - x') = x' - x by abel] at hpar
  have hx'x : ‖x' - x‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg (x' - x), norm_nonneg (xstar - x)]
  have : ‖x' - x‖ = 0 := by nlinarith [norm_nonneg (x' - x)]
  exact (sub_eq_zero.1 (norm_eq_zero.1 this)).symm

/-- Saad, *Iterative Methods*, §8.3, and Choi, *Iterative Methods for Singular Linear
Equations*: minimal error over `x₀ + A† K` is Petrov–Galerkin with `L = K`
(CGNE / Craig's method as a Petrov–Galerkin method). -/
theorem isPetrovGalerkin_of_map_adjoint [FiniteDimensional 𝕜 E] {L : Submodule 𝕜 E}
    (hK : K = L.map (LinearMap.adjoint A)) (hstar : A xstar = b) (hx : IsMinError xstar x₀ K x) :
    IsPetrovGalerkin A b x₀ K L x := by
  refine ⟨hx.mem, (Submodule.mem_orthogonal _ _).2 fun w hw => ?_⟩
  have h1 : b - A x = A (xstar - x) := by rw [map_sub, hstar]
  rw [h1, ← LinearMap.adjoint_inner_left]
  refine (Submodule.mem_orthogonal _ _).1 hx.sub_mem_orthogonal _ ?_
  rw [hK]
  exact Submodule.mem_map_of_mem hw

end IsMinError

/-- Existence and characterization: `x₀ + P_K (x* - x₀)` is the minimal-error point. -/
theorem isMinError_add_starProjection [K.HasOrthogonalProjection] (xstar x₀ : E) :
    IsMinError xstar x₀ K (x₀ + K.starProjection (xstar - x₀)) := by
  refine ⟨?_, fun y hy => ?_⟩
  · rw [add_sub_cancel_left]
    exact Submodule.starProjection_apply_mem K _
  · rw [show xstar - (x₀ + K.starProjection (xstar - x₀))
        = (xstar - x₀) - K.starProjection (xstar - x₀) by abel,
      show xstar - y = (xstar - x₀) - (y - x₀) by abel]
    exact Submodule.norm_sub_le_of_forall_inner_eq_zero (Submodule.starProjection_apply_mem K _)
      (fun w hw => K.starProjection_inner_eq_zero _ w hw) hy
