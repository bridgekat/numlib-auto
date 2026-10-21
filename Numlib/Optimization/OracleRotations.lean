import Numlib.Optimization.DerivativeOracleMethods

/-!
# Rectangular rotations of derivative oracles

An isometric embedding pulls objectives back by its adjoint. This preserves objective
values, infima, gradient norms and positive-order diagonal derivative Lipschitz bounds.
The statements concern actual derivatives of the pullback; they make no history-agreement
assumption about an oracle method.
-/

noncomputable section
open scoped ContDiff InnerProductSpace

namespace Optimization.ZeroChains

variable {n m p : ℕ}

/-- The adjoint of an isometric embedding is a left inverse. -/
@[simp] theorem adjoint_embedding_apply (U : Space n →ₗᵢ[ℝ] Space m) (x : Space n) :
    U.toContinuousLinearMap.adjoint (U x) = x := by
  have h := congrArg (fun L : Space n →L[ℝ] Space n => L x) U.adjoint_comp_self
  exact h

/-- Every vector is the adjoint projection of its isometric embedding. -/
theorem adjoint_embedding_surjective (U : Space n →ₗᵢ[ℝ] Space m) :
    Function.Surjective U.toContinuousLinearMap.adjoint :=
  fun x => ⟨U x, adjoint_embedding_apply U x⟩

/-- An isometric embedding's adjoint has operator norm at most one, including dimension zero. -/
theorem norm_adjoint_embedding_le_one (U : Space n →ₗᵢ[ℝ] Space m) :
    ‖U.toContinuousLinearMap.adjoint‖ ≤ 1 := by
  rw [ContinuousLinearMap.adjoint.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp

/-- The adjoint projection is a contraction on vectors. -/
theorem norm_adjoint_embedding_apply_le (U : Space n →ₗᵢ[ℝ] Space m) (x : Space m) :
    ‖U.toContinuousLinearMap.adjoint x‖ ≤ ‖x‖ := by
  exact (U.toContinuousLinearMap.adjoint.le_opNorm x).trans
    (by simpa using mul_le_mul_of_nonneg_right (norm_adjoint_embedding_le_one U) (norm_nonneg x))

/-- Full tensor chain rule for a linear pullback, retaining every direction. -/
theorem iteratedFDeriv_pullback {f : Space n → ℝ} (hf : ContDiff ℝ p f)
    {q : ℕ} (hq : q ≤ p) (L : Space m →L[ℝ] Space n) (x : Space m) :
    iteratedFDeriv ℝ q (pullback L f) x =
      (iteratedFDeriv ℝ q f (L x)).compContinuousLinearMap (fun _ => L) := by
  exact L.iteratedFDeriv_comp_right hf x (by exact_mod_cast hq)

/-- Full tensor chain rule for the adjoint pullback of an isometric embedding. -/
theorem iteratedFDeriv_rotate {f : Space n → ℝ} (hf : ContDiff ℝ p f)
    {q : ℕ} (hq : q ≤ p) (U : Space n →ₗᵢ[ℝ] Space m) (x : Space m) :
    iteratedFDeriv ℝ q (rotate U f) x =
      (iteratedFDeriv ℝ q f (U.toContinuousLinearMap.adjoint x)).compContinuousLinearMap
        (fun _ => U.toContinuousLinearMap.adjoint) :=
  iteratedFDeriv_pullback hf hq U.toContinuousLinearMap.adjoint x

/-- The rotated objective agrees with the original on the embedded subspace. -/
@[simp] theorem rotate_embedding (U : Space n →ₗᵢ[ℝ] Space m) (f : Space n → ℝ)
    (x : Space n) : rotate U f (U x) = f x := by
  simp [rotate, pullback]

/-- Rectangular rotation preserves the objective at the origin. -/
@[simp] theorem rotate_zero (U : Space n →ₗᵢ[ℝ] Space m) (f : Space n → ℝ) :
    rotate U f 0 = f 0 := by simp [rotate, pullback]

/-- Rectangular rotation preserves the entire range of objective values. -/
theorem range_rotate (U : Space n →ₗᵢ[ℝ] Space m) (f : Space n → ℝ) :
    Set.range (rotate U f) = Set.range f := by
  exact (adjoint_embedding_surjective U).range_comp f

/-- Rectangular rotation preserves the actual infimum of the objective, even when unbounded. -/
@[simp] theorem sInf_range_rotate (U : Space n →ₗᵢ[ℝ] Space m) (f : Space n → ℝ) :
    sInf (Set.range (rotate U f)) = sInf (Set.range f) := by rw [range_rotate]

/-- Boundedness below is invariant under rectangular rotation. -/
@[simp] theorem bddBelow_range_rotate_iff (U : Space n →ₗᵢ[ℝ] Space m) (f : Space n → ℝ) :
    BddBelow (Set.range (rotate U f)) ↔ BddBelow (Set.range f) := by rw [range_rotate]

/-- The gradient of the pullback is the embedded original gradient at the projected point. -/
theorem gradient_rotate {f : Space n → ℝ}
    (U : Space n →ₗᵢ[ℝ] Space m) (x : Space m)
    (hf : DifferentiableAt ℝ f (U.toContinuousLinearMap.adjoint x)) :
    gradient (rotate U f) x = U (gradient f (U.toContinuousLinearMap.adjoint x)) := by
  apply ext_inner_right ℝ
  intro y
  rw [inner_gradient_left]
  change fderiv ℝ (f ∘ U.toContinuousLinearMap.adjoint) x y = _
  rw [fderiv_comp x hf U.toContinuousLinearMap.adjoint.differentiableAt,
    U.toContinuousLinearMap.adjoint.fderiv]
  change fderiv ℝ f (U.toContinuousLinearMap.adjoint x) (U.toContinuousLinearMap.adjoint y) = _
  rw [← inner_gradient_left]
  exact U.toContinuousLinearMap.adjoint_inner_right _ _

/-- Rectangular rotation preserves gradient norms at every projected query. -/
theorem norm_gradient_rotate {f : Space n → ℝ}
    (U : Space n →ₗᵢ[ℝ] Space m) (x : Space m)
    (hf : DifferentiableAt ℝ f (U.toContinuousLinearMap.adjoint x)) :
    ‖gradient (rotate U f) x‖ = ‖gradient f (U.toContinuousLinearMap.adjoint x)‖ := by
  rw [gradient_rotate U x hf, U.norm_map]

end Optimization.ZeroChains

namespace Optimization.DerivativeOracle
open ZeroChains

/-- Positive-order smoothness classes are preserved by actual rectangular rotations.
No increase of the objective gap or the diagonal derivative Lipschitz constant is needed. -/
theorem FunctionClass.rotate {n m p : ℕ} {Δ L : ℝ} {f : Space n → ℝ}
    (hf : FunctionClass p Δ L n f) (hp : 0 < p) (U : Space n →ₗᵢ[ℝ] Space m) :
    FunctionClass p Δ L m (ZeroChains.rotate U f) := by
  refine ⟨hf.smooth.comp U.toContinuousLinearMap.adjoint.contDiff,
    (bddBelow_range_rotate_iff U f).mpr hf.bounded_below,
    by simpa using hf.initial_gap, hf.lipschitz_nonneg, ?_⟩
  intro x y
  have hs : ContDiff ℝ p f := hf.smooth.of_le (by simp)
  rw [iteratedFDeriv_rotate hs le_rfl, iteratedFDeriv_rotate hs le_rfl]
  have he :
      (iteratedFDeriv ℝ p f (U.toContinuousLinearMap.adjoint x)).compContinuousLinearMap
          (fun _ => U.toContinuousLinearMap.adjoint) -
        (iteratedFDeriv ℝ p f (U.toContinuousLinearMap.adjoint y)).compContinuousLinearMap
          (fun _ => U.toContinuousLinearMap.adjoint) =
      (iteratedFDeriv ℝ p f (U.toContinuousLinearMap.adjoint x) -
        iteratedFDeriv ℝ p f (U.toContinuousLinearMap.adjoint y)).compContinuousLinearMap
          (fun _ => U.toContinuousLinearMap.adjoint) := by ext v; rfl
  rw [he]
  exact (ContinuousMultilinearMap.diagonalNorm_compContinuousLinearMap_le hp _ _
    (norm_adjoint_embedding_le_one U)).trans ((hf.lipschitz _ _).trans
      (mul_le_mul_of_nonneg_left (by simpa only [← map_sub] using
        norm_adjoint_embedding_apply_le U (x - y)) hf.lipschitz_nonneg))

end Optimization.DerivativeOracle
