import Numlib.Optimization.TrustRegion.SecondOrder.Finite
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Least eigenpairs of the actual Hessian

Symmetry of the second Fréchet derivative makes its Riesz Hessian self-adjoint.
In positive finite dimension, minimizing its actual quadratic form on the compact
unit sphere gives the least eigenvalue and a unit eigenvector. Changing the
vector's sign arranges the descent-ray convention without changing its eigenvalue.
-/

namespace SecondOrderTrustRegion
open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Riesz Hessian of a twice continuously differentiable objective is self-adjoint. -/
theorem hessian_isSelfAdjoint {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    IsSelfAdjoint (hessian f x) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro v w
  change inner ℝ (hessian f x v) w = inner ℝ v (hessian f x w)
  rw [←real_inner_comm v (hessian f x w)]
  simp only [hessian_apply, TaylorModel.hessianOperator, InnerProductSpace.toDual_symm_apply]
  exact (hf.isSymmSndFDerivAt (by norm_num)).eq v w

/-- In positive finite dimension an actual least Hessian eigenpair exists, and its
unit eigenvector can always be chosen with nonpositive gradient inner product. -/
theorem exists_leastEigenpair [FiniteDimensional ℝ E] [Nontrivial E]
    (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ 2 f x) :
    ∃ μ : ℝ, ∃ u : E, IsLeastEigenpair f x μ u ∧ inner ℝ (gradient f x) u ≤ 0 := by
  obtain ⟨v, hv⟩ := exists_norm_eq E (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨u, hu, hm⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (show (sphere (0 : E) 1).Nonempty from ⟨v, by simpa using hv⟩)
    (hessian f x).reApplyInnerSelf_continuous.continuousOn
  have hun : ‖u‖ = 1 := by simpa using hu
  let μ := (hessian f x).rayleighQuotient u
  have he : hessian f x u = μ • u := by
    apply (hessian_isSelfAdjoint hf).eq_smul_self_of_isLocalExtrOn
    rw [hun]
    exact Or.inl hm.isLocalMinOn
  have hp : IsLeastEigenpair f x μ u := by
    refine ⟨hun, he, ?_⟩
    intro w hw
    have hh := hm (show w ∈ sphere (0 : E) 1 by simpa using hw)
    have hv : (![w,w] : Fin 2 → E) = fun _ => w := by ext i; fin_cases i <;> rfl
    have hi := TaylorModel.inner_hessianOperator f x w w
    rw [hv] at hi
    calc
      μ = (hessian f x).reApplyInnerSelf u := by
        simp [μ, ContinuousLinearMap.rayleighQuotient, hun]
      _ ≤ (hessian f x).reApplyInnerSelf w := hh
      _ = iteratedFDeriv ℝ 2 f x (fun _ => w) := by
        simpa only [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real,
          hessian_apply] using hi
  by_cases hg : inner ℝ (gradient f x) u ≤ 0
  · exact ⟨μ,u,hp,hg⟩
  · refine ⟨μ,-u,?_,?_⟩
    · refine ⟨by simpa using hun, ?_, hp.least⟩
      change hessian f x (-u) = μ • -u
      rw [map_neg,he,smul_neg]
    · rw [inner_neg_right]
      linarith
end SecondOrderTrustRegion
