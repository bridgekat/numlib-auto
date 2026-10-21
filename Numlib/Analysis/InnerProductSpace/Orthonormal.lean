/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Orthonormal`, and
`Mathlib.Analysis.InnerProductSpace.PiL2` (which imports it) for `norm_sum_smul_eq_norm_toLp`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Parseval's identity for a finite orthonormal family

`Orthonormal.norm_sum_smul_sq`: for an orthonormal family `v` indexed by a finite type,
`‖∑ c_i v_i‖² = ∑ |c_i|²`, the squared-norm form of Mathlib's `Orthonormal.inner_sum`. It is the
coordinate computation behind every column expansion of a factorization with orthonormal columns
(the singular value decomposition, principal vectors). Its square root
`Orthonormal.norm_sum_smul_eq_norm_toLp` reads the coefficients as a vector of `EuclideanSpace`.
-/

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]

/-- **Parseval for a finite orthonormal family**: `‖∑ c_i v_i‖² = ∑ |c_i|²`. -/
theorem Orthonormal.norm_sum_smul_sq {v : ι → E} (hv : Orthonormal 𝕜 v) (c : ι → 𝕜) :
    ‖∑ i, c i • v i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
  have h := hv.inner_sum c c Finset.univ
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ((‖∑ i, c i • v i‖ ^ 2 : ℝ) : 𝕜) = ((∑ i, ‖c i‖ ^ 2 : ℝ) : 𝕜) := by
    push_cast
    rw [h]
    exact Finset.sum_congr rfl fun i _ => RCLike.conj_mul (c i)
  exact_mod_cast h2

/-- **Parseval for a finite orthonormal family**, unsquared: the norm of a combination is the
Euclidean norm of its coefficient vector. -/
theorem Orthonormal.norm_sum_smul_eq_norm_toLp {v : ι → E} (hv : Orthonormal 𝕜 v) (c : ι → 𝕜) :
    ‖∑ i, c i • v i‖ = ‖(WithLp.toLp 2 c : EuclideanSpace 𝕜 ι)‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [hv.norm_sum_smul_sq, EuclideanSpace.norm_sq_eq]
