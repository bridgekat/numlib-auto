import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearSolve.Stationary.ADI
import NumlibSurface.SaadSparse.Chapter02.Section02

/-!
# Saad §4.3: alternating direction methods

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §4.3: the splitting `A = H + V` (4.49) of a discretized elliptic operator into its horizontal
and vertical three-point differences, Algorithm 4.3 (Peaceman–Rachford), the identities
(4.50)–(4.52) with Problem P-4.5, and the convergence claim the section asserts in prose.

The section states no numbered result. One sweep of Algorithm 4.3 is `adiStep`, with
`adiHalfStep` for the intermediate vector; `equation_4_50` identifies it with the affine map
`x ↦ G_adi x + f_adi` of (4.50)–(4.51), and `adiSplitting` with `equation_4_52`,
`adiSplitting_iterationOperator` and `f_adi_eq` are the splitting `A = M - N` of (4.52) together
with the closed form of `f = M⁻¹ b` that Problem P-4.5 asks for. All of that is matrix algebra
and holds for every `H`, `V` and `r`.

The one theorem is `adi_converges`: for symmetric positive definite `H` and `V` and a positive
constant `r` the sweep converges, from every starting vector and for every right-hand side, to
the solution of `(H + V) x = b`, and `adi_complexSpectralRadius_lt_one` gives `ρ(G_r) < 1`. Both
specialize `Numlib/LinearSolve/Stationary/ADI.lean` through `Matrix.toEuclideanCLM`, which
carries `G_adi` to `Stationary.peacemanRachford` (`toEuclideanCLM_G_adi`). Commutativity of `H`
and `V` is neither needed nor assumed: it belongs to the theory of the optimal parameter
*sequence*, which the book only cites.

Everything is indexed by an arbitrary finite type rather than by `Fin n`, because the model
problem needs the product index `Fin n₁ × Fin n₂`: `adi_model_problem` reads the five-point
matrix of §2.2.5 as `H + V` with `H` the horizontal and `V` the vertical one-dimensional
Laplacean, each positive definite, and applies `adi_converges` to it. That identity is
`SaadSparse.Chapter02.laplacian2D_eq_kroneckerSum` read as a sum of its two Kronecker factors, and
it is the only discretization this section needs.

Not formalized, with reasons. The optimal parameter `r` and the cyclic parameter sequences: the
book states no formula, no bound and no theorem, and cites a theory that exists only when `H` and
`V` commute. The claim that ADI with the optimal `r` has the asymptotic rate of SSOR with the
optimal `ω` on the model problem: an asymptotic remark with no constant and no proof. The
`O(n² log n)` operation count. The parabolic formulation (4.53)–(4.56) and the time-stepping pair
after it, which is a semi-discretization of a partial differential equation and is not the image
of Algorithm 4.3 under `r = 2/Δt`, the sign patterns differing. And the line-ordering remark that
each half-step decouples into independent tridiagonal systems, which is about a data layout and
not about the iteration.
-/

open Filter Matrix Stationary Topology
open scoped Kronecker

namespace SaadSparse.Chapter04

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H V : Matrix ι ι ℝ} {r : ℝ}

/-! ### Elementary facts used throughout -/

private theorem mulVec_nonsing_inv_mulVec {M : Matrix ι ι ℝ} (hM : IsUnit M) (u : ι → ℝ) :
    M *ᵥ (M⁻¹ *ᵥ u) = u := by
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det M).mp hM), one_mulVec]

private theorem nonsing_inv_mulVec_eq {M : Matrix ι ι ℝ} (hM : IsUnit M) {u v : ι → ℝ}
    (h : M *ᵥ v = u) : M⁻¹ *ᵥ u = v := by
  rw [← h, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det M).mp hM), one_mulVec]

private theorem isUnit_smul_matrix {c : ℝ} (hc : c ≠ 0) {M : Matrix ι ι ℝ} (hM : IsUnit M) :
    IsUnit (c • M) := by
  rw [isUnit_iff_isUnit_det, det_smul, isUnit_iff_ne_zero]
  exact mul_ne_zero (pow_ne_zero _ hc) (isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det M).mp hM))

private theorem splitting_n_eq {R : Type*} [Ring R] {a : R} (s : Stationary.Splitting a) :
    s.n = s.m - a := rfl

/-! ### Algorithm 4.3 -/

/-- Saad, Algorithm 4.3: the intermediate vector `u_{k+1/2}` of one Peaceman–Rachford sweep with
parameter `r`, the solution of `(H + r I) u_{k+1/2} = (r I - V) u_k + b`. -/
noncomputable def adiHalfStep (H V : Matrix ι ι ℝ) (r : ℝ) (b x : ι → ℝ) : ι → ℝ :=
  (H + r • 1)⁻¹ *ᵥ ((r • 1 - V) *ᵥ x + b)

/-- Saad, Algorithm 4.3: one Peaceman–Rachford sweep with parameter `r`, the horizontal
half-step `(H + r I) u_{k+1/2} = (r I - V) u_k + b` followed by the vertical one
`(V + r I) u_{k+1} = (r I - H) u_{k+1/2} + b`. -/
noncomputable def adiStep (H V : Matrix ι ι ℝ) (r : ℝ) (b x : ι → ℝ) : ι → ℝ :=
  (V + r • 1)⁻¹ *ᵥ ((r • 1 - H) *ᵥ adiHalfStep H V r b x + b)

/-- Saad, Algorithm 4.3, first half-step: `(H + r I) u_{k+1/2} = (r I - V) u_k + b`. -/
theorem adiHalfStep_spec (hH : IsUnit (H + r • (1 : Matrix ι ι ℝ))) (b x : ι → ℝ) :
    (H + r • 1) *ᵥ adiHalfStep H V r b x = (r • 1 - V) *ᵥ x + b :=
  mulVec_nonsing_inv_mulVec hH _

/-- Saad, Algorithm 4.3, second half-step: `(V + r I) u_{k+1} = (r I - H) u_{k+1/2} + b`. -/
theorem adiStep_spec (hV : IsUnit (V + r • (1 : Matrix ι ι ℝ))) (b x : ι → ℝ) :
    (V + r • 1) *ᵥ adiStep H V r b x = (r • 1 - H) *ᵥ adiHalfStep H V r b x + b :=
  mulVec_nonsing_inv_mulVec hV _

/-! ### The affine form (4.50)–(4.51) -/

/-- Saad (4.50): the iteration matrix `G_r = (V + r)⁻¹ (H - r) (H + r)⁻¹ (V - r)` of one
Peaceman–Rachford sweep. -/
noncomputable def G_adi (H V : Matrix ι ι ℝ) (r : ℝ) : Matrix ι ι ℝ :=
  (V + r • 1)⁻¹ * (H - r • 1) * (H + r • 1)⁻¹ * (V - r • 1)

/-- Saad (4.51): the affine part `f_r = (V + r)⁻¹ (I - (H - r) (H + r)⁻¹) b` of one
Peaceman–Rachford sweep. -/
noncomputable def f_adi (H V : Matrix ι ι ℝ) (r : ℝ) (b : ι → ℝ) : ι → ℝ :=
  (V + r • 1)⁻¹ *ᵥ ((1 - (H - r • 1) * (H + r • 1)⁻¹) *ᵥ b)

/-- Saad (4.50)–(4.51): one sweep of Algorithm 4.3 is the affine map `x ↦ G_r x + f_r`.  This is
matrix algebra alone; no nonsingularity is used, both sides being read with Mathlib's junk value
for the inverse of a singular matrix. -/
theorem equation_4_50 (H V : Matrix ι ι ℝ) (r : ℝ) (b x : ι → ℝ) :
    adiStep H V r b x = G_adi H V r *ᵥ x + f_adi H V r b := by
  simp only [adiStep, adiHalfStep, G_adi, f_adi, ← mulVec_mulVec, mulVec_add, sub_mulVec,
    mulVec_sub, one_mulVec, smul_mulVec, mulVec_smul]
  module

/-! ### The bridge to the backbone -/

private theorem toEuclideanCLM_injective :
    Function.Injective (toEuclideanCLM (n := ι) (𝕜 := ℝ)) := fun _ _ h => by
  simpa using congrArg (toEuclideanCLM (n := ι) (𝕜 := ℝ)).symm h

private theorem toEuclideanCLM_ringInverse {M : Matrix ι ι ℝ} (hM : IsUnit M) :
    toEuclideanCLM (𝕜 := ℝ) (Ring.inverse M) = Ring.inverse (toEuclideanCLM (𝕜 := ℝ) M) := by
  have hu : IsUnit (toEuclideanCLM (n := ι) (𝕜 := ℝ) M) := hM.map _
  refine hu.mul_left_cancel ?_
  rw [← map_mul, Ring.mul_inverse_cancel _ hM, map_one, Ring.mul_inverse_cancel _ hu]

private theorem toEuclideanCLM_nonsing_inv {M : Matrix ι ι ℝ} (hM : IsUnit M) :
    toEuclideanCLM (𝕜 := ℝ) M⁻¹ = Ring.inverse (toEuclideanCLM (𝕜 := ℝ) M) := by
  rw [nonsing_inv_eq_ringInverse, toEuclideanCLM_ringInverse hM]

private theorem toEuclideanCLM_add_smul_one (H : Matrix ι ι ℝ) (r : ℝ) :
    toEuclideanCLM (𝕜 := ℝ) (H + r • 1) = toEuclideanCLM (𝕜 := ℝ) H + (r : ℝ) • 1 := by
  rw [map_add, map_smul, map_one]

private theorem toEuclideanCLM_sub_smul_one (H : Matrix ι ι ℝ) (r : ℝ) :
    toEuclideanCLM (𝕜 := ℝ) (H - r • 1) = toEuclideanCLM (𝕜 := ℝ) H - (r : ℝ) • 1 := by
  rw [map_sub, map_smul, map_one]

private theorem isUnit_toEuclideanCLM_add_smul_one
    (hH : IsUnit (H + r • (1 : Matrix ι ι ℝ))) :
    IsUnit (toEuclideanCLM (𝕜 := ℝ) H + (r : ℝ) • 1) := by
  have h := hH.map (toEuclideanCLM (n := ι) (𝕜 := ℝ))
  rwa [toEuclideanCLM_add_smul_one] at h

/-- Saad (4.50): the iteration matrix of Algorithm 4.3 is the Peaceman–Rachford operator of
`Numlib/LinearSolve/Stationary/ADI.lean`, read through `Matrix.toEuclideanCLM`. -/
theorem toEuclideanCLM_G_adi (hH : IsUnit (H + r • (1 : Matrix ι ι ℝ)))
    (hV : IsUnit (V + r • (1 : Matrix ι ι ℝ))) :
    toEuclideanCLM (𝕜 := ℝ) (G_adi H V r)
      = peacemanRachford (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) r := by
  rw [G_adi, peacemanRachford, map_mul, map_mul, map_mul, toEuclideanCLM_nonsing_inv hV,
    toEuclideanCLM_nonsing_inv hH, toEuclideanCLM_add_smul_one, toEuclideanCLM_add_smul_one,
    toEuclideanCLM_sub_smul_one, toEuclideanCLM_sub_smul_one]
  norm_num

/-- Saad (4.51): the affine part of Algorithm 4.3 is `Stationary.peacemanRachfordConst`. -/
theorem toLp_f_adi (hH : IsUnit (H + r • (1 : Matrix ι ι ℝ)))
    (hV : IsUnit (V + r • (1 : Matrix ι ι ℝ))) (b : ι → ℝ) :
    (WithLp.toLp 2 (f_adi H V r b) : EuclideanSpace ℝ ι)
      = peacemanRachfordConst (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) r
          (WithLp.toLp 2 b) := by
  have h : toEuclideanCLM (𝕜 := ℝ) ((V + r • 1)⁻¹ * (1 - (H - r • 1) * (H + r • 1)⁻¹))
      = Ring.inverse (toEuclideanCLM (𝕜 := ℝ) V + (r : ℝ) • 1) *
        (1 - (toEuclideanCLM (𝕜 := ℝ) H - (r : ℝ) • 1) *
          Ring.inverse (toEuclideanCLM (𝕜 := ℝ) H + (r : ℝ) • 1)) := by
    rw [map_mul, toEuclideanCLM_nonsing_inv hV, toEuclideanCLM_add_smul_one, map_sub, map_one,
      map_mul, toEuclideanCLM_nonsing_inv hH, toEuclideanCLM_add_smul_one,
      toEuclideanCLM_sub_smul_one]
  rw [f_adi, mulVec_mulVec, ← toEuclideanCLM_toLp, h, peacemanRachfordConst, mul_apply_eq_comp]
  rfl

/-! ### The splitting (4.52) and Problem P-4.5 -/

/-- Saad (4.52): the splitting `A = M - N` of `A = H + V` behind Algorithm 4.3, given by
`M = (H + r)(V + r) / (2r)`. -/
noncomputable def adiSplitting (H V : Matrix ι ι ℝ) {r : ℝ} (hr : r ≠ 0)
    (hH : IsUnit (H + r • (1 : Matrix ι ι ℝ))) (hV : IsUnit (V + r • (1 : Matrix ι ι ℝ))) :
    Stationary.Splitting (H + V) :=
  ⟨(2 * r)⁻¹ • ((H + r • 1) * (V + r • 1)),
    isUnit_smul_matrix (inv_ne_zero (mul_ne_zero two_ne_zero hr)) (hH.mul hV)⟩

/-- Saad (4.52): the preconditioner of the splitting is `M = (H + r)(V + r) / (2r)`. -/
theorem adiSplitting_m {hr : r ≠ 0} {hH : IsUnit (H + r • (1 : Matrix ι ι ℝ))}
    {hV : IsUnit (V + r • (1 : Matrix ι ι ℝ))} :
    (adiSplitting H V hr hH hV).m = (2 * r)⁻¹ • ((H + r • 1) * (V + r • 1)) := rfl

private theorem toEuclideanCLM_adiSplitting_m {hr : r ≠ 0}
    {hH : IsUnit (H + r • (1 : Matrix ι ι ℝ))} {hV : IsUnit (V + r • (1 : Matrix ι ι ℝ))} :
    toEuclideanCLM (𝕜 := ℝ) (adiSplitting H V hr hH hV).m
      = (peacemanRachfordSplitting (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) hr
          (isUnit_toEuclideanCLM_add_smul_one hH) (isUnit_toEuclideanCLM_add_smul_one hV)).m := by
  rw [adiSplitting_m, peacemanRachfordSplitting_m, map_smul, map_mul,
    toEuclideanCLM_add_smul_one, toEuclideanCLM_add_smul_one]
  norm_num

private theorem toEuclideanCLM_adiSplitting_n {hr : r ≠ 0}
    {hH : IsUnit (H + r • (1 : Matrix ι ι ℝ))} {hV : IsUnit (V + r • (1 : Matrix ι ι ℝ))} :
    toEuclideanCLM (𝕜 := ℝ) (adiSplitting H V hr hH hV).n
      = (peacemanRachfordSplitting (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) hr
          (isUnit_toEuclideanCLM_add_smul_one hH) (isUnit_toEuclideanCLM_add_smul_one hV)).n := by
  rw [splitting_n_eq, splitting_n_eq, map_sub, toEuclideanCLM_adiSplitting_m, map_add]

/-- Saad (4.52): the complementary part of the splitting is `N = (H - r)(V - r) / (2r)`, so that
`M - N = H + V`.  The `H V` terms cancel, which is why the identity needs no commutativity of
`H` and `V`. -/
theorem equation_4_52 {hr : r ≠ 0} {hH : IsUnit (H + r • (1 : Matrix ι ι ℝ))}
    {hV : IsUnit (V + r • (1 : Matrix ι ι ℝ))} :
    (adiSplitting H V hr hH hV).n = (2 * r)⁻¹ • ((H - r • 1) * (V - r • 1)) := by
  refine toEuclideanCLM_injective ?_
  rw [toEuclideanCLM_adiSplitting_n, peacemanRachfordSplitting_n, map_smul, map_mul,
    toEuclideanCLM_sub_smul_one, toEuclideanCLM_sub_smul_one]
  norm_num

/-- Saad (4.52): the iteration matrix of the splitting is the `G_r` of (4.50). -/
theorem adiSplitting_iterationOperator {hr : r ≠ 0}
    {hH : IsUnit (H + r • (1 : Matrix ι ι ℝ))} {hV : IsUnit (V + r • (1 : Matrix ι ι ℝ))} :
    (adiSplitting H V hr hH hV).iterationOperator = G_adi H V r := by
  refine toEuclideanCLM_injective ?_
  rw [toEuclideanCLM_G_adi hH hV, ← peacemanRachfordSplitting_iterationOperator
      (hr := hr) (hH := isUnit_toEuclideanCLM_add_smul_one hH)
      (hV := isUnit_toEuclideanCLM_add_smul_one hV),
    Stationary.Splitting.iterationOperator, Stationary.Splitting.iterationOperator, map_sub,
    map_one, map_mul, toEuclideanCLM_ringInverse (adiSplitting H V hr hH hV).isUnit,
    toEuclideanCLM_adiSplitting_m, map_add]

/-- Saad, Problem P-4.5: the affine part (4.51) of the sweep is the simpler
`2 r (V + r)⁻¹ (H + r)⁻¹ b`. -/
theorem f_adi_eq (hH : IsUnit (H + r • (1 : Matrix ι ι ℝ))) (b : ι → ℝ) :
    f_adi H V r b = (2 * r) • ((V + r • 1)⁻¹ *ᵥ ((H + r • 1)⁻¹ *ᵥ b)) := by
  have hkey : (1 : Matrix ι ι ℝ) - (H - r • 1) * (H + r • 1)⁻¹
      = (2 * r) • (H + r • 1)⁻¹ := by
    have h2 : ((H + r • 1) - (H - r • 1)) * (H + r • (1 : Matrix ι ι ℝ))⁻¹
        = (2 * r) • (H + r • 1)⁻¹ := by
      rw [show (H + r • 1) - (H - r • (1 : Matrix ι ι ℝ)) = (2 * r) • (1 : Matrix ι ι ℝ) by module,
        smul_mul_assoc, one_mul]
    rwa [sub_mul, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hH)] at h2
  rw [f_adi, hkey, smul_mulVec, mulVec_smul]

/-- Saad, Problem P-4.5: the affine part (4.51) is `M⁻¹ b` for the preconditioner `M` of the
splitting (4.52), so that one sweep of Algorithm 4.3 really is the stationary iteration of that
splitting. -/
theorem f_adi_eq_m_inv_mulVec {hr : r ≠ 0} {hH : IsUnit (H + r • (1 : Matrix ι ι ℝ))}
    {hV : IsUnit (V + r • (1 : Matrix ι ι ℝ))} (b : ι → ℝ) :
    f_adi H V r b = (adiSplitting H V hr hH hV).m⁻¹ *ᵥ b := by
  refine (nonsing_inv_mulVec_eq (adiSplitting H V hr hH hV).isUnit ?_).symm
  rw [adiSplitting_m, f_adi_eq hH, smul_mulVec, mulVec_smul, ← mulVec_mulVec,
    mulVec_nonsing_inv_mulVec hV, mulVec_nonsing_inv_mulVec hH, smul_smul,
    inv_mul_cancel₀ (mul_ne_zero two_ne_zero hr), one_smul]

/-! ### Convergence -/

/-- For a symmetric positive definite `H` and `r > 0` the matrix `H + r I` of a half-step of
Algorithm 4.3 is nonsingular, so the sweep is well defined. -/
theorem isUnit_add_smul_one_of_posDef (hH : H.PosDef) (hr : 0 < r) :
    IsUnit (H + r • (1 : Matrix ι ι ℝ)) := by
  obtain ⟨c, hc, hcw⟩ := ((posDef_iff_isSymmetricCoercive H).1 hH).isCoercive
  have h := (Stationary.isUnit_add_smul_one (A := toEuclideanCLM (𝕜 := ℝ) H) hc hcw hr).map
    (toEuclideanCLM (n := ι) (𝕜 := ℝ)).symm
  rwa [map_add, map_smul, map_one, StarAlgEquiv.symm_apply_apply] at h

open scoped Matrix.Norms.L2Operator in
/-- Saad §4.3: for symmetric positive definite `H` and `V` and a positive parameter `r`, the
iteration matrix (4.50) of Algorithm 4.3 has spectral radius below one.  The Euclidean operator
norm of `G_r` itself need not be below one; what is below one is the norm of its conjugate by
`V + r`, which is the product of the two Cayley transforms.  And `X ↦ ‖(V + r) X (V + r)⁻¹‖₂` is
a consistent matrix norm, so it dominates the spectral radius. -/
theorem adi_complexSpectralRadius_lt_one (hH : H.PosDef) (hV : V.PosDef) (hr : 0 < r) :
    complexSpectralRadius (G_adi H V r) < 1 := by
  have hHu : IsUnit (H + r • (1 : Matrix ι ι ℝ)) := isUnit_add_smul_one_of_posDef hH hr
  have hVu : IsUnit (V + r • (1 : Matrix ι ι ℝ)) := isUnit_add_smul_one_of_posDef hV hr
  have hSS : (V + r • (1 : Matrix ι ι ℝ))⁻¹ * (V + r • 1) = 1 :=
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hVu)
  have hmul : ∀ B C : Matrix ι ι ℝ,
      ‖(V + r • (1 : Matrix ι ι ℝ)) * (B * C) * (V + r • 1)⁻¹‖₊
        ≤ ‖(V + r • (1 : Matrix ι ι ℝ)) * B * (V + r • 1)⁻¹‖₊ *
          ‖(V + r • (1 : Matrix ι ι ℝ)) * C * (V + r • 1)⁻¹‖₊ := by
    intro B C
    have h : (V + r • (1 : Matrix ι ι ℝ)) * (B * C) * (V + r • 1)⁻¹
        = ((V + r • 1) * B * (V + r • 1)⁻¹) * ((V + r • 1) * C * (V + r • 1)⁻¹) := by
      calc (V + r • (1 : Matrix ι ι ℝ)) * (B * C) * (V + r • 1)⁻¹
          = (V + r • 1) * B * ((V + r • 1)⁻¹ * (V + r • 1)) * C * (V + r • 1)⁻¹ := by
            rw [hSS]; noncomm_ring
        _ = _ := by noncomm_ring
    rw [h]
    exact nnnorm_mul_le _ _
  have hsmul : ∀ (c : ℝ) (B : Matrix ι ι ℝ),
      ‖(V + r • (1 : Matrix ι ι ℝ)) * (c • B) * (V + r • 1)⁻¹‖₊
        = ‖c‖₊ * ‖(V + r • (1 : Matrix ι ι ℝ)) * B * (V + r • 1)⁻¹‖₊ := by
    intro c B
    rw [mul_smul_comm, smul_mul_assoc, nnnorm_smul]
  have hzero : ∀ B : Matrix ι ι ℝ,
      ‖(V + r • (1 : Matrix ι ι ℝ)) * B * (V + r • 1)⁻¹‖₊ = 0 → B = 0 := by
    intro B hB
    have h0 : (V + r • (1 : Matrix ι ι ℝ)) * B * (V + r • 1)⁻¹ = 0 := by
      simpa using hB
    have h1 : (V + r • (1 : Matrix ι ι ℝ))⁻¹ *
        ((V + r • 1) * B * (V + r • 1)⁻¹) * (V + r • 1) = B := by
      calc (V + r • (1 : Matrix ι ι ℝ))⁻¹ * ((V + r • 1) * B * (V + r • 1)⁻¹) * (V + r • 1)
          = ((V + r • 1)⁻¹ * (V + r • 1)) * B * ((V + r • 1)⁻¹ * (V + r • 1)) := by
            noncomm_ring
        _ = B := by rw [hSS, one_mul, mul_one]
    rw [h0] at h1
    simpa using h1.symm
  refine (complexSpectralRadius_le_of_norm
    (fun X => ‖(V + r • (1 : Matrix ι ι ℝ)) * X * (V + r • 1)⁻¹‖₊) (G_adi H V r) hmul hsmul
    hzero).trans_lt ?_
  rw [ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_one, coe_nnnorm,
    ← l2_opNorm_toEuclideanCLM (𝕜 := ℝ), map_mul, map_mul, toEuclideanCLM_G_adi hHu hVu,
    toEuclideanCLM_nonsing_inv hVu, toEuclideanCLM_add_smul_one]
  obtain ⟨c₁, hc₁, h₁⟩ := ((posDef_iff_isSymmetricCoercive H).1 hH).isCoercive
  obtain ⟨c₂, hc₂, h₂⟩ := ((posDef_iff_isSymmetricCoercive V).1 hV).isCoercive
  exact norm_conj_peacemanRachford_lt_one ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩ hr

/-- **The convergence claim of Saad §4.3**, which the book asserts without proof: when `H` and
`V` are symmetric positive definite and the parameter `r` is a positive constant, the iterates of
Algorithm 4.3 converge, from every starting vector and for every right-hand side, to the solution
of `(H + V) x = b`.  Commutativity of `H` and `V` is not needed and is not assumed. -/
theorem adi_converges (hH : H.PosDef) (hV : V.PosDef) (hr : 0 < r) (b x₀ : ι → ℝ) {x : ι → ℝ}
    (hx : (H + V) *ᵥ x = b) :
    Tendsto (fun k => (adiStep H V r b)^[k] x₀) atTop (𝓝 x) := by
  have hHu : IsUnit (H + r • (1 : Matrix ι ι ℝ)) := isUnit_add_smul_one_of_posDef hH hr
  have hVu : IsUnit (V + r • (1 : Matrix ι ι ℝ)) := isUnit_add_smul_one_of_posDef hV hr
  obtain ⟨c₁, hc₁, h₁⟩ := ((posDef_iff_isSymmetricCoercive H).1 hH).isCoercive
  obtain ⟨c₂, hc₂, h₂⟩ := ((posDef_iff_isSymmetricCoercive V).1 hV).isCoercive
  have hxe : (toEuclideanCLM (𝕜 := ℝ) H + toEuclideanCLM (𝕜 := ℝ) V)
      (WithLp.toLp 2 x : EuclideanSpace ℝ ι) = WithLp.toLp 2 b := by
    rw [← map_add, toEuclideanCLM_toLp, hx]
  have hlim := tendsto_peacemanRachford (H := toEuclideanCLM (𝕜 := ℝ) H)
    (V := toEuclideanCLM (𝕜 := ℝ) V) ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩ hr hxe (WithLp.toLp 2 x₀)
  have hstep : ∀ y : ι → ℝ, (WithLp.toLp 2 (adiStep H V r b y) : EuclideanSpace ℝ ι)
      = step (peacemanRachford (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) r)
          (peacemanRachfordConst (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) r
            (WithLp.toLp 2 b)) (WithLp.toLp 2 y) := by
    intro y
    have hs : step (peacemanRachford (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) r)
        (peacemanRachfordConst (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) r
          (WithLp.toLp 2 b)) (WithLp.toLp 2 y)
        = peacemanRachford (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) r
            (WithLp.toLp 2 y)
          + peacemanRachfordConst (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) r
            (WithLp.toLp 2 b) := rfl
    rw [hs, equation_4_50, WithLp.toLp_add, ← toEuclideanCLM_toLp, toEuclideanCLM_G_adi hHu hVu,
      toLp_f_adi hHu hVu]
  have hiter : ∀ k : ℕ, (WithLp.toLp 2 ((adiStep H V r b)^[k] x₀) : EuclideanSpace ℝ ι)
      = (step (peacemanRachford (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) r)
          (peacemanRachfordConst (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) r
            (WithLp.toLp 2 b)))^[k] (WithLp.toLp 2 x₀) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hstep, ih]
  have hconv := ((PiLp.continuous_ofLp 2 (fun _ : ι => ℝ)).tendsto _).comp hlim
  refine Filter.Tendsto.congr (fun k => ?_) hconv
  simp only [Function.comp_apply, ← hiter k, WithLp.ofLp_toLp]

/-- Saad §4.3, `adi_converges` in the form that names the limit: since `H + V` is symmetric
positive definite the system always has a solution, and the iterates of Algorithm 4.3 converge to
it from every starting vector. -/
theorem adi_tendsto_inv_mulVec (hH : H.PosDef) (hV : V.PosDef) (hr : 0 < r) (b x₀ : ι → ℝ) :
    Tendsto (fun k => (adiStep H V r b)^[k] x₀) atTop (𝓝 ((H + V)⁻¹ *ᵥ b)) :=
  adi_converges hH hV hr b x₀
    (mulVec_nonsing_inv_mulVec (Matrix.PosDef.isUnit (Matrix.PosDef.add hH hV)) b)

/-! ### (4.49) for the model problem -/

section ModelProblem

open SaadSparse.Chapter02

/-- Saad (4.49) for the model problem: the horizontal part of the five-point matrix, the
one-dimensional Laplacean in the first coordinate. -/
noncomputable def modelH (n₁ n₂ : ℕ) (h₁ : ℝ) : Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) ℝ :=
  laplacian1D n₁ h₁ ⊗ₖ (1 : Matrix (Fin n₂) (Fin n₂) ℝ)

/-- Saad (4.49) for the model problem: the vertical part of the five-point matrix, the
one-dimensional Laplacean in the second coordinate. -/
noncomputable def modelV (n₁ n₂ : ℕ) (h₂ : ℝ) : Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) ℝ :=
  (1 : Matrix (Fin n₁) (Fin n₁) ℝ) ⊗ₖ laplacian1D n₂ h₂

/-- Saad (4.49): the two-dimensional five-point matrix of §2.2.5 is `H + V`, with `H` and `V` the
horizontal and vertical one-dimensional Laplaceans.  This is
`SaadSparse.Chapter02.laplacian2D_eq_kroneckerSum` read as a sum of its two Kronecker factors. -/
theorem laplacian2D_eq_modelH_add_modelV (n₁ n₂ : ℕ) (h₁ h₂ : ℝ) :
    laplacian2D n₁ n₂ h₁ h₂ = modelH n₁ n₂ h₁ + modelV n₁ n₂ h₂ :=
  laplacian2D_eq_kroneckerSum n₁ n₂ h₁ h₂

private theorem posDef_kronecker_one {m p : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.PosDef) :
    (A ⊗ₖ (1 : Matrix (Fin p) (Fin p) ℝ)).PosDef := by
  obtain ⟨c, hc, hcw⟩ := ((posDef_iff_isSymmetricCoercive A).1 hA).isCoercive
  have hz : (toEuclideanLin (0 : Matrix (Fin p) (Fin p) ℝ)).IsCoerciveWith 0 := by
    intro z; simp
  have hsum : A ⊗ₖ (1 : Matrix (Fin p) (Fin p) ℝ) = A ⊕ₖ (0 : Matrix (Fin p) (Fin p) ℝ) := by
    rw [kroneckerSum_def, kronecker_zero, add_zero]
  rw [hsum, posDef_iff_isSymmetricCoercive]
  refine ⟨isSymmetric_toEuclideanLin_iff.2 (isHermitian_kroneckerSum
    (Matrix.PosDef.isHermitian hA) isHermitian_zero), c, hc, ?_⟩
  have h := isCoerciveWith_kroneckerSum hcw hz
  rwa [add_zero] at h

private theorem posDef_one_kronecker {m p : ℕ} {B : Matrix (Fin p) (Fin p) ℝ} (hB : B.PosDef) :
    ((1 : Matrix (Fin m) (Fin m) ℝ) ⊗ₖ B).PosDef := by
  obtain ⟨c, hc, hcw⟩ := ((posDef_iff_isSymmetricCoercive B).1 hB).isCoercive
  have hz : (toEuclideanLin (0 : Matrix (Fin m) (Fin m) ℝ)).IsCoerciveWith 0 := by
    intro z; simp
  have hsum : (1 : Matrix (Fin m) (Fin m) ℝ) ⊗ₖ B = (0 : Matrix (Fin m) (Fin m) ℝ) ⊕ₖ B := by
    rw [kroneckerSum_def, zero_kronecker, zero_add]
  rw [hsum, posDef_iff_isSymmetricCoercive]
  refine ⟨isSymmetric_toEuclideanLin_iff.2 (isHermitian_kroneckerSum isHermitian_zero
    (Matrix.PosDef.isHermitian hB)), c, hc, ?_⟩
  have h := isCoerciveWith_kroneckerSum hz hcw
  rwa [zero_add] at h

/-- The horizontal part of the model problem is symmetric positive definite. -/
theorem modelH_posDef (n₁ n₂ : ℕ) {h₁ : ℝ} (h₁0 : h₁ ≠ 0) : (modelH n₁ n₂ h₁).PosDef :=
  posDef_kronecker_one (laplacian1D_posDef n₁ h₁0)

/-- The vertical part of the model problem is symmetric positive definite. -/
theorem modelV_posDef (n₁ n₂ : ℕ) {h₂ : ℝ} (h₂0 : h₂ ≠ 0) : (modelV n₁ n₂ h₂).PosDef :=
  posDef_one_kronecker (laplacian1D_posDef n₂ h₂0)

/-- Saad §4.3 for the model problem: Algorithm 4.3 applied to the five-point matrix of §2.2.5,
split as the horizontal plus the vertical one-dimensional Laplacean, converges for every
parameter `r > 0`. -/
theorem adi_model_problem (n₁ n₂ : ℕ) {h₁ h₂ : ℝ} (h₁0 : h₁ ≠ 0) (h₂0 : h₂ ≠ 0) {r : ℝ}
    (hr : 0 < r) (b x₀ : Fin n₁ × Fin n₂ → ℝ) {x : Fin n₁ × Fin n₂ → ℝ}
    (hx : laplacian2D n₁ n₂ h₁ h₂ *ᵥ x = b) :
    Tendsto (fun k => (adiStep (modelH n₁ n₂ h₁) (modelV n₁ n₂ h₂) r b)^[k] x₀) atTop (𝓝 x) :=
  adi_converges (modelH_posDef n₁ n₂ h₁0) (modelV_posDef n₁ n₂ h₂0) hr b x₀
    (by rwa [← laplacian2D_eq_modelH_add_modelV])

end ModelProblem

end SaadSparse.Chapter04
