import Numlib.LinearAlgebra.Matrix.HermitianPart
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.Complexify

/-!
# Hermitian/skew-Hermitian splitting

The two-step splitting for $H+K$ can be written as a single residual correction. The algebra
of the update uses only invertible shifts; Hermitian and skew-Hermitian hypotheses enter when
establishing invertibility and convergence.

## Main definitions

* `Matrix.hssIterationMatrix`: the homogeneous iteration matrix of the alternating splitting.
* `Matrix.hssPreconditioner`: the product of the two shifted factors divided by $2\alpha$.

## Main results

* `Matrix.hssIterationMatrix_eq`: the iteration matrix is $I-P_\alpha^{-1}(H+K)$.
* `Matrix.hssStep_eq`: an exact two-stage update is equivalent to a preconditioned residual update.
* `Matrix.isUnit_add_shift_of_skewHermitian`: a positive real shift of a skew-Hermitian matrix
  is invertible.
* `Matrix.norm_sub_one_lt_one_of_hss`: strict spectral contraction if no skew-part eigenvector
  lies in the kernel of the Hermitian part.
-/

namespace Matrix

open scoped ComplexOrder

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- The HSS iteration matrix, obtained by composing the two homogeneous half-steps. -/
noncomputable def hssIterationMatrix (H S : Matrix n n K) (α : K) : Matrix n n K :=
  (S + α • 1)⁻¹ * (α • 1 - H) * (H + α • 1)⁻¹ * (α • 1 - S)

/-- The normalized HSS preconditioner, whose factor order is the reverse of the solve order. -/
noncomputable def hssPreconditioner (H S : Matrix n n K) (α : K) : Matrix n n K :=
  (2 * α)⁻¹ • ((H + α • 1) * (S + α • 1))

/-- The inverse HSS preconditioner applies the Hermitian solve first and the
skew-Hermitian solve second, followed by multiplication by $2\alpha$. -/
theorem inv_hssPreconditioner {H S : Matrix n n K} {α : K} (hα : 2 * α ≠ 0)
    (hH : IsUnit (H + α • 1)) (hS : IsUnit (S + α • 1)) :
    (hssPreconditioner H S α)⁻¹ = (2 * α) • ((S + α • 1)⁻¹ * (H + α • 1)⁻¹) := by
  have hHi := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hH)
  have hSi := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hS)
  apply inv_eq_left_inv
  rw [hssPreconditioner, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hα, one_smul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((H + α • 1)⁻¹), hHi, Matrix.one_mul, hSi]

private theorem hssIterationFactor_eq (H : Matrix n n K) (α : K)
    (hH : IsUnit (H + α • 1)) :
    1 + (α • 1 - H) * (H + α • 1)⁻¹ = (2 * α) • (H + α • 1)⁻¹ := by
  have hH' := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hH)
  calc
    _ = ((H + α • 1) + (α • 1 - H)) * (H + α • 1)⁻¹ := by
      rw [Matrix.add_mul, hH']
    _ = _ := by
      rw [show (H + α • 1) + (α • 1 - H) = (2 * α) • (1 : Matrix n n K) by
        rw [two_mul, add_smul]; abel, smul_mul, Matrix.one_mul]

/-- The alternating iteration is the stationary iteration associated with the split
$H+S=P_\alpha-(P_\alpha-H-S)$. -/
theorem hssIterationMatrix_eq {H S : Matrix n n K} {α : K} (hα : 2 * α ≠ 0)
    (hH : IsUnit (H + α • 1)) (hS : IsUnit (S + α • 1)) :
    hssIterationMatrix H S α = 1 - (hssPreconditioner H S α)⁻¹ * (H + S) := by
  have hHi := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hH)
  have hSi := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hS)
  let Mh := H + α • (1 : Matrix n n K)
  let Ms := S + α • (1 : Matrix n n K)
  let Nh := α • (1 : Matrix n n K) - H
  have hN : α • (1 : Matrix n n K) - S = Mh - (H + S) := by dsimp [Mh]; abel
  have hM : Nh = Ms - (H + S) := by dsimp [Nh, Ms]; abel
  have hf : 1 + Nh * Mh⁻¹ = (2 * α) • Mh⁻¹ := hssIterationFactor_eq H α hH
  change Ms⁻¹ * Nh * Mh⁻¹ * (α • 1 - S) = 1 - (hssPreconditioner H S α)⁻¹ * (H + S)
  rw [inv_hssPreconditioner hα hH hS]
  change _ = 1 - ((2 * α) • (Ms⁻¹ * Mh⁻¹)) * (H + S)
  calc
    _ = Ms⁻¹ * Nh - Ms⁻¹ * (Nh * Mh⁻¹) * (H + S) := by
      rw [hN, Matrix.mul_sub, Matrix.mul_assoc (Ms⁻¹ * Nh), show Mh⁻¹ * Mh = 1 from hHi]
      simp [Matrix.mul_assoc]
    _ = 1 - Ms⁻¹ * (1 + Nh * Mh⁻¹) * (H + S) := by
      rw [hM, Matrix.mul_sub, show Ms⁻¹ * Ms = 1 from hSi]
      noncomm_ring
    _ = _ := by rw [hf, Matrix.mul_smul, Matrix.smul_mul]

/-- If the two shifted systems have been solved exactly, the combined update is
$u_{\mathrm{new}}=u+P_\alpha^{-1}(b-(H+S)u)$. -/
theorem hssStep_eq {H S : Matrix n n K} {α : K} (hα : 2 * α ≠ 0)
    (hH : IsUnit (H + α • 1)) (hS : IsUnit (S + α • 1))
    {u w v b : n → K}
    (hw : (H + α • 1) *ᵥ w = (α • 1 - S) *ᵥ u + b)
    (hv : (S + α • 1) *ᵥ v = (α • 1 - H) *ᵥ w + b) :
    v = u + (hssPreconditioner H S α)⁻¹ *ᵥ (b - (H + S) *ᵥ u) := by
  let r := b - (H + S) *ᵥ u
  have hw' : (H + α • 1) *ᵥ (w - u) = r := by
    rw [mulVec_sub, hw]
    dsimp [r]
    simp only [sub_mulVec, add_mulVec]
    abel
  have hv' : (S + α • 1) *ᵥ (v - u) = (α • 1 - H) *ᵥ (w - u) + r := by
    rw [mulVec_sub, hv, mulVec_sub]
    dsimp [r]
    simp only [sub_mulVec, add_mulVec]
    abel
  have heq := (nonsing_inv_mulVec_eq hS hv').symm
  have hsum : (1 + (α • 1 - H) * (H + α • 1)⁻¹) *ᵥ r =
      ((α • 1 - H) * (H + α • 1)⁻¹) *ᵥ r + r := by
    rw [add_mulVec, one_mulVec, add_comm]
  rw [← nonsing_inv_mulVec_eq hH hw', mulVec_mulVec, ← hsum,
    hssIterationFactor_eq H α hH, mulVec_mulVec,
    Matrix.mul_smul, ← inv_hssPreconditioner hα hH hS] at heq
  rw [sub_eq_iff_eq_add] at heq
  simpa only [add_comm] using heq

/-- If $S^H=-S$ and $\alpha>0$, the shift $S+\alpha I$ is nonsingular:
its Hermitian part is the positive definite matrix $\alpha I$. -/
theorem isUnit_add_shift_of_skewHermitian {S : Matrix n n ℂ} (hS : Sᴴ = -S)
    {α : ℝ} (hα : 0 < α) : IsUnit (S + (α : ℂ) • 1) := by
  apply isUnit_of_posDef_hermitianPart
  have heq : hermitianPart (S + (α : ℂ) • 1) = (α : ℂ) • (1 : Matrix n n ℂ) := by
    rw [hermitianPart, conjTranspose_add, conjTranspose_smul, conjTranspose_one, hS]
    simp only [Complex.star_def, Complex.conj_ofReal]
    rw [show (S + (α : ℂ) • 1) + (-S + (α : ℂ) • 1) =
      (2 : ℂ) • ((α : ℂ) • (1 : Matrix n n ℂ)) by rw [two_smul]; abel]
    rw [smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
  rw [heq]
  simpa using (PosDef.one : PosDef (1 : Matrix n n ℂ)).smul hα


private def hssEnergy (v : n → ℂ) : ℝ := (star v ⬝ᵥ v).re

omit [DecidableEq n] in
private theorem hssEnergy_pos {v : n → ℂ} (hv : v ≠ 0) : 0 < hssEnergy v :=
  (Complex.pos_iff.mp (dotProduct_star_self_pos_iff.mpr hv)).1

omit [DecidableEq n] in
private theorem hssEnergy_smul (z : ℂ) (v : n → ℂ) :
    hssEnergy (z • v) = ‖z‖ ^ 2 * hssEnergy v := by
  rw [hssEnergy, show star (z • v) = star z • star v by
    ext i; simp [Pi.smul_apply], smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, ← mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq, hssEnergy]

private theorem shiftEnergy_diff (Q : Matrix n n ℂ) (α : ℝ) (v : n → ℂ) :
    hssEnergy ((Q + (α : ℂ) • 1) *ᵥ v) - hssEnergy (((α : ℂ) • 1 - Q) *ᵥ v) =
      2 * α * (star v ⬝ᵥ ((Q + Qᴴ) *ᵥ v)).re := by
  let T : Matrix n n ℂ := (α : ℂ) • 1
  have hT : Tᴴ = T := by simp [T, conjTranspose_smul]
  have hGram : (Q + T)ᴴ * (Q + T) - (T - Q)ᴴ * (T - Q) =
      (2 * (α : ℂ)) • (Q + Qᴴ) := by
    rw [conjTranspose_add, conjTranspose_sub, hT]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub]
    dsimp only [T]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    module
  change hssEnergy ((Q + T) *ᵥ v) - hssEnergy ((T - Q) *ᵥ v) = _
  simp only [hssEnergy, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
    ← Complex.sub_re, ← dotProduct_sub, ← sub_mulVec, hGram, smul_mulVec, dotProduct_smul,
    smul_eq_mul, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.re_ofReal_mul]

/-- Suppose $H$ is Hermitian positive semidefinite, $S$ is skew-Hermitian, and no nonzero
eigenvector of $S$ lies in $\ker H$. For any real $\alpha>0$, every eigenvalue $\lambda$ of the
HSS-preconditioned matrix satisfies $|\lambda-1|<1$.

The shifted skew factor preserves the squared norm when its sign is reversed, whereas the
difference for the Hermitian factor is $4\alpha\,w^H H w$. Equality would force an eigenvector
of the skew factor into $\ker H$. -/
theorem norm_sub_one_lt_one_of_hss {H S : Matrix n n ℂ} (hH : H.PosSemidef) (hS : Sᴴ = -S)
    (hker : ∀ (ν : ℂ) (v : n → ℂ), H *ᵥ v = 0 → S *ᵥ v = ν • v → v = 0)
    {α : ℝ} (hα : 0 < α) {ell : ℂ}
    (hell : ell ∈ spectrum ℂ ((hssPreconditioner H S (α : ℂ))⁻¹ * (H + S))) :
    ‖ell - 1‖ < 1 := by
  let a : ℂ := α
  let T : Matrix n n ℂ := a • 1
  have ha : a ≠ 0 := by
    change (α : ℂ) ≠ 0
    exact_mod_cast hα.ne'
  have hHu : IsUnit (H + T) := by
    apply PosDef.isUnit
    exact PosDef.posSemidef_add hH (by
      simpa [T, a] using (PosDef.one : (1 : Matrix n n ℂ).PosDef).smul hα)
  have hSu : IsUnit (S + T) := isUnit_add_shift_of_skewHermitian hS hα
  obtain ⟨v, hv, hvec⟩ := (mem_spectrum_iff_exists_mulVec_eq_smul _ _).mp hell
  let μ : ℂ := 1 - ell
  have hiter : hssIterationMatrix H S a *ᵥ v = μ • v := by
    rw [hssIterationMatrix_eq (mul_ne_zero (by norm_num) ha) hHu hSu]
    rw [sub_mulVec, one_mulVec, hvec, sub_smul, one_smul]
  let w := (H + T)⁻¹ *ᵥ ((T - S) *ᵥ v)
  have hw : (H + T) *ᵥ w = (T - S) *ᵥ v := mulVec_nonsing_inv_mulVec hHu _
  have hstep : (T - H) *ᵥ w = μ • ((S + T) *ᵥ v) := by
    have h := congrArg (fun x ↦ (S + T) *ᵥ x) hiter
    change (S + T) *ᵥ (((S + T)⁻¹ * (T - H) * (H + T)⁻¹ * (T - S)) *ᵥ v) = _ at h
    simpa only [← mulVec_mulVec, mulVec_nonsing_inv_mulVec hSu, mulVec_smul, w] using h
  have hHenergy : hssEnergy ((H + T) *ᵥ w) - hssEnergy ((T - H) *ᵥ w) =
      4 * α * (star w ⬝ᵥ (H *ᵥ w)).re := by
    rw [shiftEnergy_diff H α w, hH.1.eq, add_mulVec, dotProduct_add, Complex.add_re]
    ring
  have hSenergy : hssEnergy ((S + T) *ᵥ v) = hssEnergy ((T - S) *ᵥ v) := by
    apply sub_eq_zero.mp
    rw [shiftEnergy_diff S α v, hS, add_neg_cancel, zero_mulVec, dotProduct_zero,
      Complex.zero_re, mul_zero]
  have hp : 0 < hssEnergy ((S + T) *ᵥ v) := by
    apply hssEnergy_pos
    intro hz
    exact hv (by simpa [hz] using (nonsing_inv_mulVec_mulVec hSu v).symm)
  by_contra hn
  have hμ : 1 ≤ ‖μ‖ := by
    simpa [μ, norm_sub_rev] using le_of_not_gt hn
  have hsq : 1 ≤ ‖μ‖ ^ 2 := by nlinarith [norm_nonneg μ]
  rw [hw, ← hSenergy, hstep, hssEnergy_smul] at hHenergy
  have hq := (Complex.nonneg_iff.mp (hH.dotProduct_mulVec_nonneg w))
  have hqzero : (star w ⬝ᵥ (H *ᵥ w)).re = 0 := by
    by_contra hneq
    have hpos : 0 < (star w ⬝ᵥ (H *ᵥ w)).re := lt_of_le_of_ne hq.1 (Ne.symm hneq)
    have hleft := mul_le_mul_of_nonneg_right hsq hp.le
    have hright := mul_pos (mul_pos (show (0 : ℝ) < 4 by norm_num) hα) hpos
    linarith
  have hHw : H *ᵥ w = 0 := hH.dotProduct_mulVec_zero_iff.mp
    (Complex.ext (by simpa using hqzero) (by simpa using hq.2.symm))
  have hw' : a • w = a • v - S *ᵥ v := by
    simpa only [add_mulVec, sub_mulVec, smul_mulVec, one_mulVec, hHw, zero_add, T] using hw
  have hstep' : a • w = μ • (S *ᵥ v + a • v) := by
    simpa only [add_mulVec, sub_mulVec, smul_mulVec, one_mulVec, hHw, sub_zero, T] using hstep
  have hvS : (1 + μ) • (S *ᵥ v) = ((1 - μ) * a) • v := by
    have heq := hw'.symm.trans hstep'
    linear_combination (norm := module) -heq
  have hμa : 1 + μ ≠ 0 := by
    intro hz
    have hval : μ = -1 := by linear_combination hz
    have hcoef : (1 - μ) * a ≠ 0 := by simp [hval, ha]
    rw [hz, zero_smul, eq_comm, smul_eq_zero] at hvS
    exact hvS.elim hcoef hv
  let ν := (1 + μ)⁻¹ * ((1 - μ) * a)
  have hSv : S *ᵥ v = ν • v := by
    have h := congrArg (fun x : n → ℂ ↦ (1 + μ)⁻¹ • x) hvS
    simpa [smul_smul, inv_mul_cancel₀ hμa, ν] using h
  have hcv : a • w = (a - ν) • v := by rw [hw', hSv, sub_smul]
  have hν : a - ν ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hcv
    have hw0 := (smul_eq_zero.mp hcv).resolve_left ha
    have hμne : μ ≠ 0 := by
      intro h
      norm_num [h] at hμ
    rw [hw0, mulVec_zero, eq_comm, smul_eq_zero] at hstep
    exact (ne_of_gt hp) (by simp [hstep.resolve_left hμne, hssEnergy])
  have hHv : H *ᵥ v = 0 := by
    have h := congrArg (fun x ↦ H *ᵥ x) hcv
    simp only [mulVec_smul, hHw, smul_zero] at h
    exact (smul_eq_zero.mp h.symm).resolve_left hν
  exact hv (hker ν v hHv hSv)

end Matrix
