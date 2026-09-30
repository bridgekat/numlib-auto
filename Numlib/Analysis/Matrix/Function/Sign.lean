import Mathlib.Analysis.CStarAlgebra.Matrix
import Numlib.Analysis.Matrix.Function.Basic
import Numlib.Analysis.Normed.Algebra.PrimaryFunctionalCalculus.Analytic
import Numlib.Analysis.Normed.Algebra.SpectralRadius

/-!
# The matrix sign function and Newton's iteration

The matrix sign function ([golub2013matrix] §9.4.1; Higham, *Functions of Matrices*, Ch. 5)
`sign(A) = pfc (z ↦ sign (Re z)) A` of a complex matrix with no eigenvalue on the imaginary axis
(junk otherwise). The scalar function is locally constant off the axis, so the primary functional
calculus computes it as `∑ ±E_λ` (`Matrix.matrixSign_eq_sum`): minus the spectral projector of the
open left half-plane plus that of the right. Newton's iteration `S₀ = A`,
`S_{k+1} = (S_k + S_k⁻¹)/2` ([golub2013matrix] (9.4.1)) is `Matrix.newtonSignIterate A k`.

## Main results

* `Matrix.matrixSign_eq_sum`, `Matrix.matrixSign_sq`, `Matrix.isUnit_add_matrixSign`,
  `Matrix.spectrum_matrixSign_subset`: the spectral form of `sign(A)`, `sign(A)² = 1`, and the
  nonsingularity of `A + sign(A)`.
* `Matrix.matrixSign_conj_fromBlocks`: the Jordan-ordered form `sign(A) = X diag(-1, 1) X⁻¹`.
* `Matrix.range_one_add_matrixSign`: `(1 + sign(A))/2` projects onto the invariant subspace of the
  eigenvalues in the right half-plane.
* `half_smul_add_inverse_sub_eq_of_commute`, … : the algebraic identities (9.4.2)–(9.4.4), in any
  algebra over a field of characteristic `≠ 2`.
* `Matrix.isUnit_newtonSignIterate`, `Matrix.matrixSign_newtonSignIterate`: every Newton iterate
  is a nonsingular rational function of `A` with the same sign.
* `Matrix.tendsto_newtonSignIterate`: the iteration converges to `sign(A)`, quadratically
  (`Matrix.norm_newtonSignIterate_sub_le`).

## Implementation notes

The name is `matrixSign`, not `sign`, to avoid the root `SignType.sign` under `open Matrix`. The
convergence proof is the book's: with `S = sign(A)` and `G_k = (S_k - S)(S_k + S)⁻¹`,
`G_{k+1} = G_k²` and `G_0 = g(A)` for `g(z) = (z - sign z)/(z + sign z)`, whose spectral radius is
`< 1`; the powers of `G_0` tend to `0` (`tendsto_pow_of_spectralRadius_lt_one`, in the spectral
norm of `open scoped Matrix.Norms.L2Operator`, whose topology is the usual one on matrices).
-/

open Polynomial Filter Topology

/-! ### The algebraic identities (9.4.2)–(9.4.4) -/

section Algebra

variable {K R : Type*} [Field K] [NeZero (2 : K)] [Ring R] [Algebra K R]

/-- **[golub2013matrix] (9.4.2)**: for a unit `s` and an involution `S` (`S² = 1`) commuting with
it, `½(s + s⁻¹) - S = ½ s⁻¹ (s - S)²`. -/
theorem half_smul_add_inverse_sub_eq_of_commute {s S : R} (hs : IsUnit s) (hS : S * S = 1)
    (hc : Commute s S) :
    (2 : K)⁻¹ • (s + Ring.inverse s) - S = (2 : K)⁻¹ • (Ring.inverse s * (s - S) ^ 2) := by
  have h1 : Ring.inverse s * s = 1 := Ring.inverse_mul_cancel s hs
  have hcS : Commute (Ring.inverse s) S := by
    obtain ⟨u, rfl⟩ := hs
    rw [Ring.inverse_unit]
    exact hc.units_inv_left
  have key : Ring.inverse s * (s - S) ^ 2 = s + Ring.inverse s - (2 : K) • S := by
    have e1 : Ring.inverse s * (s - S) ^ 2 = Ring.inverse s * s * s - Ring.inverse s * s * S -
        Ring.inverse s * S * s + Ring.inverse s * (S * S) := by
      noncomm_ring
    rw [e1, h1, hcS.eq, mul_assoc S, h1, hS]
    simp only [one_mul, mul_one, two_smul]
    abel
  rw [key, smul_sub, smul_smul, inv_mul_cancel₀ (NeZero.ne (2 : K)), one_smul]

/-- **[golub2013matrix] (9.4.3)**: `½(s + s⁻¹) + S = ½ s⁻¹ (s + S)²`. -/
theorem half_smul_add_inverse_add_eq_of_commute {s S : R} (hs : IsUnit s) (hS : S * S = 1)
    (hc : Commute s S) :
    (2 : K)⁻¹ • (s + Ring.inverse s) + S = (2 : K)⁻¹ • (Ring.inverse s * (s + S) ^ 2) := by
  have h := half_smul_add_inverse_sub_eq_of_commute (K := K) hs
    (show (-S) * (-S) = 1 by rw [neg_mul_neg, hS]) hc.neg_right
  rwa [sub_neg_eq_add, sub_neg_eq_add] at h

end Algebra

/-- The scalar sign function `z ↦ sign (Re z)` is locally constant off the imaginary axis. -/
theorem Complex.sign_re_eventuallyEq {μ : ℂ} (hμ : μ.re ≠ 0) :
    (fun z : ℂ => ((SignType.sign z.re : SignType) : ℂ)) =ᶠ[𝓝 μ]
      fun _ => ((SignType.sign μ.re : SignType) : ℂ) := by
  rcases lt_or_gt_of_ne hμ with h | h
  · filter_upwards [Complex.continuous_re.continuousAt.eventually (gt_mem_nhds h)] with z hz
    rw [sign_neg hz, sign_neg h]
  · filter_upwards [Complex.continuous_re.continuousAt.eventually (lt_mem_nhds h)] with z hz
    rw [sign_pos hz, sign_pos h]

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The matrix sign function** ([golub2013matrix] §9.4.1): `sign(A) = pfc (z ↦ sign (Re z)) A`,
meaningful when no eigenvalue of `A` is purely imaginary. -/
noncomputable def matrixSign (A : Matrix n n ℂ) : Matrix n n ℂ :=
  pfc (fun z : ℂ => ((SignType.sign z.re : SignType) : ℂ)) A

/-- The roots of the minimal polynomial are the eigenvalues. -/
private theorem mem_spectrum_of_mem_roots {A : Matrix n n ℂ} {μ : ℂ}
    (hμ : μ ∈ (minpoly ℂ A).roots) : μ ∈ spectrum ℂ A := by
  have hA : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral _
  rw [spectrum.mem_iff_isRoot_minpoly hA]
  exact (mem_roots (minpoly.ne_zero hA)).mp hμ

/-- A function that is locally constant off the imaginary axis is smooth there. -/
private theorem contDiffAt_of_eventuallyEq_const {f : ℂ → ℂ} {μ c : ℂ} (h : f =ᶠ[𝓝 μ] fun _ => c)
    (k : WithTop ℕ∞) : ContDiffAt ℂ k f μ :=
  contDiffAt_const.congr_of_eventuallyEq h

variable {A : Matrix n n ℂ}

/-- **The spectral form of the sign** ([golub2013matrix] §9.4.1): with no purely imaginary
eigenvalue, `sign(A) = ∑_{Re λ > 0} E_λ - ∑_{Re λ < 0} E_λ`, the spectral idempotents. -/
theorem matrixSign_eq_sum (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0) :
    matrixSign A = ∑ μ ∈ (minpoly ℂ A).roots.toFinset with 0 < μ.re, spectralIdempotent A μ -
      ∑ μ ∈ (minpoly ℂ A).roots.toFinset with μ.re < 0, spectralIdempotent A μ := by
  classical
  rw [matrixSign, pfc_eq_sum_smul_spectralIdempotent_of_eventuallyEq
    (Algebra.IsIntegral.isIntegral _) (IsAlgClosed.splits _)
    (fun μ hμ => Complex.sign_re_eventuallyEq (hA μ (mem_spectrum_of_mem_roots hμ)))]
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun μ : ℂ => 0 < μ.re), sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [sign_pos (Finset.mem_filter.mp hμ).2, SignType.coe_one, one_smul]
  · rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hne := hA μ (mem_spectrum_of_mem_roots (Multiset.mem_toFinset.mp hμ))
    rcases lt_or_gt_of_ne hne with h | h
    · rw [ite_eq_left (not_lt.mpr h.le), ite_eq_left h, sign_neg h, SignType.coe_neg_one,
        neg_one_smul]
    · rw [ite_eq_right (not_not.mpr h), ite_eq_right (not_lt.mpr h.le)]

/-- `sign(A)² = 1` ([golub2013matrix] §9.4.1). -/
theorem matrixSign_sq (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0) : matrixSign A ^ 2 = 1 := by
  have hev := fun μ (hμ : μ ∈ (minpoly ℂ A).roots) =>
    Complex.sign_re_eventuallyEq (hA μ (mem_spectrum_of_mem_roots hμ))
  rw [sq, matrixSign]
  refine pfc_mul_pfc_eq_one (Algebra.IsIntegral.isIntegral _) (IsAlgClosed.splits _)
    (fun μ hμ => contDiffAt_of_eventuallyEq_const (hev μ hμ) _)
    (fun μ hμ => contDiffAt_of_eventuallyEq_const (hev μ hμ) _) fun μ hμ => ?_
  filter_upwards [hev μ hμ] with z hz
  simp only [Pi.mul_apply, hz]
  rcases lt_or_gt_of_ne (hA μ (mem_spectrum_of_mem_roots hμ)) with h | h
  · simp [sign_neg h]
  · simp [sign_pos h]

/-- `A` commutes with `sign(A)`. -/
theorem commute_matrixSign (A : Matrix n n ℂ) : Commute A (matrixSign A) :=
  commute_pfc A _

/-- Similarity: `sign(P A P⁻¹) = P sign(A) P⁻¹`. -/
theorem matrixSign_conj {P : Matrix n n ℂ} (hP : IsUnit P) (A : Matrix n n ℂ) :
    matrixSign (P * A * P⁻¹) = P * matrixSign A * P⁻¹ :=
  pfc_conj hP _ A

/-- The eigenvalues of `sign(A)` are `±1`. -/
theorem spectrum_matrixSign_subset (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0) :
    spectrum ℂ (matrixSign A) ⊆ {-1, 1} := by
  rw [matrixSign, spectrum_pfc (Algebra.IsIntegral.isIntegral _) (IsAlgClosed.splits _)]
  rintro _ ⟨μ, hμ, rfl⟩
  rcases lt_or_gt_of_ne (hA μ hμ) with h | h
  · simp [sign_neg h]
  · simp [sign_pos h]

/-- **`A + sign(A)` is nonsingular** ([golub2013matrix] §9.4.1): its eigenvalues are
`λ + sign(Re λ) ≠ 0`. -/
theorem isUnit_add_matrixSign (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0) : IsUnit (A + matrixSign A) := by
  have hI : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral _
  have hev := fun μ (hμ : μ ∈ (minpoly ℂ A).roots) =>
    Complex.sign_re_eventuallyEq (hA μ (mem_spectrum_of_mem_roots hμ))
  have h : A + matrixSign A = pfc (fun z => z + ((SignType.sign z.re : SignType) : ℂ)) A := by
    rw [show (fun z : ℂ => z + ((SignType.sign z.re : SignType) : ℂ)) =
        (fun z => z) + fun z => ((SignType.sign z.re : SignType) : ℂ) from rfl,
      pfc_add (f := fun z : ℂ => z) (fun μ _ => contDiffAt_id)
        (fun μ hμ => contDiffAt_of_eventuallyEq_const (hev μ hμ) _),
      pfc_id hI (IsAlgClosed.splits _), matrixSign]
  rw [h, ← spectrum.zero_notMem_iff ℂ, spectrum_pfc hI (IsAlgClosed.splits _)]
  rintro ⟨μ, hμ, h0⟩
  have hre := congrArg Complex.re h0
  rcases lt_or_gt_of_ne (hA μ hμ) with h | h
  · simp [sign_neg h] at hre
    linarith
  · simp [sign_pos h] at hre
    linarith

/-! ### The Jordan-ordered form and the invariant subspaces -/

section Blocks

variable {l m : Type*} [Fintype l] [DecidableEq l] [Fintype m] [DecidableEq m]

/-- A function constant near every eigenvalue of `B` takes that value at `B`. -/
private theorem pfc_eq_algebraMap_of_eventuallyEq {k : Type*} [Fintype k] [DecidableEq k]
    {B : Matrix k k ℂ} {f : ℂ → ℂ} {c : ℂ} (h : ∀ μ ∈ spectrum ℂ B, f =ᶠ[𝓝 μ] fun _ => c) :
    pfc f B = algebraMap ℂ _ c := by
  have hB : IsIntegral ℂ B := Algebra.IsIntegral.isIntegral _
  rw [pfc_congr (g := fun _ => c) fun μ hμ j _ =>
    (h μ (mem_spectrum_of_mem_roots hμ)).iteratedDeriv_eq j, pfc_const hB (IsAlgClosed.splits _)]

/-- **The Jordan-ordered form of the sign** ([golub2013matrix] §9.4.1): if
`X⁻¹ A X = diag(J₁, J₂)` with the eigenvalues of `J₁` in the open left half-plane and those of `J₂`
in the open right half-plane, then `sign(A) = X diag(-1, 1) X⁻¹`. No Jordan structure of the
blocks is used. -/
theorem matrixSign_conj_fromBlocks (e : l ⊕ m ≃ n) {A X : Matrix n n ℂ} (hX : IsUnit X)
    {J₁ : Matrix l l ℂ} {J₂ : Matrix m m ℂ}
    (h : X⁻¹ * A * X = reindex e e (fromBlocks J₁ 0 0 J₂))
    (h₁ : ∀ μ ∈ spectrum ℂ J₁, μ.re < 0) (h₂ : ∀ μ ∈ spectrum ℂ J₂, 0 < μ.re) :
    matrixSign A = X * reindex e e (fromBlocks (-1) 0 0 1) * X⁻¹ := by
  have hdet := (isUnit_iff_isUnit_det X).mp hX
  have hA : A = X * (X⁻¹ * A * X) * X⁻¹ := by
    simp only [← mul_assoc, mul_nonsing_inv _ hdet, one_mul]
    rw [mul_assoc, mul_nonsing_inv _ hdet, mul_one]
  have e1 : ∀ μ ∈ spectrum ℂ J₁, (fun z : ℂ => ((SignType.sign z.re : SignType) : ℂ)) =ᶠ[𝓝 μ]
      fun _ => -1 := fun μ hμ => by
    have := Complex.sign_re_eventuallyEq (h₁ μ hμ).ne
    rwa [sign_neg (h₁ μ hμ), SignType.coe_neg_one] at this
  have e2 : ∀ μ ∈ spectrum ℂ J₂, (fun z : ℂ => ((SignType.sign z.re : SignType) : ℂ)) =ᶠ[𝓝 μ]
      fun _ => 1 := fun μ hμ => by
    have := Complex.sign_re_eventuallyEq (h₂ μ hμ).ne'
    rwa [sign_pos (h₂ μ hμ), SignType.coe_one] at this
  rw [matrixSign, hA, pfc_conj hX, h, pfc_reindex,
    pfc_fromBlocks_zero (IsAlgClosed.splits _) (IsAlgClosed.splits _),
    pfc_eq_algebraMap_of_eventuallyEq e1, pfc_eq_algebraMap_of_eventuallyEq e2, map_neg, map_one,
    map_one]

/-- **`(1 + sign(A))/2` is the spectral projector onto the right half-plane**
([golub2013matrix] §9.4.1, `X₂Y₂ᴴ = (I + sign(A))/2`): in the setting of
`Matrix.matrixSign_conj_fromBlocks`, with `X₂` the columns of `X` belonging to `J₂` and `Y₂` the
corresponding rows of `X⁻¹`, `(1 + sign(A))/2 = X₂ Y₂`; it is idempotent, and its range is
spanned by the columns of `X₂`, a subspace of dimension `card m`. -/
theorem range_one_add_matrixSign (e : l ⊕ m ≃ n) {A X : Matrix n n ℂ} (hX : IsUnit X)
    {J₁ : Matrix l l ℂ} {J₂ : Matrix m m ℂ}
    (h : X⁻¹ * A * X = reindex e e (fromBlocks J₁ 0 0 J₂))
    (h₁ : ∀ μ ∈ spectrum ℂ J₁, μ.re < 0) (h₂ : ∀ μ ∈ spectrum ℂ J₂, 0 < μ.re) :
    (2 : ℂ)⁻¹ • (1 + matrixSign A) =
        X.submatrix id (e ∘ Sum.inr) * X⁻¹.submatrix (e ∘ Sum.inr) id ∧
      IsIdempotentElem ((2 : ℂ)⁻¹ • (1 + matrixSign A)) ∧
      LinearMap.range ((2 : ℂ)⁻¹ • (1 + matrixSign A)).mulVecLin =
        Submodule.span ℂ (Set.range (X.submatrix id (e ∘ Sum.inr)).col) ∧
      Module.finrank ℂ (LinearMap.range ((2 : ℂ)⁻¹ • (1 + matrixSign A)).mulVecLin) =
        Fintype.card m := by
  have hdet := (isUnit_iff_isUnit_det X).mp hX
  set X₂ := X.submatrix id (e ∘ Sum.inr)
  set Y₂ := X⁻¹.submatrix (e ∘ Sum.inr) id
  have hinj : Function.Injective (e ∘ Sum.inr : m → n) := e.injective.comp Sum.inr_injective
  have hYX : Y₂ * X₂ = 1 := by
    change X⁻¹.submatrix (e ∘ Sum.inr) id * X.submatrix id (e ∘ Sum.inr) = 1
    rw [← submatrix_mul X⁻¹ X (e ∘ Sum.inr) id (e ∘ Sum.inr) Function.bijective_id,
      nonsing_inv_mul _ hdet, submatrix_one _ hinj]
  have hP : (2 : ℂ)⁻¹ • (1 + matrixSign A) = X₂ * Y₂ := by
    rw [matrixSign_conj_fromBlocks e hX h h₁ h₂]
    ext i j
    have h1 : (1 : Matrix n n ℂ) i j = ∑ x : l ⊕ m, X i (e x) * X⁻¹ (e x) j := by
      rw [← mul_nonsing_inv X hdet, mul_apply, ← e.sum_comp]
    simp only [smul_apply, add_apply, h1, mul_apply, reindex_apply, submatrix_apply, X₂, Y₂,
      Function.comp_apply, id]
    simp only [← e.sum_comp, e.symm_apply_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
    simp only [neg_apply, one_apply, zero_apply]
    simp only [mul_ite, mul_one, mul_zero, mul_neg, neg_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero,
      add_zero, zero_add, Finset.sum_neg_distrib, smul_eq_mul]
    ring
  refine ⟨hP, ?_, ?_, ?_⟩
  · rw [IsIdempotentElem, hP, Matrix.mul_assoc, ← Matrix.mul_assoc Y₂, hYX, Matrix.one_mul]
  · have hsurj : LinearMap.range Y₂.mulVecLin = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro v
      exact ⟨X₂ *ᵥ v, by rw [mulVecLin_apply, mulVec_mulVec, hYX, one_mulVec]⟩
    rw [hP, mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ hsurj, range_mulVecLin]
  · have hinjX : Function.Injective X₂.mulVecLin := fun v w hvw => by
      have := congrArg Y₂.mulVecLin hvw
      simpa [mulVecLin_apply, mulVec_mulVec, hYX] using this
    rw [hP, mulVecLin_mul, LinearMap.range_comp_of_range_eq_top, LinearMap.finrank_range_of_inj
      hinjX, Module.finrank_fintype_fun_eq_card]
    rw [LinearMap.range_eq_top]
    intro v
    exact ⟨X₂ *ᵥ v, by rw [mulVecLin_apply, mulVec_mulVec, hYX, one_mulVec]⟩

end Blocks

/-! ### Newton's iteration -/

/-- **Newton's iteration for the sign** ([golub2013matrix] (9.4.1)): `S₀ = A`,
`S_{k+1} = (S_k + S_k⁻¹)/2`. -/
noncomputable def newtonSignIterate (A : Matrix n n ℂ) : ℕ → Matrix n n ℂ
  | 0 => A
  | k + 1 => (2 : ℂ)⁻¹ • (newtonSignIterate A k + (newtonSignIterate A k)⁻¹)

@[simp]
theorem newtonSignIterate_zero (A : Matrix n n ℂ) : newtonSignIterate A 0 = A := rfl

theorem newtonSignIterate_succ (A : Matrix n n ℂ) (k : ℕ) :
    newtonSignIterate A (k + 1) =
      (2 : ℂ)⁻¹ • (newtonSignIterate A k + (newtonSignIterate A k)⁻¹) := rfl

/-- The scalar Newton map `r₀ = id`, `r_{k+1} = (r_k + 1/r_k)/2`. -/
private noncomputable def signFun : ℕ → ℂ → ℂ
  | 0 => fun z => z
  | k + 1 => fun z => (2 : ℂ)⁻¹ * (signFun k z + (signFun k z)⁻¹)

/-- `Re ((w + w⁻¹)/2)` has the sign of `Re w`. -/
private theorem re_half_add_inv (w : ℂ) :
    ((2 : ℂ)⁻¹ * (w + w⁻¹)).re = w.re / 2 * (1 + (Complex.normSq w)⁻¹) := by
  have h2 : ((2 : ℂ)⁻¹).re = 2⁻¹ := by norm_num
  have h2' : ((2 : ℂ)⁻¹).im = 0 := by norm_num
  rw [Complex.mul_re, h2, h2', Complex.add_re, Complex.inv_re]
  ring

private theorem signFun_spec (k : ℕ) {z : ℂ} (hz : z.re ≠ 0) :
    ContDiffAt ℂ ⊤ (signFun k) z ∧ (0 < (signFun k z).re ↔ 0 < z.re) ∧
      ((signFun k z).re < 0 ↔ z.re < 0) := by
  induction k with
  | zero => exact ⟨contDiffAt_id, Iff.rfl, Iff.rfl⟩
  | succ k ih =>
    obtain ⟨hd, hp, hn⟩ := ih
    have hre : (signFun k z).re ≠ 0 := by
      rcases lt_or_gt_of_ne hz with h | h
      · exact (hn.mpr h).ne
      · exact (hp.mpr h).ne'
    have hne : signFun k z ≠ 0 := fun h => hre (by rw [h, Complex.zero_re])
    have hsq : 0 < 1 + (Complex.normSq (signFun k z))⁻¹ := by
      have := Complex.normSq_nonneg (signFun k z)
      positivity
    refine ⟨contDiffAt_const.mul (hd.add (hd.inv hne)), ?_, ?_⟩
    · change 0 < ((2 : ℂ)⁻¹ * (signFun k z + (signFun k z)⁻¹)).re ↔ _
      rw [re_half_add_inv, ← hp]
      constructor
      · intro h
        by_contra h'
        have : (signFun k z).re / 2 * (1 + (Complex.normSq (signFun k z))⁻¹) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith [not_lt.mp h']) hsq.le
        linarith
      · intro h
        positivity
    · change ((2 : ℂ)⁻¹ * (signFun k z + (signFun k z)⁻¹)).re < 0 ↔ _
      rw [re_half_add_inv, ← hn]
      constructor
      · intro h
        by_contra h'
        have : 0 ≤ (signFun k z).re / 2 * (1 + (Complex.normSq (signFun k z))⁻¹) :=
          mul_nonneg (by linarith [not_lt.mp h']) hsq.le
        linarith
      · intro h
        exact mul_neg_of_neg_of_pos (by linarith) hsq

private theorem signFun_re_ne_zero (k : ℕ) {z : ℂ} (hz : z.re ≠ 0) : (signFun k z).re ≠ 0 := by
  have := signFun_spec k hz
  rcases lt_or_gt_of_ne hz with h | h
  · exact (this.2.2.mpr h).ne
  · exact (this.2.1.mpr h).ne'

private theorem signFun_ne_zero (k : ℕ) {z : ℂ} (hz : z.re ≠ 0) : signFun k z ≠ 0 :=
  fun h => signFun_re_ne_zero k hz (by rw [h, Complex.zero_re])

/-- Functions agreeing off the imaginary axis agree at a matrix without imaginary eigenvalues. -/
private theorem pfc_congr_of_re_ne_zero {A : Matrix n n ℂ} (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0)
    {f g : ℂ → ℂ} (h : ∀ z : ℂ, z.re ≠ 0 → f z = g z) : pfc f A = pfc g A := by
  refine pfc_congr fun μ hμ j _ => Filter.EventuallyEq.iteratedDeriv_eq j ?_
  have hopen : IsOpen {z : ℂ | z.re ≠ 0} := isOpen_ne_fun Complex.continuous_re continuous_const
  filter_upwards [hopen.mem_nhds (hA μ (mem_spectrum_of_mem_roots hμ))] with z hz
  exact h z hz

/-- Each Newton iterate is a rational function of `A`. -/
private theorem newtonSignIterate_eq_pfc {A : Matrix n n ℂ} (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0)
    (k : ℕ) : newtonSignIterate A k = pfc (signFun k) A := by
  have hI : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral _
  have hsmooth : ∀ k, ∀ μ ∈ (minpoly ℂ A).roots,
      ContDiffAt ℂ ((minpoly ℂ A).rootMultiplicity μ - 1 : ℕ) (signFun k) μ := fun k μ hμ =>
    (signFun_spec k (hA μ (mem_spectrum_of_mem_roots hμ))).1.of_le le_top
  have hne : ∀ k, ∀ μ ∈ (minpoly ℂ A).roots, signFun k μ ≠ 0 := fun k μ hμ =>
    signFun_ne_zero k (hA μ (mem_spectrum_of_mem_roots hμ))
  induction k with
  | zero => exact (pfc_id hI (IsAlgClosed.splits _)).symm
  | succ k ih =>
    have hinv := pfc_inv hI (IsAlgClosed.splits _) (hsmooth k) (hne k)
    rw [newtonSignIterate_succ, ih, nonsing_inv_eq_ringInverse, ← hinv.2,
      ← pfc_add (f := signFun k) (g := fun z => (signFun k z)⁻¹) (hsmooth k)
        fun μ hμ => (hsmooth k μ hμ).inv (hne k μ hμ), ← pfc_const_smul]
    rfl

/-- **The Newton iterates are nonsingular** ([golub2013matrix] §9.4.1): with no purely imaginary
eigenvalue, every `S_k` is invertible (so the iteration is well defined) and has no purely
imaginary eigenvalue; it is a rational function of `A`. -/
theorem isUnit_newtonSignIterate {A : Matrix n n ℂ} (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0) (k : ℕ) :
    IsUnit (newtonSignIterate A k) ∧ ∀ μ ∈ spectrum ℂ (newtonSignIterate A k), μ.re ≠ 0 := by
  have hI : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral _
  rw [newtonSignIterate_eq_pfc hA, ← spectrum.zero_notMem_iff ℂ,
    spectrum_pfc hI (IsAlgClosed.splits _)]
  refine ⟨?_, ?_⟩
  · rintro ⟨μ, hμ, h0⟩
    exact signFun_re_ne_zero k (hA μ hμ) (by rw [h0, Complex.zero_re])
  · rintro _ ⟨μ, hμ, rfl⟩
    exact signFun_re_ne_zero k (hA μ hμ)

/-- **The Newton iterates have the sign of `A`** ([golub2013matrix] §9.4.1): `sign(S_k) = sign(A)`,
since `z ↦ (z + 1/z)/2` preserves the sign of the real part. -/
theorem matrixSign_newtonSignIterate {A : Matrix n n ℂ} (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0)
    (k : ℕ) : matrixSign (newtonSignIterate A k) = matrixSign A := by
  have hI : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral _
  rw [newtonSignIterate_eq_pfc hA, matrixSign, matrixSign,
    ← pfc_comp hI (IsAlgClosed.splits _) (fun μ hμ =>
      (signFun_spec k (hA μ (mem_spectrum_of_mem_roots hμ))).1.of_le le_top) fun μ hμ =>
      contDiffAt_of_eventuallyEq_const
        (Complex.sign_re_eventuallyEq
          (signFun_re_ne_zero k (hA μ (mem_spectrum_of_mem_roots hμ)))) _]
  refine pfc_congr_of_re_ne_zero hA fun z hz => ?_
  have := signFun_spec k hz
  rcases lt_or_gt_of_ne hz with h | h
  · simp [Function.comp_apply, sign_neg h, sign_neg (this.2.2.mpr h)]
  · simp [Function.comp_apply, sign_pos h, sign_pos (this.2.1.mpr h)]

open scoped Matrix.Norms.L2Operator in
/-- **Quadratic convergence** ([golub2013matrix] §9.4.1, from (9.4.2)): in the spectral norm,
`‖S_{k+1} - sign(A)‖ ≤ ½ ‖S_k⁻¹‖ ‖S_k - sign(A)‖²`. -/
theorem norm_newtonSignIterate_sub_le {A : Matrix n n ℂ} (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0)
    (k : ℕ) :
    ‖newtonSignIterate A (k + 1) - matrixSign A‖ ≤
      2⁻¹ * ‖(newtonSignIterate A k)⁻¹‖ * ‖newtonSignIterate A k - matrixSign A‖ ^ 2 := by
  have hS : matrixSign A * matrixSign A = 1 := by rw [← sq, matrixSign_sq hA]
  have hc : Commute (newtonSignIterate A k) (matrixSign A) := by
    rw [newtonSignIterate_eq_pfc hA, matrixSign]
    exact commute_pfc_pfc A _ _
  have h := half_smul_add_inverse_sub_eq_of_commute (K := ℂ) (isUnit_newtonSignIterate hA k).1 hS hc
  rw [newtonSignIterate_succ, nonsing_inv_eq_ringInverse, h, norm_smul]
  have h2 : ‖(2 : ℂ)⁻¹‖ = 2⁻¹ := by norm_num
  rw [h2, mul_assoc]
  gcongr
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_pow_le' _ two_pos) (norm_nonneg _))

/-- `A` commutes with its Newton sign iterates. -/
theorem commute_newtonSignIterate (A : Matrix n n ℂ) (k : ℕ) :
    Commute A (newtonSignIterate A k) := by
  induction k with
  | zero => exact Commute.refl A
  | succ k ih => exact (ih.add_right (commute_nonsing_inv_right ih)).smul_right _

/-- A matrix with all eigenvalues in the open right half-plane has sign `1`. -/
theorem matrixSign_eq_one_of_re_pos {A : Matrix n n ℂ} (hA : ∀ μ ∈ spectrum ℂ A, 0 < μ.re) :
    matrixSign A = 1 := by
  rw [matrixSign, pfc_eq_algebraMap_of_eventuallyEq (c := 1) fun μ hμ => ?_, map_one]
  have := Complex.sign_re_eventuallyEq (hA μ hμ).ne'
  rwa [sign_pos (hA μ hμ), SignType.coe_one] at this

/-! ### Convergence of Newton's iteration -/

/-- The Cayley-type contraction `g(z) = (z - sign z)/(z + sign z)` of [golub2013matrix] §9.4.1. -/
private noncomputable def contraction (z : ℂ) : ℂ :=
  (z - ((SignType.sign z.re : SignType) : ℂ)) / (z + ((SignType.sign z.re : SignType) : ℂ))

private theorem sign_cases {z : ℂ} (hz : z.re ≠ 0) :
    (0 < z.re ∧ ((SignType.sign z.re : SignType) : ℂ) = 1) ∨
      (z.re < 0 ∧ ((SignType.sign z.re : SignType) : ℂ) = -1) := by
  rcases lt_or_gt_of_ne hz with h | h
  · exact Or.inr ⟨h, by simp [sign_neg h]⟩
  · exact Or.inl ⟨h, by simp [sign_pos h]⟩

private theorem add_sign_ne_zero {z : ℂ} (hz : z.re ≠ 0) :
    z + ((SignType.sign z.re : SignType) : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rcases sign_cases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] at this <;> simp at this <;> linarith

private theorem norm_contraction_lt_one {z : ℂ} (hz : z.re ≠ 0) : ‖contraction z‖ < 1 := by
  have hne := add_sign_ne_zero hz
  rw [contraction, norm_div, div_lt_one (norm_pos_iff.mpr hne), ← sq_lt_sq₀ (norm_nonneg _)
    (norm_nonneg _), Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  rcases sign_cases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;> simp <;> nlinarith

private theorem contDiffAt_contraction {μ : ℂ} (hμ : μ.re ≠ 0) :
    ContDiffAt ℂ ⊤ contraction μ := by
  have hev := Complex.sign_re_eventuallyEq hμ
  have hne := add_sign_ne_zero hμ
  refine ContDiffAt.congr_of_eventuallyEq (f := fun z =>
    (z - ((SignType.sign μ.re : SignType) : ℂ)) / (z + ((SignType.sign μ.re : SignType) : ℂ)))
    ((contDiffAt_id.sub contDiffAt_const).div (contDiffAt_id.add contDiffAt_const) hne) ?_
  filter_upwards [hev] with z hz
  simp only [contraction, hz]

/-- The closed form `r_k = sign · (1 + g^{2^k}) / (1 - g^{2^k})` of the scalar Newton map. -/
private theorem signFun_eq (k : ℕ) {z : ℂ} (hz : z.re ≠ 0) :
    signFun k z = ((SignType.sign z.re : SignType) : ℂ) * (1 + contraction z ^ 2 ^ k) *
      (1 - contraction z ^ 2 ^ k)⁻¹ := by
  have hg := norm_contraction_lt_one hz
  have hq : ∀ N : ℕ, 0 < N → 1 - contraction z ^ N ≠ 0 ∧ 1 + contraction z ^ N ≠ 0 :=
    fun N hN => by
      have h : ‖contraction z ^ N‖ < 1 := by
        rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hg hN.ne'
      refine ⟨fun h0 => ?_, fun h0 => ?_⟩
      · have h1 : contraction z ^ N = 1 := by linear_combination -h0
        rw [h1, norm_one] at h
        exact lt_irrefl _ h
      · have h1 : contraction z ^ N = -1 := by linear_combination h0
        rw [h1, norm_neg, norm_one] at h
        exact lt_irrefl _ h
  have hne := add_sign_ne_zero hz
  induction k with
  | zero =>
    obtain ⟨h1, h2⟩ := hq 1 one_pos
    rw [pow_zero, pow_one] at *
    change z = _
    rw [contraction] at h1 h2 ⊢
    rcases sign_cases hz with ⟨-, hs⟩ | ⟨-, hs⟩ <;> rw [hs] at hne h1 h2 ⊢ <;>
      field_simp <;> ring_nf
  | succ k ih =>
    obtain ⟨h1, h2⟩ := hq (2 ^ k) (by positivity)
    obtain ⟨h3, h4⟩ := hq (2 ^ (k + 1)) (by positivity)
    change (2 : ℂ)⁻¹ * (signFun k z + (signFun k z)⁻¹) = _
    rw [ih, pow_succ, pow_mul]
    rw [pow_succ, pow_mul] at h3 h4
    set q := contraction z ^ 2 ^ k
    rcases sign_cases hz with ⟨-, hs⟩ | ⟨-, hs⟩ <;> rw [hs] <;> field_simp <;> ring

/-- **Convergence of Newton's iteration** ([golub2013matrix] §9.4.1): with no purely imaginary
eigenvalue, `S_k → sign(A)`. With `G = g(A)`, `g(z) = (z - sign z)/(z + sign z)` of spectral radius
`< 1`, the iterates are `S_k = sign(A) (1 + G^{2^k}) (1 - G^{2^k})⁻¹`. -/
theorem tendsto_newtonSignIterate {A : Matrix n n ℂ} (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0) :
    Tendsto (newtonSignIterate A) atTop (𝓝 (matrixSign A)) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact tendsto_const_nhds.congr fun k => Subsingleton.elim _ _
  have hI : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral _
  have hs := IsAlgClosed.splits (minpoly ℂ A)
  have hsp : ∀ μ ∈ (minpoly ℂ A).roots, μ.re ≠ 0 := fun μ hμ =>
    hA μ (mem_spectrum_of_mem_roots hμ)
  set G := pfc contraction A
  set S := matrixSign A
  have hGpow : ∀ N : ℕ, pfc (fun z => contraction z ^ N) A = G ^ N := fun N => by
    have := pfc_comp hI hs (f := contraction) (g := fun w => w ^ N)
      (fun μ hμ => (contDiffAt_contraction (hsp μ hμ)).of_le le_top)
      (fun μ hμ => (contDiff_id.pow N).contDiffAt)
    rw [show (fun w : ℂ => w ^ N) ∘ contraction = fun z => contraction z ^ N from rfl] at this
    rw [this, pfc_pow (Algebra.IsIntegral.isIntegral _) (IsAlgClosed.splits _)]
  have hpowsm : ∀ N : ℕ, ∀ μ ∈ (minpoly ℂ A).roots, ContDiffAt ℂ ⊤ (fun z => contraction z ^ N) μ :=
    fun N μ hμ => (contDiffAt_contraction (hsp μ hμ)).pow N
  have hSk : ∀ k, newtonSignIterate A k = S * (1 + G ^ 2 ^ k) * Ring.inverse (1 - G ^ 2 ^ k) := by
    intro k
    have hg : ∀ μ ∈ (minpoly ℂ A).roots, 1 - contraction μ ^ 2 ^ k ≠ 0 := fun μ hμ h0 => by
      have h := norm_contraction_lt_one (hsp μ hμ)
      rw [sub_eq_zero] at h0
      have : ‖contraction μ ^ 2 ^ k‖ < 1 := by
        rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) h (by positivity)
      rw [← h0, norm_one] at this
      exact lt_irrefl _ this
    have hsm1 : ∀ μ ∈ (minpoly ℂ A).roots, ContDiffAt ℂ ⊤ (fun z => 1 - contraction z ^ 2 ^ k) μ :=
      fun μ hμ => contDiffAt_const.sub (hpowsm _ μ hμ)
    have hsm2 : ∀ μ ∈ (minpoly ℂ A).roots, ContDiffAt ℂ ⊤ (fun z => 1 + contraction z ^ 2 ^ k) μ :=
      fun μ hμ => contDiffAt_const.add (hpowsm _ μ hμ)
    have hsgn : ∀ μ ∈ (minpoly ℂ A).roots,
        ContDiffAt ℂ ⊤ (fun z => ((SignType.sign z.re : SignType) : ℂ)) μ := fun μ hμ =>
      contDiffAt_of_eventuallyEq_const (Complex.sign_re_eventuallyEq (hsp μ hμ)) _
    have hinv := pfc_inv hI hs (fun μ hμ => (hsm1 μ hμ).of_le le_top) hg
    rw [newtonSignIterate_eq_pfc hA, pfc_congr_of_re_ne_zero hA fun z hz => signFun_eq k hz]
    rw [show (fun z => ((SignType.sign z.re : SignType) : ℂ) * (1 + contraction z ^ 2 ^ k) *
        (1 - contraction z ^ 2 ^ k)⁻¹) = ((fun z => ((SignType.sign z.re : SignType) : ℂ)) *
          fun z => 1 + contraction z ^ 2 ^ k) * fun z => (1 - contraction z ^ 2 ^ k)⁻¹ from rfl,
      pfc_mul (f := (fun z : ℂ => ((SignType.sign z.re : SignType) : ℂ)) *
          fun z => 1 + contraction z ^ 2 ^ k) (g := fun z => (1 - contraction z ^ 2 ^ k)⁻¹) hI hs
        (fun μ hμ => ((hsgn μ hμ).mul (hsm2 μ hμ)).of_le le_top)
        (fun μ hμ => ((hsm1 μ hμ).inv (hg μ hμ)).of_le le_top),
      pfc_mul (f := fun z : ℂ => ((SignType.sign z.re : SignType) : ℂ))
        (g := fun z => 1 + contraction z ^ 2 ^ k) hI hs (fun μ hμ => (hsgn μ hμ).of_le le_top)
        (fun μ hμ => (hsm2 μ hμ).of_le le_top), hinv.2]
    rw [show (fun z => 1 + contraction z ^ 2 ^ k) = (fun _ => (1 : ℂ)) + fun z =>
        contraction z ^ 2 ^ k from rfl, show (fun z => 1 - contraction z ^ 2 ^ k) =
        (fun _ => (1 : ℂ)) - fun z => contraction z ^ 2 ^ k from rfl,
      pfc_add (f := fun _ => (1 : ℂ)) (g := fun z => contraction z ^ 2 ^ k)
        (fun μ _ => contDiffAt_const) (fun μ hμ => (hpowsm _ μ hμ).of_le le_top),
      pfc_sub (f := fun _ => (1 : ℂ)) (g := fun z => contraction z ^ 2 ^ k)
        (fun μ _ => contDiffAt_const) (fun μ hμ => (hpowsm _ μ hμ).of_le le_top),
      pfc_const hI hs, hGpow, map_one]
    rfl
  -- the powers of `G` tend to `0`
  let := Matrix.instL2OpNormedRing (𝕜 := ℂ) (n := n)
  let := Matrix.instL2OpNormedAlgebra (𝕜 := ℂ) (n := n)
  have hρ : spectralRadius ℂ G < 1 := by
    have hne : (spectrum ℂ G).Nonempty := spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ G
    obtain ⟨k, hk, hkr⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty hne
    rw [← hkr]
    rw [spectrum_pfc hI hs] at hk
    obtain ⟨μ, hμ, rfl⟩ := hk
    exact_mod_cast norm_contraction_lt_one (hA μ hμ)
  have hG : Tendsto (fun k : ℕ => G ^ 2 ^ k) atTop (𝓝 0) :=
    (tendsto_pow_of_spectralRadius_lt_one hρ).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hinv : Tendsto (fun k : ℕ => Ring.inverse (1 - G ^ 2 ^ k)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun k : ℕ => 1 - G ^ 2 ^ k) atTop
        (𝓝 ((1 : (Matrix n n ℂ)ˣ) : Matrix n n ℂ)) := by
      simpa using tendsto_const_nhds.sub hG
    have := (NormedRing.inverse_continuousAt (1 : (Matrix n n ℂ)ˣ)).tendsto.comp h1
    simpa [Function.comp_def] using this
  have hlim : Tendsto (fun k : ℕ => S * ((1 + G ^ 2 ^ k) * Ring.inverse (1 - G ^ 2 ^ k))) atTop
      (𝓝 (S * ((1 + 0) * 1))) := tendsto_const_nhds.mul ((tendsto_const_nhds.add hG).mul hinv)
  rw [add_zero, mul_one, mul_one] at hlim
  refine hlim.congr fun k => ?_
  rw [hSk, mul_assoc]

end Matrix
