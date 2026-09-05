import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Eigen.Perturbation
import NumlibSurface.SaadSparse.Common

/-!
# §1.11 Positive-definite matrices

Section 1.11 of Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003: the Hermitian/skew-Hermitian decomposition (1.49)–(1.52), Saad's non-symmetric
notion of a positive definite real matrix (1.48), Theorem 1.34, Bendixson's Theorem 1.35 and
the `B`-inner product (1.57).

Saad's "positive definite" is `Matrix.IsPositiveReal` here; the backbone counterpart is
`LinearMap.IsCoercive` of `Matrix.toEuclideanLin`, and the equivalence
`Matrix.isPositiveReal_iff_isCoercive` is what carries every result over.
-/

open Matrix Finset

open scoped SaadSparse ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-! ### Saad's positive definite matrices (1.48) -/

/-- Saad (1.48): a real matrix `A` is *positive definite* if `(A u, u) > 0` for every nonzero
`u ∈ ℝⁿ`. No symmetry is assumed. -/
def IsPositiveReal (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ u : Fin n → ℝ, u ≠ 0 → 0 < (A *ᵥ u) ⬝ᵥ u

/-- Saad §1.11: `A` is *symmetric positive definite* (SPD) if it is symmetric and satisfies
(1.48). -/
def IsSPD (A : Matrix (Fin n) (Fin n) ℝ) : Prop := A.IsSymm ∧ A.IsPositiveReal

/-- Saad's (1.48) is coercivity of the associated Euclidean operator, the backbone's
`LinearMap.IsCoercive`. -/
theorem isPositiveReal_iff_isCoercive (A : Matrix (Fin n) (Fin n) ℝ) :
    A.IsPositiveReal ↔ (toEuclideanLin A).IsCoercive := by
  rw [LinearMap.isCoercive_iff_forall_pos]
  constructor
  · intro h x hx
    have hx' : WithLp.ofLp x ≠ 0 := fun hc => hx (by ext i; exact congrFun hc i)
    simpa [SaadSparse.real_inner_apply_self, RCLike.re_to_real] using h _ hx'
  · intro h u hu
    have hu' : (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n)) ≠ 0 := fun hc =>
      hu (by ext i; exact congrFun (congrArg WithLp.ofLp hc) i)
    have hpos := h _ hu'
    rw [SaadSparse.real_inner_apply_self] at hpos
    simpa [RCLike.re_to_real] using hpos

/-- Saad's SPD is Mathlib's `Matrix.PosDef`. -/
theorem isSPD_iff_posDef (A : Matrix (Fin n) (Fin n) ℝ) : A.IsSPD ↔ A.PosDef := by
  rw [posDef_iff_dotProduct_mulVec, IsSPD]
  constructor
  · rintro ⟨hs, hp⟩
    exact ⟨isHermitian_iff_isSymm.mpr hs, fun x hx => by simpa [dotProduct_comm] using hp x hx⟩
  · rintro ⟨hh, hp⟩
    exact ⟨isHermitian_iff_isSymm.mp hh, fun x hx => by simpa [dotProduct_comm] using hp hx⟩

/-- A symmetric positive definite matrix has a symmetric coercive Euclidean operator; the
composite of `Matrix.isSPD_iff_posDef` and `Matrix.posDef_iff_isSymmetricCoercive`. -/
theorem IsSPD.isSymmetricCoercive {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSPD) :
    (toEuclideanLin A).IsSymmetricCoercive :=
  (posDef_iff_isSymmetricCoercive A).mp ((isSPD_iff_posDef A).mp hA)

/-! ### Hermitian and skew-Hermitian parts (1.49)–(1.51) -/

/-- Saad (1.50): the Hermitian part `H = (A + Aᴴ)/2` of a square matrix. -/
noncomputable def hermitianPart (A : Matrix (Fin n) (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  (2⁻¹ : 𝕜) • (A + Aᴴ)

/-- Saad (1.51): the matrix `S = (A - Aᴴ)/(2i)`, so that `A = H + iS`.  Over `ℝ` the division
by `2i` is meaningless, so this is stated over `ℂ` only. -/
noncomputable def skewPart (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (2 * Complex.I)⁻¹ • (A - Aᴴ)

@[simp]
theorem hermitianPart_apply (A : Matrix (Fin n) (Fin n) 𝕜) (i j : Fin n) :
    hermitianPart A i j = (2⁻¹ : 𝕜) * (A i j + starRingEnd 𝕜 (A j i)) := rfl

@[simp]
theorem skewPart_apply (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    skewPart A i j = (2 * Complex.I)⁻¹ * (A i j - starRingEnd ℂ (A j i)) := rfl

/-- Saad (1.52): the Hermitian part is Hermitian. -/
theorem hermitianPart_isHermitian (A : Matrix (Fin n) (Fin n) 𝕜) :
    (hermitianPart A).IsHermitian := by
  change ((2⁻¹ : 𝕜) • (A + Aᴴ))ᴴ = (2⁻¹ : 𝕜) • (A + Aᴴ)
  rw [conjTranspose_smul, show star (2⁻¹ : 𝕜) = 2⁻¹ by simp, conjTranspose_add,
    conjTranspose_conjTranspose, add_comm Aᴴ A]

/-- Saad's `S = (A - Aᴴ)/(2i)` is the Hermitian part of `-i A`. -/
theorem skewPart_eq_hermitianPart (A : Matrix (Fin n) (Fin n) ℂ) :
    skewPart A = hermitianPart ((-Complex.I) • A) := by
  ext i j
  simp only [skewPart_apply, hermitianPart_apply, smul_apply, smul_eq_mul, map_mul, map_neg,
    Complex.conj_I, neg_neg]
  rw [mul_inv, Complex.inv_I]
  ring

/-- The Hermitian part of `-i A` is Saad's `S`. -/
theorem hermitianPart_neg_I_smul (A : Matrix (Fin n) (Fin n) ℂ) :
    hermitianPart ((-Complex.I) • A) = skewPart A :=
  (skewPart_eq_hermitianPart A).symm

/-- Saad (1.52): `S = (A - Aᴴ)/(2i)` is Hermitian. -/
theorem skewPart_isHermitian (A : Matrix (Fin n) (Fin n) ℂ) : (skewPart A).IsHermitian := by
  rw [skewPart_eq_hermitianPart]
  exact hermitianPart_isHermitian _

/-- `i S = (A - Aᴴ)/2` is the skew-Hermitian part of `A`. -/
theorem I_smul_skewPart (A : Matrix (Fin n) (Fin n) ℂ) :
    Complex.I • skewPart A = (2⁻¹ : ℂ) • (A - Aᴴ) := by
  rw [skewPart, smul_smul]
  congr 1
  rw [mul_inv, ← mul_assoc, mul_comm Complex.I (2⁻¹ : ℂ), mul_assoc,
    mul_inv_cancel₀ Complex.I_ne_zero, mul_one]

/-- Saad (1.49): `A = H + iS`. -/
theorem eq_hermitianPart_add_I_smul_skewPart (A : Matrix (Fin n) (Fin n) ℂ) :
    A = hermitianPart A + Complex.I • skewPart A := by
  rw [I_smul_skewPart, hermitianPart, ← smul_add,
    show A + Aᴴ + (A - Aᴴ) = (2 : ℂ) • A by module, smul_smul,
    inv_mul_cancel₀ (two_ne_zero' ℂ), one_smul]

/-- Saad §1.11: for real `A` and real `u`, `(A u, u) = (H u, u)`. -/
theorem mulVec_dotProduct_eq_hermitianPart (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    (A *ᵥ u) ⬝ᵥ u = (hermitianPart A *ᵥ u) ⬝ᵥ u := by
  have hT : (Aᵀ *ᵥ u) ⬝ᵥ u = (A *ᵥ u) ⬝ᵥ u := by
    rw [dotProduct_comm, dotProduct_mulVec, vecMul_transpose]
  have hH : hermitianPart A = (2⁻¹ : ℝ) • (A + Aᵀ) := by
    ext i j; simp [hermitianPart_apply]
  rw [hH, smul_mulVec, smul_dotProduct, add_mulVec, add_dotProduct, hT, smul_eq_mul]
  ring

/-- The real part of the quadratic form of `A` is that of its Hermitian part; the matrix form of
the backbone's `ContinuousLinearMap.re_inner_hermitianPart_apply`. -/
theorem re_inner_hermitianPart (A : Matrix (Fin n) (Fin n) 𝕜) (x : EuclideanSpace 𝕜 (Fin n)) :
    RCLike.re (inner 𝕜 (hermitianPart A ⬝ x) x) = RCLike.re (inner 𝕜 (A ⬝ x) x) := by
  have hH : toEuclideanLin (hermitianPart A) =
      (2⁻¹ : 𝕜) • (toEuclideanLin A + LinearMap.adjoint (toEuclideanLin A)) := by
    rw [hermitianPart, map_smul, map_add, toEuclideanLin_conjTranspose]
  have hadj : inner 𝕜 (LinearMap.adjoint (toEuclideanLin A) x) x
      = starRingEnd 𝕜 (inner 𝕜 (toEuclideanLin A x) x) := by
    rw [LinearMap.adjoint_inner_left, inner_conj_symm]
  have key : inner 𝕜 (toEuclideanLin (hermitianPart A) x) x
      = (2⁻¹ : 𝕜) * (inner 𝕜 (toEuclideanLin A x) x
        + starRingEnd 𝕜 (inner 𝕜 (toEuclideanLin A x) x)) := by
    rw [hH]
    simp only [LinearMap.smul_apply, LinearMap.add_apply, inner_smul_left, inner_add_left, hadj,
      map_inv₀, RCLike.conj_ofNat]
  change RCLike.re (inner 𝕜 (toEuclideanLin (hermitianPart A) x) x) = _
  rw [key, RCLike.add_conj, ← mul_assoc, show (2⁻¹ : 𝕜) * 2 = 1 by norm_num, one_mul,
    RCLike.ofReal_re]

/-! ### The energy (`B`-) inner product (1.57) -/

/-- Saad (1.57): the `B`-inner product `(x, y)_B = (B x, y)` for a symmetric positive definite
`B` (in Mathlib's convention, `inner 𝕜 y (B x)`). -/
noncomputable def energyInner (B : Matrix (Fin n) (Fin n) 𝕜) (x y : EuclideanSpace 𝕜 (Fin n)) :
    𝕜 := inner 𝕜 y (B ⬝ x)

/-- Saad §1.11: `A` is Hermitian with respect to the `B`-inner product. -/
def IsSelfAdjointWrt (B A : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  ∀ x y : EuclideanSpace 𝕜 (Fin n), energyInner B (A ⬝ x) y = energyInner B x (A ⬝ y)

/-- The surface's (1.57) is the conjugate of the backbone's `energyInner`; over `ℝ` they
agree. -/
theorem energyInner_eq (B : Matrix (Fin n) (Fin n) 𝕜) (x y : EuclideanSpace 𝕜 (Fin n)) :
    energyInner B x y = starRingEnd 𝕜 (_root_.energyInner (toEuclideanLin B) x y) := by
  rw [energyInner, _root_.energyInner, inner_conj_symm]

/-- Over `ℝ` the surface's (1.57) is literally the backbone's `energyInner`. -/
theorem real_energyInner_eq (B : Matrix (Fin n) (Fin n) ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    energyInner B x y = _root_.energyInner (toEuclideanLin B) x y := by
  rw [energyInner_eq]; simp

section BInner

variable {B : Matrix (Fin n) (Fin n) ℝ}

/-- (1.57) is symmetric (Saad §1.4, axiom (i) over `ℝ`). -/
theorem energyInner_comm (hB : B.IsSPD) (x y : EuclideanSpace ℝ (Fin n)) :
    energyInner B x y = energyInner B y x := by
  rw [energyInner, energyInner, real_inner_comm (B ⬝ x) y,
    hB.isSymmetricCoercive.isSymmetric x y]

/-- (1.57) is additive in its first argument. -/
theorem energyInner_add_left (x y z : EuclideanSpace ℝ (Fin n)) :
    energyInner B (x + y) z = energyInner B x z + energyInner B y z := by
  simp [energyInner, inner_add_right]

/-- (1.57) is homogeneous in its first argument. -/
theorem energyInner_smul_left (c : ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    energyInner B (c • x) y = c * energyInner B x y := by
  simp [energyInner, inner_smul_right]

/-- (1.57) is positive definite: `(x, x)_B > 0` for `x ≠ 0`. -/
theorem energyInner_self_pos (hB : B.IsSPD) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    0 < energyInner B x x := by
  have h := hB.isSymmetricCoercive.isCoercive.inner_self_pos hx
  rw [energyInner, real_inner_comm]
  simpa [RCLike.re_to_real] using h

/-- (1.57) vanishes on the diagonal only at `0`. -/
theorem energyInner_self_eq_zero_iff (hB : B.IsSPD) {x : EuclideanSpace ℝ (Fin n)} :
    energyInner B x x = 0 ↔ x = 0 := by
  refine ⟨fun h => by_contra fun hx => ?_, fun h => by simp [h, energyInner]⟩
  exact absurd h (energyInner_self_pos hB hx).ne'

/-! ### `B`-self-adjointness (Exercise P-1.18) -/

private theorem mulVec_dotProduct_transpose (M : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) :
    (M *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (Mᵀ *ᵥ v) := by
  rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

/-- `A` is self-adjoint for the `B`-inner product as soon as `B A` is symmetric. -/
theorem isSelfAdjointWrt_of_isSymm_mul {A : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm)
    (h : (B * A).IsSymm) : B.IsSelfAdjointWrt A := by
  intro x y
  have key : ∀ u v : Fin n → ℝ, (B *ᵥ (A *ᵥ u)) ⬝ᵥ v = (B *ᵥ u) ⬝ᵥ (A *ᵥ v) := by
    intro u v
    rw [mulVec_mulVec, mulVec_dotProduct_transpose, h,
      mulVec_dotProduct_transpose B u (A *ᵥ v), hB, mulVec_mulVec]
  simp only [energyInner, SaadSparse.real_inner_toEuclideanLin', SaadSparse.ofLp_toEuclideanLin]
  exact key _ _

/-- With `C` symmetric and `B` symmetric positive definite, `A = B⁻¹ C` is self-adjoint for the
`B`-inner product (Saad §1.11; Exercise P-1.18). -/
theorem isSelfAdjointWrt_inv_mul {C : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSPD) (hBu : IsUnit B)
    (hC : C.IsSymm) : B.IsSelfAdjointWrt (B⁻¹ * C) := by
  refine isSelfAdjointWrt_of_isSymm_mul hB.1 ?_
  rw [← mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det B).mp hBu), one_mul]
  exact hC

/-- With `C` symmetric and `B` symmetric, `A = C B` is self-adjoint for the `B`-inner product
(Saad §1.11; Exercise P-1.18). -/
theorem isSelfAdjointWrt_mul {C : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) (hC : C.IsSymm) :
    B.IsSelfAdjointWrt (C * B) := by
  refine isSelfAdjointWrt_of_isSymm_mul hB ?_
  change (B * (C * B))ᵀ = B * (C * B)
  rw [transpose_mul, transpose_mul, hB, hC]
  exact mul_assoc B C B

end BInner

end Matrix

namespace SaadSparse.Ch01

open Matrix

variable {n : ℕ}

/-! ### Theorem 1.34 -/

/-- **Theorem 1.34**.  A real positive definite matrix (Saad (1.48)) is nonsingular, and there is
an `α > 0` with `(A u, u) ≥ α ‖u‖₂²` for every `u ∈ ℝⁿ`. -/
theorem theorem_1_34 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsPositiveReal) :
    IsUnit A ∧ ∃ α > 0, ∀ u : Fin n → ℝ, α * (u ⬝ᵥ u) ≤ (A *ᵥ u) ⬝ᵥ u := by
  obtain ⟨c, hc, hcA⟩ := (isPositiveReal_iff_isCoercive A).mp hA
  refine ⟨?_, c, hc, fun u => ?_⟩
  · refine mulVec_injective_iff_isUnit.mp fun u v huv => ?_
    have hinj : (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n)) = WithLp.toLp 2 v :=
      LinearMap.IsCoercive.injective ⟨c, hc, hcA⟩ (by ext i; exact congrFun huv i)
    ext i
    exact congrFun (congrArg WithLp.ofLp hinj) i
  · have h := hcA (WithLp.toLp 2 u)
    rw [SaadSparse.real_inner_apply_self] at h
    rw [← SaadSparse.real_norm_sq_eq_dotProduct (WithLp.toLp 2 u)]
    simpa [RCLike.re_to_real] using h

/-- **Theorem 1.34**, with the book's constant `α = λ_min(H)`, `H` the Hermitian part of `A`. -/
theorem theorem_1_34' [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    SaadSparse.lambdaMin (hermitianPart_isHermitian A) * (u ⬝ᵥ u) ≤ (A *ᵥ u) ⬝ᵥ u := by
  have hb := SaadSparse.isSymmetricBoundedBy_toEuclideanLin (hermitianPart_isHermitian A)
  have h := hb.le_re_inner (WithLp.toLp 2 u)
  rw [SaadSparse.real_inner_apply_self] at h
  rw [mulVec_dotProduct_eq_hermitianPart, ← SaadSparse.real_norm_sq_eq_dotProduct]
  simpa [RCLike.re_to_real] using h

/-- **Theorem 1.34**: a real positive definite matrix is coercive with constant `λ_min(H)`. -/
theorem isCoerciveWith_lambdaMin [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) :
    (toEuclideanLin A).IsCoerciveWith (SaadSparse.lambdaMin (hermitianPart_isHermitian A)) := by
  intro x
  have h := theorem_1_34' A (WithLp.ofLp x)
  rw [SaadSparse.real_inner_apply_self]
  simpa [RCLike.re_to_real, SaadSparse.real_norm_sq_eq_dotProduct] using h

/-! ### Theorem 1.35 (Bendixson) -/

/-- **Theorem 1.35** (Bendixson), real part: every eigenvalue `μ` of a complex matrix `A`
satisfies `λ_min(H) ≤ Re μ ≤ λ_max(H)` with `H` the Hermitian part of `A`. -/
theorem theorem_1_35_re [NeZero n] {A : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    μ.re ∈ Set.Icc (SaadSparse.lambdaMin (hermitianPart_isHermitian A))
      (SaadSparse.lambdaMax (hermitianPart_isHermitian A)) :=
  re_hasEigenvalue_mem_Icc_of_symmetricPart
    (SaadSparse.isSymmetricBoundedBy_toEuclideanLin (hermitianPart_isHermitian A))
    (fun x => re_inner_hermitianPart A x) ((hasEigenvalue_toEuclideanLin_iff A μ).mpr hμ)

/-- The eigenvalues of `c • A` are `c` times those of `A`. -/
private theorem hasEigenvalue_smul {c : ℂ} {A : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ}
    (h : Module.End.HasEigenvalue (toEuclideanLin A) μ) :
    Module.End.HasEigenvalue (toEuclideanLin (c • A)) (c * μ) := by
  obtain ⟨v, hv, hv0⟩ := h.exists_hasEigenvector
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv0⟩
  rw [Module.End.mem_eigenspace_iff]
  have hAv : toEuclideanLin A v = μ • v := Module.End.mem_eigenspace_iff.mp hv
  rw [map_smul, LinearMap.smul_apply, hAv, smul_smul]

/-- **Theorem 1.35** (Bendixson), imaginary part: every eigenvalue `μ` of a complex matrix `A`
satisfies `λ_min(S) ≤ Im μ ≤ λ_max(S)` with `S = (A - Aᴴ)/(2i)`. -/
theorem theorem_1_35_im [NeZero n] {A : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    μ.im ∈ Set.Icc (SaadSparse.lambdaMin (skewPart_isHermitian A))
      (SaadSparse.lambdaMax (skewPart_isHermitian A)) := by
  have hev : Module.End.HasEigenvalue (toEuclideanLin ((-Complex.I) • A)) (-Complex.I * μ) :=
    hasEigenvalue_smul ((hasEigenvalue_toEuclideanLin_iff A μ).mpr hμ)
  have hHA : ∀ x : EuclideanSpace ℂ (Fin n),
      RCLike.re (inner ℂ (skewPart A ⬝ x) x)
        = RCLike.re (inner ℂ (((-Complex.I) • A) ⬝ x) x) := by
    intro x
    rw [skewPart_eq_hermitianPart]
    exact re_inner_hermitianPart _ x
  have h := re_hasEigenvalue_mem_Icc_of_symmetricPart
    (SaadSparse.isSymmetricBoundedBy_toEuclideanLin (skewPart_isHermitian A)) hHA hev
  simpa using h

/-- **Theorem 1.35** (Bendixson): every eigenvalue of `A` lies in the rectangle
`[λ_min(H), λ_max(H)] × [λ_min(S), λ_max(S)]`. -/
theorem theorem_1_35 [NeZero n] {A : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    SaadSparse.lambdaMin (hermitianPart_isHermitian A) ≤ μ.re ∧
      μ.re ≤ SaadSparse.lambdaMax (hermitianPart_isHermitian A) ∧
      SaadSparse.lambdaMin (skewPart_isHermitian A) ≤ μ.im ∧
      μ.im ≤ SaadSparse.lambdaMax (skewPart_isHermitian A) :=
  ⟨(theorem_1_35_re hμ).1, (theorem_1_35_re hμ).2, (theorem_1_35_im hμ).1, (theorem_1_35_im hμ).2⟩

end SaadSparse.Ch01
