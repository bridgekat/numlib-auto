import Numlib.Surface.SaadSparse.Ch01.Projectors
import Numlib.Surface.SaadSparse.Ch01.PositiveDefinite

/-!
# §5.1–§5.2 Projection methods

Sections 5.1 and 5.2 of Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003: the general projection step (5.1)–(5.7), the nonsingularity of `WᵀAV`
(Proposition 5.1), the optimality characterizations (Propositions 5.2–5.5), the operators
`P_K`, `Q_K^L`, `A_m` of §5.2.3, Proposition 5.6 and the error identity behind Theorem 5.7.

The book's condition (5.5)–(5.6) is `SaadSparse.Ch05.IsProjectionApprox`; it is the backbone's
`IsPetrovGalerkin` for `Matrix.toEuclideanLin A` (`isProjectionApprox_iff`), so that every
statement below specializes a result of `Numlib/LinearSolve/Projection/`.

Left open here: the matrix reading of Theorem 5.7 (R-5.14 of the plan), which needs the
compression of an operator in an orthonormal basis; and the additive/multiplicative procedures
of §5.4 (phase 2 of the backbone, `tracker/backbone.md` §2.4.4).
-/

open Matrix Module Submodule Finset
open scoped SaadSparse

namespace SaadSparse.Ch05

variable {n m : ℕ}

/-- Saad Chapter 5 works in `ℝⁿ`. -/
local notation "E" n => EuclideanSpace ℝ (Fin n)

/-! ### The projection step (5.1)–(5.7) -/

/-- Saad (5.5)–(5.6): `x` is the approximation produced by a projection method onto `K`
orthogonally to `L`, starting from `x₀`. -/
def IsProjectionApprox (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : E n)
    (K L : Submodule ℝ (E n)) (x : E n) : Prop :=
  x - x₀ ∈ K ∧ ∀ w ∈ L, inner ℝ w (b - (A ⬝ x)) = 0

variable {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ x : E n} {K L : Submodule ℝ (E n)}

/-- Saad (5.5)–(5.6) is the backbone's Petrov–Galerkin condition. -/
theorem isProjectionApprox_iff :
    IsProjectionApprox A b x₀ K L x ↔ IsPetrovGalerkin (toEuclideanLin A) b x₀ K L x :=
  ⟨fun h => ⟨h.1, (Submodule.mem_orthogonal _ _).2 h.2⟩,
    fun h => ⟨h.mem, (Submodule.mem_orthogonal _ _).1 h.orth⟩⟩

/-- Saad (5.7)/Algorithm 5.1: the projection step `x ↦ x + V (WᵀAV)⁻¹ Wᵀ r`. -/
noncomputable def projStep (A : Matrix (Fin n) (Fin n) ℝ) (b : E n)
    (V W : Matrix (Fin n) (Fin m) ℝ) (x : E n) : E n :=
  x + ((V * (Wᵀ * A * V)⁻¹ * Wᵀ) ⬝ (b - (A ⬝ x)))

section Bases

variable {V W : Matrix (Fin n) (Fin m) ℝ}

/-- Over `ℝ` the conjugate transpose is the transpose. -/
theorem conjTranspose_eq_transpose (V : Matrix (Fin n) (Fin m) ℝ) : Vᴴ = Vᵀ :=
  conjTranspose_eq_transpose_of_trivial V

/-- The matrix `(⟪w_i, A v_j⟫)` of the backbone's bases form is `Wᵀ A V`. -/
theorem crossGram_matrix (A : Matrix (Fin n) (Fin n) ℝ) (V W : Matrix (Fin n) (Fin m) ℝ) :
    (Matrix.of fun i j => inner ℝ (W.cols i) (A ⬝ V.cols j)) = Wᵀ * A * V := by
  ext i j
  rw [Matrix.of_apply, SaadSparse.real_inner_toEuclideanLin', Matrix.mul_assoc, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.transpose_apply, ofLp_cols_apply, mul_comm]
  rfl

/-- `x₀ + V y` in the book's notation is the backbone's `x₀ + ∑ j y j • v j`. -/
theorem add_toEuclideanLin_eq (V : Matrix (Fin n) (Fin m) ℝ) (x₀ : E n) (y : Fin m → ℝ) :
    x₀ + (V ⬝ (WithLp.toLp 2 y : E m)) = x₀ + ∑ j, y j • V.cols j := by
  rw [toEuclideanLin_apply_eq_sum]
  rfl

/-- Saad (5.7): `x̃ = x₀ + V y` satisfies the Petrov–Galerkin condition iff
`(WᵀAV) y = Wᵀ r₀`. -/
theorem isProjectionApprox_add_iff (hV : V.IsBasisOf K) (hW : W.IsBasisOf L) (y : Fin m → ℝ) :
    IsProjectionApprox A b x₀ K L (x₀ + (V ⬝ (WithLp.toLp 2 y : E m))) ↔
      (Wᵀ * A * V) *ᵥ y = Wᵀ *ᵥ WithLp.ofLp (b - (A ⬝ x₀)) := by
  have hbasis := isPetrovGalerkin_iff_mulVec (A := toEuclideanLin A) (b := b) (x₀ := x₀)
    hV.toBasis hW.toBasis y
  simp only [IsBasisOf.coe_toBasis_apply] at hbasis
  rw [isProjectionApprox_iff, add_toEuclideanLin_eq, hbasis, crossGram_matrix]
  constructor
  · intro h
    rw [h, ← conjTranspose_eq_transpose, conjTranspose_mulVec_eq_inner]
  · intro h
    rw [h, ← conjTranspose_eq_transpose, conjTranspose_mulVec_eq_inner]

/-- Saad §5.1: `WᵀAV` is nonsingular iff no nonzero vector `u` of `K` has `A u ⟂ L`. -/
theorem isUnit_transpose_mul_mul_iff (hV : V.IsBasisOf K) (hW : W.IsBasisOf L) :
    IsUnit (Wᵀ * A * V) ↔ ∀ u ∈ K, (A ⬝ u) ∈ Lᗮ → u = 0 := by
  have hzero : ∀ y : Fin m → ℝ, (Wᵀ * A * V) *ᵥ y = 0 ↔
      (A ⬝ (V ⬝ (WithLp.toLp 2 y : E m))) ∈ Lᗮ := by
    intro y
    rw [← Ch01.conjTranspose_mulVec_eq_zero_iff hW]
    have h1 : WithLp.ofLp (A ⬝ (V ⬝ (WithLp.toLp 2 y : E m))) = A *ᵥ (V *ᵥ y) := rfl
    rw [h1, mulVec_mulVec, mulVec_mulVec, conjTranspose_eq_transpose]
  have hmemK : ∀ y : Fin m → ℝ, (V ⬝ (WithLp.toLp 2 y : E m)) ∈ K :=
    fun y => hV.span_eq ▸ Ch01.toEuclideanLin_mem_span V _
  constructor
  · intro h u huK huL
    rw [← hV.span_eq] at huK
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 huK
    have hVc : (V ⬝ (WithLp.toLp 2 c : E m)) = ∑ k, c k • V.cols k :=
      toEuclideanLin_apply_eq_sum V c
    have h0 : (Wᵀ * A * V) *ᵥ c = 0 := (hzero c).mpr (by rw [hVc]; exact huL)
    have hc : c = 0 := by
      have hinj := mulVec_injective_iff_isUnit.mpr h
      exact hinj (a₁ := c) (a₂ := 0) (by rw [h0, mulVec_zero])
    rw [hc]
    simp
  · intro hcond
    refine mulVec_injective_iff_isUnit.mp fun u v huv => ?_
    have hsub : (Wᵀ * A * V) *ᵥ (u - v) = 0 := by rw [mulVec_sub, huv, sub_self]
    have hzeroV := hcond _ (hmemK (u - v)) ((hzero (u - v)).mp hsub)
    rw [toEuclideanLin_apply_eq_sum] at hzeroV
    have hli := Fintype.linearIndependent_iff.mp hV.linearIndependent (u - v) hzeroV
    funext i
    have hi := hli i
    rwa [Pi.sub_apply, sub_eq_zero] at hi

end Bases

/-! ### Proposition 5.1 -/

/-- Saad, Proposition 5.1 (i): for positive real `A` and `L = K`, the projected system is
nonsingular; equivalently the Galerkin approximation exists and is unique. -/
theorem prop_5_1_i (hA : A.IsPositiveReal) (K : Submodule ℝ (E n)) (b x₀ : E n) :
    ∃! x, IsProjectionApprox A b x₀ K K x := by
  have hc : (toEuclideanLin A).IsCoercive := (Matrix.isPositiveReal_iff_isCoercive A).mp hA
  obtain ⟨x, hx, huniq⟩ := existsUnique_isGalerkin_of_isCoercive (A := toEuclideanLin A) b x₀ K hc
  exact ⟨x, isProjectionApprox_iff.mpr hx, fun y hy => huniq y (isProjectionApprox_iff.mp hy)⟩

/-- `toEuclideanLin A` is injective when `A` is nonsingular. -/
theorem injective_toEuclideanLin (hA : IsUnit A) : Function.Injective (toEuclideanLin A) := by
  intro u v huv
  have h1 : A *ᵥ WithLp.ofLp u = A *ᵥ WithLp.ofLp v := congrArg WithLp.ofLp huv
  simpa using congrArg (WithLp.toLp 2) (mulVec_injective_iff_isUnit.mpr hA h1)

/-- Saad, Proposition 5.1 (ii): for nonsingular `A` and `L = A K`, the projected system is
nonsingular. -/
theorem prop_5_1_ii (hA : IsUnit A) (K : Submodule ℝ (E n)) (b x₀ : E n) :
    ∃! x, IsProjectionApprox A b x₀ K (K.map (toEuclideanLin A)) x := by
  have hinj : Set.InjOn (toEuclideanLin A) K :=
    fun u _ v _ huv => injective_toEuclideanLin hA huv
  obtain ⟨x, hx, huniq⟩ := existsUnique_isMinRes_of_injOn (A := toEuclideanLin A) b x₀ K hinj
  refine ⟨x, isProjectionApprox_iff.mpr hx.isPetrovGalerkin, fun y hy => ?_⟩
  exact huniq y (IsMinRes.iff_isPetrovGalerkin.mpr (isProjectionApprox_iff.mp hy))

/-- Saad §5.1: `A` symmetric ⇒ the projected matrix `VᵀAV` is symmetric. -/
theorem isSymm_transpose_mul_mul (hA : A.IsSymm) (V : Matrix (Fin n) (Fin m) ℝ) :
    (Vᵀ * A * V).IsSymm := by
  unfold Matrix.IsSymm
  rw [transpose_mul, transpose_mul, transpose_transpose, hA, Matrix.mul_assoc]

/-- Saad §5.1: `A` SPD ⇒ the projected matrix `VᵀAV` is SPD. -/
theorem posDef_transpose_mul_mul {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {V : Matrix (Fin n) (Fin m) ℝ} (hV : Function.Injective V.mulVec) :
    (Vᵀ * A * V).PosDef := by
  have h := hA.conjTranspose_mul_mul_same hV
  rwa [conjTranspose_eq_transpose] at h

/-! ### Propositions 5.2–5.5 -/

/-- Saad §5.3: the error functional `E(x) = (A(x* - x), x* - x)^{1/2}`. -/
noncomputable def E_A (A : Matrix (Fin n) (Fin n) ℝ) (xstar x : E n) : ℝ :=
  Real.sqrt (inner ℝ (A ⬝ (xstar - x)) (xstar - x))

/-- Saad §5.3: the residual functional `R(x) = ‖b - A x‖₂`. -/
noncomputable def R_A (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) : ℝ := ‖b - (A ⬝ x)‖

/-- `E(x)` is the backbone's energy norm of the error. -/
theorem E_A_eq_energyNorm (A : Matrix (Fin n) (Fin n) ℝ) (xstar x : E n) :
    E_A A xstar x = energyNorm (toEuclideanLin A) (xstar - x) := rfl

/-- Saad, Proposition 5.2: for SPD `A` and `L = K`, the projection approximation is exactly the
minimizer of the energy norm of the error over `x₀ + K`. -/
theorem prop_5_2 (hA : A.PosDef) {xstar : E n} (hstar : (A ⬝ xstar) = b) :
    IsProjectionApprox A b x₀ K K x ↔
      (x - x₀ ∈ K ∧ ∀ y, y - x₀ ∈ K → E_A A xstar x ≤ E_A A xstar y) := by
  have hsc : (toEuclideanLin A).IsSymmetricCoercive :=
    (Matrix.posDef_iff_isSymmetricCoercive A).mp hA
  rw [isProjectionApprox_iff]
  simpa only [E_A_eq_energyNorm] using
    IsGalerkin.iff_energyNorm_min (A := toEuclideanLin A) (b := b) (x₀ := x₀) (K := K) (x := x)
      (xstar := xstar) hsc hstar

/-- Saad, Proposition 5.3: for `L = A K` the projection approximation is exactly the minimizer of
the residual norm over `x₀ + K`. -/
theorem prop_5_3 :
    IsProjectionApprox A b x₀ K (K.map (toEuclideanLin A)) x ↔
      (x - x₀ ∈ K ∧ ∀ y, y - x₀ ∈ K → R_A A b x ≤ R_A A b y) := by
  rw [isProjectionApprox_iff, ← IsMinRes.iff_isPetrovGalerkin]
  exact ⟨fun h => ⟨h.mem, h.min⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Saad, Proposition 5.4: for `L = A K` the residual is `(I - P) r₀` with `P` the orthogonal
projector onto `A K`. -/
theorem prop_5_4 (hx : IsProjectionApprox A b x₀ K (K.map (toEuclideanLin A)) x) :
    b - (A ⬝ x) =
      (b - (A ⬝ x₀)) - (K.map (toEuclideanLin A)).starProjection (b - (A ⬝ x₀)) :=
  (IsMinRes.iff_isPetrovGalerkin.mpr (isProjectionApprox_iff.mp hx)).residual_eq

/-- Saad §5.2.2: the residual norm does not increase. -/
theorem norm_residual_le (hx : IsProjectionApprox A b x₀ K (K.map (toEuclideanLin A)) x) :
    ‖b - (A ⬝ x)‖ ≤ ‖b - (A ⬝ x₀)‖ :=
  IsMinRes.norm_residual_le_norm_residual_zero
    (IsMinRes.iff_isPetrovGalerkin.mpr (isProjectionApprox_iff.mp hx))

/-- Saad, Proposition 5.5 (characterization): for `L = K` the error `x* - x̃` is `A`-orthogonal
to `K`. -/
theorem prop_5_5_char {xstar : E n} (hstar : (A ⬝ xstar) = b)
    (hx : IsProjectionApprox A b x₀ K K x) :
    x - x₀ ∈ K ∧ ∀ w ∈ K, A.energyInner (xstar - x) w = 0 := by
  refine ⟨hx.1, fun w hw => ?_⟩
  have h : A.energyInner (xstar - x) w = inner ℝ w (A ⬝ (xstar - x)) := rfl
  rw [h, map_sub, hstar]
  simpa using hx.2 w hw

/-- Saad, Proposition 5.5: the energy norm of the error does not increase. -/
theorem energyNorm_error_le (hA : A.PosDef) {xstar : E n} (hstar : (A ⬝ xstar) = b)
    (hx : IsProjectionApprox A b x₀ K K x) : E_A A xstar x ≤ E_A A xstar x₀ :=
  IsGalerkin.energyNorm_le ((Matrix.posDef_iff_isSymmetricCoercive A).mp hA)
    (isProjectionApprox_iff.mp hx) hstar (by simp)

/-! ### §5.2.3: `P_K`, `Q_K^L` and `A_m` -/

/-- Saad §5.2.3: the operator `A_m = Q_K^L A P_K`. -/
noncomputable def A_m (A : Matrix (Fin n) (Fin n) ℝ) (K L : Submodule ℝ (E n))
    (hd : finrank ℝ K = finrank ℝ L) (h : K ⊓ Lᗮ = ⊥) : (E n) →ₗ[ℝ] (E n) :=
  (SaadSparse.obliqueProjection K L hd h).comp
    ((toEuclideanLin A).comp (K.starProjection : (E n) →L[ℝ] (E n)).toLinearMap)

/-- Saad §5.2.3: with `x₀ = 0` the projection condition reads `x ∈ K` and `Q (b - A x) = 0`. -/
theorem isProjectionApprox_zero_iff_Q (hd : finrank ℝ K = finrank ℝ L) (h : K ⊓ Lᗮ = ⊥) :
    IsProjectionApprox A b 0 K L x ↔
      x ∈ K ∧ SaadSparse.obliqueProjection K L hd h (b - (A ⬝ x)) = 0 := by
  rw [IsProjectionApprox,
    SaadSparse.obliqueProjection_eq_zero_iff hd h (b - (A ⬝ x)),
    ← Submodule.mem_orthogonal L (b - (A ⬝ x))]
  simp

/-- Saad §5.2.3: with `x₀ = 0` the projection condition is the projected equation
`A_m x = Q b`. -/
theorem isProjectionApprox_zero_iff_A_m (hd : finrank ℝ K = finrank ℝ L) (h : K ⊓ Lᗮ = ⊥) :
    IsProjectionApprox A b 0 K L x ↔
      x ∈ K ∧ A_m A K L hd h x = SaadSparse.obliqueProjection K L hd h b := by
  rw [isProjectionApprox_zero_iff_Q hd h]
  refine and_congr_right fun hx => ?_
  have hP : K.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
  have hAm : A_m A K L hd h x = SaadSparse.obliqueProjection K L hd h (A ⬝ x) := by
    rw [A_m]
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hP]
  rw [hAm, map_sub, sub_eq_zero, eq_comm]

/-! ### Proposition 5.6 -/

/-- Saad, Proposition 5.6: if `K` is invariant under `A`, the initial residual lies in `K` and
`K ∩ Lᗮ = 0`, then the projection approximation is exact. -/
theorem prop_5_6 (hK : K ∈ Module.End.invtSubmodule (toEuclideanLin A))
    (hKL : ∀ z ∈ K, z ∈ Lᗮ → z = 0) (hr : b - (A ⬝ x₀) ∈ K)
    (hx : IsProjectionApprox A b x₀ K L x) : (A ⬝ x) = b :=
  (isProjectionApprox_iff.mp hx).eq_of_invt hK hr hKL

/-! ### Theorem 5.7 -/

/-- Saad §5.2.4: the distance from any `x ∈ K` to `x*` is at least the distance of `x*` to `K`. -/
theorem norm_sub_ge_of_mem {xstar : E n} (hx : x ∈ K) :
    ‖xstar - K.starProjection xstar‖ ≤ ‖xstar - x‖ :=
  Submodule.norm_sub_le_of_forall_inner_eq_zero (K.starProjection_apply_mem xstar)
    (fun w hw => K.starProjection_inner_eq_zero xstar w hw) hx

/-- Saad, Theorem 5.7 (the underlying identity): with `b ∈ K` and `x₀ = 0`, the exact solution
`x*` satisfies `b - A_m x* = Q A (I - P_K) x*`, whence
`‖b - A_m x*‖ ≤ ‖Q A (I - P_K)‖ ‖(I - P_K) x*‖`. -/
theorem thm_5_7 (hd : finrank ℝ K = finrank ℝ L) (h : K ⊓ Lᗮ = ⊥) (hb : b ∈ K)
    {xstar : E n} (hstar : (A ⬝ xstar) = b) :
    b - A_m A K L hd h xstar =
      SaadSparse.obliqueProjection K L hd h (A ⬝ (xstar - K.starProjection xstar)) := by
  have hQb : SaadSparse.obliqueProjection K L hd h b = b :=
    ((SaadSparse.isProjOnto_iff_eq_obliqueProjection hd h b b).mp ⟨hb, by simp⟩)
  have hAm : A_m A K L hd h xstar
      = SaadSparse.obliqueProjection K L hd h (A ⬝ K.starProjection xstar) := rfl
  rw [hAm, ← hQb, ← map_sub]
  congr 1
  rw [map_sub, hstar]

end SaadSparse.Ch05
