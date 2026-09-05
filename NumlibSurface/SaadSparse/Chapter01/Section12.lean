import Numlib.Analysis.InnerProductSpace.Projection.ObliqueProjection
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.LinearSolve.Projection.Basic
import NumlibSurface.SaadSparse.Common

/-!
# §1.12 Projection operators

Section 1.12 of Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003: projectors (1.58), the projector onto `M` orthogonally to `L` (1.59)–(1.62), its
matrix representations (1.63)–(1.66), orthogonal projectors (1.67)–(1.72), Lemma 1.36,
Proposition 1.37, Theorem 1.38 and Corollary 1.39.

A projector in the book's sense is an idempotent matrix; the backbone counterparts are
`IsIdempotentElem` on `EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n)`,
`LinearMap.obliqueProjectionOfBases` and `Submodule.starProjection`.
-/

open Module Submodule

open scoped SaadSparse

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}

/-! ### Projectors (1.58) and orthogonal projectors (1.67) -/

/-- Saad §1.12.1: a *projector* is an idempotent matrix, `P² = P`. -/
abbrev IsProjector (P : Matrix (Fin n) (Fin n) 𝕜) : Prop := IsIdempotentElem P

/-- A matrix is a projector iff the operator it defines on `ℂⁿ` is idempotent. -/
theorem isProjector_iff_isIdempotentElem_toEuclideanLin (P : Matrix (Fin n) (Fin n) 𝕜) :
    P.IsProjector ↔ IsIdempotentElem (toEuclideanLin P) := by
  constructor
  · intro h
    change toEuclideanLin P ∘ₗ toEuclideanLin P = toEuclideanLin P
    rw [← toEuclideanLin_mul, h]
  · intro h
    refine toEuclideanLin.injective ?_
    rw [toEuclideanLin_mul]
    exact h

/-- Saad (1.67): `P` is an *orthogonal projector* if it is a projector whose null space is the
orthogonal complement of its range. -/
def IsOrthogonalProjector (P : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  IsIdempotentElem P ∧
    LinearMap.ker (toEuclideanLin P) = (LinearMap.range (toEuclideanLin P))ᗮ

/-! ### Bases and matrix representations (1.63)–(1.66) -/

/-- The columns of an `n × m` matrix, as a family of vectors of `ℂⁿ`. -/
def cols (V : Matrix (Fin n) (Fin m) 𝕜) : Fin m → EuclideanSpace 𝕜 (Fin n) :=
  fun j => WithLp.toLp 2 (Vᵀ j)

omit [RCLike 𝕜] in
@[simp]
theorem ofLp_cols_apply (V : Matrix (Fin n) (Fin m) 𝕜) (j : Fin m) (i : Fin n) :
    WithLp.ofLp (V.cols j) i = V i j := rfl

/-- Saad §1.12.3: `V = [v₁, …, v_m]` is a basis of the subspace `M`. -/
structure IsBasisOf (V : Matrix (Fin n) (Fin m) 𝕜) (M : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n))) :
    Prop where
  /-- The columns of `V` are linearly independent. -/
  linearIndependent : LinearIndependent 𝕜 V.cols
  /-- The columns of `V` span `M`. -/
  span_eq : Submodule.span 𝕜 (Set.range V.cols) = M

/-- The `Module.Basis` of `M` given by the columns of `V`, for use with the backbone statements
phrased with `Module.Basis`. -/
noncomputable def IsBasisOf.toBasis {V : Matrix (Fin n) (Fin m) 𝕜}
    {M : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n))} (hV : V.IsBasisOf M) :
    Module.Basis (Fin m) 𝕜 M :=
  (Module.Basis.span hV.linearIndependent).map (LinearEquiv.ofEq _ _ hV.span_eq)

@[simp]
theorem IsBasisOf.coe_toBasis_apply {V : Matrix (Fin n) (Fin m) 𝕜}
    {M : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n))} (hV : V.IsBasisOf M) (j : Fin m) :
    (hV.toBasis j : EuclideanSpace 𝕜 (Fin n)) = V.cols j := by
  simp [IsBasisOf.toBasis]

/-- Saad §1.12.3: `V` and `W` are biorthogonal when `Wᴴ V = I` (1.63). -/
def IsBiorthogonal (V W : Matrix (Fin n) (Fin m) 𝕜) : Prop := Wᴴ * V = 1

/-- Saad (1.66): the projector `P = V (Wᴴ V)⁻¹ Wᴴ` onto `span V` orthogonally to `span W`. -/
noncomputable def obliqueProj (V W : Matrix (Fin n) (Fin m) 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  V * (Wᴴ * V)⁻¹ * Wᴴ

/-- The backbone's cross-Gram matrix of the columns of `V` and `W` is `Wᴴ V`. -/
theorem crossGram_cols (V W : Matrix (Fin n) (Fin m) 𝕜) :
    LinearMap.crossGram 𝕜 V.cols W.cols = Wᴴ * V := by
  ext i j
  simp [LinearMap.crossGram, SaadSparse.inner_eq_dotProduct_star, Matrix.mul_apply, dotProduct,
    mul_comm]

/-- The book's `Wᴴ x` is the family of inner products `(x, w_i)` used by the backbone. -/
theorem conjTranspose_mulVec_eq_inner (W : Matrix (Fin n) (Fin m) 𝕜)
    (x : EuclideanSpace 𝕜 (Fin n)) :
    (Wᴴ *ᵥ WithLp.ofLp x) = fun i => inner 𝕜 (W.cols i) x := by
  funext i
  simp [SaadSparse.inner_eq_dotProduct_star, mulVec, dotProduct, mul_comm]

/-- Saad (1.66) is the backbone's `LinearMap.obliqueProjectionOfBases`. -/
theorem toEuclideanLin_obliqueProj (V W : Matrix (Fin n) (Fin m) 𝕜) :
    toEuclideanLin (obliqueProj V W) = LinearMap.obliqueProjectionOfBases 𝕜 V.cols W.cols := by
  refine LinearMap.ext fun x => ?_
  have hrhs : LinearMap.obliqueProjectionOfBases 𝕜 V.cols W.cols x
      = ∑ j, ((Wᴴ * V)⁻¹ *ᵥ (Wᴴ *ᵥ WithLp.ofLp x)) j • V.cols j := by
    change ∑ j, (LinearMap.crossGram 𝕜 V.cols W.cols)⁻¹.mulVec
      (fun i => inner 𝕜 (W.cols i) x) j • V.cols j = _
    rw [crossGram_cols, ← conjTranspose_mulVec_eq_inner]
  have hlhs : toEuclideanLin (obliqueProj V W) x
      = toEuclideanLin V (WithLp.toLp 2 ((Wᴴ * V)⁻¹ *ᵥ (Wᴴ *ᵥ WithLp.ofLp x))) := by
    change WithLp.toLp 2 ((V * (Wᴴ * V)⁻¹ * Wᴴ) *ᵥ WithLp.ofLp x) = _
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    rfl
  rw [hlhs, hrhs, toEuclideanLin_apply_eq_sum]
  rfl

end Matrix

namespace SaadSparse

variable {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}

/-! ### The projector onto `M` orthogonal to `L` (1.59)–(1.62) -/

/-- Saad (1.59)–(1.60): `u` is *the* projection of `x` onto `M` orthogonally to `L` when `u ∈ M`
and `x - u ⟂ L`. -/
def IsProjOnto (M L : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n))) (x u : EuclideanSpace 𝕜 (Fin n)) :
    Prop := u ∈ M ∧ x - u ∈ Lᗮ

/-- The projector onto `M` orthogonally to `L`: the unique idempotent with range `M` and kernel
`Lᗮ`, which exists as soon as `dim M = dim L` and no nonzero vector of `M` is orthogonal to
`L` (Saad §1.12.2). -/
noncomputable def obliqueProjection (M L : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)))
    (hd : finrank 𝕜 M = finrank 𝕜 L) (h : M ⊓ Lᗮ = ⊥) :
    EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n) :=
  (LinearMap.existsUnique_isIdempotentElem_of_inf_orthogonal_eq_bot hd h).exists.choose

variable {M L : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n))}

theorem obliqueProjection_spec (hd : finrank 𝕜 M = finrank 𝕜 L) (h : M ⊓ Lᗮ = ⊥) :
    IsIdempotentElem (obliqueProjection M L hd h) ∧
      LinearMap.range (obliqueProjection M L hd h) = M ∧
      LinearMap.ker (obliqueProjection M L hd h) = Lᗮ :=
  (LinearMap.existsUnique_isIdempotentElem_of_inf_orthogonal_eq_bot hd h).exists.choose_spec

/-- Saad (1.62): the range of the projector onto `M` orthogonally to `L` is `M`. -/
theorem range_obliqueProjection (hd : finrank 𝕜 M = finrank 𝕜 L) (h : M ⊓ Lᗮ = ⊥) :
    LinearMap.range (obliqueProjection M L hd h) = M := (obliqueProjection_spec hd h).2.1

/-- Saad (1.62): the null space of the projector onto `M` orthogonally to `L` is `Lᗮ`. -/
theorem ker_obliqueProjection (hd : finrank 𝕜 M = finrank 𝕜 L) (h : M ⊓ Lᗮ = ⊥) :
    LinearMap.ker (obliqueProjection M L hd h) = Lᗮ := (obliqueProjection_spec hd h).2.2

/-- The defining property (1.59)–(1.60) of the projector: `P x = u` iff `u ∈ M` and `x - u ⟂ L`. -/
theorem isProjOnto_iff_eq_obliqueProjection (hd : finrank 𝕜 M = finrank 𝕜 L) (h : M ⊓ Lᗮ = ⊥)
    (x u : EuclideanSpace 𝕜 (Fin n)) :
    IsProjOnto M L x u ↔ obliqueProjection M L hd h x = u :=
  (LinearMap.IsIdempotentElem.apply_eq_iff (obliqueProjection_spec hd h).1
    (range_obliqueProjection hd h) (ker_obliqueProjection hd h) x u).symm

theorem isProjOnto_obliqueProjection (hd : finrank 𝕜 M = finrank 𝕜 L) (h : M ⊓ Lᗮ = ⊥)
    (x : EuclideanSpace 𝕜 (Fin n)) : IsProjOnto M L x (obliqueProjection M L hd h x) :=
  (isProjOnto_iff_eq_obliqueProjection hd h x _).mpr rfl

/-- Saad (1.62): `P x = 0` iff `x ⟂ L`. -/
theorem obliqueProjection_eq_zero_iff (hd : finrank 𝕜 M = finrank 𝕜 L) (h : M ⊓ Lᗮ = ⊥)
    (x : EuclideanSpace 𝕜 (Fin n)) : obliqueProjection M L hd h x = 0 ↔ x ∈ Lᗮ := by
  rw [← LinearMap.mem_ker, ker_obliqueProjection]

/-- The orthogonal case `L = M` of (1.59)–(1.60) is Mathlib's `Submodule.starProjection`. -/
theorem isProjOnto_self_iff_eq_starProjection (x u : EuclideanSpace 𝕜 (Fin n)) :
    IsProjOnto M M x u ↔ u = M.starProjection x := by
  refine ⟨fun h => (Submodule.eq_starProjection_of_mem_orthogonal h.1 h.2).symm, ?_⟩
  rintro rfl
  exact ⟨M.starProjection_apply_mem x, M.sub_starProjection_mem_orthogonal x⟩

end SaadSparse

namespace SaadSparse.Ch01

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}
variable {M L : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n))}

/-! ### Projector basics (1.58) -/

/-- Saad §1.12.1: `I - P` is a projector whenever `P` is. -/
theorem isProjector_one_sub {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P.IsProjector) :
    (1 - P).IsProjector := hP.one_sub

/-- Saad §1.12.1: `Null P = Ran (I - P)`. -/
theorem ker_eq_range_one_sub {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P.IsProjector) :
    LinearMap.ker (toEuclideanLin P) = LinearMap.range (toEuclideanLin (1 - P)) := by
  have hidem : IsIdempotentElem (toEuclideanLin P) :=
    (isProjector_iff_isIdempotentElem_toEuclideanLin P).mp hP
  have h1 : toEuclideanLin (1 - P) = 1 - toEuclideanLin P := by
    rw [map_sub, toEuclideanLin_one]; rfl
  rw [h1]
  exact LinearMap.IsIdempotentElem.ker_eq_range_one_sub hidem

/-- Saad §1.12.1: `ℂⁿ = Ran P ⊕ Null P`, in particular `Null P ∩ Ran P = {0}`. -/
theorem isCompl_range_ker {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P.IsProjector) :
    IsCompl (LinearMap.range (toEuclideanLin P)) (LinearMap.ker (toEuclideanLin P)) :=
  LinearMap.IsIdempotentElem.isCompl
    ((isProjector_iff_isIdempotentElem_toEuclideanLin P).mp hP)

/-- Saad §1.12.1: every pair of complementary subspaces `(M, S)` is the range/null-space pair of
a unique projector. -/
theorem existsUnique_projector (h : IsCompl M L) :
    ∃! P : EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n),
      IsIdempotentElem P ∧ LinearMap.range P = M ∧ LinearMap.ker P = L := by
  refine ⟨M.projection L h, ⟨Submodule.isIdempotentElem_projection h,
    Submodule.range_projection h, Submodule.ker_projection h⟩, ?_⟩
  rintro Q ⟨hQ, hQr, hQk⟩
  exact LinearMap.IsIdempotentElem.ext_of_range_eq_of_ker_eq hQ
    (Submodule.isIdempotentElem_projection h)
    (hQr.trans (Submodule.range_projection h).symm)
    (hQk.trans (Submodule.ker_projection h).symm)

/-- Saad §1.12.1: `rank P = m` gives `dim Ran (I - P) = n - m`. -/
theorem finrank_range_one_sub_add {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P.IsProjector) :
    finrank 𝕜 (LinearMap.range (toEuclideanLin (1 - P)))
      + finrank 𝕜 (LinearMap.range (toEuclideanLin P)) = n := by
  rw [← ker_eq_range_one_sub hP, add_comm,
    LinearMap.finrank_range_add_finrank_ker (toEuclideanLin P)]
  simp

/-! ### Lemma 1.36 -/

/-- **Lemma 1.36**.  For subspaces `M`, `L` of the same dimension: no nonzero vector of `M` is
orthogonal to `L` if and only if for every `x` there is a unique `u` with `u ∈ M` and
`x - u ⟂ L`. -/
theorem lemma_1_36 (hd : finrank 𝕜 M = finrank 𝕜 L) :
    (∀ v ∈ M, v ∈ Lᗮ → v = 0) ↔ ∀ x, ∃! u, IsProjOnto M L x u := by
  constructor
  · intro hv x
    have hbot : M ⊓ Lᗮ = ⊥ := by
      refine le_antisymm (fun z hz => ?_) bot_le
      exact (Submodule.mem_bot 𝕜).mpr (hv z hz.1 hz.2)
    exact ⟨obliqueProjection M L hd hbot x, isProjOnto_obliqueProjection hd hbot x,
      fun y hy => ((isProjOnto_iff_eq_obliqueProjection hd hbot x y).mp hy).symm⟩
  · intro h v hvM hvL
    obtain ⟨u, -, hu⟩ := h v
    have h0 : (0 : EuclideanSpace 𝕜 (Fin n)) = u := hu 0 ⟨M.zero_mem, by simpa using hvL⟩
    have hv0 : v = u := hu v ⟨hvM, by simp⟩
    rw [hv0, ← h0]

/-! ### Matrix representations (1.63)–(1.66) -/

section Bases

variable {V W : Matrix (Fin n) (Fin m) 𝕜}

/-- Saad (1.65): with biorthogonal bases, `P = V Wᴴ`. -/
theorem obliqueProj_of_biorthogonal (h : IsBiorthogonal V W) : obliqueProj V W = V * Wᴴ := by
  rw [obliqueProj, show Wᴴ * V = 1 from h, inv_one]
  simp

/-- Saad §1.12.3: `Wᴴ z = 0` exactly when `z ⟂ L`, for `W` a basis of `L`. -/
theorem conjTranspose_mulVec_eq_zero_iff (hW : W.IsBasisOf L) (z : EuclideanSpace 𝕜 (Fin n)) :
    Wᴴ *ᵥ WithLp.ofLp z = 0 ↔ z ∈ Lᗮ := by
  rw [conjTranspose_mulVec_eq_inner, ← hW.span_eq, Submodule.mem_orthogonal_span]
  constructor
  · intro h
    rintro _ ⟨i, rfl⟩
    exact congrFun h i
  · intro h
    funext i
    exact h _ (Set.mem_range_self i)

/-- `V y` lies in the span of the columns of `V`. -/
theorem toEuclideanLin_mem_span (V : Matrix (Fin n) (Fin m) 𝕜)
    (y : EuclideanSpace 𝕜 (Fin m)) : (V ⬝ y) ∈ Submodule.span 𝕜 (Set.range V.cols) := by
  rw [show (V ⬝ y) = toEuclideanLin V (WithLp.toLp 2 (WithLp.ofLp y)) from rfl,
    toEuclideanLin_apply_eq_sum]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))

/-- Saad (1.64): `P x = V y` iff `Wᴴ (x - V y) = 0`. -/
theorem isProjOnto_iff_conjTranspose_mulVec_eq_zero (hV : V.IsBasisOf M) (hW : W.IsBasisOf L)
    (x : EuclideanSpace 𝕜 (Fin n)) (y : EuclideanSpace 𝕜 (Fin m)) :
    IsProjOnto M L x (V ⬝ y) ↔ Wᴴ *ᵥ (WithLp.ofLp x - V *ᵥ WithLp.ofLp y) = 0 := by
  have hmem : (V ⬝ y) ∈ M := hV.span_eq ▸ toEuclideanLin_mem_span V y
  have hsub : WithLp.ofLp (x - (V ⬝ y)) = WithLp.ofLp x - V *ᵥ WithLp.ofLp y := rfl
  rw [IsProjOnto, ← conjTranspose_mulVec_eq_zero_iff hW (x - (V ⬝ y)), hsub]
  simp [hmem]

/-- Saad §1.12.3: `Wᴴ V` is nonsingular iff no nonzero vector of `M` is orthogonal to `L`
(the hypothesis of Lemma 1.36). -/
theorem isUnit_conjTranspose_mul_iff (hV : V.IsBasisOf M) (hW : W.IsBasisOf L) :
    IsUnit (Wᴴ * V) ↔ ∀ v ∈ M, v ∈ Lᗮ → v = 0 := by
  have hzero : ∀ y : Fin m → 𝕜, (Wᴴ * V) *ᵥ y = 0 ↔
      (V ⬝ (WithLp.toLp 2 y : EuclideanSpace 𝕜 (Fin m))) ∈ Lᗮ := by
    intro y
    rw [← conjTranspose_mulVec_eq_zero_iff hW, ← mulVec_mulVec]
    rfl
  constructor
  · intro h v hvM hvL
    rw [← hV.span_eq] at hvM
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1 hvM
    have hVc : (V ⬝ (WithLp.toLp 2 c : EuclideanSpace 𝕜 (Fin m))) = ∑ k, c k • V.cols k :=
      toEuclideanLin_apply_eq_sum V c
    have h0 : (Wᴴ * V) *ᵥ c = 0 := (hzero c).mpr (by rw [hVc]; exact hvL)
    have hc : c = 0 := by
      have hinj := mulVec_injective_iff_isUnit.mpr h
      have := hinj (a₁ := c) (a₂ := 0) (by rw [h0, mulVec_zero])
      exact this
    rw [hc]
    simp
  · intro hcond
    refine mulVec_injective_iff_isUnit.mp fun u v huv => ?_
    have hsub : (Wᴴ * V) *ᵥ (u - v) = 0 := by
      rw [mulVec_sub, huv, sub_self]
    have hmemM : (V ⬝ (WithLp.toLp 2 (u - v) : EuclideanSpace 𝕜 (Fin m))) ∈ M :=
      hV.span_eq ▸ toEuclideanLin_mem_span V _
    have hzeroV := hcond _ hmemM ((hzero (u - v)).mp hsub)
    rw [toEuclideanLin_apply_eq_sum] at hzeroV
    have := Fintype.linearIndependent_iff.mp hV.linearIndependent (u - v) hzeroV
    funext i
    have := this i
    rwa [Pi.sub_apply, sub_eq_zero] at this

/-- Saad (1.66): `P = V (Wᴴ V)⁻¹ Wᴴ` is the projector onto `M` orthogonally to `L`. -/
theorem obliqueProj_isProjOnto (hV : V.IsBasisOf M) (hW : W.IsBasisOf L) (h : IsUnit (Wᴴ * V))
    (x : EuclideanSpace 𝕜 (Fin n)) : IsProjOnto M L x (obliqueProj V W ⬝ x) := by
  have h' : IsUnit (LinearMap.crossGram 𝕜 V.cols W.cols) := by rw [crossGram_cols]; exact h
  refine ⟨?_, ?_⟩
  · rw [toEuclideanLin_obliqueProj, ← hV.span_eq,
      ← LinearMap.range_obliqueProjectionOfBases V.cols W.cols h']
    exact LinearMap.mem_range_self _ x
  · rw [toEuclideanLin_obliqueProj, ← hW.span_eq]
    exact LinearMap.sub_obliqueProjectionOfBases_apply_mem_orthogonal V.cols W.cols h' x

end Bases

/-! ### Adjoint projector (1.68)–(1.70) -/

/-- Saad (1.68): `Pᴴ` is a projector. -/
theorem isProjector_conjTranspose {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P.IsProjector) :
    Pᴴ.IsProjector := by
  change Pᴴ * Pᴴ = Pᴴ
  rw [← conjTranspose_mul, show P * P = P from hP]

/-- Saad (1.69): `Null Pᴴ = (Ran P)ᗮ`. -/
theorem ker_conjTranspose_eq_orthogonal_range (P : Matrix (Fin n) (Fin n) 𝕜) :
    LinearMap.ker (toEuclideanLin Pᴴ) = (LinearMap.range (toEuclideanLin P))ᗮ := by
  rw [toEuclideanLin_conjTranspose, LinearMap.orthogonal_range]

/-- Saad (1.70): `Null P = (Ran Pᴴ)ᗮ`. -/
theorem ker_eq_orthogonal_range_conjTranspose (P : Matrix (Fin n) (Fin n) 𝕜) :
    LinearMap.ker (toEuclideanLin P) = (LinearMap.range (toEuclideanLin Pᴴ))ᗮ := by
  rw [toEuclideanLin_conjTranspose, LinearMap.orthogonal_range, LinearMap.adjoint_adjoint]

/-! ### Proposition 1.37 -/

/-- **Proposition 1.37**.  A projector is orthogonal if and only if it is Hermitian. -/
theorem proposition_1_37 {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P.IsProjector) :
    P.IsOrthogonalProjector ↔ P.IsHermitian := by
  have hidem : IsIdempotentElem (toEuclideanLin P) :=
    (isProjector_iff_isIdempotentElem_toEuclideanLin P).mp hP
  rw [← isSymmetric_toEuclideanLin_iff,
    LinearMap.IsIdempotentElem.isSymmetric_iff_orthogonal_range hidem]
  exact ⟨fun h => h.2.symm, fun h => ⟨hP, h.symm⟩⟩

/-- An orthogonal projector is the orthogonal projection onto its range. -/
theorem toEuclideanLin_eq_starProjection {P : Matrix (Fin n) (Fin n) 𝕜}
    (hP : P.IsOrthogonalProjector) :
    toEuclideanLin P = ((LinearMap.range (toEuclideanLin P)).starProjection :
      EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n)) := by
  have hidem : IsIdempotentElem (toEuclideanLin P) :=
    (isProjector_iff_isIdempotentElem_toEuclideanLin P).mp hP.1
  refine LinearMap.ext fun x => (Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_).symm
  · exact LinearMap.mem_range_self _ x
  · rw [← hP.2, LinearMap.mem_ker, map_sub,
      (LinearMap.IsIdempotentElem.mem_range_iff hidem).mp (LinearMap.mem_range_self _ x), sub_self]

/-! ### `P = V Vᴴ` (1.71)–(1.72) -/

section Orthonormal

variable {V : Matrix (Fin n) (Fin m) 𝕜}

/-- `Vᴴ V = I` says exactly that the columns of `V` are orthonormal. -/
theorem conjTranspose_mul_self_eq_one_iff (V : Matrix (Fin n) (Fin m) 𝕜) :
    Vᴴ * V = 1 ↔ Orthonormal 𝕜 V.cols := by
  rw [orthonormal_iff_ite, ← crossGram_cols V V]
  constructor
  · intro h i j
    have hij := congrFun (congrFun h i) j
    rw [Matrix.one_apply] at hij
    simpa [LinearMap.crossGram] using hij
  · intro h
    ext i j
    rw [Matrix.one_apply]
    simpa [LinearMap.crossGram] using h i j

/-- Saad (1.71): with orthonormal columns spanning `M`, `P = V Vᴴ` is the orthogonal projector
onto `M`. -/
theorem toEuclideanLin_mul_conjTranspose (hV : Vᴴ * V = 1) (hVM : V.IsBasisOf M) :
    toEuclideanLin (V * Vᴴ) = (M.starProjection : EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] _) := by
  obtain ⟨hli, rfl⟩ := hVM
  have horth : Orthonormal 𝕜 V.cols := (conjTranspose_mul_self_eq_one_iff V).mp hV
  have hproj : obliqueProj V V = V * Vᴴ := by
    rw [obliqueProj, hV, inv_one]
    simp
  rw [← hproj, toEuclideanLin_obliqueProj,
    LinearMap.obliqueProjectionOfBases_self_eq_starProjection V.cols horth]

/-- Saad §1.12.3: `V₁ V₁ᴴ = V₂ V₂ᴴ` for any two orthonormal bases of the same subspace
(Exercise P-1.30). -/
theorem mul_conjTranspose_eq_of_isBasisOf {V₁ V₂ : Matrix (Fin n) (Fin m) 𝕜}
    (hV₁ : V₁ᴴ * V₁ = 1) (hV₂ : V₂ᴴ * V₂ = 1) (h₁ : V₁.IsBasisOf M) (h₂ : V₂.IsBasisOf M) :
    V₁ * V₁ᴴ = V₂ * V₂ᴴ :=
  toEuclideanLin.injective
    ((toEuclideanLin_mul_conjTranspose hV₁ h₁).trans (toEuclideanLin_mul_conjTranspose hV₂ h₂).symm)

end Orthonormal

/-! ### Properties of orthogonal projectors (§1.12.4) -/

/-- Saad §1.12.4: `‖x‖₂² = ‖P x‖₂² + ‖(I - P) x‖₂²`. -/
theorem norm_sq_eq_add {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P.IsOrthogonalProjector)
    (x : EuclideanSpace 𝕜 (Fin n)) : ‖x‖ ^ 2 = ‖P ⬝ x‖ ^ 2 + ‖(1 - P) ⬝ x‖ ^ 2 := by
  have hPx : (P ⬝ x) = (LinearMap.range (toEuclideanLin P)).starProjection x :=
    LinearMap.congr_fun (toEuclideanLin_eq_starProjection hP) x
  have hQx : ((1 - P) ⬝ x) = (LinearMap.range (toEuclideanLin P))ᗮ.starProjection x := by
    have hadd := Submodule.starProjection_add_starProjection_orthogonal
      (K := LinearMap.range (toEuclideanLin P)) x
    have h1 : toEuclideanLin (1 - P) = 1 - toEuclideanLin P := by
      rw [map_sub, toEuclideanLin_one]; rfl
    have h2 := eq_sub_of_add_eq' hadd
    rw [h2, ← hPx]
    change toEuclideanLin (1 - P) x = _
    rw [h1, LinearMap.sub_apply, Module.End.one_apply]
  rw [hPx, hQx]
  exact (LinearMap.range (toEuclideanLin P)).norm_sq_eq_add_norm_sq_starProjection x

/-- Saad §1.12.4: an orthogonal projector is a contraction, `‖P x‖₂ ≤ ‖x‖₂`. -/
theorem norm_apply_le {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P.IsOrthogonalProjector)
    (x : EuclideanSpace 𝕜 (Fin n)) : ‖P ⬝ x‖ ≤ ‖x‖ := by
  have h := norm_sq_eq_add hP x
  nlinarith [norm_nonneg ((1 - P) ⬝ x), norm_nonneg (P ⬝ x), norm_nonneg x]

/-- Saad §1.12.4: the eigenvalues of a projector are `0` and `1`. -/
theorem spectrum_subset_pair {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.IsProjector) :
    spectrum ℂ P ⊆ {0, 1} := by
  intro μ hμ
  obtain ⟨v, hv, hv0⟩ :=
    ((hasEigenvalue_toEuclideanLin_iff P μ).mpr hμ).exists_hasEigenvector
  have hPv : toEuclideanLin P v = μ • v := Module.End.mem_eigenspace_iff.mp hv
  have hidem := (isProjector_iff_isIdempotentElem_toEuclideanLin P).mp hP
  have h2 : μ • v = (μ * μ) • v := by
    conv_lhs => rw [← hPv, ← DFunLike.congr_fun hidem v]
    change toEuclideanLin P (toEuclideanLin P v) = _
    rw [hPv, map_smul, hPv, smul_smul]
  have hμ2 : μ * μ = μ := by
    by_contra hne
    refine hv0 ?_
    have hs : (μ - μ * μ) • v = 0 := by rw [sub_smul, ← h2, sub_self]
    rcases smul_eq_zero.mp hs with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h
  rcases eq_or_ne μ 0 with rfl | h0
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (by
      have : μ * μ = μ * 1 := by rw [mul_one]; exact hμ2
      simpa using mul_left_cancel₀ h0 this)

/-- Saad §1.12.4: `x` is in the range of a projector iff it is fixed by it (an eigenvector for
the eigenvalue `1`). -/
theorem mem_range_iff_eigen_one {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P.IsProjector)
    (x : EuclideanSpace 𝕜 (Fin n)) :
    x ∈ LinearMap.range (toEuclideanLin P) ↔ (P ⬝ x) = x :=
  LinearMap.IsIdempotentElem.mem_range_iff
    (p := toEuclideanLin P) ((isProjector_iff_isIdempotentElem_toEuclideanLin P).mp hP)

/-! ### Theorem 1.38 and Corollary 1.39 -/

/-- **Theorem 1.38**.  For a subspace `M` and `x ∈ ℂⁿ`, `min_{y ∈ M} ‖x - y‖₂ = ‖x - P x‖₂` with
`P` the orthogonal projector onto `M`. -/
theorem theorem_1_38 (M : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n))) (x : EuclideanSpace 𝕜 (Fin n)) :
    IsLeast ((fun y => ‖x - y‖) '' (M : Set (EuclideanSpace 𝕜 (Fin n))))
      ‖x - M.starProjection x‖ := by
  refine ⟨⟨M.starProjection x, M.starProjection_apply_mem x, rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact Submodule.norm_sub_le_of_forall_inner_eq_zero (M.starProjection_apply_mem x)
    (fun w hw => M.starProjection_inner_eq_zero x w hw) hy

/-- **Corollary 1.39**.  For `y ∈ M`, the distance `‖x - y‖₂` is minimal over `M` if and only if
`x - y ⟂ M`.  (The book's "`min_{y ∈ M}`" is read as ranging over `M`, so membership is a
hypothesis rather than part of the conclusion.) -/
theorem corollary_1_39 (M : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)))
    {x y : EuclideanSpace 𝕜 (Fin n)} (hy : y ∈ M) :
    IsLeast ((fun z => ‖x - z‖) '' (M : Set (EuclideanSpace 𝕜 (Fin n)))) ‖x - y‖ ↔
      x - y ∈ Mᗮ := by
  constructor
  · intro hmin
    rw [Submodule.mem_orthogonal']
    intro u hu
    exact Submodule.inner_eq_zero_of_forall_norm_sub_le hy
      (fun w hw => hmin.2 ⟨w, hw, rfl⟩) hu
  · intro h
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact Submodule.norm_sub_le_of_forall_inner_eq_zero hy
      (fun u hu => (Submodule.mem_orthogonal' _ _).1 h u hu) hw

end SaadSparse.Ch01
