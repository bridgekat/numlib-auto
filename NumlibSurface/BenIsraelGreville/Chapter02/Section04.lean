/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.Similar
import NumlibSurface.BenIsraelGreville.Chapter01.Section03
import NumlibSurface.BenIsraelGreville.Chapter02.Section05
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Trace

/-!
# Idempotent matrices and projectors

Section 2.4 of [benIsrael2003generalized] identifies idempotent matrices with oblique
projectors. The image and kernel determine an idempotent matrix uniquely.

## Deviations from the source

* **Lemma 1(b)** (reading). The spectrum is contained in $\{0,1\}$. Either value may be absent.
-/

namespace BenIsraelGreville.Chapter02

open Matrix Polynomial
open BenIsraelGreville.Chapter01 (definition_1 mem_one_iff mem_one_two_iff)

variable {m n k : Type*} [Fintype n]

/-- **Section 2.4** of [benIsrael2003generalized]. The projector onto $L$ along a
complementary subspace $M$ sends $x=y+z$, with $y\in L$ and $z\in M$, to $y$. -/
noncomputable abbrev projector {V : Type*} [AddCommGroup V] [Module ℂ V]
    {L M : Submodule ℂ V} (h : IsCompl L M) : V →ₗ[ℂ] V :=
  L.projection M h

private theorem idempotent_iff_mulVecLin {E : Matrix n n ℂ} :
    IsIdempotentElem E ↔ IsIdempotentElem E.mulVecLin := by
  classical
  change E * E = E ↔ E.mulVecLin.comp E.mulVecLin = E.mulVecLin
  rw [← mulVecLin_mul, ← toLin'_apply', ← toLin'_apply']
  exact toLin'.injective.eq_iff.symm

/-- **Lemma 1(a), (d)–(g)** of [benIsrael2003generalized], Chapter 2. The adjoint and
complement of an idempotent are idempotent. The complementary product vanishes on both
sides, the original matrix fixes its range, it is a reflexive inverse of itself, and
its kernel is the range of its complement. -/
theorem lemma_1_projection [DecidableEq n] {E : Matrix n n ℂ} (hE : IsIdempotentElem E) :
    IsIdempotentElem Eᴴ ∧ IsIdempotentElem (1 - E) ∧
      E * (1 - E) = 0 ∧ (1 - E) * E = 0 ∧
      (∀ x : n → ℂ, E *ᵥ x = x ↔ x ∈ LinearMap.range E.mulVecLin) ∧
      E ∈ definition_1 E {.inner, .outer} ∧
      LinearMap.ker E.mulVecLin = LinearMap.range (1 - E).mulVecLin := by
  have hf := idempotent_iff_mulVecLin.mp hE
  have hc : IsIdempotentElem Eᴴ := by
    change Eᴴ * Eᴴ = Eᴴ
    simpa only [conjTranspose_mul] using congrArg Matrix.conjTranspose hE.eq
  have he : E * E * E = E := by rw [hE.eq, hE.eq]
  refine ⟨hc, hE.one_sub, hE.mul_one_sub_self, hE.one_sub_mul_self, ?_,
    mem_one_two_iff.mpr ⟨he, he⟩, ?_⟩
  · intro x
    exact (LinearMap.IsIdempotentElem.mem_range_iff hf (x := x)).symm
  · have hsub : (1 - E).mulVecLin = LinearMap.id - E.mulVecLin := calc
      (1 - E).mulVecLin = toLin' (1 - E) := (toLin'_apply' _).symm
      _ = _ := by rw [map_sub, toLin'_one, toLin'_apply']
    rw [hsub]
    exact LinearMap.IsIdempotentElem.ker_eq_range hf

/-- **Lemma 1(b)–(c)** of [benIsrael2003generalized], Chapter 2. An idempotent matrix
has spectrum contained in $\{0,1\}$. The multiplicity of $1$ and the trace both
equal the rank.

**Reading.** The listed eigenvalues are the possible values. For example, the zero matrix
on a nonzero space has no eigenvalue $1$. -/
theorem lemma_1_spectral [DecidableEq n] {E : Matrix n n ℂ} (hE : IsIdempotentElem E) :
    (∀ z ∈ spectrum ℂ E, z = 0 ∨ z = 1) ∧
      E.charpoly.rootMultiplicity 1 = E.rank ∧ E.trace = (E.rank : ℂ) := by
  let f := E.mulVecLin
  have hf : IsIdempotentElem f := idempotent_iff_mulVecLin.mp hE
  have hp := (LinearMap.isProj_range_iff_isIdempotentElem f).mpr hf
  let d := Module.finrank ℂ f.ker
  have hChar : E.charpoly = (Polynomial.X - 1) ^ E.rank * Polynomial.X ^ d := calc
    E.charpoly = f.charpoly := (Matrix.charpoly_toLin' E).symm
    _ = (LinearMap.prodMap (LinearMap.id : f.range →ₗ[ℂ] f.range)
          (0 : f.ker →ₗ[ℂ] f.ker)).charpoly :=
      (congrArg LinearMap.charpoly hp.eq_conj_prodMap).trans (LinearEquiv.charpoly_conj _ _)
    _ = _ := by
      rw [LinearMap.charpoly_prodMap, ← Module.End.one_eq_id,
        LinearMap.charpoly_one, LinearMap.charpoly_zero]
      rfl
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hr := (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz).eq_zero
    simp only [hChar, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_one] at hr
    rcases mul_eq_zero.mp hr with h | h
    · exact Or.inr (sub_eq_zero.mp (eq_zero_of_pow_eq_zero h))
    · exact Or.inl (eq_zero_of_pow_eq_zero h)
  · have hroot : (Polynomial.X ^ d : ℂ[X]).rootMultiplicity 1 = 0 := by
      apply Polynomial.rootMultiplicity_eq_zero
      intro h
      have he := h.eq_zero
      simp only [Polynomial.eval_pow, Polynomial.eval_X, one_pow, one_ne_zero] at he
    have hm := Polynomial.rootMultiplicity_mul_X_sub_C_pow (a := (1 : ℂ)) (n := E.rank)
      (pow_ne_zero d Polynomial.X_ne_zero)
    rw [hChar, mul_comm]
    simpa only [Polynomial.C_1, hroot, zero_add] using hm
  · exact (Matrix.trace_toLin'_eq E).symm.trans hp.trace

/-- **Lemma 2** of [benIsrael2003generalized], Chapter 2. For a full-rank factorization
$E=FG$, the matrix $E$ is idempotent if and only if $GF=I$. -/
theorem lemma_2 [Fintype k] [DecidableEq k] (F : Matrix n k ℂ)
    (G : Matrix k n ℂ) (hF : F.rank = Fintype.card k) (hG : G.rank = Fintype.card k) :
    IsIdempotentElem (F * G) ↔ G * F = 1 := by
  classical
  have hL := (Chapter01.lemma_2_a (mem_one_iff.mpr F.mul_pinv_mul_self)).mpr hF
  have hR := (Chapter01.lemma_2_b (mem_one_iff.mpr G.mul_pinv_mul_self)).mpr hG
  constructor
  · intro h
    calc
      G * F = (F.pinv * F) * (G * F) * (G * G.pinv) := by
        rw [hL, hR, Matrix.one_mul, Matrix.mul_one]
      _ = F.pinv * ((F * G) * (F * G)) * G.pinv := by simp only [Matrix.mul_assoc]
      _ = (F.pinv * F) * (G * G.pinv) := by rw [h.eq]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hL, hR, Matrix.one_mul]
  · intro h
    change (F * G) * (F * G) = F * G
    calc
      (F * G) * (F * G) = F * (G * F) * G := by simp only [Matrix.mul_assoc]
      _ = F * G := by rw [h, Matrix.mul_one]

/-- **Theorem 8** of [benIsrael2003generalized], Chapter 2. An idempotent matrix is the
projection onto its range along its kernel. Conversely, complementary subspaces determine
a unique idempotent matrix having that range and kernel. -/
theorem theorem_8 :
    (∀ E : Matrix n n ℂ, IsIdempotentElem E →
      ∃ h : IsCompl (LinearMap.range E.mulVecLin) (LinearMap.ker E.mulVecLin),
        E.mulVecLin = projector h) ∧
    (∀ L M : Submodule ℂ (n → ℂ), IsCompl L M →
      ∃! E : Matrix n n ℂ, IsIdempotentElem E ∧
        LinearMap.range E.mulVecLin = L ∧ LinearMap.ker E.mulVecLin = M) := by
  classical
  refine ⟨fun E hE => LinearMap.isIdempotentElem_iff_eq_projection_range_ker.mp
    (idempotent_iff_mulVecLin.mp hE), ?_⟩
  intro L M h
  let E : Matrix n n ℂ := toLin'.symm (projector h)
  have he : E.mulVecLin = projector h := by
    rw [← toLin'_apply', LinearEquiv.apply_symm_apply]
  have hProj := Submodule.isIdempotentElem_projection h
  have hid : IsIdempotentElem E.mulVecLin := he.symm ▸ hProj
  have hr : LinearMap.range E.mulVecLin = L := he.symm ▸ Submodule.range_projection h
  have hk : LinearMap.ker E.mulVecLin = M := he.symm ▸ Submodule.ker_projection h
  refine ⟨E, ⟨idempotent_iff_mulVecLin.mpr hid, hr, hk⟩, ?_⟩
  rintro Y ⟨hi, hYr, hYk⟩
  apply toLin'.injective
  simpa only [toLin'_apply'] using
    (LinearMap.IsIdempotentElem.ext (idempotent_iff_mulVecLin.mp hi) hid
      ⟨hYr.trans hr.symm, hYk.trans hk.symm⟩)

/-- **Corollary 6** of [benIsrael2003generalized], Chapter 2. The components in complementary
subspaces are obtained by applying the projector and its complement. -/
theorem corollary_6 {V : Type*} [AddCommGroup V] [Module ℂ V]
    {L M : Submodule ℂ V} (h : IsCompl L M) (x : V) :
    projector h x ∈ L ∧ x - projector h x ∈ M ∧
      ∀ y ∈ L, ∀ z ∈ M, y + z = x → y = projector h x ∧ z = x - projector h x := by
  refine ⟨L.projection_apply_mem h x, L.sub_projection_mem h x, ?_⟩
  intro y hy z hz hsum
  have hyx : projector h x = y := by
    rw [← hsum, map_add, (L.projection_eq_self_iff h y).mpr hy,
      L.projection_apply_of_mem_right h hz, add_zero]
  exact ⟨hyx.symm, by rw [hyx, ← hsum, add_sub_cancel_left]⟩

/-- **Corollary 7** of [benIsrael2003generalized], Chapter 2. For a reflexive inverse $X$
of $A$, $AX$ projects onto the range of $A$ along the kernel of $X$, and $XA$ projects
onto the range of $X$ along the kernel of $A$. -/
theorem corollary_7 [Fintype m]
    {A : Matrix m n ℂ} {X : Matrix n m ℂ} (hX : X ∈ definition_1 A {.inner, .outer}) :
    (∃ h : IsCompl (LinearMap.range A.mulVecLin) (LinearMap.ker X.mulVecLin),
      (A * X).mulVecLin = projector h) ∧
    (∃ h : IsCompl (LinearMap.range X.mulVecLin) (LinearMap.ker A.mulVecLin),
      (X * A).mulVecLin = projector h) := by
  obtain ⟨hi, ho⟩ := mem_one_two_iff.mp hX
  have hi' := isOuterInverse_iff_isInnerInverse.mp ho
  constructor
  · have h := theorem_8.1 (A * X) hi.isIdempotentElem_mul
    rwa [hi.range_mul, hi'.ker_mul_rev] at h
  · have h := theorem_8.1 (X * A) hi.isIdempotentElem_mul_rev
    rwa [hi'.range_mul, hi.ker_mul_rev] at h

/-- The spectral decomposition equations for a diagonalizable matrix, with the
projectors extended by zero outside the spectrum. -/
structure IsDiagonalSpectralDecomposition [DecidableEq n] (A : Matrix n n ℂ)
    (E : ℂ → Matrix n n ℂ) : Prop where
  supported : ∀ z ∉ spectralValues A, E z = 0
  mul : ∀ z w, E z * E w = if z = w then E z else 0
  sum : ∑ z ∈ spectralValues A, E z = 1
  weightedSum : A = ∑ z ∈ spectralValues A, z • E z

private theorem range_le_eigenspace_iff_mul_eq_smul (A E : Matrix n n ℂ) (z : ℂ) :
    E.mulVecLin.range ≤ Module.End.eigenspace A.mulVecLin z ↔ A * E = z • E := by
  classical
  rw [ext_iff_mulVec]
  have hEval (x : n → ℂ) : (A * E) *ᵥ x = (z • E) *ᵥ x ↔
      E.mulVecLin x ∈ Module.End.eigenspace A.mulVecLin z := by
    change (A * E).mulVecLin x = (z • E).mulVecLin x ↔ _
    rw [mulVecLin_mul, LinearMap.comp_apply, ← toLin'_apply' (z • E), map_smul,
      LinearMap.smul_apply, toLin'_apply', Module.End.mem_eigenspace_iff]
  refine ⟨fun h x => (hEval x).mpr (h (LinearMap.mem_range_self E.mulVecLin x)), ?_⟩
  rintro h _ ⟨x, rfl⟩
  exact (hEval x).mp (h x)

/-- For a diagonalizable matrix, the principal idempotent at $z$ projects onto
the eigenspace at $z$ along the sum of the other eigenspaces. -/
theorem principalIdempotent_range_ker_of_diagonalizable [DecidableEq n] {A : Matrix n n ℂ}
    (hA : ∃ d : n → ℂ, IsSimilar A (diagonal d)) (z : ℂ) :
    (principalIdempotent A z).mulVecLin.range = Module.End.eigenspace A.mulVecLin z ∧
    (principalIdempotent A z).mulVecLin.ker =
      ⨆ w : ℂ, ⨆ _ : w ≠ z, Module.End.eigenspace A.mulVecLin w := by
  have h := (isSimilar_diagonal_iff_iSup_eigenspace_eq_top A).mp hA
  have he := Module.End.maxGenEigenspace_eq_eigenspace_of_iSup_eigenspace_eq_top h
  simp only [range_principalIdempotent, ker_principalIdempotent, he, and_self]

private theorem range_le_eigenspace_of_diagonal_decomposition [DecidableEq n]
    {A : Matrix n n ℂ} {E : ℂ → Matrix n n ℂ} (hE : IsDiagonalSpectralDecomposition A E)
    (z : ℂ) : (E z).mulVecLin.range ≤ Module.End.eigenspace A.mulVecLin z := by
  rw [range_le_eigenspace_iff_mul_eq_smul]
  by_cases hz : z ∈ spectralValues A
  · rw [hE.weightedSum, Finset.sum_mul, Finset.sum_eq_single_of_mem z hz]
    · simp [hE.mul]
    · intro w _ hw
      rw [Matrix.smul_mul, hE.mul, ite_eq_right hw, smul_zero]
  · rw [hE.supported z hz, Matrix.mul_zero, smul_zero]

/-- **Theorem 9** of [benIsrael2003generalized], Chapter 2. A matrix is
diagonalizable precisely when it has a spectral decomposition into a family
of pairwise annihilating idempotents that sum to the identity. The family is unique. -/
theorem theorem_9 [DecidableEq n] (A : Matrix n n ℂ) :
    (∃ d : n → ℂ, IsSimilar A (diagonal d)) ↔ ∃! E, IsDiagonalSpectralDecomposition A E := by
  constructor
  · intro hA
    let E := principalIdempotent A
    have hE := (theorem_10 A).1
    refine ⟨E, ⟨hE.supported, hE.mul, hE.sum, ?_⟩,
      fun F hF => eq_principalIdempotent_of_range_and_sum A F hF.supported hF.sum
        fun z => (range_le_eigenspace_of_diagonal_decomposition hF z).trans
          Module.End.eigenspace_le_maxGenEigenspace⟩
    calc
      A = A * ∑ z ∈ spectralValues A, E z := by
        change A = A * ∑ z ∈ spectralValues A, principalIdempotent A z
        rw [hE.sum, Matrix.mul_one]
      _ = ∑ z ∈ spectralValues A, A * E z := Finset.mul_sum _ _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro z _
        exact (range_le_eigenspace_iff_mul_eq_smul A (E z) z).mp
          (principalIdempotent_range_ker_of_diagonalizable hA z).1.le
  · rintro ⟨E, hE, _⟩
    rw [isSimilar_diagonal_iff_iSup_eigenspace_eq_top]
    apply top_unique
    intro x _
    have h : x = ∑ z ∈ spectralValues A, (E z).mulVecLin x := by
      have hSum := congrArg (fun B : Matrix n n ℂ => B.toLin' x) hE.sum
      change toLin' (∑ z ∈ spectralValues A, E z) x = toLin' (1 : Matrix n n ℂ) x at hSum
      rw [toLin'_one, LinearMap.id_apply, map_sum, LinearMap.sum_apply] at hSum
      exact hSum.symm
    rw [h]
    exact Submodule.sum_mem _ fun z _ => le_iSup (Module.End.eigenspace A.mulVecLin) z
      (range_le_eigenspace_of_diagonal_decomposition hE z (LinearMap.mem_range_self _ x))

end BenIsraelGreville.Chapter02
