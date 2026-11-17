import Mathlib.Algebra.Module.PID
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.AnnihilatingPolynomial
import Numlib.Krylov.Subspace
import Numlib.LinearAlgebra.Matrix.Jordan

/-!
# Cyclic decompositions and full Krylov grade

The maximal grade of a vector is the degree of the minimal polynomial of the operator.
Over the real or complex scalars, the vectors of this grade contain a basis.
A Jordan basis gives an internal direct sum of cyclic subspaces with primary minimal polynomials.

## Main results

* `Module.End.exists_minpolyVec_eq_minpoly`: existence of a vector annihilated by precisely
  the polynomials that annihilate the operator.
* `Module.End.exists_basis_fullGrade`: existence of a basis of full-grade vectors.
* `Module.End.exists_isInternal_primaryKrylov`: the direct sum over the Jordan chains.

## Proof outline

View the space as a polynomial module, with the indeterminate acting by the operator. The
structure theorem for finitely generated modules over a principal ideal domain gives a vector
whose annihilator is the whole module's annihilator. The set of full-grade vectors is open
in a finite-dimensional model of the space, so its linear span is the whole space.
-/

open Polynomial
open scoped Matrix

namespace Module.End

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The grade of any vector is at most the degree of the operator's minimal polynomial. -/
theorem grade_le_natDegree_minpoly (A : End K V) (v : V) :
    Krylov.grade A v ≤ (minpoly K A).natDegree := by
  rw [← Krylov.natDegree_minpolyVec A v]
  refine natDegree_le_of_dvd ((Krylov.minpolyVec_dvd_iff A v).2 ?_)
    (minpoly.ne_zero_of_finite K A)
  rw [minpoly.aeval, LinearMap.zero_apply]

/-- For every endomorphism of a finite-dimensional space there is a vector whose minimal
polynomial equals the operator's minimal polynomial. -/
theorem exists_minpolyVec_eq_minpoly (A : End K V) :
    ∃ v : V, Krylov.minpolyVec A v = minpoly K A := by
  obtain ⟨w, hw⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator
    (R := K[X]) (M := Module.AEval' A)
  let v := (Module.AEval'.of A).symm w
  refine ⟨v, ?_⟩
  have hp := Krylov.minpolyVec_monic A v (Krylov.minpolyVec_ne_zero A v)
  have hm := minpoly.monic (IsIntegral.of_finite K A)
  have hd : Krylov.minpolyVec A v ∣ minpoly K A :=
    (Krylov.minpolyVec_dvd_iff A v).2 (by rw [minpoly.aeval, LinearMap.zero_apply])
  have hd' : minpoly K A ∣ Krylov.minpolyVec A v := by
    rw [← Ideal.mem_span_singleton, Polynomial.span_minpoly_eq_annihilator, ← hw,
      LinearMap.mem_ker]
    change Krylov.minpolyVec A v • w = 0
    apply (Module.AEval'.of A).symm.injective
    rw [Module.AEval.of_symm_smul, map_zero]
    exact Krylov.aeval_minpolyVec A v
  exact eq_of_dvd_of_natDegree_le_of_leadingCoeff hd
    (natDegree_le_of_dvd hd' hp.ne_zero) (hp.leadingCoeff.trans hm.leadingCoeff.symm)

omit [FiniteDimensional K V] in
private theorem basis_equivFun_apply_eq_jordanColumn {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e : ι → ℕ} {μ : ι → K}
    (A : End K V) (b : Basis ((i : ι) × Fin (e i)) K V)
    (hb : LinearMap.toMatrix b b A = Matrix.jordanForm e μ) (j : (i : ι) × Fin (e i)) :
    b.equivFun (A (b j)) = (Matrix.jordanForm e μ)ᵀ j := by
  funext i
  rw [Matrix.transpose_apply, ← hb, LinearMap.toMatrix_apply]
  rfl

private theorem eq_span_jordan_chain {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e : ι → ℕ} {μ : ι → K}
    (A : End K V) (b : Basis ((i : ι) × Fin (e i)) K V)
    (hb : LinearMap.toMatrix b b A = Matrix.jordanForm e μ) (i : ι) (hi : 0 < e i) :
    ∃ v : V, Krylov.grade A v = e i ∧ Krylov.minpolyVec A v = (X - C (μ i)) ^ e i ∧
      Krylov.fullSubspace A v = Submodule.span K (b '' {j | j.1 = i}) := by
  classical
  let w (j : ℕ) (hj : j < e i) := b ⟨i, ⟨j, hj⟩⟩
  let v := w (e i - 1) (by omega)
  let T := A - algebraMap K (End K V) (μ i)
  have hsingle (j : (i : ι) × Fin (e i)) : b.equivFun (b j) = Pi.single j 1 := by
    funext k
    simp [Basis.equivFun_self, Pi.single_apply, eq_comm]
  have hzero : T (w 0 hi) = 0 := by
    have ha : A (w 0 hi) = μ i • w 0 hi := by
      apply b.equivFun.injective
      dsimp only [w]
      rw [basis_equivFun_apply_eq_jordanColumn A b hb, Matrix.jordanForm_transpose_zero,
        map_smul, hsingle]
    simp [T, LinearMap.sub_apply, Module.algebraMap_end_apply, ha]
  have hstep (j : ℕ) (hj : j + 1 < e i) : T (w (j + 1) hj) = w j (by omega) := by
    have ha : A (w (j + 1) hj) = μ i • w (j + 1) hj + w j (by omega) := by
      apply b.equivFun.injective
      dsimp only [w]
      rw [basis_equivFun_apply_eq_jordanColumn A b hb, Matrix.jordanForm_transpose_succ,
        map_add, map_smul, hsingle, hsingle]
    simp [T, LinearMap.sub_apply, Module.algebraMap_end_apply, ha]
  have hpow (k : ℕ) (hk : k < e i) :
      (T ^ k) v = w (e i - 1 - k) (by omega) := by
    induction k with
    | zero => simp [v]
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih (by omega)]
      have he : e i - 1 - k = e i - 1 - (k + 1) + 1 := by omega
      have hw : w (e i - 1 - k) (by omega) =
          w (e i - 1 - (k + 1) + 1) (by omega) :=
        congrArg (fun j : Fin (e i) => b ⟨i, j⟩) (Fin.ext he)
      rw [hw, hstep]
  have hkill : (T ^ e i) v = 0 := by
    have hpow0 : (T ^ (e i - 1)) v = w 0 hi := by simpa using hpow (e i - 1) (by omega)
    nth_rw 1 [show e i = e i - 1 + 1 by omega]
    rw [pow_succ', Module.End.mul_apply, hpow0, hzero]
  have hLI : LinearIndependent K (fun k : Fin (e i) => (T ^ (k : ℕ)) v) := by
    let f (k : Fin (e i)) : (i : ι) × Fin (e i) := ⟨i, ⟨e i - 1 - k, by omega⟩⟩
    have hf : Function.Injective f := by
      intro x y h
      have he := congrArg (fun z : (j : ι) × Fin (e j) => (z.2 : ℕ)) h
      change e i - 1 - (x : ℕ) = e i - 1 - (y : ℕ) at he
      apply Fin.ext
      omega
    have heq : (fun k : Fin (e i) => (T ^ (k : ℕ)) v) = b ∘ f :=
      funext fun k => hpow k k.2
    rw [heq]
    exact b.linearIndependent.comp f hf
  have hgradeT : Krylov.grade T v = e i := by
    apply le_antisymm
    · exact (Krylov.grade_le_iff T v).2 (hkill ▸ (Submodule.zero_mem _))
    · by_contra! hlt
      exact (Krylov.linearIndependent_iff_forall_pow_notMem T v |>.1 hLI _ hlt)
        (Krylov.pow_grade_apply_mem T v)
  have hgrade : Krylov.grade A v = e i := by
    rw [← hgradeT]
    simpa [T, sub_eq_add_neg] using (Krylov.grade_add_algebraMap A v (-μ i)).symm
  have hspan : Krylov.fullSubspace A v = Submodule.span K (b '' {j | j.1 = i}) := by
    have heq : Krylov.fullSubspace A v = Krylov.fullSubspace T v := by
      simpa [T, sub_eq_add_neg] using (Krylov.fullSubspace_add_algebraMap A v (-μ i)).symm
    rw [heq, ← Krylov.subspace_grade_eq_fullSubspace, hgradeT, Krylov.subspace]
    congr 1
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      change (T ^ (k : ℕ)) v ∈ b '' {j | j.1 = i}
      rw [hpow (k : ℕ) k.2]
      exact ⟨⟨i, ⟨e i - 1 - k, by omega⟩⟩, rfl, rfl⟩
    · rintro ⟨⟨j, k⟩, hj, rfl⟩
      change j = i at hj
      subst j
      let m : Fin (e i) := ⟨e i - 1 - k, by omega⟩
      refine ⟨m, ?_⟩
      change (T ^ (m : ℕ)) v = b ⟨i, k⟩
      rw [hpow (m : ℕ) m.2]
      exact congrArg (fun a : Fin (e i) => b ⟨i, a⟩) (Fin.ext (by dsimp [m]; omega))
  refine ⟨v, hgrade, ?_, hspan⟩
  have hp : (Krylov.minpolyVec A v).Monic :=
    Krylov.minpolyVec_monic A v (Krylov.minpolyVec_ne_zero A v)
  have hq : ((X - C (μ i)) ^ e i).Monic := (monic_X_sub_C (μ i)).pow _
  refine eq_of_dvd_of_natDegree_le_of_leadingCoeff ?_ ?_
    (hp.leadingCoeff.trans hq.leadingCoeff.symm)
  · apply (Krylov.minpolyVec_dvd_iff A v).2
    simp only [map_pow, map_sub, aeval_X, aeval_C]
    exact hkill
  · rw [Krylov.natDegree_minpolyVec, hgrade, natDegree_pow, natDegree_X_sub_C, mul_one]

/-- A Jordan basis with positive block sizes $e_i$ and eigenvalues $\mu_i$ gives an internal
direct sum of full Krylov subspaces with generators of grade $e_i$ and minimal polynomial
$(X-\mu_i)^{e_i}$. -/
theorem exists_isInternal_primaryKrylov {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : End K V) (e : ι → ℕ) (μ : ι → K)
    (b : Basis ((i : ι) × Fin (e i)) K V) (he : ∀ i, 0 < e i)
    (hb : LinearMap.toMatrix b b A = Matrix.jordanForm e μ) :
    ∃ v : ι → V, (∀ i, Krylov.grade A (v i) = e i) ∧
      (∀ i, Krylov.minpolyVec A (v i) = (X - C (μ i)) ^ e i) ∧
      DirectSum.IsInternal (fun i => Krylov.fullSubspace A (v i)) := by
  classical
  choose v hv hpoly hs using fun i => eq_span_jordan_chain A b hb i (he i)
  refine ⟨v, hv, hpoly, ?_⟩
  simp_rw [hs]
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro i
    have hdisj : Disjoint {j : (k : ι) × Fin (e k) | j.1 = i} {j | j.1 ≠ i} :=
      Set.disjoint_left.2 fun _ hx hy => hy hx
    refine (b.linearIndependent.disjoint_span_image hdisj).mono_right ?_
    exact iSup_le fun j => iSup_le fun hj =>
      Submodule.span_mono (Set.image_mono fun x hx => hx.trans_ne hj)
  · apply top_unique
    rw [← b.span_eq, Submodule.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact le_iSup (fun i => Submodule.span K (b '' {x | x.1 = i})) i
      (Submodule.subset_span ⟨⟨i, j⟩, rfl, rfl⟩)

end Field

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

private theorem isOpen_setOf_fullGrade (A : End 𝕜 E) :
    IsOpen {v : E | Krylov.grade A v = (minpoly 𝕜 A).natDegree} := by
  let d := (minpoly 𝕜 A).natDegree
  let powers (v : E) (i : Fin d) := (A ^ (i : ℕ)) v
  have hcont : Continuous powers :=
    continuous_pi fun i => (A ^ (i : ℕ)).continuous_of_finiteDimensional
  have heq : {v : E | Krylov.grade A v = d} = powers ⁻¹' {f | LinearIndependent 𝕜 f} := by
    ext v
    change Krylov.grade A v = d ↔ LinearIndependent 𝕜 (powers v)
    refine ⟨fun h => Krylov.linearIndependent_of_le_grade A v h.ge, fun h => ?_⟩
    apply le_antisymm (grade_le_natDegree_minpoly A v)
    by_contra! hlt
    exact (Krylov.linearIndependent_iff_forall_pow_notMem A v |>.1 h _ hlt)
      (Krylov.pow_grade_apply_mem A v)
  rw [show (minpoly 𝕜 A).natDegree = d from rfl, heq]
  exact isOpen_setOfPred_linearIndependent.preimage hcont

variable {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]

/-- An endomorphism over the real or complex scalars has a basis consisting of vectors whose
grades all equal the degree of its minimal polynomial. -/
theorem exists_basis_fullGrade (A : End 𝕜 V) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) 𝕜 V),
      ∀ i, Krylov.grade A (b i) = (minpoly 𝕜 A).natDegree := by
  classical
  let e := (Module.finBasis 𝕜 V).equivFun
  let T := e.conjAlgEquiv 𝕜 A
  let S := {v | Krylov.grade T v = (minpoly 𝕜 T).natDegree}
  obtain ⟨w, hw⟩ := exists_minpolyVec_eq_minpoly T
  have hS : IsOpen S := isOpen_setOf_fullGrade T
  have hwS : w ∈ S := by
    change Krylov.grade T w = (minpoly 𝕜 T).natDegree
    rw [← Krylov.natDegree_minpolyVec T w, hw]
  have hspan : Submodule.span 𝕜 S = ⊤ := (Submodule.span 𝕜 S).eq_top_of_nonempty_interior'
    ⟨w, interior_mono Submodule.subset_span (hS.interior_eq.symm ▸ hwS)⟩
  let b := Module.Basis.ofSpan hspan.ge
  let := Fintype.ofFinite (linearIndepOn_empty 𝕜 id |>.extend (Set.empty_subset S))
  let ϵ := Fintype.equivFin (linearIndepOn_empty 𝕜 id |>.extend (Set.empty_subset S))
  refine ⟨_, (b.map e.symm).reindex ϵ, fun i => ?_⟩
  have hb := Module.Basis.ofSpan_subset hspan.ge ⟨ϵ.symm i, rfl⟩
  have hsem : Function.Semiconj e.toLinearMap A T := fun x => by
    simp [T, LinearEquiv.conjAlgEquiv_apply]
  have hgrade (v : V) : Krylov.grade A v = Krylov.grade T (e v) := by
    change Module.finrank 𝕜 (Krylov.fullSubspace A v) =
      Module.finrank 𝕜 (Krylov.fullSubspace T (e.toLinearMap v))
    rw [← Krylov.map_fullSubspace_of_semiconj hsem v]
    exact (Submodule.equivMapOfInjective _ e.injective _).finrank_eq
  rw [Module.Basis.reindex_apply, Module.Basis.map_apply, hgrade, e.apply_symm_apply,
    ← minpoly.algEquiv_eq (e.conjAlgEquiv 𝕜) A]
  exact hb

end RCLike
end Module.End
