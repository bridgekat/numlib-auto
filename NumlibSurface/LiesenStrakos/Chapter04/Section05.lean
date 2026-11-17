import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Numlib.Algebra.Polynomial.Commute
import Numlib.Eigen.Normal
import Numlib.Krylov.Coprime
import Numlib.Krylov.ShortRecurrence
import Numlib.LinearAlgebra.MinpolyOn
import NumlibSurface.LiesenStrakos.Chapter04.Section04

/-!
# Liesen and Strakoš, Section 4.5: Necessary conditions

Section 4.5 of [liesen2013krylov] uses continuity of an Arnoldi vector under variation of the
start when the corresponding iteration is before breakdown. The continuity of the unnormalized
Arnoldi vectors is established in `Numlib.Krylov.ShortRecurrence`.

## Main results

* Theorem 4.5.1, `LiesenStrakos.theorem_4_5_1`: normality of degree $s$ through spectral
  interpolation of conjugation.
* Lemma 4.5.2, `LiesenStrakos.lemma_4_5_2`: a short Krylov containment on all full-grade
  vectors implies a polynomial adjoint of bounded degree.
* Lemma 4.5.3, `LiesenStrakos.lemma_4_5_3`: continuous dependence along curves of
  sufficiently high grade.

* Theorem 4.5.4, `LiesenStrakos.theorem_4_5_4`: an optimal short recurrence forces the adjoint
  to be a polynomial of the corresponding degree in the operator.
-/

namespace LiesenStrakos

open Polynomial Module.End Krylov
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The finite set of distinct eigenvalues of a complex endomorphism. -/
noncomputable def distinctEigenvalues (A : Module.End ℂ E) : Finset ℂ :=
  (finite_hasEigenvalue A).toFinset

@[simp]
private theorem mem_distinctEigenvalues (A : Module.End ℂ E) (z : ℂ) :
    z ∈ distinctEigenvalues A ↔ A.HasEigenvalue z :=
  (finite_hasEigenvalue A).mem_toFinset

private theorem isStarNormal_of_orthonormal_eigenbasis (A : Module.End ℂ E) {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ E) (μ : Fin n → ℂ)
    (h : ∀ i, A (b i) = μ i • b i) : IsStarNormal A := by
  have ha (i : Fin n) : A.adjoint (b i) = star (μ i) • b i := by
    apply InnerProductSpace.ext_inner_left_basis b.toBasis
    intro j
    change inner ℂ (b j) (A.adjoint (b i)) = inner ℂ (b j) (star (μ i) • b i)
    rw [LinearMap.adjoint_inner_right, h j, inner_smul_left, inner_smul_right, b.inner_eq_ite]
    split_ifs with hij
    · subst j
      rfl
    · simp
  refine ⟨?_⟩
  rw [LinearMap.star_eq_adjoint]
  apply b.toBasis.ext
  intro i
  change A.adjoint (A (b i)) = A (A.adjoint (b i))
  rw [h i, ha i, map_smul, map_smul, h i, ha i, smul_smul, smul_smul, mul_comm]

private theorem card_distinctEigenvalues_of_eigenbasis (A : Module.End ℂ E) {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ E) (μ : Fin n → ℂ)
    (h : ∀ i, A (b i) = μ i • b i) :
    (distinctEigenvalues A).card = operatorMinimalDegree A := by
  classical
  let S := distinctEigenvalues A
  have hS (z : ℂ) : z ∈ S ↔ A.HasEigenvalue z := mem_distinctEigenvalues A z
  apply le_antisymm
  · apply card_le_degree_of_subset_roots
    intro z hz
    obtain ⟨v, hv⟩ := ((hS z).1 hz).exists_hasEigenvector
    have he := aeval_apply_of_mem_apply_eq_smul (p := minpoly ℂ A) hv.apply_eq_smul
    rw [minpoly.aeval, LinearMap.zero_apply] at he
    exact (mem_roots (minpoly.ne_zero_of_finite ℂ A)).2
      ((smul_eq_zero.1 he.symm).resolve_right hv.2)
  · let p := ∏ z ∈ S, (X - C z)
    have hp : p.Monic := monic_prod_of_monic _ _ fun z _ => monic_X_sub_C z
    have hdeg : p.natDegree = S.card := by
      simp [p, natDegree_prod_of_monic, monic_X_sub_C]
    have hzero : aeval A p = 0 := by
      apply b.toBasis.ext
      intro i
      have hμ : μ i ∈ S := (hS _).2 (hasEigenvalue_of_hasEigenvector
        ⟨mem_eigenspace_iff.2 (h i), b.toBasis.ne_zero i⟩)
      have he : p.eval (μ i) = 0 := by
        rw [show p = ∏ z ∈ S, (X - C z) from rfl, eval_prod]
        exact Finset.prod_eq_zero hμ (by simp)
      change aeval A p (b i) = 0
      rw [aeval_apply_of_mem_apply_eq_smul (h i), he, zero_smul]
    exact hdeg ▸ natDegree_le_of_dvd (minpoly.dvd ℂ A hzero) hp.ne_zero

private theorem aeval_eq_adjoint_iff_eval_eq {A : Module.End ℂ E} (hA : IsStarNormal A)
    (p : ℂ[X]) : aeval A p = A.adjoint ↔ ∀ z : ℂ, A.HasEigenvalue z → p.eval z = star z := by
  refine ⟨fun hp z hz => ?_, fun hp => LinearMap.IsStarNormal.aeval_eq_adjoint_of_eval_eq hA hp⟩
  obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
  have hmem : v ∈ eigenspace A.adjoint (starRingEnd ℂ z) := by
    rw [LinearMap.IsStarNormal.eigenspace_adjoint hA]
    exact hv.1
  have he : A.adjoint v = star z • v := mem_eigenspace_iff.1 hmem
  have hv' := congrArg (fun B : Module.End ℂ E => B v) hp
  rw [aeval_apply_of_mem_apply_eq_smul hv.apply_eq_smul, he] at hv'
  exact smul_left_injective ℂ hv.2 hv'

/-- An operator is normal of degree $s$ if and only if it admits an orthonormal eigenbasis,
the number of its distinct eigenvalues is $d_{\min}(A)$, and the conjugation values on
those eigenvalues have a unique least-degree interpolating polynomial of degree $s$.
This is Theorem 4.5.1 of [liesen2013krylov]. -/
theorem theorem_4_5_1 (A : Module.End ℂ E) (s : ℕ) :
    IsNormalOfDegree A s ↔
      ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E)
        (μ : Fin (Module.finrank ℂ E) → ℂ) (p : ℂ[X]),
        (∀ i, A (b i) = μ i • b i) ∧
        (distinctEigenvalues A).card = operatorMinimalDegree A ∧
        p.degree = s ∧ (∀ z : ℂ, A.HasEigenvalue z → p.eval z = star z) ∧
        ∀ q : ℂ[X], (∀ z : ℂ, A.HasEigenvalue z → q.eval z = star z) →
          (s : WithBot ℕ) ≤ q.degree ∧ (q.degree = s → q = p) := by
  constructor
  · intro hNormal
    have hbound := Polynomial.IsMinDegreeRepresentation.degree_lt_minpoly hNormal
      (IsIntegral.of_finite ℂ A)
    obtain ⟨p, hpdeg, hp, hmin⟩ := hNormal
    have hA : IsStarNormal A := by
      refine ⟨?_⟩
      rw [LinearMap.star_eq_adjoint, ← hp]
      exact (Commute.refl A).aeval_left p
    let b := LinearMap.IsStarNormal.eigenvectorBasis hA (rfl : Module.finrank ℂ E = _)
    let μ := LinearMap.IsStarNormal.eigenvalues hA (rfl : Module.finrank ℂ E = _)
    have h := LinearMap.IsStarNormal.apply_eigenvectorBasis hA (rfl : Module.finrank ℂ E = _)
    refine ⟨b, μ, p, h, card_distinctEigenvalues_of_eigenbasis A b μ h, hpdeg,
      (aeval_eq_adjoint_iff_eval_eq hA p).1 hp, ?_⟩
    intro q hq
    have hq' := (aeval_eq_adjoint_iff_eval_eq hA q).2 hq
    refine ⟨hmin q hq', fun hqdeg => ?_⟩
    apply sub_eq_zero.1
    by_contra h0
    have hz : aeval A (q - p) = 0 := by rw [map_sub, hp, hq', sub_self]
    apply (not_lt_of_ge (minpoly.degree_le_of_ne_zero ℂ A h0 hz))
    exact (degree_sub_le q p).trans_lt (by rw [hqdeg, hpdeg, max_self]; exact hbound)
  · rintro ⟨b, μ, p, hb, -, hpdeg, hp, hmin⟩
    have hA := isStarNormal_of_orthonormal_eigenbasis A b μ hb
    exact ⟨p, hpdeg, (aeval_eq_adjoint_iff_eval_eq hA p).2 hp,
      fun q hq => (hmin q ((aeval_eq_adjoint_iff_eval_eq hA q).1 hq)).1⟩

private theorem aeval_eq_zero_at_fullGrade (A : Module.End ℂ E) {v : E}
    (hv : vectorGrade A v = operatorMinimalDegree A) {p : ℂ[X]}
    (hd : p.natDegree < operatorMinimalDegree A) (hp : aeval A p v = 0) : p = 0 := by
  by_contra hn
  have h := natDegree_le_of_dvd ((Krylov.minpolyVec_dvd_iff A v).2 hp) hn
  rw [Krylov.natDegree_minpolyVec, show Krylov.grade A v = operatorMinimalDegree A from hv] at h
  exact hd.not_ge h

omit [FiniteDimensional ℂ E] in
private theorem grade_shift_apply (A : Module.End ℂ E) (z : ℂ) (hz : ¬ A.HasEigenvalue z)
    (v : E) :
    vectorGrade A ((A - algebraMap ℂ (Module.End ℂ E) z) v) = vectorGrade A v := by
  let Q := A - algebraMap ℂ (Module.End ℂ E) z
  have hq : Function.Injective Q := by
    refine LinearMap.ker_eq_bot.1 (bot_unique fun x hx => ?_)
    have hx' : A x = z • x := by
      simpa [Q, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] using
        (LinearMap.mem_ker.mp hx)
    rw [Submodule.mem_bot]
    by_contra hx0
    exact hz (hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.2 hx', hx0⟩)
  have hcomm : Commute Q A :=
    (Commute.refl A).sub_left (Algebra.commute_algebraMap_left z A)
  have hsem : Function.Semiconj Q A A :=
    fun x => congrArg (fun T : Module.End ℂ E => T x) hcomm.eq
  change Module.finrank ℂ (Krylov.fullSubspace A (Q v)) =
    Module.finrank ℂ (Krylov.fullSubspace A v)
  rw [← Krylov.map_fullSubspace_of_semiconj hsem v]
  exact (Submodule.equivMapOfInjective _ hq _).finrank_eq.symm

omit [FiniteDimensional ℂ E] in
private theorem exists_natDegree_aeval_of_mem {A : Module.End ℂ E} {v w : E} {s : ℕ}
    (h : w ∈ Krylov.subspace A v (s + 1)) :
    ∃ p : ℂ[X], p.natDegree ≤ s ∧ aeval A p v = w := by
  obtain ⟨p, hp, heval⟩ := (Krylov.mem_subspace_iff_exists_aeval A v).1 h
  refine ⟨p, ?_, heval⟩
  by_cases h0 : p = 0
  · simp [h0]
  · rw [degree_eq_natDegree h0] at hp
    exact Nat.lt_succ_iff.mp (WithBot.coe_lt_coe.mp hp)

private theorem commute_of_fullGrade_mem_subspace (A B : Module.End ℂ E) {s : ℕ}
    (hs : s + 2 ≤ operatorMinimalDegree A)
    (hB : ∀ v, vectorGrade A v = operatorMinimalDegree A →
      B v ∈ Krylov.subspace A v (s + 1)) : Commute B A := by
  classical
  let Q (z : ℂ) := A - algebraMap ℂ (Module.End ℂ E) z
  obtain ⟨c, hc⟩ := (finite_hasEigenvalue A).exists_notMem
  have hc' : ¬ A.HasEigenvalue c := hc
  have hloc (v : E) (hv : vectorGrade A v = operatorMinimalDegree A) :
      ∃ p : ℂ[X], p.natDegree ≤ s ∧ aeval A p v = B v :=
    exists_natDegree_aeval_of_mem (hB v hv)
  have hshift (z : ℂ) (hz : ¬ A.HasEigenvalue z) (v : E)
      (hv : vectorGrade A v = operatorMinimalDegree A) :
      ∃ p : ℂ[X], p.natDegree ≤ s ∧ aeval A p (Q z v) = B (Q z v) :=
    hloc (Q z v) ((grade_shift_apply A z hz v).trans hv)
  obtain ⟨n, b, hgrade⟩ := A.exists_basis_fullGrade
  apply b.ext
  intro i
  set v := b i
  have hv : vectorGrade A v = operatorMinimalDegree A := hgrade i
  obtain ⟨r, hrdeg, hr⟩ := hloc v hv
  obtain ⟨q, hqdeg, hq⟩ := hshift c hc' v hv
  have hQpoly (z : ℂ) : aeval A (X - C z) = Q z := by simp [Q]
  have hQapply (z : ℂ) (x : E) : Q z x = A x - z • x := by
    simp only [Q, LinearMap.sub_apply, Module.algebraMap_end_apply]
  have hqr : q = r := by
    by_contra hne
    have hf : ({z : ℂ | A.HasEigenvalue z} ∪ {c} ∪ {z | (q - r).IsRoot z}).Finite :=
      ((finite_hasEigenvalue A).union (Set.finite_singleton c)).union
        (finite_setOfPred_isRoot (sub_ne_zero.mpr hne))
    obtain ⟨z, hz⟩ := hf.exists_notMem
    have hzA : ¬ A.HasEigenvalue z := fun h => hz (Or.inl (Or.inl h))
    have hzc : z ≠ c := fun h => hz (Or.inl (Or.inr h))
    have hzroot : ¬ (q - r).IsRoot z := fun h => hz (Or.inr h)
    obtain ⟨p, hpdeg, hp⟩ := hshift z hzA v hv
    let t := p * (X - C z) - q * (X - C c) - C (c - z) * r
    have hdeg (p' : ℂ[X]) (z' : ℂ) (hp' : p'.natDegree ≤ s) :
        (p' * (X - C z')).natDegree ≤ s + 1 := by
      have h := natDegree_mul_le (p := p') (q := X - C z')
      rw [natDegree_X_sub_C] at h
      omega
    have hlast : (C (c - z) * r).natDegree ≤ s + 1 := by
      have h := natDegree_mul_le (p := C (c - z)) (q := r)
      rw [natDegree_C, zero_add] at h
      omega
    have htd : t.natDegree ≤ s + 1 := by
      have h := natDegree_sub_le_of_le
        (natDegree_sub_le_of_le (hdeg p z hpdeg) (hdeg q c hqdeg)) hlast
      simpa [t] using h
    have heval : aeval A t v = 0 := by
      simp only [t, map_sub, map_mul, LinearMap.sub_apply, Module.End.mul_apply, hQpoly,
        aeval_C, Module.algebraMap_end_apply, hp, hq, hr]
      have he : Q z v = Q c v + (c - z) • v := by
        rw [hQapply, hQapply, sub_smul]
        abel
      rw [he, map_add, map_smul]
      module
    have ht := aeval_eq_zero_at_fullGrade A hv (show t.natDegree < operatorMinimalDegree A by
      omega) heval
    have htz := congrArg (fun f : ℂ[X] => f.eval z) ht
    simp only [t, eval_sub, eval_mul, eval_X, eval_C, eval_zero, sub_self, mul_zero, zero_sub]
      at htz
    have he : (z - c) * (q.eval z - r.eval z) = 0 := by linear_combination -htz
    exact hzroot (by simpa only [IsRoot, eval_sub] using
      (mul_eq_zero.1 he).resolve_left (sub_ne_zero.mpr hzc))
  have hcomm : Commute (aeval A r) (Q c) :=
    ((Commute.refl A).sub_right (Algebra.commute_algebraMap_right c A)).aeval_left r
  have h : B (Q c v) = Q c (B v) := by
    rw [← hq, hqr, ← hr]
    exact congrArg (fun T : Module.End ℂ E => T v) hcomm.eq
  rw [hQapply, hQapply, map_sub, map_smul] at h
  calc
    B (A v) = B (A v) - c • B v + c • B v := by abel
    _ = A (B v) - c • B v + c • B v := by rw [h]
    _ = A (B v) := by abel

/-- Suppose $s+2\le d_{\min}(A)$ and $A^*v\in\mathcal K_{s+1}(A,v)$ whenever
$v$ has full grade. Then $A$ is normal of some degree at most $s$.
This is Lemma 4.5.2 of [liesen2013krylov]. -/
theorem lemma_4_5_2 (A : Module.End ℂ E) (s : ℕ) (hs : s + 2 ≤ operatorMinimalDegree A)
    (hA : ∀ v, vectorGrade A v = operatorMinimalDegree A →
      A.adjoint v ∈ Krylov.subspace A v (s + 1)) :
    ∃ t ≤ s, IsNormalOfDegree A t := by
  have hNormal : IsStarNormal A := ⟨by
    rw [LinearMap.star_eq_adjoint]
    exact commute_of_fullGrade_mem_subspace A A.adjoint hs hA⟩
  obtain ⟨f, hf⟩ := LinearMap.IsStarNormal.exists_aeval_eq_adjoint hNormal
  let p := f %ₘ minpoly ℂ A
  have hp : aeval A p = A.adjoint := by simpa [p] using hf
  have hA' : A.adjoint ≠ 0 := by
    intro h
    have hzero : A = 0 := by
      simpa using congrArg (LinearMap.adjoint (𝕜 := ℂ)) h
    have hd : (minpoly ℂ A).natDegree ≤ 1 := by
      have hz : aeval A (X : ℂ[X]) = 0 := by simp [hzero]
      simpa using natDegree_le_of_dvd (minpoly.dvd ℂ A hz) X_ne_zero
    change s + 2 ≤ (minpoly ℂ A).natDegree at hs
    omega
  have hp0 : p ≠ 0 := by
    intro h
    exact hA' (by rw [h, map_zero] at hp; exact hp.symm)
  have hdeg : p.natDegree < operatorMinimalDegree A := by
    have hd := degree_modByMonic_lt f (minpoly.monic (IsIntegral.of_finite ℂ A))
    change p.degree < (minpoly ℂ A).degree at hd
    rw [degree_eq_natDegree hp0, degree_eq_natDegree (minpoly.ne_zero_of_finite ℂ A)] at hd
    exact WithBot.coe_lt_coe.mp hd
  obtain ⟨v, hv⟩ := A.exists_minpolyVec_eq_minpoly
  have hgrade : vectorGrade A v = operatorMinimalDegree A := by
    change Krylov.grade A v = (minpoly ℂ A).natDegree
    rw [← Krylov.natDegree_minpolyVec, hv]
  obtain ⟨q, hqdeg, hq⟩ := exists_natDegree_aeval_of_mem (hA v hgrade)
  have heq : p = q := by
    apply sub_eq_zero.1
    refine aeval_eq_zero_at_fullGrade A hgrade
      ((natDegree_sub_le _ _).trans_lt (max_lt hdeg (lt_of_le_of_lt hqdeg (by omega)))) ?_
    rw [map_sub, LinearMap.sub_apply, hp, hq, sub_self]
  refine ⟨p.natDegree, heq ▸ hqdeg, p, degree_eq_natDegree hp0, hp, ?_⟩
  intro r hr
  by_contra! hlt
  have hr0 : r ≠ 0 := by
    intro h
    exact hA' (by rw [h, map_zero] at hr; exact hr.symm)
  rw [degree_eq_natDegree hr0] at hlt
  have hlt' : r.natDegree < p.natDegree := WithBot.coe_lt_coe.mp hlt
  have heq' : r = p := by
    apply sub_eq_zero.1
    refine aeval_eq_zero_at_fullGrade A hgrade
      ((natDegree_sub_le _ _).trans_lt (max_lt (hlt'.trans hdeg) hdeg)) ?_
    rw [map_sub, LinearMap.sub_apply, hp, hr, sub_self]
  exact hlt'.ne (congrArg natDegree heq')

/-- Let $v(\gamma)$ be a continuous family of initial vectors. If every start has grade
at least $j+1$, then the unnormalized Arnoldi vector of index $j$ is continuous in $\gamma$.
The Arnoldi vectors are indexed from zero. This is Lemma 4.5.3 of [liesen2013krylov]. -/
theorem lemma_4_5_3 (A : Module.End ℂ E) (v : ℂ → E) (hv : Continuous v)
    (j : ℕ) (hgrade : ∀ γ, j < Krylov.grade A (v γ)) :
    Continuous (fun γ => Arnoldi.orthogonalVec A (v γ) j) := by
  refine continuous_iff_continuousAt.2 fun γ => ?_
  exact (Arnoldi.continuousAt_orthogonalVec A (v γ) (hgrade γ)).comp hv.continuousAt

/-- A degree-$(s + 2)$ cyclic restriction of a uniform bandwidth-$s$ operator is normal
of degree at most $s$. -/
private theorem exists_normal_restrict_fullSubspace (A : Module.End ℂ E) {s : ℕ}
    (hmin : s + 2 < operatorMinimalDegree A)
    (h : ∀ v : E, Arnoldi.HasUpperBandwidth A v s) (u : E) (hu : grade A u = s + 2)
    (hW : Set.MapsTo A (fullSubspace A u) (fullSubspace A u)) :
    ∃ t ≤ s, IsNormalOfDegree (A.restrict hW) t := by
  let W := fullSubspace A u
  let T := A.restrict hW
  have hTdeg : operatorMinimalDegree T = s + 2 := by
    change (A.minpolyOn W hW).natDegree = _
    rw [LinearMap.minpolyOn_fullKrylovSubspace A u hW, natDegree_minpolyVec, hu]
  have hdim : Module.finrank ℂ W = s + 2 := hu
  apply lemma_4_5_2 T s hTdeg.ge
  intro v hv
  change grade T v = operatorMinimalDegree T at hv
  have hvgrade : grade T v = s + 2 := hv.trans hTdeg
  have he : Function.Semiconj W.subtypeₗᵢ T A := fun _ => rfl
  have hmap : grade A (v : E) = grade T v := by
    change Module.finrank ℂ (fullSubspace A (W.subtype v)) = Module.finrank ℂ (fullSubspace T v)
    rw [← map_fullSubspace_of_semiconj (N := W.subtype) he]
    exact (Submodule.equivMapOfInjective W.subtype Subtype.val_injective _).finrank_eq.symm
  have hcoeff : Arnoldi.coeff T v 0 (s + 1) = 0 :=
    (Arnoldi.coeff_map_linearIsometry W.subtypeₗᵢ he v 0 (s + 1)).symm.trans
      (Arnoldi.coeff_zero_of_uniform_hasUpperBandwidth hmin h (v : E) (hmap.trans hvgrade).ge)
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [grade_zero] at hvgrade
    omega
  have hzv : ((‖v‖⁻¹ : ℂ) : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr hv0)
  rw [Arnoldi.coeff, Arnoldi.vec_zero T v hv0, inner_smul_left] at hcoeff
  have hlast : inner ℂ (Arnoldi.vec T v (s + 1)) (T.adjoint v) = 0 := by
    rw [LinearMap.adjoint_inner_right, ← inner_conj_symm,
      (mul_eq_zero.mp hcoeff).resolve_left (star_ne_zero.mpr hzv), map_zero]
  have htop : subspace T v (s + 2) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_subspace, hvgrade, hdim, min_self]
  have hmem : T.adjoint v ∈ subspace T v (s + 2) := htop ▸ Submodule.mem_top
  have hsum := Arnoldi.eq_sum_inner_smul_vec T v hmem
  rw [Finset.sum_range_succ, hlast, zero_smul, add_zero] at hsum
  change T.adjoint v ∈ subspace T v (s + 1)
  rw [hsum]
  exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
    (Arnoldi.vec_mem_subspace_of_lt T v (Finset.mem_range.mp hi))

section MonicDivisors

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- A split monic polynomial has a monic divisor of every degree up to its own degree. -/
private theorem exists_monic_dvd_natDegree_eq (p : K[X]) (hp : p.Monic) (k : ℕ)
    (hk : k ≤ p.natDegree) : ∃ q : K[X], q.Monic ∧ q.natDegree = k ∧ q ∣ p := by
  induction k generalizing p with
  | zero => exact ⟨1, monic_one, natDegree_one, one_dvd _⟩
  | succ k ih =>
    have hpos : 0 < p.natDegree := by omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root p (natDegree_pos_iff_degree_pos.1 hpos).ne'
    obtain ⟨r, hr⟩ := dvd_iff_isRoot.2 hz
    have hrm : r.Monic := (monic_X_sub_C z).of_mul_monic_left (hr ▸ hp)
    have hdeg : p.natDegree = 1 + r.natDegree := by
      rw [hr, natDegree_mul (X_sub_C_ne_zero z) hrm.ne_zero, natDegree_X_sub_C]
    obtain ⟨t, htm, htdeg, ht⟩ := ih r hrm (by omega)
    refine ⟨(X - C z) * t, (monic_X_sub_C z).mul htm, ?_, ?_⟩
    · rw [natDegree_mul (X_sub_C_ne_zero z) htm.ne_zero, natDegree_X_sub_C, htdeg]
      omega
    · exact hr.symm ▸ mul_dvd_mul_left _ ht

end MonicDivisors

private theorem distinctEigenvalues_eq_roots_toFinset (A : Module.End ℂ E) :
    distinctEigenvalues A = (minpoly ℂ A).roots.toFinset := by
  ext z
  rw [distinctEigenvalues, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Multiset.mem_toFinset,
    mem_roots (minpoly.ne_zero_of_finite ℂ A), hasEigenvalue_iff_isRoot]

private theorem minpoly_squarefree_of_normalOfDegree {A : Module.End ℂ E} {s : ℕ}
    (h : IsNormalOfDegree A s) : Squarefree (minpoly ℂ A) := by
  obtain ⟨-, -, -, -, hcard, -⟩ := (theorem_4_5_1 A s).1 h
  change (distinctEigenvalues A).card = (minpoly ℂ A).natDegree at hcard
  rw [distinctEigenvalues_eq_roots_toFinset,
    (IsAlgClosed.splits (minpoly ℂ A)).natDegree_eq_card_roots] at hcard
  exact ((nodup_roots_iff_of_splits (minpoly.ne_zero_of_finite ℂ A) (IsAlgClosed.splits _)).1
    (Multiset.toFinset_card_eq_card_iff_nodup.1 hcard)).squarefree

/-- Uniform short Arnoldi bandwidth and sufficient minimal degree imply a squarefree
minimal polynomial. -/
private theorem squarefree_minpoly_of_uniform_hasUpperBandwidth (A : Module.End ℂ E) {s : ℕ}
    (hmin : s + 2 < operatorMinimalDegree A) (h : ∀ v, Arnoldi.HasUpperBandwidth A v s) :
    Squarefree (minpoly ℂ A) := by
  let m := minpoly ℂ A
  have hm : m.Monic := minpoly.monic (IsIntegral.of_finite ℂ A)
  intro r hr
  by_contra hru
  have hr0 : r ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul, zero_dvd_iff] at hr
    exact hm.ne_zero hr
  have hrdeg : r.degree ≠ 0 := by
    intro hdeg
    have hC := eq_C_of_natDegree_eq_zero (natDegree_eq_of_degree_eq_some hdeg)
    have hc : r.coeff 0 ≠ 0 := by
      intro hc
      exact hr0 (by simpa [hc] using hC)
    exact hru (hC ▸ (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)))
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root r hrdeg
  let p : ℂ[X] := X - C z
  have hp : p.Monic := monic_X_sub_C z
  have hpd : p.natDegree = 1 := natDegree_X_sub_C z
  have hpm : p * p ∣ m := (mul_dvd_mul (dvd_iff_isRoot.2 hz) (dvd_iff_isRoot.2 hz)).trans hr
  obtain ⟨r', hr'⟩ := hpm
  have hr'm : r'.Monic := (hp.mul hp).of_mul_monic_left (hr' ▸ hm)
  have hmdeg : m.natDegree = 2 + r'.natDegree := by
    rw [hr', natDegree_mul (hp.mul hp).ne_zero hr'm.ne_zero,
      natDegree_mul hp.ne_zero hp.ne_zero, hpd]
  change s + 2 < m.natDegree at hmin
  obtain ⟨q, hq, hqdeg, hqr'⟩ := exists_monic_dvd_natDegree_eq r' hr'm s (by omega)
  let p' := p * p * q
  have hp' : p'.Monic := (hp.mul hp).mul hq
  have hp'deg : p'.natDegree = s + 2 := by
    change (p * p * q).natDegree = _
    rw [natDegree_mul (hp.mul hp).ne_zero hq.ne_zero, natDegree_mul hp.ne_zero hp.ne_zero,
      hpd, hqdeg]
    omega
  have hp'div : p' ∣ m := hr'.symm ▸ mul_dvd_mul_left _ hqr'
  obtain ⟨u, hu⟩ := Krylov.exists_minpolyVec_eq_of_monic_dvd A hp' hp'div
  have hugrade : Krylov.grade A u = s + 2 := by rw [← Krylov.natDegree_minpolyVec, hu, hp'deg]
  let hW := (Module.End.mem_invtSubmodule_iff_mapsTo A).1
    (Krylov.fullSubspace_mem_invtSubmodule A u)
  obtain ⟨t, -, ht⟩ := exists_normal_restrict_fullSubspace A hmin h u hugrade hW
  have hsq := minpoly_squarefree_of_normalOfDegree ht
  change Squarefree (A.minpolyOn (fullSubspace A u) hW) at hsq
  rw [LinearMap.minpolyOn_fullKrylovSubspace A u hW, hu] at hsq
  exact (not_isUnit_of_natDegree_pos p (by rw [hpd]; decide)) (hsq p (dvd_mul_right _ _))

private theorem minpolyVec_of_eigenvector {A : Module.End ℂ E} {z : ℂ} {x : E}
    (hx : A.HasEigenvector z x) : minpolyVec A x = X - C z := by
  have hp : (minpolyVec A x).Monic := minpolyVec_monic A x (minpolyVec_ne_zero A x)
  have hdiv := (minpolyVec_dvd_iff A x (p := X - C z)).2 (by
    simp [hx.apply_eq_smul])
  have hdegree := grade_pos_of_ne_zero A x hx.2
  rw [← natDegree_minpolyVec] at hdegree
  exact eq_of_dvd_of_natDegree_le_of_leadingCoeff hdiv (by rw [natDegree_X_sub_C]; omega)
    (hp.leadingCoeff.trans (monic_X_sub_C z).leadingCoeff.symm)

private theorem local_spectralData (A : Module.End ℂ E) {s : ℕ}
    (hmin : s + 2 < operatorMinimalDegree A) (h : ∀ v, Arnoldi.HasUpperBandwidth A v s)
    (S : Finset ℂ) (hcard : S.card = s + 2) (v : S → E)
    (hv : ∀ i : S, A.HasEigenvector (i : ℂ) (v i)) :
    ∃ p : ℂ[X], p.degree ≤ s ∧ (∀ i : S, p.eval (i : ℂ) = star (i : ℂ)) ∧
      ∀ i j : S, i ≠ j → inner ℂ (v i) (v j) = 0 := by
  classical
  let u := ∑ i : S, v i
  let W := fullSubspace A u
  have hcop : Pairwise fun i j : S => IsCoprime (minpolyVec A (v i)) (minpolyVec A (v j)) := by
    intro i j hij
    rw [minpolyVec_of_eigenvector (hv i), minpolyVec_of_eigenvector (hv j)]
    exact isCoprime_X_sub_C_of_isUnit_sub ((sub_ne_zero.mpr (fun h => hij (Subtype.ext h))).isUnit)
  obtain ⟨hpoly, hspan⟩ := minpolyVec_fullSubspace_finsetSum_of_pairwise_isCoprime A v hcop Finset.univ
  have hgrade : grade A u = s + 2 := by
    rw [← natDegree_minpolyVec]
    change (minpolyVec A (∑ i : S, v i)).natDegree = _
    rw [hpoly]
    simp only [fun i : S => minpolyVec_of_eigenvector (hv i)]
    simpa only [natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ, Fintype.card_coe] using hcard
  have hmem (i : S) : v i ∈ W := by
    change v i ∈ fullSubspace A (∑ j : S, v j)
    rw [hspan]
    refine Finset.le_sup (f := fun j => fullSubspace A (v j)) (Finset.mem_univ i) ?_
    exact subspace_le_fullSubspace A (v i) 1 (self_mem_subspace A (v i) (by decide))
  let hW := (Module.End.mem_invtSubmodule_iff_mapsTo A).1 (fullSubspace_mem_invtSubmodule A u)
  let T : Module.End ℂ W := A.restrict hW
  let w (i : S) : W := ⟨v i, hmem i⟩
  have hw (i : S) : T.HasEigenvector (i : ℂ) (w i) := by
    refine ⟨mem_eigenspace_iff.2 (Subtype.ext (hv i).apply_eq_smul), ?_⟩
    intro hzero
    exact (hv i).2 (congrArg Subtype.val hzero)
  obtain ⟨t, ht, hp⟩ := exists_normal_restrict_fullSubspace A hmin h u hgrade hW
  obtain ⟨p, hpd, hp, -⟩ := hp
  change aeval T p = T.adjoint at hp
  have hnormal : IsStarNormal T := ⟨by
    rw [LinearMap.star_eq_adjoint, ← hp]
    exact (Commute.refl T).aeval_left p⟩
  refine ⟨p, hpd.trans_le (WithBot.coe_le_coe.mpr ht), ?_, ?_⟩
  · intro i
    have hwp := aeval_apply_of_mem_apply_eq_smul (p := p) (hw i).apply_eq_smul
    have hadj : T.adjoint (w i) = star (i : ℂ) • w i := by
      apply mem_eigenspace_iff.1
      change w i ∈ eigenspace T.adjoint (starRingEnd ℂ (i : ℂ))
      rw [LinearMap.IsStarNormal.eigenspace_adjoint hnormal]
      exact (hw i).1
    rw [hp, hadj] at hwp
    exact (smul_left_injective ℂ (hw i).2 hwp).symm
  · intro i j hij
    exact LinearMap.IsStarNormal.inner_eq_zero_of_ne hnormal
      (fun heq => hij (Subtype.ext heq)) (hw i).1 (hw j).1

private theorem interpolation_on_card_eq (A : Module.End ℂ E) {s : ℕ}
    (hmin : s + 2 < operatorMinimalDegree A) (h : ∀ v, Arnoldi.HasUpperBandwidth A v s)
    {S : Finset ℂ} (hcard : S.card = s + 2) (hS : S ⊆ distinctEigenvalues A) :
    ∃ p : ℂ[X], p.degree ≤ s ∧ ∀ z ∈ S, p.eval z = star z := by
  classical
  have hex (i : S) : ∃ v, A.HasEigenvector (i : ℂ) v :=
    ((mem_distinctEigenvalues _ _).1 (hS i.2)).exists_hasEigenvector
  choose v hv using hex
  obtain ⟨p, hd, heval, -⟩ := local_spectralData A hmin h S hcard v hv
  exact ⟨p, hd, fun z hz => heval ⟨z, hz⟩⟩

private theorem interpolation_of_uniform_bandwidth (A : Module.End ℂ E) {s : ℕ}
    (hmin : s + 2 < operatorMinimalDegree A) (h : ∀ v, Arnoldi.HasUpperBandwidth A v s)
    (hcard : (distinctEigenvalues A).card = operatorMinimalDegree A) :
    ∃ p : ℂ[X], p.degree ≤ s ∧ ∀ z, A.HasEigenvalue z → p.eval z = star z := by
  classical
  let S := distinctEigenvalues A
  have hle : s + 1 ≤ S.card := by change s + 1 ≤ (distinctEigenvalues A).card; rw [hcard]; omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hle
  have hlt : T.card < S.card := by change T.card < (distinctEigenvalues A).card; rw [hTcard, hcard]; omega
  obtain ⟨z₀, hz₀, hz₀T⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have interp (z : ℂ) (hz : z ∈ S) (hzT : z ∉ T) :
      ∃ q : ℂ[X], q.degree ≤ s ∧ ∀ w ∈ insert z T, q.eval w = star w :=
    interpolation_on_card_eq A hmin h (by rw [Finset.card_insert_of_notMem hzT, hTcard])
      (Finset.insert_subset hz hT)
  obtain ⟨p, hp, hpeval⟩ := interp z₀ hz₀ hz₀T
  refine ⟨p, hp, ?_⟩
  intro z hz
  have hzS : z ∈ S := (mem_distinctEigenvalues A z).2 hz
  by_cases hzT : z ∈ T
  · exact hpeval z (Finset.mem_insert_of_mem hzT)
  · obtain ⟨q, hq, hqeval⟩ := interp z hzS hzT
    have heq : p = q := by
      by_contra hne
      have h0 := sub_ne_zero.mpr hne
      have hroots : T.val ⊆ (p - q).roots := by
        intro w hw
        apply (mem_roots h0).2
        simp [IsRoot, hpeval w (Finset.mem_insert_of_mem hw),
          hqeval w (Finset.mem_insert_of_mem hw)]
      have h1 := card_le_degree_of_subset_roots hroots
      have h2 := (degree_sub_le p q).trans (max_le hp hq)
      rw [degree_eq_natDegree h0] at h2
      have h3 : (p - q).natDegree ≤ s := WithBot.coe_le_coe.mp h2
      rw [hTcard] at h1
      omega
    rw [heq]
    exact hqeval z (Finset.mem_insert_self _ _)

private theorem eigenspaces_orthogonal_of_uniform_bandwidth (A : Module.End ℂ E) {s : ℕ}
    (hmin : s + 2 < operatorMinimalDegree A) (h : ∀ v, Arnoldi.HasUpperBandwidth A v s)
    (hcard : (distinctEigenvalues A).card = operatorMinimalDegree A)
    {a b : ℂ} (hab : a ≠ b) {x y : E}
    (hx : x ∈ eigenspace A a) (hy : y ∈ eigenspace A b) : inner ℂ x y = 0 := by
  classical
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  have ha : A.HasEigenvector a x := ⟨hx, hx0⟩
  have hb : A.HasEigenvector b y := ⟨hy, hy0⟩
  let S := distinctEigenvalues A
  have haS : a ∈ S := (mem_distinctEigenvalues _ _).2 (hasEigenvalue_of_hasEigenvector ha)
  have hbS : b ∈ S := (mem_distinctEigenvalues _ _).2 (hasEigenvalue_of_hasEigenvector hb)
  have habS : {a, b} ⊆ S := Finset.insert_subset haS (Finset.singleton_subset_iff.2 hbS)
  have hle : s + 2 ≤ S.card := by change s + 2 ≤ (distinctEigenvalues A).card; rw [hcard]; omega
  obtain ⟨T, habT, hT, hTcard⟩ := Finset.exists_subsuperset_card_eq habS
    (by rw [Finset.card_insert_of_notMem (by simpa), Finset.card_singleton]; omega) hle
  have haT : a ∈ T := habT (Finset.mem_insert_self _ _)
  have hbT : b ∈ T := habT (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hex (i : T) : ∃ v, A.HasEigenvector (i : ℂ) v :=
    ((mem_distinctEigenvalues _ _).1 (hT i.2)).exists_hasEigenvector
  choose w hw using hex
  let v (i : T) : E := if (i : ℂ) = a then x else if (i : ℂ) = b then y else w i
  have hv (i : T) : A.HasEigenvector (i : ℂ) (v i) := by
    dsimp [v]
    split_ifs with hia hib
    · rwa [hia]
    · rwa [hib]
    · exact hw i
  obtain ⟨-, -, -, ho⟩ := local_spectralData A hmin h T hTcard v hv
  have hxy := ho ⟨a, haT⟩ ⟨b, hbT⟩ (fun heq => hab (congrArg Subtype.val heq))
  simpa [v, hab.symm] using hxy

private theorem aeval_eq_adjoint_of_orthogonal_eigenspaces (A : Module.End ℂ E)
    (hspan : ⨆ z : ℂ, eigenspace A z = ⊤)
    (horth : ∀ {a b : ℂ}, a ≠ b → ∀ {x y : E},
      x ∈ eigenspace A a → y ∈ eigenspace A b → inner ℂ x y = 0)
    (p : ℂ[X]) (hp : ∀ z, A.HasEigenvalue z → p.eval z = star z) :
    aeval A p = A.adjoint := by
  apply (LinearMap.eq_adjoint_iff _ _).2
  have hall (x : E) : x ∈ ⨆ z : ℂ, eigenspace A z := hspan ▸ Submodule.mem_top
  have hpair (a b : ℂ) (x y : E) (hx : x ∈ eigenspace A a) (hy : y ∈ eigenspace A b) :
      inner ℂ (aeval A p x) y = inner ℂ x (A y) := by
    by_cases hx0 : x = 0
    · simp [hx0]
    rw [aeval_apply_of_mem_apply_eq_smul (mem_eigenspace_iff.1 hx),
      hp a (hasEigenvalue_of_hasEigenvector ⟨hx, hx0⟩), mem_eigenspace_iff.1 hy,
      inner_smul_left, inner_smul_right]
    change star (star a) * inner ℂ x y = b * inner ℂ x y
    rw [star_star]
    by_cases hab : a = b
    · rw [hab]
    · simp [horth hab hx hy]
  intro x y
  refine Submodule.iSup_induction _ (motive := fun x => inner ℂ (aeval A p x) y = inner ℂ x (A y))
    (hall x) ?_ (by simp) ?_
  · intro a v hv
    refine Submodule.iSup_induction _
      (motive := fun y => inner ℂ (aeval A p v) y = inner ℂ v (A y))
      (hall y) (fun b w hw => hpair a b v w hv hw) (by simp) ?_
    intro v₁ v₂ h₁ h₂
    simp only [map_add, inner_add_right, h₁, h₂]
  · intro v₁ v₂ h₁ h₂
    simp only [map_add, inner_add_left, h₁, h₂]

/-- If an operator admits an optimal $(s + 2)$-term recurrence and
$s + 2<d_{\min}(A)$, its adjoint is a polynomial in the operator of least degree $s$.
This is Theorem 4.5.4 of [liesen2013krylov]. -/
theorem theorem_4_5_4 (A : Module.End ℂ E) {s : ℕ}
    (hmin : s + 2 < operatorMinimalDegree A) (h : AdmitsOptimalRecurrence A s) :
    IsNormalOfDegree A s := by
  obtain ⟨hband, w, hopt⟩ := h
  have hsquare := squarefree_minpoly_of_uniform_hasUpperBandwidth A hmin hband
  have hsemi := isSemisimple_of_squarefree_aeval_eq_zero hsquare (minpoly.aeval ℂ A)
  have hcard : (distinctEigenvalues A).card = operatorMinimalDegree A := by
    change _ = (minpoly ℂ A).natDegree
    rw [distinctEigenvalues_eq_roots_toFinset,
      (IsAlgClosed.splits (minpoly ℂ A)).natDegree_eq_card_roots]
    exact Multiset.toFinset_card_of_nodup (nodup_roots (PerfectField.separable_iff_squarefree.2 hsquare))
  obtain ⟨p, hpdeg, hpeval⟩ := interpolation_of_uniform_bandwidth A hmin hband hcard
  have hp := aeval_eq_adjoint_of_orthogonal_eigenspaces A hsemi.iSup_eigenspace_eq_top
    (fun {a b} hab {x y} hx hy =>
      eigenspaces_orthogonal_of_uniform_bandwidth A hmin hband hcard (a := a) (b := b)
        hab (x := x) (y := y) hx hy)
    p hpeval
  have hlocal (v : E) (_ : vectorGrade A v = operatorMinimalDegree A) :
      A.adjoint v ∈ subspace A v (s + 1) := by
    rw [← hp]
    exact aeval_apply_mem_subspace A v (hpdeg.trans_lt (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self s)))
  obtain ⟨t, ht, htA⟩ := lemma_4_5_2 A s (by omega) hlocal
  have hts : s ≤ t := by
    by_contra hn
    obtain ⟨i, j, hij, hne⟩ := hopt.2.2.2.2
    have htband := (theorem_4_4_3 A (show t + 2 < operatorMinimalDegree A by omega) htA).1 w
    exact hne (htband i j (by omega))
  exact (le_antisymm ht hts) ▸ htA

end LiesenStrakos
