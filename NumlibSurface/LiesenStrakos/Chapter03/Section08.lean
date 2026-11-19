/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.CG
import Numlib.Projection.Optimality

/-!
# Matching moments and projection processes

Before CG terminates, its residual is a scaled orthogonal component of the next Krylov
vector. Section 3.8 of [liesen2013krylov] uses this component to express the oblique
decomposition of the initial residual.

## Main results

* `LiesenStrakos.Chapter03.theorem_3_8_1` relates the CG residual to the Vorobyev projection
  and gives the two terms of the corresponding oblique decomposition.
* `LiesenStrakos.Chapter03.remark_3_8_2` gives the three equivalent projection
  characterizations of the CG iterate.

## Deviations from the source

* **Remark 3.8.2** (correction). The error and residual descriptions use the complementary
  projections specified by the decompositions, and the residual formula uses its polynomial
  scaling.
-/

open Krylov Polynomial
open scoped Polynomial

namespace LiesenStrakos.Chapter03

/-- **Theorem 3.8.1** of [liesen2013krylov]. Let $r_0$ be the initial residual, let $P$ be the
orthogonal projection onto $\mathcal K_n(A,r_0)$, and assume CG has yet to terminate at
step $n$. There is a monic polynomial $p$ of degree $n$ with $\alpha_0=p(0)\ne0$ such that
$P A^n r_0=-(p-X^n)(A)r_0$. The CG residual is then
$r_n=\alpha_0^{-1}(A^nr_0-P A^nr_0)$, and $r_0-r_n$ is the image under $A$ of the step-$n$
correction in $\mathcal K_n(A,r_0)$, equal to $-\alpha_0^{-1}(p-\alpha_0)(A)r_0$.

**Generalization.** The decomposition holds on any inner product space with a finite-
dimensional cyclic span. -/
theorem theorem_3_8_1 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {A : E →ₗ[𝕜] E} (b x₀ : E) {n : ℕ} (hA : A.IsSymmetricCoercive)
    [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] (hn : n < grade A (b - A x₀)) :
    let r₀ := b - A x₀
    let r := (CG.iterate A b x₀ n).r
    let K := subspace A r₀ n
    ∃ p : 𝕜[X], p.Monic ∧ p.degree = n ∧ p.eval 0 ≠ 0 ∧
      K.starProjection ((A ^ n) r₀) = -aeval A (p - X ^ n) r₀ ∧
      r = (p.eval 0)⁻¹ • ((A ^ n) r₀ - K.starProjection ((A ^ n) r₀)) ∧
      r ∈ Kᗮ ∧ r₀ - r ∈ K.map A ∧
      r₀ - r = (-(p.eval 0)⁻¹) • aeval A (p - C (p.eval 0)) r₀ := by
  dsimp only
  let r₀ := b - A x₀
  let r := (CG.iterate A b x₀ n).r
  let K := subspace A r₀ n
  have hG := CG.isGalerkinIterate b x₀ hA n
  have hrne : r ≠ 0 := CG.residual_ne_zero_of_lt_grade b x₀ hn
  have hperp : r ∈ Kᗮ := by
    simpa only [r, CG.residual_eq] using hG.orth
  obtain ⟨q, hqdeg, hq0, hq⟩ := Krylov.exists_residual_poly hG.mem
  rw [← CG.residual_eq] at hq
  change r = aeval A q r₀ at hq
  have hqdeg' : q.degree = n := by
    refine le_antisymm hqdeg (le_of_not_gt fun h => hrne ?_)
    have hmem : r ∈ K := by
      rw [hq]
      exact aeval_apply_mem_subspace A r₀ h
    exact inner_self_eq_zero.1 ((Submodule.mem_orthogonal K r).1 hperp _ hmem)
  have hqne : q ≠ 0 := fun he => by simp [he] at hq0
  let c := q.leadingCoeff⁻¹
  have hc : c ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.2 hqne)
  let p := C c * q
  have hp : p.Monic :=
    monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ (leadingCoeff_ne_zero.2 hqne))
  have hpdeg : p.degree = n := (degree_C_mul_of_isUnit hc.isUnit q).trans hqdeg'
  have hp0 : p.eval 0 = c := by simp [p, hq0]
  have hpA : aeval A p r₀ = c • r := by
    rw [show p = C c * q from rfl, map_mul, Module.End.mul_apply, ← hq]
    simp
  have hdiffdeg : (p - X ^ n).degree < (n : WithBot ℕ) := by
    rw [← hpdeg]
    exact degree_sub_lt_left (hpdeg.trans (degree_X_pow (R := 𝕜) (n := n)).symm) hp.ne_zero
      (hp.leadingCoeff.trans (monic_X_pow n).leadingCoeff.symm)
  have hAevalSub : aeval A (p - X ^ n) r₀ = c • r - (A ^ n) r₀ := by
    rw [map_sub (aeval A : 𝕜[X] →ₐ[𝕜] (E →ₗ[𝕜] E)), LinearMap.sub_apply, map_pow, aeval_X, hpA]
  have htail : (A ^ n) r₀ - (-aeval A (p - X ^ n) r₀) = c • r := by
    rw [hAevalSub]
    abel
  have hprojection : K.starProjection ((A ^ n) r₀) = -aeval A (p - X ^ n) r₀ := by
    refine Submodule.eq_starProjection_of_mem_orthogonal
      (K.neg_mem (aeval_apply_mem_subspace A r₀ hdiffdeg)) ?_
    rw [htail]
    exact (Kᗮ).smul_mem c hperp
  change (∃ p : 𝕜[X], p.Monic ∧ p.degree = n ∧ p.eval 0 ≠ 0 ∧
    K.starProjection ((A ^ n) r₀) = -aeval A (p - X ^ n) r₀ ∧
    r = (p.eval 0)⁻¹ • ((A ^ n) r₀ - K.starProjection ((A ^ n) r₀)) ∧
    r ∈ Kᗮ ∧ r₀ - r ∈ K.map A ∧
    r₀ - r = (-(p.eval 0)⁻¹) • aeval A (p - C (p.eval 0)) r₀)
  refine ⟨p, hp, hpdeg, by rwa [hp0], hprojection, ?_, hperp, ?_, ?_⟩
  · rw [hp0, hprojection, htail, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · refine ⟨(CG.iterate A b x₀ n).x - x₀, hG.mem, ?_⟩
    dsimp [r₀, r]
    rw [map_sub, CG.residual_eq]
    abel
  · rw [hp0, map_sub (aeval A : 𝕜[X] →ₐ[𝕜] (E →ₗ[𝕜] E)), LinearMap.sub_apply, hpA]
    simp [← smul_sub, smul_smul, inv_mul_cancel₀ hc, neg_smul]

/-- **Remark 3.8.2** of [liesen2013krylov]. Before termination the CG iterate is uniquely
determined by any of three projection formulas. Its error is the projection of the initial
error onto the energy-orthogonal complement of the Krylov space. Its residual is the component
of the initial residual along the orthogonal complement of the Krylov space in the oblique
decomposition. It is also the orthogonal component of $A^n r_0$ scaled by the reciprocal of
the constant term of the monic residual polynomial.

**Correction.** The error is the $A$-orthogonal projection onto the orthogonal complement of
the trial space. The residual is in the complementary summand of the oblique decomposition. Its
orthogonal formula uses the complementary projection of $A^n r_0$ scaled by $1/p(0)$, as in
Theorem 3.8.1. -/
theorem remark_3_8_2 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {A : E →ₗ[𝕜] E} (b x₀ : E) {n : ℕ} (hA : A.IsSymmetricCoercive)
    [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] (hn : n < grade A (b - A x₀))
    {xstar : E} (hstar : A xstar = b) :
    let r₀ := b - A x₀
    let K := subspace A r₀ n
    let xCG := (CG.iterate A b x₀ n).x
    ∃ p : 𝕜[X], p.Monic ∧ p.degree = n ∧ p.eval 0 ≠ 0 ∧
      K.starProjection ((A ^ n) r₀) = -aeval A (p - X ^ n) r₀ ∧
      ∀ x : E,
        (x = xCG ↔ WithEnergy.equiv A hA (xstar - x) =
          (WithEnergy.submoduleMap A hA K)ᗮ.starProjection (WithEnergy.equiv A hA (xstar - x₀))) ∧
        (x = xCG ↔ (b - A x) ∈ Kᗮ ∧ r₀ - (b - A x) ∈ K.map A) ∧
        (x = xCG ↔ b - A x = (p.eval 0)⁻¹ • ((A ^ n) r₀ - K.starProjection ((A ^ n) r₀))) := by
  dsimp only
  obtain ⟨p, hp, hd, hne, hP, hr, hperp, hmem, _⟩ := theorem_3_8_1 b x₀ hA hn
  have hG := CG.isGalerkinIterate b x₀ hA n
  have hE := IsGalerkin.error_eq_starProjection hA hG hstar
  rw [CG.residual_eq] at hr hperp hmem
  refine ⟨p, hp, hd, hne, hP, fun x => ⟨?_, ?_, ?_⟩⟩
  · refine ⟨fun he => he.symm ▸ hE, fun he => ?_⟩
    exact sub_right_inj.mp ((WithEnergy.equiv A hA).injective (he.trans hE.symm))
  · constructor
    · rintro rfl
      exact ⟨hperp, hmem⟩
    · rintro ⟨hxorth, hxmem⟩
      obtain ⟨y, hy, hAy⟩ := Submodule.mem_map.1 hxmem
      rw [residual_eq_sub_apply_sub A b x₀ x, sub_sub_cancel] at hAy
      have hxG : IsGalerkinIterate A b x₀ n x :=
        ⟨(hA.isCoercive.injective hAy) ▸ hy, hxorth⟩
      exact hxG.eq_of_forall hG fun _ hz hAz =>
        eq_zero_of_isCoercive_of_apply_mem_orthogonal _ hA.isCoercive hz hAz
  · refine ⟨fun he => he.symm ▸ hr, fun he => ?_⟩
    exact hA.isCoercive.injective (sub_right_inj.mp (he.trans hr.symm))

end LiesenStrakos.Chapter03
