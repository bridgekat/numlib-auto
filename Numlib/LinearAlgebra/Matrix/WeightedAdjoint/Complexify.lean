import Mathlib.Algebra.Polynomial.Eval.Subring
import Numlib.Algebra.Polynomial.MinDegreeRepresentation
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.WeightedAdjoint

/-!
# Complexification of weighted adjoints and polynomial representations

Complexification preserves the weighted adjoint of a real matrix and the least degree
of a polynomial representing one real matrix in another.

## Main results

* `Matrix.isMinDegreeRepresentation_complexify_iff`: real and complex coefficients give
  the same least degree for real arguments and values.
* `Matrix.complexify_weightedAdjoint`: the weighted adjoint commutes with complexification.
* `Matrix.minpoly_complexify`: complexification maps the real minimal polynomial
  coefficient by coefficient.
-/

open Polynomial
open scoped Matrix ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Complexification of a polynomial in a real matrix is the polynomial with the same
coefficients evaluated in the complexification of that matrix. -/
theorem complexify_aeval (A : Matrix n n ℝ) (p : ℝ[X]) :
    (aeval A p).complexify = aeval A.complexify (p.map Complex.ofRealHom) := by
  let ψ : Matrix n n ℝ →+* Matrix n n ℂ := Complex.ofRealHom.mapMatrix
  change ψ (aeval A p) = aeval (ψ A) (p.map Complex.ofRealHom)
  apply Polynomial.map_aeval_eq_aeval_map
  ext c i j
  by_cases h : i = j <;> simp [Matrix.algebraMap_matrix_apply, Matrix.map_apply, h, ψ]

/-- Entrywise complex conjugation commutes with polynomial evaluation when the
polynomial coefficients are conjugated as well. -/
theorem star_map_aeval (A : Matrix n n ℂ) (p : ℂ[X]) :
    (starRingEnd ℂ).mapMatrix (aeval A p) =
      aeval ((starRingEnd ℂ).mapMatrix A) (p.map (starRingEnd ℂ)) := by
  apply Polynomial.map_aeval_eq_aeval_map
  ext c i j
  by_cases h : i = j <;> simp [Matrix.algebraMap_matrix_apply, Matrix.map_apply, h]

/-- Entrywise complex conjugation fixes complexifications of real matrices. -/
theorem star_map_complexify (A : Matrix n n ℝ) :
    (starRingEnd ℂ).mapMatrix A.complexify = A.complexify := by
  ext i j
  simp [Matrix.map_apply]

/-- If a polynomial in a complexified real matrix represents a real matrix, then a
real polynomial of no greater degree represents it over the reals. -/
theorem exists_real_aeval_of_complexify {A B : Matrix n n ℝ} {p : ℂ[X]}
    (h : aeval A.complexify p = B.complexify) :
    ∃ q : ℝ[X], q.degree ≤ p.degree ∧ aeval A q = B := by
  have hconj := star_map_aeval A.complexify p
  rw [h, star_map_complexify A, star_map_complexify B] at hconj
  let f := starRingEnd ℂ
  let r := (1/2 : ℂ) • (p + p.map f)
  have hd : r.degree ≤ p.degree := by
    have hdmap := degree_map_eq_of_injective (f := f) star_injective p
    exact (degree_smul_le _ _).trans ((degree_add_le _ _).trans (max_le le_rfl hdmap.le))
  have hr : aeval A.complexify r = B.complexify := by
    change aeval A.complexify ((1/2 : ℂ) • (p + p.map f)) = _
    rw [map_smul, map_add, h, ← hconj, ← two_smul ℂ B.complexify, smul_smul]
    norm_num
  have hfixed (k : ℕ) : star (r.coeff k) = r.coeff k := by
    simp only [r, coeff_smul, smul_eq_mul, coeff_add, coeff_map, f, starRingEnd_apply, star_mul,
      star_add, star_star]
    have hh : star (1/2 : ℂ) = 1/2 := by simp
    rw [hh]
    ring
  have hrange : r ∈ (Polynomial.mapRingHom Complex.ofRealHom).range := by
    apply (Polynomial.mem_map_range _).2
    intro k
    exact ⟨(r.coeff k).re, Complex.conj_eq_iff_re.mp (hfixed k)⟩
  obtain ⟨q, hq⟩ := hrange
  change q.map Complex.ofRealHom = r at hq
  refine ⟨q, ?_, Matrix.complexify_injective ?_⟩
  · rwa [← hq, degree_map_eq_of_injective Complex.ofReal_injective] at hd
  · rw [complexify_aeval, hq, hr]

/-- Complexifying real matrices preserves the minimum degree of a polynomial
representing one matrix in another. -/
theorem isMinDegreeRepresentation_complexify_iff (A B : Matrix n n ℝ) (s : ℕ) :
    IsMinDegreeRepresentation (R := ℂ) A.complexify B.complexify s ↔
      IsMinDegreeRepresentation (R := ℝ) A B s := by
  have hmap (q : ℝ[X]) : (q.map Complex.ofRealHom).degree = q.degree :=
    degree_map_eq_of_injective Complex.ofReal_injective q
  have heval (q : ℝ[X]) (h : aeval A q = B) :
      aeval A.complexify (q.map Complex.ofRealHom) = B.complexify :=
    (complexify_aeval A q).symm.trans (congrArg Matrix.complexify h)
  constructor
  · rintro ⟨p, hdeg, hp, hmin⟩
    obtain ⟨q, hqd, hq⟩ := exists_real_aeval_of_complexify hp
    have hle := hmin (q.map Complex.ofRealHom) (heval q hq)
    rw [hmap q] at hle
    refine ⟨q, le_antisymm (hqd.trans_eq hdeg) hle, hq, fun r hr => ?_⟩
    exact (hmin _ (heval r hr)).trans_eq (hmap r)
  · rintro ⟨p, hdeg, hp, hmin⟩
    refine ⟨p.map Complex.ofRealHom, (hmap p).trans hdeg, heval p hp, fun r hr => ?_⟩
    obtain ⟨q, hqd, hq⟩ := exists_real_aeval_of_complexify hr
    exact (hmin q hq).trans hqd

/-- Complexifying a real weighted adjoint gives the complex weighted adjoint. -/
theorem complexify_weightedAdjoint (A B : Matrix n n ℝ) :
    (A.weightedAdjoint B).complexify = A.complexify.weightedAdjoint B.complexify := by
  simp only [weightedAdjoint, complexify_mul, complexify_inv, complexify_conjTranspose]

/-- Complexification maps the real minimal polynomial coefficient by coefficient. -/
theorem minpoly_complexify (A : Matrix n n ℝ) :
    minpoly ℂ A.complexify = (minpoly ℝ A).map Complex.ofRealHom := by
  let m := minpoly ℂ A.complexify
  let f := starRingEnd ℂ
  have hm : m.Monic := minpoly.monic (IsIntegral.of_finite ℂ A.complexify)
  have hann : aeval A.complexify m = 0 := minpoly.aeval ℂ A.complexify
  have hconj : aeval A.complexify (m.map f) = 0 := by
    have h := star_map_aeval A.complexify m
    rw [star_map_complexify, hann, map_zero] at h
    exact h.symm
  have hself : m = m.map f := by
    refine eq_of_dvd_of_natDegree_le_of_leadingCoeff (minpoly.dvd ℂ _ hconj) ?_
      (hm.leadingCoeff.trans (hm.map f).leadingCoeff.symm)
    rw [natDegree_map_eq_of_injective (f := f) star_injective]
  have hrange : m ∈ (Polynomial.mapRingHom Complex.ofRealHom).range := by
    apply (Polynomial.mem_map_range _).2
    intro k
    have hstar : star (m.coeff k) = m.coeff k := by
      simpa only [coeff_map, f, starRingEnd_apply] using
        congrArg (fun p : ℂ[X] => p.coeff k) hself.symm
    exact ⟨(m.coeff k).re, Complex.conj_eq_iff_re.mp hstar⟩
  obtain ⟨q, hq⟩ := hrange
  change q.map Complex.ofRealHom = m at hq
  have hqann : aeval A q = 0 := by
    apply complexify_injective
    rw [complexify_aeval, hq, hann, complexify_zero]
  have hd₁ : m ∣ (minpoly ℝ A).map Complex.ofRealHom := by
    apply minpoly.dvd ℂ
    rw [← complexify_aeval, minpoly.aeval, complexify_zero]
  have hd₂ : (minpoly ℝ A).map Complex.ofRealHom ∣ m :=
    hq ▸ Polynomial.map_dvd Complex.ofRealHom (minpoly.dvd ℝ A hqann)
  have hm' := (minpoly.monic (IsIntegral.of_finite ℝ A)).map Complex.ofRealHom
  exact eq_of_monic_of_associated hm hm' (associated_of_dvd_dvd hd₁ hd₂)

end Matrix
