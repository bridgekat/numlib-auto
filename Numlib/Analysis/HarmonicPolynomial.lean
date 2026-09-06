import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity.Basic

/-!
# The Laplacian of a multivariate polynomial

`MvPolynomial.laplacian` is `Δ = Σ_i ∂²/∂x_i²` as a linear map on `MvPolynomial σ R`, and
`MvPolynomial.sumSq` is `|x|² = Σ_i x_i²`.

The result the module exists for is
`MvPolynomial.eq_zero_of_laplacian_one_sub_sumSq_mul_eq_zero`: a polynomial multiple of `1 − |x|²`
cannot be harmonic unless it is zero. Analytically that is the uniqueness statement for the
Dirichlet problem on a ball — a harmonic function continuous up to the boundary and vanishing on the
sphere vanishes — but the proof here uses no analysis. The engine is Euler's identity, which turns
the product rule into `Δ(|x|² h) = (2d + 4m) h + |x|² Δh` for `h` homogeneous of degree `m`; that
identity forces a homogeneous `h` with `a • h + |x|² Δh = 0` and `a > 0` to vanish, by a descent on
the degree, and the general case follows by peeling off the homogeneous component of top degree.

The consequence is that `Δ` is a linear bijection from `(1 − |x|²) Π_n^d` onto `Π_n^d`, which is
what makes the spectral Galerkin method for a Dirichlet problem on a ball uniquely solvable.

## Main definitions

* `MvPolynomial.laplacian`: `Δ p = Σ_i ∂²p/∂x_i²`.
* `MvPolynomial.sumSq σ R`: `Σ_i X_i²`.

## Main results

* `MvPolynomial.totalDegree_laplacian_le`: `Δ` drops the total degree by two.
* `MvPolynomial.laplacian_sumSq_mul`: `Δ(|x|² h) = (2d + 4m) h + |x|² Δh` for homogeneous `h`.
* `MvPolynomial.eq_zero_of_smul_add_sumSq_mul_laplacian_eq_zero` and
  `MvPolynomial.eq_zero_of_laplacian_one_sub_sumSq_mul_eq_zero`.
-/

open Finset

namespace MvPolynomial

section Degree

variable {σ R : Type*} [CommSemiring R]

/-- A partial derivative strictly drops the total degree, or is zero. -/
theorem totalDegree_pderiv_le (i : σ) (p : MvPolynomial σ R) :
    (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  rw [totalDegree]
  refine Finset.sup_le fun m hm => ?_
  rw [mem_support_iff, coeff_pderiv] at hm
  have hmem : m + Finsupp.single i 1 ∈ p.support :=
    mem_support_iff.2 fun hz => hm (by rw [hz, zero_mul])
  have hle : (m + Finsupp.single i 1).sum (fun _ e => e) ≤ p.totalDegree :=
    Finset.le_sup (f := fun s : σ →₀ ℕ => s.sum fun _ e => e) hmem
  have hsum : (m + Finsupp.single i 1).sum (fun _ e => e) = (m.sum fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) fun _ _ _ => rfl, Finsupp.sum_single_index rfl]
  omega

end Degree

section Laplacian

variable {σ R : Type*} [CommSemiring R] [Fintype σ]

/-- The **Laplacian** `Δ p = Σ_i ∂²p/∂x_i²` of a polynomial in finitely many variables. -/
noncomputable def laplacian : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  ∑ i : σ, (pderiv (R := R) i).toLinearMap ∘ₗ (pderiv i).toLinearMap

/-- The Laplacian evaluated: `Δ p` is the sum over the variables of the second derivatives. -/
theorem laplacian_apply (p : MvPolynomial σ R) :
    laplacian p = ∑ i : σ, pderiv i (pderiv i p) := by
  simp [laplacian, LinearMap.sum_apply]

/-- The Laplacian drops the total degree by two. -/
theorem totalDegree_laplacian_le (p : MvPolynomial σ R) :
    (laplacian p).totalDegree ≤ p.totalDegree - 2 := by
  rw [laplacian_apply]
  refine totalDegree_finsetSum_le fun i _ => ?_
  have h1 := totalDegree_pderiv_le i (pderiv i p)
  have h2 := totalDegree_pderiv_le i p
  omega

/-- The Laplacian of a polynomial of degree at most one vanishes: its first derivatives are
constants. -/
theorem laplacian_eq_zero_of_totalDegree_le_one {p : MvPolynomial σ R} (h : p.totalDegree ≤ 1) :
    laplacian p = 0 := by
  rw [laplacian_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 := totalDegree_pderiv_le i p
  have h2 : (pderiv i p).totalDegree = 0 := Nat.le_zero.1 (by omega)
  rw [totalDegree_eq_zero_iff_eq_C.1 h2, pderiv_C]

variable (σ R) in
/-- `|x|² = Σ_i X_i²`, the polynomial whose real level set `|x|² = 1` is the unit sphere. -/
noncomputable def sumSq : MvPolynomial σ R := ∑ i : σ, X i * X i

/-- `|x|²` is homogeneous of degree two. -/
theorem isHomogeneous_sumSq : (sumSq σ R).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun i _ => by
    simpa using (isHomogeneous_X R i).mul (isHomogeneous_X R i)

theorem totalDegree_sumSq_le : (sumSq σ R).totalDegree ≤ 2 :=
  isHomogeneous_sumSq.totalDegree_le

/-- `∂|x|²/∂x_j = 2 x_j`, written without a numeral so that it holds over any commutative
semiring. -/
theorem pderiv_sumSq (j : σ) : pderiv j (sumSq σ R) = X j + X j := by
  classical
  rw [sumSq, map_sum, Finset.sum_eq_single j]
  · rw [pderiv_mul, pderiv_X_self, one_mul, mul_one]
  · intro i _ hij
    rw [pderiv_mul, pderiv_X_of_ne hij, zero_mul, mul_zero, add_zero]
  · simp

/-- The Laplacian of a homogeneous polynomial of degree `m` is homogeneous of degree `m - 2`. -/
theorem IsHomogeneous.laplacian {m : ℕ} {p : MvPolynomial σ R} (hp : p.IsHomogeneous m) :
    (MvPolynomial.laplacian p).IsHomogeneous (m - 2) := by
  rw [laplacian_apply]
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  simpa [Nat.sub_sub] using (hp.pderiv (i := i)).pderiv (i := i)

/-- **Euler's identity in the form the Dirichlet problem needs**: multiplying a homogeneous
polynomial `h` of degree `m` by `|x|²` and applying the Laplacian gives `(2d + 4m) h + |x|² Δh`,
with `d` the number of variables. The product rule contributes `2d h` and two cross terms, and
Euler's identity `Σ_i x_i ∂_i h = m h` turns the cross terms into `4 m h`. -/
theorem laplacian_sumSq_mul {m : ℕ} {h : MvPolynomial σ R} (hh : h.IsHomogeneous m) :
    laplacian (sumSq σ R * h)
      = (2 * Fintype.card σ + 4 * m) • h + sumSq σ R * laplacian h := by
  have key : ∀ i : σ, pderiv i (pderiv i (sumSq σ R * h))
      = h + h + (X i * pderiv i h + X i * pderiv i h
        + (X i * pderiv i h + X i * pderiv i h)) + sumSq σ R * pderiv i (pderiv i h) := by
    intro i
    rw [pderiv_mul, pderiv_sumSq, map_add, pderiv_mul, pderiv_mul, pderiv_sumSq, map_add,
      pderiv_X_self]
    ring
  rw [laplacian_apply, Finset.sum_congr rfl fun i (_ : i ∈ univ) => key i]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Finset.mul_sum]
  rw [← laplacian_apply, hh.sum_X_mul_pderiv]
  module

end Laplacian

section Real

variable {σ : Type*} [Fintype σ]

/-- `MvPolynomial.laplacian_sumSq_mul` with the coefficient written as a real scalar. -/
theorem laplacian_sumSq_mul' {m : ℕ} {h : MvPolynomial σ ℝ} (hh : h.IsHomogeneous m) :
    laplacian (sumSq σ ℝ * h)
      = ((2 * Fintype.card σ + 4 * m : ℕ) : ℝ) • h + sumSq σ ℝ * laplacian h := by
  rw [laplacian_sumSq_mul hh, Nat.cast_smul_eq_nsmul]

/-- A homogeneous polynomial `h` with `a • h + |x|² Δh = 0` for some `a > 0` is zero. The proof is a
descent on the degree: applying `Δ` to the relation and expanding `Δ(|x|² Δh)` by
`MvPolynomial.laplacian_sumSq_mul` gives a relation of the same shape for `Δh`, two degrees lower
and with a larger positive constant, and below degree two the Laplacian already vanishes. -/
theorem eq_zero_of_smul_add_sumSq_mul_laplacian_eq_zero {m : ℕ} {a : ℝ} (ha : 0 < a)
    {h : MvPolynomial σ ℝ} (hh : h.IsHomogeneous m)
    (heq : a • h + sumSq σ ℝ * laplacian h = 0) : h = 0 := by
  induction m using Nat.strong_induction_on generalizing a h with
  | _ m ih =>
    have hzero : laplacian h = 0 → h = 0 := fun h0 => by
      have hah : a • h = 0 := by rw [← heq, h0, mul_zero, add_zero]
      simpa [ha.ne'] using hah
    rcases le_or_gt m 1 with hm | hm
    · exact hzero (laplacian_eq_zero_of_totalDegree_le_one (hh.totalDegree_le.trans hm))
    · refine hzero (ih (m - 2) (by omega)
        (a := a + ((2 * Fintype.card σ + 4 * (m - 2) : ℕ) : ℝ)) (by positivity) hh.laplacian ?_)
      have hd := congrArg (fun q => laplacian (R := ℝ) (σ := σ) q) heq
      simp only [map_add, map_smul, map_zero, laplacian_sumSq_mul' hh.laplacian] at hd
      rw [← hd]
      module

/-- **A polynomial multiple of `1 − |x|²` is harmonic only if it is zero.** Analytically this says
that a harmonic function on the unit ball, continuous up to the boundary and vanishing on the
sphere, is zero; the proof here is algebraic. Peeling off the homogeneous component of top degree
turns the hypothesis into `(2d + 4m) h + |x|² Δh = 0` for that component, which
`MvPolynomial.eq_zero_of_smul_add_sumSq_mul_laplacian_eq_zero` kills; what is left of the polynomial
then satisfies the same hypothesis one degree lower. -/
theorem eq_zero_of_laplacian_one_sub_sumSq_mul_eq_zero (hσ : Nonempty σ) {n : ℕ}
    {p : MvPolynomial σ ℝ} (hp : p.totalDegree ≤ n)
    (h : laplacian ((1 - sumSq σ ℝ) * p) = 0) : p = 0 := by
  have hcard : (0 : ℝ) < 2 * Fintype.card σ := by
    have := Fintype.card_pos_iff.2 hσ
    positivity
  have hone : ((1 : MvPolynomial σ ℝ) - sumSq σ ℝ).totalDegree ≤ 2 :=
    (totalDegree_sub _ _).trans (by simp [totalDegree_sumSq_le])
  induction n generalizing p with
  | zero =>
    have hpc : p = C (coeff 0 p) := totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hp)
    have hlap : laplacian (C (coeff 0 p) : MvPolynomial σ ℝ) = 0 := by simp [laplacian_apply]
    rw [hpc, sub_mul, one_mul, map_sub, hlap, laplacian_sumSq_mul' (isHomogeneous_C σ _),
      hlap] at h
    simp only [mul_zero, add_zero, zero_sub, neg_eq_zero] at h
    rw [hpc]
    rcases smul_eq_zero.1 h with h' | h'
    · exact absurd h' (by push_cast; exact hcard.ne')
    · exact h'
  | succ n ih =>
    have hh₁ : (homogeneousComponent (n + 1) p).IsHomogeneous (n + 1) :=
      homogeneousComponent_isHomogeneous (n + 1) p
    -- what is left after removing the top homogeneous part has degree at most `n`
    have hdeg' : (p - homogeneousComponent (n + 1) p).totalDegree ≤ n := by
      rcases le_or_gt p.totalDegree n with hn | hn
      · rw [homogeneousComponent_eq_zero (n + 1) p (by omega), sub_zero]
        exact hn
      · have hsum := sum_homogeneousComponent p
        rw [show p.totalDegree = n + 1 by omega, Finset.sum_range_succ] at hsum
        have hrw : p - homogeneousComponent (n + 1) p
            = ∑ i ∈ Finset.range (n + 1), homogeneousComponent i p :=
          (eq_sub_of_add_eq hsum).symm
        rw [hrw]
        exact totalDegree_finsetSum_le fun i hi =>
          (homogeneousComponent_isHomogeneous i p).totalDegree_le.trans
            (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    -- the degree-`n + 1` part of `Δ((1 − |x|²) p)`, which the hypothesis says is zero
    have hhom : ((2 * Fintype.card σ + 4 * (n + 1) : ℕ) • homogeneousComponent (n + 1) p
        + sumSq σ ℝ * laplacian (homogeneousComponent (n + 1) p)).IsHomogeneous (n + 1) := by
      refine IsHomogeneous.add ?_ ?_
      · rw [← Nat.cast_smul_eq_nsmul ℝ]
        exact (mem_homogeneousSubmodule _ _).1
          (Submodule.smul_mem _ _ ((mem_homogeneousSubmodule _ _).2 hh₁))
      · rcases Nat.eq_zero_or_pos n with rfl | hn
        · rw [laplacian_eq_zero_of_totalDegree_le_one hh₁.totalDegree_le, mul_zero]
          exact isHomogeneous_zero _ _ _
        · have hmul := isHomogeneous_sumSq.mul hh₁.laplacian
          rwa [show 2 + (n + 1 - 2) = n + 1 from by omega] at hmul
    have e1 : laplacian ((1 - sumSq σ ℝ) * homogeneousComponent (n + 1) p)
        = laplacian (homogeneousComponent (n + 1) p)
          - ((2 * Fintype.card σ + 4 * (n + 1) : ℕ) • homogeneousComponent (n + 1) p
            + sumSq σ ℝ * laplacian (homogeneousComponent (n + 1) p)) := by
      rw [sub_mul, one_mul, map_sub, laplacian_sumSq_mul hh₁]
    have e2 : homogeneousComponent (n + 1) (laplacian (homogeneousComponent (n + 1) p)) = 0 := by
      have hd := hh₁.totalDegree_le
      have := totalDegree_laplacian_le (homogeneousComponent (n + 1) p)
      exact homogeneousComponent_eq_zero _ _ (by omega)
    have e3 : homogeneousComponent (n + 1)
        (laplacian ((1 - sumSq σ ℝ) * (p - homogeneousComponent (n + 1) p))) = 0 := by
      have hb := (totalDegree_mul ((1 : MvPolynomial σ ℝ) - sumSq σ ℝ)
        (p - homogeneousComponent (n + 1) p)).trans (Nat.add_le_add hone hdeg')
      have := totalDegree_laplacian_le
        ((1 - sumSq σ ℝ) * (p - homogeneousComponent (n + 1) p))
      exact homogeneousComponent_eq_zero _ _ (by omega)
    have hkey : (2 * Fintype.card σ + 4 * (n + 1) : ℕ) • homogeneousComponent (n + 1) p
        + sumSq σ ℝ * laplacian (homogeneousComponent (n + 1) p) = 0 := by
      have hz : homogeneousComponent (n + 1) (laplacian ((1 - sumSq σ ℝ) * p)) = 0 := by
        rw [h, map_zero]
      have hsplit : (1 - sumSq σ ℝ) * p = (1 - sumSq σ ℝ) * homogeneousComponent (n + 1) p
          + (1 - sumSq σ ℝ) * (p - homogeneousComponent (n + 1) p) := by ring
      rw [hsplit, map_add, map_add, e1, map_sub, e2, e3,
        homogeneousComponent_eq_self hhom, zero_sub, add_zero, neg_eq_zero] at hz
      exact hz
    have hh₁zero : homogeneousComponent (n + 1) p = 0 := by
      refine eq_zero_of_smul_add_sumSq_mul_laplacian_eq_zero
        (a := ((2 * Fintype.card σ + 4 * (n + 1) : ℕ) : ℝ)) (by push_cast; positivity) hh₁ ?_
      rwa [← Nat.cast_smul_eq_nsmul ℝ] at hkey
    refine ih ?_ h
    rw [← sub_zero p, ← hh₁zero]
    exact hdeg'

end Real

end MvPolynomial
