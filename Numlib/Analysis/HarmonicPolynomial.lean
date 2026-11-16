/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Basic.Real.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity.Basic

/-!
# The Laplacian of a multivariate polynomial

Let $\sigma$ be a finite set of $d$ variables and let $R$ be a commutative semiring. This module
defines the Laplacian $\Delta = \sum_i \partial^2 / \partial x_i^2$ as a linear map on the
polynomials in the variables $x_i$, $i \in \sigma$, with coefficients in $R$, and the polynomial
$|x|^2 = \sum_i x_i^2$. Its main result is that a real polynomial multiple of $1 - |x|^2$ is
harmonic only if it is zero: if $\Delta((1 - |x|^2) p) = 0$, then $p = 0$. In analysis this is the
uniqueness statement for the Dirichlet problem on a ball: a harmonic function that is continuous up
to the boundary and vanishes on the sphere is zero. The proof here uses no analysis.

As a consequence, $\Delta$ is a linear bijection from $(1 - |x|^2) \Pi_n^d$ onto $\Pi_n^d$, where
$\Pi_n^d$ is the space of real polynomials of total degree at most $n$ in $d$ variables. This makes
the spectral Galerkin method for a Dirichlet problem on a ball uniquely solvable.

## Main definitions

* `MvPolynomial.laplacian`: the Laplacian $\Delta p = \sum_i \partial^2 p / \partial x_i^2$.
* `MvPolynomial.sumSq`: the polynomial $|x|^2 = \sum_i x_i^2$.

## Main results

* `MvPolynomial.totalDegree_laplacian_le`: $\Delta$ lowers the total degree by at least two.
* `MvPolynomial.laplacian_sumSq_mul`: $\Delta(|x|^2 h) = (2d + 4m) h + |x|^2 \Delta h$ for $h$
  homogeneous of degree $m$.
* `MvPolynomial.eq_zero_of_smul_add_sumSq_mul_laplacian_eq_zero`: a real homogeneous polynomial $h$
  with $a h + |x|^2 \Delta h = 0$ for some $a > 0$ is zero.
* `MvPolynomial.eq_zero_of_laplacian_one_sub_sumSq_mul_eq_zero`: if $d \ge 1$ and
  $\Delta((1 - |x|^2) p) = 0$ for a real polynomial $p$, then $p = 0$.

## Proof outline

The main tool is Euler's identity $\sum_i x_i \partial_i h = m h$ for $h$ homogeneous of degree $m$.
With the product rule, it gives $\Delta(|x|^2 h) = (2d + 4m) h + |x|^2 \Delta h$. This identity
forces a homogeneous $h$ with $a h + |x|^2 \Delta h = 0$ and $a > 0$ to vanish, by a descent on the
degree. The general case follows by taking off the homogeneous component of top degree.
-/

open Finset

namespace MvPolynomial

section Degree

variable {σ R : Type*} [CommSemiring R]

/-- A partial derivative lowers the total degree: for $i \in \sigma$ and a polynomial $p$,
$$\deg \frac{\partial p}{\partial x_i} \le \deg p - 1,$$
where $\deg$ is the total degree and the subtraction is in $\mathbb{N}$, so that the bound is
$0$ when $p$ is constant. -/
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

/-- The **Laplacian** of a polynomial $p$ in finitely many variables $x_i$, $i \in \sigma$:
$$\Delta p = \sum_{i \in \sigma} \frac{\partial^2 p}{\partial x_i^2},$$
as an $R$-linear map on the polynomials. -/
noncomputable def laplacian : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  ∑ i : σ, (pderiv (R := R) i).toLinearMap ∘ₗ (pderiv i).toLinearMap

/-- The value of the Laplacian: $\Delta p = \sum_{i \in \sigma} \partial_i (\partial_i p)$, where
$\partial_i$ is the partial derivative with respect to $x_i$. -/
theorem laplacian_apply (p : MvPolynomial σ R) :
    laplacian p = ∑ i : σ, pderiv i (pderiv i p) := by
  simp [laplacian, LinearMap.sum_apply]

/-- The Laplacian lowers the total degree by at least two: $\deg \Delta p \le \deg p - 2$, with the
subtraction in $\mathbb{N}$. -/
theorem totalDegree_laplacian_le (p : MvPolynomial σ R) :
    (laplacian p).totalDegree ≤ p.totalDegree - 2 := by
  rw [laplacian_apply]
  refine totalDegree_finsetSum_le fun i _ => ?_
  have h1 := totalDegree_pderiv_le i (pderiv i p)
  have h2 := totalDegree_pderiv_le i p
  omega

/-- If $p$ has total degree at most $1$, then $\Delta p = 0$, because the first partial derivatives
of $p$ are constants. -/
theorem laplacian_eq_zero_of_totalDegree_le_one {p : MvPolynomial σ R} (h : p.totalDegree ≤ 1) :
    laplacian p = 0 := by
  rw [laplacian_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 := totalDegree_pderiv_le i p
  have h2 : (pderiv i p).totalDegree = 0 := Nat.le_zero.1 (by omega)
  rw [totalDegree_eq_zero_iff_eq_C.1 h2, pderiv_C]

variable (σ R) in
/-- The polynomial
$$|x|^2 = \sum_{i \in \sigma} x_i^2.$$
Over $\mathbb{R}$, its level set $|x|^2 = 1$ is the unit sphere. -/
noncomputable def sumSq : MvPolynomial σ R := ∑ i : σ, X i * X i

/-- The polynomial $|x|^2$ is homogeneous of degree $2$. -/
theorem isHomogeneous_sumSq : (sumSq σ R).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun i _ => by
    simpa using (isHomogeneous_X R i).mul (isHomogeneous_X R i)

/-- The polynomial $|x|^2$ has total degree at most $2$. -/
theorem totalDegree_sumSq_le : (sumSq σ R).totalDegree ≤ 2 :=
  isHomogeneous_sumSq.totalDegree_le

/-- For $j \in \sigma$, $\partial |x|^2 / \partial x_j = x_j + x_j$.

The right side is written without the numeral $2$, so that the identity holds over every
commutative semiring. -/
theorem pderiv_sumSq (j : σ) : pderiv j (sumSq σ R) = X j + X j := by
  classical
  rw [sumSq, map_sum, Finset.sum_eq_single j]
  · rw [pderiv_mul, pderiv_X_self, one_mul, mul_one]
  · intro i _ hij
    rw [pderiv_mul, pderiv_X_of_ne hij, zero_mul, mul_zero, add_zero]
  · simp

/-- Let $p$ be homogeneous of degree $m$. Then $\Delta p$ is homogeneous of degree $m - 2$, with the
subtraction in $\mathbb{N}$. -/
theorem IsHomogeneous.laplacian {m : ℕ} {p : MvPolynomial σ R} (hp : p.IsHomogeneous m) :
    (MvPolynomial.laplacian p).IsHomogeneous (m - 2) := by
  rw [laplacian_apply]
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  simpa [Nat.sub_sub] using (hp.pderiv (i := i)).pderiv (i := i)

/-- **Euler's identity in the form that the Dirichlet problem needs**: let $h$ be a homogeneous
polynomial of degree $m$ in $d$ variables. Then
$$\Delta(|x|^2 h) = (2d + 4m) h + |x|^2 \Delta h.$$

The product rule gives $2d h$, the term $|x|^2 \Delta h$ and two cross terms
$2 \sum_i 2 x_i \partial_i h$. Euler's identity $\sum_i x_i \partial_i h = m h$ turns the cross
terms into $4 m h$. The number $d$ is `Fintype.card σ`, and $2d + 4m$ acts as a natural number
scalar. -/
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

/-- The identity `MvPolynomial.laplacian_sumSq_mul` for real polynomials, with the coefficient
$2d + 4m$ as a real scalar: $\Delta(|x|^2 h) = (2d + 4m) h + |x|^2 \Delta h$ for $h$ homogeneous
of degree $m$. -/
theorem laplacian_sumSq_mul' {m : ℕ} {h : MvPolynomial σ ℝ} (hh : h.IsHomogeneous m) :
    laplacian (sumSq σ ℝ * h)
      = ((2 * Fintype.card σ + 4 * m : ℕ) : ℝ) • h + sumSq σ ℝ * laplacian h := by
  rw [laplacian_sumSq_mul hh, Nat.cast_smul_eq_nsmul]

/-- Let $h$ be a real homogeneous polynomial of degree $m$, and let $a > 0$ with
$$a h + |x|^2 \Delta h = 0.$$
Then $h = 0$.

The proof is a descent on the degree. Applying $\Delta$ to the relation and expanding
$\Delta(|x|^2 \Delta h)$ by `MvPolynomial.laplacian_sumSq_mul` gives a relation of the same form
for $\Delta h$, two degrees lower and with a larger positive constant. Below degree two, the
Laplacian is zero. -/
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

/-- **A polynomial multiple of $1 - |x|^2$ is harmonic only if it is zero.** Let the number $d$ of
variables be at least $1$, let $n \in \mathbb{N}$, and let $p$ be a real polynomial of total
degree at most $n$ with
$$\Delta\bigl((1 - |x|^2) p\bigr) = 0.$$
Then $p = 0$.

In analysis this says that a harmonic function on the unit ball that is continuous up to the
boundary and vanishes on the sphere is zero; the proof here is algebraic. Taking off the
homogeneous component of top degree turns the hypothesis into $(2d + 4m) h + |x|^2 \Delta h = 0$
for that component $h$ of degree $m$, so $h = 0$ by
`MvPolynomial.eq_zero_of_smul_add_sumSq_mul_laplacian_eq_zero`. The rest of the polynomial then
satisfies the same hypothesis one degree lower. The degree bound $n$ is arbitrary, so it is no
restriction on $p$; the hypothesis $d \ge 1$ is `Nonempty σ`. -/
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
    have hpc : p = C (p.coeff 0) := totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hp)
    have hlap : laplacian (C (p.coeff 0) : MvPolynomial σ ℝ) = 0 := by simp [laplacian_apply]
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
