/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Numlib.Algebra.Polynomial.ConjugateRoots
import NumlibSurface.LiesenStrakos.Chapter04.Section06

/-!
# Liesen and Strakoš, §4.7: Short recurrences and distinct eigenvalues

The elementary square-degree bound for the equation $p(z)=\overline z$
gives an obstruction to short recurrences, including the sharp obstruction
of Theorem 4.7.1 for $s=2$. The general deduction uses the sharp harmonic
root bound as a hypothesis.

## Deviations from the source

* **Theorem 4.7.1** (reading). The unconditional result covers $s=2$ over the complex
  numbers. The general bound assumes the sharp harmonic root bound. Both statements
  deduce diagonalizability from the recurrence. See `LiesenStrakos.theorem_4_7_1_two` and
  `LiesenStrakos.theorem_4_7_1_of_harmonic_root_bound`.

## Not formalized

* The sharp $3s-2$ root bound for the harmonic equation is used as a hypothesis when $s>2$.
-/

open Matrix Polynomial
open scoped ComplexOrder

namespace LiesenStrakos

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem spectrum_eq_range_of_diagonal {A Y : Matrix n n ℂ} {d : n → ℂ}
    (hY : IsUnit Y) (hdiag : A = Y * Matrix.diagonal d * Y⁻¹) :
    spectrum ℂ A = Set.range d := by
  let e := Matrix.similarityAlgEquiv Y hY
  have he : e A = Matrix.diagonal d :=
    (Matrix.similarityAlgEquiv_apply_eq_iff Y hY A _).2 hdiag
  rw [← AlgEquiv.spectrum_eq e A, he, spectrum_diagonal]

private theorem minpoly_natDegree_le_ncard_spectrum_of_diagonal
    {A Y : Matrix n n ℂ} {d : n → ℂ}
    (hY : IsUnit Y) (hdiag : A = Y * Matrix.diagonal d * Y⁻¹) :
    (minpoly ℂ A).natDegree ≤ (spectrum ℂ A).ncard := by
  let S := Finset.univ.image d
  let p : ℂ[X] := ∏ z ∈ S, (X - C z)
  have hp : p.Monic := monic_prod_of_monic _ _ fun z _ => monic_X_sub_C z
  have hdeg : p.natDegree = S.card := natDegree_finsetProd_X_sub_C_eq_card _ _
  have hr (i : n) : p.eval (d i) = 0 := by
    have hi : d i ∈ S := Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
    simp only [p, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero hi (sub_self _)
  have hz : aeval (Matrix.diagonal d) p = 0 := by
    have heval : aeval (Matrix.diagonal d) p = Matrix.diagonal (fun i => p.eval (d i)) := by
      rw [← Matrix.diagonalAlgHom_apply ℂ, aeval_algHom_apply, aeval_pi_apply]
      simp [coe_aeval_eq_eval]
    rw [heval, show (fun i => p.eval (d i)) = fun _ : n => (0 : ℂ) from funext hr,
      Matrix.diagonal_zero]
  let e := Matrix.similarityAlgEquiv Y hY
  have he : e A = Matrix.diagonal d :=
    (Matrix.similarityAlgEquiv_apply_eq_iff Y hY A _).2 hdiag
  have hq : (minpoly ℂ (Matrix.diagonal d)).natDegree ≤ p.natDegree :=
    natDegree_le_of_dvd (minpoly.dvd ℂ (Matrix.diagonal d) hz) hp.ne_zero
  have hspec : spectrum ℂ A = (S : Set ℂ) := by
    rw [spectrum_eq_range_of_diagonal hY hdiag]
    simp [S]
  rw [← he, minpoly.algEquiv_eq, hdeg] at hq
  rwa [hspec, Set.ncard_coe_finset]

private theorem no_optimalWeightedRecurrence_of_rootBound {A : Matrix n n ℂ}
    {s D : ℕ} (hstep : s + 2 < (minpoly ℂ A).natDegree)
    (hdegree : D < (minpoly ℂ A).natDegree)
    (hline : ¬ ∃ z w : ℂ, w ≠ 0 ∧
      ∀ u ∈ spectrum ℂ A, ∃ t : ℝ, u = z + (t : ℂ) * w)
    (hbound : ∀ p : ℂ[X], 1 < p.natDegree → p.natDegree ≤ s →
      {z : ℂ | p.eval z = star z}.ncard ≤ D)
    {t : ℕ} (ht : t ≤ s) (B : Matrix n n ℂ) (hB : B.PosDef) :
    ¬ AdmitsOptimalWeightedRecurrence A B t := by
  intro hrec
  have hnormal := (theorem_4_6_2 A B hB t (by omega)).1 hrec
  obtain ⟨_, Y, d, hY, hdiag, _, _, hpoly⟩ := corollary_4_6_4 hnormal
  obtain ⟨p, hp, heval, _⟩ := (hpoly t).2 rfl
  have hd := natDegree_eq_of_degree_eq_some hp
  have hgt : 1 < t := by
    by_contra! hle
    have hc : t = 0 ∨ t = 1 := by omega
    rcases hc with hzero | hone
    · have he : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero (hd.trans hzero)
      rw [he] at heval
      simp only [eval_C] at heval
      apply hline
      refine ⟨star (p.coeff 0), 1, one_ne_zero, fun u hu => ?_⟩
      rw [spectrum_eq_range_of_diagonal hY hdiag] at hu
      obtain ⟨i, rfl⟩ := hu
      exact ⟨0, by simpa using (congrArg star (heval i)).symm⟩
    · have h := (theorem_4_6_5_one A).1 ⟨B, hone ▸ hnormal⟩
      obtain ⟨W, a, hW, hAW, _, z, w, hw, hcoords⟩ := h
      apply hline
      refine ⟨z, w, hw, fun u hu => ?_⟩
      rw [spectrum_eq_range_of_diagonal hW hAW] at hu
      obtain ⟨i, rfl⟩ := hu
      exact hcoords i
  have hfin := (p.finite_setOf_eval_eq_star_and_ncard_le_sq (hd.symm ▸ hgt)).1
  have hsub : spectrum ℂ A ⊆ {z : ℂ | p.eval z = star z} := by
    rw [spectrum_eq_range_of_diagonal hY hdiag]
    rintro _ ⟨i, rfl⟩
    exact heval i
  have hle := (minpoly_natDegree_le_ncard_spectrum_of_diagonal hY hdiag).trans
    ((Set.ncard_le_ncard hsub hfin).trans (hbound p (hd.symm ▸ hgt) (hd.symm ▸ ht)))
  exact (not_le_of_gt hdegree) hle

/-- The square-degree obstruction in §4.7 of [liesen2013krylov]. If the
noncollinear spectrum has minimal-polynomial degree greater than $s^2$,
then no positive definite metric admits an optimal recurrence of length
at most $s+2$.

**Reading.** The threshold is $s^2$, which can exceed the sharp $3s-2$ threshold in the source.
Diagonalizability is a consequence of the assumed recurrence in the contradiction proof. -/
theorem no_optimalWeightedRecurrence_of_squareDegree {A : Matrix n n ℂ}
    {s : ℕ} (hs : 1 < s) (hdegree : s ^ 2 < (minpoly ℂ A).natDegree)
    (hline : ¬ ∃ z w : ℂ, w ≠ 0 ∧
      ∀ u ∈ spectrum ℂ A, ∃ t : ℝ, u = z + (t : ℂ) * w)
    {t : ℕ} (ht : t ≤ s) (B : Matrix n n ℂ) (hB : B.PosDef) :
    ¬ AdmitsOptimalWeightedRecurrence A B t := by
  have hstep : s + 2 ≤ s ^ 2 := calc
    s + 2 ≤ s + s := by omega
    _ = 2 * s := (two_mul s).symm
    _ ≤ s ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right s hs
  apply no_optimalWeightedRecurrence_of_rootBound (hstep.trans_lt hdegree) hdegree hline _
    ht B hB
  intro p hp hps
  refine (p.finite_setOf_eval_eq_star_and_ncard_le_sq hp).2.trans ?_
  gcongr

/-- **Theorem 4.7.1** of [liesen2013krylov] for $s=2$. If the spectrum is
noncollinear and the minimal-polynomial degree exceeds four, no positive
definite metric admits an optimal recurrence of four terms or fewer.

**Reading.** The source gives $d_{\min}(A)>3s-2$ for all $s>1$ and assumes that $A$ is
diagonalizable. Here $s=2$ makes the square-degree bound sufficient, and the short
recurrence characterization supplies the diagonalization. -/
theorem theorem_4_7_1_two {A : Matrix n n ℂ}
    (hdegree : 4 < (minpoly ℂ A).natDegree)
    (hline : ¬ ∃ z w : ℂ, w ≠ 0 ∧
      ∀ u ∈ spectrum ℂ A, ∃ t : ℝ, u = z + (t : ℂ) * w)
    {t : ℕ} (ht : t ≤ 2) (B : Matrix n n ℂ) (hB : B.PosDef) :
    ¬ AdmitsOptimalWeightedRecurrence A B t :=
  no_optimalWeightedRecurrence_of_squareDegree (s := 2) (by decide) hdegree hline ht B hB

/-- Conditional deduction of **Theorem 4.7.1** of [liesen2013krylov] from the
sharp bound on the number of distinct roots of $p(z)=\overline z$. If
$d_{\min}(A)>3s-2$ and the spectrum is noncollinear, no positive definite
metric admits an optimal recurrence of length at most $s+2$.

**Reading.** The source cites the harmonic root bound to give an unconditional result.
Here that bound is an explicit hypothesis, and the short recurrence characterization
supplies the diagonalization of the complex matrix. -/
theorem theorem_4_7_1_of_harmonic_root_bound
    (hroot : ∀ p : ℂ[X], 1 < p.natDegree →
      {z : ℂ | p.eval z = star z}.ncard ≤ 3 * p.natDegree - 2)
    {A : Matrix n n ℂ} {s : ℕ} (hs : 1 < s) (hdegree : 3 * s - 2 < (minpoly ℂ A).natDegree)
    (hline : ¬ ∃ z w : ℂ, w ≠ 0 ∧
      ∀ u ∈ spectrum ℂ A, ∃ t : ℝ, u = z + (t : ℂ) * w)
    {t : ℕ} (ht : t ≤ s) (B : Matrix n n ℂ) (hB : B.PosDef) :
    ¬ AdmitsOptimalWeightedRecurrence A B t := by
  apply no_optimalWeightedRecurrence_of_rootBound (by omega) hdegree hline _ ht B hB
  intro p hp hps
  exact (hroot p hp).trans (by omega)

end LiesenStrakos
