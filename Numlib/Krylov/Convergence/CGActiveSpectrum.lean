/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.FiniteMinimaxPolynomial
import Numlib.Krylov.Convergence.Polynomial

/-!
# The active-eigenvalue formula for the CG minimax bound

Before the degree of the minimal polynomial, the CG spectral minimax
value is determined by a subset of $n+1$ distinct eigenvalues. Interpolation
at those eigenvalues gives the explicit value of the certificate.
-/

open Finset Polynomial

namespace CG

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} {N : ℕ}

private theorem natDegree_minpoly_le_card_eigenvalues (hN : Module.finrank 𝕜 E = N)
    (hA : A.IsSymmetric) :
    (minpoly 𝕜 A).natDegree ≤ (Finset.univ.image (hA.eigenvalues hN)).card := by
  let S := Finset.univ.image (hA.eigenvalues hN)
  let p : 𝕜[X] := ∏ y ∈ S, (X - C (y : 𝕜))
  have hp : p.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (i : 𝕜)
  have hdegree : p.natDegree = S.card := natDegree_finsetProd_X_sub_C_eq_card _ _
  have hroot (i : Fin N) : p.eval (hA.eigenvalues hN i : 𝕜) = 0 := by
    have hi : hA.eigenvalues hN i ∈ S := Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
    simp only [p, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero hi (sub_self _)
  have ha : aeval A p = 0 := by
    apply LinearMap.ext
    intro x
    apply (hA.eigenvectorBasis hN).repr.injective
    ext i
    rw [hA.repr_aeval_apply hN, hroot, zero_mul, LinearMap.zero_apply, map_zero]
    rfl
  rw [← hdegree]
  exact natDegree_le_of_dvd (minpoly.dvd 𝕜 A ha) hp.ne_zero

/-- At a positive step $n$ below the degree of the minimal polynomial, the
minimax value on the spectrum of a finite-dimensional symmetric operator is
realized on a subset of $n+1$ distinct eigenvalues. The reciprocal of the
sum of their absolute Lagrange basis values at zero gives the value. -/
theorem exists_activeEigenvalues (hN : Module.finrank 𝕜 E = N)
    (hA : A.IsSymmetric) {n : ℕ} (hn : 0 < n) (hd : n < (minpoly 𝕜 A).natDegree) :
    ∃ T ⊆ Finset.univ.image (hA.eigenvalues hN), T.card = n + 1 ∧
      (⨅ p : {p : 𝕜[X] // p.degree ≤ n ∧ p.eval 0 = 1},
        ⨆ i, ‖p.1.eval (hA.eigenvalues hN i : 𝕜)‖) =
        (∑ x ∈ T, ∏ y ∈ T.erase x, |y| / |y - x|)⁻¹ := by
  let μ := hA.eigenvalues hN
  let S := Finset.univ.image μ
  have hS : n + 1 ≤ S.card := Nat.succ_le_of_lt (hd.trans_le
    (natDegree_minpoly_le_card_eigenvalues hN hA))
  obtain ⟨T, hTS, hTc, hEq⟩ :=
    Polynomial.exists_active_nodes_eval_minimax_eq (𝕜 := 𝕜) hn S hS
  refine ⟨T, hTS, hTc, ?_⟩
  have hs (p : 𝕜[X]) :
      (⨆ i, ‖p.eval (μ i : 𝕜)‖) = ⨆ x : S, ‖p.eval (algebraMap ℝ 𝕜 x.val)‖ := by
    apply le_antisymm
    · refine Real.iSup_le (fun i => ?_) ?_
      · have hi : μ i ∈ S := Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
        simpa only [RCLike.algebraMap_eq_ofReal] using
          le_ciSup (f := fun x : S => ‖p.eval (algebraMap ℝ 𝕜 x.val)‖)
            (Finite.bddAbove_range _) ⟨μ i, hi⟩
      · exact Real.iSup_nonneg fun x => norm_nonneg _
    · refine Real.iSup_le (fun x : S => ?_) (Real.iSup_nonneg fun i => norm_nonneg _)
      obtain ⟨i, _, hi⟩ := Finset.mem_image.1 x.property
      simpa only [← hi, RCLike.algebraMap_eq_ofReal] using
        le_ciSup (f := fun j => ‖p.eval (μ j : 𝕜)‖) (Finite.bddAbove_range _) i
  simpa only [← hs] using hEq

end CG
