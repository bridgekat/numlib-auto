import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder

/-!
# Vector-valued Taylor remainders: from components to Euclidean norms

The remainder bounds (A.19)–(A.20) of [cartis2022evaluation] for a vector-valued map
`c : E → F` are `norm_sub_taylorPolynomial_le_of_lipschitz` and
`norm_iteratedFDeriv_sub_taylorPolynomial_le_of_lipschitz` (the Taylor polynomial is `F`-valued).
The book applies them to constraint maps `c : ℝⁿ → ℝᵐ` whose components `cᵢ` each satisfy a
Lipschitz (or boundedness) condition with a common constant; the Euclidean constant is then
`√m` times the componentwise one ((14.1.3), (B.14.3)). This file proves that conversion.

## Main results

* `ContinuousMultilinearMap.norm_le_sqrt_card_mul_of_euclidean`: a multilinear map into
  `EuclideanSpace ℝ (Fin m)` whose components have norm at most `B` has norm at most `√m B`;
* `iteratedFDerivLipschitzOn_of_forall_component`: `√m L`-Lipschitz `∇^j c` from
  `L`-Lipschitz `∇^j cᵢ`;
* `norm_iteratedFDeriv_le_of_forall_component`: the same for derivative bounds.
-/

open Finset
open scoped Nat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- **Euclidean norm from component norms.** If every component
`(EuclideanSpace.proj i) ∘ A` of a continuous multilinear map `A` with values in
`EuclideanSpace ℝ (Fin m)` has norm at most `B`, then `‖A‖ ≤ √m B` ([cartis2022evaluation],
(14.1.3), (B.14.3)). -/
theorem ContinuousMultilinearMap.norm_le_sqrt_card_mul_of_euclidean {k : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) (EuclideanSpace ℝ (Fin m))) {B : ℝ}
    (h : ∀ i, ‖(EuclideanSpace.proj i).compContinuousMultilinearMap A‖ ≤ B) :
    ‖A‖ ≤ Real.sqrt m * B := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : A = 0 := by ext v i; exact i.elim0
    simp [this]
  have hB : 0 ≤ B := (norm_nonneg _).trans (h ⟨0, hm⟩)
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  have hcomp : ∀ i, ‖A v i‖ ≤ B * ∏ j, ‖v j‖ := fun i =>
    (((EuclideanSpace.proj i).compContinuousMultilinearMap A).le_opNorm v).trans
      (by gcongr; exact h i)
  rw [EuclideanSpace.norm_eq, mul_assoc,
    ← Real.sqrt_sq (by positivity : 0 ≤ B * ∏ j, ‖v j‖), ← Real.sqrt_mul (Nat.cast_nonneg m)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖A v i‖ ^ 2 ≤ ∑ _i : Fin m, (B * ∏ j, ‖v j‖) ^ 2 :=
        sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hcomp i) 2
    _ = m * (B * ∏ j, ‖v j‖) ^ 2 := by simp

/-- The `j`-th derivative of the component `cᵢ` of `c : E → EuclideanSpace ℝ (Fin m)` is the
`i`-th component of the `j`-th derivative of `c`. -/
theorem iteratedFDeriv_euclidean_component {c : E → EuclideanSpace ℝ (Fin m)} {j : ℕ} {y : E}
    (hc : ContDiffAt ℝ j c y) (i : Fin m) :
    iteratedFDeriv ℝ j (fun x => c x i) y =
      (EuclideanSpace.proj i).compContinuousMultilinearMap (iteratedFDeriv ℝ j c y) :=
  (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).iteratedFDeriv_comp_left hc le_rfl

/-- **Componentwise derivative bounds** ([cartis2022evaluation], (14.1.3)): if
`‖∇^j cᵢ(y)‖ ≤ B` for every component, then `‖∇^j c(y)‖ ≤ √m B`. -/
theorem norm_iteratedFDeriv_le_of_forall_component {c : E → EuclideanSpace ℝ (Fin m)} {j : ℕ}
    {y : E} {B : ℝ} (hc : ContDiffAt ℝ j c y)
    (h : ∀ i, ‖iteratedFDeriv ℝ j (fun x => c x i) y‖ ≤ B) :
    ‖iteratedFDeriv ℝ j c y‖ ≤ Real.sqrt m * B :=
  ContinuousMultilinearMap.norm_le_sqrt_card_mul_of_euclidean _ fun i => by
    simpa [iteratedFDeriv_euclidean_component hc i] using h i

/-- **Componentwise Lipschitz constants** ([cartis2022evaluation], (14.1.3), (B.14.3)): if `c` is
`C^j` at every point of `C` and every `∇^j cᵢ` is `L`-Lipschitz on `C`, then `∇^j c` is
`√m L`-Lipschitz on `C`. -/
theorem iteratedFDerivLipschitzOn_of_forall_component {c : E → EuclideanSpace ℝ (Fin m)} {j : ℕ}
    {L : ℝ} {C : Set E} (hc : ∀ y ∈ C, ContDiffAt ℝ j c y)
    (h : ∀ i, IteratedFDerivLipschitzOn (fun x => c x i) j L C) :
    IteratedFDerivLipschitzOn c j (Real.sqrt m * L) C := by
  rw [iteratedFDerivLipschitzOn_iff]
  intro x hx y hy
  rw [mul_assoc]
  refine ContinuousMultilinearMap.norm_le_sqrt_card_mul_of_euclidean _ fun i => ?_
  have hi := (iteratedFDerivLipschitzOn_iff.1 (h i)) x hx y hy
  rw [iteratedFDeriv_euclidean_component (hc x hx), iteratedFDeriv_euclidean_component (hc y hy)]
    at hi
  convert hi using 2
  ext v
  simp
