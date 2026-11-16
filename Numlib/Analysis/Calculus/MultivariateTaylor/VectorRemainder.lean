/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder

/-!
# Vector-valued Taylor remainders: from components to Euclidean norms

The remainder bounds (A.19) and (A.20) of [cartis2022evaluation] for a vector-valued map
$c \colon E \to F$ are `norm_sub_taylorPolynomial_le_of_lipschitz` and
`norm_iteratedFDeriv_sub_taylorPolynomial_le_of_lipschitz`, where the Taylor polynomial takes values
in $F$. In [cartis2022evaluation] these bounds are applied to constraint maps
$c \colon \mathbb{R}^n \to \mathbb{R}^m$ whose components $c_i$ each satisfy a Lipschitz or
boundedness condition with a common constant. The constant for the Euclidean norm on $\mathbb{R}^m$
is then $\sqrt{m}$ times the constant for the components, as in (14.1.3) and (B.14.3). This module
proves this conversion.

## Main results

* `ContinuousMultilinearMap.norm_le_sqrt_card_mul_of_euclidean`: a continuous multilinear map into
  $\mathbb{R}^m$ whose components have norm at most $B$ has norm at most $\sqrt{m} B$.
* `norm_iteratedFDeriv_le_of_forall_component`: $\|\nabla^j c_i(y)\| \le B$ for all $i$ implies
  $\|\nabla^j c(y)\| \le \sqrt{m} B$.
* `iteratedFDerivLipschitzOn_of_forall_component`: if every $\nabla^j c_i$ is $L$-Lipschitz, then
  $\nabla^j c$ is $\sqrt{m} L$-Lipschitz.

## Implementation notes

* The space $\mathbb{R}^m$ with the Euclidean norm is `EuclideanSpace ℝ (Fin m)`, and the component
  $c_i$ is `fun x => c x i`.
-/

open Finset
open scoped Nat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- **Euclidean norm from component norms.** Let $A$ be a continuous $k$-linear map from $E$ to
$\mathbb{R}^m$ with the Euclidean norm, and let $B \in \mathbb{R}$. If every component
$\pi_i \circ A$, where $\pi_i$ is the $i$-th coordinate projection, has norm at most $B$, then
$$\|A\| \le \sqrt{m} \, B.$$

This is the estimate behind (14.1.3) and (B.14.3) of [cartis2022evaluation]. The projection
$\pi_i$ is `EuclideanSpace.proj i`. -/
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

/-- Let $c \colon E \to \mathbb{R}^m$ be of class $C^j$ at $y$. Then for every $i$, the $j$-th
derivative of the component $c_i$ at $y$ is $\pi_i \circ \nabla^j c(y)$, where $\pi_i$ is the
$i$-th coordinate projection. -/
theorem iteratedFDeriv_euclidean_component {c : E → EuclideanSpace ℝ (Fin m)} {j : ℕ} {y : E}
    (hc : ContDiffAt ℝ j c y) (i : Fin m) :
    iteratedFDeriv ℝ j (fun x => c x i) y =
      (EuclideanSpace.proj i).compContinuousMultilinearMap (iteratedFDeriv ℝ j c y) :=
  (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).iteratedFDeriv_comp_left hc le_rfl

/-- **Componentwise derivative bounds.** Let $c \colon E \to \mathbb{R}^m$ be of class $C^j$ at $y$,
with the Euclidean norm on $\mathbb{R}^m$. If $\|\nabla^j c_i(y)\| \le B$ for every component
$c_i$, then
$$\|\nabla^j c(y)\| \le \sqrt{m} \, B.$$

This is the conversion in (14.1.3) of [cartis2022evaluation]. -/
theorem norm_iteratedFDeriv_le_of_forall_component {c : E → EuclideanSpace ℝ (Fin m)} {j : ℕ}
    {y : E} {B : ℝ} (hc : ContDiffAt ℝ j c y)
    (h : ∀ i, ‖iteratedFDeriv ℝ j (fun x => c x i) y‖ ≤ B) :
    ‖iteratedFDeriv ℝ j c y‖ ≤ Real.sqrt m * B :=
  ContinuousMultilinearMap.norm_le_sqrt_card_mul_of_euclidean _ fun i => by
    simpa [iteratedFDeriv_euclidean_component hc i] using h i

/-- **Componentwise Lipschitz constants.** Let $C \subseteq E$, and let
$c \colon E \to \mathbb{R}^m$ be of class $C^j$ at every point of $C$, with the Euclidean norm
on $\mathbb{R}^m$. If $\nabla^j c_i$ is $L$-Lipschitz on $C$ for every component $c_i$, then
$\nabla^j c$ is $\sqrt{m} L$-Lipschitz on $C$.

This is the conversion in (14.1.3) and (B.14.3) of [cartis2022evaluation]. Lipschitz continuity
of the derivatives is `IteratedFDerivLipschitzOn`. -/
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
