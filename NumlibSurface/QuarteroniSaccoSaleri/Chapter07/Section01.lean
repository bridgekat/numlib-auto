import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Nonlinear.DifferenceJacobian
import Numlib.Nonlinear.FixedPoint
import Numlib.Nonlinear.Newton
import Numlib.Nonlinear.QuasiNewton
import Numlib.Stationary.ConsistentlyOrdered
import NumlibSurface.QuarteroniSaccoSaleri.Chapter04.Section01

/-!
# Quarteroni–Sacco–Saleri §7.1: solution of systems of nonlinear equations

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §7.1: Newton's method (7.4) in `ℝⁿ` with Theorem 7.1, the composite
Newton–SOR method (7.7)–(7.8) through Exercise 7.1, the difference-Jacobian method (7.9)–(7.10)
and Property 7.1, Broyden's method (7.11)–(7.14) with the least-change characterization the book
derives it from, and the fixed-point iteration (7.17) with Definition 7.1, Theorem 7.2, Property
7.3, Example 7.4 and Remark 7.1. The backbone is `Numlib/Nonlinear/{Newton, DifferenceJacobian,
QuasiNewton, FixedPoint}` and `Numlib/Stationary/Basic` for the truncated inner iteration.

## Conventions

Newton's iteration is the backbone's `Newton.iterate F F' x₀` with the junk-valued
`ContinuousLinearMap.inverse` (so that "the sequence is uniquely defined" is the clause that every
`F' (x k)` is invertible); the difference-Jacobian iteration (7.10) is `equation_7_10`; Broyden's
is `Broyden.step`/`Broyden.iterate`; the fixed-point iteration (7.17) is `G^[k] x₀` and needs no
definition. Theorem 7.1 is stated on an arbitrary finite-dimensional real normed space, because
the book allows "any vector norm" with the induced (consistent) matrix norm; everything that
needs coordinates lives on `EuclideanSpace ℝ (Fin n)`, and the Jacobian matrix `J_F(x)` is
`jacobianMatrix F x`, the matrix of `fderiv ℝ F x` in the standard basis. Spectral radii are
`Matrix.complexSpectralRadius`, as in chapter 4.

## Readings

* Property 7.1 is stated in the `‖·‖₁` norm; here it is in the Euclidean norm, where the
  difference-Jacobian error carries a factor `√n` that changes no conclusion. Its "or,
  equivalently" clause is one-directional as used: `‖F(x)‖ ≲ ‖x - x*‖` near the root is all the
  quadratic conclusion needs.
* Theorem 7.2 omits `D₀ ≠ ∅`; the empty set is closed, `G` maps it into itself and it has no
  fixed point. Definition 7.1 allows `α < 0`, which is the same as `α = 0`; the a priori
  estimate of the proof is stated for `0 ≤ α`.
* Remark 7.1 writes Newton's method as `(I - J_{G_N}(x^{(k)})) δ = -r^{(k)}`; the matrix that
  makes the identity true, and Newton a preconditioned Richardson iteration, is `J_F(x^{(k)})`
  (`notes/book-errata.md`).
* Property 7.2 (superlinear convergence of Broyden's method, the Dennis–Moré theory) is not
  formalized; Examples 7.1–7.3 are numerical runs.
-/

open Filter Matrix Metric Set Topology WithLp
open scoped ENNReal InnerProductSpace

namespace QuarteroniSaccoSaleri.Chapter07

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Newton's method (7.4) and Theorem 7.1 -/

/-- **(7.4).** Newton's method for `F(x) = 0` in `EuclideanSpace ℝ (Fin n)`: at each step solve
`J_F(x^{(k)}) δx^{(k)} = -F(x^{(k)})` and set `x^{(k+1)} = x^{(k)} + δx^{(k)}`. The iterates are
`Newton.iterate F F' x₀`, and whenever `J_F(x^{(k)}) = F' (x k)` is invertible the increment
`δx^{(k)} = x^{(k+1)} - x^{(k)}` solves the linear system. -/
theorem equation_7_4 (F : E → E) (F' : E → E →L[ℝ] E) (x₀ : E) (k : ℕ) (e : E ≃L[ℝ] E)
    (he : (e : E →L[ℝ] E) = F' (Newton.iterate F F' x₀ k)) :
    F' (Newton.iterate F F' x₀ k) (Newton.iterate F F' x₀ (k + 1) - Newton.iterate F F' x₀ k)
        = -F (Newton.iterate F F' x₀ k) ∧
      Newton.iterate F F' x₀ (k + 1)
        = Newton.iterate F F' x₀ k
          + (Newton.iterate F F' x₀ (k + 1) - Newton.iterate F F' x₀ k) := by
  refine ⟨?_, by abel⟩
  have hinv : (F' (Newton.iterate F F' x₀ k)).inverse = (e.symm : E →L[ℝ] E) := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
  rw [Newton.iterate_succ, Newton.step, hinv, sub_sub_cancel_left, map_neg, ← he]
  simp

/-- **Theorem 7.1 (local convergence of Newton's method).** Let `F : ℝⁿ → ℝⁿ` be `C¹` on a convex
open set containing `x*` (here: differentiable with derivative `F'` on `B(x*; R)`), with
`F(x*) = 0`, `J_F(x*)⁻¹` existing with `‖J_F(x*)⁻¹‖ ≤ C`, and
`‖J_F(x) - J_F(y)‖ ≤ L ‖x - y‖` on `B(x*; R)`, for positive constants `R`, `C`, `L`; the norm is
any norm on the finite-dimensional space `E` and the matrix norm is the induced one. Then there
is `r > 0` such that for every `x^{(0)} ∈ B(x*; r)` the sequence (7.4) is uniquely defined
(every `J_F(x^{(k)})` is invertible), converges to `x*`, and satisfies (7.5)
`‖x^{(k+1)} - x*‖ ≤ C L ‖x^{(k)} - x*‖²`. The radius is the book's `r = min(R, 1/(2CL))`;
`Newton.forall_norm_iterate_succ_sub_le_of_mem_ball`. -/
theorem theorem_7_1 [FiniteDimensional ℝ E] {F : E → E} {F' : E → E →L[ℝ] E} {xstar : E}
    (hstar : F xstar = 0) (e : E ≃L[ℝ] E) (he : (e : E →L[ℝ] E) = F' xstar) {R C L : ℝ}
    (hR : 0 < R) (hC : 0 < C) (hL : 0 < L) (hCe : ‖(e.symm : E →L[ℝ] E)‖ ≤ C)
    (hF : ∀ x ∈ ball xstar R, HasFDerivAt F (F' x) x)
    (hLip : ∀ x ∈ ball xstar R, ∀ y ∈ ball xstar R, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ r > 0, ∀ x₀ ∈ ball xstar r,
      (∀ k, ∃ e' : E ≃L[ℝ] E, (e' : E →L[ℝ] E) = F' (Newton.iterate F F' x₀ k)) ∧
      Tendsto (Newton.iterate F F' x₀) atTop (𝓝 xstar) ∧
      ∀ k, ‖Newton.iterate F F' x₀ (k + 1) - xstar‖
        ≤ C * L * ‖Newton.iterate F F' x₀ k - xstar‖ ^ 2 := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  refine ⟨min R (1 / (2 * C * L)), lt_min hR (by positivity), fun x₀ hx₀ => ?_⟩
  have h := fun k => Newton.forall_norm_iterate_succ_sub_le_of_mem_ball hstar e he hCe hF hLip
    hx₀ k
  refine ⟨fun k => ⟨(h k).2.1.choose, (h k).2.1.choose_spec.1⟩, ?_, fun k => (h k).2.2.1⟩
  exact tendsto_of_eventually_norm_sub_succ_le (by norm_num : (1 / 2 : ℝ) < 1)
    (Eventually.of_forall fun k => by linarith [(h k).2.2.2])

/-! ### The Newton–SOR method (7.7)–(7.8) and Exercise 7.1 -/

section NewtonSOR

variable {n : ℕ}

/-- **The `m`-step Newton–SOR method of §7.1.2 (2), one outer step.** With the decomposition
(7.6) `J_F(x) = D - E - F` into the diagonal, strictly lower and strictly upper parts, the SOR
iteration (7.7) for the linear system `J_F(x) δ = -F(x)` from `δx₀ = 0` is
`δx_{r+1} = M δx_r - ω (D - ω E)⁻¹ F(x)`, with the SOR matrix
`M = (D - ω E)⁻¹ ((1 - ω) D + ω F)` (`Matrix.sorIterationMatrix (J x) ω`); the outer step moves
from `x` to `x + δx_m`. Stated on `Fin n → ℝ` because the splitting is a matrix operation; the
inner iteration is chapter 4's `affineStep`. -/
noncomputable def newtonSORStep (F : (Fin n → ℝ) → Fin n → ℝ)
    (J : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (m : ℕ) (x : Fin n → ℝ) : Fin n → ℝ :=
  x + (Chapter04.affineStep (sorIterationMatrix (J x) ω)
    (-(ω • ((diagPart (J x) + ω • strictLower (J x))⁻¹ *ᵥ F x))))^[m] 0

/-- **The `m`-step Newton–SOR iterates** from `x^{(0)}`: `m` SOR sweeps on the Newton system at
every outer step. The one-step Newton–SOR method is the case `m = 1`. -/
noncomputable def newtonSORIterate (F : (Fin n → ℝ) → Fin n → ℝ)
    (J : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (m : ℕ) (x₀ : Fin n → ℝ) (k : ℕ) :
    Fin n → ℝ :=
  (newtonSORStep F J ω m)^[k] x₀

/-- The SOR matrix of (7.7) is the iteration operator of the backbone's SOR splitting of
`J_F(x)` whenever the diagonal `D` is nonsingular and `ω ≠ 0` (`Matrix.sorSplitting`). -/
theorem sorIterationMatrix_eq_sorSplitting_iterationOperator (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    sorIterationMatrix A ω = (sorSplitting A h hω).iterationOperator :=
  (sorSplitting_iterationOperator_eq A h hω).symm

/-- `m` steps of the linear iteration `δ ↦ B δ + f` from `0` produce `(B^{m-1} + ⋯ + B + I) f`:
chapter 4's `affineStep` transported to the backbone's `Stationary.step_iterate_eq_pow_add_sum`. -/
theorem affineStep_iterate_zero (B : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → ℝ) (m : ℕ) :
    (Chapter04.affineStep B f)^[m] 0 = (∑ j ∈ Finset.range m, B ^ j) *ᵥ f := by
  apply toLp_injective 2
  rw [Chapter04.toLp_affineStep_iterate, Stationary.step_iterate_eq_pow_add_sum, toLp_zero,
    map_zero, zero_add, sum_mulVec, toLp_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← map_pow, toEuclideanCLM_toLp]

/-- **Exercise 7.1, cited for (7.8).** The `m`-step Newton–SOR iterate is
`x^{(k+1)} = x^{(k)} - ω (M_k^{m-1} + ⋯ + M_k + I) (D_k - ω E_k)⁻¹ F(x^{(k)})`, with
`M_k = sorIterationMatrix (J x^{(k)}) ω` and `D_k - ω E_k = D_k + ω strictLower(J x^{(k)})`.
From `Stationary.step_iterate_eq_pow_add_sum` and `δx₀ = 0`; the identity is algebraic and needs
neither `D_k` nonsingular nor `ω ≠ 0` (the inverses are junk-valued otherwise). -/
theorem exercise_7_1 (F : (Fin n → ℝ) → Fin n → ℝ) (J : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (ω : ℝ) (m : ℕ) (x₀ : Fin n → ℝ) (k : ℕ) :
    newtonSORIterate F J ω m x₀ (k + 1)
      = newtonSORIterate F J ω m x₀ k
        - ω • ((∑ j ∈ Finset.range m, sorIterationMatrix (J (newtonSORIterate F J ω m x₀ k)) ω ^ j)
          *ᵥ ((diagPart (J (newtonSORIterate F J ω m x₀ k))
            + ω • strictLower (J (newtonSORIterate F J ω m x₀ k)))⁻¹
              *ᵥ F (newtonSORIterate F J ω m x₀ k))) := by
  rw [newtonSORIterate, Function.iterate_succ_apply', ← newtonSORIterate, newtonSORStep,
    affineStep_iterate_zero, mulVec_neg, mulVec_smul, sub_eq_add_neg]

end NewtonSOR

/-! ### Difference approximations of the Jacobian, (7.9)–(7.10) and Property 7.1 -/

section DifferenceJacobian

variable {n : ℕ}

/-- **(7.9).** The difference Jacobian `J_h` of `F` at `x` with increments `h`: its entries are
`(F(x + h_j e_j)_i - F(x)_i) / h_j`, and its `j`-th column, read as the image of the basis vector
`e_j`, is the forward difference `(F(x + h_j e_j) - F(x)) / h_j` of `F` along `e_j`.
`Matrix.differenceJacobian`. -/
theorem equation_7_9 (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (h : Fin n → ℝ) (i j : Fin n) :
    differenceJacobian F x h i j = (F (x + h j • EuclideanSpace.single j 1) i - F x i) / h j ∧
      toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F x h) (EuclideanSpace.single j 1)
        = (h j)⁻¹ • (F (x + h j • EuclideanSpace.single j 1) - F x) :=
  ⟨differenceJacobian_apply F x h i j, toEuclideanCLM_differenceJacobian_single F x h j⟩

/-- **(7.10).** The difference-Jacobian Newton iteration
`x^{(k+1)} = x^{(k)} - (J_h^{(k)})⁻¹ F(x^{(k)})`, with the increments `h k` of step `k`; the
inverse is the junk-valued `ContinuousLinearMap.inverse`, so that invertibility of every `J_h^{(k)}`
is a conclusion of Property 7.1 rather than a hypothesis. -/
noncomputable def equation_7_10 (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → Fin n → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => x₀
  | k + 1 => equation_7_10 F h x₀ k
      - (toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F (equation_7_10 F h x₀ k) (h k))).inverse
          (F (equation_7_10 F h x₀ k))

/-- The recurrence of (7.10). -/
theorem equation_7_10_succ (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → Fin n → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    equation_7_10 F h x₀ (k + 1) = equation_7_10 F h x₀ k
      - (toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F (equation_7_10 F h x₀ k) (h k))).inverse
          (F (equation_7_10 F h x₀ k)) :=
  rfl

open scoped Classical in
/-- The guarded form of a Newton-like recursion `x_{k+1} = x_k - (B k (x k))⁻¹ F (x k)`: the
approximate derivative `B k (x k)` is used while the iterate is in `S`, and the exact one
outside. It agrees with the unguarded recursion as long as the iterates stay in `S`, which is
how the conditional convergence theorem below is reduced to the unconditional one. -/
private noncomputable def guardedIterate (F : E → E) (F' : E → E →L[ℝ] E)
    (B : ℕ → E → E →L[ℝ] E) (S : Set E) (x₀ : E) : ℕ → E
  | 0 => x₀
  | k + 1 =>
    let z := guardedIterate F F' B S x₀ k
    z - (if z ∈ S then B k z else F' z).inverse (F z)

-- TODO(backbone): the hypothesis `∀ k, ‖B k - F' (x k)‖ ≤ η` of
-- `Newton.tendsto_of_forall_inverse_sub_step_of_norm_sub_fderiv_le` is only used at iterates
-- lying in the ball; this is its conditional form, for approximations `B k` that are functions
-- of the current iterate, derived here by guarding the recursion rather than by reproving the
-- induction. Natural home: `Numlib/Nonlinear/Newton`, beside the unconditional statement.
/-- **Linear convergence of Newton-like iterations with approximate derivatives depending on the
iterate**: near a root `x*` with `F'(x*)` invertible and `F'` Lipschitz there are `δ, η > 0` such
that for every family `B k z` of operators with `‖B k z - F' z‖ ≤ η` *for `z` in the ball
`B(x*; δ)`*, every sequence `x (k+1) = x k - (B k (x k))⁻¹ F (x k)` started in the ball stays in
it, has every `B k (x k)` invertible with `‖(B k (x k))⁻¹‖ ≤ 2 ‖F'(x*)⁻¹‖`, halves its error at
every step and converges to `x*`. -/
theorem _root_.Newton.tendsto_of_forall_inverse_sub_step_of_norm_sub_fderiv_le_of_mem
    [CompleteSpace E] {F : E → E} {F' : E → E →L[ℝ] E} {xstar : E} (hstar : F xstar = 0)
    (e : E ≃L[ℝ] E) (he : (e : E →L[ℝ] E) = F' xstar) {r L : ℝ} (hr : 0 < r)
    (hF : ∀ x ∈ ball xstar r, HasFDerivAt F (F' x) x)
    (hLip : ∀ x ∈ ball xstar r, ∀ y ∈ ball xstar r, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ δ > 0, δ ≤ r ∧ ∃ η > 0, ∀ (B : ℕ → E → E →L[ℝ] E) (x : ℕ → E),
      x 0 ∈ ball xstar δ → (∀ k, ∀ z ∈ ball xstar δ, ‖B k z - F' z‖ ≤ η) →
      (∀ k, x (k + 1) = x k - (B k (x k)).inverse (F (x k))) →
      (∀ k, x k ∈ ball xstar δ) ∧
        (∀ k, ∃ e' : E ≃L[ℝ] E, (e' : E →L[ℝ] E) = B k (x k) ∧
          ‖(e'.symm : E →L[ℝ] E)‖ ≤ 2 * ‖(e.symm : E →L[ℝ] E)‖) ∧
        (∀ k, ‖x (k + 1) - xstar‖ ≤ ‖x k - xstar‖ / 2) ∧ Tendsto x atTop (𝓝 xstar) := by
  classical
  obtain ⟨δ, hδ, hδr, η, hη, hmain⟩ :=
    Newton.tendsto_of_forall_inverse_sub_step_of_norm_sub_fderiv_le hstar e he hr hF hLip
  refine ⟨δ, hδ, hδr, η, hη, fun B x hx0 hB hstep => ?_⟩
  let x' : ℕ → E := guardedIterate F F' B (ball xstar δ) (x 0)
  let B' : ℕ → E →L[ℝ] E := fun k =>
    if x' k ∈ ball xstar δ then B k (x' k) else F' (x' k)
  have hx'0 : x' 0 = x 0 := rfl
  have hx'succ : ∀ k, x' (k + 1) = x' k - (B' k).inverse (F (x' k)) := fun k => by
    change guardedIterate F F' B (ball xstar δ) (x 0) (k + 1) = _
    rw [guardedIterate]
  have hB'η : ∀ k, ‖B' k - F' (x' k)‖ ≤ η := fun k => by
    change ‖(if x' k ∈ ball xstar δ then B k (x' k) else F' (x' k)) - F' (x' k)‖ ≤ η
    split_ifs with hmem
    · exact hB k _ hmem
    · rw [sub_self, norm_zero]; exact hη.le
  obtain ⟨hmem, hinv, hhalf, hlim⟩ := hmain x' B' (by rw [hx'0]; exact hx0) hB'η hx'succ
  -- the guarded sequence is the original one
  have heq : ∀ k, x' k = x k := by
    intro k
    induction k with
    | zero => exact hx'0
    | succ k ih =>
      have : B' k = B k (x k) := by
        have hm := hmem k
        rw [ih] at hm
        change (if x' k ∈ ball xstar δ then B k (x' k) else F' (x' k)) = B k (x k)
        simp only [ih, hm, ↓reduceIte]
      rw [hx'succ, hstep, ih, this]
  have hB'eq : ∀ k, B' k = B k (x k) := fun k => by
    have hm := hmem k
    rw [heq] at hm
    change (if x' k ∈ ball xstar δ then B k (x' k) else F' (x' k)) = B k (x k)
    simp only [heq, hm, ↓reduceIte]
  refine ⟨fun k => heq k ▸ hmem k, fun k => ?_, fun k => ?_, ?_⟩
  · obtain ⟨e', he', hn⟩ := hinv k
    exact ⟨e', by rw [he', hB'eq], hn⟩
  · have := hhalf k
    rwa [heq, heq] at this
  · exact hlim.congr heq

variable {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
  {F' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
  {xstar : EuclideanSpace ℝ (Fin n)}

/-- The difference Jacobian at a point of `B(x*; R/2)` with increments below `η < R/2` is within
`√n (L/2) η` of the derivative, under the hypotheses of Theorem 7.1 on `B(x*; R)`
(`Matrix.opNorm_toEuclideanCLM_differenceJacobian_sub_le`). -/
private theorem norm_differenceJacobian_sub_le {R L : ℝ}
    (hF : ∀ x ∈ ball xstar R, HasFDerivAt F (F' x) x)
    (hLip : ∀ x ∈ ball xstar R, ∀ y ∈ ball xstar R, ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ ball xstar (R / 2)) {h : Fin n → ℝ} {η : ℝ}
    (hη : η < R / 2)
    (hh : ∀ j, 0 < |h j| ∧ |h j| ≤ η) :
    ‖toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F z h) - F' z‖
      ≤ √(Fintype.card (Fin n) : ℝ) * (L / 2) * η := by
  have hsub : ball z (R / 2) ⊆ ball xstar R := by
    intro y hy
    rw [mem_ball] at hy hz ⊢
    linarith [dist_triangle y z xstar]
  have hR2 : 0 < R / 2 := lt_of_le_of_lt dist_nonneg (mem_ball.1 hz)
  exact opNorm_toEuclideanCLM_differenceJacobian_sub_le (fun y hy => hF y (hsub hy))
    (fun y hy => hLip y (hsub hy) z (hsub (mem_ball_self hR2)))
    (fun j => ⟨abs_pos.1 (hh j).1, lt_of_le_of_lt (hh j).2 hη⟩) fun j => (hh j).2

/-- The common core of the three clauses of Property 7.1: the radius `ε`, the increment bound
`η`, and for every admissible increment sequence and every start in `B(x*; ε)`, the iterates of
(7.10) stay in `B(x*; ε) ⊆ B(x*; R/2)`, every `J_h^{(k)}` is invertible with
`‖(J_h^{(k)})⁻¹‖ ≤ 2 C`, the error halves at every step, and the increments stay below `R/2`. -/
private theorem property_7_1_core {R C L : ℝ} (hstar : F xstar = 0)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (he : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = F' xstar) (hR : 0 < R)
    (hCe : ‖(e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ C)
    (hF : ∀ x ∈ ball xstar R, HasFDerivAt F (F' x) x)
    (hLip : ∀ x ∈ ball xstar R, ∀ y ∈ ball xstar R, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ ε > 0, ε ≤ R / 2 ∧ ∃ η > 0, η < R / 2 ∧ ∀ h : ℕ → Fin n → ℝ,
      (∀ k j, 0 < |h k j| ∧ |h k j| ≤ η) → ∀ x₀ ∈ ball xstar ε,
      (∀ k, equation_7_10 F h x₀ k ∈ ball xstar ε) ∧
      (∀ k, ∃ e' : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
        (e' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
          = toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F (equation_7_10 F h x₀ k) (h k)) ∧
        ‖(e'.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ 2 * C) ∧
      (∀ k, ‖equation_7_10 F h x₀ (k + 1) - xstar‖ ≤ ‖equation_7_10 F h x₀ k - xstar‖ / 2) ∧
      Tendsto (equation_7_10 F h x₀) atTop (𝓝 xstar) := by
  have hF2 : ∀ x ∈ ball xstar (R / 2), HasFDerivAt F (F' x) x := fun x hx =>
    hF x (ball_subset_ball (by linarith) hx)
  have hLip2 : ∀ x ∈ ball xstar (R / 2), ∀ y ∈ ball xstar (R / 2), ‖F' x - F' y‖ ≤ L * ‖x - y‖ :=
    fun x hx y hy =>
      hLip x (ball_subset_ball (by linarith) hx) y (ball_subset_ball (by linarith) hy)
  obtain ⟨δ, hδ, hδR, η₀, hη₀, hmain⟩ :=
    Newton.tendsto_of_forall_inverse_sub_step_of_norm_sub_fderiv_le_of_mem hstar e he
      (by positivity : 0 < R / 2) hF2 hLip2
  set c : ℝ := √(Fintype.card (Fin n) : ℝ) * (L / 2) with hc
  set η : ℝ := min (R / 4) (η₀ / (|c| + 1)) with hηdef
  have hηpos : 0 < η := lt_min (by positivity) (by positivity)
  have hηR : η < R / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hηc : c * η ≤ η₀ := by
    calc c * η ≤ |c| * η := mul_le_mul_of_nonneg_right (le_abs_self c) hηpos.le
      _ ≤ |c| * (η₀ / (|c| + 1)) := by gcongr; exact min_le_right _ _
      _ ≤ η₀ := by
          rw [mul_div_assoc']
          exact (div_le_iff₀ (by positivity)).2 (by nlinarith [abs_nonneg c])
  refine ⟨δ, hδ, hδR, η, hηpos, hηR, fun h hh x₀ hx₀ => ?_⟩
  have hB : ∀ k, ∀ z ∈ ball xstar δ,
      ‖toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F z (h k)) - F' z‖ ≤ η₀ := fun k z hz =>
    (norm_differenceJacobian_sub_le hF hLip (ball_subset_ball hδR hz) hηR (hh k)).trans hηc
  obtain ⟨hmem, hinv, hhalf, hlim⟩ := hmain (fun k z => toEuclideanCLM (𝕜 := ℝ)
    (differenceJacobian F z (h k))) (equation_7_10 F h x₀) hx₀ hB (equation_7_10_succ F h x₀)
  refine ⟨hmem, fun k => ?_, hhalf, hlim⟩
  obtain ⟨e', he', hn⟩ := hinv k
  exact ⟨e', he', hn.trans (by linarith)⟩

/-- **Property 7.1, first part.** Under the hypotheses of Theorem 7.1 (in the Euclidean norm; the
book's `‖·‖₁` changes only the constants), there are `ε, h > 0` such that for every increment
sequence with `0 < |h_j^{(k)}| ≤ h` and every `x^{(0)} ∈ B(x*; ε)` the sequence (7.10) is well
defined — every `J_h^{(k)}` is invertible — and converges linearly to `x*`: the error halves at
every step, so the convergence is of order `1` with factor `1/2`.
`Newton.tendsto_of_forall_inverse_sub_step_of_norm_sub_fderiv_le` with the difference-Jacobian
error bound `Matrix.opNorm_toEuclideanCLM_differenceJacobian_sub_le`. The book states the result
without proof. -/
theorem property_7_1 {R C L : ℝ} (hstar : F xstar = 0)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (he : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = F' xstar) (hR : 0 < R)
    (hCe : ‖(e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ C)
    (hF : ∀ x ∈ ball xstar R, HasFDerivAt F (F' x) x)
    (hLip : ∀ x ∈ ball xstar R, ∀ y ∈ ball xstar R, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ ε > 0, ∃ η > 0, ∀ h : ℕ → Fin n → ℝ, (∀ k j, 0 < |h k j| ∧ |h k j| ≤ η) →
      ∀ x₀ ∈ ball xstar ε,
      (∀ k, ∃ e' : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
        (e' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
          = toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F (equation_7_10 F h x₀ k) (h k))) ∧
      (∀ k, ‖equation_7_10 F h x₀ (k + 1) - xstar‖ ≤ ‖equation_7_10 F h x₀ k - xstar‖ / 2) ∧
      Tendsto (equation_7_10 F h x₀) atTop (𝓝 xstar) ∧
      ConvergesWithOrder (equation_7_10 F h x₀) xstar 1 := by
  obtain ⟨ε, hε, -, η, hη, -, hcore⟩ := property_7_1_core hstar e he hR hCe hF hLip
  refine ⟨ε, hε, η, hη, fun h hh x₀ hx₀ => ?_⟩
  obtain ⟨-, hinv, hhalf, hlim⟩ := hcore h hh x₀ hx₀
  refine ⟨fun k => ⟨(hinv k).choose, (hinv k).choose_spec.1⟩, hhalf, hlim, ?_⟩
  exact convergesWithOrder_one_of_eventually_norm_sub_succ_le (C := 1 / 2) (by norm_num)
    (by norm_num) (Eventually.of_forall fun k => by linarith [hhalf k])

/-- **Property 7.1, second part.** In the situation of `property_7_1`, if moreover
`max_j |h_j^{(k)}| ≤ C' ‖x^{(k)} - x*‖` for all `k`, then the convergence is quadratic:
`‖x^{(k+1)} - x*‖ ≤ K ‖x^{(k)} - x*‖²` for all `k`, with `K = 2C (√n (L/2) C' + L/2)`, and the
sequence converges with order `2`. `Newton.norm_succ_sub_le_sq_of_norm_sub_fderiv_le_mul` with
the derivative error `√n (L/2) C' ‖x^{(k)} - x*‖`. -/
theorem property_7_1_quadratic {R C L : ℝ} (hstar : F xstar = 0)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (he : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = F' xstar) (hR : 0 < R)
    (hCe : ‖(e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ C)
    (hF : ∀ x ∈ ball xstar R, HasFDerivAt F (F' x) x)
    (hLip : ∀ x ∈ ball xstar R, ∀ y ∈ ball xstar R, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ ε > 0, ∃ η > 0, ∀ h : ℕ → Fin n → ℝ, (∀ k j, 0 < |h k j| ∧ |h k j| ≤ η) →
      ∀ x₀ ∈ ball xstar ε, ∀ C' : ℝ, (∀ k j, |h k j| ≤ C' * ‖equation_7_10 F h x₀ k - xstar‖) →
      (∃ K, ∀ k, ‖equation_7_10 F h x₀ (k + 1) - xstar‖
        ≤ K * ‖equation_7_10 F h x₀ k - xstar‖ ^ 2) ∧
      ConvergesWithOrder (equation_7_10 F h x₀) xstar 2 := by
  obtain ⟨ε, hε, hεR, η, hη, hηR, hcore⟩ := property_7_1_core hstar e he hR hCe hF hLip
  refine ⟨ε, hε, η, hη, fun h hh x₀ hx₀ C' hC' => ?_⟩
  obtain ⟨hmem, hinv, -, hlim⟩ := hcore h hh x₀ hx₀
  set c : ℝ := √(Fintype.card (Fin n) : ℝ) * (L / 2) with hc
  have hx2 : ∀ k, equation_7_10 F h x₀ k ∈ ball xstar (R / 2) := fun k =>
    ball_subset_ball hεR (hmem k)
  have hxR : ∀ k, equation_7_10 F h x₀ k ∈ ball xstar R := fun k =>
    ball_subset_ball (by linarith) (hx2 k)
  -- the derivative error is first order in the error
  have hCk : ∀ k, ‖toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F (equation_7_10 F h x₀ k) (h k))
      - F' (equation_7_10 F h x₀ k)‖ ≤ |c| * |C'| * ‖equation_7_10 F h x₀ k - xstar‖ := by
    intro k
    set η' : ℝ := min η (|C'| * ‖equation_7_10 F h x₀ k - xstar‖) with hη'
    have hη'R : η' < R / 2 := lt_of_le_of_lt (min_le_left _ _) hηR
    have hhk : ∀ j, 0 < |h k j| ∧ |h k j| ≤ η' := fun j =>
      ⟨(hh k j).1, le_min (hh k j).2 ((hC' k j).trans
        (mul_le_mul_of_nonneg_right (le_abs_self C') (norm_nonneg _)))⟩
    have hη'0 : 0 ≤ η' := le_min hη.le (by positivity)
    calc ‖toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F (equation_7_10 F h x₀ k) (h k))
          - F' (equation_7_10 F h x₀ k)‖
        ≤ c * η' := norm_differenceJacobian_sub_le hF hLip (hx2 k) hη'R hhk
      _ ≤ |c| * η' := mul_le_mul_of_nonneg_right (le_abs_self c) hη'0
      _ ≤ |c| * (|C'| * ‖equation_7_10 F h x₀ k - xstar‖) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg c)
      _ = |c| * |C'| * ‖equation_7_10 F h x₀ k - xstar‖ := by ring
  have hK := fun k => Newton.norm_succ_sub_le_sq_of_norm_sub_fderiv_le_mul hstar hF hLip hxR hinv
    (equation_7_10_succ F h x₀) hCk k
  refine ⟨⟨2 * C * (|c| * |C'| + L / 2), hK⟩, hlim, max (2 * C * (|c| * |C'| + L / 2)) 1,
    lt_of_lt_of_le one_pos (le_max_right _ _), Eventually.of_forall fun k => ?_⟩
  rw [Real.rpow_two]
  exact (hK k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))

/-- **Property 7.1, the "or, equivalently" clause.** The quadratic convergence of
`property_7_1_quadratic` also holds when `max_j |h_j^{(k)}| ≤ c ‖F(x^{(k)})‖`: on `B(x*; R)` the
map `F` is Lipschitz with constant `‖F'(x*)‖ + L R` (mean value inequality), and `F(x*) = 0`, so
`‖F(x^{(k)})‖ ≤ (‖F'(x*)‖ + L R) ‖x^{(k)} - x*‖` and the previous clause applies with
`C' = c (‖F'(x*)‖ + L R)` (written with `|L|`, since no sign of `L` is assumed). The converse
direction of the book's "equivalently" is not needed. -/
theorem property_7_1_residual {R C L : ℝ} (hstar : F xstar = 0)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (he : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = F' xstar) (hR : 0 < R)
    (hCe : ‖(e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ C)
    (hF : ∀ x ∈ ball xstar R, HasFDerivAt F (F' x) x)
    (hLip : ∀ x ∈ ball xstar R, ∀ y ∈ ball xstar R, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ ε > 0, ∃ η > 0, ∀ h : ℕ → Fin n → ℝ, (∀ k j, 0 < |h k j| ∧ |h k j| ≤ η) →
      ∀ x₀ ∈ ball xstar ε, ∀ c : ℝ, (∀ k j, |h k j| ≤ c * ‖F (equation_7_10 F h x₀ k)‖) →
      (∃ K, ∀ k, ‖equation_7_10 F h x₀ (k + 1) - xstar‖
        ≤ K * ‖equation_7_10 F h x₀ k - xstar‖ ^ 2) ∧
      ConvergesWithOrder (equation_7_10 F h x₀) xstar 2 := by
  obtain ⟨ε, hε, η, hη, hquad⟩ := property_7_1_quadratic hstar e he hR hCe hF hLip
  -- the iterates stay in `B(x*; ε) ⊆ B(x*; R)`
  obtain ⟨ε', hε', hε'R, η', hη', -, hcore⟩ := property_7_1_core hstar e he hR hCe hF hLip
  refine ⟨min ε ε', lt_min hε hε', min η η', lt_min hη hη', fun h hh x₀ hx₀ c hc => ?_⟩
  have hhη : ∀ k j, 0 < |h k j| ∧ |h k j| ≤ η := fun k j =>
    ⟨(hh k j).1, (hh k j).2.trans (min_le_left _ _)⟩
  have hhη' : ∀ k j, 0 < |h k j| ∧ |h k j| ≤ η' := fun k j =>
    ⟨(hh k j).1, (hh k j).2.trans (min_le_right _ _)⟩
  obtain ⟨hmem, -, -, -⟩ := hcore h hhη' x₀ (ball_subset_ball (min_le_right _ _) hx₀)
  -- `F` is Lipschitz on the ball with constant `‖F'(x*)‖ + |L| R`
  have hFlip : ∀ z ∈ ball xstar R, ‖F z‖ ≤ (‖F' xstar‖ + |L| * R) * ‖z - xstar‖ := by
    intro z hz
    have hbound : ∀ y ∈ ball xstar R, ‖F' y‖ ≤ ‖F' xstar‖ + |L| * R := fun y hy => by
      have h1 := hLip y hy xstar (mem_ball_self hR)
      have h2 : ‖y - xstar‖ ≤ R := by rw [← dist_eq_norm]; exact (mem_ball.1 hy).le
      have h3 : L * ‖y - xstar‖ ≤ |L| * R :=
        (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left h2 (abs_nonneg L))
      calc ‖F' y‖ = ‖F' xstar + (F' y - F' xstar)‖ := by congr 1; abel
        _ ≤ ‖F' xstar‖ + ‖F' y - F' xstar‖ := norm_add_le _ _
        _ ≤ ‖F' xstar‖ + |L| * R := by linarith
    have := (convex_ball xstar R).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y hy => (hF y hy).hasFDerivWithinAt) hbound (mem_ball_self hR) hz
    rwa [hstar, sub_zero] at this
  refine hquad h hhη x₀ (ball_subset_ball (min_le_left _ _) hx₀) (c * (‖F' xstar‖ + |L| * R))
    fun k j => ?_
  have hz := hFlip _ (ball_subset_ball (by linarith) (hmem k))
  have hc0 : 0 ≤ c := by
    by_contra hneg
    rw [not_le] at hneg
    have h1 := (hh k j).1
    have h2 := hc k j
    have h3 := norm_nonneg (F (equation_7_10 F h x₀ k))
    nlinarith
  calc |h k j| ≤ c * ‖F (equation_7_10 F h x₀ k)‖ := hc k j
    _ ≤ c * ((‖F' xstar‖ + |L| * R) * ‖equation_7_10 F h x₀ k - xstar‖) :=
        mul_le_mul_of_nonneg_left hz hc0
    _ = c * (‖F' xstar‖ + |L| * R) * ‖equation_7_10 F h x₀ k - xstar‖ := by ring

end DifferenceJacobian

/-! ### Broyden's method (7.11)–(7.14) -/

section Broyden

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **(7.11).** One step of Broyden's method solves `Q_k δx^{(k+1)} = -F(x^{(k)})` and sets
`x^{(k+1)} = x^{(k)} + δx^{(k+1)}`: for a state `σ = (x^{(k)}, Q_k)` with `Q_k` invertible,
`Q_k (x^{(k+1)} - x^{(k)}) = -F(x^{(k)})`. `Broyden.apply_step_x_sub`. -/
theorem equation_7_11 (F : H → H) (σ : Broyden.State H) (e : H ≃L[ℝ] H)
    (he : (e : H →L[ℝ] H) = σ.Q) :
    σ.Q ((Broyden.step F σ).x - σ.x) = -F σ.x ∧
      (Broyden.step F σ).x = σ.x + ((Broyden.step F σ).x - σ.x) :=
  ⟨Broyden.apply_step_x_sub F σ e he, by abel⟩

/-- **(7.12) with `j = 1`, the secant condition.** The matrix produced by a Broyden step satisfies
`Q_{k+1} (x^{(k+1)} - x^{(k)}) = F(x^{(k+1)}) - F(x^{(k)})` whenever `x^{(k+1)} ≠ x^{(k)}`.
`Broyden.step_Q_apply_sub`, from `Broyden.update_apply_self`. -/
theorem equation_7_12 (F : H → H) (σ : Broyden.State H) (h : (Broyden.step F σ).x ≠ σ.x) :
    (Broyden.step F σ).Q ((Broyden.step F σ).x - σ.x) = F (Broyden.step F σ).x - F σ.x :=
  Broyden.step_Q_apply_sub F σ h

/-- **(7.14).** Broyden's update in matrix form,
`Q_k = Q_{k-1} + ((b^{(k)} - Q_{k-1} δx^{(k)}) δx^{(k)ᵀ}) / (δx^{(k)ᵀ} δx^{(k)})`, is
`Matrix.broydenUpdate Q_{k-1} δx^{(k)} b^{(k)}`, and read on `ℝⁿ = EuclideanSpace ℝ (Fin n)` it
is the operator update `Broyden.update` of the backbone (`Matrix.toEuclideanCLM_broydenUpdate`). -/
theorem equation_7_14 {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (s y : Fin n → ℝ) :
    broydenUpdate Q s y = Q + (1 / (s ⬝ᵥ s)) • vecMulVec (y - Q *ᵥ s) s ∧
      toEuclideanCLM (𝕜 := ℝ) (broydenUpdate Q s y)
        = Broyden.update (toEuclideanCLM (𝕜 := ℝ) Q) (toLp 2 s) (toLp 2 y) :=
  ⟨rfl, toEuclideanCLM_broydenUpdate Q s y⟩

/-- **The characterization behind (7.14)** (§7.1.4): Broyden's `Q_k = Broyden.update Q_{k-1} s b`
with `s = δx^{(k)} ≠ 0` and `b = b^{(k)}` satisfies the secant condition (7.12), `j = 1`, and
`(Q_k - Q_{k-1}) v = 0` for every `v` orthogonal to `δx^{(k)}` — the minimum possible value of
the quantity the text minimizes — and it is the *unique* operator with these two properties:
an operator determined on `span {s}` and on `s^⊥` is determined.
`Broyden.update_apply_self`, `Broyden.update_sub_apply_of_inner_eq_zero`. -/
theorem broydenUpdate_leastChange (Q : H →L[ℝ] H) {s : H} (hs : s ≠ 0) (b : H) :
    Broyden.update Q s b s = b ∧
      (∀ v, ⟪s, v⟫_ℝ = 0 → (Broyden.update Q s b - Q) v = 0) ∧
      ∀ Q' : H →L[ℝ] H, Q' s = b → (∀ v, ⟪s, v⟫_ℝ = 0 → (Q' - Q) v = 0) →
        Q' = Broyden.update Q s b := by
  refine ⟨Broyden.update_apply_self Q hs b, fun v hv =>
    Broyden.update_sub_apply_of_inner_eq_zero Q s b hv, fun Q' hQ's hQ' => ?_⟩
  ext v
  set α : ℝ := ⟪s, v⟫_ℝ / ⟪s, s⟫_ℝ with hα
  have hss : ⟪s, s⟫_ℝ ≠ 0 := inner_self_ne_zero.2 hs
  have hw : ⟪s, v - α • s⟫_ℝ = 0 := by
    rw [inner_sub_right, inner_smul_right, hα, div_mul_cancel₀ _ hss, sub_self]
  have hv : v = α • s + (v - α • s) := by abel
  have h1 : Q' (v - α • s) = Q (v - α • s) := by
    have := hQ' _ hw
    rwa [_root_.sub_apply, sub_eq_zero] at this
  have h2 : Broyden.update Q s b (v - α • s) = Q (v - α • s) := by
    have := Broyden.update_sub_apply_of_inner_eq_zero Q s b hw
    rwa [_root_.sub_apply, sub_eq_zero] at this
  rw [hv, map_add, map_add, map_smul, map_smul, hQ's, Broyden.update_apply_self Q hs b, h1, h2]

end Broyden

/-! ### Fixed-point methods: Definition 7.1, Theorem 7.2, Property 7.3 -/

/-- **Definition 7.1.** A mapping `G` is *contractive* on a set `D₀` if there is a constant
`α < 1` with `‖G(x) - G(y)‖ ≤ α ‖x - y‖` for all `x, y ∈ D₀`; the "suitable vector norm" is the
norm of `E`, so a different norm is a different `E`. The book does not ask `α ≥ 0`; a negative
`α` forces `D₀` to have at most one point and is the same as `α = 0` (`definition_7_1_iff`). -/
def definition_7_1 (G : E → E) (D₀ : Set E) : Prop :=
  ∃ α < 1, ∀ x ∈ D₀, ∀ y ∈ D₀, ‖G x - G y‖ ≤ α * ‖x - y‖

omit [NormedSpace ℝ E] in
/-- Definition 7.1 is Mathlib's `LipschitzOnWith` with a constant `K < 1`: a negative `α` is
replaced by `max α 0`, which still works. -/
theorem definition_7_1_iff (G : E → E) (D₀ : Set E) :
    definition_7_1 G D₀ ↔ ∃ K : NNReal, K < 1 ∧ LipschitzOnWith K G D₀ := by
  constructor
  · rintro ⟨α, hα, hG⟩
    refine ⟨(max α 0).toNNReal, ?_, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (le_max_right _ _), NNReal.coe_one]
      exact max_lt hα one_pos
    · rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (le_max_right _ _)]
      exact (hG x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · rintro ⟨K, hK, hG⟩
    refine ⟨K, by exact_mod_cast hK, fun x hx y hy => ?_⟩
    have := hG.dist_le_mul x hx y hy
    rwa [dist_eq_norm, dist_eq_norm] at this

omit [NormedSpace ℝ E] in
/-- **Theorem 7.2 (contraction-mapping theorem).** If `G` is contractive on a closed set `D₀`
and `G(x) ∈ D₀` for all `x ∈ D₀`, then `G` has a unique fixed point in `D₀`. The book omits
`D₀ ≠ ∅`: the empty set satisfies every hypothesis and has no fixed point. Stated on a complete
space, which `ℝⁿ` is; `exists_unique_fixedPoint_of_mapsTo` (`Numlib/Nonlinear/FixedPoint`). -/
theorem theorem_7_2 [CompleteSpace E] {G : E → E} {D₀ : Set E} (hG : definition_7_1 G D₀)
    (hD : IsClosed D₀) (hne : D₀.Nonempty) (hmaps : MapsTo G D₀ D₀) :
    ∃! x, x ∈ D₀ ∧ G x = x := by
  obtain ⟨α, hα, hG⟩ := hG
  refine exists_unique_fixedPoint_of_mapsTo hD hne hmaps (K := max α 0) (le_max_right _ _)
    (max_lt hα one_pos) fun x hx y hy => ?_
  rw [dist_eq_norm, dist_eq_norm]
  exact (hG x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

omit [NormedSpace ℝ E] in
/-- **Theorem 7.2, the content of its existence proof.** Under the hypotheses of Theorem 7.2 with
the contraction constant `0 ≤ α < 1`, for every `x^{(0)} ∈ D₀` the fixed-point iterates (7.17)
`x^{(k)} = G^{[k]}(x^{(0)})` converge to the fixed point `x*`, with the a priori estimate
`‖x^{(k)} - x*‖ ≤ α^k / (1 - α) ‖x^{(1)} - x^{(0)}‖` (the limit of the Cauchy estimate
`‖x^{(k+p)} - x^{(k)}‖ ≤ α^k / (1 - α) ‖x^{(1)} - x^{(0)}‖` of the proof, as `p → ∞`).
`dist_iterate_le_of_mapsTo`. -/
theorem theorem_7_2_tendsto [CompleteSpace E] {G : E → E} {D₀ : Set E} {α : ℝ} (hα0 : 0 ≤ α)
    (hα : α < 1) (hG : ∀ x ∈ D₀, ∀ y ∈ D₀, ‖G x - G y‖ ≤ α * ‖x - y‖) (hD : IsClosed D₀)
    (hmaps : MapsTo G D₀ D₀) {xstar : E} (hstar : xstar ∈ D₀) (hfix : G xstar = xstar) {x₀ : E}
    (hx₀ : x₀ ∈ D₀) :
    (∀ k, ‖G^[k] x₀ - xstar‖ ≤ α ^ k / (1 - α) * ‖G x₀ - x₀‖) ∧
      Tendsto (fun k => G^[k] x₀) atTop (𝓝 xstar) := by
  have hG' : ∀ x ∈ D₀, ∀ y ∈ D₀, dist (G x) (G y) ≤ α * dist x y := fun x hx y hy => by
    rw [dist_eq_norm, dist_eq_norm]; exact hG x hx y hy
  have hbound : ∀ k, ‖G^[k] x₀ - xstar‖ ≤ α ^ k / (1 - α) * ‖G x₀ - x₀‖ := fun k => by
    have := dist_iterate_le_of_mapsTo hD hmaps hα0 hα hG' hstar hfix hx₀ k
    rwa [dist_eq_norm, dist_eq_norm] at this
  refine ⟨hbound, ?_⟩
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _) hbound ?_)
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα).div_const (1 - α)).mul_const
    ‖G x₀ - x₀‖
  simpa using h

section Jacobian

variable {n : ℕ}

/-- **The Jacobian matrix** `J_F(x)`, `(J_F(x))_{ij} = ∂F_i/∂x_j (x)`, of
`F : ℝⁿ → ℝⁿ` at `x`: the matrix of the Fréchet derivative `fderiv ℝ F x` in the standard basis
of `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def jacobianMatrix (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (fderiv ℝ F x : _ →ₗ[ℝ] _)

/-- The entries of the Jacobian matrix are the partial derivatives: `(J_F(x))_{ij}` is the `i`-th
component of the derivative of `F` at `x` in the direction of the `j`-th basis vector. -/
theorem jacobianMatrix_apply (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    jacobianMatrix F x i j = fderiv ℝ F x (EuclideanSpace.single j 1) i := by
  rw [jacobianMatrix, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply]
  rfl

/-- The bridge to the derivative: the Jacobian matrix acts on `ℝⁿ` as `fderiv ℝ F x`. -/
theorem toEuclideanLin_jacobianMatrix (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    toEuclideanLin (jacobianMatrix F x) = (fderiv ℝ F x : _ →ₗ[ℝ] _) := by
  rw [jacobianMatrix, toEuclideanLin_eq_toLin_orthonormal, Matrix.toLin_toMatrix]

/-- The bridge to the derivative, as continuous linear maps. -/
theorem toEuclideanCLM_jacobianMatrix (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    toEuclideanCLM (𝕜 := ℝ) (jacobianMatrix F x) = fderiv ℝ F x := by
  apply ContinuousLinearMap.coe_injective
  rw [coe_toEuclideanCLM_eq_toEuclideanLin, toEuclideanLin_jacobianMatrix]

/-- **Property 7.3.** Let `G : D ⊆ ℝⁿ → ℝⁿ` have a fixed point `x*` in the interior of `D` and be
continuously differentiable in a neighbourhood of `x*`, with `ρ(J_G(x*)) < 1`. Then there is a
neighbourhood `S ⊆ D` of `x*` such that for every `x^{(0)} ∈ S` the iterates (7.17) all lie in
`D` and converge to `x*`. In finite dimension `ρ(J) < 1` gives `‖J^m‖ < 1` for some `m`
(`Matrix.exists_opNorm_toEuclideanLin_pow_lt_one_of_complexSpectralRadius_lt_one`), and
Ostrowski's theorem for `G^{[m]}` (`tendsto_iterate_of_exists_norm_pow_fderiv_lt_one`,
`exists_ball_mapsTo_iterate_of_exists_norm_pow_fderiv_lt_one`) does the rest. The book cites
Ortega–Rheinboldt for the proof. -/
theorem property_7_3 {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {D : Set (EuclideanSpace ℝ (Fin n))} {xstar : EuclideanSpace ℝ (Fin n)}
    (hint : xstar ∈ interior D) (hfix : G xstar = xstar) (hG : ContDiffAt ℝ 1 G xstar)
    (hρ : complexSpectralRadius (jacobianMatrix G xstar) < 1) :
    ∃ S ∈ 𝓝 xstar, S ⊆ D ∧ ∀ x₀ ∈ S,
      (∀ k, G^[k] x₀ ∈ D) ∧ Tendsto (fun k => G^[k] x₀) atTop (𝓝 xstar) := by
  have hd : HasFDerivAt G (fderiv ℝ G xstar) xstar :=
    (hG.differentiableAt one_ne_zero).hasFDerivAt
  have hpow : ∃ m : ℕ, ‖fderiv ℝ G xstar ^ m‖ < 1 :=
    exists_opNorm_toEuclideanLin_pow_lt_one_of_complexSpectralRadius_lt_one hρ
      (toEuclideanLin_jacobianMatrix G xstar).symm
  obtain ⟨S, hS, hSD, hSin⟩ := exists_ball_mapsTo_iterate_of_exists_norm_pow_fderiv_lt_one hfix
    hd hpow (mem_interior_iff_mem_nhds.1 hint)
  obtain ⟨δ, hδ, hconv⟩ := tendsto_iterate_of_exists_norm_pow_fderiv_lt_one hfix hd hpow
  refine ⟨S ∩ ball xstar δ, inter_mem hS (ball_mem_nhds xstar hδ), inter_subset_left.trans hSD,
    fun x₀ hx₀ => ⟨hSin x₀ hx₀.1, hconv x₀ hx₀.2⟩⟩

/-- **The remark after Property 7.3**: it suffices that `‖J_G(x*)‖ < 1` in some induced matrix
norm, here the spectral norm `‖toEuclideanCLM (J_G(x*))‖`, and then the convergence is geometric,
`‖x^{(k)} - x*‖ ≤ q^k ‖x^{(0)} - x*‖` for any `q` with `‖J_G(x*)‖ < q < 1`
(`exists_ball_norm_iterate_sub_le_of_norm_fderiv_lt_one`, the case `m = 1` of Ostrowski's
theorem). -/
theorem property_7_3_norm {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {D : Set (EuclideanSpace ℝ (Fin n))} {xstar : EuclideanSpace ℝ (Fin n)}
    (hint : xstar ∈ interior D) (hfix : G xstar = xstar) (hG : DifferentiableAt ℝ G xstar)
    {q : ℝ} (hq : ‖toEuclideanCLM (𝕜 := ℝ) (jacobianMatrix G xstar)‖ < q) (hq1 : q < 1) :
    ∃ S ∈ 𝓝 xstar, S ⊆ D ∧ ∀ x₀ ∈ S, ∀ k, G^[k] x₀ ∈ D ∧
      ‖G^[k] x₀ - xstar‖ ≤ q ^ k * ‖x₀ - xstar‖ := by
  rw [toEuclideanCLM_jacobianMatrix] at hq
  obtain ⟨ρ, hρ, hρD⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
  obtain ⟨δ, hδ, hball⟩ :=
    exists_ball_norm_iterate_sub_le_of_norm_fderiv_lt_one hfix hG.hasFDerivAt hq hq1
  refine ⟨ball xstar (min ρ δ), ball_mem_nhds xstar (lt_min hρ hδ),
    (ball_subset_ball (min_le_left _ _)).trans hρD, fun x₀ hx₀ k => ?_⟩
  have h := hball x₀ (ball_subset_ball (min_le_right _ _) hx₀) k
  refine ⟨hρD ?_, h.2⟩
  have hk : ‖G^[k] x₀ - xstar‖ ≤ ‖x₀ - xstar‖ := by
    calc ‖G^[k] x₀ - xstar‖ ≤ q ^ k * ‖x₀ - xstar‖ := h.2
      _ ≤ 1 * ‖x₀ - xstar‖ := by
          gcongr
          exact pow_le_one₀ (le_trans (norm_nonneg _) hq.le) hq1.le
      _ = ‖x₀ - xstar‖ := one_mul _
  rw [mem_ball, dist_eq_norm]
  exact lt_of_le_of_lt hk (lt_of_lt_of_le (mem_ball.1 hx₀) (min_le_left _ _))

end Jacobian

/-! ### Example 7.4 and Remark 7.1 -/

section Example74

/-- The system `F(x) = (x₁² + x₂² - 1, 2x₁ + x₂ - 1) = 0` of Example 7.4. -/
noncomputable def example_7_4_F (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[x 0 ^ 2 + x 1 ^ 2 - 1, 2 * x 0 + x 1 - 1]

/-- The first iteration function of (7.18), `G₁(x) = ((1 - x₂)/2, √(1 - x₁²))`. -/
noncomputable def example_7_4_G₁ (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[(1 - x 1) / 2, √(1 - x 0 ^ 2)]

/-- The second iteration function of (7.18), `G₂(x) = ((1 - x₂)/2, -√(1 - x₁²))`. -/
noncomputable def example_7_4_G₂ (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[(1 - x 1) / 2, -√(1 - x 0 ^ 2)]

/-- **Example 7.4, the algebraic part.** `x₁* = (0, 1)` and `x₂* = (4/5, -3/5)` solve the system,
and they are fixed points of `G₁` and `G₂` respectively: `G₁(x₁*) = x₁*`, `G₂(x₂*) = x₂*`. -/
theorem example_7_4_fixedPoint :
    example_7_4_F !₂[0, 1] = 0 ∧ example_7_4_F !₂[4 / 5, -3 / 5] = 0 ∧
      example_7_4_G₁ !₂[0, 1] = !₂[0, 1] ∧
      example_7_4_G₂ !₂[4 / 5, -3 / 5] = !₂[4 / 5, -3 / 5] := by
  have h35 : √(1 - (4 / 5 : ℝ) ^ 2) = 3 / 5 := by
    rw [show (1 : ℝ) - (4 / 5) ^ 2 = (3 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;>
    simp [example_7_4_F, example_7_4_G₁, example_7_4_G₂, h35] <;> norm_num

end Example74

/-- **Remark 7.1, corrected.** (a) Newton's method is the fixed-point iteration of
`G_N(x) = x - J_F(x)⁻¹ F(x)` (7.19): the backbone's `Newton.step F F'` is `G_N` definitionally,
and when `J_F(x)` is invertible, `G_N(x) = x` iff `F(x) = 0`. (b) With the residual
`r^{(k)} = F(x^{(k)})`, the Newton increment satisfies
`J_F(x^{(k)}) (x^{(k+1)} - x^{(k)}) = -r^{(k)}`, the preconditioned stationary Richardson step
with preconditioner `J_F(x^{(k)})`; the accelerated variant
`J_F(x^{(k)}) (x^{(k+1)} - x^{(k)}) = -α_k r^{(k)}` is the damped step
`x^{(k+1)} = x^{(k)} - α_k J_F(x^{(k)})⁻¹ F(x^{(k)})` of §7.2.6. The book prints the
preconditioner as `I - J_{G_N}(x^{(k)})`, which is wrong: `J_{G_N}(x) = -(D(J_F⁻¹)(x)·) F(x)`, so
`I - J_{G_N}(x) ≠ J_F(x)` in general (it is `I` at a root, where `J_F` need not be `I`). -/
theorem remark_7_1 (F : E → E) (F' : E → E →L[ℝ] E) (x : E) (e : E ≃L[ℝ] E)
    (he : (e : E →L[ℝ] E) = F' x) (α : ℝ) :
    Newton.step F F' x = x - (F' x).inverse (F x) ∧
      (Newton.step F F' x = x ↔ F x = 0) ∧
      F' x (Newton.step F F' x - x) = -F x ∧
      F' x ((x - α • (F' x).inverse (F x)) - x) = -(α • F x) := by
  have hinv : (F' x).inverse = (e.symm : E →L[ℝ] E) := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
  refine ⟨rfl, ⟨fun h => ?_, fun h => Newton.step_eq_self_of_eq_zero F F' h⟩, ?_, ?_⟩
  · rw [Newton.step, hinv, sub_eq_self] at h
    have := congrArg e h
    rwa [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, map_zero] at this
  · rw [Newton.step, hinv, sub_sub_cancel_left, map_neg, ← he]
    simp
  · rw [hinv, sub_sub_cancel_left, map_neg, map_smul, ← he]
    simp

end QuarteroniSaccoSaleri.Chapter07
