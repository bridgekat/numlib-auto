/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.RingTheory.Artinian.Module
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Analysis.Normed.Ring.Inverse
import Numlib.Conditioning.Problem

/-!
# Perturbation theory for linear systems

Let $A$ be an isomorphism of a normed space $E$, and let $\kappa(A) = \|A\| \|A^{-1}\|$ be its
condition number. This module gives the normwise error bounds for the linear system $Ax = b$: the
residual–error relation $\|x - y\| / \|x\| \le \kappa(A) \|b - Ay\| / \|b\|$, the perturbation bound
$$\frac{\|y - x\|}{\|x\|} \le \frac{\kappa(A)}{1 - \|A^{-1}\| \|\Delta A\|} \left( \frac{\|\Delta
A\|}{\|A\|} + \frac{\|\Delta b\|}{\|b\|} \right)$$ for $(A + \Delta A) y = b + \Delta b$, and the
derivative of the solution of a perturbed system. It also proves the Rigal–Gaches formula for the
normwise backward error: the least $\xi$ for which $y$ solves exactly some system
$(A + \Delta A) y = b + \Delta b$ with $\|\Delta A\| \le \xi \alpha \|A\|$ and
$\|\Delta b\| \le \xi \beta \|b\|$ is $\|b - Ay\| / (\alpha \|A\| \|y\| + \beta \|b\|)$. The sources
are [saad2003iterative], §1.13.2, [han2009theoretical], (2.4.1), [kress1998numerical], Theorem 5.3,
[higham2002accuracy], Theorems 7.1 and 7.2, and [fong2012cg], (3.2)–(3.4).

The module also contains the material of §3.1 of [quarteroni2000numerical]: Kahan's formula
$1 / \kappa(A)$ for the relative distance from $A$ to the singular operators (Remark 3.1), the two
inequalities of Theorem 3.2, the relative bounds of Theorem 3.3, and Property 3.1 on approximate
inverses with the a posteriori bound (3.20). Finally it shows that $\kappa(A)$ is the relative
condition number of the inversion $T \mapsto T^{-1}$ at $A$, and proves the limit formula (2.6.7) of
[golub2013matrix] for $\kappa(A)$.

## Main definitions

* `backwardError`: the normwise backward error $\|b - Ay\| / (\alpha \|A\| \|y\| + \beta \|b\|)$.

## Main results

* `ContinuousLinearEquiv.relative_error_le_condNumber_mul_relative_residual`,
  `relative_error_le_condNumber_mul_relative_residual`: the residual–error relation, which is the
  upper inequality of Theorem 3.2 of [quarteroni2000numerical].
* `ContinuousLinearEquiv.relative_residual_le_condNumber_mul_relative_error`: the lower inequality
  of Theorem 3.2 of [quarteroni2000numerical].
* `relative_error_le_norm_inverse`: the rigorous form of (2.6.2) of [golub2013matrix], of which
  `relative_error_le_condNumber` is the consequence after $\|b\| \le \|A\| \|x\|$.
* `isLeast_backwardError`: the Rigal–Gaches theorem.
* `hasDerivAt_perturbed_solution`: the derivative of the solution of $(A + \varepsilon B)
  x(\varepsilon) = b + \varepsilon e$ at $\varepsilon = 0$.
* `ContinuousLinearEquiv.isLeast_dist_singular`: Kahan's distance to singularity, (3.6) of
  [quarteroni2000numerical], in any operator norm on a finite-dimensional space.
* `NormedRing.norm_le_of_not_isUnit_add`: its lower half, which is also the corrected form of (3.7)
  of [quarteroni2000numerical].
* `ContinuousLinearEquiv.relCondNumber_ringInverse`: $\kappa(A)$ is the relative condition number of
  inversion at $A$.
* `ContinuousLinearEquiv.tendsto_iSup_norm_inverse_add_sub_div`: the limit formula (2.6.7) of
  [golub2013matrix].
* `relative_error_le_of_norm_le_mul`, `norm_add_div_le_of_norm_le_mul`: the bounds (3.13) and (3.12)
  of Theorem 3.3 of [quarteroni2000numerical].
* `NormedRing.norm_inverse_le_of_norm_mul_sub_one_lt` and its companions: Property 3.1 of
  [quarteroni2000numerical] in a complete normed ring, with (3.19).
* `norm_error_le_of_norm_mul_sub_one_lt`: the a posteriori bound (3.20) of
  [quarteroni2000numerical].

## Implementation notes

* The condition number is `NormedRing.condNumber` for an element of the operator ring $E \to E$ and
  `ContinuousLinearEquiv.condNumber` for an isomorphism $E \to F$; for $F = E$ the two agree.
* The proof that $\kappa(A)$ is the relative condition number of inversion uses the first-order
  formula `Conditioning.relCondNumber_eq_enorm_fderiv` of `Numlib.Conditioning.Problem`. The
  derivative of inversion at $A$ is $H \mapsto -A^{-1} H A^{-1}$, and its norm is $\|A^{-1}\|^2$
  (`ContinuousLinearEquiv.norm_mulLeftRight_symm_symm`, from
  `ContinuousLinearMap.norm_mulLeftRight_apply_apply`).
* The componentwise theory, with the Skeel condition numbers of (3.14)–(3.16) of
  [quarteroni2000numerical], is in `Numlib.Conditioning.LinearSystem.Componentwise`.
* There are two backward errors in the library. The root-namespace `backwardError` of this module is
  the normwise, weighted backward error of a linear system, a real number.
  `Conditioning.backwardError` of `Numlib.Conditioning.Method` is the $[0, \infty]$-valued infimum
  of the sizes of the data perturbations for which a computed solution of an abstract problem is
  exact. The first weights the perturbations of $A$ and $b$ relatively and by tolerances; the second
  is absolute and for a single datum. No relation between them is stated.
-/

open Filter NormedRing Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

section TwoSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **The residual–error relation for two spaces.** Let $L : E \to F$ be an isomorphism of normed
spaces, and let $L v = w$ and $L v' = w'$ with $w \neq 0$. Then $$\frac{\|v - v'\|}{\|v\|} \le
\kappa(L) \, \frac{\|w - w'\|}{\|w\|},$$ where $\kappa(L) = \|L\| \|L^{-1}\|$. So the relative
error of the solution of $L v = w$ is at most $\kappa(L)$ times the relative error of the data.
This is (2.4.1) of [han2009theoretical].

The condition number is `ContinuousLinearEquiv.condNumber`. The single-space
`relative_error_le_condNumber_mul_relative_residual` is the case $F = E$. -/
theorem ContinuousLinearEquiv.relative_error_le_condNumber_mul_relative_residual (L : E ≃L[𝕜] F)
    {v v' : E} {w w' : F} (hv : L v = w) (hv' : L v' = w') (hw : w ≠ 0) :
    ‖v - v'‖ / ‖v‖ ≤ L.condNumber * (‖w - w'‖ / ‖w‖) := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hw (by rw [← hv]; simp)
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hvv : v - v' = (L.symm : F →L[𝕜] E) (w - w') := by
    rw [← hv, ← hv']
    simp
  have h1 : ‖v - v'‖ ≤ ‖(L.symm : F →L[𝕜] E)‖ * ‖w - w'‖ := by
    rw [hvv]
    exact (L.symm : F →L[𝕜] E).le_opNorm _
  have h2 : ‖w‖ ≤ ‖(L : E →L[𝕜] F)‖ * ‖v‖ := by
    rw [← hv]
    simpa using (L : E →L[𝕜] F).le_opNorm v
  rw [ContinuousLinearEquiv.condNumber, ← mul_div_assoc, div_le_div_iff₀ hvn hwn]
  calc ‖v - v'‖ * ‖w‖
      ≤ ‖(L.symm : F →L[𝕜] E)‖ * ‖w - w'‖ * (‖(L : E →L[𝕜] F)‖ * ‖v‖) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = ‖(L : E →L[𝕜] F)‖ * ‖(L.symm : F →L[𝕜] E)‖ * ‖w - w'‖ * ‖v‖ := by ring

end TwoSpace

/-- **The residual–error relation.** Let $A$ be an isomorphism of the normed space $E$, and let
$Ax = b$ with $b \neq 0$. Then for every $y \in E$, $$\frac{\|x - y\|}{\|x\|} \le \kappa(A) \,
\frac{\|b - Ay\|}{\|b\|},$$ where $\kappa(A) = \|A\| \|A^{-1}\|$. This is (2.4.1) of
[han2009theoretical], and the upper inequality of Theorem 3.2 of [quarteroni2000numerical].

The condition number is `NormedRing.condNumber` of $A$ in the operator ring. The theorem is the
case $F = E$, $w' = Ay$ of
`ContinuousLinearEquiv.relative_error_le_condNumber_mul_relative_residual`. -/
theorem relative_error_le_condNumber_mul_relative_residual (A : E ≃L[𝕜] E) {b x y : E}
    (hx : A x = b) (hb : b ≠ 0) :
    ‖x - y‖ / ‖x‖ ≤ condNumber (A : E →L[𝕜] E) * (‖b - A y‖ / ‖b‖) := by
  rw [ContinuousLinearEquiv.condNumber_coe]
  exact A.relative_error_le_condNumber_mul_relative_residual hx rfl hb

/-- **The normwise perturbation bound with $\|A^{-1}\|$.** Let $A$ be an isomorphism of the normed
space $E$ and $\Delta A$ a bounded operator on $E$ with $\|A^{-1}\| \|\Delta A\| < 1$. If
$Ax = b$ with $x \neq 0$ and $(A + \Delta A) y = b + \Delta b$, then $$\frac{\|y - x\|}{\|x\|}
\le \frac{\|A^{-1}\|}{1 - \|A^{-1}\| \|\Delta A\|} \left( \frac{\|\Delta b\|}{\|x\|} + \|\Delta
A\| \right).$$

This is the rigorous form of (2.6.2) of [golub2013matrix]. With $\Delta A = \varepsilon F$ and
$\Delta b = \varepsilon f$ it is the first-order bound of the source, with its
$O(\varepsilon^2)$ term made explicit as the factor $1 / (1 - |\varepsilon| \|A^{-1}\| \|F\|)$.
The proof uses $A (y - x) = \Delta b - \Delta A \, y$ and $\|y\| \le \|y - x\| + \|x\|$. -/
theorem relative_error_le_norm_inverse (A : E ≃L[𝕜] E) (ΔA : E →L[𝕜] E) {b Δb x y : E}
    (hx : A x = b) (hy : ((A : E →L[𝕜] E) + ΔA) y = b + Δb)
    (hsmall : ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ < 1) (hx0 : x ≠ 0) :
    ‖y - x‖ / ‖x‖ ≤ ‖(A.symm : E →L[𝕜] E)‖ / (1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖)
      * (‖Δb‖ / ‖x‖ + ‖ΔA‖) := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hden : 0 < 1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ := by linarith
  -- the residual identity `A (y - x) = Δb - ΔA y`
  have hyx : y - x = (A.symm : E →L[𝕜] E) (Δb - ΔA y) := by
    have hAy : (A : E →L[𝕜] E) y + ΔA y = b + Δb := by rw [← hy]; simp
    have hb' : b = (A : E →L[𝕜] E) y + ΔA y - Δb := by rw [hAy]; abel
    have hsub : Δb - ΔA y = (A : E →L[𝕜] E) y - b := by rw [hb']; abel
    rw [hsub, ← hx]
    simp
  have h1 : ‖y - x‖
      ≤ ‖(A.symm : E →L[𝕜] E)‖ * ‖Δb‖ + ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ * ‖y‖ := by
    calc ‖y - x‖ ≤ ‖(A.symm : E →L[𝕜] E)‖ * ‖Δb - ΔA y‖ := by
          rw [hyx]
          exact (A.symm : E →L[𝕜] E).le_opNorm _
      _ ≤ ‖(A.symm : E →L[𝕜] E)‖ * (‖Δb‖ + ‖ΔA‖ * ‖y‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact (norm_sub_le _ _).trans (by gcongr; exact ΔA.le_opNorm _)
      _ = ‖(A.symm : E →L[𝕜] E)‖ * ‖Δb‖ + ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ * ‖y‖ := by ring
  have h2 : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by simpa using norm_add_le (y - x) x
  have h3 : ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ * ‖y‖
      ≤ ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ * (‖y - x‖ + ‖x‖) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have hexp : ‖(A.symm : E →L[𝕜] E)‖ / (1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖)
        * (‖Δb‖ / ‖x‖ + ‖ΔA‖) * ‖x‖
      = (‖(A.symm : E →L[𝕜] E)‖ * ‖Δb‖ + ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ * ‖x‖)
        / (1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖) := by
    field_simp
  rw [div_le_iff₀ hxn, hexp, le_div_iff₀ hden]
  nlinarith [h1, h3]

/-- **The normwise perturbation bound.** Let $A$ be an isomorphism of the normed space $E$ and
$\Delta A$ a bounded operator on $E$ with $\|A^{-1}\| \|\Delta A\| < 1$. If $Ax = b$ with
$x \neq 0$ and $b \neq 0$, and $(A + \Delta A) y = b + \Delta b$, then $$\frac{\|y - x\|}{\|x\|}
\le \frac{\kappa(A)}{1 - \|A^{-1}\| \|\Delta A\|} \left( \frac{\|\Delta A\|}{\|A\|} +
\frac{\|\Delta b\|}{\|b\|} \right),$$ where $\kappa(A) = \|A\| \|A^{-1}\|$. This is (1.76) of
[saad2003iterative], Theorem 5.3 of [kress1998numerical] and Theorem 7.2 of
[higham2002accuracy].

The condition number is `NormedRing.condNumber`. The theorem is `relative_error_le_norm_inverse`
after $\|b\| \le \|A\| \|x\|$. -/
theorem relative_error_le_condNumber (A : E ≃L[𝕜] E) (ΔA : E →L[𝕜] E)
    {b Δb x y : E} (hx : A x = b) (hy : ((A : E →L[𝕜] E) + ΔA) y = b + Δb)
    (hsmall : ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ < 1) (hx0 : x ≠ 0) (hb : b ≠ 0) :
    ‖y - x‖ / ‖x‖ ≤ condNumber (A : E →L[𝕜] E) / (1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖)
      * (‖ΔA‖ / ‖(A : E →L[𝕜] E)‖ + ‖Δb‖ / ‖b‖) := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hAb : ‖b‖ ≤ ‖(A : E →L[𝕜] E)‖ * ‖x‖ := by
    rw [← hx]
    simpa using (A : E →L[𝕜] E).le_opNorm x
  have hN : 0 < ‖(A : E →L[𝕜] E)‖ := by nlinarith [norm_nonneg (A : E →L[𝕜] E)]
  have hden : 0 < 1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ := by linarith
  refine (relative_error_le_norm_inverse A ΔA hx hy hsmall hx0).trans ?_
  have hexp : condNumber (A : E →L[𝕜] E) / (1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖)
        * (‖ΔA‖ / ‖(A : E →L[𝕜] E)‖ + ‖Δb‖ / ‖b‖)
      = ‖(A.symm : E →L[𝕜] E)‖ / (1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖)
        * (‖(A : E →L[𝕜] E)‖ * ‖Δb‖ / ‖b‖ + ‖ΔA‖) := by
    rw [ContinuousLinearEquiv.condNumber_eq]
    field_simp
    ring
  rw [hexp]
  refine mul_le_mul_of_nonneg_left (add_le_add_left ?_ _)
    (div_nonneg (norm_nonneg _) hden.le)
  rw [div_le_div_iff₀ hxn hbn]
  nlinarith [norm_nonneg Δb]

/-- Let $E$ be a Banach space, $A$ an isomorphism of $E$, and $\Delta A$ a bounded operator on $E$
with $\|A^{-1}\| \|\Delta A\| < 1$. Then for every $b' \in E$ the perturbed system
$(A + \Delta A) y = b'$ has a unique solution $y$. This complements
`relative_error_le_condNumber`. -/
theorem exists_perturbed_solution [CompleteSpace E] (A : E ≃L[𝕜] E) (ΔA : E →L[𝕜] E)
    (hsmall : ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ < 1) (b' : E) :
    ∃! y, ((A : E →L[𝕜] E) + ΔA) y = b' := by
  obtain ⟨e', he', -, -⟩ := ContinuousLinearEquiv.exists_symm_norm_le_of_add A ΔA hsmall
  refine ⟨e'.symm b', ?_, fun z hz => ?_⟩
  · rw [← he']; simp
  · rw [← he'] at hz
    rw [← hz]; simp

section BackwardError

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The **normwise backward error** of an approximate solution $y$ of $Ax = b$, with the tolerances
$\alpha$ on $A$ and $\beta$ on $b$: $$\frac{\|b - Ay\|}{\alpha \|A\| \|y\| + \beta \|b\|}.$$
Here $E$ is an inner product space over $\mathbb{R}$ or $\mathbb{C}$ and $A$ is a bounded
operator on $E$. The value is $0$ when the denominator is $0$.

By the Rigal–Gaches theorem `isLeast_backwardError`, this is the least $\xi$ for which $y$
solves exactly some system $(A + \Delta A) y = b + \Delta b$ with
$\|\Delta A\| \le \xi \alpha \|A\|$ and $\|\Delta b\| \le \xi \beta \|b\|$ ([fong2012cg],
(3.2)). -/
noncomputable def backwardError (A : E →L[𝕜] E) (b y : E) (α β : ℝ) : ℝ :=
  ‖b - A y‖ / (α * ‖A‖ * ‖y‖ + β * ‖b‖)

/-- The backward error is the quotient $\|b - Ay\| / (\alpha \|A\| \|y\| + \beta \|b\|)$. -/
private theorem backwardError_def (A : E →L[𝕜] E) (b y : E) (α β : ℝ) :
    backwardError A b y α β = ‖b - A y‖ / (α * ‖A‖ * ‖y‖ + β * ‖b‖) := rfl

/-- If $\alpha \|A\| \|y\| + \beta \|b\| > 0$, then the backward error is nonnegative. -/
private theorem backwardError_nonneg (A : E →L[𝕜] E) (b y : E) {α β : ℝ}
    (hpos : 0 < α * ‖A‖ * ‖y‖ + β * ‖b‖) : 0 ≤ backwardError A b y α β := by
  rw [backwardError_def]
  positivity

/-- **The optimal perturbations.** Let $\alpha, \beta \ge 0$ with
$\alpha \|A\| \|y\| + \beta \|b\| > 0$, and let $\xi$ be the backward error of $y$. Then there
are a bounded operator $\Delta A$ and a vector $\Delta b$ with $$(A + \Delta A) y = b + \Delta
b, \qquad \|\Delta A\| = \xi \alpha \|A\|, \qquad \|\Delta b\| = \xi \beta \|b\|.$$

For $y \neq 0$ the perturbations are those of (3.3) of [fong2012cg]: with $r = b - Ay$ and
$\omega = \beta \|b\| / (\alpha \|A\| \|y\| + \beta \|b\|)$, they are $\Delta A = ((1 - \omega)
/ \|y\|^2) \, r \otimes y$ and $\Delta b = -\omega r$, where $r \otimes y$ is the rank-one
operator $z \mapsto \langle y, z \rangle \, r$. For $y = 0$ the proof takes
$\Delta A = \xi \alpha A$ and $\Delta b = -b$. -/
theorem exists_optimal_perturbation (A : E →L[𝕜] E) (b y : E) {α β : ℝ} (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hpos : 0 < α * ‖A‖ * ‖y‖ + β * ‖b‖) :
    ∃ (ΔA : E →L[𝕜] E) (Δb : E), (A + ΔA) y = b + Δb ∧
      ‖ΔA‖ = backwardError A b y α β * α * ‖A‖ ∧ ‖Δb‖ = backwardError A b y α β * β * ‖b‖ := by
  have hη0 : 0 ≤ backwardError A b y α β := backwardError_nonneg A b y hpos
  by_cases hy : y = 0
  · subst hy
    have hbpos : 0 < β * ‖b‖ := by simpa using hpos
    have hβ0 : β ≠ 0 := by rintro rfl; simp at hbpos
    have hbne : ‖b‖ ≠ 0 := by rintro h; rw [h, mul_zero] at hbpos; exact lt_irrefl 0 hbpos
    refine ⟨((backwardError A b (0 : E) α β * α : ℝ) : 𝕜) • A, -b, by simp, ?_, ?_⟩
    · rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (by positivity), mul_assoc]
    · rw [norm_neg, backwardError_def]
      simp only [map_zero, sub_zero, norm_zero, mul_zero, zero_add]
      field_simp
  · set D : ℝ := α * ‖A‖ * ‖y‖ + β * ‖b‖ with hDdef
    set ω : ℝ := β * ‖b‖ / D with hωdef
    have hDne : D ≠ 0 := ne_of_gt hpos
    have hω0 : 0 ≤ ω := by rw [hωdef]; positivity
    have hω1 : 1 - ω = α * ‖A‖ * ‖y‖ / D := by
      rw [hωdef, eq_div_iff hDne, sub_mul, one_mul, div_mul_cancel₀ _ hDne, hDdef]
      ring
    have hc0 : 0 ≤ (1 - ω) / ‖y‖ ^ 2 := by
      rw [hω1]
      positivity
    refine ⟨(innerSL 𝕜 y).smulRight ((((1 - ω) / ‖y‖ ^ 2 : ℝ) : 𝕜) • (b - A y)),
      ((-ω : ℝ) : 𝕜) • (b - A y), ?_, ?_, ?_⟩
    · have hyy : (inner 𝕜 y y : 𝕜) = ((‖y‖ ^ 2 : ℝ) : 𝕜) := by
        rw [inner_self_eq_norm_sq_to_K]
        push_cast
        ring
      have happ : ((innerSL 𝕜 y).smulRight ((((1 - ω) / ‖y‖ ^ 2 : ℝ) : 𝕜) • (b - A y))) y
          = ((1 - ω : ℝ) : 𝕜) • (b - A y) := by
        rw [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, hyy, smul_smul,
          ← RCLike.ofReal_mul]
        congr 2
        field_simp
      rw [add_apply, happ]
      push_cast
      module
    · rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, norm_smul,
        RCLike.norm_ofReal, abs_of_nonneg hc0, backwardError_def, ← hDdef, hω1]
      field_simp
    · rw [norm_smul, RCLike.norm_ofReal, abs_neg, abs_of_nonneg hω0, backwardError_def, ← hDdef,
        hωdef]
      field_simp

/-- **The Rigal–Gaches theorem**, Theorem 7.1 of [higham2002accuracy]. Let $\alpha, \beta \ge 0$
with $\alpha \|A\| \|y\| + \beta \|b\| > 0$. Then the backward error $\|b - Ay\| / (\alpha \|A\|
\|y\| + \beta \|b\|)$ is the least real $\xi$ such that $(A + \Delta A) y = b + \Delta b$ for
some bounded operator $\Delta A$ and vector $\Delta b$ with $\|\Delta A\| \le \xi \alpha \|A\|$
and $\|\Delta b\| \le \xi \beta \|b\|$. -/
theorem isLeast_backwardError (A : E →L[𝕜] E) (b y : E) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hpos : 0 < α * ‖A‖ * ‖y‖ + β * ‖b‖) :
    IsLeast {ξ : ℝ | ∃ (ΔA : E →L[𝕜] E) (Δb : E), (A + ΔA) y = b + Δb ∧
        ‖ΔA‖ ≤ ξ * α * ‖A‖ ∧ ‖Δb‖ ≤ ξ * β * ‖b‖}
      (backwardError A b y α β) := by
  constructor
  · obtain ⟨ΔA, Δb, h1, h2, h3⟩ := exists_optimal_perturbation A b y hα hβ hpos
    exact ⟨ΔA, Δb, h1, h2.le, h3.le⟩
  · rintro ξ ⟨ΔA, Δb, h1, h2, h3⟩
    have hb : b = A y + ΔA y - Δb := by
      rw [← add_apply, h1]; abel
    have hr : b - A y = ΔA y - Δb := by rw [hb]; abel
    rw [backwardError_def, div_le_iff₀ hpos]
    calc ‖b - A y‖ = ‖ΔA y - Δb‖ := by rw [hr]
      _ ≤ ‖ΔA y‖ + ‖Δb‖ := norm_sub_le _ _
      _ ≤ ‖ΔA‖ * ‖y‖ + ‖Δb‖ := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ξ * α * ‖A‖ * ‖y‖ + ξ * β * ‖b‖ := by gcongr
      _ = ξ * (α * ‖A‖ * ‖y‖ + β * ‖b‖) := by ring

/-- **The stopping rule** (3.4) of [fong2012cg]. If $\alpha \|A\| \|y\| + \beta \|b\| > 0$, then for
every real $\xi$, the backward error of $y$ is at most $\xi$ if and only if $$\|b - Ay\| \le \xi
\, (\alpha \|A\| \|y\| + \beta \|b\|).$$
-/
theorem backwardError_le_iff (A : E →L[𝕜] E) (b y : E) {α β ξ : ℝ}
    (hpos : 0 < α * ‖A‖ * ‖y‖ + β * ‖b‖) :
    backwardError A b y α β ≤ ξ ↔ ‖b - A y‖ ≤ ξ * (α * ‖A‖ * ‖y‖ + β * ‖b‖) := by
  rw [backwardError_def, div_le_iff₀ hpos]

end BackwardError

/-- **First-order perturbation theory for a linear system.** Let $E$ be a Banach space, $A$ an
isomorphism of $E$, $B$ a bounded operator on $E$, and $b, e \in E$. Then the solution
$x(\varepsilon) = (A + \varepsilon B)^{-1} (b + \varepsilon e)$ of the perturbed system $(A +
\varepsilon B) x(\varepsilon) = b + \varepsilon e$ is differentiable in $\varepsilon$ at $0$,
with $$x'(0) = A^{-1} (e - B A^{-1} b).$$ This is (1.74)–(1.75) of [saad2003iterative], Theorem
5.3 of [kress1998numerical], and Chapter 7 of [higham2002accuracy].

The inverse is `Ring.inverse` in the algebra of bounded operators, which is $0$ at a
non-invertible operator. This value does not matter here: $A$ is invertible, so
$A + \varepsilon B$ is invertible for all small $\varepsilon$, and near $0$ the map agrees with
the solution of the perturbed system. -/
theorem hasDerivAt_perturbed_solution [CompleteSpace E] (A : E ≃L[𝕜] E) (B : E →L[𝕜] E)
    (b e : E) :
    HasDerivAt (fun ε : 𝕜 => (Ring.inverse ((A : E →L[𝕜] E) + ε • B)) (b + ε • e))
      ((A.symm : E →L[𝕜] E) (e - B ((A.symm : E →L[𝕜] E) b))) 0 := by
  obtain ⟨u, hu⟩ : IsUnit (A : E →L[𝕜] E) := ⟨A.toUnit, rfl⟩
  have hg : HasDerivAt (fun ε : 𝕜 => (A : E →L[𝕜] E) + ε • B) B 0 := by
    simpa using (hasDerivAt_const_add_iff (A : E →L[𝕜] E)).2
      (HasDerivAt.smul_const (hasDerivAt_id (0 : 𝕜)) B)
  have hg0 : (fun ε : 𝕜 => (A : E →L[𝕜] E) + ε • B) 0 = (u : E →L[𝕜] E) := by
    simp [hu]
  have hinv : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight 𝕜 (E →L[𝕜] E) (↑u⁻¹) (↑u⁻¹))
      ((fun ε : 𝕜 => (A : E →L[𝕜] E) + ε • B) 0) := by
    rw [hg0]
    exact hasFDerivAt_ringInverse u
  have hcomp : HasDerivAt (fun ε : 𝕜 => Ring.inverse ((A : E →L[𝕜] E) + ε • B))
      ((-ContinuousLinearMap.mulLeftRight 𝕜 (E →L[𝕜] E) (↑u⁻¹) (↑u⁻¹)) B) 0 := by
    have h := HasFDerivAt.comp_hasDerivAt 0 hinv hg
    exact h
  have hb : HasDerivAt (fun ε : 𝕜 => b + ε • e) e 0 := by
    simpa using (hasDerivAt_const_add_iff b).2
      (HasDerivAt.smul_const (hasDerivAt_id (0 : 𝕜)) e)
  have hAinv : ((u⁻¹ : (E →L[𝕜] E)ˣ) : E →L[𝕜] E) = (A.symm : E →L[𝕜] E) := by
    rw [← ContinuousLinearEquiv.ring_inverse_coe A, ← hu, Ring.inverse_unit]
  have hres := HasDerivAt.clm_apply hcomp hb
  convert hres using 1
  simp only [zero_smul, add_zero, ContinuousLinearEquiv.ring_inverse_coe, hAinv, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, map_sub]
  abel

/-! ### The lower inequality of the residual–error relation -/

section Lower

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **The lower inequality of Theorem 3.2** of [quarteroni2000numerical], the first half of (3.11).
Let $L : E \to F$ be an isomorphism of normed spaces, and let $L v = w$ and $L v' = w'$ with
$v \neq 0$. Then $$\frac{\|w - w'\|}{\|w\|} \le \kappa(L) \, \frac{\|v - v'\|}{\|v\|},$$ where
$\kappa(L) = \|L\| \|L^{-1}\|$. In the notation of the source, $\frac{1}{\kappa(A)}
\frac{\|\delta b\|}{\|b\|} \le \frac{\|\delta x\|}{\|x\|}$.

The proof applies the upper inequality
`ContinuousLinearEquiv.relative_error_le_condNumber_mul_relative_residual` to $L^{-1}$, whose
condition number is that of $L$. -/
theorem ContinuousLinearEquiv.relative_residual_le_condNumber_mul_relative_error (L : E ≃L[𝕜] F)
    {v v' : E} {w w' : F} (hv : L v = w) (hv' : L v' = w') (hv0 : v ≠ 0) :
    ‖w - w'‖ / ‖w‖ ≤ L.condNumber * (‖v - v'‖ / ‖v‖) := by
  have h := L.symm.relative_error_le_condNumber_mul_relative_residual (v := w) (v' := w')
    (w := v) (w' := v') (by rw [← hv]; simp) (by rw [← hv']; simp) hv0
  rwa [ContinuousLinearEquiv.condNumber_symm] at h

end Lower

/-! ### The distance to singularity -/

section Distance

variable {R : Type*} [NormedRing R] [NormOneClass R] [CompleteSpace R]

omit [NormOneClass R] in
/-- **The lower half of Kahan's distance-to-singularity formula** (Remark 3.1 of
[quarteroni2000numerical]). Let $R$ be a complete normed ring and $a \in R$ a unit. If $a + t$
is not a unit, then $$\|t\| \ge \|a^{-1}\|^{-1}.$$

This is also the corrected form of (3.7) of [quarteroni2000numerical]: a perturbation with
$\|\delta A\| \|A^{-1}\| < 1$ leaves $A + \delta A$ nonsingular. The printed (3.7) has $\|A\|$
in place of $\|A^{-1}\|$ and states the implication in the opposite direction. The theorem is
the contrapositive of `Units.isUnit_add_of_norm_lt`. -/
theorem NormedRing.norm_le_of_not_isUnit_add {a t : R} (ha : IsUnit a) (h : ¬ IsUnit (a + t)) :
    ‖Ring.inverse a‖⁻¹ ≤ ‖t‖ := by
  obtain ⟨x, rfl⟩ := ha
  by_contra hlt
  rw [not_le, Ring.inverse_unit] at hlt
  exact h (Units.isUnit_add_of_norm_lt x t hlt)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Let $E$ be a nontrivial finite-dimensional normed space over $\mathbb{R}$ or $\mathbb{C}$. Every
bounded operator $f$ on $E$ attains its norm on the unit sphere: there is $y \in E$ with
$\|y\| = 1$ and $\|f y\| = \|f\|$. -/
theorem ContinuousLinearMap.exists_norm_eq_one_and_norm_apply_eq [FiniteDimensional 𝕜 E]
    [Nontrivial E] (f : E →L[𝕜] E) : ∃ y : E, ‖y‖ = 1 ∧ ‖f y‖ = ‖f‖ := by
  have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  have hne : (Metric.sphere (0 : E) 1).Nonempty := by
    have : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    exact NormedSpace.sphere_nonempty.2 zero_le_one
  obtain ⟨y, hy, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hne
    (f.continuous.norm.continuousOn)
  rw [mem_sphere_zero_iff_norm] at hy
  refine ⟨y, hy, le_antisymm (by simpa [hy] using f.le_opNorm y) ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound f (norm_nonneg _) fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx0
  have h1 : ‖((‖x‖⁻¹ : ℝ) : 𝕜) • x‖ = 1 := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.2 (norm_nonneg _)),
      inv_mul_cancel₀ hxn]
  have h2 : ‖f (((‖x‖⁻¹ : ℝ) : 𝕜) • x)‖ ≤ ‖f y‖ := hmax (mem_sphere_zero_iff_norm.2 h1)
  rw [map_smul, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.2 (norm_nonneg x)),
    inv_mul_le_iff₀ (norm_pos_iff.2 hx0), mul_comm] at h2
  exact h2

/-- **The upper half of Kahan's distance-to-singularity formula** (Remark 3.1 of
[quarteroni2000numerical], after the references Kah66 and Gas83 of the source). Let $E$ be a
nontrivial finite-dimensional normed space over $\mathbb{R}$ or $\mathbb{C}$, and let $A$ be an
isomorphism of $E$. Then there is a bounded operator $t$ on $E$ such that $A + t$ is not
invertible and $$\|t\| = \|A^{-1}\|^{-1}.$$

The perturbation constructed has rank one. Let $y$ be a unit vector with
$\|A^{-1} y\| = \|A^{-1}\|$, let $x = A^{-1} y$, and let $\varphi$ be a norming functional of
$x$. Then $t = -\|x\|^{-1} \varphi(\cdot) \, y$ sends $x$ to $-y$, so $(A + t) x = 0$. This is
the construction of the Rigal–Gaches optimal perturbation (`exists_optimal_perturbation`) with
the inner product replaced by a norming functional, which makes it valid in any operator norm. -/
theorem ContinuousLinearEquiv.exists_not_isUnit_add_norm_le [FiniteDimensional 𝕜 E]
    [Nontrivial E] (A : E ≃L[𝕜] E) :
    ∃ t : E →L[𝕜] E, ¬ IsUnit ((A : E →L[𝕜] E) + t) ∧ ‖t‖ = ‖(A.symm : E →L[𝕜] E)‖⁻¹ := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  obtain ⟨y, hy1, hy⟩ := (A.symm : E →L[𝕜] E).exists_norm_eq_one_and_norm_apply_eq
  set x := (A.symm : E →L[𝕜] E) y with hx
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy1
  have hx0 : x ≠ 0 := by
    rw [hx]
    intro h
    exact hy0 (by simpa using congrArg A h)
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx0
  obtain ⟨φ, hφ1, hφx⟩ := exists_dual_vector 𝕜 x hxn
  refine ⟨-(((‖x‖⁻¹ : ℝ) : 𝕜) • φ.smulRight y), fun hu => ?_, ?_⟩
  · have hinj := (ContinuousLinearMap.isUnit_iff_bijective.1 hu).1
    have h0 : ((A : E →L[𝕜] E) + -(((‖x‖⁻¹ : ℝ) : 𝕜) • φ.smulRight y)) x = 0 := by
      change (A : E →L[𝕜] E) x + -(((‖x‖⁻¹ : ℝ) : 𝕜) • (φ x • y)) = 0
      rw [hφx, smul_smul, ← RCLike.ofReal_mul, inv_mul_cancel₀ hxn, RCLike.ofReal_one, one_smul,
        hx]
      simp
    exact hx0 (hinj (h0.trans (by simp)))
  · rw [norm_neg, norm_smul, ContinuousLinearMap.norm_smulRight_apply, hφ1, hy1, RCLike.norm_ofReal,
      abs_of_nonneg (inv_nonneg.2 (norm_nonneg _)), hx, hy]
    ring

/-- Let $E$ be a nontrivial finite-dimensional normed space over $\mathbb{R}$ or $\mathbb{C}$. For
bounded operators $a$ and $b$ on $E$ there is a bounded operator $T$ with $\|T\| = 1$ and
$\|a T b\| = \|a\| \|b\|$.

Take unit vectors $y$ and $z$ at which $a$ and $b$ attain their norms and a norming functional
$\varphi$ of $b z$. The rank-one operator $T = \varphi(\cdot) \, y$ gives
$a T b z = \|b z\| \, a y$. -/
theorem ContinuousLinearMap.exists_norm_eq_one_and_norm_mul_mul_eq [FiniteDimensional 𝕜 E]
    [Nontrivial E] (a b : E →L[𝕜] E) : ∃ T : E →L[𝕜] E, ‖T‖ = 1 ∧ ‖a * T * b‖ = ‖a‖ * ‖b‖ := by
  obtain ⟨y, hy1, hay⟩ := a.exists_norm_eq_one_and_norm_apply_eq
  obtain ⟨z, hz1, hbz⟩ := b.exists_norm_eq_one_and_norm_apply_eq
  obtain ⟨φ, hφ1, hφ⟩ := exists_dual_vector' 𝕜 (b z)
  have hT : ‖φ.smulRight y‖ = 1 := by rw [norm_smulRight_apply, hφ1, hy1, one_mul]
  refine ⟨φ.smulRight y, hT, le_antisymm ?_ ?_⟩
  · calc ‖a * φ.smulRight y * b‖ ≤ ‖a * φ.smulRight y‖ * ‖b‖ := _root_.norm_mul_le _ _
      _ ≤ ‖a‖ * ‖φ.smulRight y‖ * ‖b‖ := by gcongr; exact _root_.norm_mul_le _ _
      _ = ‖a‖ * ‖b‖ := by rw [hT, mul_one]
  have happ : (a * φ.smulRight y * b) z = ((‖b z‖ : ℝ) : 𝕜) • a y := by
    change a (φ (b z) • y) = _
    rw [hφ, map_smul]
  calc ‖a‖ * ‖b‖ = ‖(a * φ.smulRight y * b) z‖ := by
        rw [happ, norm_smul, RCLike.norm_ofReal, abs_norm, hbz, hay, mul_comm]
    _ ≤ ‖a * φ.smulRight y * b‖ * ‖z‖ := le_opNorm _ _
    _ = ‖a * φ.smulRight y * b‖ := by rw [hz1, mul_one]

/-- Let $E$ be a nontrivial finite-dimensional normed space over $\mathbb{R}$ or $\mathbb{C}$. For
bounded operators $a$ and $b$ on $E$, the two-sided multiplication $T \mapsto a T b$ on the
algebra of bounded operators has norm $\|a\| \|b\|$.

The inequality $\le$ is submultiplicativity
(`ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le`). The inequality $\ge$ comes from the
operator $T$ of `ContinuousLinearMap.exists_norm_eq_one_and_norm_mul_mul_eq`. The map
$T \mapsto a T b$ is `ContinuousLinearMap.mulLeftRight 𝕜 (E →L[𝕜] E) a b`. -/
theorem ContinuousLinearMap.norm_mulLeftRight_apply_apply [FiniteDimensional 𝕜 E] [Nontrivial E]
    (a b : E →L[𝕜] E) : ‖ContinuousLinearMap.mulLeftRight 𝕜 (E →L[𝕜] E) a b‖ = ‖a‖ * ‖b‖ := by
  refine le_antisymm (opNorm_mulLeftRight_apply_apply_le 𝕜 _ a b) ?_
  obtain ⟨T, hT, hab⟩ := a.exists_norm_eq_one_and_norm_mul_mul_eq b
  calc ‖a‖ * ‖b‖ = ‖mulLeftRight 𝕜 (E →L[𝕜] E) a b T‖ := by rw [mulLeftRight_apply, hab]
    _ ≤ ‖mulLeftRight 𝕜 (E →L[𝕜] E) a b‖ * ‖T‖ := le_opNorm _ _
    _ = ‖mulLeftRight 𝕜 (E →L[𝕜] E) a b‖ := by rw [hT, mul_one]

/-- **The Fréchet derivative of inversion has norm $\|A^{-1}\|^2$.** Let $E$ be a nontrivial
finite-dimensional normed space over $\mathbb{R}$ or $\mathbb{C}$, and let $A$ be an isomorphism
of $E$. Then the map $H \mapsto A^{-1} H A^{-1}$ on the algebra of bounded operators has norm
$\|A^{-1}\|^2$.

The derivative of inversion at $A$ is $H \mapsto -A^{-1} H A^{-1}$ (Mathlib's
`hasFDerivAt_ringInverse`), so its norm is $\|A^{-1}\|^2$. The theorem is
`ContinuousLinearMap.norm_mulLeftRight_apply_apply` for $a = b = A^{-1}$. -/
theorem ContinuousLinearEquiv.norm_mulLeftRight_symm_symm [FiniteDimensional 𝕜 E] [Nontrivial E]
    (A : E ≃L[𝕜] E) :
    ‖ContinuousLinearMap.mulLeftRight 𝕜 (E →L[𝕜] E) (A.symm : E →L[𝕜] E) (A.symm : E →L[𝕜] E)‖
      = ‖(A.symm : E →L[𝕜] E)‖ ^ 2 := by
  rw [ContinuousLinearMap.norm_mulLeftRight_apply_apply, sq]

/-- **The condition number is the relative condition number of inversion.** Let $E$ be a nontrivial
finite-dimensional normed space over $\mathbb{R}$ or $\mathbb{C}$, and let $A$ be an isomorphism
of $E$. Then the first-order relative condition number of the inversion $T \mapsto T^{-1}$ at
$A$, on the admissible data of all bounded operators, is $$K(A) = \kappa(A) = \|A\|
\|A^{-1}\|.$$ This is (2.6.7) of [golub2013matrix] in the language of
`Numlib.Conditioning.Problem`.

The relative condition number is `Conditioning.relCondNumber`, and the inversion is
`Ring.inverse`. By the first-order formula `Conditioning.relCondNumber_eq_enorm_fderiv`, $K(A) =
\|H \mapsto A^{-1} H A^{-1}\| \, \|A\| / \|A^{-1}\| = \|A^{-1}\|^2 \|A\| / \|A^{-1}\|$. -/
theorem ContinuousLinearEquiv.relCondNumber_ringInverse [FiniteDimensional 𝕜 E] [Nontrivial E]
    (A : E ≃L[𝕜] E) :
    Conditioning.relCondNumber (fun T : E →L[𝕜] E => Ring.inverse T) Set.univ (A : E →L[𝕜] E)
      = ENNReal.ofReal A.condNumber := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have hne : ∀ B : E ≃L[𝕜] E, (B : E →L[𝕜] E) ≠ 0 := fun B hB => by
    obtain ⟨y, hy⟩ := exists_ne (0 : E)
    exact hy (B.injective (by simpa using congrArg (fun T : E →L[𝕜] E => T y) hB))
  have hsymm : 0 < ‖(A.symm : E →L[𝕜] E)‖ := norm_pos_iff.2 (hne A.symm)
  have hd : HasFDerivAt (fun T : E →L[𝕜] E => Ring.inverse T)
      (-ContinuousLinearMap.mulLeftRight 𝕜 (E →L[𝕜] E) (A.symm : E →L[𝕜] E)
        (A.symm : E →L[𝕜] E)) (A : E →L[𝕜] E) :=
    hasFDerivAt_ringInverse A.toUnit
  have hG : Ring.inverse (A : E →L[𝕜] E) = (A.symm : E →L[𝕜] E) := A.ring_inverse_coe
  rw [Conditioning.relCondNumber_eq_enorm_fderiv hd Filter.univ_mem (hne A)
      (by rw [hG]; exact hne A.symm), hG, enorm_neg, ← ofReal_norm, ← ofReal_norm,
    ← ofReal_norm, A.norm_mulLeftRight_symm_symm, ← ENNReal.ofReal_div_of_pos hsymm,
    ← ENNReal.ofReal_mul (by positivity), ContinuousLinearEquiv.condNumber]
  congr 1
  field_simp

/-- Let $0 < \varepsilon$ with $\varepsilon \kappa(A) < 1$. Then the largest change
$\|(A + \Delta A)^{-1} - A^{-1}\|$ over the perturbations with
$\|\Delta A\| \le \varepsilon \|A\|$, divided by $\varepsilon \|A^{-1}\|$, lies between
$\kappa(A) / (1 + \varepsilon \kappa(A))$ and $\kappa(A) / (1 - \varepsilon \kappa(A))$; these
are the two bounds behind `ContinuousLinearEquiv.tendsto_iSup_norm_inverse_add_sub_div`. -/
private theorem ContinuousLinearEquiv.iSup_norm_inverse_add_sub_div_mem [FiniteDimensional 𝕜 E]
    [Nontrivial E] (A : E ≃L[𝕜] E) {ε : ℝ} (hε : 0 < ε) (hεκ : ε * A.condNumber < 1) :
    A.condNumber / (1 + ε * A.condNumber)
        ≤ (⨆ ΔA : {ΔA : E →L[𝕜] E // ‖ΔA‖ ≤ ε * ‖(A : E →L[𝕜] E)‖},
            ‖Ring.inverse ((A : E →L[𝕜] E) + ΔA) - (A.symm : E →L[𝕜] E)‖)
          / (ε * ‖(A.symm : E →L[𝕜] E)‖) ∧
      (⨆ ΔA : {ΔA : E →L[𝕜] E // ‖ΔA‖ ≤ ε * ‖(A : E →L[𝕜] E)‖},
            ‖Ring.inverse ((A : E →L[𝕜] E) + ΔA) - (A.symm : E →L[𝕜] E)‖)
          / (ε * ‖(A.symm : E →L[𝕜] E)‖) ≤ A.condNumber / (1 - ε * A.condNumber) := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  set A' : E →L[𝕜] E := (A : E →L[𝕜] E) with hA'
  set Ai : E →L[𝕜] E := (A.symm : E →L[𝕜] E) with hAi
  set a := ‖A'‖ with ha_def
  set s := ‖Ai‖ with hs_def
  have hne : ∀ B : E ≃L[𝕜] E, (B : E →L[𝕜] E) ≠ 0 := fun B hB => by
    obtain ⟨y, hy⟩ := exists_ne (0 : E)
    exact hy (B.injective (by simpa using congrArg (fun T : E →L[𝕜] E => T y) hB))
  have ha : 0 < a := norm_pos_iff.2 (hne A)
  have hs : 0 < s := norm_pos_iff.2 (hne A.symm)
  have hκ : A.condNumber = a * s := rfl
  rw [hκ] at hεκ ⊢
  have hεs : 0 < ε * s := mul_pos hε hs
  have hsmall : ∀ Δ : E →L[𝕜] E, ‖Δ‖ ≤ ε * a → ‖Δ‖ < ‖Ai‖⁻¹ := fun Δ hΔ => by
    rw [← hs_def, ← one_div, lt_div_iff₀ hs]
    nlinarith
  -- the upper bound, perturbation by perturbation
  have hup : ∀ Δ : {Δ : E →L[𝕜] E // ‖Δ‖ ≤ ε * a},
      ‖Ring.inverse (A' + Δ) - Ai‖ ≤ s ^ 2 * (ε * a) / (1 - ε * (a * s)) := by
    rintro ⟨Δ, hΔ⟩
    have h : ‖Ring.inverse (A' + Δ) - Ai‖ ≤ s ^ 2 * ‖Δ‖ / (1 - s * ‖Δ‖) :=
      Units.norm_inverse_add_sub_le A.toUnit Δ (hsmall Δ hΔ)
    refine h.trans (div_le_div₀ (by positivity) (by gcongr) (by linarith) ?_)
    change 1 - ε * (a * s) ≤ 1 - s * ‖Δ‖
    nlinarith
  have : Nonempty {Δ : E →L[𝕜] E // ‖Δ‖ ≤ ε * a} := ⟨⟨0, by rw [norm_zero]; positivity⟩⟩
  have hbdd : BddAbove (Set.range fun Δ : {Δ : E →L[𝕜] E // ‖Δ‖ ≤ ε * a} =>
      ‖Ring.inverse (A' + Δ) - Ai‖) := ⟨_, Set.forall_mem_range.2 hup⟩
  -- the lower bound, at one perturbation
  obtain ⟨T, hT1, hTT⟩ := Ai.exists_norm_eq_one_and_norm_mul_mul_eq Ai
  set Δ₀ : E →L[𝕜] E := ((-(ε * a) : ℝ) : 𝕜) • T with hΔ₀_def
  have hΔ₀ : ‖Δ₀‖ = ε * a := by
    rw [hΔ₀_def, norm_smul, RCLike.norm_ofReal, abs_neg, abs_of_pos (by positivity), hT1,
      mul_one]
  have hunit : IsUnit (A' + Δ₀) := Units.isUnit_add_of_norm_lt A.toUnit Δ₀ (hsmall _ hΔ₀.le)
  set B := Ring.inverse (A' + Δ₀) with hB
  have hB1 : (A' + Δ₀) * B = 1 := Ring.mul_inverse_cancel _ hunit
  have hB2 : B * (A' + Δ₀) = 1 := Ring.inverse_mul_cancel _ hunit
  have hAiA : Ai * A' = 1 := by ext x; simp [hA', hAi]
  have hAAi : A' * Ai = 1 := by ext x; simp [hA', hAi]
  have hdiff : B - Ai = -(B * Δ₀ * Ai) := by
    calc B - Ai = B * (A' * Ai) - B * (A' + Δ₀) * Ai := by rw [hAAi, hB2, mul_one, one_mul]
      _ = -(B * Δ₀ * Ai) := by noncomm_ring
  have hkey : Ai * Δ₀ * Ai = (1 + Ai * Δ₀) * (B * Δ₀ * Ai) := by
    calc Ai * Δ₀ * Ai = Ai * ((A' + Δ₀) * B) * Δ₀ * Ai := by rw [hB1, mul_one]
      _ = (Ai * A' + Ai * Δ₀) * (B * Δ₀ * Ai) := by noncomm_ring
      _ = (1 + Ai * Δ₀) * (B * Δ₀ * Ai) := by rw [hAiA]
  have hn1 : ‖Ai * Δ₀ * Ai‖ = ε * a * s ^ 2 := by
    rw [hΔ₀_def, mul_smul_comm, smul_mul_assoc, norm_smul, RCLike.norm_ofReal, abs_neg,
      abs_of_pos (by positivity), hTT]
    ring
  have hn2 : ‖1 + Ai * Δ₀‖ ≤ 1 + ε * (a * s) := by
    refine (norm_add_le _ _).trans (add_le_add norm_one.le ?_)
    calc ‖Ai * Δ₀‖ ≤ s * ‖Δ₀‖ := _root_.norm_mul_le _ _
      _ = ε * (a * s) := by rw [hΔ₀]; ring
  have hD : ε * a * s ^ 2 ≤ (1 + ε * (a * s)) * ‖B - Ai‖ := by
    rw [← hn1, hkey, hdiff, norm_neg]
    exact (_root_.norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hn2 (norm_nonneg _))
  have hlow : ‖B - Ai‖ ≤ ⨆ Δ : {Δ : E →L[𝕜] E // ‖Δ‖ ≤ ε * a}, ‖Ring.inverse (A' + Δ) - Ai‖ :=
    le_ciSup hbdd ⟨Δ₀, hΔ₀.le⟩
  constructor
  · rw [div_le_div_iff₀ (by positivity) hεs]
    calc a * s * (ε * s) = ε * a * s ^ 2 := by ring
      _ ≤ (1 + ε * (a * s)) * ‖B - Ai‖ := hD
      _ ≤ (1 + ε * (a * s)) * ⨆ Δ : {Δ : E →L[𝕜] E // ‖Δ‖ ≤ ε * a},
            ‖Ring.inverse (A' + Δ) - Ai‖ := by gcongr
      _ = _ := by ring
  · rw [div_le_div_iff₀ hεs (by linarith)]
    calc (⨆ Δ : {Δ : E →L[𝕜] E // ‖Δ‖ ≤ ε * a}, ‖Ring.inverse (A' + Δ) - Ai‖)
          * (1 - ε * (a * s))
        ≤ s ^ 2 * (ε * a) / (1 - ε * (a * s)) * (1 - ε * (a * s)) :=
          mul_le_mul_of_nonneg_right (ciSup_le hup) (by linarith)
      _ = a * s * (ε * s) := by
          rw [div_mul_cancel₀ _ (by linarith : (0 : ℝ) < 1 - ε * (a * s)).ne']
          ring

/-- **The limit formula for the condition number**, (2.6.7) of [golub2013matrix]. Let $E$ be a
nontrivial finite-dimensional normed space over $\mathbb{R}$ or $\mathbb{C}$, and let $A$ be an
isomorphism of $E$. Then $$\kappa(A) = \lim_{\varepsilon \to 0^+} \frac{1}{\varepsilon
\|A^{-1}\|} \sup_{\|\Delta A\| \le \varepsilon \|A\|} \|(A + \Delta A)^{-1} - A^{-1}\|.$$

The condition number is `ContinuousLinearEquiv.condNumber`, and the inverse of $A + \Delta A$ is
`Ring.inverse`. For small $\varepsilon$ the quotient lies between
$\kappa(A) / (1 + \varepsilon \kappa(A))$ and $\kappa(A) / (1 - \varepsilon \kappa(A))$. -/
theorem ContinuousLinearEquiv.tendsto_iSup_norm_inverse_add_sub_div [FiniteDimensional 𝕜 E]
    [Nontrivial E] (A : E ≃L[𝕜] E) :
    Tendsto (fun ε : ℝ => (⨆ ΔA : {ΔA : E →L[𝕜] E // ‖ΔA‖ ≤ ε * ‖(A : E →L[𝕜] E)‖},
        ‖Ring.inverse ((A : E →L[𝕜] E) + ΔA) - (A.symm : E →L[𝕜] E)‖)
          / (ε * ‖(A.symm : E →L[𝕜] E)‖)) (𝓝[>] 0) (𝓝 A.condNumber) := by
  have hlim : ∀ c : ℝ, Tendsto (fun ε : ℝ => A.condNumber / (1 + c * (ε * A.condNumber)))
      (𝓝[>] 0) (𝓝 A.condNumber) := fun c => by
    have h : Tendsto (fun ε : ℝ => A.condNumber / (1 + c * (ε * A.condNumber))) (𝓝 0)
        (𝓝 (A.condNumber / (1 + c * (0 * A.condNumber)))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.add (tendsto_const_nhds.mul
        (tendsto_id.mul tendsto_const_nhds))) (by simp)
    simpa using h.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε * A.condNumber < 1 := by
    have h2 : Tendsto (fun ε : ℝ => ε * A.condNumber) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_id.mul_const A.condNumber).mono_left
        (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
    exact (eventually_mem_nhdsWithin.mono fun ε hε => hε).and
      (h2.eventually (gt_mem_nhds one_pos))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hlim 1) (by
    simpa [sub_eq_add_neg] using hlim (-1)) (hev.mono fun ε h => ?_) (hev.mono fun ε h => ?_)
  · exact (A.iSup_norm_inverse_add_sub_div_mem h.1 h.2).1
  · exact (A.iSup_norm_inverse_add_sub_div_mem h.1 h.2).2

/-- **Kahan's distance-to-singularity formula**, (3.6) of Remark 3.1 of [quarteroni2000numerical],
after the references Kah66 and Gas83 of the source. Let $E$ be a nontrivial finite-dimensional
normed space over $\mathbb{R}$ or $\mathbb{C}$, and let $A$ be an isomorphism of $E$. Then the
least relative distance from $A$ to a singular operator is $$\min \left\{ \frac{\|t\|}{\|A\|} :
A + t \text{ is not invertible} \right\} = \frac{1}{\kappa(A)},$$ in any operator norm.

The condition number is `ContinuousLinearEquiv.condNumber`. The two halves are
`NormedRing.norm_le_of_not_isUnit_add` and
`ContinuousLinearEquiv.exists_not_isUnit_add_norm_le`. -/
theorem ContinuousLinearEquiv.isLeast_dist_singular [FiniteDimensional 𝕜 E] [Nontrivial E]
    (A : E ≃L[𝕜] E) :
    IsLeast {r : ℝ | ∃ t : E →L[𝕜] E, ¬ IsUnit ((A : E →L[𝕜] E) + t) ∧
      ‖t‖ / ‖(A : E →L[𝕜] E)‖ = r} (1 / A.condNumber) := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have hA : 0 < ‖(A : E →L[𝕜] E)‖ := by
    obtain ⟨y, hy1, -⟩ := (A : E →L[𝕜] E).exists_norm_eq_one_and_norm_apply_eq
    have h1 := (A : E →L[𝕜] E).le_opNorm y
    have hAy : (A : E →L[𝕜] E) y ≠ 0 := fun h => by
      have hy0 : y = 0 := by simpa using congrArg A.symm h
      rw [hy0, norm_zero] at hy1
      exact zero_ne_one hy1
    rw [hy1, mul_one] at h1
    exact (norm_pos_iff.2 hAy).trans_le h1
  have hinv := A.ring_inverse_coe
  constructor
  · obtain ⟨t, ht, htn⟩ := A.exists_not_isUnit_add_norm_le
    refine ⟨t, ht, ?_⟩
    rw [htn, ContinuousLinearEquiv.condNumber, one_div, mul_inv, div_eq_mul_inv, mul_comm]
  · rintro r ⟨t, ht, rfl⟩
    have h := NormedRing.norm_le_of_not_isUnit_add (a := (A : E →L[𝕜] E)) ⟨A.toUnit, rfl⟩ ht
    rw [hinv] at h
    rw [ContinuousLinearEquiv.condNumber, one_div, mul_inv, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right h hA.le

end Distance

/-! ### The relative bounds of Theorem 3.3 -/

section Theorem33

open NormedRing

/-- **Theorem 3.3** of [quarteroni2000numerical], the bound (3.13). Let $A$ be an isomorphism of the
normed space $E$ and $\Delta A$ a bounded operator on $E$, and let $\gamma$ be real with
$\|\Delta A\| \le \gamma \|A\|$, $\|\Delta b\| \le \gamma \|b\|$ and $\gamma \kappa(A) < 1$. If
$Ax = b$ with $b \neq 0$ and $(A + \Delta A) y = b + \Delta b$, then $$\frac{\|y - x\|}{\|x\|}
\le \frac{2 \gamma}{1 - \gamma \kappa(A)} \, \kappa(A).$$

The condition number is `NormedRing.condNumber`. The bound follows from
`relative_error_le_condNumber`, since $\|A^{-1}\| \|\Delta A\| \le \gamma \kappa(A)$. -/
theorem relative_error_le_of_norm_le_mul (A : E ≃L[𝕜] E) (ΔA : E →L[𝕜] E) {b Δb x y : E}
    (hx : A x = b) (hy : ((A : E →L[𝕜] E) + ΔA) y = b + Δb) {γ : ℝ}
    (hΔA : ‖ΔA‖ ≤ γ * ‖(A : E →L[𝕜] E)‖) (hΔb : ‖Δb‖ ≤ γ * ‖b‖)
    (hsmall : γ * condNumber (A : E →L[𝕜] E) < 1) (hb : b ≠ 0) :
    ‖y - x‖ / ‖x‖ ≤ 2 * γ / (1 - γ * condNumber (A : E →L[𝕜] E)) * condNumber (A : E →L[𝕜] E) := by
  have hκ := A.condNumber_eq
  set N := ‖(A : E →L[𝕜] E)‖ with hN
  set M := ‖(A.symm : E →L[𝕜] E)‖ with hM
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb (by rw [← hx]; simp)
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hAb : ‖b‖ ≤ N * ‖x‖ := by
    rw [← hx]
    simpa using (A : E →L[𝕜] E).le_opNorm x
  have hN0 : 0 < N := by nlinarith [norm_nonneg (A : E →L[𝕜] E), norm_nonneg x]
  have hM0 : 0 ≤ M := norm_nonneg _
  have hMΔ : M * ‖ΔA‖ ≤ γ * (N * M) := by nlinarith
  rw [hκ] at hsmall ⊢
  have hsmall' : M * ‖ΔA‖ < 1 := hMΔ.trans_lt hsmall
  refine (relative_error_le_condNumber A ΔA hx hy hsmall' hx0 hb).trans ?_
  rw [hκ]
  have e1 : ‖ΔA‖ / N ≤ γ := (div_le_iff₀ hN0).2 hΔA
  have e2 : ‖Δb‖ / ‖b‖ ≤ γ := (div_le_iff₀ hbn).2 hΔb
  have h1 : ‖ΔA‖ / N + ‖Δb‖ / ‖b‖ ≤ 2 * γ := by linarith
  have hpos' : 0 < 1 - γ * (N * M) := by linarith
  calc N * M / (1 - M * ‖ΔA‖) * (‖ΔA‖ / N + ‖Δb‖ / ‖b‖)
      ≤ N * M / (1 - γ * (N * M)) * (2 * γ) :=
        mul_le_mul (div_le_div_of_nonneg_left (mul_nonneg hN0.le hM0) hpos' (by linarith)) h1
          (add_nonneg (div_nonneg (norm_nonneg _) hN0.le) (div_nonneg (norm_nonneg _) hbn.le))
          (div_nonneg (mul_nonneg hN0.le hM0) hpos'.le)
    _ = 2 * γ / (1 - γ * (N * M)) * (N * M) := by ring

/-- **Theorem 3.3** of [quarteroni2000numerical], the bound (3.12). Under the hypotheses of
`relative_error_le_of_norm_le_mul`, $$\frac{\|y\|}{\|x\|} \le \frac{1 + \gamma \kappa(A)}{1 -
\gamma \kappa(A)}.$$ This follows from (3.13) by the triangle inequality. -/
theorem norm_add_div_le_of_norm_le_mul (A : E ≃L[𝕜] E) (ΔA : E →L[𝕜] E) {b Δb x y : E}
    (hx : A x = b) (hy : ((A : E →L[𝕜] E) + ΔA) y = b + Δb) {γ : ℝ}
    (hΔA : ‖ΔA‖ ≤ γ * ‖(A : E →L[𝕜] E)‖) (hΔb : ‖Δb‖ ≤ γ * ‖b‖)
    (hsmall : γ * condNumber (A : E →L[𝕜] E) < 1) (hb : b ≠ 0) :
    ‖y‖ / ‖x‖ ≤ (1 + γ * condNumber (A : E →L[𝕜] E)) / (1 - γ * condNumber (A : E →L[𝕜] E)) := by
  have h := relative_error_le_of_norm_le_mul A ΔA hx hy hΔA hΔb hsmall hb
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb (by rw [← hx]; simp)
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  set k := condNumber (A : E →L[𝕜] E) with hk
  have hpos : 0 < 1 - γ * k := by linarith
  have hy' : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by simpa using norm_add_le (y - x) x
  rw [div_le_iff₀ hxn] at h ⊢
  calc ‖y‖ ≤ ‖y - x‖ + ‖x‖ := hy'
    _ ≤ 2 * γ / (1 - γ * k) * k * ‖x‖ + ‖x‖ := by linarith
    _ = (1 + γ * k) / (1 - γ * k) * ‖x‖ := by
        field_simp
        ring

end Theorem33

/-! ### Approximate inverses: Property 3.1 -/

section ApproxInverse

variable {R : Type*} [NormedRing R] [NormOneClass R] [CompleteSpace R]

/-- **Property 3.1** of [quarteroni2000numerical], the first bound. Let $R$ be a complete normed
ring with $\|1\| = 1$, let $a \in R$ be a unit, and let $c \in R$ with $\|ac - 1\| < 1$. Then
$$\|a^{-1}\| \le \frac{\|c\|}{1 - \|ac - 1\|}.$$

The source states this for matrices $A$ and $C$. The proof uses that $ac = 1 + (ac - 1)$ is a
unit and $a^{-1} = c (ac)^{-1}$. -/
theorem NormedRing.norm_inverse_le_of_norm_mul_sub_one_lt {a c : R} (ha : IsUnit a)
    (hr : ‖a * c - 1‖ < 1) : ‖Ring.inverse a‖ ≤ ‖c‖ / (1 - ‖a * c - 1‖) := by
  have hr' : ‖-(a * c - 1)‖ < 1 := by rwa [norm_neg]
  have hunit : IsUnit (1 - -(a * c - 1)) := isUnit_one_sub_of_norm_lt_one hr'
  have hac : 1 - -(a * c - 1) = a * c := by abel
  have hinv : Ring.inverse a = c * Ring.inverse (1 - -(a * c - 1)) := by
    calc Ring.inverse a
        = Ring.inverse a * ((1 - -(a * c - 1)) * Ring.inverse (1 - -(a * c - 1))) := by
          rw [Ring.mul_inverse_cancel _ hunit, mul_one]
      _ = c * Ring.inverse (1 - -(a * c - 1)) := by
          rw [hac, ← mul_assoc, ← mul_assoc, Ring.inverse_mul_cancel _ ha, one_mul]
  rw [hinv]
  calc ‖c * Ring.inverse (1 - -(a * c - 1))‖ ≤ ‖c‖ * ‖Ring.inverse (1 - -(a * c - 1))‖ :=
        _root_.norm_mul_le _ _
    _ ≤ ‖c‖ * (1 / (1 - ‖-(a * c - 1)‖)) :=
        mul_le_mul_of_nonneg_left (NormedRing.norm_inverse_one_sub_le hr') (norm_nonneg _)
    _ = ‖c‖ / (1 - ‖a * c - 1‖) := by rw [norm_neg]; ring

omit [NormOneClass R] in
/-- **Property 3.1** of [quarteroni2000numerical], the upper bound of the second display. Let $R$ be
a complete normed ring, let $a \in R$ be a unit, and let $c \in R$ with $\|ac - 1\| < 1$. Then
$$\|c - a^{-1}\| \le \frac{\|c\| \|ac - 1\|}{1 - \|ac - 1\|}.$$

The proof uses $c - a^{-1} = -c ((ac)^{-1} - 1)$. -/
theorem NormedRing.norm_sub_inverse_le_of_norm_mul_sub_one_lt {a c : R} (ha : IsUnit a)
    (hr : ‖a * c - 1‖ < 1) :
    ‖c - Ring.inverse a‖ ≤ ‖c‖ * ‖a * c - 1‖ / (1 - ‖a * c - 1‖) := by
  have hr' : ‖-(a * c - 1)‖ < 1 := by rwa [norm_neg]
  have hunit : IsUnit (1 - -(a * c - 1)) := isUnit_one_sub_of_norm_lt_one hr'
  have hac : 1 - -(a * c - 1) = a * c := by abel
  have hinv : Ring.inverse a = c * Ring.inverse (1 - -(a * c - 1)) := by
    calc Ring.inverse a
        = Ring.inverse a * ((1 - -(a * c - 1)) * Ring.inverse (1 - -(a * c - 1))) := by
          rw [Ring.mul_inverse_cancel _ hunit, mul_one]
      _ = c * Ring.inverse (1 - -(a * c - 1)) := by
          rw [hac, ← mul_assoc, ← mul_assoc, Ring.inverse_mul_cancel _ ha, one_mul]
  have hdiff : c - Ring.inverse a = -(c * (Ring.inverse (1 - -(a * c - 1)) - 1)) := by
    rw [hinv, mul_sub, mul_one]
    abel
  rw [hdiff, norm_neg]
  calc ‖c * (Ring.inverse (1 - -(a * c - 1)) - 1)‖
      ≤ ‖c‖ * ‖Ring.inverse (1 - -(a * c - 1)) - 1‖ := _root_.norm_mul_le _ _
    _ ≤ ‖c‖ * (‖-(a * c - 1)‖ / (1 - ‖-(a * c - 1)‖)) :=
        mul_le_mul_of_nonneg_left (NormedRing.norm_inverse_one_sub_sub_one_le hr') (norm_nonneg _)
    _ = ‖c‖ * ‖a * c - 1‖ / (1 - ‖a * c - 1‖) := by rw [norm_neg]; ring

omit [NormOneClass R] [CompleteSpace R] in
/-- **Property 3.1** of [quarteroni2000numerical], the lower bound. Let $R$ be a normed ring and
$a \in R$ a unit. Then for every $c \in R$, $$\frac{\|ac - 1\|}{\|a\|} \le \|c - a^{-1}\|,$$
since $ac - 1 = a (c - a^{-1})$. -/
theorem NormedRing.norm_mul_sub_one_div_norm_le_norm_sub_inverse {a c : R} (ha : IsUnit a) :
    ‖a * c - 1‖ / ‖a‖ ≤ ‖c - Ring.inverse a‖ := by
  have h : a * c - 1 = a * (c - Ring.inverse a) := by
    rw [mul_sub, Ring.mul_inverse_cancel _ ha]
  rcases eq_or_lt_of_le (norm_nonneg a) with h0 | h0
  · rw [← h0, div_zero]
    exact norm_nonneg _
  · rw [div_le_iff₀ h0, h, mul_comm]
    exact _root_.norm_mul_le _ _

omit [NormOneClass R] in
/-- **Property 3.1** of [quarteroni2000numerical], "then $A$ and $C$ are nonsingular". Let $R$ be a
complete normed ring that is Dedekind-finite (`IsDedekindFiniteMonoid R`: $ab = 1$ implies
$ba = 1$). If $\|ac - 1\| < 1$, then $a$ and $c$ are units.

The operator rings of finite-dimensional spaces are Dedekind-finite
(`ContinuousLinearMap.isDedekindFiniteMonoid`), and so are the matrices over a field. The proof
shows that $ac$ is a unit; then $a$ and $c$ have one-sided inverses, which are two-sided. -/
theorem isUnit_of_norm_mul_sub_one_lt [IsDedekindFiniteMonoid R] {a c : R}
    (hr : ‖a * c - 1‖ < 1) : IsUnit a ∧ IsUnit c := by
  have hr' : ‖-(a * c - 1)‖ < 1 := by rwa [norm_neg]
  have hunit : IsUnit (1 - -(a * c - 1)) := isUnit_one_sub_of_norm_lt_one hr'
  have hac : 1 - -(a * c - 1) = a * c := by abel
  rw [hac] at hunit
  obtain ⟨u, hu⟩ := hunit
  have h1 : a * (c * ↑u⁻¹) = 1 := by rw [← mul_assoc, ← hu, Units.mul_inv]
  have h2 : (↑u⁻¹ * a) * c = 1 := by rw [mul_assoc, ← hu, Units.inv_mul]
  exact ⟨⟨⟨a, c * ↑u⁻¹, h1, mul_eq_one_symm h1⟩, rfl⟩, ⟨⟨c, ↑u⁻¹ * a, mul_eq_one_symm h2, h2⟩, rfl⟩⟩

omit [NormOneClass R] in
/-- The bound (3.19) of [quarteroni2000numerical], the backward reading of Property 3.1 with the
roles of $A$ and $C$ exchanged. Let $R$ be a complete normed ring, let $c \in R$ be a unit, and
let $a \in R$ with $\|ca - 1\| < 1$. Then the perturbation $\delta A = c^{-1} - a$, for which
$c$ is an exact inverse of $a + \delta A$, satisfies $$\|c^{-1} - a\| \le \frac{\|ca - 1\| \,
\|a\|}{1 - \|ca - 1\|}.$$

The source writes the residual as $AC - I$. In a noncommutative ring $\|ca - 1\|$ and
$\|ac - 1\|$ differ; the proof uses $\|ca - 1\|$, and that is the hypothesis here. -/
theorem NormedRing.norm_sub_le_of_norm_mul_sub_one_lt {a c : R} (hc : IsUnit c)
    (hr : ‖c * a - 1‖ < 1) :
    ‖Ring.inverse c - a‖ ≤ ‖c * a - 1‖ * ‖a‖ / (1 - ‖c * a - 1‖) := by
  rw [norm_sub_rev, mul_comm]
  exact NormedRing.norm_sub_inverse_le_of_norm_mul_sub_one_lt hc hr

end ApproxInverse

section DedekindFinite

/-- The ring of bounded operators on a finite-dimensional normed space is Dedekind-finite: $ab = 1$
implies $ba = 1$. The operators form a finite-dimensional algebra over the field, hence an
Artinian ring, and Artinian rings are Dedekind-finite. This is the hypothesis that
`isUnit_of_norm_mul_sub_one_lt` asks of the operator ring. -/
instance ContinuousLinearMap.isDedekindFiniteMonoid [FiniteDimensional 𝕜 E] :
    IsDedekindFiniteMonoid (E →L[𝕜] E) :=
  have : IsArtinianRing (E →L[𝕜] E) := IsArtinianRing.of_finite 𝕜 (E →L[𝕜] E)
  inferInstance

end DedekindFinite

/-! ### A posteriori: the residual and an approximate inverse -/

section APosteriori

open NormedRing

/-- **The a posteriori bound** (3.20) of [quarteroni2000numerical]. Let $E$ be a Banach space, $A$
an isomorphism of $E$, and $C$ a bounded operator on $E$ with $\|AC - I\| < 1$. If $Ax = b$,
then every $y \in E$ satisfies $$\|y - x\| \le \frac{\|b - Ay\| \, \|C\|}{1 - \|AC - I\|}.$$

The proof uses $y - x = -A^{-1} (b - Ay)$ and the bound
$\|A^{-1}\| \le \|C\| / (1 - \|AC - I\|)$ of `NormedRing.norm_inverse_le_of_norm_mul_sub_one_lt`
in the ring of operators. -/
theorem norm_error_le_of_norm_mul_sub_one_lt [CompleteSpace E] (A : E ≃L[𝕜] E) (C : E →L[𝕜] E)
    (hr : ‖(A : E →L[𝕜] E) * C - 1‖ < 1) {b x : E} (hx : A x = b) (y : E) :
    ‖y - x‖ ≤ ‖b - A y‖ * ‖C‖ / (1 - ‖(A : E →L[𝕜] E) * C - 1‖) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [Subsingleton.elim (y - x) 0, norm_zero]
    positivity
  have hyx : y - x = -((A.symm : E →L[𝕜] E) (b - A y)) := by
    rw [← hx]
    simp
  rw [hyx, norm_neg, div_eq_mul_inv, mul_assoc, mul_comm ‖C‖, ← div_eq_inv_mul, ← mul_div_assoc,
    mul_comm]
  calc ‖(A.symm : E →L[𝕜] E) (b - A y)‖
      ≤ ‖(A.symm : E →L[𝕜] E)‖ * ‖b - A y‖ := (A.symm : E →L[𝕜] E).le_opNorm _
    _ ≤ ‖C‖ / (1 - ‖(A : E →L[𝕜] E) * C - 1‖) * ‖b - A y‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have h := NormedRing.norm_inverse_le_of_norm_mul_sub_one_lt (a := (A : E →L[𝕜] E))
          ⟨A.toUnit, rfl⟩ hr
        rwa [A.ring_inverse_coe] at h
    _ = ‖C‖ * ‖b - A y‖ / (1 - ‖(A : E →L[𝕜] E) * C - 1‖) := by ring

end APosteriori
