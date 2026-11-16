/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Complexity.Basic
import Numlib.Optimization.Complexity.Existence
import NumlibSurface.CartisGouldToint.Chapter08.Section02

/-!
# Cartis, Gould and Toint, Section 8.3: Subproblem solution

This module formalizes Section 8.3 of [cartis2022evaluation]. Let $H \in \mathbb{R}^{n \times n}$ be
symmetric, $M \in \mathbb{R}^{n \times n}$ symmetric positive definite and $g \in \mathbb{R}^n$. Let
$\lambda_1$ be the leftmost eigenvalue of the pencil $(H, M)$, let
$\lambda_s = \max(0, -\lambda_1)$, and let $s(\lambda) = -(H + \lambda M)^{-1} g$ for
$\lambda > \lambda_s$. The section divides the real line into three sets:
$\mathcal{N} = (-\infty, \lambda_s]$, the set $\mathcal{L}$ of $\lambda > \lambda_s$ where
$\|s(\lambda)\|_M$ is at least the target (the radius $\Delta$ of the trust-region subproblem
(8.1.2), or $(\lambda/\sigma)^{1/(r-2)}$ for the regularization subproblem (8.1.3)), and the set
$\mathcal{G}$ of $\lambda > \lambda_s$ where it is smaller. If $\lambda^*$ is the multiplier of a
global minimizer, then $\mathcal{L} = (\lambda_s, \lambda^*]$ and
$\mathcal{G} = (\lambda^*, \infty)$.

From a point of $\mathcal{L}$, Algorithms 8.3.1 and 8.3.2 take at each iteration the largest of a
finite set of candidates, built from the Taylor and Newton corrections of Section 8.2. The iterates
stay in $\mathcal{L}$, increase, and converge to $\lambda^*$, Q-linearly and Q-superlinearly when a
Newton candidate is used. Corollaries 8.3.1 and 8.3.2 describe all global minimizers of the two
subproblems, the hard case $\lambda^* = -\lambda_1$ included, by the minimum-norm solution $s_s$ of
(8.3.2). The proofs are transported to the operator backbone `Numlib.Optimization.Subproblem`.

## Main definitions

* Section 8.3.1, `CartisGouldToint.Chapter08.setN`: the set $\mathcal{N} = (-\infty, \lambda_s]$.
* Section 8.3.1, `CartisGouldToint.Chapter08.setL_reg`, `CartisGouldToint.Chapter08.setG_reg`,
  `CartisGouldToint.Chapter08.setF_reg`: the sets $\mathcal{L}$, $\mathcal{G}$ and
  $\mathcal{F} = \mathcal{L} \cup \mathcal{G}$ for the regularization subproblem.
* Algorithm 8.3.1, `CartisGouldToint.Chapter08.algorithm_8_3_1`: a run of the secular iteration for
  the regularization subproblem, with candidates `CartisGouldToint.Chapter08.candidates831`.
* Equation (8.3.2), `CartisGouldToint.Chapter08.minNormSolution`: the minimum-$M$-norm solution
  $s_s = -(H + \lambda M)^{+} g$.
* Section 8.3.2, `CartisGouldToint.Chapter08.setL_tr`, `CartisGouldToint.Chapter08.setG_tr`: the
  sets $\mathcal{L}$ and $\mathcal{G}$ for the trust-region subproblem.
* Algorithm 8.3.2, `CartisGouldToint.Chapter08.algorithm_8_3_2`: a run of the secular iteration for
  the trust-region subproblem, with candidates `CartisGouldToint.Chapter08.candidates832`.
* `CartisGouldToint.Chapter08.taylorCorrectionFn`,
  `CartisGouldToint.Chapter08.regNewtonCorrectionFn`,
  `CartisGouldToint.Chapter08.trNewtonCorrectionFn`: the Taylor correction of (8.2.15) and the
  Newton corrections (8.2.25) and (8.2.24), which the two algorithms use.
* `CartisGouldToint.Chapter08.exitTest`: the exit test $|\lambda_k - \lambda_{k-1}| \le \varepsilon$
  of the two algorithms.

## Main results

* Section 8.3.1, `CartisGouldToint.Chapter08.setF_reg_eq_Ioi`: for the regularization subproblem,
  $\mathcal{N}$, $\mathcal{L}$ and $\mathcal{G}$ partition $\mathbb{R}$.
* Section 8.3.1, `CartisGouldToint.Chapter08.setL_reg_eq_Ioc`:
  $\mathcal{L} = (\lambda_s, \lambda^*]$ and $\mathcal{G} = (\lambda^*, \infty)$ for the
  regularization subproblem.
* Algorithm 8.3.1, `CartisGouldToint.Chapter08.algorithm_8_3_1_terminates`: from
  $\lambda_0 \in \mathcal{L}$ the iterates increase in $\mathcal{L}$ to $\lambda^*$, and a run
  exists.
* Section 8.3.1, `CartisGouldToint.Chapter08.tendsto_stepOf_minNormSolution`: if
  $g \perp \ker(H - \lambda_1 M)$, then $s(\lambda) \to s_s$ as $\lambda \downarrow -\lambda_1$.
* Equation (8.3.2), `CartisGouldToint.Chapter08.minNormSolution_spec`: $s_s$ is the solution of
  $(H + \lambda M) s = -g$ of least $M$-norm.
* Corollary 8.3.1, `CartisGouldToint.Chapter08.corollary_8_3_1`: the global minimizers of the
  regularization subproblem and the optimal value (8.3.3).
* Section 8.3.2, `CartisGouldToint.Chapter08.setL_tr_union_setG_tr`: for the trust-region
  subproblem, $\mathcal{L}$ and $\mathcal{G}$ partition $(\lambda_s, \infty)$.
* Section 8.3.2, `CartisGouldToint.Chapter08.setL_tr_eq_Ioc`: $\mathcal{L} = (\lambda_s, \lambda^*]$
  and $\mathcal{G} = (\lambda^*, \infty)$ for the trust-region subproblem.
* Algorithm 8.3.2, `CartisGouldToint.Chapter08.algorithm_8_3_2_terminates`: from
  $\lambda_0 \in \mathcal{L}$ the iterates increase in $\mathcal{L}$ to $\lambda^*$, and a run
  exists.
* Corollary 8.3.2, `CartisGouldToint.Chapter08.corollary_8_3_2`: the global minimizers of the
  trust-region subproblem and the optimal value (8.3.5).

## Implementation notes

* The sets $\mathcal{L}$ and $\mathcal{G}$ are defined inside $(\lambda_s, \infty)$ by the norm
  $\|s(\lambda)\|_M$ (`CartisGouldToint.Chapter08.mNorm` of `CartisGouldToint.Chapter08.stepOf`).
  The lemmas `CartisGouldToint.Chapter08.mem_setL_reg_iff` and its companions restate them by the
  secular function $\pi(\lambda) = \|s(\lambda)\|_M^2$.
* An algorithm is a run predicate: a sequence $(\lambda_k)$ and an exit index $K$ that obey the
  rules of the algorithm up to the first iteration that meets the exit test
  (`Optimization.IsFirstHit`).
* Each surface correction equals the corresponding correction of
  `Numlib.Optimization.Subproblem.SecularIteration` for the scaled operator $M^{-1} H$ and the
  scaled gradient $M^{-1} g$ on the $M$-inner product space `Subproblem.ScaledSpace`. The lemmas
  `CartisGouldToint.Chapter08.taylorCorrectionFn_eq` and its companions record this.

## Deviations from the source

* **Section 8.3, the sets $\mathcal{N}$, $\mathcal{L}$, $\mathcal{G}$** (correction). The
  set-builder descriptions of the source are wrong when $\lambda_1 > 0$; the interval forms, which
  partition $\mathbb{R}$, are used. See `CartisGouldToint.Chapter08.setN`,
  `CartisGouldToint.Chapter08.setF_reg_eq_Ioi` and
  `CartisGouldToint.Chapter08.setL_tr_union_setG_tr`.
* **Section 8.3.1, the transformed target** (typo). The target is $(\lambda/\sigma)^{2\beta/(r-2)}$,
  not $(\lambda/\sigma)^{\beta/(r-2)}$, and the ranges of $\beta$ are $(0, (r-2)/2]$ and
  $[-1/2, 0)$. See `CartisGouldToint.Chapter08.regSecularFn`.
* **Algorithm 8.3.1** (correction). The Newton correction (8.2.25) is undefined at $\beta = 0$; the
  exponents satisfy $\beta_j \neq 0$. See `CartisGouldToint.Chapter08.algorithm_8_3_1`.
* **Corollaries 8.3.1 and 8.3.2** (correction). When $\lambda_1$ is multiple, one fixed eigenvector
  $v_1$ does not parametrize all minimizers; the statements allow any nonzero generalized
  eigenvector for $\lambda_1$. See `CartisGouldToint.Chapter08.corollary_8_3_1` and
  `CartisGouldToint.Chapter08.corollary_8_3_2`.
* **Equation (8.3.2)** (reading). The minimum-norm solution is taken in the $M$-norm, which makes it
  the limit of $s(\lambda)$ as $\lambda \downarrow \lambda_s$. See
  `CartisGouldToint.Chapter08.minNormSolution`.
* **Corollary 8.3.2, boundary condition** (correction). For $\lambda^* = 0$ the minimizer need not
  lie on the boundary; $\|s_s + \alpha v\|_M = \Delta$ is stated for $\lambda^* > 0$ only. See
  `CartisGouldToint.Chapter08.corollary_8_3_2`.
-/

open Matrix Set Filter Topology
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter08

open Subproblem

variable {n : ℕ} {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}

/-! ### The sets $\mathcal{N}$, $\mathcal{L}$, $\mathcal{G}$ -/

/-- **Section 8.3.1** of [cartis2022evaluation], the set $\mathcal{N}$. Let $H$ be symmetric and $M$
symmetric positive definite, and let $\lambda_s = \max(0, -\lambda_1)$, where $\lambda_1$ is the
leftmost eigenvalue of the pencil $(H, M)$. The set $\mathcal{N}$ is the interval
$(-\infty, \lambda_s]$.

**Correction.** The source also describes $\mathcal{N}$ as $\{\lambda \mid H + \lambda M \text{
is not positive definite}\}$. That set is $(-\infty, -\lambda_1]$, which differs from
$(-\infty, \lambda_s]$ when $\lambda_1 > 0$. The interval form is used, so that $\mathcal{N}$,
$\mathcal{L}$ and $\mathcal{G}$ partition $\mathbb{R}$.

The number $\lambda_s$ is `CartisGouldToint.Chapter08.lambdaS`. -/
noncomputable def setN (hH : H.IsHermitian) (hM : M.PosDef) : Set ℝ := Iic (lambdaS hH hM)

/-- **Section 8.3.1** of [cartis2022evaluation], the set $\mathcal{L}$ for the regularization
subproblem (8.1.3). Let $\sigma, r \in \mathbb{R}$. The set $\mathcal{L}$ consists of the
$\lambda > \lambda_s$ with
$$\|s(\lambda)\|_M \ge (\lambda/\sigma)^{1/(r-2)}.$$

**Correction.** The source describes $\mathcal{L}$ by the conditions $H + \lambda M \succ 0$ and
$\|s(\lambda)\|_M \ge (\lambda/\sigma)^{1/(r-2)}$. When $\lambda_1 > 0$ this set contains points
$\lambda \in (-\lambda_1, 0]$ outside $(\lambda_s, \infty)$; the definition requires
$\lambda > \lambda_s$.

If $s^*$ is a global minimizer with multiplier $\lambda^* = \sigma \|s^*\|_M^{r-2}$, then
$\mathcal{L} = (\lambda_s, \lambda^*]$ (`CartisGouldToint.Chapter08.setL_reg_eq_Ioc`). The power
is the real power `Real.rpow`. -/
def setL_reg (hH : H.IsHermitian) (hM : M.PosDef) (g : EuclideanSpace ℝ (Fin n)) (σ r : ℝ) :
    Set ℝ :=
  {lam | lambdaS hH hM < lam ∧ (lam / σ) ^ (1 / (r - 2)) ≤ mNorm M (stepOf g H M lam)}

/-- **Section 8.3.1** of [cartis2022evaluation], the set $\mathcal{G}$ for the regularization
subproblem (8.1.3). Let $\sigma, r \in \mathbb{R}$. The set $\mathcal{G}$ consists of the
$\lambda > \lambda_s$ with
$$\|s(\lambda)\|_M < (\lambda/\sigma)^{1/(r-2)}.$$

**Correction.** The source describes $\mathcal{G}$ by the conditions $H + \lambda M \succ 0$ and
$\|s(\lambda)\|_M < (\lambda/\sigma)^{1/(r-2)}$. When $\lambda_1 > 0$ this set contains points
outside $(\lambda_s, \infty)$, for example $\lambda = -1/2$ for $H = M = I$; the definition
requires $\lambda > \lambda_s$.

If $s^*$ is a global minimizer with multiplier $\lambda^*$, then
$\mathcal{G} = (\lambda^*, \infty)$ (`CartisGouldToint.Chapter08.setL_reg_eq_Ioc`). -/
def setG_reg (hH : H.IsHermitian) (hM : M.PosDef) (g : EuclideanSpace ℝ (Fin n)) (σ r : ℝ) :
    Set ℝ :=
  {lam | lambdaS hH hM < lam ∧ mNorm M (stepOf g H M lam) < (lam / σ) ^ (1 / (r - 2))}

/-- **Section 8.3.1** of [cartis2022evaluation], the set $\mathcal{F}$. For the regularization
subproblem (8.1.3), $\mathcal{F} = \mathcal{L} \cup \mathcal{G}$. It is the interval
$(\lambda_s, \infty)$ (`CartisGouldToint.Chapter08.setF_reg_eq_Ioi`). -/
def setF_reg (hH : H.IsHermitian) (hM : M.PosDef) (g : EuclideanSpace ℝ (Fin n)) (σ r : ℝ) :
    Set ℝ :=
  setL_reg hH hM g σ r ∪ setG_reg hH hM g σ r

/-- **Section 8.3.2** of [cartis2022evaluation], the set $\mathcal{L}$ for the trust-region
subproblem (8.1.2). Let $\Delta \in \mathbb{R}$. The set $\mathcal{L}$ consists of the
$\lambda > \lambda_s$ with $\|s(\lambda)\|_M \ge \Delta$.

**Correction.** As for the regularization subproblem, the set-builder description of the source
with $H + \lambda M \succ 0$ contains points outside $(\lambda_s, \infty)$ when $\lambda_1 > 0$;
the definition requires $\lambda > \lambda_s$. -/
def setL_tr (hH : H.IsHermitian) (hM : M.PosDef) (g : EuclideanSpace ℝ (Fin n)) (Δ : ℝ) :
    Set ℝ :=
  {lam | lambdaS hH hM < lam ∧ Δ ≤ mNorm M (stepOf g H M lam)}

/-- **Section 8.3.2** of [cartis2022evaluation], the set $\mathcal{G}$ for the trust-region
subproblem (8.1.2). Let $\Delta \in \mathbb{R}$. The set $\mathcal{G}$ consists of the
$\lambda > \lambda_s$ with $\|s(\lambda)\|_M < \Delta$.

**Correction.** As for the regularization subproblem, the set-builder description of the source
with $H + \lambda M \succ 0$ contains points outside $(\lambda_s, \infty)$ when $\lambda_1 > 0$;
the definition requires $\lambda > \lambda_s$. -/
def setG_tr (hH : H.IsHermitian) (hM : M.PosDef) (g : EuclideanSpace ℝ (Fin n)) (Δ : ℝ) :
    Set ℝ :=
  {lam | lambdaS hH hM < lam ∧ mNorm M (stepOf g H M lam) < Δ}

/-- The **regularization target** $\tau(\lambda) = (\lambda/\sigma)^{2/(r-2)}$ of (8.2.9) of
[cartis2022evaluation], with the real power. -/
noncomputable def regTarget (σ r : ℝ) (lam : ℝ) : ℝ := (lam / σ) ^ (2 / (r - 2))

/-- For $\sigma > 0$ and $\lambda \ge 0$, the regularization target is a square: $\tau(\lambda) =
\bigl((\lambda/\sigma)^{1/(r-2)}\bigr)^2$. -/
theorem regTarget_eq_sq {σ lam : ℝ} (r : ℝ) (hσ : 0 < σ) (hlam : 0 ≤ lam) :
    regTarget σ r lam = ((lam / σ) ^ (1 / (r - 2))) ^ 2 := by
  rw [regTarget, ← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hlam hσ.le)]
  congr 1
  push_cast
  ring

variable (hH : H.IsHermitian) (hM : M.PosDef)
include hH

/-- For $\sigma > 0$, $\lambda$ lies in the regularization set $\mathcal{L}$ if and only if
$\lambda > \lambda_s$ and $\tau(\lambda) \le \pi(\lambda)$, where $\pi$ is the secular function. -/
theorem mem_setL_reg_iff {σ r lam : ℝ} (hσ : 0 < σ) :
    lam ∈ setL_reg hH hM g σ r ↔ lambdaS hH hM < lam ∧ regTarget σ r lam ≤ secularFn g H M lam := by
  refine and_congr_right fun hlam => ?_
  have hl : 0 ≤ lam := (lambdaS_nonneg hH hM).trans hlam.le
  rw [regTarget_eq_sq r hσ hl, ← mNorm_stepOf_sq hM]
  exact (pow_le_pow_iff_left₀ (Real.rpow_nonneg (div_nonneg hl hσ.le) _) (mNorm_nonneg _ _)
    two_ne_zero).symm

/-- For $\sigma > 0$, $\lambda$ lies in the regularization set $\mathcal{G}$ if and only if
$\lambda > \lambda_s$ and $\pi(\lambda) < \tau(\lambda)$, where $\pi$ is the secular function. -/
theorem mem_setG_reg_iff {σ r lam : ℝ} (hσ : 0 < σ) :
    lam ∈ setG_reg hH hM g σ r ↔ lambdaS hH hM < lam ∧ secularFn g H M lam < regTarget σ r lam := by
  refine and_congr_right fun hlam => ?_
  have hl : 0 ≤ lam := (lambdaS_nonneg hH hM).trans hlam.le
  rw [regTarget_eq_sq r hσ hl, ← mNorm_stepOf_sq hM]
  exact (pow_lt_pow_iff_left₀ (mNorm_nonneg _ _) (Real.rpow_nonneg (div_nonneg hl hσ.le) _)
    two_ne_zero).symm

/-- For $\Delta > 0$, $\lambda$ lies in the trust-region set $\mathcal{L}$ if and only if
$\lambda > \lambda_s$ and $\Delta^2 \le \pi(\lambda)$, where $\pi$ is the secular function. -/
theorem mem_setL_tr_iff {Δ lam : ℝ} (hΔ : 0 < Δ) :
    lam ∈ setL_tr hH hM g Δ ↔ lambdaS hH hM < lam ∧ Δ ^ 2 ≤ secularFn g H M lam := by
  refine and_congr_right fun _ => ?_
  rw [← mNorm_stepOf_sq hM]
  exact (pow_le_pow_iff_left₀ hΔ.le (mNorm_nonneg _ _) two_ne_zero).symm

/-- For $\Delta > 0$, $\lambda$ lies in the trust-region set $\mathcal{G}$ if and only if
$\lambda > \lambda_s$ and $\pi(\lambda) < \Delta^2$, where $\pi$ is the secular function. -/
theorem mem_setG_tr_iff {Δ lam : ℝ} (hΔ : 0 < Δ) :
    lam ∈ setG_tr hH hM g Δ ↔ lambdaS hH hM < lam ∧ secularFn g H M lam < Δ ^ 2 := by
  refine and_congr_right fun _ => ?_
  rw [← mNorm_stepOf_sq hM]
  exact (pow_lt_pow_iff_left₀ (mNorm_nonneg _ _) hΔ.le two_ne_zero).symm

/-- **Section 8.3.1** of [cartis2022evaluation], the partition for the regularization subproblem.
Let $H$ be symmetric, $M$ symmetric positive definite, and $\sigma, r \in \mathbb{R}$. Then
$\mathcal{L} \cap \mathcal{G} = \emptyset$, $\mathcal{F} = \mathcal{L} \cup \mathcal{G} =
(\lambda_s, \infty)$, $\mathcal{N} \cap \mathcal{F} = \emptyset$ and
$\mathcal{N} \cup \mathcal{F} = \mathbb{R}$. So $\mathcal{N}$, $\mathcal{L}$ and $\mathcal{G}$
partition $\mathbb{R}$.

**Correction.** The partition holds for the interval forms of the sets, not for the set-builder
forms of the source (see `CartisGouldToint.Chapter08.setN`). -/
theorem setF_reg_eq_Ioi (σ r : ℝ) :
    Disjoint (setL_reg hH hM g σ r) (setG_reg hH hM g σ r) ∧
      setF_reg hH hM g σ r = Ioi (lambdaS hH hM) ∧
      Disjoint (setN hH hM) (setF_reg hH hM g σ r) ∧ setN hH hM ∪ setF_reg hH hM g σ r = univ := by
  have hF : setF_reg hH hM g σ r = Ioi (lambdaS hH hM) := by
    ext lam
    simp only [setF_reg, setL_reg, setG_reg, mem_union, mem_ofPred_eq, mem_Ioi]
    exact ⟨fun h => h.elim And.left And.left, fun h => (le_or_gt _ _).imp (⟨h, ·⟩) (⟨h, ·⟩)⟩
  refine ⟨Set.disjoint_left.2 fun lam h1 h2 => not_le.2 h2.2 h1.2, hF, ?_, ?_⟩
  · rw [hF]; exact Set.disjoint_left.2 fun lam (h1 : lam ≤ _) (h2 : _ < lam) => not_le.2 h2 h1
  · rw [hF, setN, Iic_union_Ioi]

/-- **Section 8.3.2** of [cartis2022evaluation], the partition for the trust-region subproblem. Let
$H$ be symmetric, $M$ symmetric positive definite, and $\Delta \in \mathbb{R}$. Then
$\mathcal{L} \cap \mathcal{G} = \emptyset$ and $\mathcal{L} \cup \mathcal{G} = (\lambda_s,
\infty)$.

**Correction.** The partition holds for the interval forms of the sets, not for the set-builder
forms of the source (see `CartisGouldToint.Chapter08.setN`). -/
theorem setL_tr_union_setG_tr (Δ : ℝ) :
    Disjoint (setL_tr hH hM g Δ) (setG_tr hH hM g Δ) ∧
      setL_tr hH hM g Δ ∪ setG_tr hH hM g Δ = Ioi (lambdaS hH hM) := by
  refine ⟨Set.disjoint_left.2 fun lam h1 h2 => not_le.2 h2.2 h1.2, ?_⟩
  ext lam
  simp only [setL_tr, setG_tr, mem_union, mem_ofPred_eq, mem_Ioi]
  exact ⟨fun h => h.elim And.left And.left, fun h => (le_or_gt _ _).imp (⟨h, ·⟩) (⟨h, ·⟩)⟩

/-- **Section 8.3.1** of [cartis2022evaluation], $\mathcal{L}$ and $\mathcal{G}$ as intervals for
the regularization subproblem. Let $H$ be symmetric, $M$ symmetric positive definite,
$\sigma > 0$ and $r > 2$. Let $s^*$ be a global minimizer of the regularization subproblem
(8.1.3), and let $\lambda^* = \sigma \|s^*\|_M^{r-2}$. Then $\lambda_s \le \lambda^*$,
$$\mathcal{L} = (\lambda_s, \lambda^*], \qquad \mathcal{G} = (\lambda^*, \infty), \qquad
  \mathcal{F} = (\lambda_s, \infty),$$
and $\mathcal{L}$ is nonempty if and only if $\lambda^* > \lambda_s$ (the easy case). -/
theorem setL_reg_eq_Ioc {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r) {s : EuclideanSpace ℝ (Fin n)}
    (hs : IsRegularizationSolution g H M σ r s) :
    lambdaS hH hM ≤ σ * mNorm M s ^ (r - 2) ∧
      setL_reg hH hM g σ r = Ioc (lambdaS hH hM) (σ * mNorm M s ^ (r - 2)) ∧
      setG_reg hH hM g σ r = Ioi (σ * mNorm M s ^ (r - 2)) ∧
      setF_reg hH hM g σ r = Ioi (lambdaS hH hM) ∧
      ((setL_reg hH hM g σ r).Nonempty ↔ lambdaS hH hM < σ * mNorm M s ^ (r - 2)) := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hmin := (isRegularizationSolution_iff_scaled hM).1 hs
  have hle : lambdaS hH hM ≤ σ * mNorm M s ^ (r - 2) := by
    rw [lambdaS_eq, mNorm_eq_norm_toScaled hM]
    exact (shiftThreshold_le_of_isMinOn_regModel (hH := hT) hσ hr hmin).1
  have hiff : ∀ lam, lambdaS hH hM < lam →
      (regTarget σ r lam ≤ secularFn g H M lam ↔ lam ≤ σ * mNorm M s ^ (r - 2)) := by
    intro lam hlam
    rw [lambdaS_eq] at hlam
    rw [secularFn_eq_secular hM, mNorm_eq_norm_toScaled hM]
    exact le_secular_iff_of_regularization hσ hr hmin hlam
  have hL : setL_reg hH hM g σ r = Ioc (lambdaS hH hM) (σ * mNorm M s ^ (r - 2)) := by
    ext lam
    rw [mem_setL_reg_iff hH hM hσ, mem_Ioc]
    exact and_congr_right (hiff lam)
  have hG : setG_reg hH hM g σ r = Ioi (σ * mNorm M s ^ (r - 2)) := by
    ext lam
    rw [mem_setG_reg_iff hH hM hσ, mem_Ioi]
    constructor
    · rintro ⟨hlam, h⟩
      exact not_le.1 fun h' => (not_le.2 h) ((hiff lam hlam).2 h')
    · intro h
      have hlam := hle.trans_lt h
      exact ⟨hlam, not_le.1 fun h' => (not_le.2 h) ((hiff lam hlam).1 h')⟩
  refine ⟨hle, hL, hG, ?_, ?_⟩
  · rw [setF_reg, hL, hG, Ioc_union_Ioi_eq_Ioi hle]
  · rw [hL, nonempty_Ioc]

/-- **Section 8.3.2** of [cartis2022evaluation], $\mathcal{L}$ and $\mathcal{G}$ as intervals for
the trust-region subproblem. Let $H$ be symmetric, $M$ symmetric positive definite and
$\Delta > 0$. Let $s^*$ be a global minimizer of the trust-region subproblem (8.1.2), and let
$\lambda^*$ be a multiplier for $s^*$ in the sense of Theorem 8.2.7. Then
$\lambda_s \le \lambda^*$,
$$\mathcal{L} = (\lambda_s, \lambda^*], \qquad \mathcal{G} = (\lambda^*, \infty),$$
and $\mathcal{L}$ is nonempty if and only if $\lambda^* > \lambda_s$.

The multiplier conditions are `CartisGouldToint.Chapter08.IsTrustRegionKKT`. -/
theorem setL_tr_eq_Ioc {Δ : ℝ} (hΔ : 0 < Δ) {s : EuclideanSpace ℝ (Fin n)}
    (hs : IsTrustRegionSolution g H M Δ s) {lamStar : ℝ}
    (hkkt : IsTrustRegionKKT g H M Δ s lamStar) :
    lambdaS hH hM ≤ lamStar ∧ setL_tr hH hM g Δ = Ioc (lambdaS hH hM) lamStar ∧
      setG_tr hH hM g Δ = Ioi lamStar ∧
      ((setL_tr hH hM g Δ).Nonempty ↔ lambdaS hH hM < lamStar) := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hn := ((isTrustRegionSolution_iff_scaled hM).1 hs).1
  have hμ := (isTrustRegionKKT_iff_scaled hM hΔ).1 hkkt
  have hle : lambdaS hH hM ≤ lamStar := by
    rw [lambdaS_eq]; exact (shiftThreshold_le_of_isTrustRegionMultiplier (hH := hT) hμ).1
  have hiff : ∀ lam, lambdaS hH hM < lam → (Δ ^ 2 ≤ secularFn g H M lam ↔ lam ≤ lamStar) := by
    intro lam hlam
    rw [lambdaS_eq] at hlam
    rw [secularFn_eq_secular hM]
    exact le_secular_iff_of_trustRegion hΔ hμ hn hlam
  have hL : setL_tr hH hM g Δ = Ioc (lambdaS hH hM) lamStar := by
    ext lam
    rw [mem_setL_tr_iff hH hM hΔ, mem_Ioc]
    exact and_congr_right (hiff lam)
  refine ⟨hle, hL, ?_, by rw [hL, nonempty_Ioc]⟩
  ext lam
  rw [mem_setG_tr_iff hH hM hΔ, mem_Ioi]
  constructor
  · rintro ⟨hlam, h⟩
    exact not_le.1 fun h' => (not_le.2 h) ((hiff lam hlam).2 h')
  · intro h
    have hlam := hle.trans_lt h
    exact ⟨hlam, not_le.1 fun h' => (not_le.2 h) ((hiff lam hlam).1 h')⟩

omit hH

/-! ### The corrections -/

/-- **Section 8.2.1** of [cartis2022evaluation], the **Taylor correction**. Let
$\tau : \mathbb{R} \to \mathbb{R}$ be a target, $k \in \mathbb{N}$ and
$\lambda_c \in \mathbb{R}$, and let $t_k$ be the Taylor polynomial of order $k$ of the secular
function $\pi$ at $\lambda_c$. The Taylor correction $\delta^T_k(\lambda_c)$ is the rightmost
real root $\delta$ of
$$t_k(\delta) = \tau(\lambda_c + \delta), \qquad (8.2.15)$$
defined as the supremum of the set of roots.

The supremum is the value `sSup` of Mathlib, which is $0$ when the set of roots is empty or
unbounded above. For odd $k$ and $\lambda_c \in \mathcal{L}$ the set is nonempty and bounded
above (`Subproblem.taylorCorrection_mem`). -/
noncomputable def taylorCorrectionFn (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (τ : ℝ → ℝ) (k : ℕ) (lamc : ℝ) : ℝ :=
  sSup {δ | secularTaylorPoly g H M k lamc δ = τ (lamc + δ)}

/-- The **transformed regularization secular function** of Section 8.2.2 of [cartis2022evaluation]:
for $\sigma, r, \beta \in \mathbb{R}$,
$$\theta(\lambda; \beta) = \pi(\lambda)^{\beta} - (\lambda/\sigma)^{2\beta/(r-2)},$$
where $\pi$ is the secular function and the powers are real powers.

**Typo.** Section 8.3.1 writes the transformed target as $(\lambda/\sigma)^{\beta/(r-2)}$. It is
$(\lambda/\sigma)^{2\beta/(r-2)}$, consistent with (8.2.25). For the same reason the prose
ranges $\beta \in (0, r - 2]$ and $\beta \in [-1, 0)$ should read $(0, (r-2)/2]$ and
$[-1/2, 0)$. -/
noncomputable def regSecularFn (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (σ r β lam : ℝ) : ℝ :=
  secularFn g H M lam ^ β - (lam / σ) ^ (2 * β / (r - 2))

/-- **Equation (8.2.25)** of [cartis2022evaluation], the **regularization Newton correction**. For
$\sigma, r, \beta, \lambda_c \in \mathbb{R}$,
$$\delta^N(\lambda_c, \beta) = -\frac{\theta(\lambda_c; \beta)}{\theta^{(1)}(\lambda_c;
  \beta)},$$
where $\theta$ is the transformed regularization secular function
`CartisGouldToint.Chapter08.regSecularFn`.

The derivative is `deriv`, which is $0$ where $\theta$ is not differentiable, and division by
$0$ gives $0$. -/
noncomputable def regNewtonCorrectionFn (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (σ r β lamc : ℝ) : ℝ :=
  -regSecularFn g H M σ r β lamc / deriv (regSecularFn g H M σ r β) lamc

/-- **Equation (8.2.24)** of [cartis2022evaluation], the **trust-region Newton correction**. For
$\Delta, \lambda_c \in \mathbb{R}$,
$$\delta^N = \frac{2\pi(\lambda_c)}{\pi^{(1)}(\lambda_c)} \Bigl(1 -
  \frac{\|s(\lambda_c)\|_M}{\Delta}\Bigr),$$
where $\pi$ is the secular function.

The derivative is `deriv`, which is $0$ where $\pi$ is not differentiable, and division by $0$
gives $0$. -/
noncomputable def trNewtonCorrectionFn (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (Δ lamc : ℝ) : ℝ :=
  2 * secularFn g H M lamc / deriv (secularFn g H M) lamc * (1 - mNorm M (stepOf g H M lamc) / Δ)

/-- The Taylor correction equals the backbone correction `Subproblem.taylorCorrection` for the
scaled gradient $M^{-1} g$ and the scaled operator $M^{-1} H$ on the $M$-inner product space. -/
theorem taylorCorrectionFn_eq (τ : ℝ → ℝ) (k : ℕ) (lamc : ℝ) :
    taylorCorrectionFn g H M τ k lamc =
      taylorCorrection (scaledGrad hM g) (scaledOp H hM) τ k lamc := by
  simp only [taylorCorrectionFn, taylorCorrection, secularTaylorPoly_eq hM]

/-- The transformed regularization secular function equals the backbone function
`Subproblem.regSecular` for the scaled gradient $M^{-1} g$ and the scaled operator $M^{-1} H$. -/
theorem regSecularFn_eq (σ r β : ℝ) :
    regSecularFn g H M σ r β = regSecular (scaledGrad hM g) (scaledOp H hM) σ r β := by
  funext lam
  rw [regSecularFn, regSecular, secularFn_eq_secular hM]

/-- The regularization Newton correction equals the backbone correction
`Subproblem.regNewtonCorrection` for the scaled gradient $M^{-1} g$ and the scaled operator
$M^{-1} H$. -/
theorem regNewtonCorrectionFn_eq (σ r β lamc : ℝ) :
    regNewtonCorrectionFn g H M σ r β lamc =
      regNewtonCorrection (scaledGrad hM g) (scaledOp H hM) σ r β lamc := by
  rw [regNewtonCorrectionFn, regNewtonCorrection, regSecularFn_eq hM]

/-- The trust-region Newton correction equals the backbone correction
`Subproblem.trNewtonCorrection` for the scaled gradient $M^{-1} g$ and the scaled operator
$M^{-1} H$. -/
theorem trNewtonCorrectionFn_eq (Δ lamc : ℝ) :
    trNewtonCorrectionFn g H M Δ lamc =
      trNewtonCorrection (scaledGrad hM g) (scaledOp H hM) Δ lamc := by
  rw [trNewtonCorrectionFn, trNewtonCorrection, secularFn_eq_secular hM,
    mNorm_eq_norm_toScaled hM, toScaled_stepOf hM]

/-! ### Runs of the secular iterations -/

/-- The **exit test** of Algorithms 8.3.1 and 8.3.2 of [cartis2022evaluation]. For
$\varepsilon \in \mathbb{R}$ and a sequence $(\lambda_k)$, the test holds at iteration $k$ if
$k \ge 1$ and $|\lambda_k - \lambda_{k-1}| \le \varepsilon$.

A run stops at the first iteration where the test holds (`Optimization.IsFirstHit`). -/
def exitTest (ε : ℝ) (lam : ℕ → ℝ) (k : ℕ) : Prop := 1 ≤ k ∧ |lam k - lam (k - 1)| ≤ ε

/-- If a real sequence converges and $\varepsilon > 0$, then the exit test holds at some iteration.
-/
theorem exists_exitTest {x : ℕ → ℝ} {L ε : ℝ} (hx : Tendsto x atTop (𝓝 L)) (hε : 0 < ε) :
    ∃ k, exitTest ε x k := by
  have hd : Tendsto (fun k => x (k + 1) - x k) atTop (𝓝 0) := by
    simpa using (hx.comp (tendsto_add_atTop_nat 1)).sub hx
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hd ε hε
  have := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at this
  exact ⟨N + 1, by omega, by simpa using this.le⟩

/-- Let $C(t)$ be a nonempty finite set of reals for each $t \in \mathbb{R}$, and let
$x_0 \in \mathbb{R}$. Then there is a sequence that starts at $x_0$ in which each $x_{k+1}$ is
the largest element of $C(x_k)$. -/
theorem exists_isGreatest_seq (C : ℝ → Finset ℝ) (hC : ∀ t, (C t).Nonempty) (x₀ : ℝ) :
    ∃ x : ℕ → ℝ, x 0 = x₀ ∧ ∀ k, IsGreatest (C (x k) : Set ℝ) (x (k + 1)) := by
  obtain ⟨x, hx0, hx⟩ := Optimization.exists_run_of_forall_exists (init := fun a => a = x₀)
    (stop := fun _ _ => False) (step := fun _ a b => IsGreatest (C a : Set ℝ) b) ⟨x₀, rfl⟩
    fun _ a _ => ⟨_, Finset.isGreatest_max' _ (hC a)⟩
  exact ⟨x, hx0, fun k => hx k not_false⟩

/-- Let $x$ be a real sequence, $a, L \in \mathbb{R}$ and $K \in \mathbb{N}$. If $x_0 \in (a, L]$
and, for each $k < K$, $x_k \in (a, L]$ implies $x_k \le x_{k+1} \le L$, then $x_k \in (a, L]$
for all $k \le K$. -/
theorem mem_Ioc_of_le {x : ℕ → ℝ} {a L : ℝ} {K : ℕ} (h0 : x 0 ∈ Ioc a L)
    (hstep : ∀ k < K, x k ∈ Ioc a L → x k ≤ x (k + 1) ∧ x (k + 1) ≤ L) :
    ∀ k ≤ K, x k ∈ Ioc a L := by
  intro k hk
  induction k with
  | zero => exact h0
  | succ k ih =>
    have hmem := ih (by omega)
    obtain ⟨h1, h2⟩ := hstep k (by omega) hmem
    exact ⟨hmem.1.trans_le h1, h2⟩

/-- Let $x$ be a real sequence and $a, L \in \mathbb{R}$. If $x_0 \in (a, L]$ and, for each $k$,
$x_k \in (a, L]$ implies $x_k \le x_{k+1} \le L$, then $x_k \in (a, L]$ for all $k$ and $x$ is
monotone. -/
theorem mem_Ioc_and_monotone {x : ℕ → ℝ} {a L : ℝ} (h0 : x 0 ∈ Ioc a L)
    (hstep : ∀ k, x k ∈ Ioc a L → x k ≤ x (k + 1) ∧ x (k + 1) ≤ L) :
    (∀ k, x k ∈ Ioc a L) ∧ Monotone x := by
  have hmem : ∀ k, x k ∈ Ioc a L := fun k =>
    mem_Ioc_of_le (K := k) h0 (fun j _ => hstep j) k le_rfl
  exact ⟨hmem, monotone_nat_of_le_succ fun k => (hstep k (hmem k)).1⟩

/-! ### Algorithm 8.3.1 -/

/-- **Algorithm 8.3.1** of [cartis2022evaluation], the candidates. Let $\sigma, r \in \mathbb{R}$,
$i_{\max}, j_{\max} \in \mathbb{N}$, exponents $\beta_1, \dots, \beta_{j_{\max}}$ and
$\lambda_c \in \mathbb{R}$. The candidates of one iteration from $\lambda_c$ are the finite set
of the numbers
$$\lambda_c + \delta^T_{2i-1}(\lambda_c) \quad (i = 1, \dots, i_{\max}), \qquad \lambda_c +
  \delta^N(\lambda_c, \beta_j) \quad (j = 1, \dots, j_{\max}),$$
where $\delta^T_{2i-1}$ is the Taylor correction of odd order $2i - 1$ for the target
$\tau(\lambda) = (\lambda/\sigma)^{2/(r-2)}$, and $\delta^N$ is the Newton correction (8.2.25).

The exponents are indexed by `Fin jMax`, from $0$. -/
noncomputable def candidates831 (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (σ r : ℝ) (iMax jMax : ℕ) (β : Fin jMax → ℝ) (lamc : ℝ) : Finset ℝ :=
  (Finset.Icc 1 iMax).image
      (fun i => lamc + taylorCorrectionFn g H M (regTarget σ r) (2 * i - 1) lamc) ∪
    Finset.univ.image fun j => lamc + regNewtonCorrectionFn g H M σ r (β j) lamc

/-- **Algorithm 8.3.1** of [cartis2022evaluation], a run. The algorithm estimates the multiplier
$\lambda^*$ of the regularization subproblem (8.1.3) from a point of $\mathcal{L}$. Let
$\sigma, r, \varepsilon \in \mathbb{R}$, $i_{\max}, j_{\max} \in \mathbb{N}$ and exponents
$\beta_1, \dots, \beta_{j_{\max}}$. A sequence $(\lambda_k)$ and an index $K$ form a **run of
Algorithm 8.3.1** if $i_{\max} \ge 1$, $\varepsilon > 0$, each $\beta_j \in [-1/2, (r-2)/2]$
with $\beta_j \neq 0$, $\lambda_0 \in \mathcal{L}$, each $\lambda_{k+1}$ with $k < K$ is the
largest candidate (`CartisGouldToint.Chapter08.candidates831`) from $\lambda_k$, and $K$ is the
first iteration at which $K \ge 1$ and $|\lambda_K - \lambda_{K-1}| \le \varepsilon$. The output
is $\lambda_K$.

**Correction.** The source allows any $\beta_j \in [-1/2, (r-2)/2]$, but the Newton correction
(8.2.25) is undefined at $\beta = 0$. The run requires $\beta_j \neq 0$. -/
structure algorithm_8_3_1 (hH : H.IsHermitian) (hM : M.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (σ r : ℝ) (iMax jMax : ℕ) (β : Fin jMax → ℝ) (ε : ℝ) (lam : ℕ → ℝ) (K : ℕ) : Prop where
  /-- The number of Taylor corrections satisfies $i_{\max} \ge 1$. -/
  one_le_iMax : 1 ≤ iMax
  /-- The exit tolerance satisfies $\varepsilon > 0$. -/
  eps_pos : 0 < ε
  /-- Each exponent satisfies $\beta_j \in [-1/2, (r-2)/2]$ and $\beta_j \neq 0$. -/
  beta_mem : ∀ j, β j ∈ Icc (-1 / 2) ((r - 2) / 2) ∧ β j ≠ 0
  /-- The initial estimate $\lambda_0$ lies in $\mathcal{L}$. -/
  start : lam 0 ∈ setL_reg hH hM g σ r
  /-- For each $k < K$, $\lambda_{k+1}$ is the largest candidate from $\lambda_k$. -/
  step : ∀ k < K, IsGreatest (candidates831 g H M σ r iMax jMax β (lam k) : Set ℝ) (lam (k + 1))
  /-- The index $K$ is the first iteration at which the exit test holds. -/
  exit : Optimization.IsFirstHit (exitTest ε lam) K

/-- **Algorithm 8.3.1** of [cartis2022evaluation], convergence and termination. Let $H$ be
symmetric, $M$ symmetric positive definite, $\sigma > 0$ and $r > 2$. Let $s^*$ be a global
minimizer of the regularization subproblem (8.1.3), and let
$\lambda^* = \sigma \|s^*\|_M^{r-2}$. Let $i_{\max} \ge 1$, let each
$\beta_j \in [-1/2, (r-2)/2]$ with $\beta_j \neq 0$, let $\varepsilon > 0$, and let
$\lambda_0 \in \mathcal{L}$. Then:

* every sequence $(x_k)$ with $x_0 = \lambda_0$ in which each $x_{k+1}$ is the largest candidate
  from $x_k$ stays in $\mathcal{L}$, is monotone and converges to $\lambda^*$; if moreover
  $j_{\max} \ge 1$, then there is $\gamma \in [0, 1)$ with $\lambda^* - x_{k+1} \le \gamma
  (\lambda^* - x_k)$ for all $k$, and the convergence is Q-superlinear;
* every run $(\lambda_k, K)$ of Algorithm 8.3.1 has $\lambda_k \in \mathcal{L}$ for $k \le K$
  and $\lambda_k \le \lambda_{k+1}$ for $k < K$, and its output satisfies
  $\lambda_K \le \lambda^*$;
* there is a run of Algorithm 8.3.1 with $\lambda_0$ as its first iterate.

The hypothesis $\lambda_0 \in \mathcal{L}$ implies the easy case $\lambda^* > \lambda_s$
(`CartisGouldToint.Chapter08.setL_reg_eq_Ioc`). Q-superlinear convergence is
`ConvergesSuperlinearly`. -/
theorem algorithm_8_3_1_terminates (hH : H.IsHermitian) (hM : M.PosDef) {σ r : ℝ} (hσ : 0 < σ)
    (hr : 2 < r) {s : EuclideanSpace ℝ (Fin n)} (hs : IsRegularizationSolution g H M σ r s)
    {iMax jMax : ℕ} (hi : 1 ≤ iMax) {β : Fin jMax → ℝ}
    (hβ : ∀ j, β j ∈ Icc (-1 / 2) ((r - 2) / 2) ∧ β j ≠ 0) {ε : ℝ} (hε : 0 < ε) {lam₀ : ℝ}
    (h₀ : lam₀ ∈ setL_reg hH hM g σ r) :
    (∀ x : ℕ → ℝ, x 0 = lam₀ →
      (∀ k, IsGreatest (candidates831 g H M σ r iMax jMax β (x k) : Set ℝ) (x (k + 1))) →
      (∀ k, x k ∈ setL_reg hH hM g σ r) ∧ Monotone x ∧
      Tendsto x atTop (𝓝 (σ * mNorm M s ^ (r - 2))) ∧
      (0 < jMax → ∃ γ ∈ Ico (0 : ℝ) 1,
        (∀ k, σ * mNorm M s ^ (r - 2) - x (k + 1) ≤ γ * (σ * mNorm M s ^ (r - 2) - x k)) ∧
        ConvergesSuperlinearly x (σ * mNorm M s ^ (r - 2)))) ∧
    (∀ (lam : ℕ → ℝ) (K : ℕ), algorithm_8_3_1 hH hM g σ r iMax jMax β ε lam K →
      (∀ k ≤ K, lam k ∈ setL_reg hH hM g σ r) ∧ (∀ k < K, lam k ≤ lam (k + 1)) ∧
        lam K ≤ σ * mNorm M s ^ (r - 2)) ∧
    ∃ lam K, algorithm_8_3_1 hH hM g σ r iMax jMax β ε lam K ∧ lam 0 = lam₀ := by
  set lamStar := σ * mNorm M s ^ (r - 2) with hlamStar
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hmin := (isRegularizationSolution_iff_scaled hM).1 hs
  have hL := (setL_reg_eq_Ioc hH hM hσ hr hs).2.1
  have heasy : lambdaS hH hM < lamStar := by
    have := h₀; rw [hL] at this; exact this.1.trans_le this.2
  have hstar : shiftThreshold hT < lamStar := by rwa [← lambdaS_eq]
  have hroot : secular (scaledGrad hM g) (scaledOp H hM) lamStar = regTarget σ r lamStar := by
    rw [hlamStar, mNorm_eq_norm_toScaled hM]
    exact secular_eq_of_regularization hσ hr hmin (by rwa [← mNorm_eq_norm_toScaled hM])
  have hpos : 0 < lamStar := (lambdaS_nonneg hH hM).trans_lt heasy
  have hg : scaledGrad hM g ≠ 0 := by
    intro h
    rw [h, secular_zero_left] at hroot
    exact (Real.rpow_pos_of_pos (div_pos hpos hσ) _).ne' hroot.symm
  have hadm := (tau_admissible_8_2_9 hH hM).2 σ r hσ hr
  rw [lambdaS_eq] at hadm
  have htgt : IsSecularTarget hT (scaledGrad hM g) (regTarget σ r) (shiftThreshold hT) lamStar :=
    ⟨hg, neg_leftmost_le_shiftThreshold, hadm.continuousOn.mono Ioi_subset_Ici_self,
      hadm.monotoneOn.mono Ioi_subset_Ici_self, hstar, hroot⟩
  have hβ' : ∀ j, β j ∈ Ico (-1 / 2) 0 ∪ Ioc 0 ((r - 2) / 2) := fun j => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := hβ j
    rcases h3.lt_or_gt with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨h, h2⟩
  have hLs : setL_reg hH hM g σ r = Ioc (shiftThreshold hT) lamStar := by rw [hL, lambdaS_eq]
  -- every candidate from `λc ∈ 𝓛` lies in `[λc, λ*]`
  have hcand : ∀ lamc ∈ Ioc (shiftThreshold hT) lamStar,
      ∀ c ∈ candidates831 g H M σ r iMax jMax β lamc, lamc ≤ c ∧ c ≤ lamStar := by
    intro lamc hc c hcm
    simp only [candidates831, Finset.mem_union, Finset.mem_image, Finset.mem_Icc,
      Finset.mem_univ, true_and] at hcm
    rcases hcm with ⟨i, ⟨hi1, -⟩, rfl⟩ | ⟨j, rfl⟩
    · rw [taylorCorrectionFn_eq hM]
      have hk : Odd (2 * i - 1) := ⟨i - 1, by omega⟩
      exact (htgt.taylorCorrection_mem hk hc).2.2
    · rw [regNewtonCorrectionFn_eq hM]
      obtain ⟨h1, h2⟩ := regNewtonCorrection_mem hσ hr (hβ' j) hstar hroot hc.1
      exact ⟨h2 hc.2, h1⟩
  have hseq : ∀ x : ℕ → ℝ, x 0 = lam₀ →
      (∀ k, IsGreatest (candidates831 g H M σ r iMax jMax β (x k) : Set ℝ) (x (k + 1))) →
      (∀ k, x k ∈ Ioc (shiftThreshold hT) lamStar) ∧ Monotone x := by
    intro x hx0 hx
    refine mem_Ioc_and_monotone (by rw [hx0, ← hLs]; exact h₀) fun k hk => ?_
    exact hcand _ hk _ (hx k).1
  have hconv : ∀ x : ℕ → ℝ, x 0 = lam₀ →
      (∀ k, IsGreatest (candidates831 g H M σ r iMax jMax β (x k) : Set ℝ) (x (k + 1))) →
      Tendsto x atTop (𝓝 lamStar) := by
    intro x hx0 hx
    obtain ⟨hmem, -⟩ := hseq x hx0 hx
    have hstep : ∀ j, x j + taylorCorrection (scaledGrad hM g) (scaledOp H hM) (regTarget σ r) 1
        (x j) ≤ x (j + 1) ∧ x (j + 1) ≤ lamStar := fun j => ⟨by
      rw [← taylorCorrectionFn_eq hM]
      exact (hx j).2 (Finset.mem_union_left _ (Finset.mem_image.2 ⟨1, by simp [hi], rfl⟩)),
      (hmem (j + 1)).2⟩
    exact (htgt.tendsto_of_taylorCorrection_le (k := 1) odd_one (hmem 0) hstep).2
  refine ⟨fun x hx0 hx => ?_, fun lam K hrun => ?_, ?_⟩
  · obtain ⟨hmem, hmono⟩ := hseq x hx0 hx
    refine ⟨fun k => hLs ▸ hmem k, hmono, hconv x hx0 hx, fun hj => ?_⟩
    have hstep : ∀ j, x j + regNewtonCorrection (scaledGrad hM g) (scaledOp H hM) σ r (β ⟨0, hj⟩)
        (x j) ≤ x (j + 1) ∧ x (j + 1) ≤ lamStar := fun j => ⟨by
      rw [← regNewtonCorrectionFn_eq hM]
      exact (hx j).2 (Finset.mem_union_right _ (Finset.mem_image.2 ⟨⟨0, hj⟩, by simp, rfl⟩)),
      (hmem (j + 1)).2⟩
    obtain ⟨-, -, hγ, hlin, hsup⟩ :=
      tendsto_of_regNewtonCorrection_le hσ hr (hβ' ⟨0, hj⟩) hstar hroot (hmem 0) hstep
    exact ⟨_, hγ, hlin, hsup⟩
  · have hmem := mem_Ioc_of_le (K := K) (by rw [← hLs]; exact hrun.start)
      fun k hk hm => hcand _ hm _ (hrun.step k hk).1
    exact ⟨fun k hk => hLs ▸ hmem k hk, fun k hk => (hcand _ (hmem k hk.le) _ (hrun.step k hk).1).1,
      (hmem K le_rfl).2⟩
  · have hne : ∀ t, (candidates831 g H M σ r iMax jMax β t).Nonempty := fun t =>
      ⟨_, Finset.mem_union_left _ (Finset.mem_image.2 ⟨1, by simp [hi], rfl⟩)⟩
    obtain ⟨x, hx0, hx⟩ := exists_isGreatest_seq _ hne lam₀
    obtain ⟨K, hK⟩ := Optimization.exists_isFirstHit (exists_exitTest (hconv x hx0 hx) hε)
    exact ⟨x, K, ⟨hi, hε, hβ, hx0 ▸ h₀, fun k _ => hx k, hK⟩, hx0⟩

/-! ### Algorithm 8.3.2 -/

/-- **Algorithm 8.3.2** of [cartis2022evaluation], the candidates. Let $\Delta \in \mathbb{R}$,
$i_{\max} \in \mathbb{N}$ and $\lambda_c \in \mathbb{R}$. The candidates of one iteration from
$\lambda_c$ are the finite set of the numbers
$$\lambda_c + \delta^T_{2i-1}(\lambda_c) \quad (i = 1, \dots, i_{\max}), \qquad \lambda_c +
  \delta^N,$$
where $\delta^T_{2i-1}$ is the Taylor correction of odd order $2i - 1$ for the constant target
$\Delta^2$, and $\delta^N$ is the Newton correction (8.2.24). -/
noncomputable def candidates832 (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (Δ : ℝ) (iMax : ℕ) (lamc : ℝ) : Finset ℝ :=
  insert (lamc + trNewtonCorrectionFn g H M Δ lamc)
    ((Finset.Icc 1 iMax).image fun i => lamc + taylorCorrectionFn g H M (fun _ => Δ ^ 2)
      (2 * i - 1) lamc)

/-- **Algorithm 8.3.2** of [cartis2022evaluation], a run. The algorithm estimates the multiplier
$\lambda^*$ of the trust-region subproblem (8.1.2) from a point of $\mathcal{L}$. Let
$\Delta, \varepsilon \in \mathbb{R}$ and $i_{\max} \in \mathbb{N}$. A sequence $(\lambda_k)$ and
an index $K$ form a **run of Algorithm 8.3.2** if $i_{\max} \ge 1$, $\varepsilon > 0$,
$\lambda_0$ lies in the trust-region set $\mathcal{L}$, each $\lambda_{k+1}$ with $k < K$ is the
largest candidate (`CartisGouldToint.Chapter08.candidates832`) from $\lambda_k$, and $K$ is the
first iteration at which $K \ge 1$ and $|\lambda_K - \lambda_{K-1}| \le \varepsilon$. The output
is $\lambda_K$. -/
structure algorithm_8_3_2 (hH : H.IsHermitian) (hM : M.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (Δ : ℝ) (iMax : ℕ) (ε : ℝ) (lam : ℕ → ℝ) (K : ℕ) : Prop where
  /-- The number of Taylor corrections satisfies $i_{\max} \ge 1$. -/
  one_le_iMax : 1 ≤ iMax
  /-- The exit tolerance satisfies $\varepsilon > 0$. -/
  eps_pos : 0 < ε
  /-- The initial estimate $\lambda_0$ lies in the trust-region set $\mathcal{L}$. -/
  start : lam 0 ∈ setL_tr hH hM g Δ
  /-- For each $k < K$, $\lambda_{k+1}$ is the largest candidate from $\lambda_k$. -/
  step : ∀ k < K, IsGreatest (candidates832 g H M Δ iMax (lam k) : Set ℝ) (lam (k + 1))
  /-- The index $K$ is the first iteration at which the exit test holds. -/
  exit : Optimization.IsFirstHit (exitTest ε lam) K

/-- **Algorithm 8.3.2** of [cartis2022evaluation], convergence and termination. Let $H$ be
symmetric, $M$ symmetric positive definite and $\Delta > 0$. Let $s^*$ be a global minimizer of
the trust-region subproblem (8.1.2), and let $\lambda^*$ be a multiplier for $s^*$ in the sense
of Theorem 8.2.7. Let $i_{\max} \ge 1$, $\varepsilon > 0$ and $\lambda_0 \in \mathcal{L}$. Then:

* every sequence $(x_k)$ with $x_0 = \lambda_0$ in which each $x_{k+1}$ is the largest candidate
  from $x_k$ stays in $\mathcal{L}$, is monotone and converges to $\lambda^*$; there is
  $\gamma \in [0, 1)$ with $\lambda^* - x_{k+1} \le \gamma (\lambda^* - x_k)$ for all $k$, and
  the convergence is Q-superlinear;
* every run $(\lambda_k, K)$ of Algorithm 8.3.2 has $\lambda_k \in \mathcal{L}$ for $k \le K$
  and $\lambda_k \le \lambda_{k+1}$ for $k < K$, and its output satisfies
  $\lambda_K \le \lambda^*$;
* there is a run of Algorithm 8.3.2 with $\lambda_0$ as its first iterate.

The hypothesis $\lambda_0 \in \mathcal{L}$ implies the easy case $\lambda^* > \lambda_s$
(`CartisGouldToint.Chapter08.setL_tr_eq_Ioc`). The multiplier conditions are
`CartisGouldToint.Chapter08.IsTrustRegionKKT`. -/
theorem algorithm_8_3_2_terminates (hH : H.IsHermitian) (hM : M.PosDef) {Δ : ℝ} (hΔ : 0 < Δ)
    {s : EuclideanSpace ℝ (Fin n)} (hs : IsTrustRegionSolution g H M Δ s) {lamStar : ℝ}
    (hkkt : IsTrustRegionKKT g H M Δ s lamStar) {iMax : ℕ} (hi : 1 ≤ iMax) {ε : ℝ} (hε : 0 < ε)
    {lam₀ : ℝ} (h₀ : lam₀ ∈ setL_tr hH hM g Δ) :
    (∀ x : ℕ → ℝ, x 0 = lam₀ →
      (∀ k, IsGreatest (candidates832 g H M Δ iMax (x k) : Set ℝ) (x (k + 1))) →
      (∀ k, x k ∈ setL_tr hH hM g Δ) ∧ Monotone x ∧ Tendsto x atTop (𝓝 lamStar) ∧
      (∃ γ ∈ Ico (0 : ℝ) 1, ∀ k, lamStar - x (k + 1) ≤ γ * (lamStar - x k)) ∧
      ConvergesSuperlinearly x lamStar) ∧
    (∀ (lam : ℕ → ℝ) (K : ℕ), algorithm_8_3_2 hH hM g Δ iMax ε lam K →
      (∀ k ≤ K, lam k ∈ setL_tr hH hM g Δ) ∧ (∀ k < K, lam k ≤ lam (k + 1)) ∧
        lam K ≤ lamStar) ∧
    ∃ lam K, algorithm_8_3_2 hH hM g Δ iMax ε lam K ∧ lam 0 = lam₀ := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hμ := (isTrustRegionKKT_iff_scaled hM hΔ).1 hkkt
  have hL := (setL_tr_eq_Ioc hH hM hΔ hs hkkt).2.1
  have heasy : lambdaS hH hM < lamStar := by
    have := h₀; rw [hL] at this; exact this.1.trans_le this.2
  have hstar : shiftThreshold hT < lamStar := by rwa [← lambdaS_eq]
  have hstar' := neg_leftmost_le_shiftThreshold.trans_lt hstar
  have hroot : secular (scaledGrad hM g) (scaledOp H hM) lamStar = Δ ^ 2 :=
    secular_eq_of_trustRegion hμ hstar
  have hg : scaledGrad hM g ≠ 0 := by
    intro h
    rw [h, secular_zero_left] at hroot
    exact (pow_pos hΔ 2).ne' hroot.symm
  have htgt : IsSecularTarget hT (scaledGrad hM g) (fun _ => Δ ^ 2) (shiftThreshold hT) lamStar :=
    ⟨hg, neg_leftmost_le_shiftThreshold, continuousOn_const, monotoneOn_const, hstar, hroot⟩
  have hLs : setL_tr hH hM g Δ = Ioc (shiftThreshold hT) lamStar := by rw [hL, lambdaS_eq]
  have hcand : ∀ lamc ∈ Ioc (shiftThreshold hT) lamStar,
      ∀ c ∈ candidates832 g H M Δ iMax lamc, lamc ≤ c ∧ c ≤ lamStar := by
    intro lamc hc c hcm
    simp only [candidates832, Finset.mem_insert, Finset.mem_image, Finset.mem_Icc] at hcm
    rcases hcm with rfl | ⟨i, ⟨hi1, -⟩, rfl⟩
    · rw [trNewtonCorrectionFn_eq hM]
      obtain ⟨h1, h2⟩ := trNewtonCorrection_mem hΔ hstar' hroot
        (neg_leftmost_le_shiftThreshold.trans_lt hc.1)
      exact ⟨h2 hc.2, h1⟩
    · rw [taylorCorrectionFn_eq hM]
      have hk : Odd (2 * i - 1) := ⟨i - 1, by omega⟩
      exact (htgt.taylorCorrection_mem hk hc).2.2
  have hseq : ∀ x : ℕ → ℝ, x 0 = lam₀ →
      (∀ k, IsGreatest (candidates832 g H M Δ iMax (x k) : Set ℝ) (x (k + 1))) →
      (∀ k, x k ∈ Ioc (shiftThreshold hT) lamStar) ∧ Monotone x := by
    intro x hx0 hx
    refine mem_Ioc_and_monotone (by rw [hx0, ← hLs]; exact h₀) fun k hk => ?_
    exact hcand _ hk _ (hx k).1
  have hnewton : ∀ x : ℕ → ℝ, x 0 = lam₀ →
      (∀ k, IsGreatest (candidates832 g H M Δ iMax (x k) : Set ℝ) (x (k + 1))) →
      Monotone x ∧ Tendsto x atTop (𝓝 lamStar) ∧
      (∃ γ ∈ Ico (0 : ℝ) 1, ∀ k, lamStar - x (k + 1) ≤ γ * (lamStar - x k)) ∧
      ConvergesSuperlinearly x lamStar := by
    intro x hx0 hx
    obtain ⟨hmem, -⟩ := hseq x hx0 hx
    have hstep : ∀ j, x j + trNewtonCorrection (scaledGrad hM g) (scaledOp H hM) Δ (x j) ≤
        x (j + 1) ∧ x (j + 1) ≤ lamStar := fun j => ⟨by
      rw [← trNewtonCorrectionFn_eq hM]
      exact (hx j).2 (Finset.mem_insert_self _ _), (hmem (j + 1)).2⟩
    obtain ⟨h1, h2, hγ, hlin, hsup⟩ := tendsto_of_trNewtonCorrection_le hΔ hstar' hroot
      ⟨neg_leftmost_le_shiftThreshold.trans_lt (hmem 0).1, (hmem 0).2⟩ hstep
    exact ⟨h1, h2, ⟨_, hγ, hlin⟩, hsup⟩
  refine ⟨fun x hx0 hx => ?_, fun lam K hrun => ?_, ?_⟩
  · obtain ⟨hmem, -⟩ := hseq x hx0 hx
    exact ⟨fun k => hLs ▸ hmem k, hnewton x hx0 hx⟩
  · have hmem := mem_Ioc_of_le (K := K) (by rw [← hLs]; exact hrun.start)
      fun k hk hm => hcand _ hm _ (hrun.step k hk).1
    exact ⟨fun k hk => hLs ▸ hmem k hk, fun k hk => (hcand _ (hmem k hk.le) _ (hrun.step k hk).1).1,
      (hmem K le_rfl).2⟩
  · have hne : ∀ t, (candidates832 g H M Δ iMax t).Nonempty := fun _ =>
      Finset.insert_nonempty _ _
    obtain ⟨x, hx0, hx⟩ := exists_isGreatest_seq _ hne lam₀
    obtain ⟨K, hK⟩ := Optimization.exists_isFirstHit (exists_exitTest (hnewton x hx0 hx).2.1 hε)
    exact ⟨x, K, ⟨hi, hε, hx0 ▸ h₀, fun k _ => hx k, hK⟩, hx0⟩

/-! ### Global minimizers -/

/-- **Equation (8.3.2)** of [cartis2022evaluation], the **minimum-$M$-norm solution**. Let $H$ be
symmetric, $M$ symmetric positive definite and $\lambda \in \mathbb{R}$. Let $b_1, \dots, b_n$
be generalized eigenvectors of the pencil $(H, M)$, orthonormal in the $M$-inner product, with
eigenvalues $\lambda_1, \dots, \lambda_n$. Then
$$s_s = -(H + \lambda M)^{+} g = -\sum_{i \,:\, \lambda + \lambda_i \neq 0} \frac{b_i^T
  g}{\lambda + \lambda_i} \, b_i.$$
Here $(H + \lambda M)^{+}$ is the pseudoinverse with respect to the $M$-inner product. When
$g \perp \ker(H + \lambda M)$, $s_s$ is the solution of $(H + \lambda M) x = -g$ that is
$M$-orthogonal to $\ker(H + \lambda M)$, and the solution of least $M$-norm
(`CartisGouldToint.Chapter08.minNormSolution_spec`).

**Reading.** The source does not say in which norm the solution is minimal. The $M$-norm is
used, because with it $s_s$ is the limit of $s(\lambda')$ as $\lambda' \downarrow -\lambda_1$
(`CartisGouldToint.Chapter08.tendsto_stepOf_minNormSolution`).

The definition transports `Subproblem.particular` for the scaled operator $M^{-1} H$ back from
the $M$-inner product space. -/
noncomputable def minNormSolution (hH : H.IsHermitian) (hM : M.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (lam : ℝ) : EuclideanSpace ℝ (Fin n) :=
  (toScaled hM).symm (particular (isSymmetric_scaledOp hH) (scaledGrad hM g) lam)

/-- The minimum-$M$-norm solution, moved to the $M$-inner product space, is the backbone solution
`Subproblem.particular` for the scaled operator $M^{-1} H$ and the scaled gradient $M^{-1} g$. -/
theorem toScaled_minNormSolution (hH : H.IsHermitian) (hM : M.PosDef) (lam : ℝ) :
    toScaled hM (minNormSolution hH hM g lam) =
      particular (isSymmetric_scaledOp hH) (scaledGrad hM g) lam :=
  (toScaled hM).apply_symm_apply _

/-- **Equation (8.3.2)** of [cartis2022evaluation], characterization of the minimum-$M$-norm
solution. Let $H$ be symmetric, $M$ symmetric positive definite and $\lambda \in \mathbb{R}$,
and suppose that $g \perp \ker(H + \lambda M)$. Then $s_s$ solves $(H + \lambda M) s_s = -g$,
satisfies $\langle M s_s, v \rangle = 0$ for every $v \in \ker(H + \lambda M)$, and has
$\|s_s\|_M \le \|y\|_M$ for every solution $y$ of $(H + \lambda M) y = -g$. Moreover, $s_s$ is
the only solution $x$ of $(H + \lambda M) x = -g$ with $\langle M x, v \rangle = 0$ for all
$v \in \ker(H + \lambda M)$.

The orthogonality $g \perp \ker(H + \lambda M)$ is in the Euclidean inner product. -/
theorem minNormSolution_spec (hH : H.IsHermitian) (hM : M.PosDef) {lam : ℝ}
    (hg : g ∈ (LinearMap.ker (toEuclideanLin (H + lam • M)))ᗮ) :
    toEuclideanLin (H + lam • M) (minNormSolution hH hM g lam) = -g ∧
      (∀ v ∈ LinearMap.ker (toEuclideanLin (H + lam • M)),
        ⟪toEuclideanLin M (minNormSolution hH hM g lam), v⟫ = 0) ∧
      (∀ y, toEuclideanLin (H + lam • M) y = -g →
        mNorm M (minNormSolution hH hM g lam) ≤ mNorm M y) ∧
      ∀ x, (toEuclideanLin (H + lam • M) x = -g ∧
        ∀ v ∈ LinearMap.ker (toEuclideanLin (H + lam • M)), ⟪toEuclideanLin M x, v⟫ = 0) →
        x = minNormSolution hH hM g lam := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hiff := toScaled_eq_particular_iff (hM := hM) hH hg
  have hg' := (scaledGrad_mem_orthogonal_iff (H := H) (hM := hM) lam g).2 hg
  obtain ⟨-, -, hmin, -⟩ := (particular_spec (hH := hT) (g := scaledGrad hM g) lam).2.1 hg'
  obtain ⟨h1, h2⟩ := (hiff _).1 (toScaled_minNormSolution hH hM lam)
  refine ⟨h1, h2, fun y hy => ?_, fun x hx => ?_⟩
  · rw [mNorm_eq_norm_toScaled hM, mNorm_eq_norm_toScaled hM, toScaled_minNormSolution]
    exact hmin _ ((add_smul_scaledOp_toScaled_eq_neg_iff lam g y).2 hy)
  · exact (toScaled hM).injective ((hiff x).2 hx |>.trans (toScaled_minNormSolution hH hM lam).symm)

/-- **Section 8.3.1** of [cartis2022evaluation], the limit of the step at the threshold. Let $H$ be
symmetric and $M$ symmetric positive definite, and suppose that $g \perp \ker(H - \lambda_1 M)$.
Then
$$s(\lambda) \to s_s \quad \text{as } \lambda \downarrow -\lambda_1,$$
where $s_s$ is the minimum-$M$-norm solution (8.3.2) at $\lambda = -\lambda_1$.

The orthogonality is in the Euclidean inner product. The proof specializes
`Subproblem.tendsto_step_threshold`. -/
theorem tendsto_stepOf_minNormSolution (hH : H.IsHermitian) (hM : M.PosDef)
    (hg : g ∈ (LinearMap.ker (toEuclideanLin (H + (-leftmostPencil hH hM) • M)))ᗮ) :
    Tendsto (stepOf g H M) (𝓝[>] (-leftmostPencil hH hM))
      (𝓝 (minNormSolution hH hM g (-leftmostPencil hH hM))) := by
  rw [leftmostPencil_eq] at hg ⊢
  have hg' := (scaledGrad_mem_orthogonal_iff (H := H) (hM := hM) _ g).2 hg
  have h := ((tendsto_step_threshold (hH := isSymmetric_scaledOp (hM := hM) hH)
    (g := scaledGrad hM g)).1 hg').1
  have hc : Continuous (toScaled hM).symm :=
    (toScaled hM).symm.toContinuousLinearEquiv.continuous
  have := (hc.tendsto _).comp h
  refine this.congr fun lam => ?_
  simp only [Function.comp_apply, ← toScaled_stepOf hM, LinearEquiv.symm_apply_apply]

/-- Let $n \ge 1$, $H$ symmetric and $M$ symmetric positive definite, and let $\mu = -\lambda_1$,
where $\lambda_1$ is the leftmost eigenvalue of the scaled operator $M^{-1} H$. Every vector $w$
of $\ker(M^{-1} H + \mu I)$ on the $M$-inner product space is, moved back to $\mathbb{R}^n$, of
the form $\alpha v$ for some $\alpha \in \mathbb{R}$ and some nonzero $v$ with
$H v = \lambda_1 M v$.

This is the form of the minimizers in the hard case $\lambda^* = -\lambda_1$ of Corollaries
8.3.1 and 8.3.2. -/
theorem exists_eigen_smul_of_mem_ker [NeZero n] (hH : H.IsHermitian) (hM : M.PosDef) {μ : ℝ}
    (hμ : μ = -leftmost (isSymmetric_scaledOp (hM := hM) hH)) {w : ScaledSpace hM}
    (hw : w ∈ LinearMap.ker ((scaledOp H hM + μ • 1 : ScaledSpace hM →L[ℝ] ScaledSpace hM) :
      ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)) :
    ∃ v : EuclideanSpace ℝ (Fin n), v ≠ 0 ∧ ∃ α : ℝ,
      toEuclideanLin H v = leftmostPencil hH hM • toEuclideanLin M v ∧
        (toScaled hM).symm w = α • v := by
  rcases eq_or_ne w 0 with rfl | hw0
  · have hT := isSymmetric_scaledOp (hM := hM) hH
    obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hT)
    obtain ⟨u, hu, heig⟩ := exists_eigen_of_eigenvalues (hM := hM) hH i
    exact ⟨u, hu, 0, by rw [leftmostPencil_eq, ← hi]; exact heig, by simp⟩
  · refine ⟨(toScaled hM).symm w, by simpa using hw0, 1, ?_, (one_smul _ _).symm⟩
    rw [eigen_of_mem_ker hw, hμ, neg_neg, leftmostPencil_eq]

/-- **Corollary 8.3.1** of [cartis2022evaluation] (global minimizers of the regularization
subproblem). Let $n \ge 1$, $H$ symmetric, $M$ symmetric positive definite, $\sigma > 0$ and
$r > 2$. Let $s^*$ be a global minimizer of the regularization subproblem (8.1.3), let
$\lambda^* = \sigma \|s^*\|_M^{r-2}$, let $s_s$ be the minimum-$M$-norm solution (8.3.2) at
$\lambda^*$, and let $\lambda_1$ be the leftmost eigenvalue of the pencil $(H, M)$. Then
$\lambda^* \ge -\lambda_1$, and (8.3.1) holds:

* if $\lambda^* > -\lambda_1$, then $s^* = s_s$, and $s^*$ is the only global minimizer;
* if $\lambda^* = -\lambda_1$, then $s^* = s_s + \alpha v$ for some nonzero $v$ with
  $H v = \lambda_1 M v$ and some $\alpha \in \mathbb{R}$ with $\|s_s + \alpha v\|_M =
  (\lambda^*/\sigma)^{1/(r-2)}$.

In all cases the optimal value (8.3.3) is
$$m^R(s^*) = \tfrac12 \Bigl(\langle g, s_s \rangle - \frac{r-2}{r} \lambda^*
  (\lambda^*/\sigma)^{2/(r-2)}\Bigr).$$

**Correction.** The source writes $s^* = s_s + \alpha v_1$ for a fixed eigenvector $v_1$ for
$\lambda_1$. When $\lambda_1$ is multiple, one fixed eigenvector does not parametrize all
minimizers. The statement gives some nonzero generalized eigenvector $v$ for $\lambda_1$, which
is equivalent to $s^* - s_s \in \ker(H + \lambda^* M)$.

The regularized model $m^R$ is `CartisGouldToint.Chapter08.regModel`, and $\lambda_1$ is
`CartisGouldToint.Chapter08.leftmostPencil`. -/
theorem corollary_8_3_1 [NeZero n] (hH : H.IsHermitian) (hM : M.PosDef) {σ r : ℝ} (hσ : 0 < σ)
    (hr : 2 < r) {s : EuclideanSpace ℝ (Fin n)} (hs : IsRegularizationSolution g H M σ r s) :
    -leftmostPencil hH hM ≤ σ * mNorm M s ^ (r - 2) ∧
    (-leftmostPencil hH hM < σ * mNorm M s ^ (r - 2) →
      s = minNormSolution hH hM g (σ * mNorm M s ^ (r - 2)) ∧
        ∀ u, IsRegularizationSolution g H M σ r u → u = s) ∧
    (σ * mNorm M s ^ (r - 2) = -leftmostPencil hH hM →
      ∃ v : EuclideanSpace ℝ (Fin n), v ≠ 0 ∧ ∃ α : ℝ,
        toEuclideanLin H v = leftmostPencil hH hM • toEuclideanLin M v ∧
        s = minNormSolution hH hM g (σ * mNorm M s ^ (r - 2)) + α • v ∧
        mNorm M (minNormSolution hH hM g (σ * mNorm M s ^ (r - 2)) + α • v) =
          (σ * mNorm M s ^ (r - 2) / σ) ^ (1 / (r - 2))) ∧
    regModel g H M σ r s = 1 / 2 * (⟪g, minNormSolution hH hM g (σ * mNorm M s ^ (r - 2))⟫ -
      (r - 2) / r * (σ * mNorm M s ^ (r - 2)) * (σ * mNorm M s ^ (r - 2) / σ) ^ (2 / (r - 2))) := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hmin := (isRegularizationSolution_iff_scaled hM).1 hs
  obtain ⟨hle, hker, -, hstep⟩ := shiftThreshold_le_of_isMinOn_regModel (hH := hT) hσ hr hmin
  have hn := mNorm_eq_norm_toScaled hM s
  rw [hn]
  refine ⟨?_, fun hlt => ⟨?_, fun u hu => ?_⟩, fun heq => ?_, ?_⟩
  · rw [leftmostPencil_eq]; exact neg_leftmost_le_shiftThreshold.trans hle
  · rw [leftmostPencil_eq] at hlt
    exact (toScaled hM).injective ((hstep hlt).1.trans (toScaled_minNormSolution hH hM _).symm)
  · rw [leftmostPencil_eq] at hlt
    have hc := ((isSymmetricCoercive_add_smul_iff (hH := hT) _).2 hlt).isCoercive
    exact (toScaled hM).injective (eq_of_isMinOn_regModel_of_posDef hT hσ hr hmin hc
      ((isRegularizationSolution_iff_scaled hM).1 hu))
  · rw [leftmostPencil_eq] at heq
    set w := toScaled hM s - particular hT (scaledGrad hM g) (σ * ‖toScaled hM s‖ ^ (r - 2))
    obtain ⟨v, hv0, α, heig, hwv⟩ := exists_eigen_smul_of_mem_ker hH hM heq hker
    have hsum : minNormSolution hH hM g (σ * ‖toScaled hM s‖ ^ (r - 2)) + α • v = s := by
      apply (toScaled hM).injective
      rw [map_add, toScaled_minNormSolution, ← hwv, LinearEquiv.apply_symm_apply, add_sub_cancel]
    refine ⟨v, hv0, α, heig, hsum.symm, ?_⟩
    have hσ0 : σ * ‖toScaled hM s‖ ^ (r - 2) / σ = ‖toScaled hM s‖ ^ (r - 2) := by field_simp
    rw [hsum, hn, hσ0, one_div, Real.rpow_rpow_inv (norm_nonneg _) (sub_pos.2 hr).ne']
  · rw [regModel_eq_regModel hM, optimalValue_eq_of_regularization (hH := hT) hσ hr hmin,
      ← toScaled_minNormSolution hH hM, inner_scaledGrad_toScaled]

/-- **Corollary 8.3.2** of [cartis2022evaluation] (global minimizers of the trust-region
subproblem). Let $n \ge 1$, $H$ symmetric, $M$ symmetric positive definite and $\Delta > 0$. Let
$s^*$ be a global minimizer of the trust-region subproblem (8.1.2) with multiplier $\lambda^*$
in the sense of Theorem 8.2.7, so that $\lambda^* \ge 0$ and
$\lambda^* (\|s^*\|_M^2 - \Delta^2) = 0$. Let $s_s$ be the minimum-$M$-norm solution (8.3.2) at
$\lambda^*$, and let $\lambda_1$ be the leftmost eigenvalue of the pencil $(H, M)$. Then
$\lambda^* \ge -\lambda_1$, and:

* if $\lambda^* > -\lambda_1$, then $s^* = s_s$, and $s^*$ is the only global minimizer;
* if $\lambda^* = -\lambda_1$, then $s^* = s_s + \alpha v$ for some nonzero $v$ with
  $H v = \lambda_1 M v$ and some $\alpha \in \mathbb{R}$ with $\|s_s + \alpha v\|_M \le \Delta$,
  and $\|s_s + \alpha v\|_M = \Delta$ if $\lambda^* > 0$.

In all cases the optimal value (8.3.5) is
$$m(s^*) = \tfrac12 \bigl(\langle g, s_s \rangle - \lambda^* \Delta^2\bigr).$$

**Correction.** The source writes $s^* = s_s + \alpha v_1$ for a fixed eigenvector $v_1$ for
$\lambda_1$. When $\lambda_1$ is multiple, one fixed eigenvector does not parametrize all
minimizers; the statement gives some nonzero generalized eigenvector $v$ for $\lambda_1$.

**Correction.** The source requires $\|s_s + \alpha v_1\|_M = \Delta$. When $\lambda^* = 0$ (so
$\lambda_1 = 0$, an interior solution) this fails: for $n = 1$, $H = 0$, $g = 0$, $M = 1$ and
$\Delta = 1$, the minimizer $s^* = 0$ is not on the boundary. The boundary condition is stated
for $\lambda^* > 0$ only.

The model $m$ is `CartisGouldToint.Chapter08.model`, and the multiplier conditions are
`CartisGouldToint.Chapter08.IsTrustRegionKKT`. -/
theorem corollary_8_3_2 [NeZero n] (hH : H.IsHermitian) (hM : M.PosDef) {Δ : ℝ} (hΔ : 0 < Δ)
    {s : EuclideanSpace ℝ (Fin n)} (hs : IsTrustRegionSolution g H M Δ s) {lamStar : ℝ}
    (hkkt : IsTrustRegionKKT g H M Δ s lamStar) :
    -leftmostPencil hH hM ≤ lamStar ∧
    (-leftmostPencil hH hM < lamStar →
      s = minNormSolution hH hM g lamStar ∧ ∀ u, IsTrustRegionSolution g H M Δ u → u = s) ∧
    (lamStar = -leftmostPencil hH hM →
      ∃ v : EuclideanSpace ℝ (Fin n), v ≠ 0 ∧ ∃ α : ℝ,
        toEuclideanLin H v = leftmostPencil hH hM • toEuclideanLin M v ∧
        s = minNormSolution hH hM g lamStar + α • v ∧
        mNorm M (minNormSolution hH hM g lamStar + α • v) ≤ Δ ∧
        (0 < lamStar → mNorm M (minNormSolution hH hM g lamStar + α • v) = Δ)) ∧
    model g H s = 1 / 2 * (⟪g, minNormSolution hH hM g lamStar⟫ - lamStar * Δ ^ 2) := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  obtain ⟨hn, hmin⟩ := (isTrustRegionSolution_iff_scaled hM).1 hs
  have hμ := (isTrustRegionKKT_iff_scaled hM hΔ).1 hkkt
  obtain ⟨hle, hker, -, hstep⟩ := shiftThreshold_le_of_isTrustRegionMultiplier (hH := hT) hμ
  refine ⟨?_, fun hlt => ⟨?_, fun u hu => ?_⟩, fun heq => ?_, ?_⟩
  · rw [leftmostPencil_eq]; exact neg_leftmost_le_shiftThreshold.trans hle
  · rw [leftmostPencil_eq] at hlt
    exact (toScaled hM).injective ((hstep hlt).1.trans (toScaled_minNormSolution hH hM _).symm)
  · rw [leftmostPencil_eq] at hlt
    have hc := ((isSymmetricCoercive_add_smul_iff (hH := hT) _).2 hlt).isCoercive
    obtain ⟨hun, humin⟩ := (isTrustRegionSolution_iff_scaled hM).1 hu
    exact (toScaled hM).injective (eq_of_isMinOn_closedBall_of_posDef hT hμ hn hc hun humin)
  · rw [leftmostPencil_eq] at heq
    set w := toScaled hM s - particular hT (scaledGrad hM g) lamStar
    obtain ⟨v, hv0, α, heig, hwv⟩ := exists_eigen_smul_of_mem_ker hH hM heq hker
    have hsum : minNormSolution hH hM g lamStar + α • v = s := by
      apply (toScaled hM).injective
      rw [map_add, toScaled_minNormSolution, ← hwv, LinearEquiv.apply_symm_apply, add_sub_cancel]
    refine ⟨v, hv0, α, heig, hsum.symm, ?_, fun hpos => ?_⟩
    · rw [hsum, mNorm_eq_norm_toScaled hM]; exact hn
    · rw [hsum, mNorm_eq_norm_toScaled hM]; exact hμ.norm_eq_of_pos hpos
  · rw [model_eq_quadModel hM, optimalValue_eq_of_trustRegion (hH := hT) hμ,
      ← toScaled_minNormSolution hH hM, inner_scaledGrad_toScaled]

end CartisGouldToint.Chapter08
