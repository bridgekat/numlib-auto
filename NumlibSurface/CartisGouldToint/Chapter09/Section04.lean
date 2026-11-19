/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.ModelBased.QuadraticModel
import NumlibSurface.CartisGouldToint.Chapter09.Section03

/-!
# Cartis, Gould and Toint, Section 9.4: The trust-region subproblem

This module formalizes Section 9.4 of [cartis2022evaluation], on the trust-region subproblem
(8.1.2): minimize $m(s) = \langle g, s \rangle + \frac12 \langle s, H s \rangle$ subject to
$\|s\|_M \le \Delta$. The bounds (9.4.1) bracket the multiplier $\lambda^*$ of a minimizer on the
boundary. The optimal value $m_\Delta = \min_{\|s\|_M \le \Delta} m(s)$ decreases with $\Delta$
(9.4.5), and (9.4.6)–(9.4.7) bound it from points on spheres of other radii. For
$\lambda > \lambda_s$, the radius $\Delta(\lambda) = \|s(\lambda)\|_M$ has the computable value
$m_{\Delta(\lambda)} = \frac12 (\langle g, s(\lambda) \rangle - \lambda \Delta(\lambda)^2)$. These
bounds give sufficient conditions for the early-termination tests (9.4.2)–(9.4.4) of a criticality
measure $\phi^\Delta_{f,2}(x)$, which equals $-m_\Delta$ for $g = \nabla f(x)$, $H = \nabla^2 f(x)$
and $M = I$.

The trust-region analogues of Algorithms 9.2.1 and 8.3.2 are
`CartisGouldToint.Chapter09.algorithm_9_2_1` with the trust-region sets and
`CartisGouldToint.Chapter08.algorithm_8_3_2`. The proofs use the backbone module
`Numlib.Optimization.Subproblem.TrustRegion`.

## Main definitions

* Section 9.4.2, `CartisGouldToint.Chapter09.trValue`: the optimal value $m_\Delta$ of the
  trust-region subproblem.

## Main results

* Equation (9.4.1), `CartisGouldToint.Chapter09.lambdaStar_bounds_9_4_1`: $\|g\|_{M^{-1}}/\Delta -
  \lambda_n \le \lambda^* \le \|g\|_{M^{-1}}/\Delta - \lambda_1$.
* Equation (9.4.5), `CartisGouldToint.Chapter09.trValue_antitone`: $m_\Delta$ decreases as
  $\Delta \ge 0$ grows.
* Equation (9.4.7), `CartisGouldToint.Chapter09.trValue_le_min`: $m_\Delta \le
  \min(m((\Delta/\Delta^-) s^-), m_{\Delta^-})$ for $\|s^-\|_M = \Delta^- \le \Delta$.
* Equations (9.4.5)–(9.4.7), `CartisGouldToint.Chapter09.optimalValue_bounds_9_4_6`: attainment,
  (9.4.5)–(9.4.7), and the value $m_{\Delta(\lambda)}$ for $\lambda > \lambda_s$.
* Section 9.4.2, `CartisGouldToint.Chapter09.trValue_of_posDef`: the interior case $H \succ 0$,
  $\|H^{-1} g\|_M \le \Delta$.
* Section 9.4.2, `CartisGouldToint.Chapter09.taylorMeasure_two_eq_neg_trValue_of_contDiffAt`:
  $\phi^\Delta_{f,2}(x) = -m_\Delta$ for $g = \nabla f(x)$, $H = \nabla^2 f(x)$ and $M = I$.
* Equations (9.4.2)–(9.4.4), `CartisGouldToint.Chapter09.test_9_4_2_iff_of_contDiffAt`: the tests
  (9.4.2) on $\phi^\Delta_{f,2}(x)$ are the tests (9.4.3)–(9.4.4) on $m_\Delta$.
* Section 9.4.2, `CartisGouldToint.Chapter09.test_9_4_3_of_9_4_6`,
  `CartisGouldToint.Chapter09.test_9_4_4_of_9_4_6`,
  `CartisGouldToint.Chapter09.test_9_4_3_of_9_4_7`: sufficient conditions for (9.4.3) and (9.4.4)
  from (9.4.6) and (9.4.7).
* Section 9.4.2, `CartisGouldToint.Chapter09.tests_9_4_3_9_4_4_of_setL`,
  `CartisGouldToint.Chapter09.test_9_4_3_of_setG`: the same with the radius $\Delta(\lambda)$ for
  $\lambda \in \mathcal{L}$ or $\lambda \in \mathcal{G}$.
* Footnote 65, `CartisGouldToint.Chapter09.trValue_ge_of_setG`: for $\lambda \in \mathcal{G}$,
  $m_{\Delta(\lambda)} \ge \frac12 (\langle g, s(\lambda) \rangle - \lambda \Delta^2)$.

## Conventions

* The measure $\phi^\Delta_{f,2}(x)$ of (9.4.2) is `Optimization.taylorMeasure (ftaylorSeries ℝ f x)
  2 Δ univ`. It uses the Euclidean norm, so it is compared with $m_\Delta$ for $M = I$.
* The Hessian matrix $\nabla^2 f(x)$ is `Optimization.hessianMatrix f x`.

## Deviations from the source

* **Equation (9.4.5)** (correction). The source claims $m_{\Delta_2} \le m_{\Delta_1}$ if and only
  if $\Delta_2 \ge \Delta_1$; only the implication holds. See
  `CartisGouldToint.Chapter09.trValue_antitone`.
* **Equations (9.4.6) and (9.4.7)** (generalization). The bounds hold for any point on the sphere of
  radius $\Delta^+$ (or $\Delta^-$), not only for minimizers, and for $\Delta \le \Delta^+$ (or
  $\Delta^- \le \Delta$). See `CartisGouldToint.Chapter09.optimalValue_bounds_9_4_6`.
* **Section 9.4.2, trust-region boundary** (correction). A singular positive semidefinite
  model can have interior minimizers. Also, a trial in $\mathcal{L}$ can have
  $\Delta(\lambda)=\Delta$. See `CartisGouldToint.Chapter09.trValue_of_posDef` and
  `CartisGouldToint.Chapter09.tests_9_4_3_9_4_4_of_setL`.
* **Section 9.4.2, optimal value and criticality tests** (generalization). Empty balls
  have totalized value $0$, and the test equivalences also hold for thresholds of
  arbitrary sign. See `CartisGouldToint.Chapter09.trValue` and
  `CartisGouldToint.Chapter09.test_9_4_2_iff_of_contDiffAt`.

## Not formalized

* **The Gertz–Gill criterion (9.4.8) of the Notes.** The source quotes it without saying what a
  "suitable approximate solution" is.
* **The closing advice of Section 9.4.2 to stop Algorithm 9.2.1 as soon as (9.4.3) or (9.4.4)
  holds.** It is a heuristic use of the tests; the sufficient conditions that it relies on are
  `CartisGouldToint.Chapter09.test_9_4_3_of_9_4_6`,
  `CartisGouldToint.Chapter09.test_9_4_4_of_9_4_6`, `CartisGouldToint.Chapter09.test_9_4_3_of_9_4_7`
  and their forms for $\mathcal{L}$ and $\mathcal{G}$.
-/

open Matrix Set Metric
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter09

open Subproblem CartisGouldToint.Chapter08

variable {n : ℕ} {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}

/-- **Equation (9.4.1)** of [cartis2022evaluation], bounds on the multiplier. Let $H$ be symmetric,
$M$ symmetric positive definite and $\Delta > 0$. Let $s^*$ satisfy $\|s^*\|_M = \Delta$, with a
multiplier $\lambda^*$ in the sense of Theorem 8.2.7, and let $\lambda_1 \le \lambda_n$ be the
extreme eigenvalues of the pencil $(H, M)$. Then
$$\frac{\|g\|_{M^{-1}}}{\Delta} - \lambda_n \le \lambda^* \le \frac{\|g\|_{M^{-1}}}{\Delta} -
  \lambda_1.$$
The same bounds hold with any $l_1 \le \lambda_1$ in place of $\lambda_1$ and any
$l_n \ge \lambda_n$ in place of $\lambda_n$.

The multiplier conditions are `CartisGouldToint.Chapter08.IsTrustRegionKKT`. The theorem does
not need $s^*$ to be a global minimizer. -/
theorem lambdaStar_bounds_9_4_1 (hH : H.IsHermitian) (hM : M.PosDef) {Δ : ℝ} (hΔ : 0 < Δ)
    {s : EuclideanSpace ℝ (Fin n)} {lamStar : ℝ} (hkkt : IsTrustRegionKKT g H M Δ s lamStar)
    (hsΔ : mNorm M s = Δ) :
    mNorm M⁻¹ g / Δ - rightmostPencil hH hM ≤ lamStar ∧
      lamStar ≤ mNorm M⁻¹ g / Δ - leftmostPencil hH hM ∧
      ∀ l₁ lₙ : ℝ, l₁ ≤ leftmostPencil hH hM → rightmostPencil hH hM ≤ lₙ →
        mNorm M⁻¹ g / Δ - lₙ ≤ lamStar ∧ lamStar ≤ mNorm M⁻¹ g / Δ - l₁ := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hμ := (isTrustRegionKKT_iff_scaled hM hΔ).1 hkkt
  have hne : Nonempty (Fin n) := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Subsingleton.elim s 0, mNorm_zero] at hsΔ
    exact hΔ.ne hsΔ
  have hl : -leftmost hT ≤ lamStar := (isPositive_add_smul_iff (hH := hT) lamStar).1 hμ.isPositive
  obtain ⟨h1, h2⟩ := norm_add_smul_apply_bounds (hH := hT) hl (toScaled hM s)
  rw [hμ.shifted, norm_neg, ← mNorm_eq_norm_toScaled hM, hsΔ] at h1 h2
  rw [mNorm_inv_eq_norm_scaledGrad hM, leftmostPencil_eq, rightmostPencil_eq]
  have hA : ‖scaledGrad hM g‖ / Δ - rightmost hT ≤ lamStar := by
    rw [sub_le_iff_le_add, div_le_iff₀ hΔ]; linarith
  have hB : lamStar ≤ ‖scaledGrad hM g‖ / Δ - leftmost hT := by
    rw [le_sub_iff_add_le, le_div_iff₀ hΔ]; linarith
  exact ⟨hA, hB, fun l₁ lₙ hl₁ hlₙ => ⟨by linarith, by linarith⟩⟩

/-- **Section 9.4.2** of [cartis2022evaluation], the **optimal value** of the trust-region
subproblem (8.1.2):
$$m_\Delta = \inf \{ m(s) \mid \|s\|_M \le \Delta \}.$$

The infimum is `sInf` of Mathlib, which is $0$ for the empty set, so $m_\Delta = 0$ for
$\Delta < 0$. For $\Delta \ge 0$ the infimum is attained
(`CartisGouldToint.Chapter09.exists_trValue_eq`).

**Reading.** Uses an attained infimum on nonnegative-radius balls and totalized zero when the ball
is empty.
-/
noncomputable def trValue (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (Δ : ℝ) : ℝ :=
  sInf (model g H '' {s | mNorm M s ≤ Δ})

/-- The optimal value $m_\Delta$ equals the optimal value `Subproblem.trustRegionValue` of the
operator subproblem for the scaled gradient $M^{-1} g$ and the scaled operator $M^{-1} H$ on the
$M$-inner product space. -/
theorem trValue_eq (hM : M.PosDef) (Δ : ℝ) :
    trValue g H M Δ = trustRegionValue (scaledGrad hM g) (scaledOp H hM) Δ := by
  rw [trValue, trustRegionValue]
  congr 1
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨toScaled hM s, by rwa [mem_closedBall_zero_iff, ← mNorm_eq_norm_toScaled hM],
      (model_eq_quadModel hM s).symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, rfl⟩ := (toScaled hM).surjective x
    exact ⟨s, by rwa [mem_ofPred_eq, mNorm_eq_norm_toScaled hM, ← mem_closedBall_zero_iff],
      model_eq_quadModel hM s⟩

/-- **Section 9.4.2** of [cartis2022evaluation], attainment of the optimal value. Let $M$ be
symmetric positive definite and $\Delta \ge 0$. Then some global minimizer $s$ of the
trust-region subproblem (8.1.2) has $m(s) = m_\Delta$.

The matrix $H$ need not be symmetric. -/
theorem exists_trValue_eq (hM : M.PosDef) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ∃ s, IsTrustRegionSolution g H M Δ s ∧ model g H s = trValue g H M Δ := by
  obtain ⟨x, hx, hmin⟩ := exists_isMinOn_closedBall (scaledGrad hM g) (scaledOp H hM) hΔ
  obtain ⟨s, rfl⟩ := (toScaled hM).surjective x
  refine ⟨s, (isTrustRegionSolution_iff_scaled hM).2 ⟨hx, hmin⟩, ?_⟩
  rw [trValue_eq hM, hmin.trustRegionValue_eq hx, model_eq_quadModel hM]

/-- **Equation (9.4.5)** of [cartis2022evaluation]. Let $M$ be symmetric positive definite and
$0 \le \Delta_1 \le \Delta_2$. Then $m_{\Delta_2} \le m_{\Delta_1}$.

**Correction.** The source claims $m_{\Delta_2} \le m_{\Delta_1}$ if and only if
$\Delta_2 \ge \Delta_1$. Only the implication holds: for $g = 0$ and $H = 0$, $m_\Delta = 0$ for
all $\Delta$.

The matrix $H$ need not be symmetric. -/
theorem trValue_antitone (hM : M.PosDef) {Δ₁ Δ₂ : ℝ} (h₁ : 0 ≤ Δ₁) (h : Δ₁ ≤ Δ₂) :
    trValue g H M Δ₂ ≤ trValue g H M Δ₁ := by
  rw [trValue_eq hM, trValue_eq hM]; exact trustRegionValue_antitone h₁ h

/-- **Equation (9.4.7)** of [cartis2022evaluation]. Let $M$ be symmetric positive definite,
$0 \le \Delta^- \le \Delta$ and $\|s^-\|_M = \Delta^-$. Then
$$m_\Delta \le \min\bigl(m((\Delta/\Delta^-) s^-), m_{\Delta^-}\bigr).$$

**Generalization.** The source takes $s^-$ to be a minimizer for the radius $\Delta^-$. The
bound holds for any $s^-$ on the sphere of radius $\Delta^-$, and for $\Delta^- \le \Delta$.

The matrix $H$ need not be symmetric. For $\Delta^- = 0$ the scale factor $\Delta/\Delta^-$ is
$0$, by division by zero. -/
theorem trValue_le_min (hM : M.PosDef) {Δ Δm : ℝ} {sm : EuclideanSpace ℝ (Fin n)}
    (hΔm : 0 ≤ Δm) (h : Δm ≤ Δ) (hsm : mNorm M sm = Δm) :
    trValue g H M Δ ≤ min (model g H ((Δ / Δm) • sm)) (trValue g H M Δm) := by
  have hn : ‖toScaled hM sm‖ = Δm := by rw [← mNorm_eq_norm_toScaled hM]; exact hsm
  have := trustRegionValue_le_min (g := scaledGrad hM g) (H := scaledOp H hM) hΔm h hn
  rwa [← trValue_eq hM, ← trValue_eq hM, ← map_smul, ← model_eq_quadModel hM] at this

/-- **Equations (9.4.5)–(9.4.7)** of [cartis2022evaluation], bounds on the optimal value of the
trust-region subproblem. Let $H$ be symmetric and $M$ symmetric positive definite. Then:

* for $\Delta \ge 0$, the value $m_\Delta$ is attained by a global minimizer of (8.1.2), and
  $m_\Delta \le 0$;
* (9.4.5) for $0 \le \Delta_1 \le \Delta_2$, $m_{\Delta_2} \le m_{\Delta_1}$;
* (9.4.6) for $0 \le \Delta \le \Delta^+$ and $\|s^+\|_M = \Delta^+$, $m_{\Delta^+} \le m_\Delta
  \le m((\Delta/\Delta^+) s^+)$;
* (9.4.7) for $0 \le \Delta^- \le \Delta$ and $\|s^-\|_M = \Delta^-$, $m_\Delta \le
  \min(m((\Delta/\Delta^-) s^-), m_{\Delta^-})$;
* for $\lambda > \lambda_s$ (that is, $\lambda \in \mathcal{L} \cup \mathcal{G}$) and
  $\Delta(\lambda) = \|s(\lambda)\|_M$,
$$m_{\Delta(\lambda)} = \tfrac12 \bigl(\langle g, s(\lambda) \rangle - \lambda
  \Delta(\lambda)^2\bigr).$$

**Correction.** The source states (9.4.5) as an equivalence. Its converse is false (see
`CartisGouldToint.Chapter09.trValue_antitone`).

**Generalization.** The source takes $s^+$ and $s^-$ to be minimizers for the radii $\Delta^+$
and $\Delta^-$. The bounds (9.4.6) and (9.4.7) hold for any points on these spheres, and for
$\Delta \le \Delta^+$ and $\Delta^- \le \Delta$. At zero denominator, the rescaling gives
the zero vector. -/
theorem optimalValue_bounds_9_4_6 (hH : H.IsHermitian) (hM : M.PosDef) :
    (∀ Δ : ℝ, 0 ≤ Δ → (∃ s, IsTrustRegionSolution g H M Δ s ∧ model g H s = trValue g H M Δ) ∧
      trValue g H M Δ ≤ 0) ∧
    (∀ Δ₁ Δ₂ : ℝ, 0 ≤ Δ₁ → Δ₁ ≤ Δ₂ → trValue g H M Δ₂ ≤ trValue g H M Δ₁) ∧
    (∀ (Δ Δp : ℝ) (sp : EuclideanSpace ℝ (Fin n)), 0 ≤ Δ → Δ ≤ Δp → mNorm M sp = Δp →
      trValue g H M Δp ≤ trValue g H M Δ ∧ trValue g H M Δ ≤ model g H ((Δ / Δp) • sp)) ∧
    (∀ (Δ Δm : ℝ) (sm : EuclideanSpace ℝ (Fin n)), 0 ≤ Δm → Δm ≤ Δ → mNorm M sm = Δm →
      trValue g H M Δ ≤ min (model g H ((Δ / Δm) • sm)) (trValue g H M Δm)) ∧
    (∀ lam, lambdaS hH hM < lam →
      trValue g H M (mNorm M (stepOf g H M lam)) =
        1 / 2 * (⟪g, stepOf g H M lam⟫ - lam * mNorm M (stepOf g H M lam) ^ 2)) := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hmodel : ∀ (c : ℝ) (v : EuclideanSpace ℝ (Fin n)),
      quadModel (scaledGrad hM g) (scaledOp H hM) (c • toScaled hM v) = model g H (c • v) :=
    fun c v => by rw [← map_smul, model_eq_quadModel hM]
  refine ⟨fun Δ hΔ => ⟨?_, ?_⟩, fun Δ₁ Δ₂ h₁ h => ?_, fun Δ Δp sp hΔ h hsp => ?_,
    fun Δ Δm sm hΔm h hsm => ?_, fun lam hlam => ?_⟩
  · exact exists_trValue_eq hM hΔ
  · rw [trValue_eq hM]
    exact (trustRegionValue_le (by simpa using hΔ)).trans_eq (quadModel_zero _ _)
  · exact trValue_antitone hM h₁ h
  · have hn : ‖toScaled hM sp‖ = Δp := by rw [← mNorm_eq_norm_toScaled hM]; exact hsp
    have := trustRegionValue_mem_Icc (g := scaledGrad hM g) (H := scaledOp H hM) hΔ h hn
    rw [trValue_eq hM, trValue_eq hM, ← hmodel]
    exact this
  · exact trValue_le_min hM hΔm h hsm
  · have hl := neg_leftmost_lt_of_lambdaS_lt hH hM hlam
    have hl0 : 0 ≤ lam := (lambdaS_nonneg hH hM).trans hlam.le
    have hsh := add_smul_stepOf (g := g) hH hM hl
    have hsh' := (add_smul_scaledOp_toScaled_eq_neg_iff (hM := hM) lam g _).2 hsh
    have hμ : IsTrustRegionMultiplier (scaledGrad hM g) (scaledOp H hM)
        (mNorm M (stepOf g H M lam)) (toScaled hM (stepOf g H M lam)) lam :=
      ⟨hl0, hsh', isPositive_add_smul_of_le (hH := hT) hl.le,
        by rw [mNorm_eq_norm_toScaled hM, sub_self, mul_zero]⟩
    have hn : ‖toScaled hM (stepOf g H M lam)‖ ≤ mNorm M (stepOf g H M lam) :=
      (mNorm_eq_norm_toScaled hM _).ge
    rw [trValue_eq hM, (hμ.isMinOn hT).trustRegionValue_eq hn, quadModel_eq_of_shifted hsh',
      inner_scaledGrad_toScaled, ← mNorm_eq_norm_toScaled hM]

/-! ### Early termination: the tests (9.4.2)–(9.4.4) -/

/-- **Section 9.4.2** of [cartis2022evaluation], after (9.4.5), the interior case. Let $M$ be
symmetric positive definite and $H$ positive definite, and suppose that
$\|H^{-1} g\|_M \le \Delta$. Then $s_\Delta = -H^{-1} g$ is a global minimizer of the
trust-region subproblem (8.1.2), it is the only one, and
$$m_\Delta = -\tfrac12 \langle g, H^{-1} g \rangle.$$

**Correction.** The source goes on to claim boundary attainment by $s_\Delta$ in all other
cases. A singular positive semidefinite model can have interior minimizers. For example,
$H=0$, $g=0$ and $\Delta>0$ admit $s_\Delta=0$.
-/
theorem trValue_of_posDef (hM : M.PosDef) (hpos : H.PosDef) {Δ : ℝ}
    (hs : mNorm M (toEuclideanLin H⁻¹ g) ≤ Δ) :
    IsTrustRegionSolution g H M Δ (-toEuclideanLin H⁻¹ g) ∧
      (∀ u, IsTrustRegionSolution g H M Δ u → u = -toEuclideanLin H⁻¹ g) ∧
      trValue g H M Δ = -(1 / 2) * ⟪g, toEuclideanLin H⁻¹ g⟫ := by
  have hH : H.IsHermitian := hpos.isHermitian
  have hT := isSymmetric_scaledOp (hM := hM) hH
  set s := -toEuclideanLin H⁻¹ g
  have hstep : stepOf g H M 0 = s := by rw [stepOf_def, zero_smul, add_zero, map_neg]
  have hns : ‖toScaled hM s‖ ≤ Δ := by
    rw [← mNorm_eq_norm_toScaled hM]
    simpa [s, mNorm, inner_neg_left, inner_neg_right] using hs
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · have hΔ : 0 ≤ Δ := (mNorm_nonneg _ _).trans hs
    have hsol : ∀ u, IsTrustRegionSolution g H M Δ u := fun u =>
      ⟨by rw [Subsingleton.elim u 0, mNorm_zero]; exact hΔ,
        fun v _ => by rw [Subsingleton.elim u v]⟩
    refine ⟨hsol _, fun u _ => Subsingleton.elim _ _, ?_⟩
    obtain ⟨v, hv, hval⟩ := exists_trValue_eq (g := g) (H := H) hM hΔ
    rw [← hval, Subsingleton.elim v 0, Subsingleton.elim g 0]
    simp [model_def]
  · have hc := (posDef_add_smul_iff_isSymmetricCoercive (hM := hM) 0).1 (by simpa using hpos)
    have hl : -leftmost hT < 0 := (isSymmetricCoercive_add_smul_iff (hH := hT) 0).1 hc
    have hsh := add_smul_stepOf (g := g) hH hM hl
    have hsh' := (add_smul_scaledOp_toScaled_eq_neg_iff (hM := hM) 0 g _).2 hsh
    rw [hstep] at hsh'
    have hμ : IsTrustRegionMultiplier (scaledGrad hM g) (scaledOp H hM) Δ (toScaled hM s) 0 :=
      ⟨le_rfl, hsh', isPositive_add_smul_of_le (hH := hT) hl.le, zero_mul _⟩
    have hmin := hμ.isMinOn hT
    have hsol : IsTrustRegionSolution g H M Δ s :=
      (isTrustRegionSolution_iff_scaled hM).2 ⟨hns, hmin⟩
    refine ⟨hsol, fun u hu => ?_, ?_⟩
    · obtain ⟨hu1, hu2⟩ := (isTrustRegionSolution_iff_scaled hM).1 hu
      exact (toScaled hM).injective
        (eq_of_isMinOn_closedBall_of_posDef hT hμ hns hc.isCoercive hu1 hu2)
    · rw [trValue_eq hM, hmin.trustRegionValue_eq hns, quadModel_eq_of_shifted hsh',
        inner_scaledGrad_toScaled, zero_mul, sub_zero, inner_neg_right]
      ring

/-- **Section 9.4.2** of [cartis2022evaluation], before (9.4.2), the measure $\phi^\Delta_{f,2}$ as
an optimal value. Let $f : \mathbb{R}^n \to \mathbb{R}$ and $x \in \mathbb{R}^n$, and suppose
that the second-order Taylor polynomial of $f$ at $x$ is $T_{f,2}(x, s) = f(x) + m(s)$ for all
$s$. Then for every $\Delta$,
$$\phi^\Delta_{f,2}(x) = f(x) - \min_{\|s\| \le \Delta} T_{f,2}(x, s) = -m_\Delta,$$
where $m_\Delta$ is taken with $M = I$.

The derivative data $g=\nabla f(x)$ and $H=\nabla^2 f(x)$ satisfy the polynomial
hypothesis for a $C^2$ function. The identity also holds for any data yielding the same
polynomial and uses the totalized ball values when $\Delta<0$. The measure is
`Optimization.taylorMeasure`.

**Reading.** Uses a polynomial equality hypothesis and admits any model satisfying it; negative
radii use the totalized empty value.
-/
theorem taylorMeasure_two_eq_neg_trValue {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hT : ∀ s, taylorPolynomial f 2 x s = f x + model g H s)
    (Δ : ℝ) :
    Optimization.taylorMeasure (ftaylorSeries ℝ f x) 2 Δ univ = -trValue g H 1 Δ := by
  rw [Optimization.taylorMeasure_eq_sSup, inter_univ, trValue, ← Real.sSup_neg]
  congr 1
  ext y
  simp only [mem_image, mem_neg, mem_closedBall_zero_iff, mem_ofPred_eq, mNorm_one]
  refine exists_congr fun d => and_congr_right fun _ => ?_
  rw [ftaylorSeries_taylorDecrement_eq, hT]
  constructor <;> intro h <;> linarith

/-- **Equations (9.4.2)–(9.4.4)** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$
and $x \in \mathbb{R}^n$, and suppose that $T_{f,2}(x, s) = f(x) + m(s)$ for all $s$. Then for
all $\Delta, \phi^L, \phi^U \in \mathbb{R}$, with $m_\Delta$ taken for $M = I$,
$$\phi^\Delta_{f,2}(x) \ge \phi^U \iff m_\Delta \le -\phi^U, \qquad \phi^\Delta_{f,2}(x) \le
  \phi^L \iff m_\Delta \ge -\phi^L.$$
So the tests (9.4.2) are the tests (9.4.3)–(9.4.4) with $m^L = -\phi^U$ and $m^U = -\phi^L$.
The equivalences extend the source's positive $\phi^L,\phi^U$ to arbitrary thresholds and
use the totalized ball values when $\Delta<0$.

**Reading.** Both signs and threshold reversals agree; takes arbitrary thresholds and totalized
radii.
-/
theorem test_9_4_2_iff {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hT : ∀ s, taylorPolynomial f 2 x s = f x + model g H s) (Δ φL φU : ℝ) :
    (φU ≤ Optimization.taylorMeasure (ftaylorSeries ℝ f x) 2 Δ univ ↔
        trValue g H 1 Δ ≤ -φU) ∧
      (Optimization.taylorMeasure (ftaylorSeries ℝ f x) 2 Δ univ ≤ φL ↔
        -φL ≤ trValue g H 1 Δ) := by
  rw [taylorMeasure_two_eq_neg_trValue hT]
  exact ⟨le_neg, neg_le⟩

/-- Let $f : \mathbb{R}^n \to \mathbb{R}$ be twice continuously differentiable near $x$. Then
$T_{f,2}(x, s) = f(x) + m(s)$ for all $s$, where $m$ is the model (8.1.1) with $g = \nabla f(x)$
and $H = \nabla^2 f(x)$.

The Hessian matrix is `Optimization.hessianMatrix f x`, and the hypothesis on $f$ is
`ContDiffAt ℝ 2 f x`. -/
theorem taylorPolynomial_two_eq_model {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hf : ContDiffAt ℝ 2 f x) (s : EuclideanSpace ℝ (Fin n)) :
    taylorPolynomial f 2 x s =
      f x + model (gradient f x) (Optimization.hessianMatrix f x) s := by
  rw [Optimization.taylorPolynomial_two_eq_quadModel hf, quadModel_def, model_def,
    Optimization.toEuclideanLin_hessianMatrix hf]
  rfl

/-- **Section 9.4.2** of [cartis2022evaluation], before (9.4.2), the measure $\phi^\Delta_{f,2}$ as
an optimal value. Let $f : \mathbb{R}^n \to \mathbb{R}$ be twice continuously differentiable
near $x$. Then for every $\Delta$,
$$\phi^\Delta_{f,2}(x) = -\min_{\|s\| \le \Delta} m(s),$$
where $m$ is the model (8.1.1) with $g = \nabla f(x)$, $H = \nabla^2 f(x)$ and $M = I$.

The hypothesis on $f$ is `ContDiffAt ℝ 2 f x`. The identity extends to $\Delta<0$ using the
totalized values of the empty ball.

**Generalization.** Exact negative optimal value for nonnegative radius; extends the identity by
empty-ball totalization.
-/
theorem taylorMeasure_two_eq_neg_trValue_of_contDiffAt {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hf : ContDiffAt ℝ 2 f x) (Δ : ℝ) :
    Optimization.taylorMeasure (ftaylorSeries ℝ f x) 2 Δ univ =
      -trValue (gradient f x) (Optimization.hessianMatrix f x) 1 Δ :=
  taylorMeasure_two_eq_neg_trValue (taylorPolynomial_two_eq_model hf) Δ

/-- **Equations (9.4.2)–(9.4.4)** of [cartis2022evaluation], in the form of the source. Let
$f : \mathbb{R}^n \to \mathbb{R}$ be twice continuously differentiable near $x$, and let
$m_\Delta$ be the optimal value for $g = \nabla f(x)$, $H = \nabla^2 f(x)$ and $M = I$. Then for
all $\Delta, \phi^L, \phi^U \in \mathbb{R}$,
$$\phi^\Delta_{f,2}(x) \ge \phi^U \iff m_\Delta \le -\phi^U, \qquad \phi^\Delta_{f,2}(x) \le
  \phi^L \iff m_\Delta \ge -\phi^L.$$

**Generalization.** The source takes positive thresholds. The equivalence also holds for
arbitrary thresholds and extends to $\Delta<0$ using the totalized ball values.
-/
theorem test_9_4_2_iff_of_contDiffAt {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hf : ContDiffAt ℝ 2 f x) (Δ φL φU : ℝ) :
    (φU ≤ Optimization.taylorMeasure (ftaylorSeries ℝ f x) 2 Δ univ ↔
        trValue (gradient f x) (Optimization.hessianMatrix f x) 1 Δ ≤ -φU) ∧
      (Optimization.taylorMeasure (ftaylorSeries ℝ f x) 2 Δ univ ≤ φL ↔
        -φL ≤ trValue (gradient f x) (Optimization.hessianMatrix f x) 1 Δ) :=
  test_9_4_2_iff (taylorPolynomial_two_eq_model hf) Δ φL φU

/-- **Section 9.4.2** of [cartis2022evaluation], the scaled point is feasible. Let $M$ be symmetric
positive definite, $\Delta \ge 0$, $\Delta^+ \ge 0$ and $\|s^+\|_M = \Delta^+$. Then
$\|(\Delta/\Delta^+) s^+\|_M \le \Delta$.

The theorem states only the inequality; equality holds when $\Delta^+ > 0$. For $\Delta^+ = 0$
the scale factor $\Delta/\Delta^+$ is $0$, by division by zero.

**Generalization.** Gives a feasible point and extends the formula to a zero sphere radius, where
the scale is totalized.
-/
theorem mNorm_div_smul_le (hM : M.PosDef) {Δ Δ' : ℝ} (hΔ : 0 ≤ Δ) (hΔ' : 0 ≤ Δ')
    {s : EuclideanSpace ℝ (Fin n)} (hs : mNorm M s = Δ') : mNorm M ((Δ / Δ') • s) ≤ Δ := by
  rw [mNorm_eq_norm_toScaled hM, map_smul, norm_smul, ← mNorm_eq_norm_toScaled hM, hs,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg hΔ hΔ')]
  rcases hΔ'.eq_or_lt with rfl | hpos
  · simpa using hΔ
  · rw [div_mul_cancel₀ _ hpos.ne']

/-- **Section 9.4.2** of [cartis2022evaluation], test (9.4.3) from (9.4.6). Let $M$ be symmetric
positive definite, $0 \le \Delta \le \Delta^+$ and $\|s^+\|_M = \Delta^+$, and let
$\alpha^+ = \Delta/\Delta^+$. If $m(\alpha^+ s^+) \le m^L$, then $m_\Delta \le m^L$, and
$\alpha^+ s^+$ is a feasible exemplar: $\|\alpha^+ s^+\|_M \le \Delta$ and
$m(\alpha^+ s^+) \le m^L$.

**Reading.** Retains upper-value test and feasible exemplar, allowing a nonoptimal sphere point and
equal radii.
-/
theorem test_9_4_3_of_9_4_6 (hM : M.PosDef) {Δ Δp mL : ℝ} {sp : EuclideanSpace ℝ (Fin n)}
    (hΔ : 0 ≤ Δ) (h : Δ ≤ Δp) (hsp : mNorm M sp = Δp) (hL : model g H ((Δ / Δp) • sp) ≤ mL) :
    trValue g H M Δ ≤ mL ∧ mNorm M ((Δ / Δp) • sp) ≤ Δ := by
  have hn : ‖toScaled hM sp‖ = Δp := by rw [← mNorm_eq_norm_toScaled hM]; exact hsp
  have := (trustRegionValue_mem_Icc (g := scaledGrad hM g) (H := scaledOp H hM) hΔ h hn).2
  rw [← trValue_eq hM, ← map_smul, ← model_eq_quadModel hM] at this
  exact ⟨this.trans hL, mNorm_div_smul_le hM hΔ (hΔ.trans h) hsp⟩

/-- **Section 9.4.2** of [cartis2022evaluation], test (9.4.4) from (9.4.6). Let $M$ be symmetric
positive definite and $0 \le \Delta \le \Delta^+$. If $m_{\Delta^+} \ge m^U$, then
$m_\Delta \ge m^U$.

**Reading.** Retains the lower-value test and allows equal radii and unrestricted thresholds.
-/
theorem test_9_4_4_of_9_4_6 (hM : M.PosDef) {Δ Δp mU : ℝ} (hΔ : 0 ≤ Δ) (h : Δ ≤ Δp)
    (hU : mU ≤ trValue g H M Δp) : mU ≤ trValue g H M Δ :=
  hU.trans (trValue_antitone hM hΔ h)

/-- **Section 9.4.2** of [cartis2022evaluation], test (9.4.3) from (9.4.7). Let $M$ be symmetric
positive definite, $0 \le \Delta^- \le \Delta$ and $\|s^-\|_M = \Delta^-$, and let
$\alpha^- = \Delta/\Delta^-$. If $\min(m(\alpha^- s^-), m_{\Delta^-}) \le m^L$, then
$m_\Delta \le m^L$, and there is a feasible exemplar $s$ with $\|s\|_M \le \Delta$ and
$m(s) \le m^L$.

The exemplar is $\alpha^- s^-$ or a minimizer for the radius $\Delta^-$.

**Reading.** Retains lower-radius model test and gives a witness for either branch; admits arbitrary
points on the sphere and equal radii.
-/
theorem test_9_4_3_of_9_4_7 (hM : M.PosDef) {Δ Δm mL : ℝ}
    {sm : EuclideanSpace ℝ (Fin n)} (hΔm : 0 ≤ Δm) (h : Δm ≤ Δ) (hsm : mNorm M sm = Δm)
    (hL : min (model g H ((Δ / Δm) • sm)) (trValue g H M Δm) ≤ mL) :
    trValue g H M Δ ≤ mL ∧ ∃ s, mNorm M s ≤ Δ ∧ model g H s ≤ mL := by
  refine ⟨(trValue_le_min hM hΔm h hsm).trans hL, ?_⟩
  rcases min_le_iff.1 hL with h1 | h2
  · exact ⟨_, mNorm_div_smul_le hM (hΔm.trans h) hΔm hsm, h1⟩
  · obtain ⟨s, hs, hval⟩ := exists_trValue_eq (g := g) (H := H) hM hΔm
    exact ⟨s, hs.1.trans h, hval ▸ h2⟩

/-- **Section 9.4.2** of [cartis2022evaluation], after (9.4.7), the tests from
$\lambda^+ \in \mathcal{L}$. Let $H$ be symmetric, $M$ symmetric positive definite,
$\Delta \ge 0$, and let $\lambda^+$ lie in the trust-region set $\mathcal{L}$ for $\Delta$. Let
$\Delta^+ = \|s(\lambda^+)\|_M$, so that $\Delta^+ \ge \Delta$, and
$\alpha^+ = \Delta/\Delta^+$. Then:

* if $m(\alpha^+ s(\lambda^+)) \le m^L$, then $m_\Delta \le m^L$, and there is $s$ with
  $\|s\|_M \le \Delta$ and $m(s) \le m^L$;
* if $\frac12 (\langle g, s(\lambda^+) \rangle - \lambda^+ (\Delta^+)^2) \ge m^U$, then
  $m_\Delta \ge m^U$.

The radius $\Delta^+$ is suitable for (9.4.6), with the computable value $m_{\Delta^+} = \frac12
(\langle g, s(\lambda^+) \rangle - \lambda^+ (\Delta^+)^2)$. In the first case,
$\alpha^+ s(\lambda^+)$ is a feasible exemplar.

**Correction.** The source gives $\Delta^+>\Delta$ for $\lambda^+\in\mathcal{L}$. Equality
is possible at the secular root, and the tests use $\Delta^+\ge\Delta$. -/
theorem tests_9_4_3_9_4_4_of_setL (hH : H.IsHermitian) (hM : M.PosDef) {Δ lam mL mU : ℝ}
    (hΔ : 0 ≤ Δ) (hlam : lam ∈ setL_tr hH hM g Δ) :
    (model g H ((Δ / mNorm M (stepOf g H M lam)) • stepOf g H M lam) ≤ mL →
        trValue g H M Δ ≤ mL ∧ ∃ s, mNorm M s ≤ Δ ∧ model g H s ≤ mL) ∧
      (mU ≤ 1 / 2 * (⟪g, stepOf g H M lam⟫ - lam * mNorm M (stepOf g H M lam) ^ 2) →
        mU ≤ trValue g H M Δ) := by
  have hval := (optimalValue_bounds_9_4_6 (g := g) hH hM).2.2.2.2 lam hlam.1
  refine ⟨fun hL => ?_, fun hU => test_9_4_4_of_9_4_6 hM hΔ hlam.2 (hval ▸ hU)⟩
  obtain ⟨h1, h2⟩ := test_9_4_3_of_9_4_6 hM hΔ hlam.2 rfl hL
  exact ⟨h1, _, h2, hL⟩

/-- **Section 9.4.2** of [cartis2022evaluation], after (9.4.7), test (9.4.3) from
$\lambda^- \in \mathcal{G}$. Let $H$ be symmetric, $M$ symmetric positive definite, and let
$\lambda^-$ lie in the trust-region set $\mathcal{G}$ for $\Delta$. Let
$\Delta^- = \|s(\lambda^-)\|_M$, so that $\Delta^- < \Delta$, and $\alpha^- = \Delta/\Delta^-$.
If
$$\min\Bigl(m(\alpha^- s(\lambda^-)), \tfrac12 \bigl(\langle g, s(\lambda^-) \rangle - \lambda^-
  (\Delta^-)^2\bigr)\Bigr) \le m^L,$$
then $m_\Delta \le m^L$, and there is $s$ with $\|s\|_M \le \Delta$ and $m(s) \le m^L$.

The radius $\Delta^-$ is suitable for (9.4.7), with the computable value $m_{\Delta^-}$.
The source gives $\Delta^-\le\Delta$. Membership in $\mathcal{G}$ gives the strict inequality.
For $\Delta^-=0$, the scaled step is $0$.

**Reading.** Uses strict smaller radius implied by G, preserves the value test and witness, and
totalizes scaling at zero radius.
-/
theorem test_9_4_3_of_setG (hH : H.IsHermitian) (hM : M.PosDef) {Δ lam mL : ℝ}
    (hlam : lam ∈ setG_tr hH hM g Δ)
    (hL : min (model g H ((Δ / mNorm M (stepOf g H M lam)) • stepOf g H M lam))
      (1 / 2 * (⟪g, stepOf g H M lam⟫ - lam * mNorm M (stepOf g H M lam) ^ 2)) ≤ mL) :
    trValue g H M Δ ≤ mL ∧ ∃ s, mNorm M s ≤ Δ ∧ model g H s ≤ mL := by
  have hval := (optimalValue_bounds_9_4_6 (g := g) hH hM).2.2.2.2 lam hlam.1
  exact test_9_4_3_of_9_4_7 hM (mNorm_nonneg _ _) hlam.2.le rfl (hval ▸ hL)

/-- **Footnote 65** of [cartis2022evaluation]. Let $H$ be symmetric, $M$ symmetric positive
definite, and let $\lambda$ lie in the trust-region set $\mathcal{G}$ for $\Delta$. Then, with
$\Delta(\lambda) = \|s(\lambda)\|_M$,
$$m_{\Delta(\lambda)} \ge \tfrac12 \bigl(\langle g, s(\lambda) \rangle - \lambda
  \Delta^2\bigr).$$

The proof uses $m_{\Delta(\lambda)} = \frac12 (\langle g, s(\lambda) \rangle - \lambda
\Delta(\lambda)^2)$ and $\Delta(\lambda) < \Delta$. -/
theorem trValue_ge_of_setG (hH : H.IsHermitian) (hM : M.PosDef) {Δ lam : ℝ}
    (hlam : lam ∈ setG_tr hH hM g Δ) :
    1 / 2 * (⟪g, stepOf g H M lam⟫ - lam * Δ ^ 2) ≤
      trValue g H M (mNorm M (stepOf g H M lam)) := by
  rw [(optimalValue_bounds_9_4_6 (g := g) hH hM).2.2.2.2 lam hlam.1]
  have hl0 : 0 ≤ lam := (lambdaS_nonneg hH hM).trans hlam.1.le
  have h0 := mNorm_nonneg M (stepOf g H M lam)
  have : mNorm M (stepOf g H M lam) ^ 2 ≤ Δ ^ 2 := pow_le_pow_left₀ h0 hlam.2.le 2
  nlinarith

end CartisGouldToint.Chapter09
