/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Nonlinear.Newton
import Mathlib.Topology.ClusterPt
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Sequences and basic iterations

Section 3.3.1 of [conn2000trust] measures convergence rates by comparing errors to the limit.
The displayed Q-rate criteria on pp. 50–51 have an indexing error: the left-hand side must
be the error at the successor index, `‖u (k + 1) - x‖`. The reciprocal sequence below satisfies
the printed quadratic inequality despite failing the corrected one.
The Newton–Kantorovich statement makes the required containment of a closed ball in
the differentiability domain explicit.
-/

open Filter Topology Asymptotics

namespace ConnGouldToint.Chapter03

variable {E : Type*} [NormedAddCommGroup E]

/-- Q-linear convergence, with the successor error bounded by a fixed strict contraction
factor times the current error. -/
def ConvergesQLinearly (u : ℕ → E) (x : E) : Prop :=
  Tendsto u atTop (𝓝 x) ∧ ∃ q ∈ Set.Ico (0 : ℝ) 1,
    ∀ᶠ k in atTop, ‖u (k + 1) - x‖ ≤ q * ‖u k - x‖

/-- Q-superlinear convergence, with the successor error little-o of the current error. -/
def ConvergesQSuperlinearly (u : ℕ → E) (x : E) : Prop :=
  Tendsto u atTop (𝓝 x) ∧ (fun k => u (k + 1) - x) =o[atTop] fun k => u k - x

/-- Q-quadratic convergence, with the successor error bounded by a fixed multiple of
the squared current error. -/
def ConvergesQQuadratically (u : ℕ → E) (x : E) : Prop :=
  Tendsto u atTop (𝓝 x) ∧ ∃ C : ℝ, ∀ᶠ k in atTop, ‖u (k + 1) - x‖ ≤ C * ‖u k - x‖ ^ 2

/-- R-quadratic convergence, with the error dominated by a Q-quadratically convergent
sequence of nonnegative real numbers. -/
def ConvergesRQuadratically (u : ℕ → E) (x : E) : Prop :=
  ∃ w : ℕ → ℝ, ConvergesQQuadratically w 0 ∧ ∀ k, ‖u k - x‖ ≤ w k

/-- The sequence `1 / (k + 1)` converges to zero and satisfies the printed Q-quadratic
inequality with constant one, although its convergence fails the corrected Q-quadratic test. -/
theorem reciprocal_succ_counterexample :
    let u : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
    Tendsto u atTop (𝓝 0) ∧ (∀ k, ‖u (k + 1) - u k‖ ≤ ‖u k‖ ^ 2) ∧
      ¬ ConvergesQQuadratically u 0 := by
  dsimp only
  refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_, ?_⟩
  · intro k
    push_cast
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hmono : 1 / ((k : ℝ) + 1 + 1) ≤ 1 / ((k : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.2 hmono),
      Real.norm_of_nonneg (by positivity)]
    have hcalc : -(1 / ((k : ℝ) + 1 + 1) - 1 / ((k : ℝ) + 1)) =
        1 / (((k : ℝ) + 1 + 1) * ((k : ℝ) + 1)) := by
      field_simp; ring
    rw [hcalc, div_pow, one_pow]
    gcongr; linarith
  · rintro ⟨-, C, hC⟩
    rw [eventually_atTop] at hC
    obtain ⟨N, hN⟩ := hC
    obtain ⟨m, hm⟩ := exists_nat_gt (2 * C)
    let k := max N m
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h := hN k (le_max_left _ _)
    have hm' : (m : ℝ) ≤ k := by exact_mod_cast le_max_right N m
    simp only [sub_zero, Nat.cast_add, Nat.cast_one] at h
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), div_pow,
      one_pow, mul_one_div] at h
    have h' := (div_le_div_iff₀ (by positivity : (0 : ℝ) < k + 1 + 1)
      (by positivity : (0 : ℝ) < ((k : ℝ) + 1) ^ 2)).mp h
    have hC₀ : 0 ≤ C := by
      by_contra! hneg
      nlinarith [mul_neg_of_neg_of_pos hneg (by positivity : (0 : ℝ) < k + 1 + 1)]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ k + 1 by positivity)
      (show (0 : ℝ) ≤ k + 1 - 2 * C by linarith), mul_nonneg hC₀ hk]

section Newton

variable {F : Type*} [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [CompleteSpace E] in
/-- Algorithm 3.3.1. Where the derivative is invertible, the Newton
iterate uses the unique solution of (3.3.1). -/
theorem algorithm_3_3_1 (f : E → F) (x₀ : E) (k : ℕ)
    (e : E ≃L[ℝ] F)
    (he : HasFDerivAt f (e : E →L[ℝ] F) (Newton.iterate f (fderiv ℝ f) x₀ k)) :
    let x := Newton.iterate f (fderiv ℝ f) x₀ k
    ∃! s, fderiv ℝ f x s = -f x ∧ Newton.iterate f (fderiv ℝ f) x₀ (k + 1) = x + s := by
  let x := Newton.iterate f (fderiv ℝ f) x₀ k
  refine ⟨e.symm (-f x), ⟨?_, ?_⟩, ?_⟩
  · rw [he.fderiv]
    exact e.apply_symm_apply _
  · rw [Newton.iterate_succ]
    change Newton.step f (fderiv ℝ f) x = x + e.symm (-f x)
    rw [Newton.step, he.fderiv, ContinuousLinearMap.inverse_equiv, map_neg, sub_eq_add_neg]
    rfl
  · intro s hs
    apply e.injective
    rw [e.apply_symm_apply]
    rw [he.fderiv] at hs
    exact hs.1

omit [CompleteSpace E] in
/-- Near a regular root, the norm of the residual and the distance to the root
bound one another up to constant factors. -/
private theorem eventually_residual_comparable {f : E → F} {x : E} (hroot : f x = 0)
    (e : E ≃L[ℝ] F) (he : HasFDerivAt f (e : E →L[ℝ] F) x) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ᶠ z in 𝓝 x, ‖f z‖ ≤ A * ‖z - x‖ ∧ ‖z - x‖ ≤ B * ‖f z‖ := by
  let K := ‖(e.symm : F →L[ℝ] E)‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  let ε := 1 / (2 * K)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hhalf : K * ε = 1 / 2 := by dsimp [ε]; field_simp
  refine ⟨‖(e : E →L[ℝ] F)‖ + ε, 2 * K, by positivity, by positivity, ?_⟩
  filter_upwards [he.isLittleO.bound hε] with z hz
  have hz' : ‖f z - e (z - x)‖ ≤ ε * ‖z - x‖ := by
    simpa [hroot] using hz
  have h1 : ‖f z‖ ≤ ‖e (z - x)‖ + ‖f z - e (z - x)‖ := by
    simpa using norm_add_le (e (z - x)) (f z - e (z - x))
  have h2 : ‖e (z - x)‖ ≤ ‖f z‖ + ‖f z - e (z - x)‖ := by
    simpa using norm_sub_le (f z) (f z - e (z - x))
  have h3 : ‖z - x‖ ≤ K * ‖e (z - x)‖ := by
    calc
      _ ≤ ‖(e.symm : F →L[ℝ] E)‖ * ‖e (z - x)‖ := by
        simpa using (e.symm : F →L[ℝ] E).le_opNorm (e (z - x))
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (norm_nonneg _)
  constructor
  · calc
      _ ≤ ‖e (z - x)‖ + ‖f z - e (z - x)‖ := h1
      _ ≤ ‖(e : E →L[ℝ] F)‖ * ‖z - x‖ + ε * ‖z - x‖ :=
        add_le_add ((e : E →L[ℝ] F).le_opNorm _) hz'
      _ = _ := (add_mul _ _ _).symm
  · have h4 : ‖z - x‖ ≤ K * ‖f z‖ + (1 / 2 : ℝ) * ‖z - x‖ := by
      calc
        _ ≤ K * ‖e (z - x)‖ := h3
        _ ≤ K * (‖f z‖ + ε * ‖z - x‖) :=
          mul_le_mul_of_nonneg_left (h2.trans (add_le_add_right hz' _)) hK.le
        _ = _ := by rw [mul_add, ← mul_assoc, hhalf]
    linarith

/-- **Theorem 3.3.1.** If a regular root is a cluster point of the Newton iterates,
both the iterates and their residuals converge Q-quadratically. -/
theorem theorem_3_3_1 {S : Set E} (hS : IsOpen S) {f : E → F} {x₀ x : E} (hx : x ∈ S)
    (hF : ∀ z ∈ S, DifferentiableAt ℝ f z) {L : ℝ}
    (hLip : ∀ z ∈ S, ∀ w ∈ S, ‖fderiv ℝ f z - fderiv ℝ f w‖ ≤ L * ‖z - w‖)
    (hroot : f x = 0) (e : E ≃L[ℝ] F) (he : (e : E →L[ℝ] F) = fderiv ℝ f x)
    (hcluster : MapClusterPt x atTop (Newton.iterate f (fderiv ℝ f) x₀)) :
    ConvergesQQuadratically (Newton.iterate f (fderiv ℝ f) x₀) x ∧
      ConvergesQQuadratically (fun k => f (Newton.iterate f (fderiv ℝ f) x₀ k)) 0 := by
  let u := Newton.iterate f (fderiv ℝ f) x₀
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hx)
  have hFd (z : E) (hz : z ∈ Metric.ball x r) := (hF z (hsub hz)).hasFDerivAt
  have hLd (z : E) (hz : z ∈ Metric.ball x r) (w : E) (hw : w ∈ Metric.ball x r) :=
    hLip z (hsub hz) w (hsub hw)
  obtain ⟨δ, hδ, hconv⟩ := Newton.tendsto_iterate hroot e he hr hFd hLd
  obtain ⟨k, hk⟩ := (hcluster.frequently (Metric.ball_mem_nhds x hδ)).exists
  have hu : Tendsto u atTop (𝓝 x) := by
    apply (tendsto_add_atTop_iff_nat k).mp
    have htail : (fun n => u (n + k)) = Newton.iterate f (fderiv ℝ f) (u k) := by
      funext n
      exact Function.iterate_add_apply _ n k x₀
    rw [htail]
    exact hconv (u k) hk
  obtain ⟨d, hd, C, hquad⟩ := Newton.exists_ball_norm_step_sub_le hroot e he hr hFd hLd
  have hq : ∀ᶠ k in atTop, ‖u (k + 1) - x‖ ≤ max C 0 * ‖u k - x‖ ^ 2 := by
    filter_upwards [hu.eventually (Metric.ball_mem_nhds x hd)] with k hk
    change ‖Newton.iterate f (fderiv ℝ f) x₀ (k + 1) - x‖ ≤ max C 0 * ‖u k - x‖ ^ 2
    rw [Newton.iterate_succ]
    exact (hquad (u k) hk).trans
      (mul_le_mul_of_nonneg_right (le_max_left C 0) (sq_nonneg _))
  refine ⟨⟨hu, max C 0, hq⟩, ?_⟩
  have hder : HasFDerivAt f (e : E →L[ℝ] F) x := by rw [he]; exact (hF x hx).hasFDerivAt
  have hres : Tendsto (fun k => f (u k)) atTop (𝓝 0) := hroot ▸ hder.continuousAt.tendsto.comp hu
  obtain ⟨A, B, hA, hB, hab⟩ := eventually_residual_comparable hroot e hder
  refine ⟨hres, A * max C 0 * B ^ 2, ?_⟩
  filter_upwards [hq, hu.eventually hab, (hu.comp (tendsto_add_atTop_nat 1)).eventually hab]
    with k hk hcurr hnext
  simp only [Function.comp_apply] at hnext
  simp only [sub_zero]
  calc
    _ ≤ A * ‖u (k + 1) - x‖ := hnext.1
    _ ≤ A * (max C 0 * ‖u k - x‖ ^ 2) := mul_le_mul_of_nonneg_left hk hA
    _ ≤ A * (max C 0 * (B * ‖f (u k)‖) ^ 2) := by gcongr; exact hcurr.2
    _ = _ := by ring

/-- **Theorem 3.3.2 (Newton–Kantorovich).** If the inverse at the start and the first Newton
correction have bounds `β` and `η`, the derivative has Lipschitz constant `L`, and
`β L η < 1/2`, the Newton iterates converge R-quadratically to a root. The closed ball
of the Kantorovich radius must be contained in the differentiability domain. -/
theorem theorem_3_3_2 {S : Set E} {f : E → F} {x₀ : E}
    (hF : ∀ z ∈ S, DifferentiableAt ℝ f z) {β L η : ℝ}
    (hβ : 0 < β) (hL : 0 < L) (hη : 0 ≤ η)
    (hLip : ∀ z ∈ S, ∀ w ∈ S, ‖fderiv ℝ f z - fderiv ℝ f w‖ ≤ L * ‖z - w‖)
    (e : E ≃L[ℝ] F) (he : (e : E →L[ℝ] F) = fderiv ℝ f x₀)
    (heβ : ‖(e.symm : F →L[ℝ] E)‖ ≤ β) (heη : ‖e.symm (f x₀)‖ ≤ η)
    (hh : β * L * η < 1 / 2)
    (hball : Metric.closedBall x₀ ((1 - Real.sqrt (1 - 2 * (β * L * η))) / (β * L)) ⊆ S) :
    ∃ x ∈ S, f x = 0 ∧ ConvergesRQuadratically (Newton.iterate f (fderiv ℝ f) x₀) x ∧
      ∀ k, Newton.iterate f (fderiv ℝ f) x₀ k ∈ S ∧
        ∃ ek : E ≃L[ℝ] F, (ek : E →L[ℝ] F) =
          fderiv ℝ f (Newton.iterate f (fderiv ℝ f) x₀ k) := by
  let a := 1 - Real.sqrt (1 - 2 * (β * L * η))
  let r := a / (β * L)
  have hFd (z : E) (hz : z ∈ Metric.closedBall x₀ r) := (hF z (hball hz)).hasFDerivAt
  have hLd (z : E) (hz : z ∈ Metric.closedBall x₀ r) (w : E) (hw : w ∈ Metric.closedBall x₀ r) :=
    hLip z (hball hz) w (hball hw)
  obtain ⟨x, hx, hroot, hconv, hstay, -⟩ :=
    Newton.kantorovich hβ hL hη e he heβ heη hFd hLd hh.le (le_refl r)
  refine ⟨x, hball hx, hroot, ?_, fun k => ⟨hball (hstay k), ?_⟩⟩
  · have ha₀ : 0 ≤ a := by
      dsimp [a]
      have h := Real.sq_sqrt (show 0 ≤ 1 - 2 * (β * L * η) by linarith)
      have h' := Real.sqrt_nonneg (1 - 2 * (β * L * η))
      nlinarith [show 0 ≤ β * L * η by positivity]
    have ha₁ : a < 1 := by
      dsimp [a]
      linarith [Real.sqrt_pos.2 (show 0 < 1 - 2 * (β * L * η) by linarith)]
    let w (k : ℕ) : ℝ := a ^ (2 ^ k) / (β * L)
    refine ⟨w, ⟨?_, β * L, ?_⟩, ?_⟩
    · have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one ha₀ ha₁).comp
        (tendsto_pow_atTop_atTop_of_one_lt (by decide : (1 : ℕ) < 2))
      simpa [w, Function.comp_def] using ht.div_const (β * L)
    · refine Eventually.of_forall fun k => ?_
      rw [sub_zero, sub_zero, Real.norm_of_nonneg (by dsimp [w]; positivity),
        Real.norm_of_nonneg (by dsimp [w]; positivity)]
      apply le_of_eq
      dsimp [w]
      rw [pow_succ (2 : ℕ), pow_mul]
      field_simp
    · intro k
      have h := Newton.kantorovich_norm_sub_le hβ hL hη e he heβ heη hFd hLd hh.le
        (le_refl r) hconv k
      refine h.trans ?_
      change a ^ (2 ^ k) / ((2 : ℝ) ^ k * (β * L)) ≤ a ^ (2 ^ k) / (β * L)
      have hpow : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      simpa using mul_le_mul_of_nonneg_right hpow (show 0 ≤ β * L by positivity)
  · exact Newton.kantorovich_invertible hβ hL hη e he heβ heη hFd hLd hh.le (le_refl r) k

end Newton

/-- An arbitrarily small initial Newton correction and a constant, invertible derivative
do not suffice on the open half-line. The first Newton step can leave the domain, which
contains no root in this example. -/
theorem newton_correction_small_without_domain_ball (ε : ℝ) (hε : 0 < ε) :
    ∃ (f : ℝ → ℝ) (x₀ : ℝ), 0 < x₀ ∧
      (∀ x, HasFDerivAt f (ContinuousLinearMap.id ℝ ℝ) x) ∧
      ‖(fderiv ℝ f x₀).inverse (f x₀)‖ < ε ∧
      Newton.step f (fderiv ℝ f) x₀ < 0 ∧
      (∀ x > 0, f x ≠ 0) := by
  let f (x : ℝ) := x + ε / 2
  let x₀ : ℝ := ε / 4
  have hd (x : ℝ) : HasFDerivAt f (ContinuousLinearMap.id ℝ ℝ) x := by
    exact (hasFDerivAt_id x).add_const (ε / 2)
  have hinv : (fderiv ℝ f x₀).inverse = ContinuousLinearMap.id ℝ ℝ := by
    rw [(hd x₀).fderiv]
    exact ContinuousLinearMap.inverse_equiv (ContinuousLinearEquiv.refl ℝ ℝ)
  refine ⟨f, x₀, by dsimp [x₀]; positivity, hd, ?_, ?_, ?_⟩
  · rw [hinv, ContinuousLinearMap.id_apply, Real.norm_of_nonneg (by dsimp [f, x₀]; positivity)]
    dsimp [f, x₀]
    linarith
  · rw [Newton.step, hinv, ContinuousLinearMap.id_apply]
    dsimp [f, x₀]
    linarith
  · intro x hx
    dsimp [f]
    positivity

end ConnGouldToint.Chapter03
