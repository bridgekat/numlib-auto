import Numlib.Analysis.Normed.Ring.Inverse
import Numlib.Nonlinear.Newton
import NumlibSurface.AtkinsonHan.Chapter05.Section03

/-!
# Atkinson–Han §5.4: Newton's method

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §5.4: Newton's method for `F(u) = 0` in a
Banach space, its local quadratic convergence, the Newton–Kantorovich theorem and the modified
(chord) method.

The book's iteration (5.4.2), `u_{n+1} = u_n - [F'(u_n)]⁻¹ F(u_n)`, is the backbone's
`Newton.step` / `Newton.iterate` (`Numlib/Nonlinear/Newton.lean`), which uses Mathlib's
`ContinuousLinearMap.inverse`, so no surface definition of the iteration is needed.

## Main results

* `equation_5_4_2`, `newtonStep_eq_self`, `newtonStep_sub_eq` — (5.4.2), that a root is a fixed
  point of the step, and the increment form `F'(u_n) δ_n = -F(u_n)` of (5.4.7)/(5.4.9).
* `exists_equiv_of_norm_lt` — the perturbation criterion (the book's Theorem 2.3.5) that keeps
  `F'(u_n)` invertible along the iteration.
* `equation_5_4_5` — the quadratic estimate for one Newton step, from the `L/2` Taylor lemma
  `norm_sub_sub_fderiv_le_half_mul_sq` of §5.3.
* `theorem_5_4_1` — Theorem 5.4.1, local quadratic convergence, with (5.4.3) and (5.4.4).
* `theorem_5_4_2` — Theorem 5.4.2, the **Newton–Kantorovich theorem**, together with the book's
  three finer clauses: existence localized to `B̄(u₁, t* - b)` (`theorem_5_4_2_step`),
  uniqueness within `t** = (1 + √(1-2h))/(aL)` of `u₀` (`theorem_5_4_2_unique`) and the sharp a
  priori bound `[1 - √(1-2h)]^{2ⁿ}/(2ⁿ a L)` (`theorem_5_4_2_sharp`).
* `equation_5_4_11`, `exercise_5_4_5` — the modified Newton (chord) method with a frozen
  derivative, whose convergence is linear rather than quadratic.
* `equation_5_4_7` — Newton's method for a nonlinear system in `ℝᵈ`.
* `equation_5_4_8`, `equation_5_4_10`, `equation_5_4_12` — §5.4.2 applied to the nonlinear
  integral equation `u(t) = ∫ₐᵇ k(t, s, u(s)) ds`: the derivative of `F = I − K` is `I` minus a
  Fredholm operator, so one Newton step is the solution of one *linear* integral equation of the
  second kind, and the modified method solves it with a kernel frozen at `u₀`.

## Conventions

The uniqueness domain of Theorem 5.4.2 is the **open** ball of radius `t**`, not the closed one as
the book prints it; `theorem_5_4_2_unique` explains why the closed form is false for `h < ½`.

## Not formalized here

The two-point boundary value problem `u'' = f(t, u)`, `u(0) = u(1) = 0` of §5.4.2, whose Newton
linearization is a linear boundary value problem.  The obstruction is the space: the book works in
`U = C²₀[0, 1]`, and neither this project nor Mathlib has `Cᵏ[a, b]` as a Banach space under
`∑_{j ≤ k} ‖u^{(j)}‖_∞` — Mathlib's `ContDiffMapSupportedIn` is a *seminormed* space of compactly
supported functions and is not it.  That space is backbone material and reusable (Atkinson–Han
§1.4 defines it), and once it exists the derivative computation is easy: `u ↦ u''` is a bounded
linear map `C²₀ → C⁰` and `u ↦ f(·, u(·))` is a Nemytskii operator, differentiable by the argument
of `example_5_3_10`.
-/

open Filter Metric Topology

namespace AtkinsonHan.Chapter05

variable {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- **(5.4.2)**: one step of Newton's method. -/
theorem equation_5_4_2 (F : U → W) (F' : U → U →L[ℝ] W) (u₀ : U) (n : ℕ) :
    Newton.iterate F F' u₀ (n + 1) = Newton.step F F' (Newton.iterate F F' u₀ n) :=
  Newton.iterate_succ F F' u₀ n

/-- A root of `F` is a fixed point of the Newton step. -/
theorem newtonStep_eq_self {F : U → W} (F' : U → U →L[ℝ] W) {u : U} (hu : F u = 0) :
    Newton.step F F' u = u :=
  Newton.step_eq_self_of_eq_zero F F' hu

/-- The increment form of the Newton step, `F'(u) δ = -F(u)` with `δ = u_{n+1} - u_n`; this is
how (5.4.7) and (5.4.9) write the iteration in practice. -/
theorem newtonStep_sub_eq {F : U → W} {F' : U → U →L[ℝ] W} {u : U} (e : U ≃L[ℝ] W)
    (he : (e : U →L[ℝ] W) = F' u) : F' u (Newton.step F F' u - u) = -F u := by
  have hinv : (F' u).inverse = (e.symm : W →L[ℝ] U) := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
  have hstep : Newton.step F F' u - u = -((e.symm : W →L[ℝ] U) (F u)) := by
    rw [Newton.step, hinv]
    abel
  rw [hstep, map_neg, ← he]
  simp

section Complete

variable [CompleteSpace U] [CompleteSpace W]

omit [CompleteSpace W] in
/-- Perturbation criterion for the Newton step to be well defined: an operator close enough to an
invertible one is invertible.  This specializes the backbone's
`ContinuousLinearEquiv.exists_symm_norm_le_of_add` (`Numlib/Analysis/Normed/Ring/Inverse.lean`,
the book's Theorem 2.3.5). -/
theorem exists_equiv_of_norm_lt {A : U →L[ℝ] W} (e : U ≃L[ℝ] W)
    (h : ‖(e.symm : W →L[ℝ] U)‖ * ‖A - (e : U →L[ℝ] W)‖ < 1) :
    ∃ e' : U ≃L[ℝ] W, (e' : U →L[ℝ] W) = A := by
  obtain ⟨e', he', -, -⟩ :=
    ContinuousLinearEquiv.exists_symm_norm_le_of_add e (A - (e : U →L[ℝ] W)) h
  exact ⟨e', by rw [he']; abel⟩

omit [CompleteSpace U] [CompleteSpace W] in
/-- **(5.4.5)**: with `T u = u - [F'(u)]⁻¹ F(u)`, `‖T u - u*‖ ≤ (c₀ L / 2) ‖u - u*‖²` where
`c₀` bounds `‖[F'(u)]⁻¹‖` and `L` is the Lipschitz constant of `F'`.  Proved from the `L/2`
Taylor estimate `norm_sub_sub_fderiv_le_half_mul_sq` of §5.3. -/
theorem equation_5_4_5 {F : U → W} {F' : U → U →L[ℝ] W} {ustar : U} (hroot : F ustar = 0)
    {r L c₀ : ℝ}
    (hF : ∀ z ∈ ball ustar r, HasFDerivAt F (F' z) z)
    (hL : ∀ z ∈ ball ustar r, ∀ w ∈ ball ustar r, ‖F' z - F' w‖ ≤ L * ‖z - w‖) {u : U}
    (hu : u ∈ ball ustar r) (e : U ≃L[ℝ] W) (he : (e : U →L[ℝ] W) = F' u)
    (hc₀ : ‖(e.symm : W →L[ℝ] U)‖ ≤ c₀) :
    ‖Newton.step F F' u - ustar‖ ≤ c₀ * L / 2 * ‖u - ustar‖ ^ 2 := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg (mem_ball.mp hu)
  have hstarmem : ustar ∈ ball ustar r := mem_ball_self hr
  have hinv : (F' u).inverse = (e.symm : W →L[ℝ] U) := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
  have hsymm : ∀ z : U, (e.symm : W →L[ℝ] U) (F' u z) = z := by
    intro z
    rw [← he]
    simp
  have htay := norm_sub_sub_fderiv_le_half_mul_sq (convex_ball ustar r) hF hL hu hstarmem
  have hkey : Newton.step F F' u - ustar
      = (e.symm : W →L[ℝ] U) (F ustar - F u - F' u (ustar - u)) := by
    rw [hroot]
    simp only [map_sub, hsymm, Newton.step, hinv, map_zero]
    abel
  have hc₀0 : 0 ≤ c₀ := le_trans (norm_nonneg _) hc₀
  rw [hkey, norm_sub_rev ustar u] at *
  calc ‖(e.symm : W →L[ℝ] U) (F ustar - F u - F' u (ustar - u))‖
      ≤ ‖(e.symm : W →L[ℝ] U)‖ * ‖F ustar - F u - F' u (ustar - u)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ c₀ * (L / 2 * ‖u - ustar‖ ^ 2) :=
        mul_le_mul hc₀ htay (norm_nonneg _) hc₀0
    _ = c₀ * L / 2 * ‖u - ustar‖ ^ 2 := by ring

omit [CompleteSpace W] in
/-- **Theorem 5.4.1** (local convergence of Newton's method).  If `F` is differentiable near a
root `u*` with `F'(u*)` invertible and `F'` Lipschitz with constant `L` on a ball, then there are
`δ > 0` and `M > 0` with `M δ < 1` such that from every `u₀` with `‖u₀ - u*‖ ≤ δ` the Newton
iteration is well defined, converges to `u*`, and satisfies (5.4.3)
`‖u_{n+1} - u*‖ ≤ M ‖u_n - u*‖²` and (5.4.4) `‖u_n - u*‖ ≤ (M δ)^{2ⁿ}/M`.  The backbone supplies
the quadratic step estimate (`Newton.exists_ball_norm_step_sub_le`) and the convergence
(`Newton.tendsto_iterate`); `0 < M` is added so that (5.4.4) is meaningful. -/
theorem theorem_5_4_1 {F : U → W} {F' : U → U →L[ℝ] W} {ustar : U} (hroot : F ustar = 0)
    (e : U ≃L[ℝ] W) (he : (e : U →L[ℝ] W) = F' ustar) {r L : ℝ} (hr : 0 < r)
    (hF : ∀ u ∈ ball ustar r, HasFDerivAt F (F' u) u)
    (hL : ∀ u ∈ ball ustar r, ∀ v ∈ ball ustar r, ‖F' u - F' v‖ ≤ L * ‖u - v‖) :
    ∃ δ > 0, ∃ M > 0, M * δ < 1 ∧ ∀ u₀, ‖u₀ - ustar‖ ≤ δ →
      (∀ n, ∃ e' : U ≃L[ℝ] W, (e' : U →L[ℝ] W) = F' (Newton.iterate F F' u₀ n)) ∧
      Tendsto (Newton.iterate F F' u₀) atTop (𝓝 ustar) ∧
      (∀ n, ‖Newton.iterate F F' u₀ (n + 1) - ustar‖
        ≤ M * ‖Newton.iterate F F' u₀ n - ustar‖ ^ 2) ∧
      (∀ n, ‖Newton.iterate F F' u₀ n - ustar‖ ≤ (M * δ) ^ 2 ^ n / M) := by
  obtain ⟨δ₀, hδ₀, C, hC⟩ := Newton.exists_ball_norm_step_sub_le hroot e he hr hF hL
  obtain ⟨δ₁, hδ₁, htend⟩ := Newton.tendsto_iterate hroot e he hr hF hL
  set K : ℝ := ‖(e.symm : W →L[ℝ] U)‖ with hKdef
  set L' : ℝ := max L 0 with hL'def
  set M : ℝ := max C 1 with hMdef
  have hM0 : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hK0 : 0 ≤ K := norm_nonneg _
  have hL'0 : 0 ≤ L' := le_max_right _ _
  have hp0 : 0 ≤ K * L' := mul_nonneg hK0 hL'0
  set δ : ℝ := min (min (δ₀ / 2) (δ₁ / 2))
    (min (r / 2) (min (1 / (2 * M)) (1 / (2 * (K * L' + 1))))) with hδdef
  have hδ0 : 0 < δ :=
    lt_min (lt_min (by linarith) (by linarith))
      (lt_min (by linarith) (lt_min (by positivity) (by positivity)))
  have hδδ₀ : δ ≤ δ₀ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδδ₁ : δ ≤ δ₁ / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδr : δ ≤ r / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδM : δ ≤ 1 / (2 * M) := le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
    (min_le_left _ _))
  have hδp : δ ≤ 1 / (2 * (K * L' + 1)) := le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_right _ _))
  have hMδ : M * δ ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left hδM hM0.le
    rw [mul_one_div] at h
    calc M * δ ≤ M / (2 * M) := h
      _ = 1 / 2 := by field_simp
  -- one step: quadratic decrease, and the iterate stays within `δ` of the root
  have hstep : ∀ u : U, ‖u - ustar‖ ≤ δ →
      ‖Newton.step F F' u - ustar‖ ≤ M * ‖u - ustar‖ ^ 2 ∧
        ‖Newton.step F F' u - ustar‖ ≤ δ := by
    intro u hu
    have huball : u ∈ ball ustar δ₀ := by
      rw [mem_ball, dist_eq_norm]
      linarith
    have h1 : ‖Newton.step F F' u - ustar‖ ≤ M * ‖u - ustar‖ ^ 2 :=
      (hC u huball).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    refine ⟨h1, h1.trans ?_⟩
    nlinarith [norm_nonneg (u - ustar), hM0]
  have hiter : ∀ u₀, ‖u₀ - ustar‖ ≤ δ → ∀ n, ‖Newton.iterate F F' u₀ n - ustar‖ ≤ δ := by
    intro u₀ hu₀ n
    induction n with
    | zero => simpa [Newton.iterate] using hu₀
    | succ n ih =>
      rw [Newton.iterate_succ]
      exact (hstep _ ih).2
  -- well-definedness of every step, by the perturbation theorem
  have hwell : ∀ u : U, ‖u - ustar‖ ≤ δ → ∃ e' : U ≃L[ℝ] W, (e' : U →L[ℝ] W) = F' u := by
    intro u hu
    have huball : u ∈ ball ustar r := by
      rw [mem_ball, dist_eq_norm]
      linarith
    have h1 : ‖F' u - (e : U →L[ℝ] W)‖ ≤ L' * δ := by
      rw [he]
      calc ‖F' u - F' ustar‖ ≤ L * ‖u - ustar‖ := hL u huball ustar (mem_ball_self hr)
        _ ≤ L' * ‖u - ustar‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ ≤ L' * δ := mul_le_mul_of_nonneg_left hu hL'0
    have h2 : K * (L' * δ) < 1 := by
      have h3 : K * L' * δ ≤ K * L' * (1 / (2 * (K * L' + 1))) :=
        mul_le_mul_of_nonneg_left hδp hp0
      have h4 : K * L' * (1 / (2 * (K * L' + 1))) < 1 := by
        rw [mul_one_div, div_lt_one (by positivity)]
        linarith
      calc K * (L' * δ) = K * L' * δ := by ring
        _ ≤ K * L' * (1 / (2 * (K * L' + 1))) := h3
        _ < 1 := h4
    refine exists_equiv_of_norm_lt e (lt_of_le_of_lt ?_ h2)
    exact mul_le_mul_of_nonneg_left h1 hK0
  refine ⟨δ, hδ0, M, hM0, by linarith, fun u₀ hu₀ => ⟨fun n => hwell _ (hiter u₀ hu₀ n), ?_,
    fun n => ?_, fun n => ?_⟩⟩
  · refine htend u₀ ?_
    rw [mem_ball, dist_eq_norm]
    linarith
  · rw [Newton.iterate_succ]
    exact (hstep _ (hiter u₀ hu₀ n)).1
  · induction n with
    | zero =>
      have h : (M * δ) ^ 2 ^ 0 / M = δ := by
        rw [pow_zero, pow_one]
        field_simp
      rw [h]
      simpa [Newton.iterate] using hu₀
    | succ n ih =>
      have h1 : ‖Newton.iterate F F' u₀ (n + 1) - ustar‖
          ≤ M * ‖Newton.iterate F F' u₀ n - ustar‖ ^ 2 := by
        rw [Newton.iterate_succ]
        exact (hstep _ (hiter u₀ hu₀ n)).1
      have h2 : ‖Newton.iterate F F' u₀ n - ustar‖ ^ 2 ≤ ((M * δ) ^ 2 ^ n / M) ^ 2 := by
        have hnn : (0 : ℝ) ≤ ‖Newton.iterate F F' u₀ n - ustar‖ := norm_nonneg _
        nlinarith [ih]
      have h3 : M * ((M * δ) ^ 2 ^ n / M) ^ 2 = (M * δ) ^ 2 ^ (n + 1) / M := by
        rw [pow_succ 2 n, pow_mul]
        field_simp
      calc ‖Newton.iterate F F' u₀ (n + 1) - ustar‖
          ≤ M * ‖Newton.iterate F F' u₀ n - ustar‖ ^ 2 := h1
        _ ≤ M * ((M * δ) ^ 2 ^ n / M) ^ 2 := mul_le_mul_of_nonneg_left h2 hM0.le
        _ = (M * δ) ^ 2 ^ (n + 1) / M := h3

set_option linter.unusedSectionVars false in
/-- **Theorem 5.4.2** (Newton–Kantorovich).  Every hypothesis is checkable at the starting point
`u₀`: `‖[F'(u₀)]⁻¹‖ ≤ a`, `‖[F'(u₀)]⁻¹ F(u₀)‖ ≤ b`, `F'` is `L`-Lipschitz, and `h = a b L ≤ ½`.
Then `F` has a root `u*` within `t* = (1 - √(1-2h))/(aL)` of `u₀`, the Newton iterates stay in the
ball and converge to it, with the a priori bound of the last conjunct.  This is the backbone's
`Newton.kantorovich` (`Numlib/Nonlinear/Newton.lean`).  The positivity hypotheses `0 < a` and
`0 < L` are added so that `t*` is not `0/0`.

`[CompleteSpace W]` is kept because the book states the theorem for Banach spaces, although it is
redundant: `e : U ≃L[ℝ] W` transports completeness from `U`. -/
theorem theorem_5_4_2 {F : U → W} {F' : U → U →L[ℝ] W} {u₀ : U} {r a b L : ℝ} (ha : 0 < a)
    (hLpos : 0 < L) (hb : 0 ≤ b) (e : U ≃L[ℝ] W) (he : (e : U →L[ℝ] W) = F' u₀)
    (ha' : ‖(e.symm : W →L[ℝ] U)‖ ≤ a) (hb' : ‖e.symm (F u₀)‖ ≤ b)
    (hF : ∀ u ∈ closedBall u₀ r, HasFDerivAt F (F' u) u)
    (hLip : ∀ u ∈ closedBall u₀ r, ∀ v ∈ closedBall u₀ r, ‖F' u - F' v‖ ≤ L * ‖u - v‖)
    (hh : a * b * L ≤ 1 / 2)
    (hr : (1 - Real.sqrt (1 - 2 * (a * b * L))) / (a * L) ≤ r) :
    ∃ ustar ∈ closedBall u₀ ((1 - Real.sqrt (1 - 2 * (a * b * L))) / (a * L)),
      F ustar = 0 ∧ Tendsto (Newton.iterate F F' u₀) atTop (𝓝 ustar) ∧
      (∀ n, Newton.iterate F F' u₀ n ∈ closedBall u₀ r) ∧
      (0 < a * b * L → ∀ n, ‖Newton.iterate F F' u₀ n - ustar‖ ≤
        (2 * (a * b * L)) ^ 2 ^ n * b / (2 ^ n * (a * b * L))) := by
  have hcomm : a * L * b = a * b * L := by ring
  have hkey := Newton.kantorovich ha hLpos hb e he ha' hb' hF hLip (by rw [hcomm]; exact hh)
    (by rw [hcomm]; exact hr)
  rwa [hcomm] at hkey

set_option linter.unusedSectionVars false in
/-- **Theorem 5.4.2**, the book's localized existence clause: the root is found in
`B̄(u₁, t* − b)`, the ball around the *first* Newton iterate `u₁ = T u₀`, and the domain of `F`
need only be a convex set containing `u₀` and that ball.  This is the shape in which the theorem
is applied when no a priori ball around `u₀` is known. -/
theorem theorem_5_4_2_step {F : U → W} {F' : U → U →L[ℝ] W} {u₀ : U} {D : Set U} {a b L : ℝ}
    (ha : 0 < a) (hLpos : 0 < L) (hb : 0 ≤ b) (e : U ≃L[ℝ] W) (he : (e : U →L[ℝ] W) = F' u₀)
    (ha' : ‖(e.symm : W →L[ℝ] U)‖ ≤ a) (hb' : ‖e.symm (F u₀)‖ ≤ b) (hD : Convex ℝ D)
    (hu₀ : u₀ ∈ D)
    (hsub : closedBall (Newton.step F F' u₀)
      ((1 - Real.sqrt (1 - 2 * (a * b * L))) / (a * L) - b) ⊆ D)
    (hF : ∀ u ∈ D, HasFDerivAt F (F' u) u)
    (hLip : ∀ u ∈ D, ∀ v ∈ D, ‖F' u - F' v‖ ≤ L * ‖u - v‖) (hh : a * b * L ≤ 1 / 2) :
    ∃ ustar ∈ closedBall (Newton.step F F' u₀)
        ((1 - Real.sqrt (1 - 2 * (a * b * L))) / (a * L) - b),
      F ustar = 0 ∧ Tendsto (Newton.iterate F F' u₀) atTop (𝓝 ustar) := by
  have hcomm : a * L * b = a * b * L := by ring
  have hkey := Newton.kantorovich_of_closedBall_step ha hLpos hb e he ha' hb' hD hu₀
    (by rw [hcomm]; exact hsub) hF hLip (by rw [hcomm]; exact hh)
  rwa [hcomm] at hkey

set_option linter.unusedSectionVars false in
/-- **Theorem 5.4.2**, the uniqueness clause: the root produced by the Newton–Kantorovich theorem
is the *only* root of `F` in the domain, within distance `t** = (1 + √(1 − 2h))/(aL)` of `u₀`.

Statement correction: the book, and the plan taken from it, put uniqueness on the *closed* ball of
radius `t**`.  That is false whenever `h < ½`.  The scalar majorant `p t = (L/2)t² − t/a + b/a`
satisfies every hypothesis at `u₀ = 0` and has a second root at distance exactly `t**`, so the
closed ball of radius `t**` contains a second zero; the open ball is the correct domain, and it is
what the backbone's `Newton.kantorovich_unique` proves.  (The closed ball of radius `t*` is also a
uniqueness domain, and that is the form that survives the critical case `h = ½`.) -/
theorem theorem_5_4_2_unique {F : U → W} {F' : U → U →L[ℝ] W} {u₀ : U} {r a b L : ℝ} (ha : 0 < a)
    (hLpos : 0 < L) (hb : 0 ≤ b) (e : U ≃L[ℝ] W) (he : (e : U →L[ℝ] W) = F' u₀)
    (ha' : ‖(e.symm : W →L[ℝ] U)‖ ≤ a) (hb' : ‖e.symm (F u₀)‖ ≤ b)
    (hF : ∀ u ∈ closedBall u₀ r, HasFDerivAt F (F' u) u)
    (hLip : ∀ u ∈ closedBall u₀ r, ∀ v ∈ closedBall u₀ r, ‖F' u - F' v‖ ≤ L * ‖u - v‖)
    (hh : a * b * L ≤ 1 / 2)
    (hr : (1 - Real.sqrt (1 - 2 * (a * b * L))) / (a * L) ≤ r) {ustar : U}
    (hustar : Tendsto (Newton.iterate F F' u₀) atTop (𝓝 ustar)) {v : U} (hv : F v = 0)
    (hvr : v ∈ closedBall u₀ r)
    (hvt : ‖v - u₀‖ < (1 + Real.sqrt (1 - 2 * (a * b * L))) / (a * L)) :
    v = ustar := by
  have hcomm : a * L * b = a * b * L := by ring
  exact Newton.kantorovich_unique ha hLpos hb e he ha' hb' hF hLip (by rw [hcomm]; exact hh)
    (by rw [hcomm]; exact hr) hustar hv hvr (by rw [hcomm]; exact hvt)

set_option linter.unusedSectionVars false in
/-- **Theorem 5.4.2**, the sharp a priori bound: under the hypotheses of the Newton–Kantorovich
theorem,

  `‖u_n − u*‖ ≤ [1 − √(1 − 2h)]^{2ⁿ} / (2ⁿ a L)`,

which is the book's finer form of the last conjunct of `theorem_5_4_2`.  Together with
`theorem_5_4_2_step` and `theorem_5_4_2_unique` this is Theorem 5.4.2 as the book states it. -/
theorem theorem_5_4_2_sharp {F : U → W} {F' : U → U →L[ℝ] W} {u₀ : U} {r a b L : ℝ} (ha : 0 < a)
    (hLpos : 0 < L) (hb : 0 ≤ b) (e : U ≃L[ℝ] W) (he : (e : U →L[ℝ] W) = F' u₀)
    (ha' : ‖(e.symm : W →L[ℝ] U)‖ ≤ a) (hb' : ‖e.symm (F u₀)‖ ≤ b)
    (hF : ∀ u ∈ closedBall u₀ r, HasFDerivAt F (F' u) u)
    (hLip : ∀ u ∈ closedBall u₀ r, ∀ v ∈ closedBall u₀ r, ‖F' u - F' v‖ ≤ L * ‖u - v‖)
    (hh : a * b * L ≤ 1 / 2)
    (hr : (1 - Real.sqrt (1 - 2 * (a * b * L))) / (a * L) ≤ r) {ustar : U}
    (hustar : Tendsto (Newton.iterate F F' u₀) atTop (𝓝 ustar)) (n : ℕ) :
    ‖Newton.iterate F F' u₀ n - ustar‖
      ≤ (1 - Real.sqrt (1 - 2 * (a * b * L))) ^ 2 ^ n / (2 ^ n * (a * L)) := by
  have hcomm : a * L * b = a * b * L := by ring
  have hkey := Newton.kantorovich_norm_sub_le ha hLpos hb e he ha' hb' hF hLip
    (by rw [hcomm]; exact hh) (by rw [hcomm]; exact hr) hustar n
  rwa [hcomm] at hkey

end Complete

section Chord

variable {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- **(5.4.11)**: one step of the modified Newton method, in which the derivative is frozen at a
single invertible operator `A` (in the book, `A = F'(u₀)`): `u_{n+1} = u_n − A⁻¹ F(u_n)`. -/
theorem equation_5_4_11 (F : U → W) (A : U ≃L[ℝ] W) (u₀ : U) (n : ℕ) :
    Newton.chordIterate F A u₀ (n + 1) = Newton.chordStep F A (Newton.chordIterate F A u₀ n) :=
  Newton.chordIterate_succ F A u₀ n

/-- **Exercise 5.4.5**, the modified Newton (chord) method (5.4.11).  If `F` is differentiable near
a root `u*`, `F'` is Lipschitz there, and the frozen operator `A` is close enough to `F'(u*)` that
`‖I − A⁻¹ F'(u*)‖ < 1`, then from every sufficiently close start the iteration converges to `u*`,
*linearly*: `‖u_n − u*‖ ≤ qⁿ ‖u₀ − u*‖` with a rate `q < 1`.  The book's choice `A = F'(u₀)`
satisfies the hypothesis once `u₀` is close enough to `u*`, by the perturbation theorem.

The rate is linear and not quadratic, which is exactly the point of the exercise: freezing the
derivative costs an order of convergence. -/
theorem exercise_5_4_5 {F : U → W} {F' : U → U →L[ℝ] W} {ustar : U} (hroot : F ustar = 0)
    {r L : ℝ} (hr : 0 < r) (A : U ≃L[ℝ] W)
    (hF : ∀ u ∈ closedBall ustar r, HasFDerivAt F (F' u) u)
    (hLip : ∀ u ∈ closedBall ustar r, ‖F' u - F' ustar‖ ≤ L * ‖u - ustar‖)
    (hA : ‖1 - (A.symm : W →L[ℝ] U) ∘L F' ustar‖ < 1) :
    ∃ δ > 0, ∃ q, 0 ≤ q ∧ q < 1 ∧ ∀ u₀ ∈ closedBall ustar δ,
      (∀ n, ‖Newton.chordIterate F A u₀ n - ustar‖ ≤ q ^ n * ‖u₀ - ustar‖) ∧
        Tendsto (Newton.chordIterate F A u₀) atTop (𝓝 ustar) :=
  Newton.tendsto_chordIterate hroot hr A hF hLip hA

end Chord

section System

/-- **(5.4.7)**: Newton's method for a nonlinear system `F(x) = 0` in `ℝᵈ`.  Each step solves the
linear system `F'(x_n) δ_n = -F(x_n)` and sets `x_{n+1} = x_n + δ_n`. -/
theorem equation_5_4_7 {d : ℕ} {F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {F' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {x : EuclideanSpace ℝ (Fin d)} (e : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (he : (e : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) = F' x) :
    F' x (Newton.step F F' x - x) = -F x ∧
      Newton.step F F' x = x + (Newton.step F F' x - x) := by
  refine ⟨newtonStep_sub_eq e he, by abel⟩

end System

section IntegralEquation

open Set IntegralOperator

variable {a b : ℝ}

/-- **(5.4.8)**: the Fréchet derivative of the operator `F(u) = u − K(u)` of the nonlinear integral
equation, `K` the Urysohn operator of `k`, is `F'(u) = I − K'(u)` — the identity minus the Fredholm
operator whose kernel is `∂_u k(t, s, u(s))`.  This is Example 5.3.10 (`example_5_3_10`) together
with the derivative of the identity. -/
theorem equation_5_4_8 (hab : a ≤ b) {k kz : C(Icc a b × Icc a b × ℝ, ℝ)}
    (hk : ∀ (x y : Icc a b) (z : ℝ), HasDerivAt (fun t => k (x, y, t)) (kz (x, y, z)) z)
    (u : C(Icc a b, ℝ)) :
    HasFDerivAt (fun v => v - urysohn hab k v) (1 - fredholm hab (urysohnDerivKernel kz u)) u :=
  (hasFDerivAt_id u).sub (example_5_3_10 hab hk u)

/-- `I − K` applied to a function, evaluated at a point: the left-hand side of a linear integral
equation of the second kind. -/
private theorem one_sub_fredholm_apply (hab : a ≤ b) (K : C(Icc a b × Icc a b, ℝ))
    (v : C(Icc a b, ℝ)) (t : Icc a b) :
    (1 - fredholm hab K) v t
      = v t - ∫ s in a..b, K (t, projIcc a b hab s) * v (projIcc a b hab s) :=
  rfl

/-- **(5.4.9)–(5.4.10)**: Newton's method for the nonlinear integral equation
`F(u)(t) = u(t) − ∫ₐᵇ k(t, s, u(s)) ds = 0`.  Writing `δ_{n+1} = u_{n+1} − u_n`, the step (5.4.9)
`F'(u_n) δ_{n+1} = −F(u_n)` is the **linear** integral equation (5.4.10)

`δ_{n+1}(t) − ∫ₐᵇ ∂_u k(t, s, u_n(s)) δ_{n+1}(s) ds = −F(u_n)(t)`,

a Fredholm equation of the second kind whose kernel is the partial derivative of `k` along the
current iterate.  So each Newton step for a nonlinear integral equation costs the solution of one
linear one.

Invertibility of `F'(u_n)` is a hypothesis in the book too; it is carried here as the equivalence
`e`, exactly as in `equation_5_4_7`. -/
theorem equation_5_4_10 (hab : a ≤ b) {k kz : C(Icc a b × Icc a b × ℝ, ℝ)}
    {F : C(Icc a b, ℝ) → C(Icc a b, ℝ)} (hF : ∀ v, F v = v - urysohn hab k v)
    {F' : C(Icc a b, ℝ) → C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ)}
    (hF' : ∀ v, F' v = 1 - fredholm hab (urysohnDerivKernel kz v)) (u : C(Icc a b, ℝ))
    (e : C(Icc a b, ℝ) ≃L[ℝ] C(Icc a b, ℝ))
    (he : (e : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ)) = F' u) (t : Icc a b) :
    Newton.step F F' u t - u t
        - ∫ s in a..b, kz (t, projIcc a b hab s, u (projIcc a b hab s))
            * (Newton.step F F' u (projIcc a b hab s) - u (projIcc a b hab s))
      = -(u t - ∫ s in a..b, k (t, projIcc a b hab s, u (projIcc a b hab s))) := by
  have h := newtonStep_sub_eq (F := F) e he
  rw [hF' u, hF u] at h
  have h2 := congrArg (fun w : C(Icc a b, ℝ) => w t) h
  simp only [one_sub_fredholm_apply hab, ContinuousMap.sub_apply, ContinuousMap.neg_apply,
    urysohnDerivKernel_apply, urysohn_apply] at h2
  exact h2

/-- **(5.4.11)–(5.4.12)**: the modified Newton method for the same equation freezes the kernel of
the linearization at the starting function `u₀`, so that every step solves the linear integral
equation

`δ_{n+1}(t) − ∫ₐᵇ ∂_u k(t, s, u₀(s)) δ_{n+1}(s) ds = −F(u_n)(t)`

with one and the same kernel — which is what makes the modified method cheap, and, by
`exercise_5_4_5`, only linearly convergent. -/
theorem equation_5_4_12 (hab : a ≤ b) {k kz : C(Icc a b × Icc a b × ℝ, ℝ)}
    {F : C(Icc a b, ℝ) → C(Icc a b, ℝ)} (hF : ∀ v, F v = v - urysohn hab k v)
    (u₀ : C(Icc a b, ℝ)) (A : C(Icc a b, ℝ) ≃L[ℝ] C(Icc a b, ℝ))
    (hA : (A : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ))
      = 1 - fredholm hab (urysohnDerivKernel kz u₀)) (u : C(Icc a b, ℝ)) (t : Icc a b) :
    Newton.chordStep F A u t - u t
        - ∫ s in a..b, kz (t, projIcc a b hab s, u₀ (projIcc a b hab s))
            * (Newton.chordStep F A u (projIcc a b hab s) - u (projIcc a b hab s))
      = -(u t - ∫ s in a..b, k (t, projIcc a b hab s, u (projIcc a b hab s))) := by
  have hsub : Newton.chordStep F A u - u = -(A.symm (F u)) := by
    rw [Newton.chordStep]; abel
  have h : (A : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ)) (Newton.chordStep F A u - u) = -F u := by
    rw [hsub, ContinuousLinearEquiv.coe_coe, map_neg, ContinuousLinearEquiv.apply_symm_apply]
  rw [hA, hF u] at h
  have h2 := congrArg (fun w : C(Icc a b, ℝ) => w t) h
  simp only [one_sub_fredholm_apply hab, ContinuousMap.sub_apply, ContinuousMap.neg_apply,
    urysohnDerivKernel_apply, urysohn_apply] at h2
  exact h2

end IntegralEquation

end AtkinsonHan.Chapter05
