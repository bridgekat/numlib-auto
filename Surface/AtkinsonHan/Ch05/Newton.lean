import AtkinsonHan.Ch05.Calculus

/-!
# Atkinson–Han §5.4: Newton's method

Surface formalization of §5.4 of Kendall Atkinson and Weimin Han, *Theoretical Numerical
Analysis: A Functional Analysis Framework*, 3rd edition, Springer, 2009.

The book's iteration (5.4.2), `u_{n+1} = u_n - [F'(u_n)]⁻¹ F(u_n)`, is the backbone's
`Newton.step` / `Newton.iterate` (`Numlib/Nonlinear/Newton.lean`), which uses Mathlib's
`ContinuousLinearMap.inverse`.  Contents:

* (5.4.2) and the equivalent increment form `F'(u_n) δ_n = -F(u_n)` of (5.4.7)/(5.4.9);
* (5.4.5), the quadratic estimate for one Newton step, proved from the `L/2` Taylor lemma
  `norm_sub_sub_fderiv_le_half_mul_sq` of §5.3;
* Theorem 5.4.1, local quadratic convergence, with (5.4.3) and (5.4.4);
* Theorem 5.4.2, the Newton–Kantorovich theorem;
* (5.4.7), Newton's method for a nonlinear system in `ℝᵈ`.

Deferred (`plans/surface/AtkinsonHan-Ch5.md` §3 item 2, `plans/backbone.md` §7 "5.3.2
Kantorovich", phase 2): the book's finer form of Theorem 5.4.2 — existence localized to
`B̄(u₁, t* - b)`, uniqueness in `B̄(u₀, t**)` with `t** = (1 + √(1-2h))/(aL)`, and the sharper a
priori bound `[1 - √(1-2h)]^{2ⁿ}/(2ⁿ a L)`.  Out of scope (§4 of the plan): the applications
(5.4.8)–(5.4.12), which need the phase-3 `C[a,b]` integral-operator toolkit, and the modified
Newton (chord) method of Exercise 5.4.5.
-/

open Filter Metric Topology

namespace AtkinsonHan.Ch05

variable {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- **(5.4.2)**: one step of Newton's method. -/
theorem eq_5_4_2 (F : U → W) (F' : U → U →L[ℝ] W) (u₀ : U) (n : ℕ) :
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
theorem eq_5_4_5 {F : U → W} {F' : U → U →L[ℝ] W} {ustar : U} (hroot : F ustar = 0) {r L c₀ : ℝ}
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

/-- **Theorem 5.4.1** (local convergence of Newton's method).  If `F` is differentiable near a
root `u*` with `F'(u*)` invertible and `F'` Lipschitz with constant `L` on a ball, then there are
`δ > 0` and `M > 0` with `M δ < 1` such that from every `u₀` with `‖u₀ - u*‖ ≤ δ` the Newton
iteration is well defined, converges to `u*`, and satisfies (5.4.3)
`‖u_{n+1} - u*‖ ≤ M ‖u_n - u*‖²` and (5.4.4) `‖u_n - u*‖ ≤ (M δ)^{2ⁿ}/M`.  The backbone supplies
the quadratic step estimate (`Newton.exists_ball_norm_step_sub_le`) and the convergence
(`Newton.tendsto_iterate`); `0 < M` is added so that (5.4.4) is meaningful. -/
theorem thm_5_4_1 {F : U → W} {F' : U → U →L[ℝ] W} {ustar : U} (hroot : F ustar = 0)
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

/-- **Theorem 5.4.2** (Newton–Kantorovich).  Every hypothesis is checkable at the starting point
`u₀`: `‖[F'(u₀)]⁻¹‖ ≤ a`, `‖[F'(u₀)]⁻¹ F(u₀)‖ ≤ b`, `F'` is `L`-Lipschitz, and `h = a b L ≤ ½`.
Then `F` has a root `u*` within `t* = (1 - √(1-2h))/(aL)` of `u₀`, the Newton iterates stay in the
ball and converge to it, with the a priori bound of the last conjunct.  This is the backbone's
`Newton.kantorovich` (`Numlib/Nonlinear/Newton.lean`).  The positivity hypotheses `0 < a` and
`0 < L` are added so that `t*` is not `0/0`. -/
theorem thm_5_4_2 {F : U → W} {F' : U → U →L[ℝ] W} {u₀ : U} {r a b L : ℝ} (ha : 0 < a)
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

end Complete

section System

/-- **(5.4.7)**: Newton's method for a nonlinear system `F(x) = 0` in `ℝᵈ`.  Each step solves the
linear system `F'(x_n) δ_n = -F(x_n)` and sets `x_{n+1} = x_n + δ_n`. -/
theorem eq_5_4_7 {d : ℕ} {F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {F' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {x : EuclideanSpace ℝ (Fin d)} (e : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (he : (e : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) = F' x) :
    F' x (Newton.step F F' x - x) = -F x ∧
      Newton.step F F' x = x + (Newton.step F F' x - x) := by
  refine ⟨newtonStep_sub_eq e he, by abel⟩

end System

end AtkinsonHan.Ch05
