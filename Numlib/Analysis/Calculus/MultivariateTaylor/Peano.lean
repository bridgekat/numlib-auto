import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder

/-!
# Taylor's theorem with Peano remainder

If `f : E → F` (real normed spaces) is `C^n` at `x`, then
`f(x + h) - T_{f,n}(x, h) = o(‖h‖^n)` as `h → 0` ([cartis2022evaluation], (A.12)), where
`T_{f,n}(x, h) = taylorPolynomial f n x h = ∑_{i ≤ n} (1/i!) ∇^i f(x)[h]^i`.

## Main results

* `exists_norm_sub_taylorPolynomial_le`: the quantitative form — for every `η > 0` there is
  `r > 0` with `‖f(x + h) - T_{f,n}(x, h)‖ ≤ η ‖h‖^n` whenever `‖h‖ < r`;
* `sub_taylorPolynomial_isLittleO`: the little-o form (A.12).

## Implementation notes

The book states (A.12) for `f` merely `n` times differentiable at `x`; here `f` is `C^n` at `x`
(i.e. `C^n` on a neighbourhood of `x`), the setting of all its applications. The proof is the
Hölder bound (A.14) with exponent `β = 0` on a small ball, whose "Hölder constant" is the
oscillation of `∇^n f`, small by continuity; the generalized factorial `(n + 0)!` is `n!`.

For `n = 0` the Taylor polynomial is `f(x)` and the statement is the continuity of `f` at `x`.
-/

open Filter Metric Asymptotics
open scoped Nat Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f : E → F} {n : ℕ} {x : E}

/-- If `∇^n f` oscillates by at most `H` on `C`, it is `(H, 0)`-Hölder on `C`. -/
theorem iteratedFDerivHolderOn_zero_of_norm_sub_le {C : Set E} {H : ℝ}
    (h : ∀ y ∈ C, ∀ z ∈ C, ‖iteratedFDeriv ℝ n f y - iteratedFDeriv ℝ n f z‖ ≤ H) :
    IteratedFDerivHolderOn f n H 0 C := by
  intro y hy z hz
  simpa using h y hy z hz

/-- **Peano remainder, quantitative form** ([cartis2022evaluation], (A.12)). If `f` is `C^n` at
`x`, then for every `η > 0` there is `r > 0` such that
`‖f(x + h) - T_{f,n}(x, h)‖ ≤ η ‖h‖^n` whenever `‖h‖ < r`. -/
theorem exists_norm_sub_taylorPolynomial_le (hf : ContDiffAt ℝ n f x) {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ h : E, ‖h‖ < r → ‖f (x + h) - taylorPolynomial f n x h‖ ≤ η * ‖h‖ ^ n := by
  have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ n f y := hf.eventually (by simp)
  have hcont : ∀ᶠ y in 𝓝 x,
      ‖iteratedFDeriv ℝ n f y - iteratedFDeriv ℝ n f x‖ < η * n ! / 2 := by
    have hc : ContinuousAt (iteratedFDeriv ℝ n f) x := hf.continuousAt_iteratedFDeriv le_rfl
    simpa [dist_eq_norm] using
      Metric.tendsto_nhds.1 hc (η * n ! / 2) (by positivity)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hev.and hcont)
  refine ⟨r, hr, fun h hh => ?_⟩
  have hosc : ∀ y ∈ ball x r, ∀ z ∈ ball x r,
      ‖iteratedFDeriv ℝ n f y - iteratedFDeriv ℝ n f z‖ ≤ η * n ! := by
    intro y hy z hz
    calc ‖iteratedFDeriv ℝ n f y - iteratedFDeriv ℝ n f z‖
        ≤ ‖iteratedFDeriv ℝ n f y - iteratedFDeriv ℝ n f x‖ +
          ‖iteratedFDeriv ℝ n f z - iteratedFDeriv ℝ n f x‖ := by
          rw [norm_sub_rev (iteratedFDeriv ℝ n f z)]
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ η * n ! := by linarith [(hball y hy).2, (hball z hz).2]
  have hxs : x + h ∈ ball x r := by simpa [mem_ball, dist_eq_norm] using hh
  have key := norm_sub_taylorPolynomial_le_of_holder (convex_ball x r)
    (fun y hy => (hball y hy).1) le_rfl (iteratedFDerivHolderOn_zero_of_norm_sub_le hosc)
    (mem_ball_self hr) hxs
  rwa [holderFactorial_zero_right, add_zero, Real.rpow_natCast, mul_div_cancel_right₀ _ hfac.ne']
    at key

/-- **Taylor's theorem with Peano remainder** ([cartis2022evaluation], (A.12)). If `f` is `C^n`
at `x`, then `f(x + h) - T_{f,n}(x, h) = o(‖h‖^n)` as `h → 0`. -/
theorem sub_taylorPolynomial_isLittleO (hf : ContDiffAt ℝ n f x) :
    (fun h => f (x + h) - taylorPolynomial f n x h) =o[𝓝 0] fun h => ‖h‖ ^ n := by
  refine isLittleO_iff.2 fun η hη => ?_
  obtain ⟨r, hr, hbound⟩ := exists_norm_sub_taylorPolynomial_le hf hη
  filter_upwards [ball_mem_nhds (0 : E) hr] with h hh
  rw [mem_ball_zero_iff] at hh
  simpa [abs_of_nonneg (pow_nonneg (norm_nonneg h) n)] using hbound h hh
