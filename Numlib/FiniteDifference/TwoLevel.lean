import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Two-level difference schemes: consistency and stability give convergence

A *two-level scheme* advances an approximation by a fixed amplification operator and a source
term, `v^{m+1} = Q v^m + h g^m`, where `h` is the step in the evolution variable.  The exact values
`u^m` of the problem being approximated satisfy the same recursion up to a local truncation error,
`u^{m+1} = Q u^m + h g^m + h τ^m`.  Subtracting, the error `e^m = u^m - v^m` obeys
`e^{m+1} = Q e^m + h τ^m` with `e^0 = 0`, whose closed form is

  `e^m = h ∑_{l < m} Q^{m - 1 - l} τ^l`.

So the whole theory of this scheme is a geometric-sum estimate: if the powers of `Q` are bounded
by `M₀` up to step `N` (*stability*) and the truncation errors are bounded by `δ`
(*consistency*), then over a fixed horizon `N h ≤ T` the error never exceeds `M₀ T δ`.  That is
`FiniteDifference.norm_sub_le_of_stable`, and it is the only content of the module.

The statement is an inequality with explicit constants: no limit, no order symbol, and no family
indexed by a mesh parameter.  Consistency, order, stability and convergence *of a family* of
schemes as the mesh is refined are each this inequality together with a limit, and belong wherever
that family is defined.  The space is a real normed space, because the step `h` is a real scalar
acting on its elements.

The result is Theorem 6.3.2 of Atkinson–Han[^atkinson-han], where `δ = c (h_x^{p₁} + h^{p₂})`
turns it into the convergence order of a scheme.

## References

[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
-/

namespace FiniteDifference

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Convergence of a stable, consistent two-level scheme.**  Let `Q : E →L[ℝ] E`, let the
computed values `v` satisfy `v^{m+1} = Q v^m + h g^m` and the exact values `u` satisfy
`u^{m+1} = Q u^m + h g^m + h τ^m` for `m < N`, with the same starting value.  If the scheme is
stable up to step `N`, `‖Q ^ m‖ ≤ M₀` for `m ≤ N`, the horizon is finite, `N h ≤ T`, and the local
truncation errors satisfy `‖τ^m‖ ≤ δ`, then

  `‖u^m - v^m‖ ≤ M₀ * T * δ`  for every `m ≤ N`.

The bound is uniform in `m`: the error accumulates linearly in the number of steps, and `N h ≤ T`
converts that into a constant depending only on the horizon. -/
theorem norm_sub_le_of_stable {Q : E →L[ℝ] E} {u v g τ : ℕ → E} {h T M₀ δ : ℝ} {N : ℕ}
    (hh : 0 ≤ h) (hδ : 0 ≤ δ) (hT : (N : ℝ) * h ≤ T)
    (hv : ∀ m < N, v (m + 1) = Q (v m) + h • g m)
    (hu : ∀ m < N, u (m + 1) = Q (u m) + h • g m + h • τ m) (h0 : u 0 = v 0)
    (hQ : ∀ m ≤ N, ‖Q ^ m‖ ≤ M₀) (hτ : ∀ m < N, ‖τ m‖ ≤ δ) {m : ℕ} (hm : m ≤ N) :
    ‖u m - v m‖ ≤ M₀ * T * δ := by
  have hM₀ : 0 ≤ M₀ := le_trans (norm_nonneg _) (hQ 0 (Nat.zero_le N))
  have key : ∀ k, k ≤ N → u k - v k = h • ∑ l ∈ Finset.range k, (Q ^ (k - 1 - l)) (τ l) := by
    intro k
    induction k with
    | zero => intro _; simp [h0]
    | succ n ih =>
      intro hk
      have hnN : n < N := hk
      have hn := ih (Nat.le_of_succ_le hk)
      have hstep : Q (u n) + h • g n + h • τ n - (Q (v n) + h • g n)
          = Q (u n - v n) + h • τ n := by
        rw [map_sub]
        abel
      have hrhs : ∑ l ∈ Finset.range (n + 1), (Q ^ (n + 1 - 1 - l)) (τ l)
          = (∑ l ∈ Finset.range n, Q ((Q ^ (n - 1 - l)) (τ l))) + τ n := by
        rw [Finset.sum_range_succ]
        congr 1
        · refine Finset.sum_congr rfl fun l hl => ?_
          have hl' : l < n := Finset.mem_range.mp hl
          have hidx : n + 1 - 1 - l = n - 1 - l + 1 := by omega
          rw [hidx, pow_succ']
          rfl
        · simp
      rw [hu n hnN, hv n hnN, hstep, hn, map_smul, map_sum, hrhs, smul_add]
  have hsum : ‖∑ l ∈ Finset.range m, (Q ^ (m - 1 - l)) (τ l)‖ ≤ (m : ℝ) * (M₀ * δ) := by
    calc ‖∑ l ∈ Finset.range m, (Q ^ (m - 1 - l)) (τ l)‖
        ≤ ∑ l ∈ Finset.range m, ‖(Q ^ (m - 1 - l)) (τ l)‖ := norm_sum_le _ _
      _ ≤ ∑ _l ∈ Finset.range m, M₀ * δ := by
          refine Finset.sum_le_sum fun l hl => ?_
          have hl' : l < m := Finset.mem_range.mp hl
          exact le_trans (ContinuousLinearMap.le_opNorm _ _)
            (mul_le_mul (hQ _ (by omega)) (hτ l (by omega)) (norm_nonneg _) hM₀)
      _ = (m : ℝ) * (M₀ * δ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmh : (m : ℝ) * h ≤ T :=
    le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hh) hT
  rw [key m hm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
  calc h * ‖∑ l ∈ Finset.range m, (Q ^ (m - 1 - l)) (τ l)‖ ≤ h * ((m : ℝ) * (M₀ * δ)) :=
        mul_le_mul_of_nonneg_left hsum hh
    _ = (m : ℝ) * h * (M₀ * δ) := by ring
    _ ≤ T * (M₀ * δ) := mul_le_mul_of_nonneg_right hmh (mul_nonneg hM₀ hδ)
    _ = M₀ * T * δ := by ring

end FiniteDifference
