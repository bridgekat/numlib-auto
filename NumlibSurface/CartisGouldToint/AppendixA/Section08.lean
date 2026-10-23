import Numlib.Analysis.Calculus.Taylor.ScalarRemainder
import Numlib.Analysis.Calculus.ContDiff.Lipschitz
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Cartis–Gould–Toint, Appendix A.8: Taylor remainder identities

Theorems A.8.1 and A.8.2 are the scalar integral and Lagrange Taylor formulas. Theorem A.8.5
relates Lipschitz continuity of an iterated derivative to a bound on the next derivative.
Ordinary derivatives at the interval endpoints are obtained from smoothness on an open
neighborhood. The integral formula explicitly assumes positive Taylor order, as its
factorial and kernel require; zero increments are allowed in both formulas.
-/

open Set
open scoped BigOperators

namespace CartisGouldToint

/-- **Theorem A.8.1.** The error after degree `k` is the integral of the variation of
the `k`-th derivative against `(h - ξ)^(k-1)/(k-1)!`. The positive order condition is
necessary for the factorial and Taylor kernel in equation (A.9). -/
theorem theorem_A_8_1 {ψ : ℝ → ℝ} {k : ℕ} (hk : 0 < k) {t h : ℝ} (hh : 0 ≤ h)
    {D : Set ℝ} (hD : IsOpen D) (hsub : Icc t (t + h) ⊆ D)
    (hψ : ContDiffOn ℝ k ψ D) :
    ψ (t + h) -
        (∑ i ∈ Finset.range (k + 1), h ^ i / i.factorial * iteratedDeriv i ψ t) =
      1 / ((k - 1).factorial : ℝ) * ∫ ξ in 0..h,
        (h - ξ) ^ (k - 1) * (iteratedDeriv k ψ (t + ξ) - iteratedDeriv k ψ t) := by
  cases k with
  | zero => omega
  | succ n =>
    have hf : ∀ x ∈ uIcc 0 h, ContDiffAt ℝ (n + 1) (fun ξ => ψ (t + ξ)) x := by
      intro x hx
      rw [uIcc_of_le hh] at hx
      have htx : t + x ∈ D := hsub ⟨by linarith [hx.1], by linarith [hx.2]⟩
      exact (hψ.contDiffAt (hD.mem_nhds htx)).comp x
        (contDiff_const.add contDiff_id).contDiffAt
    have hrem := sub_sum_eq_integral_iteratedDeriv_sub hf
    simpa only [iteratedDeriv_comp_const_add, add_zero, Nat.succ_eq_add_one,
      Nat.add_sub_cancel] using hrem

/-- **Theorem A.8.2 (Lagrange form).** The error of the degree-`k` Taylor polynomial
is the `(k + 1)`-st derivative at an intermediate point times `h^(k+1)/(k+1)!`.
The closed-interval witness also covers `h = 0`. -/
theorem theorem_A_8_2 {ψ : ℝ → ℝ} {k : ℕ} {t h : ℝ} (hh : 0 ≤ h)
    {D : Set ℝ} (hD : IsOpen D) (hsub : Icc t (t + h) ⊆ D)
    (hψ : ContDiffOn ℝ (k + 1) ψ D) :
    ∃ ξ ∈ Icc t (t + h), ψ (t + h) -
        (∑ i ∈ Finset.range (k + 1), h ^ i / i.factorial * iteratedDeriv i ψ t) =
      iteratedDeriv (k + 1) ψ ξ * h ^ (k + 1) / (k + 1).factorial := by
  have hth : t ≤ t + h := le_add_of_nonneg_right hh
  have ht : t ∈ D := hsub ⟨le_rfl, hth⟩
  have ha := (hψ.contDiffAt (hD.mem_nhds ht)).of_le
    (show (k : WithTop ℕ∞) ≤ k + 1 by exact_mod_cast Nat.le_succ k)
  have hf : ContDiffOn ℝ (k + 1) ψ (uIcc t (t + h)) := by
    rw [uIcc_of_le hth]
    exact hψ.mono hsub
  obtain ⟨ξ,hξ,heq⟩ := exists_sub_sum_eq_iteratedDeriv_mul ha hf
  rw [uIcc_of_le hth] at hξ
  exact ⟨ξ,hξ,by simpa using heq⟩

/-- **Theorem A.8.5.** On an open convex set, the `p`-th derivative is `L`-Lipschitz
if and only if the norm of the `(p + 1)`-st derivative is bounded by the same `L`.
All norms are the induced multilinear operator norms of the derivative tensors. -/
theorem theorem_A_8_5 {n p : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hC : IsOpen C) (hconv : Convex ℝ C) (hf : ContDiffOn ℝ (p + 1) f C) :
    (∀ x ∈ C, ∀ y ∈ C, ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤
      L * ‖x - y‖) ↔ ∀ x ∈ C, ‖iteratedFDeriv ℝ (p + 1) f x‖ ≤ L := by
  constructor
  · intro h
    exact (lipschitzOnWith_iteratedFDeriv_iff_norm_le (L := ⟨L, hL⟩) hC hconv hf).1
      (lipschitzOnWith_iff_norm_sub_le.2 h)
  · intro h
    exact ((lipschitzOnWith_iteratedFDeriv_iff_norm_le (L := ⟨L, hL⟩) hC hconv hf).2 h).norm_sub_le

end CartisGouldToint
