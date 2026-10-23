import Numlib.Analysis.Calculus.Taylor.ScalarRemainder
import Numlib.Analysis.Calculus.ContDiff.Lipschitz
import Numlib.Analysis.Calculus.TaylorModel.Holder
import NumlibSurface.CartisGouldToint.Chapter04.Section01
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Cartis–Gould–Toint, Appendix A.8: Taylor remainder identities

Theorems A.8.1 and A.8.2 are the scalar integral and Lagrange Taylor formulas. Theorem A.8.5
relates Lipschitz continuity of an iterated derivative to a bound on the next derivative.
The separate value-error helpers establish (A.14) and (A.19). The derivative-error clauses
(A.15) and (A.20) of the full Theorem A.8.3 and Corollary A.8.4 remain unformalized.
Ordinary derivatives at the interval endpoints are obtained from smoothness on an open
neighborhood. The integral formula explicitly assumes positive Taylor order, as its
factorial and kernel require; zero increments are allowed in both formulas.
-/

open Set
open scoped BigOperators

namespace CartisGouldToint

/-- The finite shifted factorial used before Theorem A.8.3: the product of `i + β`
for `i = 1, …, k`, with empty product one. -/
noncomputable abbrev shiftedFactorial (k : ℕ) (β : ℝ) : ℝ := Real.shiftedFactorial k β

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

/-- The value-error clause (A.14) of Theorem A.8.3, with its sharp finite-product
constant. This helper does not include the derivative-error assertion (A.15). -/
theorem theorem_A_8_3_value {n p : ℕ} (hp : 0 < p)
    {C D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hCD : C ⊆ D)
    (hC : Convex ℝ C) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ p f D) {H β : ℝ} (hH : 0 ≤ H) (hβ : β ∈ Icc (0 : ℝ) 1)
    (hholder : ∀ u ∈ C, ∀ v ∈ C,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ H * ‖u - v‖ ^ β)
    {x s : EuclideanSpace ℝ (Fin n)} (hx : x ∈ C) (hxs : x + s ∈ C) :
    |f (x + s) - taylorModel f p x s| ≤ H / shiftedFactorial p β * ‖s‖ ^ ((p : ℝ) + β) := by
  cases p with
  | zero => omega
  | succ q =>
    exact TaylorModel.abs_sub_eval_le_holder hD hCD hC hf hH hβ.1 hholder hx hxs

/-- The value-error clause (A.19) of Corollary A.8.4. This helper does not include
the derivative-error assertion (A.20). -/
theorem corollary_A_8_4_value {n p : ℕ} (hp : 0 < p)
    {C D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hCD : C ⊆ D)
    (hC : Convex ℝ C) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ p f D) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ u ∈ C, ∀ v ∈ C,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    {x s : EuclideanSpace ℝ (Fin n)} (hx : x ∈ C) (hxs : x + s ∈ C) :
    |f (x + s) - taylorModel f p x s| ≤ L * ‖s‖ ^ (p + 1) / (p + 1).factorial := by
  cases p with
  | zero => omega
  | succ q =>
    exact TaylorModel.abs_sub_eval_le_lipschitz hD hCD hC hf hL hlip hx hxs

end CartisGouldToint
