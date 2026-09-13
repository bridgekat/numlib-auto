import Mathlib.Analysis.ODE.DiscreteGronwall
import Mathlib.Analysis.Normed.Group.Basic

/-!
# The discrete Gronwall lemma in summed form

Mathlib's `discrete_gronwall` (`Mathlib/Analysis/ODE/DiscreteGronwall.lean`) is the *recursive*
form of the discrete Gronwall inequality: from `u (n + 1) ≤ (1 + c n) * u n + b n` it concludes
`u n ≤ (u n₀ + ∑ b) * exp (∑ c)`. The numerical-analysis books state the lemma in *summed* form
([quarteroni2000numerical] Lemma 11.2, which cites Quarteroni–Valli for the proof): from
`φ n ≤ g₀ + ∑_{s < n} p s + ∑_{s < n} k s * φ s` conclude
`φ n ≤ (g₀ + ∑_{s < n} p s) * exp (∑_{s < n} k s)`. The summed form is a corollary of the recursive
one applied to the majorant `ψ n = g₀ + ∑_{s < n} p s + ∑_{s < n} k s * φ s`, which satisfies
`φ n ≤ ψ n` and `ψ (n + 1) = ψ n + p n + k n * φ n ≤ (1 + k n) * ψ n + p n`; that is
`Gronwall.discrete_sum`. The two specializations the one-step theory uses are the
constant-coefficient case `p s = h δ`, `k s = h Λ` with the sums evaluated
(`Gronwall.discrete_sum_const`, the shape of the estimates of [quarteroni2000numerical] Theorems
11.1 and 11.2) and the norm form for a sequence in a normed group (`Gronwall.norm_discrete_sum`).
The `_of_le` variants assume the summed inequality only up to a horizon `N` and conclude up to
`N`, which is what a recursion controlled only while the grid nodes stay in the time interval
delivers.

The book states the hypothesis as `φ 0 ≤ g₀` together with the summed bound for `n ≥ 1`; since
the sums are empty at `n = 0`, this is the single hypothesis `∀ n, φ n ≤ …` used here. No sign
condition on `φ` is needed.
-/

open Finset Real

namespace Gronwall

/-- **Discrete Gronwall lemma, summed form** ([quarteroni2000numerical] Lemma 11.2). Let
`0 ≤ g₀`, `0 ≤ k s` and `0 ≤ p s` for all `s`, and suppose
`φ n ≤ g₀ + ∑ s ∈ range n, p s + ∑ s ∈ range n, k s * φ s` for every `n` (at `n = 0` this is
`φ 0 ≤ g₀`). Then `φ n ≤ (g₀ + ∑ s ∈ range n, p s) * exp (∑ s ∈ range n, k s)` for every `n`. -/
theorem discrete_sum {φ k p : ℕ → ℝ} {g₀ : ℝ} (hg₀ : 0 ≤ g₀) (hk : ∀ s, 0 ≤ k s)
    (hp : ∀ s, 0 ≤ p s)
    (h : ∀ n, φ n ≤ g₀ + ∑ s ∈ range n, p s + ∑ s ∈ range n, k s * φ s) (n : ℕ) :
    φ n ≤ (g₀ + ∑ s ∈ range n, p s) * exp (∑ s ∈ range n, k s) := by
  set ψ : ℕ → ℝ := fun n => g₀ + ∑ s ∈ range n, p s + ∑ s ∈ range n, k s * φ s with hψ
  have hψ0 : ψ 0 = g₀ := by simp [ψ]
  have hrec : ∀ m ≥ 0, ψ (m + 1) ≤ (1 + k m) * ψ m + p m := by
    intro m _
    have : ψ (m + 1) = ψ m + p m + k m * φ m := by
      simp only [ψ, sum_range_succ]
      ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left (h m) (hk m)]
  have key := discrete_gronwall (u := ψ) (b := p) (c := k) (n₀ := 0) (hψ0 ▸ hg₀) hrec
    (fun m _ => hk m) (fun m _ => hp m) (Nat.zero_le n)
  rw [hψ0, ← range_eq_Ico] at key
  exact (h n).trans key

/-- **Discrete Gronwall lemma on a finite horizon**: the summed hypothesis is only needed for
`n ≤ N`, and the conclusion holds for `n ≤ N`. This is the form the one-step and multistep
theories use, where the recursion is controlled only while the nodes stay in the time interval.
Proof: the sequence `φ' n = if n ≤ N then max (φ n) 0 else 0` satisfies the hypothesis of
`discrete_sum` for every `n` (the right-hand side is nonnegative, and `φ ≤ φ'` below `N`). -/
theorem discrete_sum_of_le {φ k p : ℕ → ℝ} {g₀ : ℝ} {N : ℕ} (hg₀ : 0 ≤ g₀) (hk : ∀ s, 0 ≤ k s)
    (hp : ∀ s, 0 ≤ p s)
    (h : ∀ n ≤ N, φ n ≤ g₀ + ∑ s ∈ range n, p s + ∑ s ∈ range n, k s * φ s) {n : ℕ}
    (hn : n ≤ N) : φ n ≤ (g₀ + ∑ s ∈ range n, p s) * exp (∑ s ∈ range n, k s) := by
  set φ' : ℕ → ℝ := fun m => if m ≤ N then max (φ m) 0 else 0 with hφ'
  have hφ'0 : ∀ m, 0 ≤ φ' m := fun m => by
    simp only [φ']; split_ifs <;> simp
  have hle : ∀ m ≤ N, φ m ≤ φ' m := fun m hm => by
    simp only [φ', hm, ite_true]; exact le_max_left _ _
  have hsum : ∀ m, φ' m ≤ g₀ + ∑ s ∈ range m, p s + ∑ s ∈ range m, k s * φ' s := by
    intro m
    have hnn : 0 ≤ g₀ + ∑ s ∈ range m, p s + ∑ s ∈ range m, k s * φ' s :=
      add_nonneg (add_nonneg hg₀ (sum_nonneg fun s _ => hp s))
        (sum_nonneg fun s _ => mul_nonneg (hk s) (hφ'0 s))
    have hm' : φ' m = if m ≤ N then max (φ m) 0 else 0 := rfl
    rw [hm']
    split_ifs with hm
    · refine max_le ((h m hm).trans ?_) hnn
      exact add_le_add_right (sum_le_sum fun s hs =>
        mul_le_mul_of_nonneg_left (hle s ((mem_range.1 hs).le.trans hm)) (hk s)) _
    · exact hnn
  exact (hle n hn).trans (discrete_sum hg₀ hk hp hsum n)

/-- The constant-coefficient discrete Gronwall lemma, in the shape of the estimates of
[quarteroni2000numerical] Theorems 11.1 and 11.2: if `0 ≤ g₀`, `0 ≤ h`, `0 ≤ δ`, `0 ≤ Λ` and
`φ n ≤ g₀ + n * h * δ + h * Λ * ∑ s ∈ range n, φ s` for every `n`, then
`φ n ≤ (g₀ + n * h * δ) * exp (n * h * Λ)` for every `n`. This is `discrete_sum` with
`p s = h * δ`, `k s = h * Λ` and the constant sums evaluated. -/
theorem discrete_sum_const {φ : ℕ → ℝ} {g₀ h δ Λ : ℝ} (hg₀ : 0 ≤ g₀) (hh : 0 ≤ h) (hδ : 0 ≤ δ)
    (hΛ : 0 ≤ Λ) (hφ : ∀ n, φ n ≤ g₀ + n * h * δ + h * Λ * ∑ s ∈ range n, φ s) (n : ℕ) :
    φ n ≤ (g₀ + n * h * δ) * exp (n * h * Λ) := by
  have key := discrete_sum (φ := φ) (k := fun _ => h * Λ) (p := fun _ => h * δ) hg₀
    (fun _ => mul_nonneg hh hΛ) (fun _ => mul_nonneg hh hδ) (fun m => by
      simpa [sum_const, card_range, nsmul_eq_mul, mul_sum, mul_assoc] using hφ m) n
  simpa [sum_const, card_range, nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using key

/-- The constant-coefficient discrete Gronwall lemma on a finite horizon: if `0 ≤ g₀`, `0 ≤ h`,
`0 ≤ δ`, `0 ≤ Λ` and `φ n ≤ g₀ + n * h * δ + h * Λ * ∑ s ∈ range n, φ s` for every `n ≤ N`, then
`φ n ≤ (g₀ + n * h * δ) * exp (n * h * Λ)` for every `n ≤ N`. -/
theorem discrete_sum_const_of_le {φ : ℕ → ℝ} {g₀ h δ Λ : ℝ} {N : ℕ} (hg₀ : 0 ≤ g₀) (hh : 0 ≤ h)
    (hδ : 0 ≤ δ) (hΛ : 0 ≤ Λ)
    (hφ : ∀ n ≤ N, φ n ≤ g₀ + n * h * δ + h * Λ * ∑ s ∈ range n, φ s) {n : ℕ} (hn : n ≤ N) :
    φ n ≤ (g₀ + n * h * δ) * exp (n * h * Λ) := by
  have key := discrete_sum_of_le (φ := φ) (k := fun _ => h * Λ) (p := fun _ => h * δ) hg₀
    (fun _ => mul_nonneg hh hΛ) (fun _ => mul_nonneg hh hδ) (fun m hm => by
      simpa [sum_const, card_range, nsmul_eq_mul, mul_sum, mul_assoc] using hφ m hm) hn
  simpa [sum_const, card_range, nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using key

variable {E : Type*} [SeminormedAddGroup E]

/-- **Discrete Gronwall lemma for a sequence in a normed group**: if `0 ≤ g₀`, `0 ≤ k s`,
`0 ≤ p s` and `‖w n‖ ≤ g₀ + ∑ s ∈ range n, p s + ∑ s ∈ range n, k s * ‖w s‖` for every `n`, then
`‖w n‖ ≤ (g₀ + ∑ s ∈ range n, p s) * exp (∑ s ∈ range n, k s)`. This is `discrete_sum` applied to
`‖w ·‖`; every consumer applies it to the difference of two orbits. -/
theorem norm_discrete_sum {w : ℕ → E} {k p : ℕ → ℝ} {g₀ : ℝ} (hg₀ : 0 ≤ g₀) (hk : ∀ s, 0 ≤ k s)
    (hp : ∀ s, 0 ≤ p s)
    (h : ∀ n, ‖w n‖ ≤ g₀ + ∑ s ∈ range n, p s + ∑ s ∈ range n, k s * ‖w s‖) (n : ℕ) :
    ‖w n‖ ≤ (g₀ + ∑ s ∈ range n, p s) * exp (∑ s ∈ range n, k s) :=
  discrete_sum hg₀ hk hp h n

end Gronwall
