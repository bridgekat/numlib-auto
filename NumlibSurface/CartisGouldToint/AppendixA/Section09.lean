import Numlib.Approximation.Hermite
import Numlib.Approximation.HermiteSpline

/-!
# Cartis–Gould–Toint §A.9: Polynomial Hermite interpolation

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §A.9.

Jets are sequences `f₀ f₁ : ℕ → ℝ` (`f₀ j = f₀^{(j)}`), the `j`-th derivative of a polynomial `π`
is `derivative^[j] π`, and the `j`-th derivative of the Taylor polynomial of the left jet,
`T^{(j)}_{f,p}(0, s) = ∑_{i=j}^p f₀^{(i)} s^{i-j}/(i-j)!`, is written out as a sum. The proofs
specialize `Numlib/Approximation/HermiteSpline`.

## Main results

* `theorem_A_9_1` — the Hermite interpolant of degree `2p + 1` on `[0, s]` exists, is unique, has
  a Lipschitz `p`-th derivative under (A.30), and bounded derivatives under (A.31), with constants
  depending only on `p` and `κ_f`.
* `theorem_A_9_2` — a `C^p` interpolant on `ℝ` of jets at nodes `x_0 < ⋯ < x_{k_e}` with
  Lipschitz `p`-th derivative under (A.32), and bounded derivatives under the additional bounds.

In Theorem A.9.2 the same interpolant satisfies both conclusions: it has the Lipschitz constant
`L` in any case and, when the additional bounds hold, the derivative bound `B`.

## Deviations from the book

* Theorem A.9.2 is stated for every `p` (the book assumes `p > 0`, which the proof does not use).
  The book's hypothesis `s_k > 0` "for `k ∈ [0 : k_e]`" is read for `k < k_e` (the only `s_k`
  defined by the data), and its bound "for all `x ∈ ℝⁿ`" is for `x ∈ ℝ`.
-/

open Polynomial Set
open scoped Polynomial

namespace CartisGouldToint.AppendixA

/-- **Theorem A.9.1 (General Hermite interpolation on an interval)** of [cartis2022evaluation].
For every `p` and `κ_f ≥ 0` there are constants `L, B ≥ 0`, depending only on `p` and `κ_f`, such
that: for `s > 0` and jets `f₀, f₁` satisfying (A.30)
`|f₁^{(j)} - T^{(j)}_{f,p}(0, s)| ≤ κ_f s^{p-j+1}` (`j ∈ [0 : p]`), the Hermite interpolation
polynomial `π` of degree `2p + 1` with (A.24) `π^{(j)}(0) = f₀^{(j)}`, `π^{(j)}(s) = f₁^{(j)}`
exists and is unique; its `p`-th derivative is `L`-Lipschitz on `[0, s]`; and if moreover (A.31)
`|f₀^{(j)}| ≤ κ_f` (`j ∈ [0 : p]`) and `s ≤ κ_f`, then `|π^{(j)}(τ)| ≤ B` on `[0, s]` for
`j ∈ [0 : p]`. -/
theorem theorem_A_9_1 (p : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) : ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧
    ∀ (s : ℝ) (f₀ f₁ : ℕ → ℝ), 0 < s →
      (∀ j ≤ p, |f₁ j - ∑ i ∈ Finset.Icc j p, f₀ i * s ^ (i - j) / (i - j).factorial| ≤
        κ * s ^ (p - j + 1)) →
      (∃! π : ℝ[X], π.natDegree ≤ 2 * p + 1 ∧ (∀ j ≤ p, (derivative^[j] π).eval 0 = f₀ j) ∧
        ∀ j ≤ p, (derivative^[j] π).eval s = f₁ j) ∧
      ∀ π : ℝ[X], π.natDegree ≤ 2 * p + 1 → (∀ j ≤ p, (derivative^[j] π).eval 0 = f₀ j) →
        (∀ j ≤ p, (derivative^[j] π).eval s = f₁ j) →
        (∀ τ₁ ∈ Icc 0 s, ∀ τ₂ ∈ Icc 0 s,
          |(derivative^[p] π).eval τ₁ - (derivative^[p] π).eval τ₂| ≤ L * |τ₁ - τ₂|) ∧
        ((∀ j ≤ p, |f₀ j| ≤ κ) → s ≤ κ →
          ∀ j ≤ p, ∀ τ ∈ Icc 0 s, |(derivative^[j] π).eval τ| ≤ B) := by
  obtain ⟨C, hC, htwo⟩ := Hermite.exists_twoPoint_interpolant p
  obtain ⟨C', hC', htwo'⟩ := Hermite.exists_twoPoint_interpolant_bounded p
  refine ⟨C * κ, (p + 1) * κ * max 1 κ ^ p + C' * κ * max 1 κ ^ (p + 1), mul_nonneg hC hκ,
    by positivity, fun s f₀ f₁ hs hcons => ?_⟩
  obtain ⟨π₀, hdeg₀, h0₀, h1₀, -, hlip₀⟩ := htwo s κ f₀ f₁ hs hcons
  have huniq : ∀ π : ℝ[X], π.natDegree ≤ 2 * p + 1 → (∀ j ≤ p, (derivative^[j] π).eval 0 = f₀ j) →
      (∀ j ≤ p, (derivative^[j] π).eval s = f₁ j) → π = π₀ := fun π hdeg h0 h1 =>
    Hermite.eq_of_twoPoint_jets hs.ne' hdeg hdeg₀ (fun j hj => (h0 j hj).trans (h0₀ j hj).symm)
      (fun j hj => (h1 j hj).trans (h1₀ j hj).symm)
  refine ⟨⟨π₀, ⟨hdeg₀, h0₀, h1₀⟩, fun π ⟨hdeg, h0, h1⟩ => huniq π hdeg h0 h1⟩,
    fun π hdeg h0 h1 => ?_⟩
  obtain rfl := huniq π hdeg h0 h1
  refine ⟨hlip₀, fun hf₀ hsκ j hj τ hτ => ?_⟩
  obtain ⟨π₁, hdeg₁, h0₁, h1₁, hb₁, -⟩ := htwo' s κ f₀ f₁ hs hsκ hf₀ hcons
  obtain rfl := huniq π₁ hdeg₁ h0₁ h1₁
  exact hb₁ j (by omega) τ hτ

/-- **Theorem A.9.2 (General Hermite interpolation)** of [cartis2022evaluation]. For every `p`
and `κ_f ≥ 0` there are constants `L, B ≥ 0`, depending only on `p` and `κ_f`, such that: for
`k_e > 0`, nodes `x_0 < x_1 < ⋯ < x_{k_e}` (`s_k = x_{k+1} - x_k > 0`) and data `f_k^{(j)}`
(`k ∈ [0 : k_e]`, `j ∈ [0 : p]`) satisfying (A.32)
`|f_{k+1}^{(j)} - T^{(j)}_{k,p}(x_k, s_k)| ≤ κ_f s_k^{p-j+1}` with
`T_{k,p}(x_k, s) = ∑_{i=0}^p f_k^{(i)} s^i / i!` (`k ∈ [0 : k_e - 1]`), there is a `p` times
continuously differentiable `f : ℝ → ℝ` with `L`-Lipschitz `p`-th derivative and
`f^{(j)}(x_k) = f_k^{(j)}` for all `k, j`; if moreover `|f_k^{(j)}| ≤ κ_f` and `s_k ≤ κ_f` for
`k ∈ [0 : k_e - 1]`, then `|f^{(j)}(x)| ≤ B` for all `x ∈ ℝ` and `j ∈ [0 : p]`. -/
theorem theorem_A_9_2 (p : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) : ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧
    ∀ (kₑ : ℕ) (x : ℕ → ℝ) (F : ℕ → ℕ → ℝ), 0 < kₑ → (∀ k < kₑ, x k < x (k + 1)) →
      (∀ k < kₑ, ∀ j ≤ p, |F (k + 1) j - ∑ i ∈ Finset.Icc j p,
        F k i * (x (k + 1) - x k) ^ (i - j) / (i - j).factorial| ≤
          κ * (x (k + 1) - x k) ^ (p - j + 1)) →
      ∃ f : ℝ → ℝ, ContDiff ℝ p f ∧
        (∀ t₁ t₂, |iteratedDeriv p f t₁ - iteratedDeriv p f t₂| ≤ L * |t₁ - t₂|) ∧
        (∀ k ≤ kₑ, ∀ j ≤ p, iteratedDeriv j f (x k) = F k j) ∧
        ((∀ k < kₑ, ∀ j ≤ p, |F k j| ≤ κ) → (∀ k < kₑ, x (k + 1) - x k ≤ κ) →
          ∀ j ≤ p, ∀ t, |iteratedDeriv j f t| ≤ B) := by
  obtain ⟨L₁, hL₁, h₁⟩ := Hermite.exists_contDiff_interpolating_jets p hκ
  obtain ⟨L₂, B, hL₂, hB, h₂⟩ := Hermite.exists_contDiff_interpolating_jets_bounded p hκ
  refine ⟨max L₁ L₂, B, hL₁.trans (le_max_left _ _), hB, fun kₑ x F hk hx hF => ?_⟩
  have hlip : ∀ {L : ℝ} {g : ℝ → ℝ}, L ≤ max L₁ L₂ →
      (∀ t₁ t₂, |iteratedDeriv p g t₁ - iteratedDeriv p g t₂| ≤ L * |t₁ - t₂|) →
      ∀ t₁ t₂, |iteratedDeriv p g t₁ - iteratedDeriv p g t₂| ≤ max L₁ L₂ * |t₁ - t₂| :=
    fun hL hg t₁ t₂ => (hg t₁ t₂).trans (mul_le_mul_of_nonneg_right hL (abs_nonneg _))
  by_cases hbd : (∀ k < kₑ, ∀ j ≤ p, |F k j| ≤ κ) ∧ ∀ k < kₑ, x (k + 1) - x k ≤ κ
  · obtain ⟨g, hg, hgL, hgB, hgF, -⟩ := h₂ kₑ x F hk hx hbd.2 hbd.1 hF
    exact ⟨g, hg, hlip (le_max_right _ _) hgL, hgF, fun _ _ => hgB⟩
  · obtain ⟨g, hg, hgL, hgF⟩ := h₁ kₑ x F hx hF
    exact ⟨g, hg, hlip (le_max_left _ _) hgL, hgF, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ hbd⟩

end CartisGouldToint.AppendixA
