import Numlib.LinearSolve.Stationary.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Fixed-point iterations

Glue around Mathlib's `ContractingWith` for the Banach fixed-point theorem with the a priori,
a posteriori and linear-rate bounds (Atkinson–Han Thm 5.1.3 (5.1.4)–(5.1.6), Kress Thm 3.45–3.46),
the `T^m`-contraction variant (AH Ex 5.1.2, Kress Problem 3.17), the derivative criterion
`sup ‖T'‖ < 1` (Kress Thm 6.8), and Zarantonello's theorem for strongly monotone Lipschitz maps on
Hilbert spaces (AH Thm 5.1.4, the nonlinear Lax–Milgram).
-/

open Filter Topology

section Metric

variable {α : Type*} [MetricSpace α]

namespace ContractingWith

variable {K : NNReal} {f : α → α}

/-- Linear rate (AH (5.1.6)): `dist (f^[n+1] x) x* ≤ K dist (f^[n] x) x*`. -/
theorem dist_iterate_succ_fixedPoint_le [Nonempty α] [CompleteSpace α] (hf : ContractingWith K f)
    (x : α) (n : ℕ) :
    dist (f^[n + 1] x) (fixedPoint f hf) ≤ K * dist (f^[n] x) (fixedPoint f hf) := by
  sorry

end ContractingWith

/-- Banach fixed point on a closed subset mapped into itself (AH Thm 5.1.3 / Kress Thm 3.45
setting): existence and uniqueness in the set. -/
theorem exists_unique_fixedPoint_of_mapsTo [CompleteSpace α] {f : α → α} {s : Set α}
    (hs : IsClosed s) (hne : s.Nonempty) (hmaps : Set.MapsTo f s s) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : K < 1) (hf : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y) :
    ∃! x, x ∈ s ∧ f x = x := by
  sorry

/-- A priori bound (5.1.4) on a closed invariant subset. -/
theorem dist_iterate_le_of_mapsTo [CompleteSpace α] {f : α → α} {s : Set α} (hs : IsClosed s)
    (hmaps : Set.MapsTo f s s) {K : ℝ} (hK0 : 0 ≤ K) (hK : K < 1)
    (hf : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y) {x' : α} (hx' : x' ∈ s)
    (hfix : f x' = x') {x₀ : α} (hx₀ : x₀ ∈ s) (n : ℕ) :
    dist (f^[n] x₀) x' ≤ K ^ n / (1 - K) * dist (f x₀) x₀ := by
  sorry

/-- AH Ex 5.1.2 / Kress Problem 3.17: a continuous `T` whose iterate `T^[m]` is a contraction has
a unique fixed point, and `T^[n] x → x*` for every `x`. -/
theorem exists_unique_fixedPoint_of_iterate_contractingWith [CompleteSpace α] {T : α → α}
    (hT : Continuous T) {m : ℕ} (hm : 0 < m) {K : NNReal} (hK : ContractingWith K T^[m]) :
    ∃! x, T x = x := by
  sorry

theorem tendsto_iterate_of_iterate_contractingWith [CompleteSpace α] {T : α → α}
    (hT : Continuous T) {m : ℕ} (hm : 0 < m) {K : NNReal} (hK : ContractingWith K T^[m]) (x : α) :
    ∃ x', T x' = x' ∧ Tendsto (fun n => T^[n] x) atTop (𝓝 x') := by
  sorry

end Metric

section Derivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Kress Thm 6.8 / AH Thm 5.2.1 criterion: a differentiable self-map of a convex set with
`sup ‖T'‖ ≤ q` is `q`-Lipschitz there, hence a contraction when `q < 1`
(Mathlib: `Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le`). -/
theorem lipschitzOnWith_of_hasFDerivWithinAt {T : E → E} {T' : E → E →L[ℝ] E} {s : Set E}
    (hs : Convex ℝ s) (hT : ∀ x ∈ s, HasFDerivWithinAt T (T' x) s x) {q : NNReal}
    (hT' : ∀ x ∈ s, ‖T' x‖₊ ≤ q) : LipschitzOnWith q T s := by
  sorry

end Derivative

section Zarantonello

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Zarantonello / AH Thm 5.1.4: a strongly monotone Lipschitz map on a Hilbert space is
bijective, with `‖x₁ - x₂‖ ≤ ‖T x₁ - T x₂‖ / c`. -/
theorem zarantonello {T : E → E} {c L : ℝ} (hc : 0 < c)
    (hmono : ∀ x y, c * ‖x - y‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T x - T y) (x - y)))
    (hlip : LipschitzWith (Real.toNNReal L) T) (b : E) : ∃! x, T x = b := by
  sorry

/-- The damped iteration `x ↦ x - θ (T x - b)` contracts with factor `√(1 - 2θc + θ²L²)` for
`0 < θ < 2c/L²` (AH proof of Thm 5.1.4; Lax–Milgram proof #1). -/
theorem contractingWith_damped {T : E → E} {c L : ℝ} (hc : 0 < c) (hL : 0 < L)
    (hmono : ∀ x y, c * ‖x - y‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T x - T y) (x - y)))
    (hlip : LipschitzWith (Real.toNNReal L) T) (b : E) {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ < 2 * c / L ^ 2) :
    ContractingWith (Real.toNNReal (Real.sqrt (1 - 2 * θ * c + θ ^ 2 * L ^ 2)))
      (fun x => x - (θ : 𝕜) • (T x - b)) := by
  sorry

/-- Lipschitz dependence on the right-hand side (AH (5.1.11)). -/
theorem norm_sub_le_of_strongly_monotone {T : E → E} {c : ℝ} (hc : 0 < c)
    (hmono : ∀ x y, c * ‖x - y‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T x - T y) (x - y))) {x₁ x₂ b₁ b₂ : E}
    (h₁ : T x₁ = b₁) (h₂ : T x₂ = b₂) : ‖x₁ - x₂‖ ≤ ‖b₁ - b₂‖ / c := by
  sorry

end Zarantonello
