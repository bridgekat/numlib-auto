import Numlib.Optimization.Subproblem.Bracketing
import NumlibSurface.CartisGouldToint.Chapter08.Section03

/-!
# Cartis–Gould–Toint §9.2: Finding a point in `𝓛`

Surface file for [cartis2022evaluation] §9.2: Algorithm 9.2.1, safeguarded interval reduction of a
bracket `[λᴸ, λᵁ] ∋ λ*` until a trial value `λ_C` lies in `𝓛`. A run only tests membership of the
trial values in the sets `𝓝`, `𝓛`, `𝓖` of the subproblem, so it is stated for arbitrary sets; for
the subproblems of Chapter 8 these are `setN`, `setL_reg`/`setL_tr`, `setG_reg`/`setG_tr`, which
are `(-∞, λₛ]`, `(λₛ, λ*]` and `(λ*, ∞)` (`CartisGouldToint.Chapter08.setL_reg_eq_Ioc`,
`CartisGouldToint.Chapter08.setL_tr_eq_Ioc`). Under this partition a run is a run of the backbone
`Subproblem.IsBracketRun` (`algorithm_9_2_1.isBracketRun`), which carries the analysis;
`algorithm_9_2_1_terminates_reg` and `algorithm_9_2_1_terminates_tr` state it for the two
subproblems.

## Corrections to the source

* The book bounds the ratio of successive bracket widths by `max(1 - θ, θ, γ √λᵁ/(√λᴸ + √λᵁ))`,
  which is valid but not uniformly below `1`; the uniform factor `max(1 - θ_L, θ_U, 1/2)` is used.
* Finite termination needs the initial lower bound strictly below `λ*`: if `λᴸ = λ*` initially, a
  run need not stop (while `λᵁ > λ*`, every trial value exceeds `λ*` and lies in `𝓖`).
-/

open Set

namespace CartisGouldToint.Chapter09

open Subproblem

/-- A **run of Algorithm 9.2.1** of [cartis2022evaluation] (find `λ ∈ 𝓛`) for the sets `𝓝`, `𝓛`,
`𝓖` of a subproblem with multiplier `λ*` and leftmost pencil eigenvalue `λ₁`, with constants
`0 < θ_L ≤ θ_U < 1`: lower bounds `lo`, upper bounds `hi` and trial values `c` with
`0 ≤ λᴸ ≤ λ* ≤ λᵁ` initially (9.2.1), and at every step `k`:
* if `λ_C ∈ 𝓛` the run has stopped (nothing changes);
* if `λ_C ∈ 𝓝`: `λᴸ ← max(λᴸ, λ_C)`, possibly `λᴸ ← max(λᴸ, -λ_E)` for an estimate `λ_E ≥ λ₁`,
  and `λ_C ← max(γ √(λᴸλᵁ), λᴸ + θ (λᵁ - λᴸ))` for some `θ ∈ [θ_L, θ_U]`, `γ ∈ {0, 1}`;
* if `λ_C ∈ 𝓖`: `λᵁ ← min(λᵁ, λ_C)`, possibly `λᴸ ← max(λᴸ, -λ_E)`, and `λ_C` in the interval
  (9.2.2) for some `θ_l ≤ θ_u` in `[θ_L, θ_U]`, `γ₁ ≤ γ₂` in `{0, 1}`.

The optional improvement by `-λ_E` with `λ_E ≥ λ₁` is `Subproblem.IsLowerUpdate (-λ₁)`. -/
structure algorithm_9_2_1 (setN setL setG : Set ℝ) (lam₁ lamStar θL θU : ℝ)
    (lo hi c : ℕ → ℝ) : Prop where
  /-- The constants satisfy `0 < θ_L ≤ θ_U < 1`. -/
  theta : 0 < θL ∧ θL ≤ θU ∧ θU < 1
  /-- The initial lower bound is nonnegative. -/
  nonneg : 0 ≤ lo 0
  /-- The initial lower bound is at most `λ*` (9.2.1). -/
  lo_zero_le : lo 0 ≤ lamStar
  /-- The initial upper bound is at least `λ*` (9.2.1). -/
  le_hi_zero : lamStar ≤ hi 0
  /-- A trial value in `𝓛` stops the run. -/
  exit : ∀ k, c k ∈ setL → lo (k + 1) = lo k ∧ hi (k + 1) = hi k ∧ c (k + 1) = c k
  /-- A trial value in `𝓝` raises the lower bound. -/
  left : ∀ k, c k ∈ setN → hi (k + 1) = hi k ∧
    IsLowerUpdate (-lam₁) (max (lo k) (c k)) (lo (k + 1)) ∧
    ∃ θ ∈ Icc θL θU, ∃ γ ∈ ({0, 1} : Set ℝ),
      c (k + 1) = bracketEstimate γ θ (lo (k + 1)) (hi (k + 1))
  /-- A trial value in `𝓖` lowers the upper bound. -/
  right : ∀ k, c k ∈ setG → hi (k + 1) = min (hi k) (c k) ∧
    IsLowerUpdate (-lam₁) (lo k) (lo (k + 1)) ∧
    ∃ θl ∈ Icc θL θU, ∃ θu ∈ Icc θL θU, θl ≤ θu ∧ ∃ γ₁ ∈ ({0, 1} : Set ℝ),
      ∃ γ₂ ∈ ({0, 1} : Set ℝ), γ₁ ≤ γ₂ ∧
        c (k + 1) ∈ Icc (bracketEstimate γ₁ θl (lo (k + 1)) (hi (k + 1)))
          (bracketEstimate γ₂ θu (lo (k + 1)) (hi (k + 1)))

variable {setN setL setG : Set ℝ} {lam₁ lamStar θL θU : ℝ} {lo hi c : ℕ → ℝ}

/-- For the partition `𝓝 = (-∞, a]`, `𝓛 = (a, λ*]`, `𝓖 = (λ*, ∞)` with `-λ₁ ≤ a` (as for
`a = λₛ = max(0, -λ₁)`), a run of Algorithm 9.2.1 is a run of `Subproblem.IsBracketRun`. -/
theorem algorithm_9_2_1.isBracketRun {a : ℝ}
    (h : algorithm_9_2_1 setN setL setG lam₁ lamStar θL θU lo hi c) (hN : setN = Iic a)
    (hL : setL = Ioc a lamStar) (hG : setG = Ioi lamStar) (ha : -lam₁ ≤ a) :
    IsBracketRun a lamStar θL θU lo hi c := by
  subst hN hL hG
  refine ⟨h.nonneg, h.lo_zero_le, h.le_hi_zero, h.exit, fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := h.left k hk
    exact ⟨h1, h2.mono ha, h3⟩
  · obtain ⟨h1, h2, h3⟩ := h.right k hk
    exact ⟨h1, h2.mono ha, h3⟩

/-- The deterministic step of Algorithm 9.2.1 with `θ = θ_L`, `γ = 0` and no eigenvalue
estimates, on states `(λᴸ, λᵁ, λ_C)`. -/
private noncomputable def bracketStepCanonical (a b θ : ℝ) (s : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  if a < s.2.2 ∧ s.2.2 ≤ b then s
  else if s.2.2 ≤ a then (max s.1 s.2.2, s.2.1, bracketEstimate 0 θ (max s.1 s.2.2) s.2.1)
  else (s.1, min s.2.1 s.2.2, bracketEstimate 0 θ s.1 (min s.2.1 s.2.2))

/-- **Runs of Algorithm 9.2.1 exist** for the partition `𝓝 = (-∞, a]`, `𝓛 = (a, λ*]`,
`𝓖 = (λ*, ∞)` (`a ≤ λ*`), any constants `0 < θ_L ≤ θ_U < 1`, any initial bounds
`0 ≤ λᴸ ≤ λ* ≤ λᵁ` (9.2.1) and any initial trial value: the run with `θ = θ_L`, `γ = 0` and no
eigenvalue estimates. -/
theorem algorithm_9_2_1_exists {a lo₀ hi₀ c₀ : ℝ} (hN : setN = Iic a)
    (hL : setL = Ioc a lamStar) (hG : setG = Ioi lamStar) (hab : a ≤ lamStar)
    (hθ : 0 < θL ∧ θL ≤ θU ∧ θU < 1) (h0 : 0 ≤ lo₀) (hlo : lo₀ ≤ lamStar)
    (hhi : lamStar ≤ hi₀) :
    ∃ lo hi c : ℕ → ℝ, algorithm_9_2_1 setN setL setG lam₁ lamStar θL θU lo hi c ∧
      lo 0 = lo₀ ∧ hi 0 = hi₀ ∧ c 0 = c₀ := by
  subst hN hL hG
  set s : ℕ → ℝ × ℝ × ℝ := fun k => (bracketStepCanonical a lamStar θL)^[k] (lo₀, hi₀, c₀)
    with hs
  have hsucc : ∀ k, s (k + 1) = bracketStepCanonical a lamStar θL (s k) := fun k => by
    simp only [hs, Function.iterate_succ_apply']
  have hθmem : θL ∈ Icc θL θU := ⟨le_rfl, hθ.2.1⟩
  have h0mem : (0 : ℝ) ∈ ({0, 1} : Set ℝ) := Or.inl rfl
  refine ⟨fun k => (s k).1, fun k => (s k).2.1, fun k => (s k).2.2,
    ⟨hθ, h0, hlo, hhi, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩, rfl, rfl, rfl⟩
  · rw [hsucc, bracketStepCanonical,
      ite_eq_left (show a < (s k).2.2 ∧ (s k).2.2 ≤ lamStar from hk)]
    exact ⟨rfl, rfl, rfl⟩
  · have hn : ¬ (a < (s k).2.2 ∧ (s k).2.2 ≤ lamStar) := fun h => absurd hk (not_le.2 h.1)
    rw [hsucc, bracketStepCanonical, ite_eq_right hn, ite_eq_left (show (s k).2.2 ≤ a from hk)]
    exact ⟨rfl, Or.inl rfl, θL, hθmem, 0, h0mem, rfl⟩
  · have hk' : lamStar < (s k).2.2 := hk
    have hn : ¬ (a < (s k).2.2 ∧ (s k).2.2 ≤ lamStar) := fun h => absurd hk' (not_lt.2 h.2)
    have hn' : ¬ (s k).2.2 ≤ a := fun h => absurd (h.trans hab) (not_le.2 hk')
    rw [hsucc, bracketStepCanonical, ite_eq_right hn, ite_eq_right hn']
    exact ⟨rfl, Or.inl rfl, θL, hθmem, θL, hθmem, le_rfl, 0, h0mem, 0, h0mem, le_rfl,
      le_rfl, le_rfl⟩

/-- **The claims of [cartis2022evaluation] §9.2 on Algorithm 9.2.1**, for the partition
`𝓝 = (-∞, a]`, `𝓛 = (a, λ*]`, `𝓖 = (λ*, ∞)` with `-λ₁ ≤ a ≤ λ*`. The brackets contain `λ*` and
shrink, and after the first step each step not stopped multiplies the bracket width by at most
`ρ = max(1 - θ_L, θ_U, 1/2) < 1`. If `𝓛` is nonempty (`a < λ*`) and the initial lower bound is
`< λ*`, some trial value lies in `𝓛` after at most
`⌈log((λᵁ₁ - λᴸ₁)/(λ* - max(λᴸ₀, a)))/log(1/ρ)⌉₊ + 1` steps. -/
theorem algorithm_9_2_1_terminates {a : ℝ}
    (h : algorithm_9_2_1 setN setL setG lam₁ lamStar θL θU lo hi c) (hN : setN = Iic a)
    (hL : setL = Ioc a lamStar) (hG : setG = Ioi lamStar) (ha : -lam₁ ≤ a)
    (hab : a ≤ lamStar) :
    (∀ k, lo k ≤ lamStar ∧ lamStar ≤ hi k) ∧ Monotone lo ∧ Antitone hi ∧
    max (1 - θL) (max θU (1 / 2)) < 1 ∧
    (∀ k, 1 ≤ k → c k ∉ setL →
      hi (k + 1) - lo (k + 1) ≤ max (1 - θL) (max θU (1 / 2)) * (hi k - lo k)) ∧
    (a < lamStar → lo 0 < lamStar →
      ∃ k ≤ ⌈Real.log ((hi 1 - lo 1) / (lamStar - max (lo 0) a)) /
        Real.log (1 / max (1 - θL) (max θU (1 / 2)))⌉₊ + 1, c k ∈ setL) := by
  have hb := h.isBracketRun hN hL hG ha
  obtain ⟨hθ0, -, hθ1⟩ := h.theta
  obtain ⟨hinv, hlo, hhi, -, -⟩ := hb.invariant hab hθ0.le hθ1.le
  refine ⟨hinv, hlo, hhi, ?_, fun k hk hc => hb.width_le hab hk (hL ▸ hc), fun hlt hlo0 => ?_⟩
  · exact max_lt (by linarith) (max_lt hθ1 (by norm_num))
  · rw [hL]; exact hb.exists_mem hlt hlo0 hθ0 hθ1

/-! ### The subproblems of Chapter 8 -/

open CartisGouldToint.Chapter08

variable {n : ℕ} {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}

/-- **Algorithm 9.2.1 for the regularization subproblem** (8.1.3): with the sets `setN`,
`setL_reg`, `setG_reg` of §8.3.1 and the multiplier `λ* = σ ‖s*‖_M^{r-2}` of a global minimizer,
the conclusions of `algorithm_9_2_1_terminates` hold with `a = λₛ`. -/
theorem algorithm_9_2_1_terminates_reg (hH : H.IsHermitian) (hM : M.PosDef) {σ r : ℝ}
    (hσ : 0 < σ) (hr : 2 < r) {s : EuclideanSpace ℝ (Fin n)}
    (hs : IsRegularizationSolution g H M σ r s)
    (h : algorithm_9_2_1 (Chapter08.setN hH hM) (setL_reg hH hM g σ r) (setG_reg hH hM g σ r)
      (leftmostPencil hH hM) (σ * mNorm M s ^ (r - 2)) θL θU lo hi c) :
    (∀ k, lo k ≤ σ * mNorm M s ^ (r - 2) ∧ σ * mNorm M s ^ (r - 2) ≤ hi k) ∧ Monotone lo ∧
    Antitone hi ∧ max (1 - θL) (max θU (1 / 2)) < 1 ∧
    (∀ k, 1 ≤ k → c k ∉ setL_reg hH hM g σ r →
      hi (k + 1) - lo (k + 1) ≤ max (1 - θL) (max θU (1 / 2)) * (hi k - lo k)) ∧
    (lambdaS hH hM < σ * mNorm M s ^ (r - 2) → lo 0 < σ * mNorm M s ^ (r - 2) →
      ∃ k ≤ ⌈Real.log ((hi 1 - lo 1) / (σ * mNorm M s ^ (r - 2) - max (lo 0) (lambdaS hH hM))) /
        Real.log (1 / max (1 - θL) (max θU (1 / 2)))⌉₊ + 1, c k ∈ setL_reg hH hM g σ r) := by
  obtain ⟨hle, hL, hG, -, -⟩ := setL_reg_eq_Ioc hH hM hσ hr hs
  exact algorithm_9_2_1_terminates h rfl hL hG (neg_leftmostPencil_le_lambdaS hH hM) hle

/-- **Algorithm 9.2.1 for the trust-region subproblem** (8.1.2): with the sets `setN`, `setL_tr`,
`setG_tr` of §8.3.2 and the multiplier `λ*` of a global minimizer, the conclusions of
`algorithm_9_2_1_terminates` hold with `a = λₛ`. -/
theorem algorithm_9_2_1_terminates_tr (hH : H.IsHermitian) (hM : M.PosDef) {Δ : ℝ} (hΔ : 0 < Δ)
    {s : EuclideanSpace ℝ (Fin n)} (hs : IsTrustRegionSolution g H M Δ s) {lamStar : ℝ}
    (hkkt : IsTrustRegionKKT g H M Δ s lamStar)
    (h : algorithm_9_2_1 (Chapter08.setN hH hM) (setL_tr hH hM g Δ) (setG_tr hH hM g Δ)
      (leftmostPencil hH hM) lamStar θL θU lo hi c) :
    (∀ k, lo k ≤ lamStar ∧ lamStar ≤ hi k) ∧ Monotone lo ∧ Antitone hi ∧
    max (1 - θL) (max θU (1 / 2)) < 1 ∧
    (∀ k, 1 ≤ k → c k ∉ setL_tr hH hM g Δ →
      hi (k + 1) - lo (k + 1) ≤ max (1 - θL) (max θU (1 / 2)) * (hi k - lo k)) ∧
    (lambdaS hH hM < lamStar → lo 0 < lamStar →
      ∃ k ≤ ⌈Real.log ((hi 1 - lo 1) / (lamStar - max (lo 0) (lambdaS hH hM))) /
        Real.log (1 / max (1 - θL) (max θU (1 / 2)))⌉₊ + 1, c k ∈ setL_tr hH hM g Δ) := by
  obtain ⟨hle, hL, hG, -⟩ := setL_tr_eq_Ioc hH hM hΔ hs hkkt
  exact algorithm_9_2_1_terminates h rfl hL hG (neg_leftmostPencil_le_lambdaS hH hM) hle

end CartisGouldToint.Chapter09
