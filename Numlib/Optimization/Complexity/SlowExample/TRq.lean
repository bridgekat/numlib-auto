import Numlib.Optimization.ModelBased.HighOrder.TRqComplexity

/-!
# Building runs of TRq for slow examples

Lower-bound constructions for the trust-region method TRq ([cartis2022evaluation],
Algorithm 12.2.1) exhibit runs whose first iterations are written down explicitly and whose
continuation is any run (which exists by `Optimization.exists_isTRqRun`). This file provides the
generic tools for such constructions, for an arbitrary objective on a real normed space:

* `Optimization.TRqParams.withΔ₀`: the parameters with another initial radius, for the run that
  continues an explicit prefix with the radius reached by the prefix;
* `Optimization.exists_isTRqRun_append`: an explicit prefix of iterations satisfying Steps 1–4,
  followed by a run started at its last point with its last radius, is a run; its termination
  tests and its successful iterations are those of the prefix and of the continuation;
* `Optimization.IsTRqRun.congr_of_taylorDecrement_eq`: a run with exact data on a feasible set
  `X` is also a run for any other objective with the same Taylor decrements and the same
  differences of values on `X` (e.g. differing by a constant near `X`).
Runs whose first iterations are unsuccessful stay at their start
(`Optimization.IsTRRun.eq_zero_of_unsucc`, in `Numlib.Optimization.ModelBased.TRRun`).

The data (Taylor data `D y` and feasible displacements `S y`) depend on the current iterate `y`,
as in `Optimization.exists_isTRqRun`.
-/

open Set Metric
open scoped Nat

namespace Optimization

/-- The exact Taylor data `k ↦ ftaylorSeries ℝ f (x k)` along the iterates. -/
local notation "𝒥" f:max x:max => fun k : ℕ => ftaylorSeries ℝ f (x k)

/-- The feasible displacements `k ↦ {e | x k + e ∈ X}`. -/
local notation "𝒳" X:max x:max => fun k : ℕ => Set.ofPred fun e => x k + e ∈ X

/-- The TRq parameters `P` with the initial radius replaced by `r ∈ (0, Δ_max]`. -/
def TRqParams.withΔ₀ (P : TRqParams) (r : ℝ) (h0 : 0 < r) (h1 : r ≤ P.Δmax) : TRqParams :=
  { P with Δ₀ := r, Δ₀_pos := h0, Δ₀_le_Δmax := h1 }

@[simp]
theorem TRqParams.withΔ₀_Δ₀ (P : TRqParams) (r : ℝ) (h0 : 0 < r) (h1 : r ≤ P.Δmax) :
    (P.withΔ₀ r h0 h1).Δ₀ = r :=
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An iteration satisfying Step 2 fails the termination test of TRq. -/
theorem IsTRqStep.not_measureTestPasses {D : FormalMultilinearSeries ℝ E ℝ} {S : Set E}
    {ς : ℝ} {q : ℕ} {ε : ℕ → ℝ} {δ Δ : ℝ} {d : ℕ → E} {j : ℕ} {s : E}
    (h : IsTRqStep D S ς q ε δ Δ d j s) :
    ¬ MeasureTestPasses (fun j => D.taylorDecrement j) q ς ε (fun _ => δ) d :=
  fun ht => absurd (ht j h.order_mem) (not_le.2 h.lt_taylorDecrement)

/-- Step 2 of TRq only depends on the Taylor decrements of the data. -/
theorem IsTRqStep.of_taylorDecrement_eq {D D' : FormalMultilinearSeries ℝ E ℝ}
    (h : ∀ j, D'.taylorDecrement j = D.taylorDecrement j) {S : Set E} {ς : ℝ} {q : ℕ}
    {ε : ℕ → ℝ} {δ Δ : ℝ} {d : ℕ → E} {j : ℕ} {s : E}
    (hs : IsTRqStep D S ς q ε δ Δ d j s) : IsTRqStep D' S ς q ε δ Δ d j s := by
  refine ⟨hs.order_mem, ?_, fun i hi hij => ?_, hs.mem, ?_⟩
  · rw [h]; exact hs.lt_taylorDecrement
  · rw [h]; exact hs.taylorDecrement_le_of_lt i hi hij
  · rw [h]; exact hs.taylorDecrement_le

open Classical in
/-- **Appending a run to an explicit prefix.** If `T` explicit iterations
`(x_k, s_k, Δ_k, j_k, d_k)`, `k < T`, starting from `Δ_0 = Δ₀`, satisfy Steps 1–4 of
Algorithm 12.2.1 with data `D (x_k)` and feasible sets `S (x_k)` and the cap `Δ_{k+1} ≤ Δ_max`,
and a run `y` starts at `x_T` with initial radius `r = Δ_T`, the concatenation is a run. It does
not terminate before `T + T'` if the continuation does not terminate before `T'`, its successful
iterations below `T + T'` are those of the prefix and of the continuation below `T'`, and it
agrees with the prefix up to `T` (iterates and radii up to `T`, steps, orders and Step-1
displacements below `T`). -/
theorem exists_isTRqRun_append {f : E → ℝ} {D : E → FormalMultilinearSeries ℝ E ℝ}
    {S : E → Set E} {P : TRqParams} {q : ℕ} {ε : ℕ → ℝ} {ϑ : ℝ} {T : ℕ} {xp sp : ℕ → E}
    {Δp : ℕ → ℝ} {jp : ℕ → ℕ} {dp : ℕ → ℕ → E} (h0 : Δp 0 = P.Δ₀) {r : ℝ} (hr : Δp T = r)
    (hpos : 0 < r) (hmax : r ≤ P.Δmax)
    (hstep : ∀ k < T, IsTRqStep (D (xp k)) (S (xp k)) P.ς q ε (min (Δp k) ϑ) (Δp k) (dp k)
      (jp k) (sp k))
    (hacc : ∀ k < T, TRAcceptance P.toTRParams
      (reductionRatio f (xp k) (sp k) ((D (xp k)).taylorDecrement (jp k) (sp k)))
      (xp k) (sp k) (xp (k + 1)) (Δp k) (Δp (k + 1)))
    (hwit : ∀ k < T, ∀ j ∈ Finset.Icc 1 q, IsApproxMeasureStep
      ((D (xp k)).taylorDecrement j) (min (Δp k) ϑ) (S (xp k)) P.ς (dp k j))
    (hcap : ∀ k < T, Δp (k + 1) ≤ P.Δmax)
    {y sy : ℕ → E} {Δy : ℕ → ℝ} {jy : ℕ → ℕ} {dy : ℕ → ℕ → E} (hy0 : y 0 = xp T)
    (hy : IsTRqRun f (fun k => D (y k)) (fun k => S (y k)) (P.withΔ₀ r hpos hmax) q ε ϑ y sy Δy
      jy dy)
    {T' c : ℕ} (hyns : ∀ k < T', ¬ trqTest (fun k => D (y k)) P q ε ϑ Δy dy k)
    (hyc : c ≤ ((Finset.range T').filter fun k =>
      P.η₁ ≤ trqRatio f (fun k => D (y k)) y sy jy k).card) :
    ∃ (x s : ℕ → E) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → E), x 0 = xp 0 ∧
      IsTRqRun f (fun k => D (x k)) (fun k => S (x k)) P q ε ϑ x s Δ jk d ∧
      (∀ k < T + T', ¬ trqTest (fun k => D (x k)) P q ε ϑ Δ d k) ∧
      ((Finset.range T).filter fun k => P.η₁ ≤ reductionRatio f (xp k) (sp k)
          ((D (xp k)).taylorDecrement (jp k) (sp k))).card + c ≤
        ((Finset.range (T + T')).filter fun k =>
          P.η₁ ≤ trqRatio f (fun k => D (x k)) x s jk k).card ∧
      (∀ k ≤ T, x k = xp k ∧ Δ k = Δp k) ∧
      (∀ k < T, s k = sp k ∧ jk k = jp k ∧ d k = dp k) := by
  obtain ⟨x, hx⟩ : ∃ x : ℕ → E, ∀ k, x k = if k < T then xp k else y (k - T) := ⟨_, fun _ => rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ → E, ∀ k, s k = if k < T then sp k else sy (k - T) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℕ → ℝ, ∀ k, Δ k = if k < T then Δp k else Δy (k - T) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨jk, hjk⟩ : ∃ jk : ℕ → ℕ, ∀ k, jk k = if k < T then jp k else jy (k - T) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℕ → E, ∀ k, d k = if k < T then dp k else dy (k - T) :=
    ⟨_, fun _ => rfl⟩
  have hΔy0 : Δy 0 = Δp T := hy.toIsTRRun.delta_zero.trans hr.symm
  -- the prefix and the continuation
  have hxl : ∀ k, k ≤ T → x k = xp k := fun k hk => by
    rcases hk.lt_or_eq with hk | rfl
    · rw [hx, ite_eq_left hk]
    · rw [hx, ite_eq_right (lt_irrefl _), Nat.sub_self, hy0]
  have hΔl : ∀ k, k ≤ T → Δ k = Δp k := fun k hk => by
    rcases hk.lt_or_eq with hk | rfl
    · rw [hΔ, ite_eq_left hk]
    · rw [hΔ, ite_eq_right (lt_irrefl _), Nat.sub_self, hΔy0]
  have hsl : ∀ k < T, s k = sp k := fun k hk => by rw [hs, ite_eq_left hk]
  have hjl : ∀ k < T, jk k = jp k := fun k hk => by rw [hjk, ite_eq_left hk]
  have hdl : ∀ k < T, d k = dp k := fun k hk => by rw [hd, ite_eq_left hk]
  have hxr : ∀ m, x (T + m) = y m := fun m => by
    rw [hx, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  have hΔr : ∀ m, Δ (T + m) = Δy m := fun m => by
    rw [hΔ, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  have hsr : ∀ m, s (T + m) = sy m := fun m => by
    rw [hs, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  have hjr : ∀ m, jk (T + m) = jy m := fun m => by
    rw [hjk, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  have hdr : ∀ m, d (T + m) = dy m := fun m => by
    rw [hd, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  have hcases : ∀ k, k < T ∨ ∃ m, k = T + m := fun k => by
    rcases lt_or_ge k T with h | h
    · exact Or.inl h
    · exact Or.inr ⟨k - T, by omega⟩
  -- the tests
  have hstopl : ∀ k < T, ¬ trqTest (fun k => D (x k)) P q ε ϑ Δ d k := fun k hk h => by
    rw [trqTest_iff, hxl k hk.le, hΔl k hk.le, hdl k hk] at h
    exact (hstep k hk).not_measureTestPasses h
  have hstopr : ∀ m, trqTest (fun k => D (x k)) P q ε ϑ Δ d (T + m) ↔
      trqTest (fun k => D (y k)) (P.withΔ₀ r hpos hmax) q ε ϑ Δy dy m := fun m => by
    rw [trqTest_iff, trqTest_iff, hxr, hΔr, hdr]
    rfl
  have htail : ∀ m, (∀ i ≤ T + m, ¬ trqTest (fun k => D (x k)) P q ε ϑ Δ d i) →
      ∀ i ≤ m, ¬ trqTest (fun k => D (y k)) (P.withΔ₀ r hpos hmax) q ε ϑ Δy dy i :=
    fun m hk i hi => (hstopr i).not.1 (hk (T + i) (by omega))
  have htail' : ∀ m, (∀ i < T + m, ¬ trqTest (fun k => D (x k)) P q ε ϑ Δ d i) →
      ∀ i < m, ¬ trqTest (fun k => D (y k)) (P.withΔ₀ r hpos hmax) q ε ϑ Δy dy i :=
    fun m hk i hi => (hstopr i).not.1 (hk (T + i) (by omega))
  have hrun : IsTRqRun f (fun k => D (x k)) (fun k => S (x k)) P q ε ϑ x s Δ jk d := by
    refine ⟨⟨?_, fun k hk => ?_, fun k hk => ?_⟩, fun k hk j hj => ?_, fun k hk => ?_⟩
    · -- the initial radius
      rw [hΔl 0 (Nat.zero_le _), h0]
    · -- Step 2
      rcases hcases k with hkT | ⟨m, rfl⟩
      · rw [hxl k hkT.le, hΔl k hkT.le, hdl k hkT, hjl k hkT, hsl k hkT]
        exact hstep k hkT
      · rw [hxr, hΔr, hdr, hjr, hsr]
        exact hy.step m (htail m hk)
    · -- Steps 3–4
      change TRAcceptance P.toTRParams (trqRatio f (fun k => D (x k)) x s jk k)
        (x k) (s k) (x (k + 1)) (Δ k) (Δ (k + 1))
      rw [trqRatio_eq]
      rcases hcases k with hkT | ⟨m, rfl⟩
      · rw [hxl k hkT.le, hΔl k hkT.le, hjl k hkT, hsl k hkT, hxl (k + 1) hkT,
          hΔl (k + 1) hkT]
        exact hacc k hkT
      · have := hy.accept m (htail m hk)
        rw [show T + m + 1 = T + (m + 1) by omega, hxr, hxr, hΔr, hΔr, hsr, hjr]
        exact this
    · -- Step 1
      rcases hcases k with hkT | ⟨m, rfl⟩
      · rw [hxl k hkT.le, hΔl k hkT.le, hdl k hkT]
        exact hwit k hkT j hj
      · have := hy.witness m (htail' m hk) j hj
        rw [hxr, hΔr, hdr]
        exact this
    · -- the cap
      change Δ (k + 1) ≤ P.Δmax
      rcases hcases k with hkT | ⟨m, rfl⟩
      · rw [hΔl (k + 1) hkT]; exact hcap k hkT
      · have := hy.cap m (htail m hk)
        rw [show T + m + 1 = T + (m + 1) by omega, hΔr]
        exact this
  refine ⟨x, s, Δ, jk, d, hxl 0 (Nat.zero_le _), hrun, fun k hk => ?_, ?_,
    fun k hk => ⟨hxl k hk, hΔl k hk⟩, fun k hk => ⟨hsl k hk, hjl k hk, hdl k hk⟩⟩
  · rcases hcases k with hkT | ⟨m, rfl⟩
    · exact hstopl k hkT
    · exact (hstopr m).not.2 (hyns m (by omega))
  · have hsplit : ∀ (p : ℕ → Prop) [DecidablePred p], ((Finset.range (T + T')).filter p).card =
        ((Finset.range T).filter p).card + ((Finset.range T').filter fun m => p (T + m)).card :=
      fun p _ => by simp only [Finset.card_filter]; exact Finset.sum_range_add _ _ _
    rw [hsplit]
    gcongr ?_ + ?_
    · refine le_of_eq (congrArg Finset.card (Finset.filter_congr fun k hk => ?_))
      have hkT := Finset.mem_range.1 hk
      rw [trqRatio_eq, hxl k hkT.le, hsl k hkT, hjl k hkT]
    · refine hyc.trans (le_of_eq (congrArg Finset.card (Finset.filter_congr fun m _ => ?_)))
      rw [trqRatio_eq, trqRatio_eq, hxr, hsr, hjr]

/-- **Transfer of a run to an objective with the same Taylor decrements and the same differences
on `X`** (e.g. an objective differing by a constant near `X`): a run of TRq with exact data on `f`
and feasible set `X` is a run with exact data on `g`, with the same termination tests (before
termination) and ratios. -/
theorem IsTRqRun.congr_of_taylorDecrement_eq {f g : E → ℝ} {X : Set E} {P : TRqParams}
    {q : ℕ} {ε : ℕ → ℝ} {ϑ : ℝ} {x s : ℕ → E} {Δ : ℕ → ℝ} {jk : ℕ → ℕ} {d : ℕ → ℕ → E}
    (hT : ∀ y ∈ X, ∀ j, (ftaylorSeries ℝ g y).taylorDecrement j =
      (ftaylorSeries ℝ f y).taylorDecrement j)
    (hD : ∀ y ∈ X, ∀ z ∈ X, g y - g z = f y - f z) (hx0 : x 0 ∈ X)
    (h : IsTRqRun f (𝒥 f x) (𝒳 X x) P q ε ϑ x s Δ jk d) :
    IsTRqRun g (𝒥 g x) (𝒳 X x) P q ε ϑ x s Δ jk d ∧
      (∀ k, (∀ i < k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i) →
        (trqTest (𝒥 g x) P q ε ϑ Δ d k ↔ trqTest (𝒥 f x) P q ε ϑ Δ d k)) ∧
      (∀ k, (∀ i ≤ k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i) →
        trqRatio g (𝒥 g x) x s jk k = trqRatio f (𝒥 f x) x s jk k) := by
  have hmem := h.mem_of_feasible hx0
  have hiff : ∀ k, (∀ i < k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i) →
      (trqTest (𝒥 g x) P q ε ϑ Δ d k ↔ trqTest (𝒥 f x) P q ε ϑ Δ d k) := fun k hk => by
    rw [trqTest_iff, trqTest_iff]
    have e : (fun j => (ftaylorSeries ℝ g (x k)).taylorDecrement j) =
        fun j => (ftaylorSeries ℝ f (x k)).taylorDecrement j := funext (hT _ (hmem k hk))
    rw [e]
  have hnot : ∀ k, (∀ i < k, ¬ trqTest (𝒥 g x) P q ε ϑ Δ d i) →
      ∀ i < k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i := by
    intro k hk i
    induction i using Nat.strong_induction_on with
    | _ i ih => exact fun hi hF => hk i hi ((hiff i fun j hj => ih j hj (hj.trans hi)).2 hF)
  have hnot' : ∀ k, (∀ i ≤ k, ¬ trqTest (𝒥 g x) P q ε ϑ Δ d i) →
      ∀ i ≤ k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i := fun k hk i hi =>
    hnot (k + 1) (fun j hj => hk j (by omega)) i (by omega)
  have hrho : ∀ k, (∀ i ≤ k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i) →
      trqRatio g (𝒥 g x) x s jk k = trqRatio f (𝒥 f x) x s jk k := fun k hk => by
    have hxk := hmem k fun i hi => hk i hi.le
    have hsk : x k + s k ∈ X := (h.isTRqStep hk).mem.2
    rw [trqRatio_eq, trqRatio_eq, reductionRatio_def, reductionRatio_def, hD _ hxk _ hsk,
      hT _ hxk]
  refine ⟨⟨⟨h.toIsTRRun.delta_zero, fun k hk => ?_, fun k hk => ?_⟩, fun k hk j hj => ?_,
    fun k hk => h.cap k (hnot' k hk)⟩, hiff, hrho⟩
  · exact (h.step k (hnot' k hk)).of_taylorDecrement_eq
      (hT _ (hmem k fun i hi => hnot' k hk i hi.le))
  · have := h.accept k (hnot' k hk)
    change TRAcceptance P.toTRParams (trqRatio g (𝒥 g x) x s jk k) (x k) (s k)
      (x (k + 1)) (Δ k) (Δ (k + 1))
    rw [hrho k (hnot' k hk)]
    exact this
  · have := h.witness k (hnot k hk) j hj
    change IsApproxMeasureStep ((ftaylorSeries ℝ g (x k)).taylorDecrement j) _ _ _ _
    rw [hT _ (hmem k (hnot k hk))]
    exact this

end Optimization
