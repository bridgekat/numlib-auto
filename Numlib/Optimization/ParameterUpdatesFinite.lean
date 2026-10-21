import Numlib.Optimization.ParameterUpdates

/-!
# Finite regularization parameter updates

A finite prefix of interval updates can be continued by holding its final parameter and
assigning acceptance ratio one. This continuation transports the usual parameter estimates
without requiring an optimizer to perform any trials after it has stopped.
-/

namespace Optimization.ParameterUpdates

/-- Hold a sequence at its last available value after the specified index. -/
def hold {α : Type*} (u : ℕ → α) (N : ℕ) (k : ℕ) : α := u (min k N)

/-- Holding a sequence preserves every value through the final index. -/
@[simp] theorem hold_of_le {α : Type*} (u : ℕ → α) {N k : ℕ} (hk : k ≤ N) :
    hold u N k = u k := by simp [hold, Nat.min_eq_left hk]

/-- Beyond the final index the held sequence is constant. -/
@[simp] theorem hold_of_ge {α : Type*} (u : ℕ → α) {N k : ℕ} (hk : N ≤ k) :
    hold u N k = u N := by simp [hold, Nat.min_eq_right hk]

/-- Preserve actual ratios within a prefix and use a very successful ratio afterward. -/
def continueRatio (rho : ℕ → ℝ) (N k : ℕ) : ℝ := if k < N then rho k else 1

/-- The source interval updates, required only for executed trials in a finite prefix. -/
structure RegularizationPrefix (p : RegularizationParameters) (rho sigma : ℕ → ℝ)
    (N : ℕ) : Prop where
  initial_lower : p.sigmaMin ≤ sigma 0
  update : ∀ k < N, if p.eta2 ≤ rho k
    then sigma (k + 1) ∈ Set.Icc (max p.sigmaMin (p.gamma1 * sigma k)) (sigma k)
    else if p.eta1 ≤ rho k
    then sigma (k + 1) ∈ Set.Icc (sigma k) (p.gamma2 * sigma k)
    else sigma (k + 1) ∈ Set.Icc (p.gamma2 * sigma k) (p.gamma3 * sigma k)

variable {p : RegularizationParameters} {rho sigma : ℕ → ℝ} {N : ℕ}

/-- Finite interval updates preserve the positive parameter floor through the final index. -/
theorem RegularizationPrefix.lower (h : RegularizationPrefix p rho sigma N)
    {k : ℕ} (hk : k ≤ N) : p.sigmaMin ≤ sigma k := by
  induction k with
  | zero => exact h.initial_lower
  | succ k ih =>
    have hi := ih (by omega)
    have hu := h.update k (by omega)
    split_ifs at hu
    · exact (le_max_left _ _).trans hu.1
    · exact hi.trans hu.1
    · exact hi.trans ((le_mul_of_one_le_left (p.sigmaMin_pos.le.trans hi)
        p.one_lt_gamma2.le).trans hu.1)

/-- Every parameter of a finite prefix is positive. -/
theorem RegularizationPrefix.pos (h : RegularizationPrefix p rho sigma N)
    {k : ℕ} (hk : k ≤ N) : 0 < sigma k := p.sigmaMin_pos.trans_le (h.lower hk)

/-- A finite prefix has a legal constant continuation with ratio one. -/
theorem RegularizationPrefix.continuation (h : RegularizationPrefix p rho sigma N) :
    RegularizationUpdates p (continueRatio rho N) (hold sigma N) := by
  refine ⟨by simpa using h.initial_lower, ?_⟩
  intro k
  by_cases hk : k < N
  · simpa only [continueRatio, ite_eq_left hk, hold_of_le sigma (by omega : k ≤ N),
      hold_of_le sigma (by omega : k + 1 ≤ N)] using h.update k hk
  · have hn : N ≤ k := by omega
    have hnext : N ≤ k + 1 := by omega
    have h1 : p.eta2 ≤ 1 := p.eta2_lt_one.le
    simp only [continueRatio, ite_eq_right hk, hold_of_ge sigma hn,
      hold_of_ge sigma hnext, ite_eq_left h1, Set.mem_Icc, le_refl, and_true]
    exact max_le (h.lower le_rfl)
      (mul_le_of_le_one_left (h.pos le_rfl).le p.gamma1_lt_one.le)

/-- A sufficient-success threshold bounds every parameter in a finite prefix. -/
theorem RegularizationPrefix.upper (h : RegularizationPrefix p rho sigma N) {T : ℝ}
    (hT : ∀ k < N, T ≤ sigma k → p.eta2 ≤ rho k) {k : ℕ} (hk : k ≤ N) :
    sigma k ≤ max (sigma 0) (p.gamma3 * T) := by
  have ht : ∀ j, T ≤ hold sigma N j → p.eta2 ≤ continueRatio rho N j := by
    intro j hj
    by_cases hjN : j < N
    · simpa only [continueRatio, ite_eq_left hjN] using
        hT j hjN (by simpa only [hold_of_le sigma (by omega : j ≤ N)] using hj)
    · simp [continueRatio, hjN, p.eta2_lt_one.le]
  simpa only [hold_of_le sigma hk, hold_of_le sigma (Nat.zero_le N)] using
    h.continuation.upper ht k

/-- The usual total-trial count estimate applies to every finite prefix. -/
theorem RegularizationPrefix.total_count_le (h : RegularizationPrefix p rho sigma N)
    {k : ℕ} (hk : k ≤ N) {M : ℝ} (hM : sigma k ≤ M) :
    (k : ℝ) ≤ (successCount (fun j => p.eta1 ≤ rho j) k : ℝ) *
      (1 + |Real.log p.gamma1| / Real.log p.gamma2) +
        Real.log (M / sigma 0) / Real.log p.gamma2 := by
  have hc : successCount (fun j => p.eta1 ≤ continueRatio rho N j) k =
      successCount (fun j => p.eta1 ≤ rho j) k := by
    classical
    unfold successCount
    congr 1
    apply Finset.filter_congr
    intro j hj
    have hjN : j < N := lt_of_lt_of_le (Finset.mem_range.mp hj) hk
    simp only [continueRatio, ite_eq_left hjN]
  have hb := h.continuation.total_count_le k (by simpa only [hold_of_le sigma hk] using hM)
  simpa only [hc, hold_of_le sigma (Nat.zero_le N)] using hb

/-- Counting successful trials and uniformly bounded failed blocks controls the total count. -/
theorem count_of_failed_blocks (P : ℕ → Prop) (B : ℝ) (hB : 0 ≤ B) (N : ℕ)
    (hblock : ∀ a m, a + m ≤ N → (∀ j < m, ¬P (a + j)) → (m : ℝ) ≤ B) :
    (N : ℝ) ≤ (successCount P N : ℝ) * (B + 1) + B := by
  classical
  induction N using Nat.strong_induction_on with
  | h N ih =>
    let S := (Finset.range N).filter P
    by_cases hS : S.Nonempty
    · let k := S.max' hS
      have hkS : k ∈ S := Finset.max'_mem S hS
      have hk : k < N := Finset.mem_range.mp (Finset.mem_filter.mp hkS).1
      have hkP : P k := (Finset.mem_filter.mp hkS).2
      have htail : ∀ j < N - (k + 1), ¬P (k + 1 + j) := by
        intro j hj hp
        have hm : k + 1 + j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
        have hh := Finset.le_max' S (k + 1 + j) hm
        change k + 1 + j ≤ k at hh
        omega
      have ht := hblock (k + 1) (N - (k + 1)) (by omega) htail
      have hi := ih k hk (fun a m ham hf => hblock a m (by omega) hf)
      have hcount : successCount P k + 1 ≤ successCount P N := by
        have he : successCount P (k + 1) =
            successCount P k + 1 := by
          simp [successCount, Finset.range_add_one, Finset.filter_insert, hkP]
        rw [← he]
        exact Finset.card_le_card (Finset.filter_subset_filter P (Finset.range_mono (by omega)))
      have hc : (successCount P k : ℝ) + 1 ≤
          (successCount P N : ℝ) := by exact_mod_cast hcount
      have hm := mul_le_mul_of_nonneg_right hc (by linarith only [hB] : 0 ≤ B + 1)
      have heq : (N : ℝ) = (k : ℝ) + 1 + (N - (k + 1) : ℕ) := by
        exact_mod_cast (show N = k + 1 + (N - (k + 1)) by omega)
      linarith only [hi, ht, hm, heq]
    · have hf : ∀ j < N, ¬P (0 + j) := by
        intro j hj hp
        exact hS ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, by simpa using hp⟩⟩
      have ht := hblock 0 N (by omega) hf
      have hc : 0 ≤ (successCount P N : ℝ) * (B + 1) := by positivity
      linarith only [ht, hc]

end Optimization.ParameterUpdates
