import Numlib.Optimization.ConstrainedTrustRegion

/-!
# Concatenating feasible trust-region executions

Two actual finite executions can be joined at equal retained points and radii. The second
execution supplies the testing witnesses at the join. A stopping endpoint then gives a full
execution in the operational sense, with no trial requirements after the first stopping test.
-/

noncomputable section
namespace Optimization.ConstrainedTrustRegion
open HigherOrderTrustRegion

variable {E : Type*}

/-- Join two trust-region traces, using the second trace's witnesses at the joining point. -/
def appendTrace (t u : Trace E) (N : ℕ) : Trace E where
  point k := if k < N then t.point k else u.point (k - N)
  step k := if k < N then t.step k else u.step (k - N)
  radius k := if k < N then t.radius k else u.radius (k - N)
  witness k := if k < N then t.witness k else u.witness (k - N)
  order k := if k < N then t.order k else u.order (k - N)

/-- Points before the join are the original prefix points. -/
@[simp] theorem appendTrace_point_before (t u : Trace E) {N k : ℕ} (hk : k < N) :
    (appendTrace t u N).point k = t.point k := ite_eq_left hk

/-- Steps before the join are the original prefix steps. -/
@[simp] theorem appendTrace_step_before (t u : Trace E) {N k : ℕ} (hk : k < N) :
    (appendTrace t u N).step k = t.step k := ite_eq_left hk

/-- Radii before the join are the original prefix radii. -/
@[simp] theorem appendTrace_radius_before (t u : Trace E) {N k : ℕ} (hk : k < N) :
    (appendTrace t u N).radius k = t.radius k := ite_eq_left hk

/-- Witnesses before the join are the original prefix witnesses. -/
@[simp] theorem appendTrace_witness_before (t u : Trace E) {N k j : ℕ} (hk : k < N) :
    (appendTrace t u N).witness k j = t.witness k j := by simp [appendTrace, hk]

/-- Selected orders before the join are the original prefix orders. -/
@[simp] theorem appendTrace_order_before (t u : Trace E) {N k : ℕ} (hk : k < N) :
    (appendTrace t u N).order k = t.order k := ite_eq_left hk

/-- Points from the join onward are the continuation points. -/
@[simp] theorem appendTrace_point_after (t u : Trace E) (N k : ℕ) :
    (appendTrace t u N).point (N + k) = u.point k := by simp [appendTrace]

/-- Steps from the join onward are the continuation steps. -/
@[simp] theorem appendTrace_step_after (t u : Trace E) (N k : ℕ) :
    (appendTrace t u N).step (N + k) = u.step k := by simp [appendTrace]

/-- Radii from the join onward are the continuation radii. -/
@[simp] theorem appendTrace_radius_after (t u : Trace E) (N k : ℕ) :
    (appendTrace t u N).radius (N + k) = u.radius k := by simp [appendTrace]

/-- Witnesses from the join onward are the continuation witnesses. -/
@[simp] theorem appendTrace_witness_after (t u : Trace E) (N k j : ℕ) :
    (appendTrace t u N).witness (N + k) j = u.witness k j := by simp [appendTrace]

/-- Selected orders from the join onward are the continuation orders. -/
@[simp] theorem appendTrace_order_after (t u : Trace E) (N k : ℕ) :
    (appendTrace t u N).order (N + k) = u.order k := by simp [appendTrace]

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- From the join onward, the observable stopping test is exactly the continuation test. -/
theorem stops_appendTrace_after (t u : Trace E) (N k : ℕ) (p : Parameters) (q : ℕ)
    (epsilon : ℕ → ℝ) (f : E → ℝ) :
    Stops p q epsilon f (appendTrace t u N) (N + k) ↔ Stops p q epsilon f u k := by
  simp only [Stops, testRadius, appendTrace_point_after, appendTrace_witness_after,
    appendTrace_radius_after]

/-- From the join onward, the actual acceptance ratio is the continuation ratio. -/
theorem ratio_appendTrace_after (t u : Trace E) (N k : ℕ) (f : E → ℝ) :
    ratio f (appendTrace t u N) (N + k) = ratio f u k := by
  simp only [ratio, appendTrace_point_after, appendTrace_step_after, appendTrace_order_after]

/-- Matching retained points and radii permit concatenation of actual legal prefixes. -/
theorem LegalPrefix.append {X : Set E} {p : Parameters} {q N M : ℕ}
    {epsilon : ℕ → ℝ} {f : E → ℝ} {t u : Trace E}
    (ht : LegalPrefix X p q epsilon f t N) (hu : LegalPrefix X p q epsilon f u M)
    (hx : u.point 0 = t.point N) (hr : u.radius 0 = t.radius N) :
    LegalPrefix X p q epsilon f (appendTrace t u N) (N + M) := by
  have hp (k : ℕ) (hk : k ≤ N) : (appendTrace t u N).point k = t.point k := by
    by_cases h : k < N
    · exact appendTrace_point_before t u h
    · have he : k = N := by omega
      subst k
      simpa only [Nat.add_zero] using (appendTrace_point_after t u N 0).trans hx
  have hrad (k : ℕ) (hk : k ≤ N) : (appendTrace t u N).radius k = t.radius k := by
    by_cases h : k < N
    · exact appendTrace_radius_before t u h
    · have he : k = N := by omega
      subst k
      simpa only [Nat.add_zero] using (appendTrace_radius_after t u N 0).trans hr
  have htst (k : ℕ) (hk : k ≤ N) : testRadius p (appendTrace t u N) k = testRadius p t k := by
    simp only [testRadius, hrad k hk]
  have hstop (k : ℕ) (hk : k < N) :
      Stops p q epsilon f (appendTrace t u N) k ↔ Stops p q epsilon f t k := by
    simp only [Stops, hp k hk.le, appendTrace_witness_before t u hk, htst k hk.le]
  have hratio (k : ℕ) (hk : k < N) : ratio f (appendTrace t u N) k = ratio f t k := by
    simp only [ratio, hp k hk.le, appendTrace_step_before t u hk,
      appendTrace_order_before t u hk]
  have htailst (k : ℕ) : testRadius p (appendTrace t u N) (N + k) = testRadius p u k := by
    simp only [testRadius, appendTrace_radius_after]
  refine {
    toOperationalPrefix := ?_
    initial_mem := ?_
    witness_mem := ?_
    trial_mem := ?_
    witness_fraction := ?_ }
  · refine {
      initial_pos := ?_
      initial_cap := ?_
      witness_feasible := ?_
      nonterminal := ?_
      order_pos := ?_
      order_le := ?_
      first_failure := ?_
      failure := ?_
      step_feasible := ?_
      prediction := ?_
      iterate := ?_
      update := ?_ }
    · simpa only [hrad 0 (Nat.zero_le _)] using ht.initial_pos
    · simpa only [hrad 0 (Nat.zero_le _)] using ht.initial_cap
    · intro k hk j hj hjq
      by_cases h : k < N
      · simpa only [appendTrace_witness_before t u h, htst k h.le] using
          ht.witness_feasible k h.le j hj hjq
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (by omega : N ≤ k)
        simpa only [appendTrace_witness_after, htailst] using
          hu.witness_feasible i (by omega) j hj hjq
    · intro k hk
      by_cases h : k < N
      · exact (hstop k h).not.mpr (ht.nonterminal k h)
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (by omega : N ≤ k)
        exact (stops_appendTrace_after t u N i p q epsilon f).not.mpr
          (hu.nonterminal i (by omega))
    · intro k hk
      by_cases h : k < N
      · simpa only [appendTrace_order_before t u h] using ht.order_pos k h
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (by omega : N ≤ k)
        simpa only [appendTrace_order_after] using hu.order_pos i (by omega)
    · intro k hk
      by_cases h : k < N
      · simpa only [appendTrace_order_before t u h] using ht.order_le k h
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (by omega : N ≤ k)
        simpa only [appendTrace_order_after] using hu.order_le i (by omega)
    · intro k hk j hj hjlt
      by_cases h : k < N
      · rw [appendTrace_order_before t u h] at hjlt
        simpa only [hp k h.le, appendTrace_witness_before t u h, htst k h.le] using
          ht.first_failure k h j hj hjlt
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (by omega : N ≤ k)
        rw [appendTrace_order_after] at hjlt
        simpa only [appendTrace_point_after, appendTrace_witness_after, htailst] using
          hu.first_failure i (by omega) j hj hjlt
    · intro k hk
      by_cases h : k < N
      · simpa only [hp k h.le, appendTrace_order_before t u h,
          appendTrace_witness_before t u h, htst k h.le] using ht.failure k h
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (by omega : N ≤ k)
        simpa only [appendTrace_point_after, appendTrace_witness_after,
          appendTrace_order_after, htailst] using hu.failure i (by omega)
    · intro k hk
      by_cases h : k < N
      · simpa only [appendTrace_step_before t u h, hrad k h.le] using ht.step_feasible k h
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (by omega : N ≤ k)
        simpa only [appendTrace_step_after, appendTrace_radius_after] using
          hu.step_feasible i (by omega)
    · intro k hk
      by_cases h : k < N
      · simpa only [hp k h.le, appendTrace_witness_before t u h,
          appendTrace_step_before t u h, appendTrace_order_before t u h] using ht.prediction k h
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (by omega : N ≤ k)
        simpa only [appendTrace_point_after, appendTrace_witness_after,
          appendTrace_step_after, appendTrace_order_after] using hu.prediction i (by omega)
    · intro k hk
      by_cases h : k < N
      · simpa only [hp (k + 1) (by omega), hp k h.le, appendTrace_step_before t u h,
          hratio k h] using ht.iterate k h
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (by omega : N ≤ k)
        simpa only [Nat.add_assoc, appendTrace_point_after, appendTrace_step_after,
          ratio_appendTrace_after] using hu.iterate i (by omega)
    · intro k hk
      by_cases h : k < N
      · simpa only [hrad (k + 1) (by omega), hrad k h.le, hratio k h] using ht.update k h
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (by omega : N ≤ k)
        simpa only [Nat.add_assoc, appendTrace_radius_after, ratio_appendTrace_after] using
          hu.update i (by omega)
  · simpa only [hp 0 (Nat.zero_le _)] using ht.initial_mem
  · intro k hk j hj hjq
    by_cases h : k < N
    · simpa only [hp k h.le, appendTrace_witness_before t u h] using ht.witness_mem k h.le j hj hjq
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (by omega : N ≤ k)
      simpa only [appendTrace_point_after, appendTrace_witness_after] using
        hu.witness_mem i (by omega) j hj hjq
  · intro k hk
    by_cases h : k < N
    · simpa only [hp k h.le, appendTrace_step_before t u h] using ht.trial_mem k h
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (by omega : N ≤ k)
      simpa only [appendTrace_point_after, appendTrace_step_after] using hu.trial_mem i (by omega)
  · intro k hk j hj hjq
    by_cases h : k < N
    · simpa only [hp k h.le, appendTrace_witness_before t u h, htst k h.le] using
        ht.witness_fraction k h.le j hj hjq
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (by omega : N ≤ k)
      simpa only [appendTrace_point_after, appendTrace_witness_after, htailst] using
        hu.witness_fraction i (by omega) j hj hjq

/-- A legal prefix ending at a stopping test is already a complete operational execution. -/
theorem LegalPrefix.isRun_of_stops {X : Set E} {p : Parameters} {q N : ℕ}
    {epsilon : ℕ → ℝ} {f : E → ℝ} {t : Trace E}
    (ht : LegalPrefix X p q epsilon f t N) (hs : Stops p q epsilon f t N) :
    IsRun X p q epsilon f t := by
  intro M hM
  apply ht.restrict
  by_contra h
  have hNM : N < M := by omega
  exact hM N hNM hs

end Optimization.ConstrainedTrustRegion

namespace Optimization.HigherOrderTrustRegion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Matching retained points and radii also permit concatenation of full-ball prefixes. -/
theorem LegalPrefix.append {p : Parameters} {q N M : ℕ}
    {epsilon : ℕ → ℝ} {f : E → ℝ} {t u : Trace E}
    (ht : LegalPrefix p q epsilon f t N) (hu : LegalPrefix p q epsilon f u M)
    (hx : u.point 0 = t.point N) (hr : u.radius 0 = t.radius N) :
    LegalPrefix p q epsilon f (ConstrainedTrustRegion.appendTrace t u N) (N + M) := by
  exact ConstrainedTrustRegion.legalPrefix_univ_iff.mp
    ((ConstrainedTrustRegion.legalPrefix_univ_iff.mpr ht).append
      (ConstrainedTrustRegion.legalPrefix_univ_iff.mpr hu) hx hr)

end Optimization.HigherOrderTrustRegion
