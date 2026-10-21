import Numlib.Optimization.TwoPhaseExecution

/-!
# Complete finite block partitions and original-oracle query schedules

Each executed trial belongs to the block determined by the number of preceding resets.
Block zero includes the initial partial block, and the last block includes any terminal
partial block. Shared endpoints are represented once in the original-oracle query schedule.
-/

noncomputable section
namespace Optimization.TwoPhaseTargets
open HigherOrderRegularization ParameterUpdates

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F]

/-- All executed trial indices, including the terminal outer history. -/
def innerTrialIndices (history : ℕ → InnerHistory E) (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range N).biUnion fun k => (Finset.range (history k).length).image (k, ·)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- An index is present exactly when both its outer and inner trials were executed. -/
@[simp] theorem mem_innerTrialIndices {history : ℕ → InnerHistory E} {N k i : ℕ} :
    (k, i) ∈ innerTrialIndices history N ↔ k < N ∧ i < (history k).length := by
  simp [innerTrialIndices]

/-- The block number counts resets strictly before the current outer iteration. -/
def blockOwner (f : E → ℝ) (c : E → F) (theta epsilon0 : ℝ)
    (x : ℕ → E) (t : ℕ → ℝ) (k : ℕ) : ℕ :=
  (resetIndices f c theta epsilon0 x t k).card

open Classical in
/-- A block contains all trials with its owner number; initial and final partial blocks
are included without special endpoint conventions. -/
def iterationBlock (f : E → ℝ) (c : E → F) (theta epsilon0 : ℝ)
    (x : ℕ → E) (t : ℕ → ℝ) (history : ℕ → InnerHistory E) (N b : ℕ) :
    Finset (ℕ × ℕ) :=
  (innerTrialIndices history N).filter fun q => blockOwner f c theta epsilon0 x t q.1 = b

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Every trial belongs to exactly its own block. -/
@[simp] theorem mem_iterationBlock {f : E → ℝ} {c : E → F} {theta epsilon0 : ℝ}
    {x : ℕ → E} {t : ℕ → ℝ} {history : ℕ → InnerHistory E} {N b k i : ℕ} :
    (k, i) ∈ iterationBlock f c theta epsilon0 x t history N b ↔
      k < N ∧ i < (history k).length ∧ blockOwner f c theta epsilon0 x t k = b := by
  classical
  simp [iterationBlock, and_assoc]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The blocks cover the entire finite execution, including its two partial blocks. -/
theorem existsUnique_iterationBlock {f : E → ℝ} {c : E → F} {theta epsilon0 : ℝ}
    {x : ℕ → E} {t : ℕ → ℝ} {history : ℕ → InnerHistory E} {N k i : ℕ}
    (hk : k < N) (hi : i < (history k).length) :
    ∃! b, (k, i) ∈ iterationBlock f c theta epsilon0 x t history N b := by
  refine ⟨blockOwner f c theta epsilon0 x t k, ?_, ?_⟩
  · simp [hk, hi]
  · intro b hb
    exact (mem_iterationBlock.mp hb).2.2.symm

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Distinct blocks are disjoint. -/
theorem disjoint_iterationBlock (f : E → ℝ) (c : E → F) (theta epsilon0 : ℝ)
    (x : ℕ → E) (t : ℕ → ℝ) (history : ℕ → InnerHistory E) (N : ℕ)
    {a b : ℕ} (hab : a ≠ b) :
    Disjoint (iterationBlock f c theta epsilon0 x t history N a)
      (iterationBlock f c theta epsilon0 x t history N b) := by
  apply Finset.disjoint_left.mpr
  intro q ha hb
  rcases q with ⟨k, i⟩
  exact hab ((mem_iterationBlock.mp ha).2.2.symm.trans (mem_iterationBlock.mp hb).2.2)

open Classical in
/-- Successful trials in a block, using the actual target objective and actual acceptance. -/
def successfulIterationBlock (params : RegularizationParameters) (p : ℕ)
    (f : E → ℝ) (c : E → F) (theta epsilon0 : ℝ)
    (x : ℕ → E) (t : ℕ → ℝ) (history : ℕ → InnerHistory E) (N b : ℕ) : Finset (ℕ × ℕ) :=
  (iterationBlock f c theta epsilon0 x t history N b).filter fun q =>
    params.eta1 ≤ ratio (TargetLeastSquares.objective f c (t q.1)) p
      ((history q.1).point q.2) ((history q.1).step q.2)

/-- Trial function queries across all inner histories; no outer endpoint is queried twice. -/
def trialQueryPoints (history : ℕ → InnerHistory E) (N : ℕ) : List E :=
  (List.range N).flatMap fun k => (List.range (history k).length).map fun i =>
    (history k).point i + (history k).step i

open Classical in
/-- New derivative queries occur at accepted successors only. The single initial query is
accounted separately, so target changes add no extra original-oracle derivative query. -/
def acceptedQueryPoints (params : RegularizationParameters) (p : ℕ) (f : E → ℝ)
    (c : E → F) (t : ℕ → ℝ) (history : ℕ → InnerHistory E) (N : ℕ) : List E :=
  (List.range N).flatMap fun k =>
    let accepted := (Finset.range (history k).length).filter fun i =>
      params.eta1 ≤ ratio (TargetLeastSquares.objective f c (t k)) p
        ((history k).point i) ((history k).step i)
    (accepted.sort (· ≤ ·)).map fun i => (history k).point (i + 1)

omit [NormedSpace ℝ E] in
/-- Function queries count every actual trial, including rejected trials. -/
theorem length_trialQueryPoints (history : ℕ → InnerHistory E) (N : ℕ) :
    (trialQueryPoints history N).length = ∑ k ∈ Finset.range N, (history k).length := by
  induction N with
  | zero => simp [trialQueryPoints]
  | succ N ih => simpa [trialQueryPoints, List.range_succ, List.flatMap_append,
      Finset.sum_range_succ] using congrArg (· + (history N).length) ih

/-- Derivative query counts add actual accepted trials; initialization remains a separate one. -/
theorem length_acceptedQueryPoints (params : RegularizationParameters) (p : ℕ) (f : E → ℝ)
    (c : E → F) (t : ℕ → ℝ) (history : ℕ → InnerHistory E) (N : ℕ) :
    (acceptedQueryPoints params p f c t history N).length =
      ∑ k ∈ Finset.range N, successCount (fun i =>
        params.eta1 ≤ ratio (TargetLeastSquares.objective f c (t k)) p
          ((history k).point i) ((history k).step i)) (history k).length := by
  classical
  induction N with
  | zero => simp [acceptedQueryPoints]
  | succ N ih =>
    simp only [acceptedQueryPoints, List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
      List.length_map, Finset.length_sort, Finset.sum_range_succ] at *
    simpa only [successCount] using congrArg (· + successCount (fun i =>
      params.eta1 ≤ ratio (TargetLeastSquares.objective f c (t N)) p
        ((history N).point i) ((history N).step i)) (history N).length) ih

end Optimization.TwoPhaseTargets
