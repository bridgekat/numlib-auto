import Numlib.Optimization.OracleFrames

/-!
# Uniform finite-history simulation of derivative-oracle methods

The resisting frame is computed from raw replies, before an objective is selected. Every
history, including histories that cannot arise from a smooth objective, determines a frame.
Only finitely many noninitial queries are simulated; the transformed method returns zero
thereafter. Exposed coordinates include every slot of every nonzero mixed tensor entry.
-/

noncomputable section
open scoped InnerProductSpace

namespace Optimization.DerivativeOracle
open ZeroChains

/-- Coordinates exposed by a complete reply, including all slots of all derivative orders. -/
def Reply.support {n p : ℕ} (r : Reply n p) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ q : Fin p, ∃ v : Fin (q.val + 1) → Fin n,
    (∃ a, v a = i) ∧ r.derivative q (fun a => EuclideanSpace.single (v a) 1) ≠ 0

/-- Membership exhibits a nonzero mixed tensor entry containing the coordinate. -/
@[simp] theorem Reply.mem_support {n p : ℕ} (r : Reply n p) (i : Fin n) :
    i ∈ r.support ↔ ∃ q : Fin p, ∃ v : Fin (q.val + 1) → Fin n,
      (∃ a, v a = i) ∧ r.derivative q (fun a => EuclideanSpace.single (v a) 1) ≠ 0 := by
  classical
  simp [Reply.support]

/-- Every derivative tensor of an arbitrary reply is supported on its exposed coordinates. -/
theorem Reply.tensorSupportedOn {n p : ℕ} (r : Reply n p) (q : Fin p)
    (s : Finset (Fin n)) (hs : r.support ⊆ s) : TensorSupportedOn (r.derivative q) s := by
  rintro v ⟨a, ha⟩
  by_contra hne
  exact ha (hs ((r.mem_support _).mpr ⟨q, v, ⟨a, rfl⟩, hne⟩))

/-- For an actual reply, exposed coordinates are exactly the derivative support. -/
theorem support_oracle {n p : ℕ} (f : Space n → ℝ) (x : Space n) :
    ((oracle p f x).support : Set (Fin n)) = derivativeSupport p f x := by
  ext i
  simp only [Finset.mem_coe, Reply.mem_support, mem_derivativeSupport]
  constructor
  · rintro ⟨q, v, hv, hne⟩
    exact ⟨q.val + 1, by omega, by omega, v, hv, hne⟩
  · rintro ⟨q, hq, hqp, v, hv, hne⟩
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    exact ⟨⟨r, by omega⟩, v, hv, hne⟩

/-- The coordinates exposed by the first `k` replies of a raw history. -/
def historySupport {n p : ℕ} (R : ℕ → Reply n p) (k : ℕ) : Finset (Fin n) :=
  (Finset.range k).biUnion fun j => (R j).support

/-- History support records one earlier reply exposing the coordinate. -/
@[simp] theorem mem_historySupport {n p : ℕ} (R : ℕ → Reply n p) (k : ℕ) (i : Fin n) :
    i ∈ historySupport R k ↔ ∃ j < k, i ∈ (R j).support := by
  classical
  simp [historySupport]

/-- Exposed coordinates increase as a raw history grows. -/
theorem historySupport_mono {n p : ℕ} (R : ℕ → Reply n p) {j k : ℕ} (hjk : j ≤ k) :
    historySupport R j ⊆ historySupport R k := by
  intro i hi
  obtain ⟨l, hl, hi⟩ := (mem_historySupport R j i).mp hi
  exact (mem_historySupport R k i).mpr ⟨l, hl.trans_le hjk, hi⟩

/-- Equal finite prefixes expose the same coordinates. -/
theorem historySupport_congr {n p k : ℕ} {R T : ℕ → Reply n p}
    (h : ∀ j < k, R j = T j) : historySupport R k = historySupport T k := by
  classical
  unfold historySupport
  apply Finset.biUnion_congr rfl
  intro j hj
  rw [h j (Finset.mem_range.mp hj)]

/-- The standard inclusion into a Euclidean space with `K` additional coordinates. -/
def initialFrame (n K : ℕ) : Space n →ₗᵢ[ℝ] Space (n + K) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let c := EuclideanSpace.basisFun (Fin (n + K)) ℝ
  let w := fun i : Fin n => c (Fin.castAdd K i)
  let L := b.toBasis.constr ℝ w
  have hw : Orthonormal ℝ w := c.orthonormal.comp (Fin.castAdd K) (Fin.castAdd_injective n K)
  have hL : L ∘ b.toBasis = w := by
    funext i
    exact b.toBasis.constr_basis ℝ w i
  exact L.isometryOfOrthonormal (v := b.toBasis) b.orthonormal (by rw [hL]; exact hw)

/-- A finite simulation state stores an actual frame and its ambient noninitial queries.
The query at index `j` is the ambient query for iteration `j + 1`. -/
structure FrameState (n K : ℕ) where
  frame : Space n →ₗᵢ[ℝ] Space (n + K)
  query : ℕ → Space (n + K)

/-- All previously generated ambient queries project into the exposed coordinate set. -/
def FrameState.Supported {n K : ℕ} (A : FrameState n K) (k : ℕ)
    (s : Finset (Fin n)) : Prop :=
  ∀ j < k, coordinateSupport (A.frame.toContinuousLinearMap.adjoint (A.query j)) ⊆
    (s : Set (Fin n))

/-- A supported raw-history state admits the next resisting-frame extension with the exact
finite horizon dimension. Its existence is independent of any objective. -/
theorem FrameState.exists_next {n p K k : ℕ} (A : FrameState n K) (M : Method p)
    (R : Fin (k + 1) → Reply n p) (s : Finset (Fin n))
    (hA : A.Supported k s) (hR : ∀ j, (R j).support ⊆ s) (hk : k < K) :
    ∃ V : Space n →ₗᵢ[ℝ] Space (n + K),
      (∀ i ∈ s, V (EuclideanSpace.single i 1) = A.frame (EuclideanSpace.single i 1)) ∧
      (∀ j < k, V.toContinuousLinearMap.adjoint (A.query j) =
        A.frame.toContinuousLinearMap.adjoint (A.query j)) ∧
      (∀ j, (R j).pullback V.toContinuousLinearMap.adjoint =
        (R j).pullback A.frame.toContinuousLinearMap.adjoint) ∧
      coordinateSupport (V.toContinuousLinearMap.adjoint
        (M.next (n + K) k (fun j => (R j).pullback V.toContinuousLinearMap.adjoint))) ⊆
          (s : Set (Fin n)) := by
  obtain ⟨V, hc, hq, hr, hy⟩ := M.exists_frame_extension_next A.frame s
    (fun j : Fin k => A.query j.val) R (fun j => hA j.val j.isLt)
    (fun j q => (R j).tensorSupportedOn q s (hR j)) (by omega)
  exact ⟨V, hc, fun j hj => hq ⟨j, hj⟩, hr, hy⟩

/-- Select the next frame from the finite raw history. An unsupported input state or a
completed horizon leaves the frame unchanged, so this operation is defined on every input. -/
def FrameState.nextFrame {n p K k : ℕ} (A : FrameState n K) (M : Method p)
    (R : Fin (k + 1) → Reply n p) : Space n →ₗᵢ[ℝ] Space (n + K) := by
  classical
  let s := Finset.univ.filter fun i => ∃ j, i ∈ (R j).support
  exact if h : A.Supported k s ∧ k < K then
    Classical.choose (A.exists_next M R s h.1
      (fun j i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨j, hi⟩⟩) h.2)
  else A.frame

/-- The next raw-history state preserves previous ambient queries and appends the method's
actual next query under the chosen frame; it appends zero after the horizon. -/
def FrameState.advance {n p K k : ℕ} (A : FrameState n K) (M : Method p)
    (R : Fin (k + 1) → Reply n p) : FrameState n K where
  frame := A.nextFrame M R
  query j := if j = k then
    if k < K then M.next (n + K) k
      (fun i => (R i).pullback (A.nextFrame M R).toContinuousLinearMap.adjoint) else 0
    else A.query j

/-- A frame change computed solely from a finite history preserves every exposed column,
every earlier query projection, and every lifted full reply. -/
theorem FrameState.nextFrame_spec {n p K k : ℕ} (A : FrameState n K) (M : Method p)
    (R : ℕ → Reply n p) (hA : A.Supported k (historySupport R (k + 1))) (hk : k < K) :
    let V := A.nextFrame M (fun j : Fin (k + 1) => R j.val)
    (∀ i ∈ historySupport R (k + 1),
      V (EuclideanSpace.single i 1) = A.frame (EuclideanSpace.single i 1)) ∧
    (∀ j < k, V.toContinuousLinearMap.adjoint (A.query j) =
      A.frame.toContinuousLinearMap.adjoint (A.query j)) ∧
    (∀ j : Fin (k + 1), (R j.val).pullback V.toContinuousLinearMap.adjoint =
      (R j.val).pullback A.frame.toContinuousLinearMap.adjoint) ∧
    coordinateSupport (V.toContinuousLinearMap.adjoint
      (M.next (n + K) k (fun j : Fin (k + 1) =>
        (R j.val).pullback V.toContinuousLinearMap.adjoint))) ⊆
      (historySupport R (k + 1) : Set (Fin n)) := by
  classical
  have hs : (Finset.univ.filter fun i => ∃ j : Fin (k + 1), i ∈ (R j.val).support) =
      historySupport R (k + 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_historySupport]
    exact ⟨fun ⟨j, hj⟩ => ⟨j.val, j.isLt, hj⟩, fun ⟨j, hj, hi⟩ => ⟨⟨j, hj⟩, hi⟩⟩
  dsimp [FrameState.nextFrame]
  simp only [hs]
  split_ifs with h
  · exact Classical.choose_spec (A.exists_next M (fun j : Fin (k + 1) => R j.val)
      (historySupport R (k + 1)) h.1
      (fun j i hi => (mem_historySupport R (k + 1) i).mpr ⟨j.val, j.isLt, hi⟩) h.2)
  · exact (h ⟨hA, hk⟩).elim

/-- Recursively build a resisting frame and ambient query history from raw replies only. -/
noncomputable def Method.frameRun {p : ℕ} (M : Method p) (n K : ℕ) (R : ℕ → Reply n p) :
    ℕ → FrameState n K
  | 0 => ⟨initialFrame n K, fun _ => 0⟩
  | k + 1 => (M.frameRun n K R k).advance M (fun j : Fin (k + 1) => R j.val)
termination_by k => k

/-- The recursive frame state uses only the received finite prefix, including on histories
that are inconsistent with every objective. -/
theorem Method.frameRun_congr {n p K k : ℕ} (M : Method p) {R T : ℕ → Reply n p}
    (h : ∀ j < k, R j = T j) : M.frameRun n K R k = M.frameRun n K T k := by
  induction k with
  | zero => simp only [Method.frameRun]
  | succ k ih =>
    simp only [Method.frameRun]
    rw [ih (fun j hj => h j (by omega))]
    congr 1
    funext j
    exact h j.val j.isLt

/-- The frame recursion maintains its exposed-coordinate invariant on every raw history. -/
theorem Method.frameRun_supported {n p K : ℕ} (M : Method p) (R : ℕ → Reply n p) (k : ℕ) :
    (M.frameRun n K R k).Supported k (historySupport R k) := by
  classical
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    have hA : (M.frameRun n K R k).Supported k (historySupport R (k + 1)) :=
      fun j hj i hi => historySupport_mono R (by omega) (ih j hj hi)
    intro j hj
    rw [Method.frameRun]
    change coordinateSupport (((M.frameRun n K R k).advance M
      (fun j : Fin (k + 1) => R j.val)).frame.toContinuousLinearMap.adjoint
      (((M.frameRun n K R k).advance M
        (fun j : Fin (k + 1) => R j.val)).query j)) ⊆ _
    by_cases hk : k < K
    · obtain ⟨_, hq, _, hy⟩ := (M.frameRun n K R k).nextFrame_spec M R hA hk
      by_cases hjk : j = k
      · subst j
        simpa only [FrameState.advance, ↓reduceIte, hk] using hy
      · have hj' : j < k := by omega
        simp only [FrameState.advance, hjk, ↓reduceIte]
        rw [hq j hj']
        exact hA j hj'
    · have hf : (M.frameRun n K R k).nextFrame M
          (fun j : Fin (k + 1) => R j.val) = (M.frameRun n K R k).frame := by
        simp [FrameState.nextFrame, hk]
      by_cases hjk : j = k
      · subst j
        simp only [FrameState.advance, ↓reduceIte, hk, map_zero,
          coordinateSupport_zero, Set.empty_subset]
      · have hj' : j < k := by omega
        simpa only [FrameState.advance, hjk, ↓reduceIte, hf] using hA j hj'

/-- Every active recursive step preserves exposed columns and previous projections. -/
theorem Method.frameRun_succ_spec {n p K k : ℕ} (M : Method p) (R : ℕ → Reply n p)
    (hk : k < K) :
    (∀ i ∈ historySupport R (k + 1),
      (M.frameRun n K R (k + 1)).frame (EuclideanSpace.single i 1) =
        (M.frameRun n K R k).frame (EuclideanSpace.single i 1)) ∧
    (∀ j < k, (M.frameRun n K R (k + 1)).frame.toContinuousLinearMap.adjoint
      ((M.frameRun n K R k).query j) =
        (M.frameRun n K R k).frame.toContinuousLinearMap.adjoint
          ((M.frameRun n K R k).query j)) := by
  have hA : (M.frameRun n K R k).Supported k (historySupport R (k + 1)) :=
    fun j hj i hi => historySupport_mono R (by omega) (M.frameRun_supported R k j hj hi)
  simpa only [Method.frameRun, FrameState.advance] using
    And.intro ((M.frameRun n K R k).nextFrame_spec M R hA hk).1
      ((M.frameRun n K R k).nextFrame_spec M R hA hk).2.1

/-- Previously generated ambient queries remain unchanged as the raw history grows. -/
theorem Method.frameRun_query_eq {n p K j l k : ℕ} (M : Method p) (R : ℕ → Reply n p)
    (hj : j < l) (hlk : l ≤ k) :
    (M.frameRun n K R k).query j = (M.frameRun n K R l).query j := by
  induction k with
  | zero =>
    have : l = 0 := by omega
    subst l
    rfl
  | succ k ih =>
    by_cases hl : l ≤ k
    · rw [Method.frameRun]
      simp only [FrameState.advance, show j ≠ k by omega, ↓reduceIte]
      exact ih hl
    · have : l = k + 1 := by omega
      subst l
      rfl

/-- Every later active frame retains columns exposed at an earlier stage. -/
theorem Method.frameRun_columns {n p K l k : ℕ} (M : Method p) (R : ℕ → Reply n p)
    (hlk : l ≤ k) (hk : k ≤ K) :
    ∀ i ∈ historySupport R l,
      (M.frameRun n K R k).frame (EuclideanSpace.single i 1) =
        (M.frameRun n K R l).frame (EuclideanSpace.single i 1) := by
  induction k with
  | zero =>
    have : l = 0 := by omega
    subst l
    intro i hi
    rfl
  | succ k ih =>
    by_cases hl : l ≤ k
    · intro i hi
      rw [(M.frameRun_succ_spec R (by omega : k < K)).1 i
        (historySupport_mono R hlk hi)]
      exact ih hl (by omega) i hi
    · have : l = k + 1 := by omega
      subst l
      intro i hi
      rfl

/-- A later active frame preserves the projected value of every earlier ambient query. -/
theorem Method.frameRun_projection_eq {n p K j l k : ℕ} (M : Method p)
    (R : ℕ → Reply n p) (hj : j < l) (hlk : l ≤ k) (hk : k ≤ K) :
    (M.frameRun n K R k).frame.toContinuousLinearMap.adjoint
        ((M.frameRun n K R k).query j) =
      (M.frameRun n K R l).frame.toContinuousLinearMap.adjoint
        ((M.frameRun n K R l).query j) := by
  induction k with
  | zero =>
    have : l = 0 := by omega
    subst l
    rfl
  | succ k ih =>
    by_cases hl : l ≤ k
    · rw [M.frameRun_query_eq R (show j < k by omega) (Nat.le_succ k)]
      rw [(M.frameRun_succ_spec R (by omega : k < K)).2 j (by omega)]
      exact ih hl (by omega)
    · have : l = k + 1 := by omega
      subst l
      rfl

/-- Lifting any previously received raw reply under a later active frame gives exactly the
same full tensor reply as at the earlier stage. -/
theorem Method.frameRun_reply_eq {n p K j l k : ℕ} (M : Method p)
    (R : ℕ → Reply n p) (hj : j < l) (hlk : l ≤ k) (hk : k ≤ K) :
    (R j).pullback (M.frameRun n K R k).frame.toContinuousLinearMap.adjoint =
      (R j).pullback (M.frameRun n K R l).frame.toContinuousLinearMap.adjoint := by
  apply (R j).pullback_adjoint_eq _ _ (historySupport R l)
  · intro q
    exact (R j).tensorSupportedOn q _
      (fun i hi => (mem_historySupport R l i).mpr ⟨j, hj, hi⟩)
  · exact M.frameRun_columns R hlk hk

/-- At an active stage, the newly appended query is the original method's next query on
exactly the supplied lifted history. -/
theorem Method.frameRun_query_last {n p K k : ℕ} (M : Method p) (R : ℕ → Reply n p)
    (hk : k < K) :
    (M.frameRun n K R (k + 1)).query k = M.next (n + K) k
      (fun j : Fin (k + 1) => (R j.val).pullback
        (M.frameRun n K R (k + 1)).frame.toContinuousLinearMap.adjoint) := by
  simp only [Method.frameRun, FrameState.advance, ↓reduceIte, hk]

/-- Extend a supplied finite history by a fixed zero reply. Its future entries are never
consulted in the corresponding finite simulation. -/
def extendHistory {n p k : ℕ} (R : Fin k → Reply n p) (j : ℕ) : Reply n p :=
  if hj : j < k then R ⟨j, hj⟩ else oracle p (fun _ => 0) 0

/-- Extending a finite history preserves every received reply. -/
@[simp] theorem extendHistory_apply {n p k : ℕ} (R : Fin k → Reply n p) (j : Fin k) :
    extendHistory R j.val = R j := by simp [extendHistory]

/-- The uniform finite-horizon transformed method is specified in every dimension and on
every raw finite history. It returns zero after `K` noninitial queries. -/
def Method.zeroRespectingTransform {p : ℕ} (M : Method p) (K : ℕ) : Method p where
  next n k R := if k < K then
    let A := M.frameRun n K (extendHistory R) (k + 1)
    A.frame.toContinuousLinearMap.adjoint (A.query k)
  else 0

/-- The transformed rule on any active finite history is the projection computed from that
history's raw recursion, independently of how the history is continued. -/
theorem Method.zeroRespectingTransform_next {n p K k : ℕ} (M : Method p)
    (R : ℕ → Reply n p) (hk : k < K) :
    (M.zeroRespectingTransform K).next n k (fun j : Fin (k + 1) => R j.val) =
      (M.frameRun n K R (k + 1)).frame.toContinuousLinearMap.adjoint
        ((M.frameRun n K R (k + 1)).query k) := by
  have he := M.frameRun_congr (n := n) (K := K) (k := k + 1)
    (R := extendHistory (fun j : Fin (k + 1) => R j.val)) (T := R)
    (fun j hj => by simp [extendHistory, hj])
  simp only [Method.zeroRespectingTransform, hk, ↓reduceIte, he]

/-- The transformed method is zero respecting on all objectives, with no smoothness,
zero-chain, or history-consistency assumption. -/
theorem Method.zeroRespectingTransform_isZeroRespecting {p : ℕ} (M : Method p) (K : ℕ) :
    (M.zeroRespectingTransform K).IsZeroRespecting := by
  intro n f
  refine ⟨by simp, ?_⟩
  intro k
  let R := fun j => oracle p f ((M.zeroRespectingTransform K).iterate f j)
  rw [Method.iterate_succ]
  by_cases hk : k < K
  · rw [M.zeroRespectingTransform_next R hk]
    intro i hi
    have hs := M.frameRun_supported R (k + 1) k (by omega) hi
    obtain ⟨j, hj, hmem⟩ := (mem_historySupport R (k + 1) i).mp hs
    exact ⟨j, by omega, by
      rw [← support_oracle]
      exact hmem⟩
  · simp only [Method.zeroRespectingTransform, hk, ↓reduceIte, coordinateSupport_zero,
      Set.empty_subset]

/-- Include the initial zero query in a stored ambient query history. -/
def FrameState.trace {n K : ℕ} (A : FrameState n K) : ℕ → Space (n + K)
  | 0 => 0
  | k + 1 => A.query k

/-- Under the final frame, every active stored query follows the original method's rule
on the final lifts of the raw replies. -/
theorem Method.frameRun_query_next_final {n p K k : ℕ} (M : Method p)
    (R : ℕ → Reply n p) (hk : k < K) :
    (M.frameRun n K R K).query k = M.next (n + K) k
      (fun j : Fin (k + 1) => (R j.val).pullback
        (M.frameRun n K R K).frame.toContinuousLinearMap.adjoint) := by
  rw [M.frameRun_query_eq R (Nat.lt_succ_self k) (by omega : k + 1 ≤ K)]
  rw [M.frameRun_query_last R hk]
  congr 1
  funext j
  exact (M.frameRun_reply_eq R j.isLt (by omega : k + 1 ≤ K) le_rfl).symm

/-- Projecting the final stored trace recovers the actual transformed trace through the
horizon. The assertion holds on every objective, without a regularity assumption. -/
theorem Method.frameRun_projected_trace {n p K : ℕ} (M : Method p) (f : Space n → ℝ)
    (k : ℕ) (hk : k ≤ K) :
    let R := fun j => oracle p f ((M.zeroRespectingTransform K).iterate f j)
    let A := M.frameRun n K R K
    A.frame.toContinuousLinearMap.adjoint (A.trace k) =
      (M.zeroRespectingTransform K).iterate f k := by
  dsimp only
  cases k with
  | zero => simp [FrameState.trace]
  | succ k =>
    let R := fun j => oracle p f ((M.zeroRespectingTransform K).iterate f j)
    change (M.frameRun n K R K).frame.toContinuousLinearMap.adjoint
      ((M.frameRun n K R K).query k) = _
    rw [M.frameRun_projection_eq R (Nat.lt_succ_self k) hk le_rfl]
    rw [Method.iterate_succ, M.zeroRespectingTransform_next R (by omega)]

/-- The final raw-history frame gives an actual oracle simulation through the finite
horizon. The oracle equality is derived from all full derivative tensors and projected
queries, rather than supplied as a certificate. -/
theorem Method.frameRun_simulation {n p K : ℕ} (M : Method p) {f : Space n → ℝ}
    (hf : ContDiff ℝ p f) :
    let R := fun j => oracle p f ((M.zeroRespectingTransform K).iterate f j)
    let A := M.frameRun n K R K
    ∀ k ≤ K, M.iterate (rotate A.frame f) k = A.trace k := by
  dsimp only
  let R := fun j => oracle p f ((M.zeroRespectingTransform K).iterate f j)
  let A := M.frameRun n K R K
  change ∀ k ≤ K, M.iterate (rotate A.frame f) k = A.trace k
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [FrameState.trace]
    | succ k =>
      rw [Method.iterate_succ]
      change M.next (n + K) k _ = A.query k
      rw [M.frameRun_query_next_final R (by omega : k < K)]
      congr 1
      funext j
      rw [ih j.val (by omega) (by omega)]
      rw [rotate, oracle_pullback hf]
      rw [M.frameRun_projected_trace (K := K) f j.val (by omega)]

/-- Every deterministic method has a single zero-respecting finite-horizon transform,
chosen before the objective. For each smooth objective an actual rectangular rotation
matches every simulated iterate and every gradient norm through that horizon. -/
theorem Method.exists_uniform_zeroRespecting_simulation {p : ℕ} (M : Method p) (K : ℕ) :
    ∃ T : Method p, T.IsZeroRespecting ∧
      ∀ n (f : Space n → ℝ), ContDiff ℝ p f →
        ∃ U : Space n →ₗᵢ[ℝ] Space (n + K), ∀ k ≤ K,
          U.toContinuousLinearMap.adjoint (M.iterate (rotate U f) k) = T.iterate f k := by
  refine ⟨M.zeroRespectingTransform K, M.zeroRespectingTransform_isZeroRespecting K, ?_⟩
  intro n f hf
  let R := fun j => oracle p f ((M.zeroRespectingTransform K).iterate f j)
  refine ⟨(M.frameRun n K R K).frame, ?_⟩
  intro k hk
  rw [M.frameRun_simulation hf k hk]
  exact M.frameRun_projected_trace f k hk

end Optimization.DerivativeOracle
