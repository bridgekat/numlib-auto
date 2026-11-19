/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.LinearAlgebra.Matrix.Drazin
import Numlib.LinearAlgebra.Matrix.PerronFrobenius
import NumlibSurface.BenIsraelGreville.Chapter00.Section09
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# The group inverse and finite Markov chains

Section 8.7 of [benIsrael2003generalized] connects the stochastic transition
matrix with state probabilities, recurrence, and the group inverse of
the identity minus the transition matrix.

## Deviations from the source

* **Equation (85)** uses the conditional distribution given the full finite
  history. The multiplicative joint-probability identity also applies when a
  history has probability zero.
* A closed communicating class has no outgoing transition. Communication by
  itself can hold between transient states.
* **Equations (95)–(96)** apply from the first transition. At time zero the
  trajectory has the given initial distribution.
* The absorbing-chain criterion uses reachability to an absorbing state from
  every state. It includes chains whose only state is absorbing.
* The Cesàro average in **Equations (103)–(104)** ends at exponent $n$, so it
  has $n+1$ terms.
* The strict spectral-radius bound in the lazy-chain argument applies to
  the complement of the stationary projection.
-/

namespace BenIsraelGreville.Chapter08

open Matrix MeasureTheory Filter Topology
open scoped BigOperators ENNReal

section Chains

variable {s : Type*} [Fintype s] [DecidableEq s]

/-- **Equations (86)–(87)** of [benIsrael2003generalized], Chapter 8. A
stochastic transition matrix is nonnegative and its rows sum to one. -/
abbrev IsStochasticMatrix (P : Matrix s s ℝ) : Prop :=
  P ∈ rowStochastic ℝ s

/-- **Equations (86)–(87)** of [benIsrael2003generalized], Chapter 8. The
row-sum and all-ones-vector tests for stochasticity agree. -/
theorem isStochasticMatrix_iff_row_sums (P : Matrix s s ℝ) :
    IsStochasticMatrix P ↔ (∀ i j, 0 ≤ P i j) ∧ (∀ i, ∑ j, P i j = 1) :=
  mem_rowStochastic_iff_sum

/-- **Equation (85)** of [benIsrael2003generalized], Chapter 8. The
probability of a finite history followed by a specified state is the
probability of that history times the transition from its last state. -/
structure IsFiniteMarkovChain {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Matrix s s ℝ) (X : ℕ → Ω → s) : Prop where
  /-- The transition matrix is row-stochastic. -/
  stochastic : IsStochasticMatrix P
  /-- Events specifying a state at a given time are measurable. -/
  measurable_state : ∀ t i, MeasurableSet {ω | X t ω = i}
  /-- The next-state probability given a history depends only on its last state. -/
  transition : ∀ (t : ℕ) (path : Fin (t + 1) → s) (j : s),
    μ {ω | (∀ k : Fin (t + 1), X k.val ω = path k) ∧ X (t + 1) ω = j} =
      ENNReal.ofReal (P (path (Fin.last t)) j) * μ {ω | ∀ k : Fin (t + 1), X k.val ω = path k}

/-- **Equations (88)–(89)** of [benIsrael2003generalized], Chapter 8.
The transition probability after `t` steps. -/
def transitionProbability (P : Matrix s s ℝ) (t : ℕ) (i j : s) : ℝ :=
  (P ^ t) i j

/-- At zero steps the transition probabilities are the entries of the identity. -/
theorem transitionProbability_zero (P : Matrix s s ℝ) (i j : s) :
    transitionProbability P 0 i j = if i = j then 1 else 0 := by
  simp [transitionProbability, Matrix.one_apply]

/-- **Equation (89)** of [benIsrael2003generalized], Chapter 8.
The Chapman–Kolmogorov equation includes the zero-step cases. -/
theorem chapmanKolmogorov (P : Matrix s s ℝ) (m n : ℕ) (i j : s) :
    transitionProbability P (m + n) i j =
      ∑ k, transitionProbability P m i k * transitionProbability P n k j := by
  simp only [transitionProbability, pow_add, Matrix.mul_apply]

/-- A stochastic matrix has stochastic powers. -/
theorem stochastic_pow {P : Matrix s s ℝ} (hP : IsStochasticMatrix P) (k : ℕ) :
    IsStochasticMatrix (P ^ k) :=
  (rowStochastic ℝ s).pow_mem hP k

/-- **Section 8.7** of [benIsrael2003generalized]. Positive-time reachability. -/
def LeadsTo (P : Matrix s s ℝ) (i j : s) : Prop :=
  ∃ n : ℕ, 0 < n ∧ 0 < transitionProbability P n i j

/-- **Section 8.7** of [benIsrael2003generalized]. Mutual reachability. -/
def Communicates (P : Matrix s s ℝ) (i j : s) : Prop :=
  LeadsTo P i j ∧ LeadsTo P j i

/-- **Exercise 17(a)** of [benIsrael2003generalized], Chapter 8.
Communication is symmetric. -/
theorem communicates_symm {P : Matrix s s ℝ} {i j : s} (h : Communicates P i j) :
    Communicates P j i := h.symm

/-- **Exercise 17(b)** of [benIsrael2003generalized], Chapter 8.
Reachability is transitive for a stochastic matrix. -/
theorem leadsTo_trans {P : Matrix s s ℝ} (hP : IsStochasticMatrix P) {i j k : s}
    (hij : LeadsTo P i j) (hjk : LeadsTo P j k) : LeadsTo P i k := by
  obtain ⟨a, ha, hia⟩ := hij
  obtain ⟨b, _, hjb⟩ := hjk
  refine ⟨a + b, Nat.add_pos_left ha b, ?_⟩
  rw [chapmanKolmogorov]
  apply (mul_pos hia hjb).trans_le
  exact Finset.single_le_sum
    (fun t _ => mul_nonneg ((stochastic_pow hP a).1 i t) ((stochastic_pow hP b).1 t k))
    (Finset.mem_univ j)

/-- **Exercise 17(b)** of [benIsrael2003generalized], Chapter 8.
Communication is transitive. -/
theorem communicates_trans {P : Matrix s s ℝ} (hP : IsStochasticMatrix P) {i j k : s}
    (hij : Communicates P i j) (hjk : Communicates P j k) : Communicates P i k :=
  ⟨leadsTo_trans hP hij.1 hjk.1, leadsTo_trans hP hjk.2 hij.2⟩

/-- A set of states is closed when transition probabilities to its complement vanish. -/
def IsClosedStateSet (P : Matrix s s ℝ) (S : Set s) : Prop :=
  ∀ i ∈ S, ∀ j ∉ S, P i j = 0

/-- A closed communicating class is nonempty, communicating, and closed. -/
def IsClosedCommunicatingClass (P : Matrix s s ℝ) (S : Set s) : Prop :=
  S.Nonempty ∧ IsClosedStateSet P S ∧ ∀ i ∈ S, ∀ j ∈ S, Communicates P i j

/-- A chain is irreducible when every state can reach every other in positive time. -/
def IsIrreducibleChain (P : Matrix s s ℝ) : Prop :=
  ∀ i j, LeadsTo P i j

/-- A state is absorbing when its single-step return probability is one. -/
def IsAbsorbingState (P : Matrix s s ℝ) (i : s) : Prop :=
  P i i = 1

/-- An absorbing chain has an absorbing state reachable from every state. -/
def IsAbsorbingChain (P : Matrix s s ℝ) : Prop :=
  ∀ i, ∃ j, IsAbsorbingState P j ∧ LeadsTo P i j

/-- A regular chain has a positive matrix among its positive powers. -/
def IsRegularChain (P : Matrix s s ℝ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ i j, 0 < transitionProbability P n i j

/-- A regular chain is irreducible. -/
theorem isIrreducibleChain_of_regular {P : Matrix s s ℝ} (h : IsRegularChain P) :
    IsIrreducibleChain P := by
  obtain ⟨n, hn, hp⟩ := h
  exact fun i j => ⟨n, hn, hp i j⟩

/-- The period is the greatest common divisor of the positive return times,
with zero for an empty set of return times. -/
noncomputable def statePeriod (P : Matrix s s ℝ) (i : s) : ℕ :=
  sSup {d : ℕ | ∀ n : ℕ, 0 < n → 0 < transitionProbability P n i i → d ∣ n}

/-- An ergodic finite chain is irreducible and has period one at every state. -/
def IsErgodicChain (P : Matrix s s ℝ) : Prop :=
  IsIrreducibleChain P ∧ ∀ i, statePeriod P i = 1

/-- **Equations (93) and (100)** of [benIsrael2003generalized], Chapter 8.
A stationary distribution is a probability vector fixed by the transpose. -/
def IsStationaryDistribution (P : Matrix s s ℝ) (π : s → ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧ (∑ i, π i = 1) ∧ Pᵀ *ᵥ π = π

/-- **Equation (97)** of [benIsrael2003generalized], Chapter 8. The
distribution obtained by evolving an initial distribution for `t` steps. -/
def stateDistribution (P : Matrix s s ℝ) (π : s → ℝ) (t : ℕ) : s → ℝ :=
  (Pᵀ ^ t) *ᵥ π

/-- **Equations (95)–(97)** of [benIsrael2003generalized], Chapter 8.
Each new distribution is obtained by one transpose multiplication. -/
theorem stateDistribution_succ (P : Matrix s s ℝ) (π : s → ℝ) (t : ℕ) :
    stateDistribution P π (t + 1) = Pᵀ *ᵥ stateDistribution P π t := by
  rw [stateDistribution, pow_succ', ← mulVec_mulVec, stateDistribution]

/-- A stationary initial distribution remains unchanged. -/
theorem stateDistribution_of_stationary {P : Matrix s s ℝ} {π : s → ℝ}
    (hπ : IsStationaryDistribution P π) (t : ℕ) : stateDistribution P π t = π := by
  induction t with
  | zero => simp [stateDistribution]
  | succ t ih => rw [stateDistribution_succ, ih, hπ.2.2]

private theorem sum_transpose_mulVec {P : Matrix s s ℝ}
    (hP : IsStochasticMatrix P) (v : s → ℝ) : ∑ i, (Pᵀ *ᵥ v) i = ∑ i, v i := by
  simp only [mulVec, dotProduct, transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_mul, sum_row_of_mem_rowStochastic hP i, one_mul]

/-- **Equation (97)** of [benIsrael2003generalized], Chapter 8.
Any convergent trajectory from an initial probability vector has a stationary limit. -/
theorem isStationaryDistribution_of_tendsto_stateDistribution {P : Matrix s s ℝ}
    (hP : IsStochasticMatrix P) {v π : s → ℝ} (hv : ∀ i, 0 ≤ v i) (hs : ∑ i, v i = 1)
    (h : Tendsto (stateDistribution P v) atTop (𝓝 π)) : IsStationaryDistribution P π := by
  refine ⟨fun i => ?_, ?_, ?_⟩
  · apply isClosed_Ici.mem_of_tendsto (tendsto_pi_nhds.mp h i)
    exact Eventually.of_forall fun t => by
      change 0 ≤ ((Pᵀ ^ t) *ᵥ v) i
      rw [← transpose_pow, mulVec, dotProduct]
      exact Finset.sum_nonneg fun j _ => mul_nonneg ((stochastic_pow hP t).1 j i) (hv j)
  · have hsum : Continuous (fun x : s → ℝ => ∑ i, x i) := by fun_prop
    have he (t : ℕ) : (∑ i, stateDistribution P v t i) = 1 := by
      change (∑ i, ((Pᵀ ^ t) *ᵥ v) i) = 1
      rw [← transpose_pow, sum_transpose_mulVec (stochastic_pow hP t), hs]
    have hlim := hsum.continuousAt.tendsto.comp h
    simp only [Function.comp_def, he] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  · have hc : Continuous (fun x : s → ℝ => Pᵀ *ᵥ x) := by
      apply continuous_pi
      intro i
      change Continuous (fun x : s → ℝ => ∑ j, P j i * x j)
      fun_prop
    have hstep := hc.continuousAt.tendsto.comp h
    have hshift := h.comp (tendsto_add_atTop_nat 1)
    simp only [Function.comp_def, stateDistribution_succ] at hshift
    exact tendsto_nhds_unique hstep hshift

end Chains

section GroupInverse

variable {s : Type*} [Fintype s] [DecidableEq s]

private theorem abs_mulVec_pow_le {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    (k : ℕ) (x : s → ℝ) (i : s) :
    |((P ^ k) *ᵥ x) i| ≤ ∑ j, |x j| := by
  change |∑ j, (P ^ k) i j * x j| ≤ _
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_of_nonneg ((stochastic_pow hP k).1 i j)]
  exact mul_le_of_le_one_left (abs_nonneg _) (le_one_of_mem_rowStochastic (stochastic_pow hP k))

private theorem kernel_one_sub_square {P : Matrix s s ℝ} (hP : IsStochasticMatrix P) :
    (1 - P : Matrix s s ℝ).mulVecLin.ker = ((1 - P : Matrix s s ℝ) ^ 2).mulVecLin.ker := by
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply, pow_two, ← mulVec_mulVec]
  let Q : Matrix s s ℝ := 1 - P
  let v := Q *ᵥ x
  change v = 0 ↔ Q *ᵥ v = 0
  refine ⟨fun h => by rw [h, mulVec_zero], fun hv => ?_⟩
  have hvP : P *ᵥ v = v := by
    change (1 - P) *ᵥ v = 0 at hv
    rwa [sub_mulVec, one_mulVec, sub_eq_zero, eq_comm] at hv
  have hxP : P *ᵥ x = x - v := by
    simp [v, Q, sub_mulVec, one_mulVec]
  have hPpow (k : ℕ) : (P ^ k) *ᵥ x = x - (k : ℝ) • v := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, mulVec_sub, mulVec_smul, hxP, hvP,
        Nat.cast_succ, add_smul, one_smul]
      abel
  funext i
  change v i = 0
  by_contra hne
  obtain ⟨k, hk⟩ := exists_nat_gt ((|x i| + ∑ j, |x j|) / |v i|)
  have habs : 0 < |v i| := abs_pos.mpr hne
  have hk' := (div_lt_iff₀ habs).mp hk
  have he : (k : ℝ) * v i = x i - ((P ^ k) *ᵥ x) i := by
    rw [hPpow, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_sub_cancel]
  have hbound : (k : ℝ) * |v i| ≤ |x i| + ∑ j, |x j| := by
    have hcast : |(k : ℝ)| = (k : ℝ) := abs_of_nonneg (Nat.cast_nonneg k)
    rw [← hcast, ← abs_mul, he]
    refine (abs_sub _ _).trans ?_
    linarith [abs_mulVec_pow_le hP k x i]
  exact not_lt_of_ge hbound hk'

/-- **Theorem 9** of [benIsrael2003generalized], Chapter 8. For any row-stochastic
matrix, the identity minus the transition matrix has a unique group inverse. -/
theorem theorem_9 {P : Matrix s s ℝ} (hP : IsStochasticMatrix P) :
    ∃! G : Matrix s s ℝ, IsGroupInverse (1 - P) G := by
  let Q : Matrix s s ℝ := 1 - P
  have hk : Q.rank = (Q ^ 2).rank := by
    have h := (Q.rank_pow_eq_iff_ker_eq (show 1 ≤ (2 : ℕ) by decide)).mpr
      (by simpa only [pow_one] using kernel_one_sub_square hP)
    simpa only [pow_one] using h
  obtain ⟨G, hG, _⟩ := Q.existsUnique_isDrazinInverseAt (k := 1) (by simpa only [pow_one] using hk)
  exact ⟨G, hG.1, fun _ h => h.unique hG.1⟩

/-- The canonical group inverse in **Theorem 9**. -/
noncomputable def stochasticGroupInverse (P : Matrix s s ℝ) (hP : IsStochasticMatrix P) :
    Matrix s s ℝ :=
  Classical.choose (theorem_9 hP).exists

/-- The canonical choice satisfies the group-inverse equations. -/
theorem stochasticGroupInverse_spec (P : Matrix s s ℝ) (hP : IsStochasticMatrix P) :
    IsGroupInverse (1 - P) (stochasticGroupInverse P hP) :=
  Classical.choose_spec (theorem_9 hP).exists

/-- **Equation (104)** of [benIsrael2003generalized], Chapter 8.
The stationary projection obtained from the group inverse. -/
noncomputable def stationaryProjection (P : Matrix s s ℝ) (hP : IsStochasticMatrix P) :
    Matrix s s ℝ :=
  1 - (1 - P) * stochasticGroupInverse P hP

private theorem stationaryProjection_annihilates {P : Matrix s s ℝ} (hP : IsStochasticMatrix P) :
    stationaryProjection P hP * (1 - P) = 0 ∧ (1 - P) * stationaryProjection P hP = 0 := by
  let Q : Matrix s s ℝ := 1 - P
  let G := stochasticGroupInverse P hP
  obtain ⟨hComm, hin, _⟩ := isGroupInverse_iff.mp (stochasticGroupInverse_spec P hP)
  change Commute Q G at hComm
  change Q * G * Q = Q at hin
  change (1 - Q * G) * Q = 0 ∧ Q * (1 - Q * G) = 0
  constructor
  · rw [Matrix.sub_mul, Matrix.one_mul, hin, sub_self]
  · have h : Q * (Q * G) = Q := by rw [hComm.eq, ← Matrix.mul_assoc, hin]
    rw [Matrix.mul_sub, Matrix.mul_one, h, sub_self]

/-- The projection is idempotent and is unchanged by a transition on either side. -/
theorem stationaryProjection_spec {P : Matrix s s ℝ} (hP : IsStochasticMatrix P) :
    let E := stationaryProjection P hP
    E * E = E ∧ P * E = E ∧ E * P = E := by
  intro E
  have ⟨hr, hl⟩ := stationaryProjection_annihilates hP
  change E * (1 - P) = 0 at hr
  change (1 - P) * E = 0 at hl
  refine ⟨?_, ?_, ?_⟩
  · change E * (1 - (1 - P) * stochasticGroupInverse P hP) = E
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hr, Matrix.zero_mul, sub_zero]
  · rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero, eq_comm] at hl
  · rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero, eq_comm] at hr

/-- The stationary projection fixes every vector fixed by the transition matrix. -/
theorem stationaryProjection_mulVec_of_fixed {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    {x : s → ℝ} (hx : P *ᵥ x = x) :
    stationaryProjection P hP *ᵥ x = x := by
  let Q : Matrix s s ℝ := 1 - P
  let G := stochasticGroupInverse P hP
  have hComm : Commute Q G := (stochasticGroupInverse_spec P hP).commute
  have hQ : Q *ᵥ x = 0 := by change (1 - P) *ᵥ x = 0; rw [sub_mulVec, one_mulVec, hx, sub_self]
  change (1 - Q * G) *ᵥ x = x
  rw [sub_mulVec, one_mulVec, hComm.eq, ← mulVec_mulVec, hQ, mulVec_zero, sub_zero]

end GroupInverse

section Cesaro

variable {s : Type*} [Fintype s] [DecidableEq s]

/-- The Cesàro mean with exponents zero through `n`. -/
noncomputable def transitionCesaro (P : Matrix s s ℝ) (n : ℕ) : Matrix s s ℝ :=
  ((n : ℝ) + 1)⁻¹ • ∑ k ∈ Finset.range (n + 1), P ^ k

private theorem transition_telescopes (P : Matrix s s ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, P ^ k) * (1 - P) = 1 - P ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Matrix.add_mul, ih, Matrix.mul_sub, Matrix.mul_one, ← pow_succ]
    abel

private theorem transition_pow_mul_projection {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    (k : ℕ) :
    P ^ k * stationaryProjection P hP = stationaryProjection P hP := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Matrix.mul_assoc, (stationaryProjection_spec hP).2.1, ih]

/-- **Equation (107)** and the transition-matrix formula following it in
[benIsrael2003generalized], Chapter 8. The Cesàro error is a telescoping
difference multiplied by the group inverse and divided by the sample size. -/
theorem transitionCesaro_eq_projection_add {P : Matrix s s ℝ}
    (hP : IsStochasticMatrix P) (n : ℕ) :
    transitionCesaro P n = stationaryProjection P hP +
      ((n : ℝ) + 1)⁻¹ • ((1 - P ^ (n + 1)) * stochasticGroupInverse P hP) := by
  let E := stationaryProjection P hP
  let G := stochasticGroupInverse P hP
  let S := ∑ k ∈ Finset.range (n + 1), P ^ k
  have hE : E + (1 - P) * G = 1 := by
    change 1 - (1 - P) * G + (1 - P) * G = 1
    exact sub_add_cancel _ _
  have hs : S * E = ((n : ℝ) + 1) • E := by
    dsimp only [S]
    rw [Finset.sum_mul]
    simp only [show ∀ k, P ^ k * E = E from transition_pow_mul_projection hP,
      Finset.sum_const, Finset.card_range]
    rw [← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_add, Nat.cast_one]
  have hs' : S * ((1 - P) * G) = (1 - P ^ (n + 1)) * G := by
    rw [← Matrix.mul_assoc, show S * (1 - P) = _ from transition_telescopes P (n + 1)]
  change ((n : ℝ) + 1)⁻¹ • S = E + ((n : ℝ) + 1)⁻¹ • ((1 - P ^ (n + 1)) * G)
  calc
    _ = ((n : ℝ) + 1)⁻¹ • (S * (E + (1 - P) * G)) := by rw [hE, Matrix.mul_one]
    _ = _ := by
      rw [Matrix.mul_add, hs, hs', smul_add, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

private theorem abs_pow_error_mul_entry_le {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    (G : Matrix s s ℝ) (n : ℕ) (i j : s) :
    |((1 - P ^ n) * G) i j| ≤ ∑ k, |G k j| := by
  rw [Matrix.mul_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  apply mul_le_of_le_one_left (abs_nonneg _)
  have h₀ : 0 ≤ (P ^ n) i k := (stochastic_pow hP n).1 i k
  have h₁ : (P ^ n) i k ≤ 1 := le_one_of_mem_rowStochastic (stochastic_pow hP n)
  have h₂ : 0 ≤ (1 : Matrix s s ℝ) i k := by
    rw [Matrix.one_apply]
    split <;> positivity
  have h₃ : (1 : Matrix s s ℝ) i k ≤ 1 := by
    rw [Matrix.one_apply]
    split <;> norm_num
  rw [Matrix.sub_apply, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- **Theorem 10**, first limit in Equation (104) of [benIsrael2003generalized],
Chapter 8. The Cesàro means converge to the stationary projection for
every finite row-stochastic matrix. -/
theorem theorem_10_cesaro {P : Matrix s s ℝ} (hP : IsStochasticMatrix P) :
    Tendsto (transitionCesaro P) atTop (𝓝 (stationaryProjection P hP)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  let E := stationaryProjection P hP
  let G := stochasticGroupInverse P hP
  let C := ∑ k, |G k j|
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * C) atTop (𝓝 0) := by
    simpa only [one_div, zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const C
  let f (n : ℕ) := ((n : ℝ) + 1)⁻¹ * (((1 - P ^ (n + 1)) * G) i j)
  have hf (n : ℕ) : |f n| ≤ ((n : ℝ) + 1)⁻¹ * C := by
    dsimp only [f]
    rw [abs_mul, abs_of_nonneg (show 0 ≤ ((n : ℝ) + 1)⁻¹ by positivity)]
    exact mul_le_mul_of_nonneg_left (abs_pow_error_mul_entry_le hP G (n + 1) i j) (by positivity)
  have hF : Tendsto f atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa only [neg_zero] using ht.neg) ht
      (fun n => (abs_le.mp (hf n)).1) (fun n => (abs_le.mp (hf n)).2)
  have h := (tendsto_const_nhds (x := E i j)).add hF
  have he (n : ℕ) : transitionCesaro P n i j = E i j + f n :=
    congrArg (fun M : Matrix s s ℝ => M i j) (transitionCesaro_eq_projection_add hP n)
  simpa only [add_zero, ← he] using h

/-- The Cesàro means are stochastic matrices. -/
theorem transitionCesaro_stochastic {P : Matrix s s ℝ} (hP : IsStochasticMatrix P) (n : ℕ) :
    IsStochasticMatrix (transitionCesaro P n) := by
  rw [isStochasticMatrix_iff_row_sums]
  have he (i j : s) : transitionCesaro P n i j =
      ((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), (P ^ k) i j := by
    simp only [transitionCesaro, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  constructor
  · intro i j
    rw [he]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => (stochastic_pow hP k).1 i j)
  · intro i
    simp_rw [he, ← Finset.mul_sum, Finset.sum_comm (s := Finset.univ),
      sum_row_of_mem_rowStochastic (stochastic_pow hP _)]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one, mul_one]
    exact inv_mul_cancel₀ (by positivity)

/-- The stationary projection is a stochastic matrix. -/
theorem stationaryProjection_stochastic {P : Matrix s s ℝ} (hP : IsStochasticMatrix P) :
    IsStochasticMatrix (stationaryProjection P hP) := by
  rw [isStochasticMatrix_iff_row_sums]
  have ht (i j : s) :
      Tendsto (fun n => transitionCesaro P n i j) atTop (𝓝 (stationaryProjection P hP i j)) :=
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (theorem_10_cesaro hP) i) j
  constructor
  · intro i j
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds (ht i j)
      (fun n => (transitionCesaro_stochastic hP n).1 i j)
  · intro i
    have hs : Tendsto (fun n => ∑ j, transitionCesaro P n i j) atTop
        (𝓝 (∑ j, stationaryProjection P hP i j)) := tendsto_finsetSum _ fun j _ => ht i j
    simp only [sum_row_of_mem_rowStochastic (transitionCesaro_stochastic hP _)] at hs
    exact tendsto_nhds_unique hs tendsto_const_nhds

end Cesaro

section Stationarity

variable {s : Type*} [Fintype s] [DecidableEq s]

private theorem fixed_by_transition_pow {P : Matrix s s ℝ} {x : s → ℝ}
    (h : P *ᵥ x = x) (k : ℕ) : P ^ k *ᵥ x = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← mulVec_mulVec, h, ih]

private theorem fixed_by_transition_is_constant [Nonempty s]
    {P : Matrix s s ℝ} (hP : IsStochasticMatrix P) (hI : IsIrreducibleChain P)
    {x : s → ℝ} (hx : P *ᵥ x = x) : ∃ c : ℝ, ∀ j, x j = c := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
  refine ⟨x i, fun j => ?_⟩
  obtain ⟨k, _, hj⟩ := hI i j
  have hc := congrFun (fixed_by_transition_pow hx k) i
  have h0 : ∑ l, (P ^ k) i l * (x i - x l) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul _ _ (x i),
      sum_row_of_mem_rowStochastic (stochastic_pow hP k), one_mul]
    change x i - ((P ^ k) *ᵥ x) i = 0
    rw [hc, sub_self]
  have hterm (l : s) : 0 ≤ (P ^ k) i l * (x i - x l) :=
    mul_nonneg ((stochastic_pow hP k).1 i l) (sub_nonneg.mpr (hi l (Finset.mem_univ l)))
  have hz : (P ^ k) i j * (x i - x j) ≤ 0 :=
    (Finset.single_le_sum (fun l _ => hterm l) (Finset.mem_univ j)).trans_eq h0
  have hp := le_antisymm hz (hterm j)
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (ne_of_gt hj))).symm

private theorem transpose_projection_mulVec_of_fixed {P : Matrix s s ℝ}
    (hP : IsStochasticMatrix P) {x : s → ℝ} (hx : Pᵀ *ᵥ x = x) :
    (stationaryProjection P hP)ᵀ *ᵥ x = x := by
  unfold stationaryProjection
  rw [transpose_sub, transpose_one, transpose_mul, transpose_sub, transpose_one, sub_mulVec,
    one_mulVec, ← mulVec_mulVec, sub_mulVec, one_mulVec, hx, sub_self, mulVec_zero, sub_zero]

/-- **Equations (91)–(93)** and **Exercise 24** of [benIsrael2003generalized],
Chapter 8. In an irreducible finite chain, the stationary projection has
identical rows. They form the unique stationary probability distribution,
and every stationary vector is a scalar multiple of it. -/
theorem stationaryDistribution_eq_groupInverse [Nonempty s] {P : Matrix s s ℝ}
    (hP : IsStochasticMatrix P) (hI : IsIrreducibleChain P) :
    ∃ π : s → ℝ, IsStationaryDistribution P π ∧ (∀ j, 0 < π j) ∧
      (∀ i j, stationaryProjection P hP i j = π j) ∧
      ∀ x : s → ℝ, Pᵀ *ᵥ x = x → x = (∑ i, x i) • π := by
  let E := stationaryProjection P hP
  let i₀ : s := Classical.arbitrary s
  let π := E.row i₀
  obtain ⟨_, hPE, hEP⟩ := stationaryProjection_spec hP
  have hrows (i j : s) : E i j = π j := by
    have hfixed : P *ᵥ E.col j = E.col j := by
      rw [← col_mul_eq_mulVec_col, show P * E = E from hPE]
    obtain ⟨c, hc⟩ := fixed_by_transition_is_constant hP hI hfixed
    exact (hc i).trans (hc i₀).symm
  have hE := stationaryProjection_stochastic hP
  have hsumπ : ∑ i, π i = 1 := sum_row_of_mem_rowStochastic hE i₀
  have hnonnegπ (j : s) : 0 ≤ π j := hE.1 i₀ j
  have hπ : IsStationaryDistribution P π := by
    refine ⟨hnonnegπ, hsumπ, ?_⟩
    rw [mulVec_transpose]
    change E.row i₀ ᵥ* P = E.row i₀
    rw [← row_mul_eq_vecMul_row, show E * P = E from hEP]
  have hposπ (j : s) : 0 < π j := by
    obtain ⟨i, _, hpos⟩ := (Finset.sum_pos_iff_of_nonneg fun i _ => hnonnegπ i).mp
      (by rw [hsumπ]; norm_num)
    obtain ⟨k, _, hij⟩ := hI i j
    have h := fixed_by_transition_pow hπ.2.2 k
    rw [← transpose_pow, mulVec_transpose] at h
    rw [← congrFun h j]
    change 0 < ∑ l, π l * (P ^ k) l j
    exact (mul_pos hpos hij).trans_le
      (Finset.single_le_sum (fun l _ => mul_nonneg (hnonnegπ l) ((stochastic_pow hP k).1 l j))
        (Finset.mem_univ i))
  refine ⟨π, hπ, hposπ, hrows, fun x hx => ?_⟩
  have h := transpose_projection_mulVec_of_fixed hP hx
  funext j
  rw [← congrFun h j]
  change ∑ i, E i j * x i = (∑ i, x i) * π j
  simp_rw [hrows, ← Finset.mul_sum]
  exact mul_comm _ _

/-- The positive stationary distribution of an irreducible finite chain is unique. -/
theorem existsUnique_stationaryDistribution [Nonempty s] {P : Matrix s s ℝ}
    (hP : IsStochasticMatrix P) (hI : IsIrreducibleChain P) :
    ∃! π : s → ℝ, IsStationaryDistribution P π := by
  obtain ⟨π, hπ, _, _, hu⟩ := stationaryDistribution_eq_groupInverse hP hI
  refine ⟨π, hπ, fun x hx => ?_⟩
  simpa only [hx.2.1, one_smul] using hu x hx.2.2

/-- **Equation (101)** of [benIsrael2003generalized], Chapter 8.
For irreducible chains, every row of the Cesàro limit is the stationary distribution. -/
theorem transitionCesaro_tendsto_stationary [Nonempty s] {P : Matrix s s ℝ}
    (hP : IsStochasticMatrix P) (hI : IsIrreducibleChain P) :
    ∃ π, IsStationaryDistribution P π ∧ (∀ j, 0 < π j) ∧
      ∀ i j, Tendsto (fun n => transitionCesaro P n i j) atTop (𝓝 (π j)) := by
  obtain ⟨π, hπ, hpos, hE, _⟩ := stationaryDistribution_eq_groupInverse hP hI
  refine ⟨π, hπ, hpos, fun i j => ?_⟩
  simpa only [hE] using tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (theorem_10_cesaro hP) i) j

end Stationarity

section FirstPassage

variable {s : Type*} [Fintype s] [DecidableEq s]

/-- The transition matrix with all arrivals at the target removed. -/
def killedTransition (P : Matrix s s ℝ) (j : s) : Matrix s s ℝ :=
  Matrix.of fun a b => if b = j then 0 else P a b

/-- The first-passage mass at time `n+1` consists of `n` steps avoiding
the target followed by one transition to it. Time zero is excluded. -/
def firstPassageProbability (P : Matrix s s ℝ) (i j : s) : ℕ → ℝ
  | 0 => 0
  | n + 1 => ((killedTransition P j) ^ n * P) i j

/-- The probability of eventual positive-time passage to the target. -/
noncomputable def eventualPassageProbability (P : Matrix s s ℝ) (i j : s) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (firstPassageProbability P i j (n + 1))

/-- The extended sum of the positive times weighted by their first-passage masses. -/
noncomputable def meanFirstPassageTime (P : Matrix s s ℝ) (i j : s) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (((n : ℝ) + 1) * firstPassageProbability P i j (n + 1))

/-- A state is recurrent when its positive-time return probability is one. -/
def IsRecurrentState (P : Matrix s s ℝ) (i : s) : Prop :=
  eventualPassageProbability P i i = 1

/-- A state is transient when it is not recurrent. -/
def IsTransientState (P : Matrix s s ℝ) (i : s) : Prop :=
  ¬IsRecurrentState P i

/-- A chain is recurrent when all of its states are recurrent. -/
def IsRecurrentChain (P : Matrix s s ℝ) : Prop :=
  ∀ i, IsRecurrentState P i

/-- A null recurrent state has infinite mean return time. -/
def IsNullState (P : Matrix s s ℝ) (i : s) : Prop :=
  IsRecurrentState P i ∧ meanFirstPassageTime P i i = ⊤

/-- An ergodic state is nonnull recurrent and aperiodic. -/
def IsErgodicState (P : Matrix s s ℝ) (i : s) : Prop :=
  IsRecurrentState P i ∧ statePeriod P i = 1 ∧ meanFirstPassageTime P i i ≠ ⊤

private theorem killedTransition_nonneg {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    (j : s) : (killedTransition P j).EntrywiseNonneg := by
  intro a b
  by_cases hb : b = j <;> simp [killedTransition, hb, hP.1 a b]

/-- The first-passage masses of a stochastic matrix are nonnegative. -/
theorem firstPassageProbability_nonneg {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    (i j : s) (k : ℕ) : 0 ≤ firstPassageProbability P i j k := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [firstPassageProbability, Matrix.mul_apply]
    exact Finset.sum_nonneg fun a _ =>
      mul_nonneg (pow_apply_nonneg (killedTransition_nonneg hP j) k i a) (hP.1 a j)

private theorem mul_killed_defect_entry (P A : Matrix s s ℝ) (j i k : s) :
    (A * (P - killedTransition P j)) i k = if k = j then (A * P) i j else 0 := by
  by_cases hk : k = j
  · subst k
    simp only [Matrix.mul_apply, Matrix.sub_apply, killedTransition, Matrix.of_apply,
      ite_true, sub_zero]
  · simp only [Matrix.mul_apply, Matrix.sub_apply, killedTransition, Matrix.of_apply,
      ite_eq_right hk, sub_self, mul_zero, Finset.sum_const_zero]

private theorem pow_eq_killed_add_passages (P : Matrix s s ℝ) (j : s) (n : ℕ) :
    P ^ n = (killedTransition P j) ^ n +
      ∑ t ∈ Finset.range n,
        (killedTransition P j) ^ t * (P - killedTransition P j) * P ^ (n - (t + 1)) := by
  let K := killedTransition P j
  let H := P - K
  induction n with
  | zero => simp
  | succ n ih =>
    let T := ∑ t ∈ Finset.range n, K ^ t * H * P ^ (n - (t + 1))
    change P ^ n = K ^ n + T at ih
    change P ^ (n + 1) = K ^ (n + 1) +
      ∑ t ∈ Finset.range (n + 1), K ^ t * H * P ^ (n + 1 - (t + 1))
    have hK : K ^ n * P = K ^ (n + 1) + K ^ n * H := by
      rw [pow_succ, show H = P - K from rfl, Matrix.mul_sub]
      abel
    have hT : T * P =
        ∑ t ∈ Finset.range n, K ^ t * H * P ^ (n + 1 - (t + 1)) := by
      dsimp only [T]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro t ht
      have hlt := Finset.mem_range.mp ht
      rw [Matrix.mul_assoc (K ^ t * H), ← pow_succ,
        show n - (t + 1) + 1 = n + 1 - (t + 1) by omega]
    rw [pow_succ P, ih, Matrix.add_mul, hK, hT, Finset.sum_range_succ, Nat.sub_self, pow_zero,
      Matrix.mul_one]
    abel

/-- **Exercise 20** of [benIsrael2003generalized], Chapter 8.
The renewal identity splits the transition by the first positive visit
to the target and follows it with a return transition. -/
theorem exercise_8_20 (P : Matrix s s ℝ) (i j : s) (n : ℕ) :
    transitionProbability P (n + 1) i j =
      ∑ t ∈ Finset.range (n + 1),
        firstPassageProbability P i j (t + 1) * transitionProbability P (n - t) j j := by
  let K := killedTransition P j
  let H := P - K
  have hK : (K ^ (n + 1)) i j = 0 := by
    rw [pow_succ, Matrix.mul_apply]
    simp [K, killedTransition]
  have he := congrArg (fun M : Matrix s s ℝ => M i j) (pow_eq_killed_add_passages P j (n + 1))
  change (P ^ (n + 1)) i j = (K ^ (n + 1) +
    ∑ t ∈ Finset.range (n + 1), K ^ t * H * P ^ (n + 1 - (t + 1))) i j at he
  rw [Matrix.add_apply, hK, zero_add, Matrix.sum_apply] at he
  change (P ^ (n + 1)) i j = _
  rw [he]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.mul_apply]
  simp only [show H = P - killedTransition P j from rfl, mul_killed_defect_entry,
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [show n + 1 - (t + 1) = n - t by omega]
  rfl

/-- The mass of paths avoiding the target through the first `n` steps. -/
def survivalProbability (P : Matrix s s ℝ) (i j : s) (n : ℕ) : ℝ :=
  ((killedTransition P j) ^ n *ᵥ 1) i

private theorem killed_defect_mulVec_one {P : Matrix s s ℝ} (hP : IsStochasticMatrix P) (j : s) :
    (1 : s → ℝ) - (killedTransition P j) *ᵥ 1 = P.col j := by
  have he : (P - killedTransition P j) *ᵥ (1 : s → ℝ) =
      1 - killedTransition P j *ᵥ (1 : s → ℝ) := by
    rw [sub_mulVec, hP.2]
  rw [← he]
  funext i
  change (∑ k, (P i k - if k = j then 0 else P i k) * 1) = P i j
  simp_rw [mul_one, show ∀ a : ℝ, ∀ b : Prop, ∀ [Decidable b],
    a - (if b then 0 else a) = if b then a else 0 from by
      intro a b inst
      split <;> simp]
  simp

/-- The first-passage mass is the drop in the avoidance probability. -/
theorem firstPassageProbability_eq_survival_sub {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    (i j : s) (n : ℕ) :
    firstPassageProbability P i j (n + 1) =
      survivalProbability P i j n - survivalProbability P i j (n + 1) := by
  let K := killedTransition P j
  change (K ^ n * P) i j = (K ^ n *ᵥ 1) i - (K ^ (n + 1) *ᵥ 1) i
  rw [pow_succ, ← mulVec_mulVec]
  change (K ^ n * P).col j i = (K ^ n *ᵥ 1 - K ^ n *ᵥ (K *ᵥ 1)) i
  rw [← mulVec_sub, show (1 : s → ℝ) - K *ᵥ 1 = P.col j from killed_defect_mulVec_one hP j,
    col_mul_eq_mulVec_col]

/-- The mass of passage within `n` steps and the mass of survival sum to one. -/
theorem sum_firstPassageProbability {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    (i j : s) (n : ℕ) :
    ∑ k ∈ Finset.range n, firstPassageProbability P i j (k + 1) =
      1 - survivalProbability P i j n := by
  induction n with
  | zero => simp [survivalProbability]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, firstPassageProbability_eq_survival_sub hP]
    ring

end FirstPassage

section ReturnTimes

variable {s : Type*} [Fintype s] [DecidableEq s]

private theorem survivalProbability_nonneg {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    (i j : s) (n : ℕ) : 0 ≤ survivalProbability P i j n := by
  change 0 ≤ ∑ k, ((killedTransition P j) ^ n) i k * 1
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (pow_apply_nonneg (killedTransition_nonneg hP j) n i k) zero_le_one

private theorem survivalProbability_antitone {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    (i j : s) : Antitone (survivalProbability P i j) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := firstPassageProbability_nonneg hP i j (n + 1)
  rwa [firstPassageProbability_eq_survival_sub hP, sub_nonneg] at h

private theorem survivalProbability_lt_one_of_pos_transition {P : Matrix s s ℝ}
    (hP : IsStochasticMatrix P) (i j : s) {k : ℕ} (hk : 0 < k)
    (hpos : 0 < transitionProbability P k i j) : survivalProbability P i j k < 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have he : transitionProbability P (n + 1) i j ≤
      ∑ t ∈ Finset.range (n + 1), firstPassageProbability P i j (t + 1) := by
    rw [exercise_8_20]
    apply Finset.sum_le_sum
    intro t _
    exact mul_le_of_le_one_right (firstPassageProbability_nonneg hP i j (t + 1))
      (le_one_of_mem_rowStochastic (stochastic_pow hP (n - t)))
  have hp := hpos.trans_le he
  rw [sum_firstPassageProbability hP] at hp
  linarith

open scoped Matrix.Norms.Operator in
/-- If every state can reach the target, the killed matrix has spectral radius
strictly less than one. Passage is then certain and has finite mean. -/
theorem killedTransition_complexSpectralRadius_lt_one {P : Matrix s s ℝ}
    (hP : IsStochasticMatrix P) (j : s) (hReach : ∀ i, LeadsTo P i j) :
    (killedTransition P j).complexSpectralRadius < 1 := by
  let : Nonempty s := ⟨j⟩
  choose k hk hp using hReach
  let N := Finset.univ.sup k
  have hN (i : s) : k i ≤ N := Finset.le_sup (Finset.mem_univ i)
  have hpos : 0 < N := (hk j).trans_le (hN j)
  have hs (i : s) : survivalProbability P i j N < 1 :=
    (survivalProbability_antitone hP i j (hN i)).trans_lt
      (survivalProbability_lt_one_of_pos_transition hP i j (hk i) (hp i))
  obtain ⟨i₀, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => survivalProbability P i j N) Finset.univ_nonempty
  let c := survivalProbability P i₀ j N
  let K := killedTransition P j
  have hnorm : ‖K ^ N‖ ≤ c := by
    apply linfty_opNorm_le_of_forall_sum_le (survivalProbability_nonneg hP i₀ j N)
    intro i
    calc
      (∑ k, |(K ^ N) i k|) = ∑ k, (K ^ N) i k :=
        Finset.sum_congr rfl fun k _ => abs_of_nonneg
          (pow_apply_nonneg (killedTransition_nonneg hP j) N i k)
      _ ≤ c := by
        simpa only [c, K, survivalProbability, mulVec, dotProduct, Pi.one_apply, mul_one] using
          hmax i (Finset.mem_univ i)
  have hρ : (K ^ N).complexSpectralRadius < 1 := by
    calc
      _ ≤ (‖K ^ N‖₊ : ℝ≥0∞) := complexSpectralRadius_le_linfty_opNNNorm (K ^ N)
      _ = ENNReal.ofReal ‖K ^ N‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal hnorm
      _ < 1 := ENNReal.ofReal_lt_one.mpr (hs i₀)
  rw [complexSpectralRadius_pow K (Nat.ne_of_gt hpos)] at hρ
  exact lt_of_not_ge fun h => not_lt_of_ge (one_le_pow₀ h) hρ

omit [DecidableEq s] in
private theorem continuous_matrix_mulVec_one_apply (i : s) :
    Continuous (fun A : Matrix s s ℝ => (A *ᵥ 1) i) := by
  change Continuous (fun A : Matrix s s ℝ => ∑ j, A i j * 1)
  fun_prop

private theorem tendsto_survivalProbability_zero {P : Matrix s s ℝ} {j : s}
    (hρ : (killedTransition P j).complexSpectralRadius < 1) (i : s) :
    Tendsto (survivalProbability P i j) atTop (𝓝 0) := by
  have h := (tendsto_pow_iff_complexSpectralRadius_lt_one _).mpr hρ
  change Tendsto (fun n : ℕ => (killedTransition P j ^ n *ᵥ 1) i) atTop (𝓝 0)
  simpa only [Function.comp_def, zero_mulVec, Pi.zero_apply] using
    (continuous_matrix_mulVec_one_apply i).continuousAt.tendsto.comp h

/-- If every state can reach the target, eventual passage has probability one. -/
theorem eventualPassageProbability_eq_one {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    (i j : s) (hReach : ∀ k, LeadsTo P k j) :
    eventualPassageProbability P i j = 1 := by
  have hρ := killedTransition_complexSpectralRadius_lt_one hP j hReach
  have hp (n : ℕ) := firstPassageProbability_nonneg hP i j (n + 1)
  have hf : HasSum (fun n : ℕ => firstPassageProbability P i j (n + 1)) 1 := by
    apply (hasSum_iff_tendsto_nat_of_nonneg hp 1).mpr
    simp_rw [sum_firstPassageProbability hP]
    simpa only [sub_zero] using tendsto_const_nhds.sub (tendsto_survivalProbability_zero hρ i)
  rw [eventualPassageProbability, ← ENNReal.ofReal_tsum_of_nonneg hp hf.summable,
    hf.tsum_eq, ENNReal.ofReal_one]

/-- Every finite irreducible chain is recurrent. -/
theorem isRecurrentChain_of_irreducible {P : Matrix s s ℝ}
    (hP : IsStochasticMatrix P) (hI : IsIrreducibleChain P) : IsRecurrentChain P :=
  fun i => eventualPassageProbability_eq_one hP i i (fun k => hI k i)

private theorem sum_weighted_firstPassageProbability {P : Matrix s s ℝ}
    (hP : IsStochasticMatrix P) (i j : s) (n : ℕ) :
    ∑ t ∈ Finset.range n, ((t : ℝ) + 1) * firstPassageProbability P i j (t + 1) =
      ∑ t ∈ Finset.range n, survivalProbability P i j t -
        (n : ℝ) * survivalProbability P i j n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih,
      firstPassageProbability_eq_survival_sub hP, Nat.cast_succ]
    ring

private theorem tendsto_mul_survivalProbability_zero {P : Matrix s s ℝ}
    (hP : IsStochasticMatrix P) {i j : s} (hρ : (killedTransition P j).complexSpectralRadius < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) * survivalProbability P i j n) atTop (𝓝 0) := by
  let K := killedTransition P j
  let ρ := K.complexSpectralRadius
  have hρR : ρ.toReal < 1 := by
    have hρfin := ne_of_lt (hρ.trans ENNReal.one_lt_top)
    simpa using (ENNReal.toReal_lt_toReal hρfin ENNReal.one_ne_top).mpr hρ
  obtain ⟨q, hqρ, hq₁⟩ := exists_between hρR
  have hq₀ : 0 < q := ENNReal.toReal_nonneg.trans_lt hqρ
  let a := q⁻¹
  have ha : 1 < a := (one_lt_inv₀ hq₀).mpr hq₁
  have ha₀ : 0 < a := zero_lt_one.trans ha
  have hρa : (a • K).complexSpectralRadius < 1 := by
    have hm : (‖a‖₊ : ℝ≥0∞) = ENNReal.ofReal a := by
      rw [← enorm_eq_nnnorm, ← ofReal_norm, Real.norm_of_nonneg ha₀.le]
    have hρfinite : ρ ≠ ⊤ := ne_of_lt (hρ.trans ENNReal.one_lt_top)
    rw [complexSpectralRadius_smul, hm]
    change ENNReal.ofReal a * ρ < 1
    rw [← ENNReal.ofReal_toReal hρfinite, ← ENNReal.ofReal_mul ha₀.le, ENNReal.ofReal_lt_one]
    change q⁻¹ * ρ.toReal < 1
    rw [mul_comm, ← div_eq_mul_inv, div_lt_one hq₀]
    exact hqρ
  have h := (tendsto_pow_iff_complexSpectralRadius_lt_one _).mpr hρa
  have hc : Tendsto (fun n : ℕ => (((a • K) ^ n) *ᵥ 1) i) atTop (𝓝 0) := by
    simpa only [Function.comp_def, survivalProbability, zero_mulVec, Pi.zero_apply] using
      (continuous_matrix_mulVec_one_apply i).continuousAt.tendsto.comp h
  have ht : Tendsto (fun n : ℕ => (a - 1)⁻¹ * (((a • K) ^ n) *ᵥ 1) i) atTop (𝓝 0) := by
    simpa only [mul_zero] using hc.const_mul ((a - 1)⁻¹)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
  · intro n
    exact mul_nonneg (Nat.cast_nonneg _) (survivalProbability_nonneg hP i j n)
  · intro n
    have hb := one_add_mul_le_pow (a := a - 1) (by linarith) n
    rw [show 1 + (a - 1) = a by ring] at hb
    have hn : (n : ℝ) ≤ (a - 1)⁻¹ * a ^ n := by
      rw [mul_comm, ← div_eq_mul_inv, le_div_iff₀ (sub_pos.mpr ha)]
      linarith
    change (n : ℝ) * survivalProbability P i j n ≤ (a - 1)⁻¹ * (((a • K) ^ n) *ᵥ 1) i
    rw [smul_pow, smul_mulVec, Pi.smul_apply, smul_eq_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hn (survivalProbability_nonneg hP i j n)

/-- The mean first-passage time to an accessible target is the corresponding
row sum of the killed transition’s Neumann series. -/
theorem meanFirstPassageTime_eq_killed_inverse {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    (i j : s) (hReach : ∀ k, LeadsTo P k j) :
    meanFirstPassageTime P i j =
      ENNReal.ofReal (((1 - killedTransition P j)⁻¹ *ᵥ 1) i) := by
  let K := killedTransition P j
  let M := (1 - K)⁻¹
  have hρ := killedTransition_complexSpectralRadius_lt_one hP j hReach
  have hM := (hasSum_pow_inv_one_sub_of_complexSpectralRadius_lt_one hρ).tendsto_sum_nat
  have ht : Tendsto (fun n => ∑ t ∈ Finset.range n, survivalProbability P i j t)
      atTop (𝓝 ((M *ᵥ 1) i)) := by
    have h := (continuous_matrix_mulVec_one_apply i).continuousAt.tendsto.comp hM
    simpa only [Function.comp_def, Matrix.sum_mulVec, Finset.sum_apply, survivalProbability] using h
  have hp (n : ℕ) : 0 ≤ ((n : ℝ) + 1) * firstPassageProbability P i j (n + 1) :=
    mul_nonneg (by positivity) (firstPassageProbability_nonneg hP i j _)
  have hsum : HasSum (fun n : ℕ => ((n : ℝ) + 1) * firstPassageProbability P i j (n + 1))
      ((M *ᵥ 1) i) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg hp _).mpr
    simp_rw [sum_weighted_firstPassageProbability hP]
    simpa only [sub_zero] using ht.sub (tendsto_mul_survivalProbability_zero hP hρ)
  rw [meanFirstPassageTime, ← ENNReal.ofReal_tsum_of_nonneg hp hsum.summable, hsum.tsum_eq]

/-- **Equation (94)** of [benIsrael2003generalized], Chapter 8.
A positive stationary probability is the reciprocal of the mean positive
return time in an irreducible finite chain. -/
theorem meanReturnTime_eq_inverse_stationary {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    (hI : IsIrreducibleChain P) {π : s → ℝ} (hπ : IsStationaryDistribution P π)
    (hpos : ∀ j, 0 < π j) (j : s) :
    meanFirstPassageTime P j j = ENNReal.ofReal ((π j)⁻¹) := by
  let K := killedTransition P j
  let M := (1 - K)⁻¹
  let m := M *ᵥ (1 : s → ℝ)
  have hReach (i : s) := hI i j
  have hρ := killedTransition_complexSpectralRadius_lt_one hP j hReach
  have hu : IsUnit (1 - K) := isUnit_one_sub_of_complexSpectralRadius_lt_one hρ
  have hm : (1 - K) *ᵥ m = 1 := by
    change (1 - K) *ᵥ ((1 - K)⁻¹ *ᵥ 1) = 1
    rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hu), one_mulVec]
  have hπP : π ᵥ* P = π := by rw [← mulVec_transpose, hπ.2.2]
  have hπK : π ᵥ* (1 - K) = Pi.single j (π j) := by
    rw [vecMul_sub, vecMul_one]
    funext k
    by_cases hk : k = j
    · subst k
      simp [K, killedTransition, Matrix.vecMul, dotProduct]
    · have he : (π ᵥ* K) k = π k := by
        simpa only [Matrix.vecMul, dotProduct, K, killedTransition, Matrix.of_apply,
          ite_eq_right hk] using congrFun hπP k
      rw [Pi.sub_apply, he, sub_self, Pi.single_eq_of_ne hk]
  have h1 := congrArg (dotProduct π) hm
  rw [dotProduct_mulVec, hπK, dotProduct_comm (Pi.single j (π j)), dotProduct_single,
    show π ⬝ᵥ (1 : s → ℝ) = 1 by simpa [dotProduct] using hπ.2.1] at h1
  have h2 : m j = (π j)⁻¹ := by
    apply (eq_div_iff (ne_of_gt (hpos j))).mpr at h1
    simpa only [one_div] using h1
  rw [meanFirstPassageTime_eq_killed_inverse hP j j hReach]
  exact congrArg ENNReal.ofReal h2

/-- **Theorem 7**, Equation (90) of [benIsrael2003generalized], Chapter 8.
For an irreducible finite chain, the Cesàro limit of the transition
probabilities is the reciprocal of the mean positive return time. -/
theorem theorem_7 {P : Matrix s s ℝ} (hP : IsStochasticMatrix P) (hI : IsIrreducibleChain P)
    (i j : s) :
    Tendsto (fun n => transitionCesaro P n i j) atTop
      (𝓝 ((meanFirstPassageTime P j j).toReal)⁻¹) := by
  let : Nonempty s := ⟨i⟩
  obtain ⟨π, hπ, hpos, ht⟩ := transitionCesaro_tendsto_stationary hP hI
  rw [meanReturnTime_eq_inverse_stationary hP hI hπ hpos j,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (hpos j).le), inv_inv]
  exact ht i j

end ReturnTimes

section PowerLimits

variable {s : Type*} [Fintype s] [DecidableEq s]

open scoped Matrix.Norms.Operator in
private theorem complexSpectralRadius_le_one_of_stochastic {P : Matrix s s ℝ}
    (hP : IsStochasticMatrix P) : P.complexSpectralRadius ≤ 1 := by
  have hn : ‖P‖ ≤ 1 := by
    apply linfty_opNorm_le_of_forall_sum_le zero_le_one
    intro i
    simp_rw [abs_of_nonneg (hP.1 i _), sum_row_of_mem_rowStochastic hP]
    exact le_rfl
  have h := complexSpectralRadius_le_linfty_opNNNorm P
  rw [← enorm_eq_nnnorm, ← ofReal_norm] at h
  exact h.trans (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hn)

/-- **Exercise 15** of [benIsrael2003generalized], Chapter 8. A nonempty
row-stochastic matrix has spectral radius one. -/
theorem exercise_8_15 [Nonempty s] {P : Matrix s s ℝ} (hP : IsStochasticMatrix P) :
    P.complexSpectralRadius = 1 := by
  refine le_antisymm (complexSpectralRadius_le_one_of_stochastic hP) ?_
  have hn : (1 : s → ℂ) ≠ 0 := by
    intro h
    have he := congrFun h (Classical.arbitrary s)
    simp at he
  have he : complexify P *ᵥ (1 : s → ℂ) = 1 := by
    change complexify P *ᵥ (fun _ => (1 : ℂ)) = fun _ => (1 : ℂ)
    simpa only [hP.2, Pi.one_apply, Complex.ofReal_one] using
      complexify_mulVec_ofReal P (1 : s → ℝ)
  have hspec : (1 : ℂ) ∈ spectrum ℂ (complexify P) :=
    (mem_spectrum_iff_exists_mulVec_eq_smul _ _).mpr ⟨1, hn, by simpa only [one_smul] using he⟩
  simpa using nnnorm_le_complexSpectralRadius hspec

private theorem norm_le_one_of_stochastic_eigen {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    {x : s → ℂ} (hx : x ≠ 0) {z : ℂ} (h : complexify P *ᵥ x = z • x) : ‖z‖ ≤ 1 := by
  have hspec : z ∈ spectrum ℂ (complexify P) :=
    (mem_spectrum_iff_exists_mulVec_eq_smul _ _).mpr ⟨x, hx, h⟩
  have hz := (nnnorm_le_complexSpectralRadius hspec).trans
    (complexSpectralRadius_le_one_of_stochastic hP)
  rwa [ENNReal.coe_le_one_iff, ← NNReal.coe_le_one, coe_nnnorm] at hz

private theorem projection_complexify_fixes {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    {x : s → ℂ} (hx : complexify P *ᵥ x = x) :
    complexify (stationaryProjection P hP) *ᵥ x = x := by
  let G := stochasticGroupInverse P hP
  let Q : Matrix s s ℝ := 1 - P
  have hComm : Commute Q G := (stochasticGroupInverse_spec P hP).commute
  have hQ : complexify Q *ᵥ x = 0 := by
    change complexify (1 - P) *ᵥ x = 0
    rw [complexify_sub, complexify_one, sub_mulVec, one_mulVec, hx, sub_self]
  have he : complexify (Q * G) = complexify G * complexify Q := by
    rw [hComm.eq, complexify_mul]
  change complexify (1 - Q * G) *ᵥ x = x
  rw [complexify_sub, complexify_one, sub_mulVec, one_mulVec, he, ← mulVec_mulVec,
    hQ, mulVec_zero, sub_zero]

omit [DecidableEq s] in
private theorem projection_annihilates_nonzero_eigen {E K : Matrix s s ℝ}
    (hEK : E * K = 0) {μ : ℂ} (hμ : μ ≠ 0) {x : s → ℂ}
    (hx : complexify K *ᵥ x = μ • x) :
    complexify E *ᵥ x = 0 := by
  have he : complexify E *ᵥ (complexify K *ᵥ x) = 0 := by
    rw [mulVec_mulVec, ← complexify_mul, hEK, complexify_zero, zero_mulVec]
  rw [hx, mulVec_smul, smul_eq_zero] at he
  exact he.resolve_left hμ

private theorem tendsto_pow_of_projection_sub {P E : Matrix s s ℝ}
    (hPE : P * E = E) (hEP : E * P = E) (hEE : E * E = E)
    (hρ : (P - E).complexSpectralRadius < 1) :
    Tendsto (fun n : ℕ => P ^ n) atTop (𝓝 E) := by
  have hE (k : ℕ) : P ^ k * E = E := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Matrix.mul_assoc, hPE, ih]
  have hpow (k : ℕ) : (P - E) ^ (k + 1) = P ^ (k + 1) - E := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ (P - E), ih, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hE, hEP,
        hEE, ← pow_succ]
      abel
  have h := (tendsto_pow_iff_complexSpectralRadius_lt_one (P - E)).mpr hρ
  have h' := h.comp (tendsto_add_atTop_nat 1)
  have h'' : Tendsto (fun n => P ^ (n + 1) - E + E) atTop (𝓝 ((0 : Matrix s s ℝ) + E)) := by
    simpa only [Function.comp_def, hpow] using h'.add tendsto_const_nhds
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [sub_add_cancel, zero_add] using h''

/-- The lazy transition retains the current state with probability `a`. -/
def lazyTransition (P : Matrix s s ℝ) (a : ℝ) : Matrix s s ℝ :=
  a • 1 + (1 - a) • P

private theorem norm_convex_combination_complex_lt_one (a : ℝ) (ha : 0 < a) (ha₁ : a < 1)
    (z : ℂ) (hz : ‖z‖ ≤ 1) (hne : z ≠ 1) :
    ‖(a : ℂ) + ((1 - a : ℝ) : ℂ) * z‖ < 1 := by
  let w := (a : ℂ) + ((1 - a : ℝ) : ℂ) * z
  have hsq : ‖w‖ ^ 2 = a + (1 - a) * ‖z‖ ^ 2 - a * (1 - a) * ‖z - 1‖ ^ 2 := by
    simp only [w, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  have hzSq := (sq_le_sq₀ (norm_nonneg z) zero_le_one).mpr hz
  have h1 := mul_le_mul_of_nonneg_left hzSq (sub_nonneg.mpr ha₁.le)
  have h2 := mul_pos (mul_pos ha (sub_pos.mpr ha₁))
    (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)))
  have hw : ‖w‖ ^ 2 < 1 := by nlinarith
  exact (sq_lt_sq₀ (norm_nonneg w) zero_le_one).mp (by simpa using hw)

/-- **Theorem 10**, second limit in Equation (104) of [benIsrael2003generalized],
Chapter 8. Every lazy transition with strictly positive holding and
transition probabilities converges to the original stationary projection. -/
theorem theorem_10_lazy {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    (a : ℝ) (ha : 0 < a) (ha₁ : a < 1) :
    Tendsto (fun n : ℕ => (lazyTransition P a) ^ n) atTop (𝓝 (stationaryProjection P hP)) := by
  let E := stationaryProjection P hP
  let B := lazyTransition P a
  let K := B - E
  obtain ⟨hEE, hPE, hEP⟩ := stationaryProjection_spec hP
  have hOne : a + (1 - a) = 1 := by ring
  have hBE : B * E = E := by
    change (a • 1 + (1 - a) • P) * E = E
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, hPE,
      ← add_smul, hOne, one_smul]
  have hEB : E * B = E := by
    change E * (a • 1 + (1 - a) • P) = E
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, hEP,
      ← add_smul, hOne, one_smul]
  have hEK : E * K = 0 := by
    change E * (B - E) = 0
    rw [Matrix.mul_sub, hEB, hEE, sub_self]
  refine tendsto_pow_of_projection_sub hBE hEB hEE ?_
  apply spectralRadius_lt_one_of_forall_norm_lt
  intro μ hμ
  by_cases hμ₀ : μ = 0
  · simp [hμ₀]
  obtain ⟨x, hx₀, hx⟩ := (mem_spectrum_iff_exists_mulVec_eq_smul _ _).mp hμ
  have hEx := projection_annihilates_nonzero_eigen hEK hμ₀ hx
  have hβ : ((1 - a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr ha₁).ne'
  let z := (μ - (a : ℂ)) / ((1 - a : ℝ) : ℂ)
  have he : (a : ℂ) • x + ((1 - a : ℝ) : ℂ) • (complexify P *ᵥ x) = μ • x := by
    change complexify (a • 1 + (1 - a) • P - E) *ᵥ x = μ • x at hx
    rwa [complexify_sub, complexify_add, complexify_smul, complexify_smul, complexify_one,
      sub_mulVec, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, hEx, sub_zero] at hx
  have hz : complexify P *ᵥ x = z • x := by
    funext i
    have hei := congrFun he i
    change (a : ℂ) * x i + ((1 - a : ℝ) : ℂ) * (complexify P *ᵥ x) i = μ * x i at hei
    change (complexify P *ᵥ x) i = (μ - (a : ℂ)) / ((1 - a : ℝ) : ℂ) * x i
    rw [div_mul_eq_mul_div, eq_div_iff hβ]
    linear_combination hei
  have hne : z ≠ 1 := by
    intro h
    rw [h, one_smul] at hz
    exact hx₀ ((projection_complexify_fixes hP hz).symm.trans hEx)
  have hμeq : (a : ℂ) + ((1 - a : ℝ) : ℂ) * z = μ := by
    dsimp only [z]
    field_simp
    ring
  rw [← hμeq]
  exact norm_convex_combination_complex_lt_one a ha ha₁ z
    (norm_le_one_of_stochastic_eigen hP hx₀ hz) hne

end PowerLimits

section Periods

variable {s : Type*} [Fintype s] [DecidableEq s]

private theorem common_return_divisors_bddAbove {P : Matrix s s ℝ} {i : s}
    (hi : LeadsTo P i i) :
    BddAbove {d : ℕ | ∀ n : ℕ, 0 < n → 0 < transitionProbability P n i i → d ∣ n} := by
  obtain ⟨n, hn, hp⟩ := hi
  exact ⟨n, fun d hd => Nat.le_of_dvd hn (hd n hn hp)⟩

/-- The period divides every positive return time when a return is possible. -/
theorem statePeriod_dvd_return {P : Matrix s s ℝ} {i : s} {n : ℕ}
    (hn : 0 < n) (hp : 0 < transitionProbability P n i i) : statePeriod P i ∣ n := by
  have h := Nat.sSup_mem
    (show {d : ℕ | ∀ k : ℕ, 0 < k → 0 < transitionProbability P k i i → d ∣ k}.Nonempty
      from ⟨1, fun _ _ _ => one_dvd _⟩)
    (common_return_divisors_bddAbove (show LeadsTo P i i from ⟨n, hn, hp⟩))
  exact h n hn hp

private theorem transitionProbability_pos_add {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    {i j k : s} {n m : ℕ} (hn : 0 < transitionProbability P n i j)
    (hm : 0 < transitionProbability P m j k) : 0 < transitionProbability P (n + m) i k := by
  rw [chapmanKolmogorov]
  exact (mul_pos hn hm).trans_le (Finset.single_le_sum
    (fun t _ => mul_nonneg ((stochastic_pow hP n).1 i t) ((stochastic_pow hP m).1 t k))
    (Finset.mem_univ j))

/-- **Exercise 23** of [benIsrael2003generalized], Chapter 8, period part.
Communicating states have the same period. -/
theorem statePeriod_eq_of_communicates {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    {i j : s} (h : Communicates P i j) : statePeriod P i = statePeriod P j := by
  have hdiv {i j : s} (h : Communicates P i j) :
      statePeriod P j ≤ statePeriod P i := by
    have hb := common_return_divisors_bddAbove (leadsTo_trans hP h.1 h.2)
    apply le_csSup hb
    intro n hn hp
    obtain ⟨a, ha, hia⟩ := h.1
    obtain ⟨b, hb', hjb⟩ := h.2
    have hd₁ := statePeriod_dvd_return (Nat.add_pos_left hb' a)
      (transitionProbability_pos_add hP hjb hia)
    have hd₂ := statePeriod_dvd_return (Nat.add_pos_left (Nat.add_pos_left hb' n) a)
      (transitionProbability_pos_add hP (transitionProbability_pos_add hP hjb hp) hia)
    have hd := Nat.dvd_sub hd₂ hd₁
    rwa [show b + n + a - (b + a) = n by omega] at hd
  exact le_antisymm (hdiv (communicates_symm h)) (hdiv h)

/-- A regular chain has period one at every state. -/
theorem isErgodicChain_of_regular {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    (hreg : IsRegularChain P) : IsErgodicChain P := by
  refine ⟨isIrreducibleChain_of_regular hreg, fun i => ?_⟩
  obtain ⟨n, hn, hpos⟩ := hreg
  have hnext : 0 < transitionProbability P (n + 1) i i := by
    obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg fun j _ => hP.1 i j).mp
      (by rw [sum_row_of_mem_rowStochastic hP]; norm_num)
    rw [show n + 1 = 1 + n by omega]
    exact transitionProbability_pos_add hP (show 0 < transitionProbability P 1 i j by
      simpa [transitionProbability] using hj) (hpos j i)
  have hset : {d : ℕ | ∀ k : ℕ, 0 < k → 0 < transitionProbability P k i i → d ∣ k} = {1} := by
    ext d
    constructor
    · intro hd
      have h₁ := hd n hn (hpos i i)
      have h₂ := hd (n + 1) (Nat.succ_pos _) hnext
      have h := Nat.dvd_sub h₂ h₁
      rw [Nat.add_sub_cancel_left] at h
      exact Set.mem_singleton_iff.mpr (Nat.dvd_one.mp h)
    · rintro rfl
      exact fun _ _ _ => one_dvd _
  rw [statePeriod, hset, csSup_singleton]

end Periods

section ErgodicLimit

variable {s : Type*} [Fintype s] [DecidableEq s]

private theorem norm_complex_sub_sq (x y : ℂ) :
    ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * (x * star y).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

private theorem re_finset_sum {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    (∑ j ∈ S, f j).re = ∑ j ∈ S, (f j).re := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih => simp [Finset.sum_insert, hj, Complex.add_re, ih]

omit [DecidableEq s] in
private theorem convex_complex_eq_of_positive_weight {w : s → ℝ} {x : s → ℂ} {y : ℂ}
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (havg : ∑ i, (w i : ℂ) * x i = y) (hx : ∀ i, ‖x i‖ ≤ ‖y‖)
    {i : s} (hi : 0 < w i) : x i = y := by
  have hc : ∑ j, w j * (x j * star y).re = ‖y‖ ^ 2 := by
    have he := congrArg (fun z : ℂ => (z * star y).re) havg
    calc
      (∑ j, w j * (x j * star y).re) = ((∑ j, (w j : ℂ) * x j) * star y).re := by
        rw [Finset.sum_mul, re_finset_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [mul_assoc]
        simp [Complex.mul_re]
      _ = (y * star y).re := he
      _ = ‖y‖ ^ 2 := by
        simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.star_def,
          Complex.conj_re, Complex.conj_im]
        ring
  have he : ∑ j, w j * ‖x j - y‖ ^ 2 = (∑ j, w j * ‖x j‖ ^ 2) - ‖y‖ ^ 2 := by
    simp_rw [norm_complex_sub_sq, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hs, one_mul]
    have hfactor : ∑ j, w j * (2 * (x j * star y).re) = 2 * ‖y‖ ^ 2 := by
      rw [← hc, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hfactor]
    ring
  have hle : (∑ j, w j * ‖x j‖ ^ 2) ≤ ‖y‖ ^ 2 := by
    rw [← one_mul (‖y‖ ^ 2), ← hs, Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hx j)) (hw j)
  have hterm (j : s) : 0 ≤ w j * ‖x j - y‖ ^ 2 := mul_nonneg (hw j) (sq_nonneg _)
  have hz : w i * ‖x i - y‖ ^ 2 = 0 := le_antisymm
    ((Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)).trans
      (by rw [he]; exact sub_nonpos.mpr hle)) (hterm i)
  have hnorm := (mul_eq_zero.mp hz).resolve_left hi.ne'
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith : ‖x i - y‖ = 0))

private theorem complex_eigen_pow {P : Matrix s s ℝ} {x : s → ℂ} {z : ℂ}
    (hz : complexify P *ᵥ x = z • x) (n : ℕ) : complexify (P ^ n) *ᵥ x = z ^ n • x := by
  rw [complexify_pow]
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← mulVec_mulVec, hz, mulVec_smul, ih, smul_smul, ← pow_succ']

private theorem unit_eigenvalue_eq_one_of_ergodic {P : Matrix s s ℝ}
    (hP : IsStochasticMatrix P) (hErg : IsErgodicChain P)
    {z : ℂ} (hz₁ : ‖z‖ = 1) {x : s → ℂ} (hx₀ : x ≠ 0)
    (hz : complexify P *ᵥ x = z • x) : z = 1 := by
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, x i₀ ≠ 0 := by
    by_contra! h
    exact hx₀ (funext h)
  have hne : (Finset.univ : Finset s).Nonempty := ⟨i₀, Finset.mem_univ _⟩
  obtain ⟨i, _, hm⟩ := Finset.exists_max_image Finset.univ (fun i => ‖x i‖) hne
  have hi : x i ≠ 0 := by
    intro h
    have hb := hm i₀ (Finset.mem_univ i₀)
    rw [h, norm_zero] at hb
    exact (not_le_of_gt (norm_pos_iff.mpr hi₀)) hb
  have hr (n : ℕ) (hp : 0 < transitionProbability P n i i) : z ^ n = 1 := by
    let y := z ^ n * x i
    let w := (P ^ n).row i
    have e : ∑ j, (w j : ℂ) * x j = y := congrFun (complex_eigen_pow hz n) i
    have hyn : ‖y‖ = ‖x i‖ := by simp [y, norm_pow, hz₁]
    have hxi : x i = y := convex_complex_eq_of_positive_weight
      (fun j => (stochastic_pow hP n).1 i j) (sum_row_of_mem_rowStochastic (stochastic_pow hP n) i)
      e (fun j => by rw [hyn]; exact hm j (Finset.mem_univ j)) hp
    apply mul_right_cancel₀ hi
    simpa only [one_mul] using hxi.symm
  have hbd := common_return_divisors_bddAbove (hErg.1 i i)
  have hd : orderOf z ≤ statePeriod P i := le_csSup hbd
    (fun n _ hn => orderOf_dvd_of_pow_eq_one (hr n hn))
  obtain ⟨k, hk, hret⟩ := hErg.1 i i
  have horder : orderOf z ≠ 0 := by
    intro h0
    have he := orderOf_dvd_of_pow_eq_one (hr k hret)
    rw [h0, Nat.zero_dvd] at he
    exact (Nat.ne_of_gt hk) he
  rw [hErg.2 i] at hd
  exact orderOf_eq_one_iff.mp (by omega)

private theorem tendsto_pow_of_peripheral_trivial {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    (hunit : ∀ {z : ℂ}, ‖z‖ = 1 → ∀ {x : s → ℂ}, x ≠ 0 →
      complexify P *ᵥ x = z • x → z = 1) :
    Tendsto (fun n : ℕ => P ^ n) atTop (𝓝 (stationaryProjection P hP)) := by
  let E := stationaryProjection P hP
  let K := P - E
  obtain ⟨hEE, hPE, hEP⟩ := stationaryProjection_spec hP
  have hEK : E * K = 0 := by
    change E * (P - E) = 0
    rw [Matrix.mul_sub, hEP, hEE, sub_self]
  refine tendsto_pow_of_projection_sub hPE hEP hEE ?_
  apply spectralRadius_lt_one_of_forall_norm_lt
  intro μ hμ
  by_cases hμ₀ : μ = 0
  · simp [hμ₀]
  obtain ⟨x, hx₀, hx⟩ := (mem_spectrum_iff_exists_mulVec_eq_smul _ _).mp hμ
  have hEx := projection_annihilates_nonzero_eigen hEK hμ₀ hx
  have hPx : complexify P *ᵥ x = μ • x := by
    change complexify (P - E) *ᵥ x = μ • x at hx
    rwa [complexify_sub, sub_mulVec, hEx, sub_zero] at hx
  have hbound := norm_le_one_of_stochastic_eigen hP hx₀ hPx
  refine lt_of_le_of_ne hbound (fun h => ?_)
  have h1 := hunit h hx₀ hPx
  rw [h1, one_smul] at hPx
  exact hx₀ ((projection_complexify_fixes hP hPx).symm.trans hEx)

/-- The powers of an irreducible, aperiodic transition matrix converge to
the stationary projection. -/
theorem theorem_10_ergodic {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    (hErg : IsErgodicChain P) :
    Tendsto (fun n : ℕ => P ^ n) atTop (𝓝 (stationaryProjection P hP)) :=
  tendsto_pow_of_peripheral_trivial hP (unit_eigenvalue_eq_one_of_ergodic hP hErg)

/-- **Theorem 10**, regular part of the last limit in Equation (104) of
[benIsrael2003generalized], Chapter 8. Every regular transition matrix
converges to its stationary projection. -/
theorem theorem_10_regular {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    (hreg : IsRegularChain P) :
    Tendsto (fun n : ℕ => P ^ n) atTop (𝓝 (stationaryProjection P hP)) :=
  theorem_10_ergodic hP (isErgodicChain_of_regular hP hreg)

private theorem absorbing_apply_of_ne {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    {i j : s} (hi : IsAbsorbingState P i) (hj : j ≠ i) : P i j = 0 := by
  have hsum : ∑ k, (P i k - (if k = i then 1 else 0)) = 0 := by
    rw [Finset.sum_sub_distrib, sum_row_of_mem_rowStochastic hP]
    simp
  have hnonneg (k : s) : 0 ≤ P i k - (if k = i then 1 else 0) := by
    by_cases hk : k = i
    · subst k
      change P i i = 1 at hi
      simp [hi]
    · simpa only [ite_eq_right hk, sub_zero] using hP.1 i k
  have hz := le_antisymm ((Finset.single_le_sum (fun k _ => hnonneg k)
    (Finset.mem_univ j)).trans_eq hsum) (hnonneg j)
  simpa only [ite_eq_right hj, sub_zero] using hz

/-- A state is absorbing exactly when its singleton is a closed communicating class. -/
theorem isAbsorbingState_iff_singleton_closed {P : Matrix s s ℝ}
    (hP : IsStochasticMatrix P) (i : s) :
    IsAbsorbingState P i ↔ IsClosedCommunicatingClass P ({i} : Set s) := by
  constructor
  · intro hi
    refine ⟨⟨i, rfl⟩, ?_, ?_⟩
    · intro j hj k hk
      rw [Set.mem_singleton_iff.mp hj]
      exact absorbing_apply_of_ne hP hi hk
    · intro j hj k hk
      rw [Set.mem_singleton_iff.mp hj, Set.mem_singleton_iff.mp hk]
      change P i i = 1 at hi
      have h : LeadsTo P i i := ⟨1, by decide, by simp [transitionProbability, hi]⟩
      exact ⟨h, h⟩
  · rintro ⟨_, hclosed, _⟩
    have hc := sum_row_of_mem_rowStochastic hP i
    rw [Finset.sum_eq_single i] at hc
    · exact hc
    · intro j _ hj
      exact hclosed i rfl j hj
    · simp

private theorem complex_absorbing_mulVec {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    {i : s} (hi : IsAbsorbingState P i) (x : s → ℂ) : (complexify P *ᵥ x) i = x i := by
  change (∑ j, (P i j : ℂ) * x j) = x i
  rw [Finset.sum_eq_single i]
  · change P i i = 1 at hi
    rw [hi, Complex.ofReal_one, one_mul]
  · intro j _ hj
    rw [absorbing_apply_of_ne hP hi hj, Complex.ofReal_zero, zero_mul]
  · simp

private theorem unit_eigenvalue_eq_one_of_absorbing {P : Matrix s s ℝ}
    (hP : IsStochasticMatrix P) (habs : IsAbsorbingChain P) {z : ℂ} (hz₁ : ‖z‖ = 1)
    {x : s → ℂ} (hx₀ : x ≠ 0) (hz : complexify P *ᵥ x = z • x) : z = 1 := by
  by_contra hne
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, x i₀ ≠ 0 := by
    by_contra! h
    exact hx₀ (funext h)
  obtain ⟨i, _, hm⟩ := Finset.exists_max_image Finset.univ (fun i => ‖x i‖)
    ⟨i₀, Finset.mem_univ i₀⟩
  have hi : x i ≠ 0 := by
    intro h
    have hb := hm i₀ (Finset.mem_univ i₀)
    rw [h, norm_zero] at hb
    exact (not_le_of_gt (norm_pos_iff.mpr hi₀)) hb
  obtain ⟨j, hj, n, _, hn⟩ := habs i
  have hjz : x j = z * x j := (complex_absorbing_mulVec hP hj x).symm.trans (congrFun hz j)
  have hj₀ : x j = 0 := by
    by_contra hjne
    apply hne
    apply mul_right_cancel₀ hjne
    simpa only [one_mul] using hjz.symm
  let y := z ^ n * x i
  let w := (P ^ n).row i
  have he : ∑ k, (w k : ℂ) * x k = y := congrFun (complex_eigen_pow hz n) i
  have hyn : ‖y‖ = ‖x i‖ := by simp [y, norm_pow, hz₁]
  have hjy : x j = y := convex_complex_eq_of_positive_weight
    (fun k => (stochastic_pow hP n).1 i k) (sum_row_of_mem_rowStochastic (stochastic_pow hP n) i)
    he (fun k => by rw [hyn]; exact hm k (Finset.mem_univ k)) hn
  have hy : 0 < ‖y‖ := hyn.symm ▸ norm_pos_iff.mpr hi
  rw [← hjy, hj₀, norm_zero] at hy
  exact (lt_irrefl 0) hy

/-- **Theorem 10**, absorbing part of the last limit in Equation (104) of
[benIsrael2003generalized], Chapter 8. If every state reaches an absorbing
state, the transition powers converge to the stationary projection. -/
theorem theorem_10_absorbing {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    (habs : IsAbsorbingChain P) :
    Tendsto (fun n : ℕ => P ^ n) atTop (𝓝 (stationaryProjection P hP)) :=
  tendsto_pow_of_peripheral_trivial hP (unit_eigenvalue_eq_one_of_absorbing hP habs)

/-- **Theorem 10**, Equations (104)–(107) of [benIsrael2003generalized], Chapter 8.
The stationary projection equals the Cesàro and lazy limits for every
finite transition matrix. It equals the ordinary power limit when the
chain is regular or absorbing. -/
theorem theorem_10 {P : Matrix s s ℝ} (hP : IsStochasticMatrix P) :
    Tendsto (transitionCesaro P) atTop (𝓝 (stationaryProjection P hP)) ∧
    (∀ a : ℝ, 0 < a → a < 1 →
      Tendsto (fun n : ℕ => (lazyTransition P a) ^ n) atTop (𝓝 (stationaryProjection P hP))) ∧
    (IsRegularChain P ∨ IsAbsorbingChain P →
      Tendsto (fun n : ℕ => P ^ n) atTop (𝓝 (stationaryProjection P hP))) :=
  ⟨theorem_10_cesaro hP, theorem_10_lazy hP,
    fun h => h.elim (theorem_10_regular hP) (theorem_10_absorbing hP)⟩

/-- **Theorem 8**, Equations (98)–(103) of [benIsrael2003generalized], Chapter 8.
For an ergodic chain every row converges to the same strictly positive
stationary distribution, with entries the reciprocals of mean return times. -/
theorem theorem_8 [Nonempty s] {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    (hErg : IsErgodicChain P) :
    ∃ π : s → ℝ, IsStationaryDistribution P π ∧ (∀ j, 0 < π j) ∧
      (∀ i j, Tendsto (fun n => transitionProbability P n i j) atTop (𝓝 (π j))) ∧
      (∀ j, π j = ((meanFirstPassageTime P j j).toReal)⁻¹) ∧
      ∀ x : s → ℝ, IsStationaryDistribution P x → x = π := by
  obtain ⟨π, hπ, hpos, hrows, huniq⟩ := stationaryDistribution_eq_groupInverse hP hErg.1
  refine ⟨π, hπ, hpos, fun i j => ?_, fun j => ?_, fun x hx => ?_⟩
  · simpa only [transitionProbability, hrows] using
      tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (theorem_10_ergodic hP hErg) i) j
  · rw [meanReturnTime_eq_inverse_stationary hP hErg.1 hπ hpos,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (hpos j).le), inv_inv]
  · simpa only [hx.2.1, one_smul] using huniq x hx.2.2

/-- The limit in **Theorem 8** also gives convergence from any initial
state distribution of total mass one. -/
theorem stateDistribution_tendsto_of_ergodic [Nonempty s] {P : Matrix s s ℝ}
    (hP : IsStochasticMatrix P) (hErg : IsErgodicChain P) :
    ∃ π, IsStationaryDistribution P π ∧ ∀ x : s → ℝ, (∑ i, x i) = 1 →
      Tendsto (stateDistribution P x) atTop (𝓝 π) := by
  obtain ⟨π, hπ, _, hrows, _⟩ := stationaryDistribution_eq_groupInverse hP hErg.1
  refine ⟨π, hπ, fun x hx => ?_⟩
  have hc : Continuous (fun A : Matrix s s ℝ => Aᵀ *ᵥ x) := by
    apply continuous_pi
    intro j
    change Continuous (fun A : Matrix s s ℝ => ∑ i, A i j * x i)
    fun_prop
  have he : (stationaryProjection P hP)ᵀ *ᵥ x = π := by
    funext j
    change ∑ i, stationaryProjection P hP i j * x i = π j
    simp_rw [hrows, ← Finset.mul_sum, hx, mul_one]
  have h := hc.continuousAt.tendsto.comp (theorem_10_ergodic hP hErg)
  change Tendsto (fun n : ℕ => (Pᵀ ^ n) *ᵥ x) atTop (𝓝 π)
  simpa only [he, Function.comp_def, transpose_pow] using h

end ErgodicLimit

section Exercises

variable {s : Type*} [Fintype s] [DecidableEq s]

/-- **Exercise 16** of [benIsrael2003generalized], Chapter 8. Decreasing any
entry of a stochastic matrix strictly decreases the spectral radius when
the resulting matrix remains nonnegative and irreducible. -/
theorem exercise_8_16 [Nonempty s] {A B : Matrix s s ℝ}
    (hP : IsStochasticMatrix (A + B)) (hA : A.IsIrreducible)
    (hB : B.EntrywiseNonneg) (hB₀ : B ≠ 0) : A.complexSpectralRadius < 1 := by
  have hAB : A ≤ₑ A + B := fun i j => le_add_of_nonneg_right (hB i j)
  have hρ := (complexSpectralRadius_le_of_entrywiseLE hA.nonneg hAB).trans_eq
    (exercise_8_15 hP)
  refine lt_of_le_of_ne hρ (fun he => ?_)
  obtain ⟨x, hx, hxA⟩ := hA.exists_pos_vecMul_eq
  rw [he, ENNReal.toReal_one, one_smul] at hxA
  have hb : (x ᵥ* B) ⬝ᵥ (1 : s → ℝ) = 0 := by
    have hv := congrArg (dotProduct x) hP.2
    rw [dotProduct_mulVec, vecMul_add, hxA, add_dotProduct] at hv
    linarith
  obtain ⟨i, j, hij⟩ : ∃ i j, 0 < B i j := by
    by_contra! h
    apply hB₀
    ext i j
    exact le_antisymm (h i j) (hB i j)
  have hv₀ (k : s) : 0 ≤ (x ᵥ* B) k :=
    Finset.sum_nonneg fun l _ => mul_nonneg (hx l).le (hB l k)
  have hv : 0 < (x ᵥ* B) j := (mul_pos (hx i) hij).trans_le
    (Finset.single_le_sum (fun k _ => mul_nonneg (hx k).le (hB k j)) (Finset.mem_univ i))
  have hh := hv.trans_le (Finset.single_le_sum (fun k _ => hv₀ k) (Finset.mem_univ j))
  rw [dotProduct] at hb
  simp only [Pi.one_apply, mul_one] at hb
  rw [hb] at hh
  exact (lt_irrefl 0) hh

/-- **Exercise 18** of [benIsrael2003generalized], Chapter 8. A finite
stochastic matrix is reducible exactly when it has a block upper-triangular
reindexing with two nonempty blocks. -/
theorem exercise_8_18 {P : Matrix s s ℝ} (hP : IsStochasticMatrix P) :
    ¬IsIrreducibleChain P ↔ ∃ (p q : ℕ) (e : Fin p ⊕ Fin q ≃ s)
      (B : Matrix (Fin p) (Fin p) ℝ) (C : Matrix (Fin p) (Fin q) ℝ)
      (D : Matrix (Fin q) (Fin q) ℝ),
      0 < p ∧ 0 < q ∧ P.submatrix e e = fromBlocks B C 0 D := by
  rw [← BenIsraelGreville.Chapter00.isReducible_iff_blockTriangular]
  rcases subsingleton_or_nontrivial s with hs | hs
  · have hirr : IsIrreducibleChain P := by
      intro i j
      have hsum := sum_row_of_mem_rowStochastic hP i
      rw [Finset.sum_eq_single j] at hsum
      · exact ⟨1, Nat.one_pos, by simp [transitionProbability, hsum]⟩
      · intro k _ hk
        exact (hk (Subsingleton.elim k j)).elim
      · simp
    have hred : ¬BenIsraelGreville.Chapter00.isReducible P := by
      rintro ⟨S, ⟨i, hi⟩, ⟨j, hj⟩, _⟩
      exact hj ((Subsingleton.elim i j) ▸ hi)
    simp [hirr, hred]
  · have h := BenIsraelGreville.Chapter00.isIrreducible_iff hP.1
    rw [Matrix.isIrreducible_iff_exists_pow_pos hP.1] at h
    change IsIrreducibleChain P ↔ ¬BenIsraelGreville.Chapter00.isReducible P at h
    exact not_iff_comm.mp h.symm

/-- In **Exercise 18**, the lower diagonal block represents the transition
matrix on a nonempty closed set. -/
theorem exercise_8_18_closed_block {P : Matrix s s ℝ} (hP : IsStochasticMatrix P)
    {p q : ℕ} {e : Fin p ⊕ Fin q ≃ s} {B : Matrix (Fin p) (Fin p) ℝ}
    {C : Matrix (Fin p) (Fin q) ℝ} {D : Matrix (Fin q) (Fin q) ℝ} (hq : 0 < q)
    (he : P.submatrix e e = fromBlocks B C 0 D) :
    (Set.range (e ∘ Sum.inr)).Nonempty ∧ IsClosedStateSet P (Set.range (e ∘ Sum.inr)) ∧
      IsStochasticMatrix D := by
  have hzero (i : Fin q) (j : Fin p) : P (e (Sum.inr i)) (e (Sum.inl j)) = 0 :=
    congrFun (congrFun he (Sum.inr i)) (Sum.inl j)
  have hrestrict (i j : Fin q) : P (e (Sum.inr i)) (e (Sum.inr j)) = D i j :=
    congrFun (congrFun he (Sum.inr i)) (Sum.inr j)
  refine ⟨⟨e (Sum.inr ⟨0, hq⟩), ⟨⟨0, hq⟩, rfl⟩⟩, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩ j hj
    obtain ⟨k | k, rfl⟩ := e.surjective j
    · exact hzero i k
    · exact (hj ⟨k, rfl⟩).elim
  · rw [isStochasticMatrix_iff_row_sums]
    refine ⟨fun i j => hrestrict i j ▸ hP.1 _ _, fun i => ?_⟩
    have hh := sum_row_of_mem_rowStochastic hP (e (Sum.inr i))
    rw [← Equiv.sum_comp e, Fintype.sum_sum_type] at hh
    simpa only [hzero, hrestrict, Finset.sum_const_zero, zero_add] using hh

/-- The three-state transition matrix in **Exercise 17(c)**. -/
noncomputable def exercise_8_17_matrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; (1 / 2 : ℝ), 1 / 2, 0; 1 / 3, 2 / 3, 0]

private theorem exercise_8_17_stochastic : IsStochasticMatrix exercise_8_17_matrix := by
  rw [isStochasticMatrix_iff_row_sums]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [exercise_8_17_matrix]
  · intro i
    fin_cases i <;> norm_num [exercise_8_17_matrix, Fin.sum_univ_succ]

private theorem exercise_8_17_middle_return (n : ℕ) :
    firstPassageProbability exercise_8_17_matrix 1 1 (n + 2) = 0 := by
  have hzero (a : Fin 3) :
      (killedTransition exercise_8_17_matrix 1 * exercise_8_17_matrix) a 1 = 0 := by
    fin_cases a <;>
      norm_num [killedTransition, exercise_8_17_matrix, Matrix.mul_apply, Fin.sum_univ_succ]
  change (killedTransition exercise_8_17_matrix 1 ^ (n + 1) * exercise_8_17_matrix) 1 1 = 0
  rw [pow_succ, Matrix.mul_assoc, Matrix.mul_apply]
  simp [hzero]

private theorem exercise_8_17_last_column (i : Fin 3) : exercise_8_17_matrix i 2 = 0 := by
  fin_cases i <;> norm_num [exercise_8_17_matrix]

/-- **Exercise 17(c)** of [benIsrael2003generalized], Chapter 8. In the
three-state example, the first state is absorbing, the last two are transient,
and the last state does not communicate with any state. -/
theorem exercise_8_17c :
    IsStochasticMatrix exercise_8_17_matrix ∧ IsAbsorbingState exercise_8_17_matrix 0 ∧
    IsTransientState exercise_8_17_matrix 1 ∧ IsTransientState exercise_8_17_matrix 2 ∧
    ∀ i, ¬Communicates exercise_8_17_matrix 2 i := by
  refine ⟨exercise_8_17_stochastic, rfl, ?_, ?_, fun i h => ?_⟩
  · intro h
    change eventualPassageProbability exercise_8_17_matrix 1 1 = 1 at h
    rw [eventualPassageProbability, tsum_eq_single (0 : ℕ)] at h
    · norm_num [firstPassageProbability, exercise_8_17_matrix] at h
    · intro n hn
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      rw [show k.succ + 1 = k + 2 by omega, exercise_8_17_middle_return, ENNReal.ofReal_zero]
  · intro h
    change eventualPassageProbability exercise_8_17_matrix 2 2 = 1 at h
    simp [eventualPassageProbability, firstPassageProbability, Matrix.mul_apply,
      exercise_8_17_last_column] at h
  · obtain ⟨n, hn, hpos⟩ := h.2
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simp [transitionProbability, pow_succ, Matrix.mul_apply, exercise_8_17_last_column] at hpos

/-- **Exercise 24**, Equation (94) of [benIsrael2003generalized], Chapter 8.
The reciprocals of the mean return times form a strictly positive stationary
probability vector, and every stationary vector is a multiple of it. -/
theorem exercise_8_24 [Nonempty s] {P : Matrix s s ℝ}
    (hP : IsStochasticMatrix P) (hI : IsIrreducibleChain P) :
    let π : s → ℝ := fun j => ((meanFirstPassageTime P j j).toReal)⁻¹
    IsStationaryDistribution P π ∧ (∀ j, 0 < π j) ∧
      ∀ x : s → ℝ, Pᵀ *ᵥ x = x → x = (∑ i, x i) • π := by
  dsimp only
  obtain ⟨π, hπ, hpos, _, huniq⟩ := stationaryDistribution_eq_groupInverse hP hI
  have he : (fun j => ((meanFirstPassageTime P j j).toReal)⁻¹) = π := by
    funext j
    rw [meanReturnTime_eq_inverse_stationary hP hI hπ hpos,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (hpos j).le), inv_inv]
  refine ⟨he.symm ▸ hπ, fun j => ?_, fun x hx => ?_⟩
  · simpa only [congrFun he j] using hpos j
  · simpa only [he] using huniq x hx

/-- The transition matrix in **Exercises 25–26**. -/
noncomputable def twoStateSwap : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

private theorem twoStateSwap_stochastic : IsStochasticMatrix twoStateSwap := by
  rw [isStochasticMatrix_iff_row_sums]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [twoStateSwap]
  · intro i
    fin_cases i <;> norm_num [twoStateSwap, Fin.sum_univ_two]

private theorem twoStateSwap_transpose : twoStateSwapᵀ = twoStateSwap := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem twoStateSwap_sq : twoStateSwap ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoStateSwap, pow_two, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two]

private theorem twoStateSwap_mulVec (x : Fin 2 → ℝ) : twoStateSwap *ᵥ x = ![x 1, x 0] := by
  funext i
  fin_cases i <;> simp [twoStateSwap, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem twoStateSwap_pow_even (n : ℕ) : twoStateSwap ^ (2 * n) = 1 := by
  rw [pow_mul, twoStateSwap_sq, one_pow]

private theorem twoStateSwap_pow_odd (n : ℕ) : twoStateSwap ^ (2 * n + 1) = twoStateSwap := by
  rw [pow_succ, twoStateSwap_pow_even, Matrix.one_mul]

/-- **Exercise 25** of [benIsrael2003generalized], Chapter 8. The coordinate
unit vector alternates between the two states. -/
theorem exercise_8_25_unit (n : ℕ) :
    stateDistribution twoStateSwap ![1, 0] (2 * n) = ![1, 0] ∧
    stateDistribution twoStateSwap ![1, 0] (2 * n + 1) = ![0, 1] := by
  constructor
  · simp [stateDistribution, twoStateSwap_transpose, twoStateSwap_pow_even]
  · simp [stateDistribution, twoStateSwap_transpose, twoStateSwap_pow_odd, twoStateSwap_mulVec]

/-- **Exercise 25** of [benIsrael2003generalized], Chapter 8. The probability
vector `[1/2, 1/2]` is stationary. Starting from any other probability vector
precludes an ordinary power limit of the evolving distribution. -/
theorem exercise_8_25 :
    IsStationaryDistribution twoStateSwap (fun _ => 1 / 2) ∧
    ∀ x : Fin 2 → ℝ, (∑ i, x i) = 1 → x ≠ (fun _ => 1 / 2) →
      ¬∃ y, Tendsto (stateDistribution twoStateSwap x) atTop (𝓝 y) := by
  constructor
  · refine ⟨fun _ => by norm_num, by norm_num [Fin.sum_univ_two], ?_⟩
    rw [twoStateSwap_transpose, twoStateSwap_mulVec]
    funext i
    fin_cases i <;> rfl
  · rintro x hsum hne ⟨y, hy⟩
    have he : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
      tendsto_atTop_mono (fun n => show n ≤ 2 * n by omega) tendsto_id
    have ho : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
      tendsto_atTop_mono (fun n => show n ≤ 2 * n + 1 by omega) tendsto_id
    have hy₀ : Tendsto (fun _ : ℕ => x) atTop (𝓝 y) := by
      simpa [Function.comp_def, stateDistribution, twoStateSwap_transpose, twoStateSwap_pow_even]
        using hy.comp he
    have hy₁ : Tendsto (fun _ : ℕ => twoStateSwap *ᵥ x) atTop (𝓝 y) := by
      simpa only [Function.comp_def, stateDistribution, twoStateSwap_transpose,
        twoStateSwap_pow_odd] using hy.comp ho
    have heq : x = twoStateSwap *ᵥ x :=
      (tendsto_nhds_unique tendsto_const_nhds hy₀).trans
        (tendsto_nhds_unique hy₁ tendsto_const_nhds)
    have hcoord : x 0 = x 1 := by simpa [twoStateSwap_mulVec] using congrFun heq (0 : Fin 2)
    rw [Fin.sum_univ_two] at hsum
    have hx₀ : x 0 = 1 / 2 := by linarith
    have hx₁ : x 1 = 1 / 2 := by linarith
    apply hne
    funext i
    fin_cases i
    · exact hx₀
    · exact hx₁

/-- **Exercise 26** of [benIsrael2003generalized], Chapter 8. The Cesàro
limit of the swap-transition powers is the constant matrix with entry `1/2`. -/
theorem exercise_8_26 :
    Tendsto (transitionCesaro twoStateSwap) atTop (𝓝 (of fun _ _ => 1 / 2)) := by
  have hI : IsIrreducibleChain twoStateSwap := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact ⟨2, by decide, by simp [transitionProbability, twoStateSwap_sq]⟩
    · refine ⟨1, by decide, ?_⟩
      fin_cases i <;> fin_cases j <;> simp_all [transitionProbability, twoStateSwap]
  obtain ⟨π, _, _, hrows, huniq⟩ :=
    stationaryDistribution_eq_groupInverse twoStateSwap_stochastic hI
  have hπ : (fun _ : Fin 2 => (1 / 2 : ℝ)) = π := by
    simpa only [exercise_8_25.1.2.1, one_smul] using huniq _ exercise_8_25.1.2.2
  have hE : stationaryProjection twoStateSwap twoStateSwap_stochastic = of fun _ _ => 1 / 2 := by
    ext i j
    exact (hrows i j).trans (congrFun hπ j).symm
  rw [← hE]
  exact theorem_10_cesaro twoStateSwap_stochastic

end Exercises

section PathProbabilities

variable {s Ω : Type*} [Fintype s] [DecidableEq s] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Matrix s s ℝ}
variable {X : ℕ → Ω → s}

omit [IsProbabilityMeasure μ] in
private theorem measure_split_by_finite_map {ι : Type*} [Fintype ι]
    {Y : Ω → ι} (hY : ∀ i, MeasurableSet {ω | Y ω = i})
    {E : Set Ω} (hE : MeasurableSet E) :
    μ E = ∑ i, μ (E ∩ {ω | Y ω = i}) := by
  classical
  have hUnion : E = ⋃ i, E ∩ {ω | Y ω = i} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨Y ω, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  have hdisj : Pairwise (fun i j : ι =>
      Disjoint (E ∩ {ω | Y ω = i}) (E ∩ {ω | Y ω = j})) := by
    intro i j hij
    refine Set.disjoint_left.mpr ?_
    rintro ω ⟨_, ei⟩ ⟨_, ej⟩
    exact hij (ei.symm.trans ej)
  calc
    μ E = μ (⋃ i, E ∩ {ω | Y ω = i}) := congrArg μ hUnion
    _ = ∑' i, μ (E ∩ {ω | Y ω = i}) := measure_iUnion hdisj (fun i => hE.inter (hY i))
    _ = ∑ i, μ (E ∩ {ω | Y ω = i}) := tsum_fintype _

private theorem finiteMarkovChain_next_given_past (h : IsFiniteMarkovChain μ P X)
    (t : ℕ) (i j : s) {E : Set Ω} (hE : MeasurableSet E)
    (hpast : ∀ ω ω' : Ω, (∀ k ≤ t, X k ω = X k ω') → (ω ∈ E ↔ ω' ∈ E))
    (hi : ∀ ω ∈ E, X t ω = i) :
    μ (E ∩ {ω | X (t + 1) ω = j}) = ENNReal.ofReal (P i j) * μ E := by
  classical
  let Y (ω : Ω) (k : Fin (t + 1)) := X k.val ω
  have hY (p : Fin (t + 1) → s) : MeasurableSet {ω | Y ω = p} := by
    have heq : {ω | Y ω = p} = ⋂ k : Fin (t + 1), {ω | X k.val ω = p k} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Y]
      exact funext_iff
    rw [heq]
    exact MeasurableSet.iInter (fun k => h.measurable_state k.val (p k))
  rw [measure_split_by_finite_map hY (hE.inter (h.measurable_state (t + 1) j))]
  conv_rhs => rw [measure_split_by_finite_map hY hE, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hex : (E ∩ {ω | Y ω = p}).Nonempty
  · obtain ⟨ω, hω, hωp⟩ := hex
    have hfull : E ∩ {ω | Y ω = p} = {ω | Y ω = p} := by
      ext ω'
      exact ⟨fun hmem => hmem.2, fun hω'p =>
        ⟨(hpast ω ω' (fun k hk => congrFun (hωp.trans hω'p.symm)
          ⟨k, Nat.lt_succ_of_le hk⟩)).mp hω, hω'p⟩⟩
    have hlast : p (Fin.last t) = i := (congrFun hωp (Fin.last t)).symm.trans (hi ω hω)
    rw [Set.inter_right_comm, hfull, ← hlast]
    simpa only [Set.ofPred_and, Set.mem_ofPred_eq, Y, funext_iff] using h.transition t p j
  · have hempty := Set.not_nonempty_iff_eq_empty.mp hex
    rw [Set.inter_right_comm, hempty, Set.empty_inter, measure_empty, mul_zero]

private theorem finiteMarkovChain_next_measure (h : IsFiniteMarkovChain μ P X)
    (t : ℕ) (j : s) {E : Set Ω} (hE : MeasurableSet E)
    (hpast : ∀ ω ω' : Ω, (∀ k ≤ t, X k ω = X k ω') → (ω ∈ E ↔ ω' ∈ E)) :
    μ (E ∩ {ω | X (t + 1) ω = j}) =
      ∑ i, ENNReal.ofReal (P i j) * μ (E ∩ {ω | X t ω = i}) := by
  rw [measure_split_by_finite_map (h.measurable_state t)
    (hE.inter (h.measurable_state (t + 1) j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Set.inter_right_comm]
  refine finiteMarkovChain_next_given_past h t i j (hE.inter (h.measurable_state t i)) ?_
    (fun _ hw => hw.2)
  intro ω ω' hw
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hpast ω ω' hw, hw t le_rfl]

private theorem finiteMarkovChain_conditional_div {E F : Set Ω} {p : ℝ≥0∞}
    (hE : μ E ≠ 0) (hjoint : μ (E ∩ F) = p * μ E) :
    μ (E ∩ F) / μ E = p := by
  rw [hjoint]
  exact ENNReal.mul_div_cancel_right hE (measure_ne_top μ E)

omit [DecidableEq s] in
private theorem sum_transition_joint (A B : Matrix s s ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    (i j : s) (p : ℝ≥0∞) :
    ∑ k, ENNReal.ofReal (B k j) * (ENNReal.ofReal (A i k) * p) =
      ENNReal.ofReal ((A * B) i j) * p := by
  classical
  rw [Matrix.mul_apply, ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (hA i k) (hB k j)),
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [ENNReal.ofReal_mul (hA i k), ← mul_assoc, mul_comm (ENNReal.ofReal (B k j))]

private theorem finiteMarkovChain_nStep_joint
    (h : IsFiniteMarkovChain μ P X) (t n : ℕ) (i j : s) :
    μ ({ω | X t ω = i} ∩ {ω | X (t + n) ω = j}) =
      ENNReal.ofReal (transitionProbability P n i j) * μ {ω | X t ω = i} := by
  induction n generalizing j with
  | zero =>
    rw [transitionProbability_zero]
    by_cases hij : i = j
    · subst j
      simp
    · have hd : Disjoint {ω | X t ω = i} {ω | X t ω = j} := by
        refine Set.disjoint_left.mpr ?_
        exact fun _ hi hj => hij (hi.symm.trans hj)
      simp [hij, hd.inter_eq]
  | succ n ih =>
    rw [Nat.add_succ, finiteMarkovChain_next_measure h (t + n) j (h.measurable_state t i)]
    · simp_rw [ih]
      simpa only [transitionProbability, pow_succ] using
        sum_transition_joint (P ^ n) P (stochastic_pow h.stochastic n).1 h.stochastic.1 i j
          (μ {ω | X t ω = i})
    · intro ω ω' hw
      simp only [Set.mem_ofPred_eq, hw t (Nat.le_add_right t n)]

/-- **Equation (88)** of [benIsrael2003generalized], Chapter 8. The conditional
probability of being at state j after n steps given state i at time t is
the corresponding entry of the nth matrix power. -/
theorem finiteMarkovChain_nStep_conditional
    (h : IsFiniteMarkovChain μ P X) (t n : ℕ) (i j : s)
    (hi : μ {ω | X t ω = i} ≠ 0) :
    μ ({ω | X t ω = i} ∩ {ω | X (t + n) ω = j}) / μ {ω | X t ω = i} =
      ENNReal.ofReal (transitionProbability P n i j) :=
  finiteMarkovChain_conditional_div hi (finiteMarkovChain_nStep_joint h t n i j)

/-- The event of being at state i at time t and avoiding state j during the
next n transitions. The initial time is excluded from the avoidance test. -/
def passageSurvivalEvent (X : ℕ → Ω → s) (t : ℕ) (i j : s) (n : ℕ) : Set Ω :=
  {ω | X t ω = i ∧ ∀ k < n, X (t + k + 1) ω ≠ j}

private theorem passageSurvivalEvent_measurable (h : IsFiniteMarkovChain μ P X)
    (t n : ℕ) (i j : s) : MeasurableSet (passageSurvivalEvent X t i j n) := by
  have he : passageSurvivalEvent X t i j n =
      {ω | X t ω = i} ∩ ⋂ k : Fin n, ({ω | X (t + k.val + 1) ω = j})ᶜ := by
    ext ω
    simp only [passageSurvivalEvent, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_compl_iff]
    exact and_congr_right fun _ =>
      ⟨fun hv k => hv k.val k.isLt, fun hv k hk => hv ⟨k, hk⟩⟩
  rw [he]
  exact (h.measurable_state t i).inter
    (MeasurableSet.iInter fun k => (h.measurable_state (t + k.val + 1) j).compl)

omit [Fintype s] [DecidableEq s] [MeasurableSpace Ω] in
private theorem passageSurvivalEvent_succ (X : ℕ → Ω → s) (t n : ℕ) (i j : s) :
    passageSurvivalEvent X t i j (n + 1) =
      passageSurvivalEvent X t i j n ∩ {ω | X (t + n + 1) ω ≠ j} := by
  ext ω
  simp only [passageSurvivalEvent, Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hi, hv⟩
    exact ⟨⟨hi, fun k hk => hv k (by omega)⟩, hv n (by omega)⟩
  · rintro ⟨⟨hi, hv⟩, hn⟩
    refine ⟨hi, fun k hk => ?_⟩
    obtain hk | rfl := (Nat.lt_succ_iff_lt_or_eq).mp hk
    · exact hv k hk
    · exact hn

omit [Fintype s] [DecidableEq s] [MeasurableSpace Ω] in
private theorem passageSurvivalEvent_determined (t n : ℕ) (i j : s)
    (ω ω' : Ω) (hω : ∀ k ≤ t + n, X k ω = X k ω') :
    ω ∈ passageSurvivalEvent X t i j n ↔ ω' ∈ passageSurvivalEvent X t i j n := by
  simp only [passageSurvivalEvent, Set.mem_ofPred_eq, hω t (Nat.le_add_right t n)]
  refine and_congr_right fun _ => ?_
  exact forall_congr' fun k => forall_congr' fun hk => by rw [hω (t + k + 1) (by omega)]

private theorem passageSurvivalEvent_joint (h : IsFiniteMarkovChain μ P X)
    (t n : ℕ) (i j b : s) :
    μ (passageSurvivalEvent X t i j n ∩ {ω | X (t + n) ω = b}) =
      ENNReal.ofReal (((killedTransition P j) ^ n) i b) * μ {ω | X t ω = i} := by
  have hK := killedTransition_nonneg h.stochastic j
  induction n generalizing b with
  | zero =>
    simpa [passageSurvivalEvent, transitionProbability] using finiteMarkovChain_nStep_joint h t 0 i b
  | succ n ih =>
    rw [passageSurvivalEvent_succ, pow_succ]
    change μ ((passageSurvivalEvent X t i j n ∩ {ω | X (t + n + 1) ω ≠ j}) ∩
      {ω | X (t + n + 1) ω = b}) =
        ENNReal.ofReal (((killedTransition P j) ^ n * killedTransition P j) i b) * _
    by_cases hb : b = j
    · subst b
      have hempty : (passageSurvivalEvent X t i j n ∩ {ω | X (t + n + 1) ω ≠ j}) ∩
          {ω | X (t + n + 1) ω = j} = ∅ := by ext ω; simp
      simp only [hempty, measure_empty, Matrix.mul_apply, killedTransition, Matrix.of_apply,
        ite_true, mul_zero, Finset.sum_const_zero, ENNReal.ofReal_zero, zero_mul]
    · have hrepl : (passageSurvivalEvent X t i j n ∩ {ω | X (t + n + 1) ω ≠ j}) ∩
          {ω | X (t + n + 1) ω = b} =
          passageSurvivalEvent X t i j n ∩ {ω | X (t + n + 1) ω = b} := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact ⟨fun hw => ⟨hw.1.1, hw.2⟩, fun hw => ⟨⟨hw.1, hw.2 ▸ hb⟩, hw.2⟩⟩
      rw [hrepl, finiteMarkovChain_next_measure h (t + n) b
        (passageSurvivalEvent_measurable h t n i j) (passageSurvivalEvent_determined t n i j)]
      simp_rw [ih]
      simpa only [Matrix.mul_apply, killedTransition, Matrix.of_apply, ite_eq_right hb] using
        sum_transition_joint ((killedTransition P j) ^ n) P (pow_apply_nonneg hK n)
          h.stochastic.1 i b (μ {ω | X t ω = i})

/-- **First passage** in [benIsrael2003generalized], Chapter 8, Section 7.
The first arrival at state j strictly after time t occurs on transition n+1
exactly when the path avoids j for the preceding n transitions and then
enters j. Its conditional probability is the killed-transition formula. -/
theorem finiteMarkovChain_firstPassage_conditional
    (h : IsFiniteMarkovChain μ P X) (t n : ℕ) (i j : s)
    (hi : μ {ω | X t ω = i} ≠ 0) :
    μ {ω | X t ω = i ∧ (∀ k < n, X (t + k + 1) ω ≠ j) ∧ X (t + n + 1) ω = j} /
        μ {ω | X t ω = i} = ENNReal.ofReal (firstPassageProbability P i j (n + 1)) := by
  have hK := killedTransition_nonneg h.stochastic j
  have he :
      {ω | X t ω = i ∧ (∀ k < n, X (t + k + 1) ω ≠ j) ∧ X (t + n + 1) ω = j} =
        {ω | X t ω = i} ∩ (passageSurvivalEvent X t i j n ∩ {ω | X (t + n + 1) ω = j}) := by
    ext ω
    simp only [passageSurvivalEvent, Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]
    exact ⟨fun ⟨hi, hv, hj⟩ => ⟨hi, hi, hv, hj⟩, fun ⟨hi, _, hv, hj⟩ => ⟨hi, hv, hj⟩⟩
  rw [he]
  apply finiteMarkovChain_conditional_div hi
  rw [← Set.inter_assoc, Set.inter_eq_right.mpr
    (show passageSurvivalEvent X t i j n ⊆ {ω | X t ω = i} from fun _ hw => hw.1)]
  rw [finiteMarkovChain_next_measure h (t + n) j (passageSurvivalEvent_measurable h t n i j)
    (passageSurvivalEvent_determined t n i j)]
  simp_rw [passageSurvivalEvent_joint h]
  exact sum_transition_joint ((killedTransition P j) ^ n) P (pow_apply_nonneg hK n)
    h.stochastic.1 i j (μ {ω | X t ω = i})

end PathProbabilities

section ClosedClasses

variable {s : Type*} [Fintype s] [DecidableEq s]
variable {P : Matrix s s ℝ} {S T : Set s}

/-- A closed set has zero transition probability to its complement at every time. -/
theorem IsClosedStateSet.transitionProbability_eq_zero (hS : IsClosedStateSet P S)
    {i j : s} (hi : i ∈ S) (hj : j ∉ S) (n : ℕ) : transitionProbability P n i j = 0 := by
  induction n generalizing j with
  | zero =>
    have hne : i ≠ j := fun h => hj (h ▸ hi)
    rw [transitionProbability_zero, ite_eq_right hne]
  | succ n ih =>
    rw [transitionProbability, pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k ∈ S
    · rw [hS k hk j hj, mul_zero]
    · rw [← transitionProbability, ih hk, zero_mul]

/-- A state reachable from a member of a closed set belongs to that set. -/
theorem IsClosedStateSet.mem_of_leadsTo (hS : IsClosedStateSet P S)
    {i j : s} (hi : i ∈ S) (hij : LeadsTo P i j) : j ∈ S := by
  by_contra hj
  obtain ⟨n, _, hn⟩ := hij
  rw [hS.transitionProbability_eq_zero hi hj n] at hn
  exact (lt_irrefl 0) hn

/-- The states reachable in zero or more transitions from the given state. -/
def stateReachableSet (P : Matrix s s ℝ) (i : s) : Set s :=
  {j | i = j ∨ LeadsTo P i j}

private theorem mem_stateReachableSet_self (P : Matrix s s ℝ) (i : s) :
    i ∈ stateReachableSet P i :=
  Or.inl rfl

private theorem stateReachableSet_subset_of_mem (hP : IsStochasticMatrix P)
    {i j : s} (hij : j ∈ stateReachableSet P i) :
    stateReachableSet P j ⊆ stateReachableSet P i := by
  rintro k (rfl | hjk)
  · exact hij
  · rcases hij with rfl | hij
    · exact Or.inr hjk
    · exact Or.inr (leadsTo_trans hP hij hjk)

private theorem leadsTo_of_pos_entry {i j : s} (hij : 0 < P i j) : LeadsTo P i j :=
  ⟨1, Nat.one_pos, by simpa [transitionProbability] using hij⟩

/-- The set of all states reachable from a state is closed. -/
theorem isClosedStateSet_stateReachableSet (hP : IsStochasticMatrix P) (i : s) :
    IsClosedStateSet P (stateReachableSet P i) := by
  intro j hj k hk
  refine le_antisymm (le_of_not_gt fun hpos => hk ?_) (hP.1 j k)
  exact stateReachableSet_subset_of_mem hP hj (Or.inr (leadsTo_of_pos_entry hpos))

private theorem exists_positive_transition (hP : IsStochasticMatrix P) (i : s) :
    ∃ j, 0 < P i j := by
  by_contra h
  push Not at h
  have hz : ∑ j, P i j = 0 :=
    Finset.sum_eq_zero fun j _ => le_antisymm (h j) (hP.1 i j)
  rw [sum_row_of_mem_rowStochastic hP] at hz
  exact one_ne_zero hz

/-- A closed communicating class is a minimal nonempty closed set.
The communicating condition uses positive times, including for self-returns. -/
theorem isClosedCommunicatingClass_iff_minimal_closed (hP : IsStochasticMatrix P) :
    IsClosedCommunicatingClass P S ↔
      S.Nonempty ∧ IsClosedStateSet P S ∧
        ∀ T ⊆ S, T.Nonempty → IsClosedStateSet P T → T = S := by
  constructor
  · rintro ⟨hS, hclosed, hcom⟩
    refine ⟨hS, hclosed, fun T hTS ⟨i, hi⟩ hT => Set.Subset.antisymm hTS ?_⟩
    exact fun j hj => hT.mem_of_leadsTo hi (hcom i (hTS hi) j hj).1
  · rintro ⟨hS, hclosed, hmin⟩
    refine ⟨hS, hclosed, ?_⟩
    have hall (i : s) (hi : i ∈ S) : stateReachableSet P i = S :=
      hmin _ (by
        rintro j (rfl | hij)
        · exact hi
        · exact hclosed.mem_of_leadsTo hi hij)
        ⟨i, mem_stateReachableSet_self P i⟩ (isClosedStateSet_stateReachableSet hP i)
    have hreach (i j : s) (hi : i ∈ S) (hj : j ∈ S) : LeadsTo P i j := by
      have hr : j ∈ stateReachableSet P i := hall i hi ▸ hj
      rcases hr with rfl | hr
      · obtain ⟨k, hk⟩ := exists_positive_transition hP i
        have hik := leadsTo_of_pos_entry hk
        have hki : i ∈ stateReachableSet P k :=
          hall k (hclosed.mem_of_leadsTo hi hik) ▸ hi
        rcases hki with hki | hki
        · rwa [hki] at hik
        · exact leadsTo_trans hP hik hki
      · exact hr
    exact fun i hi j hj => ⟨hreach i j hi hj, hreach j i hj hi⟩

/-- Every state of a finite stochastic chain reaches some closed communicating
class, in positive time. -/
theorem exists_closedCommunicatingClass_of_state (hP : IsStochasticMatrix P) (i : s) :
    ∃ (S : Set s) (j : s), IsClosedCommunicatingClass P S ∧ j ∈ S ∧ LeadsTo P i j := by
  let R := stateReachableSet P
  obtain ⟨j, hj, hmin⟩ := Set.exists_min_image (R i) (fun j => (R j).ncard)
    (Set.toFinite _) ⟨i, mem_stateReachableSet_self P i⟩
  have hsubset : R j ⊆ R i := stateReachableSet_subset_of_mem hP hj
  have hclass : IsClosedCommunicatingClass P (R j) := by
    rw [isClosedCommunicatingClass_iff_minimal_closed hP]
    refine ⟨⟨j, mem_stateReachableSet_self P j⟩, isClosedStateSet_stateReachableSet hP j, ?_⟩
    rintro T hT ⟨k, hk⟩ hclosed
    have hRT : R k ⊆ T := by
      rintro l (rfl | hkl)
      · exact hk
      · exact hclosed.mem_of_leadsTo hk hkl
    exact Set.eq_of_subset_of_ncard_le hT
      ((hmin k (hsubset (hT hk))).trans (Set.ncard_le_ncard hRT))
  have hjj := mem_stateReachableSet_self P j
  refine ⟨R j, j, hclass, hjj, ?_⟩
  rcases hj with h | hj
  · exact (hclass.2.2 j hjj j hjj).1 |> (h.symm ▸ ·)
  · exact hj

/-- Distinct closed communicating classes are disjoint. -/
theorem closedCommunicatingClass_eq_of_mem
    (hS : IsClosedCommunicatingClass P S) (hT : IsClosedCommunicatingClass P T)
    {i : s} (hiS : i ∈ S) (hiT : i ∈ T) : S = T :=
  Set.Subset.antisymm
    (fun j hj => hT.2.1.mem_of_leadsTo hiT (hS.2.2 i hiS j hj).1)
    (fun j hj => hS.2.1.mem_of_leadsTo hiS (hT.2.2 i hiT j hj).1)

/-- **Section 8.7** of [benIsrael2003generalized], Chapter 8. A finite
stochastic chain is absorbing exactly when each closed communicating class
has a single state. -/
theorem isAbsorbingChain_iff_closed_classes_singleton (hP : IsStochasticMatrix P) :
    IsAbsorbingChain P ↔ ∀ S : Set s, IsClosedCommunicatingClass P S → ∃ i, S = {i} := by
  constructor
  · intro habs S hS
    obtain ⟨i, hi⟩ := hS.1
    obtain ⟨j, hj, hij⟩ := habs i
    have hjS := hS.2.1.mem_of_leadsTo hi hij
    have hsingle := (isAbsorbingState_iff_singleton_closed hP j).mp hj
    exact ⟨j, closedCommunicatingClass_eq_of_mem hS hsingle hjS rfl⟩
  · intro h i
    obtain ⟨S, j, hS, hj, hij⟩ := exists_closedCommunicatingClass_of_state hP i
    obtain ⟨k, rfl⟩ := h S hS
    have heq : j = k := hj
    subst k
    exact ⟨j, (isAbsorbingState_iff_singleton_closed hP j).mpr hS, hij⟩

end ClosedClasses

section RenewalSummability

variable {s : Type*} [Fintype s] [DecidableEq s]
variable {P : Matrix s s ℝ}

private theorem summable_firstPassageProbability (hP : IsStochasticMatrix P) (i j : s) :
    Summable (fun n : ℕ => firstPassageProbability P i j (n + 1)) := by
  apply summable_of_sum_range_le (c := 1) (fun n => firstPassageProbability_nonneg hP i j (n + 1))
  intro n
  rw [sum_firstPassageProbability hP]
  exact sub_le_self _ (survivalProbability_nonneg hP i j n)

/-- The passage probabilities have total mass at most one. -/
theorem eventualPassageProbability_le_one (hP : IsStochasticMatrix P) (i j : s) :
    eventualPassageProbability P i j ≤ 1 := by
  rw [eventualPassageProbability, ← ENNReal.ofReal_tsum_of_nonneg
    (fun n => firstPassageProbability_nonneg hP i j (n + 1)) (summable_firstPassageProbability hP i j),
    ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  apply Real.tsum_le_of_sum_range_le (fun n => firstPassageProbability_nonneg hP i j (n + 1))
  intro n
  rw [sum_firstPassageProbability hP]
  exact sub_le_self _ (survivalProbability_nonneg hP i j n)

private theorem sum_range_renewal_triangle (f g : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (n + 1), f k * g (n - k)) =
      ∑ k ∈ Finset.range N, f k * ∑ l ∈ Finset.range (N - k), g l := by
  induction N with
  | zero => simp
  | succ N ih =>
    have he :
        (∑ k ∈ Finset.range N, f k * ∑ l ∈ Finset.range (N + 1 - k), g l) =
        ∑ k ∈ Finset.range N,
          (f k * (∑ l ∈ Finset.range (N - k), g l) + f k * g (N - k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [show N + 1 - k = (N - k) + 1 by have := Finset.mem_range.mp hk; omega,
        Finset.sum_range_succ, mul_add]
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, Finset.sum_range_succ, he,
      Finset.sum_add_distrib]
    simp [add_assoc]

/-- **Exercise 22(a)** of [benIsrael2003generalized], Chapter 8. In a transient
state the positive-time return probabilities are summable, and conversely. -/
theorem exercise_8_22a (hP : IsStochasticMatrix P) (i : s) :
    IsTransientState P i ↔ Summable (fun n : ℕ => transitionProbability P (n + 1) i i) := by
  let f n := firstPassageProbability P i i (n + 1)
  let u n := transitionProbability P n i i
  let F := ∑' n, f n
  have hf : Summable f := summable_firstPassageProbability hP i i
  have hf0 (n : ℕ) : 0 ≤ f n := firstPassageProbability_nonneg hP i i (n + 1)
  have hu0 (n : ℕ) : 0 ≤ u n := (stochastic_pow hP n).1 i i
  have huzero : u 0 = 1 := by simp [u, transitionProbability_zero]
  have hF0 : 0 ≤ F := tsum_nonneg hf0
  have hF : eventualPassageProbability P i i = ENNReal.ofReal F :=
    (ENNReal.ofReal_tsum_of_nonneg hf0 hf).symm
  have hFle : F ≤ 1 := by
    have he := eventualPassageProbability_le_one hP i i
    rwa [hF, ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff zero_le_one] at he
  have hrenewal (n : ℕ) :
      u (n + 1) = ∑ k ∈ Finset.range (n + 1), f k * u (n - k) :=
    exercise_8_20 P i i n
  change eventualPassageProbability P i i ≠ 1 ↔ Summable (fun n : ℕ => u (n + 1))
  have hFiff : eventualPassageProbability P i i = 1 ↔ F = 1 := by
    rw [hF, ← ENNReal.ofReal_one, ENNReal.ofReal_eq_ofReal_iff hF0 zero_le_one]
  rw [ne_eq, hFiff, summable_nat_add_iff 1]
  constructor
  · intro hne
    have hden : 0 < 1 - F := sub_pos.mpr (lt_of_le_of_ne hFle hne)
    apply summable_of_sum_range_le (c := 1 / (1 - F)) hu0
    intro N
    cases N with
    | zero => simp [hden.le]
    | succ N =>
      let U := ∑ n ∈ Finset.range (N + 1), u n
      have hU0 : 0 ≤ U := Finset.sum_nonneg (fun n _ => hu0 n)
      have hU : U = 1 + ∑ k ∈ Finset.range N, f k * ∑ l ∈ Finset.range (N - k), u l := by
        rw [show U = u 0 + ∑ n ∈ Finset.range N, u (n + 1) by
          dsimp [U]; rw [Finset.sum_range_succ']; exact add_comm _ _]
        simp_rw [huzero, hrenewal, sum_range_renewal_triangle]
      have hpartial (k : ℕ) : ∑ l ∈ Finset.range (N - k), u l ≤ U :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun n _ _ => hu0 n)
      have hupper : (∑ k ∈ Finset.range N, f k * ∑ l ∈ Finset.range (N - k), u l) ≤ F * U := by
        calc
          _ ≤ ∑ k ∈ Finset.range N, f k * U :=
            Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hpartial k) (hf0 k))
          _ = (∑ k ∈ Finset.range N, f k) * U := (Finset.sum_mul _ _ _).symm
          _ ≤ F * U := mul_le_mul_of_nonneg_right (hf.sum_le_tsum _ (fun n _ => hf0 n)) hU0
      change U ≤ 1 / (1 - F)
      apply (le_div_iff₀ hden).2
      linarith [show U * (1 - F) = U - F * U by ring]
  · intro hu he
    have hprod :
        F * (∑' n, u n) = ∑' n, u (n + 1) := by
      have hf' : Summable (fun n => ‖f n‖) := by simpa only [Real.norm_eq_abs, abs_of_nonneg, hf0] using hf
      have hu' : Summable (fun n => ‖u n‖) := by simpa only [Real.norm_eq_abs, abs_of_nonneg, hu0] using hu
      simpa only [← hrenewal] using tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf' hu'
    have hhead := hu.tsum_eq_zero_add
    rw [he, one_mul] at hprod
    rw [huzero] at hhead
    linarith

private theorem transitionProbability_mul_le_of_join (hP : IsStochasticMatrix P)
    (a b : ℕ) (i j k : s) :
    transitionProbability P a i j * transitionProbability P b j k ≤
      transitionProbability P (a + b) i k := by
  rw [chapmanKolmogorov]
  exact Finset.single_le_sum
    (fun t _ => mul_nonneg ((stochastic_pow hP a).1 i t) ((stochastic_pow hP b).1 t k))
    (Finset.mem_univ j)

/-- **Exercise 23** of [benIsrael2003generalized], Chapter 8. Communicating
states are recurrent together and transient together. The period equality
is recorded in the same statement. -/
theorem exercise_8_23_recurrence (hP : IsStochasticMatrix P) {i j : s}
    (hij : Communicates P i j) :
    (IsRecurrentState P i ↔ IsRecurrentState P j) ∧
      (IsTransientState P i ↔ IsTransientState P j) ∧ statePeriod P i = statePeriod P j := by
  have htransfer (a b : s) (hab : Communicates P a b)
      (ha : IsTransientState P a) : IsTransientState P b := by
    obtain ⟨⟨r, _, hr⟩, ⟨s, _, hs⟩⟩ := hab
    let c := transitionProbability P r a b * transitionProbability P s b a
    have hc : 0 < c := mul_pos hr hs
    have hbound (n : ℕ) : c * transitionProbability P (n + 1) b b ≤
        transitionProbability P ((n + 1) + (r + s)) a a := by
      calc
        _ = (transitionProbability P r a b * transitionProbability P (n + 1) b b) *
              transitionProbability P s b a := by dsimp [c]; ring
        _ ≤ transitionProbability P (r + (n + 1)) a b * transitionProbability P s b a :=
          mul_le_mul_of_nonneg_right (transitionProbability_mul_le_of_join hP r (n + 1) a b b) hs.le
        _ ≤ transitionProbability P ((n + 1) + (r + s)) a a := by
          rw [show (n + 1) + (r + s) = (r + (n + 1)) + s by omega]
          exact transitionProbability_mul_le_of_join hP (r + (n + 1)) s a b a
    have hsum : Summable (fun n : ℕ => transitionProbability P ((n + 1) + (r + s)) a a) :=
      (summable_nat_add_iff (r + s)).2 ((exercise_8_22a hP a).mp ha) |>.congr
        (fun n => congrArg (fun k => transitionProbability P k a a)
          (show n + (r + s) + 1 = n + 1 + (r + s) by omega))
    have hscaled : Summable (fun n : ℕ => c * transitionProbability P (n + 1) b b) :=
      hsum.of_nonneg_of_le (fun n => mul_nonneg hc.le ((stochastic_pow hP (n + 1)).1 b b)) hbound
    apply (exercise_8_22a hP b).mpr
    simpa [← mul_assoc, inv_mul_cancel₀ hc.ne'] using hscaled.mul_left c⁻¹
  have htrans : IsTransientState P i ↔ IsTransientState P j :=
    ⟨htransfer i j hij, htransfer j i hij.symm⟩
  exact ⟨by simpa only [IsTransientState, not_iff_not] using htrans, htrans, statePeriod_eq_of_communicates hP hij⟩

end RenewalSummability

section ClosedClassRestriction

variable {s : Type*} [Fintype s] [DecidableEq s]
variable {P : Matrix s s ℝ} {S : Set s}

/-- The matrix obtained by restricting the two state indices to a subset. -/
def restrictTransition (P : Matrix s s ℝ) (S : Set s) : Matrix S S ℝ :=
  P.submatrix Subtype.val Subtype.val

omit [Fintype s] [DecidableEq s] in
/-- Restriction retains the transition coefficient between the two selected states. -/
@[simp]
theorem restrictTransition_apply (P : Matrix s s ℝ) (S : Set s) (i j : S) :
    restrictTransition P S i j = P i.val j.val :=
  rfl

/-- A closed subset inherits the stochastic row sums. -/
theorem IsClosedStateSet.stochastic_restrictTransition [Fintype S]
    (hS : IsClosedStateSet P S) (hP : IsStochasticMatrix P) :
    IsStochasticMatrix (restrictTransition P S) := by
  classical
  rw [isStochasticMatrix_iff_row_sums]
  refine ⟨fun i j => hP.1 i j, fun i => ?_⟩
  simp only [restrictTransition_apply, Finset.sum_set_coe]
  rw [Finset.sum_subset S.toFinset.subset_univ (fun j _ hj =>
    hS i i.property j (fun h => hj (Set.mem_toFinset.mpr h)))]
  exact sum_row_of_mem_rowStochastic hP i

/-- A path starting in a closed set has the same transition probabilities
under restriction to that set. -/
theorem IsClosedStateSet.transitionProbability_restrictTransition [Fintype S]
    (hS : IsClosedStateSet P S) (n : ℕ) (i j : S) :
    transitionProbability (restrictTransition P S) n i j =
      transitionProbability P n i.val j.val := by
  classical
  induction n generalizing j with
  | zero => simp only [transitionProbability_zero, Subtype.ext_iff]
  | succ n ih =>
    rw [chapmanKolmogorov _ n 1, chapmanKolmogorov _ n 1]
    have hterm (k : S) : transitionProbability (restrictTransition P S) n i k *
        transitionProbability (restrictTransition P S) 1 k j =
        transitionProbability P n i.val k.val * transitionProbability P 1 k.val j.val := by
      rw [ih k]
      simp [transitionProbability]
    simp only [hterm]
    rw [Finset.sum_set_coe (f := fun k =>
      transitionProbability P n i.val k * transitionProbability P 1 k j.val) S]
    apply Finset.sum_subset S.toFinset.subset_univ
    intro k _ hk
    rw [hS.transitionProbability_eq_zero i.property (fun h => hk (Set.mem_toFinset.mpr h)) n,
      zero_mul]

/-- The transition matrix on a closed communicating class is irreducible. -/
theorem IsClosedCommunicatingClass.irreducible_restrictTransition [Fintype S]
    (hS : IsClosedCommunicatingClass P S) :
    IsIrreducibleChain (restrictTransition P S) := by
  intro i j
  obtain ⟨n, hn, hp⟩ := (hS.2.2 i i.property j j.property).1
  exact ⟨n, hn, (hS.2.1.transitionProbability_restrictTransition n i j).symm ▸ hp⟩

omit [Fintype s] in
private theorem restrictTransition_killedTransition (P : Matrix s s ℝ) (S : Set s) (j : S) :
    restrictTransition (killedTransition P j.val) S = killedTransition (restrictTransition P S) j := by
  ext a b
  simp [killedTransition, Subtype.ext_iff]

omit [Fintype s] in
private theorem IsClosedStateSet.killedTransition_closed (hS : IsClosedStateSet P S) (j : s) :
    IsClosedStateSet (killedTransition P j) S := by
  intro a ha b hb
  simp [killedTransition, hS a ha b hb]

/-- Restriction to a closed set preserves all first-passage probabilities
between states in the set. -/
theorem IsClosedStateSet.firstPassageProbability_restrictTransition [Fintype S]
    (hS : IsClosedStateSet P S) (i j : S) (n : ℕ) :
    firstPassageProbability (restrictTransition P S) i j n =
      firstPassageProbability P i.val j.val n := by
  classical
  cases n with
  | zero => rfl
  | succ n =>
    rw [firstPassageProbability, firstPassageProbability, ← restrictTransition_killedTransition,
      Matrix.mul_apply, Matrix.mul_apply]
    have hpow (b : S) :
        ((restrictTransition (killedTransition P j.val) S) ^ n) i b =
          (killedTransition P j.val ^ n) i.val b.val :=
      (hS.killedTransition_closed j.val).transitionProbability_restrictTransition n i b
    simp only [hpow, restrictTransition_apply]
    rw [Finset.sum_set_coe (f := fun b => (killedTransition P j.val ^ n) i.val b * P b j.val) S]
    apply Finset.sum_subset S.toFinset.subset_univ
    intro b _ hb
    have hz := (hS.killedTransition_closed j.val).transitionProbability_eq_zero
      i.property (fun h => hb (Set.mem_toFinset.mpr h)) n
    change (killedTransition P j.val ^ n) i.val b = 0 at hz
    rw [hz, zero_mul]

/-- The eventual passage probabilities between states of a closed set are
unchanged by restriction. -/
theorem IsClosedStateSet.eventualPassageProbability_restrictTransition [Fintype S]
    (hS : IsClosedStateSet P S) (i j : S) :
    eventualPassageProbability (restrictTransition P S) i j =
      eventualPassageProbability P i.val j.val := by
  simp only [eventualPassageProbability, hS.firstPassageProbability_restrictTransition]

/-- The mean passage times between states of a closed set are unchanged by
restriction. -/
theorem IsClosedStateSet.meanFirstPassageTime_restrictTransition [Fintype S]
    (hS : IsClosedStateSet P S) (i j : S) :
    meanFirstPassageTime (restrictTransition P S) i j =
      meanFirstPassageTime P i.val j.val := by
  simp only [meanFirstPassageTime, hS.firstPassageProbability_restrictTransition]

/-- A state has the same period in a closed set and in the full chain. -/
theorem IsClosedStateSet.statePeriod_restrictTransition [Fintype S]
    (hS : IsClosedStateSet P S) (i : S) :
    statePeriod (restrictTransition P S) i = statePeriod P i.val := by
  simp only [statePeriod, hS.transitionProbability_restrictTransition]

/-- States in a closed communicating class are recurrent and have finite
mean return times. -/
theorem IsClosedCommunicatingClass.recurrent_and_mean_return_ne_top
    (hP : IsStochasticMatrix P) (hS : IsClosedCommunicatingClass P S) (i : S) :
    IsRecurrentState P i.val ∧ meanFirstPassageTime P i.val i.val ≠ ⊤ := by
  let := Fintype.ofFinite S
  have hQ := hS.2.1.stochastic_restrictTransition hP
  have hirr := hS.irreducible_restrictTransition
  constructor
  · unfold IsRecurrentState
    rw [← hS.2.1.eventualPassageProbability_restrictTransition i i]
    exact isRecurrentChain_of_irreducible hQ hirr i
  · rw [← hS.2.1.meanFirstPassageTime_restrictTransition i i,
      meanFirstPassageTime_eq_killed_inverse hQ i i (fun j => hirr j i)]
    exact ENNReal.ofReal_ne_top

end ClosedClassRestriction

section LocalRecurrence

variable {s : Type*} [Fintype s] [DecidableEq s]
variable {P : Matrix s s ℝ} {S : Set s}

private theorem survivalProbability_eq_one_on_closed_set (hP : IsStochasticMatrix P)
    (hS : IsClosedStateSet P S) {i j : s} (hi : i ∈ S) (hj : j ∉ S) (n : ℕ) :
    survivalProbability P i j n = 1 := by
  have hrow (a : s) (ha : a ∈ S) (b : s) : killedTransition P j a b = P a b := by
    by_cases hb : b = j
    · subst b
      simp [killedTransition, hS a ha j hj]
    · simp [killedTransition, hb]
  have hpow (b : s) : (killedTransition P j ^ n) i b = (P ^ n) i b := by
    induction n generalizing b with
    | zero => simp only [pow_zero]
    | succ n ih =>
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [ih k]
      by_cases hk : k ∈ S
      · rw [hrow k hk]
      · have hz : (P ^ n) i k = 0 := hS.transitionProbability_eq_zero hi hk n
        rw [hz, zero_mul, zero_mul]
  simpa only [survivalProbability, Matrix.mulVec, dotProduct, Pi.one_apply, mul_one, hpow] using
    sum_row_of_mem_rowStochastic (stochastic_pow hP n) i

private theorem killedTransition_first_pos_entry (hP : IsStochasticMatrix P)
    (i j : s) (hj : i ≠ j) (hij : LeadsTo P i j) :
    ∃ n : ℕ, 0 < (killedTransition P i ^ n) i j := by
  classical
  have h : ∃ n : ℕ, 0 < transitionProbability P n i j := by
    obtain ⟨n, _, hn⟩ := hij
    exact ⟨n, hn⟩
  let n := Nat.find h
  have hn : 0 < transitionProbability P n i j := Nat.find_spec h
  have hn0 : n ≠ 0 := by
    intro hzero
    simp [hzero, transitionProbability_zero, hj] at hn
  have hzero {a : ℕ} (ha : a < n) : (P ^ a) i j = 0 :=
    le_antisymm (le_of_not_gt fun hpos => (Nat.find_min' h hpos).not_gt ha)
      ((stochastic_pow hP a).1 i j)
  let K := killedTransition P i
  have he := congrArg (fun A : Matrix s s ℝ => A i j) (pow_eq_killed_add_passages P i n)
  change (P ^ n) i j = (K ^ n +
    ∑ t ∈ Finset.range n, K ^ t * (P - K) * P ^ (n - (t + 1))) i j at he
  rw [Matrix.add_apply, Matrix.sum_apply] at he
  have hs : (∑ t ∈ Finset.range n, (K ^ t * (P - K) * P ^ (n - (t + 1))) i j) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    change (K ^ t * (P - killedTransition P i)) i k * (P ^ (n - (t + 1))) k j = 0
    rw [mul_killed_defect_entry]
    split_ifs with hk
    · subst k
      rw [hzero (by omega), mul_zero]
    · rw [zero_mul]
  rw [hs, add_zero] at he
  exact ⟨n, he ▸ hn⟩

private theorem survivalProbability_add (P : Matrix s s ℝ) (i j : s) (a b : ℕ) :
    survivalProbability P i j (a + b) =
      ∑ k, (killedTransition P j ^ a) i k * survivalProbability P k j b := by
  unfold survivalProbability
  rw [pow_add, ← Matrix.mulVec_mulVec]
  rfl

/-- A state outside a closed set that it can reach is transient. -/
theorem IsClosedStateSet.isTransient_of_reachable (hP : IsStochasticMatrix P)
    (hS : IsClosedStateSet P S) {i j : s} (hi : i ∉ S) (hj : j ∈ S)
    (hij : LeadsTo P i j) : IsTransientState P i := by
  have hne : i ≠ j := fun e => hi (e.symm ▸ hj)
  obtain ⟨a, ha⟩ := killedTransition_first_pos_entry hP i j hne hij
  let c := (killedTransition P i ^ a) i j
  have hbound (b : ℕ) : c ≤ survivalProbability P i i (a + b) := by
    rw [survivalProbability_add]
    have hterm : c = (killedTransition P i ^ a) i j * survivalProbability P j i b := by
      rw [survivalProbability_eq_one_on_closed_set hP hS hj hi, mul_one]
    rw [hterm]
    exact Finset.single_le_sum (fun k _ =>
      mul_nonneg (pow_apply_nonneg (killedTransition_nonneg hP i) a i k)
        (survivalProbability_nonneg hP k i b)) (Finset.mem_univ j)
  have hall (n : ℕ) : c ≤ survivalProbability P i i n := by
    by_cases h : a ≤ n
    · simpa only [Nat.add_sub_of_le h] using hbound (n - a)
    · exact (by simpa only [Nat.add_zero] using hbound 0 : c ≤ survivalProbability P i i a).trans
        (survivalProbability_antitone hP i i (Nat.le_of_not_ge h))
  have hsum : (∑' n, firstPassageProbability P i i (n + 1)) ≤ 1 - c := by
    apply Real.tsum_le_of_sum_range_le (fun n => firstPassageProbability_nonneg hP i i (n + 1))
    intro n
    rw [sum_firstPassageProbability hP]
    exact sub_le_sub_left (hall n) 1
  unfold IsTransientState IsRecurrentState eventualPassageProbability
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => firstPassageProbability_nonneg hP i i (n + 1))
    (summable_firstPassageProbability hP i i)]
  exact ne_of_lt (ENNReal.ofReal_lt_one.mpr (hsum.trans_lt (sub_lt_self 1 ha)))

/-- The recurrent states of a finite chain are exactly those belonging to a
closed communicating class. -/
theorem isRecurrentState_iff_mem_closedCommunicatingClass (hP : IsStochasticMatrix P) (i : s) :
    IsRecurrentState P i ↔ ∃ S : Set s, IsClosedCommunicatingClass P S ∧ i ∈ S := by
  constructor
  · intro hR
    obtain ⟨S, j, hS, hj, hij⟩ := exists_closedCommunicatingClass_of_state hP i
    refine ⟨S, hS, ?_⟩
    by_contra hi
    exact (hS.2.1.isTransient_of_reachable hP hi hj hij) hR
  · rintro ⟨S, hS, hi⟩
    exact (hS.recurrent_and_mean_return_ne_top hP ⟨i, hi⟩).1

/-- **Exercise 21** of [benIsrael2003generalized], Chapter 8. A finite chain
has no null recurrent states. Any nonempty finite chain has a recurrent state. -/
theorem exercise_8_21 (hP : IsStochasticMatrix P) :
    (∀ i, ¬IsNullState P i) ∧ (Nonempty s → ∃ i, IsRecurrentState P i) := by
  constructor
  · rintro i ⟨hR, hμ⟩
    obtain ⟨S, hS, hi⟩ := (isRecurrentState_iff_mem_closedCommunicatingClass hP i).mp hR
    exact (hS.recurrent_and_mean_return_ne_top hP ⟨i, hi⟩).2 hμ
  · rintro ⟨i⟩
    obtain ⟨S, j, hS, hj, _⟩ := exists_closedCommunicatingClass_of_state hP i
    exact ⟨j, (hS.recurrent_and_mean_return_ne_top hP ⟨j, hj⟩).1⟩

/-- **Exercise 22(b)** of [benIsrael2003generalized], Chapter 8. In a finite
chain the implications for a null state follow from the absence of such states. -/
theorem exercise_8_22b (hP : IsStochasticMatrix P) (i : s) (hi : IsNullState P i) :
    (¬ Summable (fun n : ℕ => transitionProbability P (n + 1) i i)) ∧
      Tendsto (fun n : ℕ => transitionProbability P n i i) atTop (𝓝 0) :=
  ((exercise_8_21 hP).1 i hi).elim

/-- **Exercise 22(c)** of [benIsrael2003generalized], Chapter 8. The positive
return probabilities of an ergodic state tend to the reciprocal of its mean
return time, even when the rest of the chain is reducible. -/
theorem exercise_8_22c (hP : IsStochasticMatrix P) (i : s) (hi : IsErgodicState P i) :
    Tendsto (fun n : ℕ => transitionProbability P n i i) atTop
      (𝓝 ((meanFirstPassageTime P i i).toReal)⁻¹) := by
  obtain ⟨S, hS, hm⟩ := (isRecurrentState_iff_mem_closedCommunicatingClass hP i).mp hi.1
  let := Fintype.ofFinite S
  let a : S := ⟨i, hm⟩
  let : Nonempty S := ⟨a⟩
  let Q := restrictTransition P S
  have hQ := hS.2.1.stochastic_restrictTransition hP
  have hI := hS.irreducible_restrictTransition
  have hEa : statePeriod Q a = 1 := (hS.2.1.statePeriod_restrictTransition a).trans hi.2.1
  have hE : IsErgodicChain Q :=
    ⟨hI, fun b => (statePeriod_eq_of_communicates hQ ⟨hI b a, hI a b⟩).trans hEa⟩
  obtain ⟨π, _, _, hlim, hμ, _⟩ := theorem_8 hQ hE
  have ht := hlim a a
  rw [hμ a, hS.2.1.meanFirstPassageTime_restrictTransition a a] at ht
  simpa only [hS.2.1.transitionProbability_restrictTransition] using ht

end LocalRecurrence

section PeriodicReturns

variable {s : Type*} [Fintype s] [DecidableEq s]
variable {P : Matrix s s ℝ}

private theorem statePeriod_pos_of_leadsTo_self {i : s} (hi : LeadsTo P i i) :
    0 < statePeriod P i := by
  exact zero_lt_one.trans_le (le_csSup (common_return_divisors_bddAbove hi)
    (show 1 ∈ {d : ℕ | ∀ n : ℕ, 0 < n → 0 < transitionProbability P n i i → d ∣ n}
      from fun _ _ _ => one_dvd _))

private theorem transitionProbability_iterated_pow (P : Matrix s s ℝ) (d n : ℕ) (i j : s) :
    transitionProbability (P ^ d) n i j = transitionProbability P (d * n) i j := by
  rw [transitionProbability, transitionProbability, pow_mul]

private theorem period_power_isErgodicState (hP : IsStochasticMatrix P)
    (hI : IsIrreducibleChain P) (i : s) : IsErgodicState (P ^ statePeriod P i) i := by
  let d := statePeriod P i
  let Q := P ^ d
  let S := stateReachableSet Q i
  have hd : 0 < d := statePeriod_pos_of_leadsTo_self (hI i i)
  have hQ : IsStochasticMatrix Q := stochastic_pow hP d
  have hscale {m : ℕ} (hm : 0 < m) (hdm : d ∣ m) {a b : s}
      (hp : 0 < transitionProbability P m a b) : LeadsTo Q a b := by
    obtain ⟨k, rfl⟩ := hdm
    exact ⟨k, Nat.pos_of_ne_zero (fun hk => by simp [hk] at hm),
      (transitionProbability_iterated_pow P d k a b).symm ▸ hp⟩
  have hself : LeadsTo Q i i := by
    obtain ⟨n, hn, hp⟩ := hI i i
    exact hscale hn (statePeriod_dvd_return hn hp) hp
  have hfwd (a : s) (ha : a ∈ S) : LeadsTo Q i a := by
    rcases ha with rfl | ha
    · exact hself
    · exact ha
  have hback (a : s) (ha : a ∈ S) : LeadsTo Q a i := by
    obtain ⟨n, hn, hip⟩ := hfwd a ha
    obtain ⟨m, hm, hap⟩ := hI a i
    rw [transitionProbability_iterated_pow] at hip
    have hsum : d ∣ d * n + m := statePeriod_dvd_return (by omega)
      (transitionProbability_pos_add hP hip hap)
    have hdm : d ∣ m := by
      simpa only [Nat.add_sub_cancel_left] using Nat.dvd_sub hsum (dvd_mul_right d n)
    exact hscale hm hdm hap
  have hclass : IsClosedCommunicatingClass Q S :=
    ⟨⟨i, Or.inl rfl⟩, isClosedStateSet_stateReachableSet hQ i,
      fun a ha b hb => ⟨leadsTo_trans hQ (hback a ha) (hfwd b hb),
        leadsTo_trans hQ (hback b hb) (hfwd a ha)⟩⟩
  have hdiv (n : ℕ) (hn : 0 < n) (hp : 0 < transitionProbability P n i i) :
      d * statePeriod Q i ∣ n := by
    obtain ⟨k, rfl⟩ := (show d ∣ n from statePeriod_dvd_return hn hp)
    have hk : 0 < k := Nat.pos_of_ne_zero (fun hk => by simp [hk] at hn)
    exact Nat.mul_dvd_mul_left d (statePeriod_dvd_return hk
      (show 0 < transitionProbability Q k i i by
        rw [show Q = P ^ d by rfl, transitionProbability_iterated_pow]
        exact hp))
  have hle : d * statePeriod Q i ≤ d :=
    le_csSup (common_return_divisors_bddAbove (hI i i)) hdiv
  have hperiod : statePeriod Q i = 1 := by
    refine le_antisymm ?_ (statePeriod_pos_of_leadsTo_self hself)
    exact Nat.le_of_mul_le_mul_left (by simpa only [mul_one] using hle) hd
  have ⟨hrec, hmean⟩ := hclass.recurrent_and_mean_return_ne_top hQ ⟨i, Or.inl rfl⟩
  exact ⟨hrec, hperiod, hmean⟩

private theorem sum_range_on_multiples (u : ℕ → ℝ) {d : ℕ} (hd : 0 < d)
    (hz : ∀ n : ℕ, ¬ d ∣ n → u n = 0) (N : ℕ) :
    (∑ n ∈ Finset.range (d * N), u n) = ∑ n ∈ Finset.range N, u (d * n) := by
  classical
  rw [← Finset.sum_filter_of_ne (p := fun n => d ∣ n) (fun n _ hn =>
    Classical.byContradiction (fun h => hn (hz n h)))]
  symm
  refine Finset.sum_bij (fun n _ => d * n) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro n hn
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hn) hd),
        dvd_mul_right d n⟩
  · intro a _ b _ he
    exact Nat.eq_of_mul_eq_mul_left hd he
  · intro n hn
    obtain ⟨hN, k, rfl⟩ := Finset.mem_filter.mp hn
    exact ⟨k, Finset.mem_range.mpr (Nat.lt_of_mul_lt_mul_left (Finset.mem_range.mp hN)), rfl⟩

private theorem transitionCesaro_period_subseq (hP : IsStochasticMatrix P)
    (i : s) (hd : 0 < statePeriod P i) (N : ℕ) :
    transitionCesaro P (statePeriod P i * (N + 1) - 1) i i =
      (statePeriod P i : ℝ)⁻¹ * transitionCesaro (P ^ statePeriod P i) N i i := by
  let d := statePeriod P i
  let u n := transitionProbability P n i i
  have hz (n : ℕ) (hn : ¬ d ∣ n) : u n = 0 := by
    refine le_antisymm (le_of_not_gt fun hpos => hn ?_) ((stochastic_pow hP n).1 i i)
    have hn0 : n ≠ 0 := fun h => hn (h ▸ dvd_zero d)
    exact statePeriod_dvd_return (Nat.pos_of_ne_zero hn0) hpos
  have hpos : 0 < d * (N + 1) := Nat.mul_pos hd (Nat.succ_pos N)
  have hden : (((d * (N + 1) - 1 : ℕ) : ℝ) + 1) = (d : ℝ) * ((N : ℝ) + 1) := by
    calc
      _ = ((d * (N + 1) - 1 + 1 : ℕ) : ℝ) := by norm_cast
      _ = ((d * (N + 1) : ℕ) : ℝ) := by rw [Nat.sub_add_cancel hpos]
      _ = _ := by norm_cast
  simp only [transitionCesaro, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  change (((d * (N + 1) - 1 : ℕ) : ℝ) + 1)⁻¹ *
      (∑ n ∈ Finset.range (d * (N + 1) - 1 + 1), u n) =
    (d : ℝ)⁻¹ * (((N : ℝ) + 1)⁻¹ *
      (∑ n ∈ Finset.range (N + 1), transitionProbability (P ^ d) n i i))
  rw [hden, Nat.sub_add_cancel hpos, sum_range_on_multiples u hd hz,
    mul_inv, mul_assoc]
  simp only [transitionProbability_iterated_pow, u]
  rfl

private theorem periodic_return_limit_irreducible (hP : IsStochasticMatrix P)
    (hI : IsIrreducibleChain P) (i : s) :
    Tendsto (fun n : ℕ => transitionProbability P (n * statePeriod P i) i i) atTop
      (𝓝 ((statePeriod P i : ℝ) * ((meanFirstPassageTime P i i).toReal)⁻¹)) := by
  let d := statePeriod P i
  let Q := P ^ d
  let L := ((meanFirstPassageTime Q i i).toReal)⁻¹
  let M := ((meanFirstPassageTime P i i).toReal)⁻¹
  have hd : 0 < d := statePeriod_pos_of_leadsTo_self (hI i i)
  have hq : Tendsto (fun n : ℕ => transitionProbability Q n i i) atTop (𝓝 L) :=
    exercise_8_22c (stochastic_pow hP d) i (period_power_isErgodicState hP hI i)
  have hq_avg : Tendsto (fun n : ℕ => transitionCesaro Q n i i) atTop (𝓝 L) := by
    have ht := hq.cesaro.comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, transitionCesaro, Matrix.smul_apply, smul_eq_mul,
      Matrix.sum_apply, Nat.cast_add, Nat.cast_one, transitionProbability] using ht
  have hsub : Tendsto (fun n : ℕ => d * (n + 1) - 1) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_id
    change n ≤ d * (n + 1) - 1
    have h := Nat.le_mul_of_pos_left (n + 1) hd
    omega
  have hp_avg : Tendsto (fun n : ℕ => transitionCesaro P (d * (n + 1) - 1) i i) atTop (𝓝 M) :=
    (theorem_7 hP hI i i).comp hsub
  have hq_avg' :
      Tendsto (fun n : ℕ => transitionCesaro P (d * (n + 1) - 1) i i) atTop
        (𝓝 ((d : ℝ)⁻¹ * L)) := by
    have he : (fun n : ℕ => transitionCesaro P (d * (n + 1) - 1) i i) =
        fun n : ℕ => (d : ℝ)⁻¹ * transitionCesaro Q n i i :=
      funext (transitionCesaro_period_subseq hP i hd)
    rw [he]
    exact tendsto_const_nhds.mul hq_avg
  have hcoeff := tendsto_nhds_unique hp_avg hq_avg'
  have hL : L = (d : ℝ) * M := by
    rw [hcoeff, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hd.ne'), one_mul]
  rw [hL] at hq
  simpa only [Q, d, M, transitionProbability_iterated_pow, Nat.mul_comm] using hq

/-- **Exercise 22(d)** of [benIsrael2003generalized], Chapter 8. Along the
multiples of its period, a recurrent state's return probabilities tend to
the period divided by the mean return time. -/
theorem exercise_8_22d (hP : IsStochasticMatrix P) (i : s) (hi : IsRecurrentState P i)
    (_hmean : meanFirstPassageTime P i i ≠ ⊤) :
    Tendsto (fun n : ℕ => transitionProbability P (n * statePeriod P i) i i) atTop
      (𝓝 ((statePeriod P i : ℝ) * ((meanFirstPassageTime P i i).toReal)⁻¹)) := by
  obtain ⟨S, hS, hm⟩ := (isRecurrentState_iff_mem_closedCommunicatingClass hP i).mp hi
  let := Fintype.ofFinite S
  let j : S := ⟨i, hm⟩
  simpa only [hS.2.1.transitionProbability_restrictTransition,
    hS.2.1.statePeriod_restrictTransition, hS.2.1.meanFirstPassageTime_restrictTransition] using
    periodic_return_limit_irreducible (hS.2.1.stochastic_restrictTransition hP)
      hS.irreducible_restrictTransition j

/-- **Exercise 22(c,d)** of [benIsrael2003generalized], Chapter 8. Aperiodic
states have the ordinary return limit, and positive recurrent states have
the corresponding period-sampled limit. -/
theorem exercise_8_22cd (hP : IsStochasticMatrix P) (i : s) :
    (IsErgodicState P i →
      Tendsto (fun n : ℕ => transitionProbability P n i i) atTop
        (𝓝 ((meanFirstPassageTime P i i).toReal)⁻¹)) ∧
    (IsRecurrentState P i → meanFirstPassageTime P i i ≠ ⊤ →
      Tendsto (fun n : ℕ => transitionProbability P (n * statePeriod P i) i i) atTop
        (𝓝 ((statePeriod P i : ℝ) * ((meanFirstPassageTime P i i).toReal)⁻¹))) :=
  ⟨exercise_8_22c hP i, exercise_8_22d hP i⟩

end PeriodicReturns

section ComponentDecomposition

variable {s : Type*} [Fintype s] [DecidableEq s]
variable {P : Matrix s s ℝ}

/-- The communicating component of a state, with the starting state included
even when it has no positive-time return. -/
def markovCommunicationComponent (P : Matrix s s ℝ) (i : s) : Set s :=
  {j | stateReachableSet P j = stateReachableSet P i}

/-- Two states share a communicating component exactly when their reachable sets agree. -/
@[simp]
theorem mem_markovCommunicationComponent {i j : s} :
    j ∈ markovCommunicationComponent P i ↔ stateReachableSet P j = stateReachableSet P i :=
  Iff.rfl

private theorem mem_stateReachableSet_of_pos_transition {i j : s} {n : ℕ}
    (h : 0 < transitionProbability P n i j) : j ∈ stateReachableSet P i := by
  cases n with
  | zero =>
    by_cases hi : i = j
    · exact Or.inl hi
    · simp [transitionProbability_zero, hi] at h
  | succ n => exact Or.inr ⟨n + 1, Nat.succ_pos n, h⟩

private theorem transitionProbability_restrict_communicationComponent
    (hP : IsStochasticMatrix P) (a : s) [Fintype (markovCommunicationComponent P a)]
    (n : ℕ) (i j : markovCommunicationComponent P a) :
    transitionProbability (restrictTransition P (markovCommunicationComponent P a)) n i j =
      transitionProbability P n i.val j.val := by
  let S := markovCommunicationComponent P a
  change transitionProbability (restrictTransition P S) n i j = _
  induction n generalizing j with
  | zero => simp only [transitionProbability_zero, Subtype.ext_iff]
  | succ n ih =>
    rw [chapmanKolmogorov _ n 1, chapmanKolmogorov _ n 1]
    have hterm (k : S) : transitionProbability (restrictTransition P S) n i k *
        transitionProbability (restrictTransition P S) 1 k j =
        transitionProbability P n i.val k.val * transitionProbability P 1 k.val j.val := by
      rw [ih k]
      simp [transitionProbability]
    simp only [hterm]
    rw [Finset.sum_set_coe (f := fun k =>
      transitionProbability P n i.val k * transitionProbability P 1 k j.val) S]
    apply Finset.sum_subset S.toFinset.subset_univ
    intro k _ hk
    have hnonneg : 0 ≤ transitionProbability P n i.val k * transitionProbability P 1 k j.val :=
      mul_nonneg ((stochastic_pow hP n).1 i k) ((stochastic_pow hP 1).1 k j)
    refine le_antisymm (le_of_not_gt ?_) hnonneg
    intro hpos
    have hik := mem_stateReachableSet_of_pos_transition
      (pos_of_mul_pos_left hpos ((stochastic_pow hP 1).1 k j))
    have hkj := mem_stateReachableSet_of_pos_transition
      (pos_of_mul_pos_right hpos ((stochastic_pow hP n).1 i k))
    have hi : stateReachableSet P i.val = stateReachableSet P a := i.property
    have hj : stateReachableSet P j.val = stateReachableSet P a := j.property
    have hKi := stateReachableSet_subset_of_mem hP hik
    have hJk := stateReachableSet_subset_of_mem hP hkj
    have hKa : stateReachableSet P k = stateReachableSet P a := by
      rw [hi] at hKi
      rw [hj] at hJk
      exact Set.Subset.antisymm hKi hJk
    exact hk (Set.mem_toFinset.mpr hKa)

private theorem not_isReducible_restrict_communicationComponent (hP : IsStochasticMatrix P)
    (a : s) : ¬ BenIsraelGreville.Chapter00.isReducible
      (restrictTransition P (markovCommunicationComponent P a)) := by
  let S := markovCommunicationComponent P a
  let := Fintype.ofFinite S
  let Q := restrictTransition P S
  rintro ⟨T, ⟨j, hj⟩, ⟨i, hi⟩, hzero⟩
  have hc : IsClosedStateSet Q Tᶜ := by
    intro b hb c hc
    exact hzero b hb c (Classical.byContradiction hc)
  have hjR : j.val ∈ stateReachableSet P i.val := by
    have hiR : stateReachableSet P i.val = stateReachableSet P a := i.property
    have hjR : stateReachableSet P j.val = stateReachableSet P a := j.property
    rw [hiR, ← hjR]
    exact Or.inl rfl
  rcases hjR with heq | ⟨n, _, hn⟩
  · exact hi ((Subtype.ext heq).symm ▸ hj)
  · have hq := hc.transitionProbability_eq_zero hi (fun h => h hj) n
    rw [transitionProbability_restrict_communicationComponent hP a n i j] at hq
    rw [hq] at hn
    exact (lt_irrefl 0) hn

private theorem closedCommunicatingClass_eq_communicationComponent (hP : IsStochasticMatrix P)
    {S : Set s} (hS : IsClosedCommunicatingClass P S) {i : s} (hi : i ∈ S) :
    S = markovCommunicationComponent P i := by
  ext j
  rw [mem_markovCommunicationComponent]
  constructor
  · intro hj
    have hc := hS.2.2 i hi j hj
    exact Set.Subset.antisymm (stateReachableSet_subset_of_mem hP (Or.inr hc.1))
      (stateReachableSet_subset_of_mem hP (Or.inr hc.2))
  · intro he
    have hj : j ∈ stateReachableSet P i := he ▸ mem_stateReachableSet_self P j
    rcases hj with rfl | hj
    · exact hi
    · exact hS.2.1.mem_of_leadsTo hi hj

/-- **Exercise 19**, Equation (108) of [benIsrael2003generalized], Chapter 8.
The state reindexing gives an upper block triangular matrix. Its final blocks
are exactly the minimal closed classes, are irreducible stochastic matrices,
and have zero off-diagonal row blocks. The earlier blocks are irreducible
in the matrix sense, which includes a singleton having zero self-transition. -/
theorem exercise_8_19 (hP : IsStochasticMatrix P) :
    ∃ (n k : ℕ) (C : Fin n → Set s) (e : (Σ a, C a) ≃ s),
      k ≤ n ∧ (∀ a i, e ⟨a, i⟩ = i.val) ∧
      (∀ a, (C a).Nonempty ∧ ¬ BenIsraelGreville.Chapter00.isReducible (restrictTransition P (C a))) ∧
      (∀ a, IsClosedCommunicatingClass P (C a) ↔ k ≤ a.val) ∧
      (∀ S, IsClosedCommunicatingClass P S → ∃ a, S = C a) ∧
      (∀ (a : Fin n) [Fintype (C a)], k ≤ a.val →
        IsStochasticMatrix (restrictTransition P (C a)) ∧ IsIrreducibleChain (restrictTransition P (C a))) ∧
      (∀ (a b : Fin n) (i : C a) (j : C b), b < a ∨ (k ≤ a.val ∧ a ≠ b) →
        P.submatrix e e ⟨a, i⟩ ⟨b, j⟩ = 0) := by
  classical
  let R := Set.range (stateReachableSet P)
  let F (A : R) : Set s := {i | stateReachableSet P i = A.val}
  let := Fintype.ofFinite R
  let r := Fintype.card R
  let N := Nat.card s
  let tie := Fintype.equivFin R
  let closed (A : R) := IsClosedCommunicatingClass P (F A)
  let score (A : R) := if closed A then N + 1 else N - A.val.ncard
  let key (A : R) : Lex (ℕ × Fin r) := toLex (score A, tie A)
  have hkey : Function.Injective key := by
    intro A B h
    exact tie.injective (congrArg Prod.snd (toLex.injective h))
  let K := Set.range key
  let keyEquiv : R ≃ K := Equiv.ofInjective key hkey
  let := Fintype.ofFinite K
  let n := Fintype.card K
  let order : Fin n ≃o K := Fintype.orderIsoFinOfCardEq K rfl
  let ord : Fin n ≃ R := order.toEquiv.trans keyEquiv.symm
  let C (a : Fin n) : Set s := F (ord a)
  let idx (i : s) : R := ⟨stateReachableSet P i, ⟨i, rfl⟩⟩
  let index (i : s) : Fin n := ord.symm (idx i)
  let fibres (a : Fin n) : C a ≃ {i // index i = a} :=
    Equiv.subtypeEquivRight fun i => by
      change stateReachableSet P i = (ord a).val ↔ ord.symm (idx i) = a
      rw [Equiv.symm_apply_eq]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  let e : (Σ a, C a) ≃ s := (Equiv.sigmaCongrRight fibres).trans (Equiv.sigmaFiberEquiv index)
  have hsort {a b : Fin n} (h : score (ord a) < score (ord b)) : a < b := by
    apply order.lt_iff_lt.mp
    have he (j : Fin n) : key (ord j) = (order j).val :=
      congrArg Subtype.val (keyEquiv.apply_symm_apply (order j))
    change (order a).val < (order b).val
    rw [← he, ← he]
    exact Prod.Lex.left _ _ h
  have hlast (a b : Fin n) (ha : IsClosedCommunicatingClass P (C a))
      (hb : ¬ IsClosedCommunicatingClass P (C b)) : b < a := by
    apply hsort
    change closed (ord a) at ha
    change ¬closed (ord b) at hb
    simp only [score, ite_eq_right hb, ite_eq_left ha]
    omega
  have hmono (a b : Fin n) (hab : a ≤ b) (ha : IsClosedCommunicatingClass P (C a)) :
      IsClosedCommunicatingClass P (C b) := by
    by_contra hb
    exact (not_lt_of_ge hab) (hlast a b ha hb)
  have hcut : ∃ k ≤ n, ∀ a : Fin n, IsClosedCommunicatingClass P (C a) ↔ k ≤ a.val := by
    let A := Finset.univ.filter (fun a : Fin n => IsClosedCommunicatingClass P (C a))
    by_cases hA : A.Nonempty
    · let a₀ := A.min' hA
      have ha₀ : IsClosedCommunicatingClass P (C a₀) :=
        (Finset.mem_filter.mp (A.min'_mem hA)).2
      refine ⟨a₀.val, a₀.isLt.le, fun a => ⟨fun ha => ?_, fun hab => hmono _ _ hab ha₀⟩⟩
      exact A.min'_le a (Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩)
    · refine ⟨n, le_rfl, fun a => ⟨fun ha => ?_, fun hn => (a.isLt.not_ge hn).elim⟩⟩
      exact (hA ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩).elim
  obtain ⟨k, hk, hC⟩ := hcut
  have hmember (a : Fin n) : ∃ i : s, stateReachableSet P i = (ord a).val := (ord a).property
  have hfibre {a : Fin n} {i : s} (hi : i ∈ C a) : C a = markovCommunicationComponent P i := by
    have hi' : stateReachableSet P i = (ord a).val := hi
    ext j
    simp only [mem_markovCommunicationComponent, hi']
    rfl
  refine ⟨n, k, C, e, hk, fun _ _ => rfl, ?_, hC, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨i, hi⟩ := hmember a
    exact ⟨⟨i, hi⟩, hfibre hi ▸ not_isReducible_restrict_communicationComponent hP i⟩
  · intro S hS
    obtain ⟨i, hi⟩ := hS.1
    refine ⟨index i, (closedCommunicatingClass_eq_communicationComponent hP hS hi).trans ?_⟩
    exact (hfibre (show i ∈ C (index i) from
      (congrArg Subtype.val (ord.apply_symm_apply (idx i))).symm)).symm
  · intro a hFinite ha
    have hc := (hC a).2 ha
    exact ⟨hc.2.1.stochastic_restrictTransition hP, hc.irreducible_restrictTransition⟩
  · intro a b i j hblock
    change P i.val j.val = 0
    have hab : a ≠ b := hblock.elim ne_of_gt And.right
    have hout : j.val ∉ C a := by
      intro hj
      have hjb : stateReachableSet P j.val = (ord b).val := j.property
      exact hab (ord.injective (Subtype.ext ((show stateReachableSet P j.val = (ord a).val from
        hj).symm.trans hjb)))
    by_cases ha : IsClosedCommunicatingClass P (C a)
    · exact ha.2.1 i i.property j hout
    · have hba : b < a := hblock.elim id (fun h => (ha ((hC a).2 h.1)).elim)
      refine le_antisymm (le_of_not_gt ?_) (hP.1 i j)
      intro hpos
      have hsub := stateReachableSet_subset_of_mem hP
        (show j.val ∈ stateReachableSet P i.val from Or.inr (leadsTo_of_pos_entry hpos))
      have hi' : stateReachableSet P i.val = (ord a).val := i.property
      have hj' : stateReachableSet P j.val = (ord b).val := j.property
      rw [hi', hj'] at hsub
      have hstrict : (ord b).val ⊂ (ord a).val :=
        Set.ssubset_iff_subset_ne.mpr ⟨hsub, fun he => hab (ord.injective (Subtype.ext he.symm))⟩
      have hcard := Set.ncard_lt_ncard hstrict
      have hu : (ord a).val.ncard ≤ N := Set.ncard_le_card (ord a).val
      have hscore : score (ord a) < score (ord b) := by
        change ¬closed (ord a) at ha
        by_cases hb : closed (ord b)
        · simp only [score, ite_eq_right ha, ite_eq_left hb]
          omega
        · simp only [score, ite_eq_right ha, ite_eq_right hb]
          omega
      exact (not_lt_of_ge hba.le) (hsort hscore)

end ComponentDecomposition

section AbsorbingBlocks

variable {s : Type*} [Fintype s] [DecidableEq s]
variable {P : Matrix s s ℝ}

private theorem matrix_submatrix_equiv_pow {r : Type*} [Fintype r] [DecidableEq r]
    (M : Matrix s s ℝ) (e : r ≃ s) (n : ℕ) :
    (M ^ n).submatrix e e = (M.submatrix e e) ^ n := by
  induction n with
  | zero => simp only [pow_zero, Matrix.submatrix_one_equiv]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← Matrix.submatrix_mul_equiv _ _ e e e, ih]

private theorem absorbing_fromBlocks_pow {r t : Type*} [Fintype r] [DecidableEq r]
    [Fintype t] [DecidableEq t] (R : Matrix t r ℝ) (K : Matrix t t ℝ) (n : ℕ) :
    (Matrix.fromBlocks (1 : Matrix r r ℝ) 0 R K) ^ n =
      Matrix.fromBlocks (1 : Matrix r r ℝ) 0 ((∑ a ∈ Finset.range n, K ^ a) * R) (K ^ n) := by
  induction n with
  | zero => simp only [pow_zero, Finset.range_zero, Finset.sum_empty, Matrix.zero_mul, Matrix.fromBlocks_one]
  | succ n ih =>
    conv_lhs => rw [pow_succ, ih, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Finset.sum_range_succ, Matrix.add_mul, pow_succ]

private theorem absorbing_subset_reindex (hP : IsStochasticMatrix P) :
    ∃ (r t : ℕ) (e : Fin r ⊕ Fin t ≃ s) (R : Matrix (Fin t) (Fin r) ℝ)
      (K : Matrix (Fin t) (Fin t) ℝ),
      (∀ i, IsAbsorbingState P i ↔ ∃ a, e (Sum.inl a) = i) ∧
        P.submatrix e e = Matrix.fromBlocks 1 0 R K := by
  classical
  let A := {i : s | IsAbsorbingState P i}
  let T := {i : s | ¬IsAbsorbingState P i}
  let := Fintype.ofFinite A
  let := Fintype.ofFinite T
  let a := Fintype.equivFin A
  let b := Fintype.equivFin T
  let e := (a.symm.sumCongr b.symm).trans (Equiv.sumCompl (IsAbsorbingState P))
  let R := P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl)
  let K := P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)
  have hA (i : Fin (Fintype.card A)) : IsAbsorbingState P (e (Sum.inl i)) :=
    (a.symm i).property
  refine ⟨_, _, e, R, K, ?_, ?_⟩
  · intro i
    constructor
    · intro hi
      refine ⟨a ⟨i, hi⟩, ?_⟩
      change (a.symm (a ⟨i, hi⟩)).val = i
      rw [a.symm_apply_apply]
    · rintro ⟨j, hj⟩
      exact hj ▸ hA j
  · ext i j
    rcases i with i | i <;> rcases j with j | j
    · change P (e (Sum.inl i)) (e (Sum.inl j)) = (1 : Matrix _ _ ℝ) i j
      by_cases he : i = j
      · subst j
        simpa only [Matrix.one_apply_eq, IsAbsorbingState] using hA i
      · rw [Matrix.one_apply_ne he]
        exact absorbing_apply_of_ne hP (hA i) (fun h => he (Sum.inl.inj (e.injective h.symm)))
    · exact absorbing_apply_of_ne hP (hA i) (by intro h; cases e.injective h)
    · rfl
    · rfl

open scoped Matrix.Norms.Operator in
private theorem absorbing_block_spectralRadius_lt_one (hP : IsStochasticMatrix P)
    (habs : IsAbsorbingChain P) {r t : ℕ} {e : Fin r ⊕ Fin t ≃ s}
    {R : Matrix (Fin t) (Fin r) ℝ} {K : Matrix (Fin t) (Fin t) ℝ}
    (hA : ∀ i, IsAbsorbingState P i ↔ ∃ a, e (Sum.inl a) = i)
    (hB : P.submatrix e e = Matrix.fromBlocks 1 0 R K) : K.complexSpectralRadius < 1 := by
  classical
  have hpowers (n : ℕ) : (P ^ n).submatrix e e =
      Matrix.fromBlocks 1 0 ((∑ a ∈ Finset.range n, K ^ a) * R) (K ^ n) := by
    rw [matrix_submatrix_equiv_pow, hB, absorbing_fromBlocks_pow]
  have hKpow (n : ℕ) (i j : Fin t) :
      (K ^ n) i j = transitionProbability P n (e (Sum.inr i)) (e (Sum.inr j)) :=
    (congrFun (congrFun (hpowers n) (Sum.inr i)) (Sum.inr j)).symm
  have hAdiag (n : ℕ) (j : Fin r) :
      transitionProbability P n (e (Sum.inl j)) (e (Sum.inl j)) = 1 := by
    simpa only [Matrix.fromBlocks_apply₁₁, Matrix.one_apply_eq, Matrix.submatrix_apply,
      transitionProbability] using
      congrFun (congrFun (hpowers n) (Sum.inl j)) (Sum.inl j)
  by_cases ht : Nonempty (Fin t)
  · let := ht
    have hReach (i : Fin t) : ∃ a : Fin r, LeadsTo P (e (Sum.inr i)) (e (Sum.inl a)) := by
      obtain ⟨j, hj, hreach⟩ := habs (e (Sum.inr i))
      obtain ⟨a, rfl⟩ := (hA j).1 hj
      exact ⟨a, hreach⟩
    choose a n hn hpos using hReach
    let N := Finset.univ.sup n
    have hle (i : Fin t) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
    have hN : 0 < N := (hn (Classical.choice ht)).trans_le (hle (Classical.choice ht))
    have hposN (i : Fin t) :
        0 < transitionProbability P N (e (Sum.inr i)) (e (Sum.inl (a i))) := by
      have h := transitionProbability_mul_le_of_join hP (n i) (N - n i)
        (e (Sum.inr i)) (e (Sum.inl (a i))) (e (Sum.inl (a i)))
      rw [Nat.add_sub_of_le (hle i), hAdiag, mul_one] at h
      exact (hpos i).trans_le h
    have hrows (i : Fin t) : ∑ j, (K ^ N) i j < 1 := by
      have hs := sum_row_of_mem_rowStochastic (stochastic_pow hP N) (e (Sum.inr i))
      rw [← Equiv.sum_comp e] at hs
      simp only [Fintype.sum_sum_type] at hs
      have hlt : 0 < ∑ j, transitionProbability P N (e (Sum.inr i)) (e (Sum.inl j)) :=
        (hposN i).trans_le (Finset.single_le_sum
          (fun j _ => (show 0 ≤ transitionProbability P N (e (Sum.inr i)) (e (Sum.inl j)) from
            (stochastic_pow hP N).1 _ _)) (Finset.mem_univ (a i)))
      simp_rw [hKpow]
      change (∑ j, transitionProbability P N (e (Sum.inr i)) (e (Sum.inl j))) +
        (∑ j, transitionProbability P N (e (Sum.inr i)) (e (Sum.inr j))) = 1 at hs
      linarith
    obtain ⟨i₀, _, hmax⟩ := Finset.exists_max_image Finset.univ
      (fun i => ∑ j, (K ^ N) i j) Finset.univ_nonempty
    have hnonneg (i j : Fin t) : 0 ≤ (K ^ N) i j := by
      rw [hKpow]
      exact (stochastic_pow hP N).1 _ _
    have hnorm : ‖K ^ N‖ ≤ ∑ j, (K ^ N) i₀ j := by
      apply linfty_opNorm_le_of_forall_sum_le (Finset.sum_nonneg (fun j _ => hnonneg i₀ j))
      intro i
      simpa only [abs_of_nonneg, hnonneg] using hmax i (Finset.mem_univ i)
    have hρ : (K ^ N).complexSpectralRadius < 1 := by
      calc
        _ ≤ (‖K ^ N‖₊ : ℝ≥0∞) := complexSpectralRadius_le_linfty_opNNNorm (K ^ N)
        _ = ENNReal.ofReal ‖K ^ N‖ := (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal (∑ j, (K ^ N) i₀ j) := ENNReal.ofReal_le_ofReal hnorm
        _ < 1 := ENNReal.ofReal_lt_one.mpr (hrows i₀)
    rw [complexSpectralRadius_pow K hN.ne'] at hρ
    exact lt_of_not_ge fun h => not_lt_of_ge (one_le_pow₀ h) hρ
  · have hz : K = 0 := Matrix.ext fun i _ => (ht ⟨i⟩).elim
    simp [hz]

private theorem groupInverse_absorbing_fromBlocks {r t : Type*} [Fintype r] [DecidableEq r]
    [Fintype t] [DecidableEq t] (R : Matrix t r ℝ) (K : Matrix t t ℝ)
    (hK : K.complexSpectralRadius < 1) :
    IsGroupInverse (1 - Matrix.fromBlocks (1 : Matrix r r ℝ) 0 R K)
      (Matrix.fromBlocks (0 : Matrix r r ℝ) 0 (-(((1 - K)⁻¹ : Matrix t t ℝ) ^ 2 * R)) (1 - K)⁻¹) := by
  let B := 1 - K
  let U := B⁻¹
  let Q := Matrix.fromBlocks (0 : Matrix r r ℝ) 0 (-R) B
  let G := Matrix.fromBlocks (0 : Matrix r r ℝ) 0 (-(U ^ 2 * R)) U
  have hunit : IsUnit B := isUnit_one_sub_of_complexSpectralRadius_lt_one hK
  have hBU : B * U = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det B).mp hunit)
  have hUB : U * B = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det B).mp hunit)
  have h2 : B * (U ^ 2 * R) = U * R := by
    rw [pow_two, ← Matrix.mul_assoc B, ← Matrix.mul_assoc B, hBU, Matrix.one_mul]
  have hQ : (1 : Matrix (r ⊕ t) (r ⊕ t) ℝ) - Matrix.fromBlocks 1 0 R K = Q := by
    rw [← Matrix.fromBlocks_one (l := r) (m := t)]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Q, B, Matrix.one_apply]
  rw [hQ, isGroupInverse_iff]
  change Commute Q G ∧ Q * G * Q = Q ∧ G * Q * G = G
  let E := Matrix.fromBlocks (0 : Matrix r r ℝ) 0 (-(U * R)) (1 : Matrix t t ℝ)
  have hQE : Q * G = E := by
    simp [Q, G, E, Matrix.fromBlocks_multiply, h2, hBU]
  have hGE : G * Q = E := by
    simp [Q, G, E, Matrix.fromBlocks_multiply, hUB]
  refine ⟨hQE.trans hGE.symm, ?_, ?_⟩
  · rw [hQE]
    simp [Q, E, Matrix.fromBlocks_multiply]
  · rw [hGE]
    simp [G, E, Matrix.fromBlocks_multiply]

private theorem tendsto_absorbing_fromBlocks_pow {r t : Type*} [Fintype r] [DecidableEq r]
    [Fintype t] [DecidableEq t] (R : Matrix t r ℝ) (K : Matrix t t ℝ)
    (hK : K.complexSpectralRadius < 1) :
    Tendsto (fun n : ℕ => (Matrix.fromBlocks (1 : Matrix r r ℝ) 0 R K) ^ n) atTop
      (𝓝 (Matrix.fromBlocks (1 : Matrix r r ℝ) 0 ((1 - K)⁻¹ * R) 0)) := by
  simp_rw [absorbing_fromBlocks_pow R K]
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  rcases i with i | i <;> rcases j with j | j
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds
  · simp only [Matrix.fromBlocks_apply₂₁]
    have hc : Continuous (fun A : Matrix t t ℝ => (A * R) i j) := by
      simp only [Matrix.mul_apply]
      fun_prop
    have ht := (hasSum_pow_inv_one_sub_of_complexSpectralRadius_lt_one hK).tendsto_sum_nat
    exact hc.continuousAt.tendsto.comp ht
  · simpa only [Matrix.fromBlocks_apply₂₂] using
      tendsto_pi_nhds.mp (tendsto_pi_nhds.mp
        ((tendsto_pow_iff_complexSpectralRadius_lt_one K).2 hK) i) j

private theorem groupInverse_submatrix_equiv {r : Type*} [Fintype r] [DecidableEq r]
    (hP : IsStochasticMatrix P) (e : r ≃ s) :
    IsGroupInverse (1 - P.submatrix e e) ((stochasticGroupInverse P hP).submatrix e e) := by
  let G := stochasticGroupInverse P hP
  let Q := 1 - P
  let M (A : Matrix s s ℝ) := A.submatrix e e
  have hMQ : M Q = 1 - M P := by simp [M, Q, Matrix.submatrix_sub, Matrix.submatrix_one_equiv]
  have hMul (A B : Matrix s s ℝ) : M (A * B) = M A * M B :=
    (Matrix.submatrix_mul_equiv A B e e e).symm
  have h := isGroupInverse_iff.mp (stochasticGroupInverse_spec P hP)
  obtain ⟨hc, hi, ho⟩ := h
  have hc' := congrArg M hc.eq
  have hi' := congrArg M hi
  have ho' := congrArg M ho
  change M (Q * G) = M (G * Q) at hc'
  change M (Q * G * Q) = M Q at hi'
  change M (G * Q * G) = M G at ho'
  simp only [hMul, hMQ] at hc' hi' ho'
  exact isGroupInverse_iff.mpr ⟨hc', hi', ho'⟩

/-- **Exercise 27(d)** and the absorbing case of **Theorem 10** of
[benIsrael2003generalized], Chapter 8. The absorbing states form the leading
identity block. The transient block has spectral radius less than one, and
the other blocks give the power limit and the group inverse of identity
minus the transition matrix. -/
theorem exercise_8_27d (hP : IsStochasticMatrix P) (habs : IsAbsorbingChain P) :
    ∃ (r t : ℕ) (e : Fin r ⊕ Fin t ≃ s) (R : Matrix (Fin t) (Fin r) ℝ)
      (K : Matrix (Fin t) (Fin t) ℝ),
      (∀ i, IsAbsorbingState P i ↔ ∃ a, e (Sum.inl a) = i) ∧
      P.submatrix e e = Matrix.fromBlocks 1 0 R K ∧ K.complexSpectralRadius < 1 ∧
      (∀ n : ℕ, (P ^ n).submatrix e e =
        Matrix.fromBlocks 1 0 ((∑ a ∈ Finset.range n, K ^ a) * R) (K ^ n)) ∧
      Tendsto (fun n : ℕ => (P ^ n).submatrix e e) atTop
        (𝓝 (Matrix.fromBlocks 1 0 ((1 - K)⁻¹ * R) 0)) ∧
      (stationaryProjection P hP).submatrix e e =
        Matrix.fromBlocks 1 0 ((1 - K)⁻¹ * R) 0 ∧
      (stochasticGroupInverse P hP).submatrix e e =
        Matrix.fromBlocks 0 0 (-((1 - K)⁻¹ ^ 2 * R)) (1 - K)⁻¹ := by
  obtain ⟨r, t, e, R, K, hA, hB⟩ := absorbing_subset_reindex hP
  have hK := absorbing_block_spectralRadius_lt_one hP habs hA hB
  have hpowers (n : ℕ) : (P ^ n).submatrix e e =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 R K) ^ n := by
    rw [matrix_submatrix_equiv_pow, hB]
  have ht : Tendsto (fun n : ℕ => (P ^ n).submatrix e e) atTop
      (𝓝 (Matrix.fromBlocks 1 0 ((1 - K)⁻¹ * R) 0)) := by
    simp_rw [hpowers]
    exact tendsto_absorbing_fromBlocks_pow R K hK
  refine ⟨r, t, e, R, K, hA, hB, hK, fun n => (hpowers n).trans (absorbing_fromBlocks_pow R K n),
    ht, ?_, ?_⟩
  · have hc : Continuous (fun A : Matrix s s ℝ => A.submatrix e e) := by
      apply continuous_pi_iff.mpr
      intro i
      apply continuous_pi_iff.mpr
      intro j
      exact (continuous_apply (e j)).comp (continuous_apply (e i))
    exact tendsto_nhds_unique (hc.continuousAt.tendsto.comp (theorem_10_absorbing hP habs)) ht
  · have hG := groupInverse_absorbing_fromBlocks R K hK
    rw [← hB] at hG
    exact (groupInverse_submatrix_equiv hP e).unique hG

end AbsorbingBlocks

section StationaryBlocks

variable {s : Type*} [Fintype s] [DecidableEq s]
variable {P : Matrix s s ℝ}

private theorem stationaryProjection_range_finrank_ergodic [Nonempty s]
    (hP : IsStochasticMatrix P) (hE : IsErgodicChain P) :
    Module.finrank ℝ (LinearMap.range (stationaryProjection P hP).toLin') = 1 := by
  let E := (stationaryProjection P hP).toLin'
  have hfixed (x : s → ℝ) : x ∈ LinearMap.range E ↔ P *ᵥ x = x := by
    constructor
    · rintro ⟨y, rfl⟩
      change P *ᵥ (stationaryProjection P hP *ᵥ y) = stationaryProjection P hP *ᵥ y
      rw [Matrix.mulVec_mulVec, (stationaryProjection_spec hP).2.1]
    · intro hx
      exact ⟨x, stationaryProjection_mulVec_of_fixed hP hx⟩
  have hr : LinearMap.range E = Submodule.span ℝ {(1 : s → ℝ)} := by
    ext x
    rw [hfixed, Submodule.mem_span_singleton]
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := fixed_by_transition_is_constant hP hE.1 hx
      exact ⟨c, funext fun i => by simpa using (hc i).symm⟩
    · rintro ⟨c, rfl⟩
      rw [Matrix.mulVec_smul, (mem_rowStochastic.mp hP).2]
  change Module.finrank ℝ (LinearMap.range E) = 1
  rw [hr]
  exact finrank_span_singleton (K := ℝ) (one_ne_zero : (1 : s → ℝ) ≠ 0)

set_option maxHeartbeats 700000 in
/-- **Exercise 27(a–c)** of [benIsrael2003generalized], Chapter 8. The range
and kernel of the stationary projection give a basis with diagonal blocks
I and K, where 1 is outside the complex spectrum of K. The identity block
has size one for a nonempty ergodic chain, and the powers of K tend to zero
for a regular chain. -/
theorem exercise_8_27abc (hP : IsStochasticMatrix P) :
    ∃ (k t : ℕ) (e : Fin k ⊕ Fin t ≃ s)
      (C : Matrix (Fin k ⊕ Fin t) (Fin k ⊕ Fin t) ℝ) (K : Matrix (Fin t) (Fin t) ℝ),
      IsUnit C ∧ Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 0 K =
        C⁻¹ * P.submatrix e e * C ∧ (1 : ℂ) ∉ spectrum ℂ (complexify K) ∧
      (Nonempty s → IsErgodicChain P → k = 1) ∧
      (IsRegularChain P → Tendsto (fun n : ℕ => K ^ n) atTop (𝓝 0)) := by
  classical
  let E := (stationaryProjection P hP).toLin'
  let L := P.toLin'
  let F := LinearMap.range E
  let T := LinearMap.ker E
  have hE : IsIdempotentElem E := by
    change E * E = E
    dsimp only [E]
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, (stationaryProjection_spec hP).1]
  have hFT : IsCompl F T := LinearMap.IsIdempotentElem.isCompl hE
  let k := Module.finrank ℝ F
  let t := Module.finrank ℝ T
  let bF := Module.finBasis ℝ F
  let bT := Module.finBasis ℝ T
  let q := F.prodEquivOfIsCompl T hFT
  let b := (bF.prod bT).map q
  have hbL (i : Fin k) : b (Sum.inl i) = (bF i).val := by
    simp [b, q, Submodule.coe_prodEquivOfIsCompl']
  have hbR (i : Fin t) : b (Sum.inr i) = (bT i).val := by
    simp [b, q, Submodule.coe_prodEquivOfIsCompl']
  have hEL (x : s → ℝ) : E (L x) = E x := by
    change stationaryProjection P hP *ᵥ (P *ᵥ x) = stationaryProjection P hP *ᵥ x
    rw [Matrix.mulVec_mulVec, (stationaryProjection_spec hP).2.2]
  have hLF (x : F) : L x.val = x.val := by
    obtain ⟨y, hy⟩ := x.property
    change P *ᵥ x.val = x.val
    rw [← hy]
    change P *ᵥ (stationaryProjection P hP *ᵥ y) = stationaryProjection P hP *ᵥ y
    rw [Matrix.mulVec_mulVec, (stationaryProjection_spec hP).2.1]
  let LT := L.restrict (p := T) (q := T) (fun {x} (hx : E x = 0) => show E (L x) = 0 from (hEL x).trans hx)
  let K := LinearMap.toMatrix bT bT LT
  have hK' (j : Fin t) : L (b (Sum.inr j)) = (LT (bT j)).val := by
    rw [hbR]
    rfl
  have hd : LinearMap.toMatrix b b L = Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 0 K := by
    ext i j
    rcases j with j | j
    · have hj : L (b (Sum.inl j)) = b (Sum.inl j) := by rw [hbL]; exact hLF (bF j)
      cases i <;> simp [LinearMap.toMatrix_apply, hj, Matrix.one_apply, Finsupp.single_apply, eq_comm]
    · rw [LinearMap.toMatrix_apply, hK']
      have hq : q.symm (LT (bT j)).val = (0, LT (bT j)) :=
        Submodule.prodEquivOfIsCompl_symm_apply_right F T hFT _
      change (bF.prod bT).repr (q.symm (LT (bT j)).val) i = _
      rw [hq]
      rcases i with i | i
      · simp only [Module.Basis.prod_repr_inl, map_zero, Finsupp.zero_apply,
          Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      · simp only [Module.Basis.prod_repr_inr, Matrix.fromBlocks_apply₂₂, K,
          LinearMap.toMatrix_apply]
  let e : Fin k ⊕ Fin t ≃ s := Fintype.equivOfCardEq
    ((Module.finrank_eq_card_basis b).symm.trans (Module.finrank_fintype_fun_eq_card ℝ))
  let b₀ := (Pi.basisFun ℝ s).reindex e.symm
  let C := LinearMap.toMatrix b b₀ (LinearMap.id : (s → ℝ) →ₗ[ℝ] s → ℝ)
  let D := LinearMap.toMatrix b₀ b (LinearMap.id : (s → ℝ) →ₗ[ℝ] s → ℝ)
  have hDC : D * C = 1 := by
    rw [← LinearMap.toMatrix_comp, LinearMap.id_comp, LinearMap.toMatrix_id]
  have hC : IsUnit C := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro hc
    have hdet := congrArg Matrix.det hDC
    simp [Matrix.det_mul, hc] at hdet
  have hD : D = C⁻¹ := (Matrix.inv_eq_left_inv hDC).symm
  have hPmat : LinearMap.toMatrix b₀ b₀ L = P.submatrix e e := by
    ext i j
    simp [LinearMap.toMatrix_apply, b₀, L, Matrix.toLin'_apply]
  have hsim : Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 0 K =
      C⁻¹ * P.submatrix e e * C := by
    rw [← hd, ← hD, ← hPmat, ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
    simp
  have hspec : (1 : ℝ) ∉ spectrum ℝ K := by
    intro h
    obtain ⟨v, hv, hvK⟩ := (Matrix.mem_spectrum_iff_exists_mulVec_eq_smul K (1 : ℝ)).mp h
    let w := bT.equivFun.symm v
    have hw : ⇑(bT.repr w) = v := by
      rw [← bT.equivFun_apply, LinearEquiv.apply_symm_apply]
    have hfix : LT w = w := by
      apply bT.equivFun.injective
      rw [bT.equivFun_apply, bT.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr bT bT,
        hw, hvK, one_smul]
    have he : P *ᵥ w.val = w.val := congrArg Subtype.val hfix
    have hzero : (w : s → ℝ) = 0 :=
      (stationaryProjection_mulVec_of_fixed hP he).symm.trans w.property
    have hwz : w = 0 := Subtype.ext hzero
    exact hv (hw.symm.trans (by simp [hwz]))
  have hspecC : (1 : ℂ) ∉ spectrum ℂ (complexify K) := by
    simpa only [Complex.ofReal_one] using
      (fun h => hspec ((Matrix.ofReal_mem_spectrum_complexify_iff K 1).mp h))
  refine ⟨k, t, e, C, K, hC, hsim, hspecC, ?_, ?_⟩
  · intro hs hE
    let := hs
    exact stationaryProjection_range_finrank_ergodic hP hE
  · intro hreg
    have hpow (n : ℕ) : LinearMap.toMatrix b b (P ^ n).toLin' =
        Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 0 (K ^ n) := by
      rw [Matrix.toLin'_pow]
      change LinearMap.toMatrix b b (L ^ n) = _
      rw [← LinearMap.toMatrix_pow b L n, hd, Matrix.fromBlocks_diagonal_pow, one_pow]
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    let g (A : Matrix s s ℝ) := b.coord (Sum.inr i) (A *ᵥ b (Sum.inr j))
    have hg : Continuous g := by
      have hc : Continuous (fun A : Matrix s s ℝ => A *ᵥ b (Sum.inr j)) := by
        apply continuous_pi_iff.mpr
        intro l
        simp only [Matrix.mulVec, dotProduct]
        fun_prop
      exact (b.coord (Sum.inr i)).continuous_of_finiteDimensional.comp hc
    have hterm (n : ℕ) : g (P ^ n) = (K ^ n) i j := by
      have h := congrFun (congrFun (hpow n) (Sum.inr i)) (Sum.inr j)
      change b.repr (P ^ n *ᵥ b (Sum.inr j)) (Sum.inr i) = _
      simpa only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₂₂, Matrix.toLin'_apply] using h
    have hG0 : g (stationaryProjection P hP) = 0 := by
      have hz : stationaryProjection P hP *ᵥ b (Sum.inr j) = 0 := by
        rw [hbR]
        exact (bT j).property
      simp [g, hz]
    have hconv := hg.continuousAt.tendsto.comp (theorem_10_regular hP hreg)
    change Tendsto (fun n : ℕ => g (P ^ n)) atTop (𝓝 (g (stationaryProjection P hP))) at hconv
    simpa only [hterm, hG0, Matrix.zero_apply] using hconv

end StationaryBlocks

end BenIsraelGreville.Chapter08
