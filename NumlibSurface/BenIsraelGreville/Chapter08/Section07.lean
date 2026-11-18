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

end BenIsraelGreville.Chapter08
