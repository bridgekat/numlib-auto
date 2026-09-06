/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Operator.Compact.Riesz`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Numlib.Analysis.Normed.Operator.Compact

/-!
# The Riesz ascent and descent of `μ • 1 - K` for a compact `K`

`Numlib/Analysis/Normed/Operator/Compact` proves what an equation of the second kind needs
directly: the eigenvalues of a compact operator accumulate only at `0`, the range of `μ • 1 - K`
is closed, Schauder's theorem, and the solvability criterion on a Hilbert space. This file adds
the *chain* structure that the Fredholm alternative leaves open — that the null spaces of the
powers of `μ • 1 - K` stop growing, that the ranges stop shrinking, and that the space is then
the direct sum of the two.

## Main statements

* `IsCompactOperator.exists_le_of_chain` — the one Riesz-lemma argument behind everything here.
  A chain of pairs `S' n ≤ S n` of subspaces on which `μ • 1 - K` decreases the index, and across
  which `K` does too, cannot consist of proper inclusions: an almost-orthogonal element of each
  would make the images under `K` pairwise `‖μ‖`-separated inside a compact set.
* `IsCompactOperator.exists_ker_pow_succ_le` and `IsCompactOperator.exists_range_pow_le_succ` —
  the ascent and the descent of `μ • 1 - K` are finite.
* `IsCompactOperator.exists_riesz_index` — the index `ν` itself: the null spaces increase strictly
  below `ν` and are constant from `ν` on, the ranges are constant from `ν` on, and
  `X = ker ((μ • 1 - K) ^ ν) ⊕ range ((μ • 1 - K) ^ ν)`.
* `IsCompactOperator.finiteDimensional_ker_pow` — every `ker ((μ • 1 - K) ^ n)` is
  finite-dimensional, because the compact operator `C` with `(μ • 1 - K) ^ n = μ ^ n • 1 - C`
  acts on that kernel as the invertible scalar `μ ^ n`.
* `IsCompactOperator.isUnit_smul_one_sub_of_isCompactOperator_pow` and
  `.hasEigenvalue_or_mem_resolventSet_of_isCompactOperator_pow` — the Fredholm alternative when
  only *some power* `K ^ m` is compact, which is the Riesz decomposition of `μ ^ m • 1 - K ^ m`
  together with the factorisation `μ ^ m • 1 - K ^ m = (μ • 1 - K) * S`.

* `IsCompactOperator.finrank_ker_eq_finrank_ker_adjoint` — on a Hilbert space,
  `dim (ker (μ • 1 - K)) = dim (ker (conj μ • 1 - K†))`: the operator has Fredholm index zero.
  This does *not* follow from the chain structure above, which concerns one operator at a time;
  it is a finite-rank perturbation argument, and the ascent–descent theory enters only through the
  finite-dimensionality of the two null spaces.

The auxiliary chain lemmas about the powers of a single operator — that the null spaces increase,
the ranges decrease, and that either chain is constant once two consecutive terms agree — are
stated for an arbitrary `A : X →L[𝕜] X` in the `ContinuousLinearMap` namespace, since compactness
plays no part in them.

## References

This is [han2009theoretical], Theorem 2.8.12 clauses (3), (5) and (6) and Theorem 2.8.14 (1);
[kress1989linear], §3, and [conway2007course], Chapter VII, develop the same theory.
-/

open Filter Metric Set Topology

namespace ContinuousLinearMap

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Applying a power of an operator one more time. -/
theorem pow_succ_apply (A : X →L[𝕜] X) (n : ℕ) (x : X) :
    (A ^ (n + 1)) x = (A ^ n) (A x) := by
  rw [pow_succ]; rfl

/-- Applying a power of an operator one more time, on the outside. -/
theorem pow_succ_apply' (A : X →L[𝕜] X) (n : ℕ) (x : X) :
    (A ^ (n + 1)) x = A ((A ^ n) x) := by
  rw [pow_succ']; rfl

/-- The null spaces of the powers of an operator increase. -/
theorem ker_pow_mono (A : X →L[𝕜] X) {m n : ℕ} (hmn : m ≤ n) : (A ^ m).ker ≤ (A ^ n).ker := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hmn
  intro x hx
  have hx' : (A ^ m) x = 0 := hx
  change (A ^ (m + c)) x = 0
  have h : (A ^ (m + c)) x = (A ^ c) ((A ^ m) x) := by rw [add_comm, pow_add]; rfl
  rw [h, hx', map_zero]

/-- The ranges of the powers of an operator decrease. -/
theorem range_pow_anti (A : X →L[𝕜] X) {m n : ℕ} (hmn : m ≤ n) :
    (A ^ n).range ≤ (A ^ m).range := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hmn
  intro y hy
  obtain ⟨x, hx⟩ := hy
  refine ⟨(A ^ c) x, ?_⟩
  have hx' : (A ^ (m + c)) x = y := hx
  have h : (A ^ (m + c)) x = (A ^ m) ((A ^ c) x) := by rw [pow_add]; rfl
  change (A ^ m) ((A ^ c) x) = y
  rw [← hx', h]

/-- If two consecutive null spaces of the powers of an operator agree, so do all later ones. -/
theorem ker_pow_succ_le_of_le (A : X →L[𝕜] X) {j : ℕ} (h : (A ^ (j + 1)).ker ≤ (A ^ j).ker)
    {i : ℕ} (hi : j ≤ i) : (A ^ (i + 1)).ker ≤ (A ^ i).ker := by
  induction i, hi using Nat.le_induction with
  | base => exact h
  | succ i _ ih =>
    intro x hx
    have hx' : (A ^ (i + 1 + 1)) x = 0 := hx
    have hAx : A x ∈ (A ^ (i + 1)).ker := by
      change (A ^ (i + 1)) (A x) = 0
      rw [← A.pow_succ_apply (i + 1) x]
      exact hx'
    have hxi : (A ^ i) (A x) = 0 := ih hAx
    change (A ^ (i + 1)) x = 0
    rw [A.pow_succ_apply i x, hxi]

/-- If two consecutive null spaces of the powers of an operator agree, the chain is constant
from there on. -/
theorem ker_pow_eq_of_ker_pow_succ_le (A : X →L[𝕜] X) {j : ℕ}
    (h : (A ^ (j + 1)).ker ≤ (A ^ j).ker) {i : ℕ} (hi : j ≤ i) : (A ^ i).ker = (A ^ j).ker := by
  induction i, hi using Nat.le_induction with
  | base => rfl
  | succ i hji ih =>
    exact le_antisymm ((A.ker_pow_succ_le_of_le h hji).trans ih.le) (A.ker_pow_mono (by omega))

/-- If two consecutive ranges of the powers of an operator agree, so do all later ones. -/
theorem range_pow_le_succ_of_le (A : X →L[𝕜] X) {j : ℕ} (h : (A ^ j).range ≤ (A ^ (j + 1)).range)
    {i : ℕ} (hi : j ≤ i) : (A ^ i).range ≤ (A ^ (i + 1)).range := by
  induction i, hi using Nat.le_induction with
  | base => exact h
  | succ i _ ih =>
    intro y hy
    obtain ⟨x, hx⟩ := hy
    have hx' : (A ^ (i + 1)) x = y := hx
    obtain ⟨z, hz⟩ := ih (⟨x, rfl⟩ : (A ^ i) x ∈ (A ^ i).range)
    have hz' : (A ^ (i + 1)) z = (A ^ i) x := hz
    refine ⟨z, ?_⟩
    change (A ^ (i + 1 + 1)) z = y
    have h1 : (A ^ (i + 1 + 1)) z = A ((A ^ (i + 1)) z) := A.pow_succ_apply' (i + 1) z
    rw [h1, hz', ← A.pow_succ_apply' i x, hx']

/-- If two consecutive ranges of the powers of an operator agree, the chain is constant from
there on. -/
theorem range_pow_eq_of_range_pow_succ_le (A : X →L[𝕜] X) {j : ℕ}
    (h : (A ^ j).range ≤ (A ^ (j + 1)).range) {i : ℕ} (hi : j ≤ i) :
    (A ^ i).range = (A ^ j).range := by
  induction i, hi using Nat.le_induction with
  | base => rfl
  | succ i hji ih =>
    exact le_antisymm (A.range_pow_anti (by omega))
      (ih.symm.trans_le (A.range_pow_le_succ_of_le h hji))

/-- If the null spaces of the powers of `A` have stabilized by the index `ν`, then `ker (A ^ ν)`
and `range (A ^ ν)` intersect trivially. -/
theorem disjoint_ker_range_pow (A : X →L[𝕜] X) {ν : ℕ}
    (h : (A ^ (ν + ν)).ker ≤ (A ^ ν).ker) : Disjoint (A ^ ν).ker (A ^ ν).range := by
  refine Submodule.disjoint_def.2 fun x hx1 hx2 => ?_
  obtain ⟨y, hy⟩ := hx2
  have hy' : (A ^ ν) y = x := hy
  have hx1' : (A ^ ν) x = 0 := hx1
  have hyk : y ∈ (A ^ (ν + ν)).ker := by
    change (A ^ (ν + ν)) y = 0
    have : (A ^ (ν + ν)) y = (A ^ ν) ((A ^ ν) y) := by rw [pow_add]; rfl
    rw [this, hy', hx1']
  have : (A ^ ν) y = 0 := h hyk
  rw [← hy', this]

/-- If the ranges of the powers of `A` have stabilized by the index `ν`, then `ker (A ^ ν)` and
`range (A ^ ν)` span the whole space. -/
theorem codisjoint_ker_range_pow (A : X →L[𝕜] X) {ν : ℕ}
    (h : (A ^ ν).range ≤ (A ^ (ν + ν)).range) : Codisjoint (A ^ ν).ker (A ^ ν).range := by
  refine codisjoint_iff.2 (eq_top_iff.2 fun x _ => ?_)
  obtain ⟨y, hy⟩ := h ⟨x, rfl⟩
  have hy' : (A ^ (ν + ν)) y = (A ^ ν) x := hy
  have hsplit : (A ^ ν) ((A ^ ν) y) = (A ^ ν) x := by
    rw [← hy', pow_add]; rfl
  refine Submodule.mem_sup.2 ⟨x - (A ^ ν) y, ?_, (A ^ ν) y, ⟨y, rfl⟩, by abel⟩
  change (A ^ ν) (x - (A ^ ν) y) = 0
  rw [map_sub, hsplit, sub_self]

end ContinuousLinearMap

namespace IsCompactOperator

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A power of `μ • 1 - K` is again a scalar minus a compact operator. -/
theorem exists_isCompactOperator_pow_eq {K : X →L[𝕜] X} (hK : IsCompactOperator K) (μ : 𝕜)
    (n : ℕ) : ∃ C : X →L[𝕜] X, IsCompactOperator C ∧
      (μ • (1 : X →L[𝕜] X) - K) ^ n = μ ^ n • (1 : X →L[𝕜] X) - C := by
  induction n with
  | zero => exact ⟨0, isCompactOperator_zero, by simp⟩
  | succ n ih =>
    obtain ⟨C, hC, hCeq⟩ := ih
    refine ⟨μ ^ n • K + μ • C - C * K, ((hK.smul (μ ^ n)).add (hC.smul μ)).sub (hC.comp_clm K), ?_⟩
    rw [pow_succ, hCeq]
    simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub,
      smul_smul, mul_comm μ (μ ^ n), ← pow_succ]
    abel

/-- `K` commutes with `μ • 1 - K`, hence with each of its powers. -/
theorem commute_pow (K : X →L[𝕜] X) (μ : 𝕜) (n : ℕ) :
    Commute ((μ • (1 : X →L[𝕜] X) - K) ^ n) K :=
  ((Commute.one_left K).smul_left μ).sub_left (Commute.refl K) |>.pow_left n

/-- On the kernel of `(μ • 1 - K) ^ n`, the compact operator `C` of
`IsCompactOperator.exists_isCompactOperator_pow_eq` acts as the scalar `μ ^ n`. -/
theorem apply_eq_of_mem_ker_pow {K C : X →L[𝕜] X} {μ : 𝕜} {n : ℕ}
    (hCeq : (μ • (1 : X →L[𝕜] X) - K) ^ n = μ ^ n • (1 : X →L[𝕜] X) - C)
    {v : X} (hv : v ∈ ((μ • (1 : X →L[𝕜] X) - K) ^ n).ker) : C v = μ ^ n • v := by
  have h : ((μ • (1 : X →L[𝕜] X) - K) ^ n) v = 0 := hv
  rw [hCeq] at h
  simp only [sub_apply, smul_apply, one_apply_eq_self, sub_eq_zero] at h
  exact h.symm

/-- **The kernel of a power of `μ • 1 - K` is finite-dimensional** for a compact `K` and `μ ≠ 0`:
on that kernel the compact operator `C` with `(μ • 1 - K) ^ n = μ ^ n • 1 - C` acts as the
invertible scalar `μ ^ n`, so the identity of the kernel is a compact operator. -/
theorem finiteDimensional_ker_pow [CompleteSpace 𝕜] {K : X →L[𝕜] X} (hK : IsCompactOperator K)
    {μ : 𝕜} (hμ : μ ≠ 0) (n : ℕ) :
    FiniteDimensional 𝕜 (((μ • (1 : X →L[𝕜] X) - K) ^ n).ker) := by
  obtain ⟨C, hC, hCeq⟩ := hK.exists_isCompactOperator_pow_eq μ n
  set N := ((μ • (1 : X →L[𝕜] X) - K) ^ n).ker with hNdef
  have hCv : ∀ v ∈ N, C v = μ ^ n • v := fun v hv => apply_eq_of_mem_ker_pow hCeq hv
  have hmaps : ∀ v ∈ N, (C : X →ₗ[𝕜] X) v ∈ N := by
    intro v hv
    have : (C : X →ₗ[𝕜] X) v = μ ^ n • v := hCv v hv
    rw [this]
    exact N.smul_mem _ hv
  have hclosed : IsClosed (N : Set X) := ((μ • (1 : X →L[𝕜] X) - K) ^ n).isClosed_ker
  have hrestrict : IsCompactOperator ((C : X →ₗ[𝕜] X).restrict hmaps) := hC.restrict hmaps hclosed
  have heq : (C : X →ₗ[𝕜] X).restrict hmaps = μ ^ n • (LinearMap.id : N →ₗ[𝕜] N) := by
    ext v
    exact hCv v.1 v.2
  rw [heq] at hrestrict
  have hid : IsCompactOperator (id : N → N) := by
    have := (IsCompactOperator.smul_iff₀ (M₂ := N) (pow_ne_zero n hμ)
      (f := ((LinearMap.id : N →ₗ[𝕜] N) : N → N))).1 (by simpa using hrestrict)
    simpa using this
  exact FiniteDimensional.of_isCompactOperator_id hid

/-- **The Riesz chain argument.** Let `K` be compact and `μ ≠ 0`. Suppose `S' n` is a closed
subspace of `S n`, that `μ • 1 - K` maps `S n` into `S' n`, and that for any two distinct indices
`K` maps one of the two larger spaces into the other's smaller one. Then the inclusion
`S' n ≤ S n` is an equality for some `n`.

If it never were, Riesz's lemma would give `wₙ ∈ S n` of bounded norm at distance at least `1`
from `S' n`, and then `‖K wₙ - K wₘ‖ ≥ ‖μ‖` for `m ≠ n`, which no sequence in a compact set can
satisfy. This is the one argument behind both the finiteness of the ascent and the finiteness of
the descent of `μ • 1 - K`. -/
theorem exists_le_of_chain {K : X →L[𝕜] X} (hK : IsCompactOperator K) {μ : 𝕜} (hμ : μ ≠ 0)
    (S S' : ℕ → Submodule 𝕜 X) (hclosed : ∀ n, IsClosed (S' n : Set X))
    (hle : ∀ n, S' n ≤ S n)
    (hstep : ∀ n, ∀ z ∈ S n, (μ • (1 : X →L[𝕜] X) - K) z ∈ S' n)
    (hcross : ∀ m n, m ≠ n → (∀ z ∈ S m, K z ∈ S' n) ∨ (∀ z ∈ S n, K z ∈ S' m)) :
    ∃ n, S n ≤ S' n := by
  by_contra hcon
  rw [not_exists] at hcon
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hR : ‖c‖ < ‖c‖ + 1 := by linarith
  have hriesz : ∀ n, ∃ w : X, w ∈ S n ∧ ‖w‖ ≤ ‖c‖ + 1 ∧ ∀ z ∈ S' n, 1 ≤ ‖w - z‖ := by
    intro n
    have h₁ : IsClosed ((↑((S' n).comap (S n).subtype) : Set ↥(S n))) := by
      simpa using! (hclosed n).preimage_val
    have h₂ : ∃ z : ↥(S n), z ∉ (S' n).comap (S n).subtype := by
      obtain ⟨x, hx1, hx2⟩ := SetLike.not_le_iff_exists.1 (hcon n)
      exact ⟨⟨x, hx1⟩, by simpa using hx2⟩
    obtain ⟨w, hwnorm, hwsep⟩ := riesz_lemma_of_norm_lt hc hR h₁ h₂
    exact ⟨(w : X), w.2, hwnorm,
      fun z hz => by simpa using hwsep ⟨z, hle n hz⟩ (by simpa using hz)⟩
  choose w hwmem hwnorm hwsep using hriesz
  have hkey : ∀ m n : ℕ, (∀ z ∈ S m, K z ∈ S' n) → ‖μ‖ ≤ ‖K (w n) - K (w m)‖ := by
    intro m n hmn
    have ht : (μ • (1 : X →L[𝕜] X) - K) (w n) + K (w m) ∈ S' n :=
      Submodule.add_mem _ (hstep n _ (hwmem n)) (hmn _ (hwmem m))
    have heq : K (w n) - K (w m)
        = μ • (w n - μ⁻¹ • ((μ • (1 : X →L[𝕜] X) - K) (w n) + K (w m))) := by
      rw [smul_sub, smul_inv_smul₀ hμ]
      simp only [sub_apply, smul_apply, one_apply_eq_self]
      abel
    rw [heq, norm_smul]
    calc ‖μ‖ = ‖μ‖ * 1 := (mul_one _).symm
      _ ≤ ‖μ‖ * ‖w n - μ⁻¹ • ((μ • (1 : X →L[𝕜] X) - K) (w n) + K (w m))‖ := by
          gcongr
          exact hwsep n _ (Submodule.smul_mem _ _ ht)
  have hsep : ∀ m n : ℕ, m ≠ n → ‖μ‖ ≤ ‖K (w m) - K (w n)‖ := by
    intro m n hne
    rcases hcross m n hne with h | h
    · rw [norm_sub_rev]; exact hkey m n h
    · exact hkey n m h
  obtain ⟨Kc, hKc, hKcsub⟩ := hK.image_closedBall_subset_compact (‖c‖ + 1)
  obtain ⟨y, -, φ, hφ, hφy⟩ := hKc.tendsto_subseq (x := fun n => K (w n))
    fun n => hKcsub ⟨w n, mem_closedBall_zero_iff.2 (hwnorm n), rfl⟩
  have hcauchy := hφy.cauchySeq
  rw [Metric.cauchySeq_iff'] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy ‖μ‖ (norm_pos_iff.2 hμ)
  have hlt := hN (N + 1) (Nat.le_succ N)
  rw [Function.comp_apply, Function.comp_apply, dist_eq_norm] at hlt
  exact absurd hlt (not_lt.2 (hsep (φ (N + 1)) (φ N)
    fun h => absurd (hφ.injective h) (by omega)))

/-- `K` commutes with the powers of `μ • 1 - K`, pointwise. -/
theorem pow_apply_comm (K : X →L[𝕜] X) (μ : 𝕜) (n : ℕ) (z : X) :
    ((μ • (1 : X →L[𝕜] X) - K) ^ n) (K z) = K (((μ • (1 : X →L[𝕜] X) - K) ^ n) z) :=
  congrArg (fun T : X →L[𝕜] X => T z) (commute_pow K μ n)

/-- The null space of a power of `μ • 1 - K` is invariant under `K`. -/
theorem mapsTo_ker_pow (K : X →L[𝕜] X) (μ : 𝕜) (n : ℕ) {z : X}
    (hz : z ∈ ((μ • (1 : X →L[𝕜] X) - K) ^ n).ker) :
    K z ∈ ((μ • (1 : X →L[𝕜] X) - K) ^ n).ker := by
  have hz' : ((μ • (1 : X →L[𝕜] X) - K) ^ n) z = 0 := hz
  change ((μ • (1 : X →L[𝕜] X) - K) ^ n) (K z) = 0
  rw [pow_apply_comm, hz', map_zero]

/-- The range of a power of `μ • 1 - K` is invariant under `K`. -/
theorem mapsTo_range_pow (K : X →L[𝕜] X) (μ : 𝕜) (n : ℕ) {z : X}
    (hz : z ∈ ((μ • (1 : X →L[𝕜] X) - K) ^ n).range) :
    K z ∈ ((μ • (1 : X →L[𝕜] X) - K) ^ n).range := by
  obtain ⟨y, hy⟩ := hz
  have hy' : ((μ • (1 : X →L[𝕜] X) - K) ^ n) y = z := hy
  refine ⟨K y, ?_⟩
  change ((μ • (1 : X →L[𝕜] X) - K) ^ n) (K y) = K z
  rw [pow_apply_comm, hy']

/-- The range of a power of `μ • 1 - K` is closed, for a compact `K` and `μ ≠ 0`. -/
theorem isClosed_range_pow {K : X →L[𝕜] X} (hK : IsCompactOperator K) {μ : 𝕜} (hμ : μ ≠ 0)
    (n : ℕ) : IsClosed ((((μ • (1 : X →L[𝕜] X) - K) ^ n).range : Submodule 𝕜 X) : Set X) := by
  obtain ⟨C, hC, hCeq⟩ := hK.exists_isCompactOperator_pow_eq μ n
  rw [hCeq]
  exact hC.isClosed_range_smul_sub (pow_ne_zero n hμ)

/-- **The ascent of `μ • 1 - K` is finite** for a compact `K` and `μ ≠ 0`: the chain of null
spaces of the powers stops growing. -/
theorem exists_ker_pow_succ_le {K : X →L[𝕜] X} (hK : IsCompactOperator K) {μ : 𝕜} (hμ : μ ≠ 0) :
    ∃ n, ((μ • (1 : X →L[𝕜] X) - K) ^ (n + 1)).ker ≤ ((μ • (1 : X →L[𝕜] X) - K) ^ n).ker := by
  refine hK.exists_le_of_chain hμ (fun n => ((μ • (1 : X →L[𝕜] X) - K) ^ (n + 1)).ker)
    (fun n => ((μ • (1 : X →L[𝕜] X) - K) ^ n).ker)
    (fun n => ContinuousLinearMap.isClosed_ker _)
    (fun n => ContinuousLinearMap.ker_pow_mono _ (Nat.le_succ n)) (fun n z hz => ?_)
    (fun m n hmn => ?_)
  · have hz' : ((μ • (1 : X →L[𝕜] X) - K) ^ (n + 1)) z = 0 := hz
    change ((μ • (1 : X →L[𝕜] X) - K) ^ n) ((μ • (1 : X →L[𝕜] X) - K) z) = 0
    rw [← ContinuousLinearMap.pow_succ_apply, hz']
  · rcases lt_or_gt_of_ne hmn with h | h
    · exact Or.inl fun z hz => ContinuousLinearMap.ker_pow_mono _ h (mapsTo_ker_pow K μ (m + 1) hz)
    · exact Or.inr fun z hz => ContinuousLinearMap.ker_pow_mono _ h (mapsTo_ker_pow K μ (n + 1) hz)

/-- **The descent of `μ • 1 - K` is finite** for a compact `K` and `μ ≠ 0`: the chain of ranges of
the powers stops shrinking. -/
theorem exists_range_pow_le_succ {K : X →L[𝕜] X} (hK : IsCompactOperator K) {μ : 𝕜} (hμ : μ ≠ 0) :
    ∃ n, ((μ • (1 : X →L[𝕜] X) - K) ^ n).range
      ≤ ((μ • (1 : X →L[𝕜] X) - K) ^ (n + 1)).range := by
  refine hK.exists_le_of_chain hμ (fun n => ((μ • (1 : X →L[𝕜] X) - K) ^ n).range)
    (fun n => ((μ • (1 : X →L[𝕜] X) - K) ^ (n + 1)).range)
    (fun n => hK.isClosed_range_pow hμ (n + 1))
    (fun n => ContinuousLinearMap.range_pow_anti _ (Nat.le_succ n)) (fun n z hz => ?_)
    (fun m n hmn => ?_)
  · obtain ⟨y, hy⟩ := hz
    have hy' : ((μ • (1 : X →L[𝕜] X) - K) ^ n) y = z := hy
    refine ⟨y, ?_⟩
    change ((μ • (1 : X →L[𝕜] X) - K) ^ (n + 1)) y = (μ • (1 : X →L[𝕜] X) - K) z
    rw [ContinuousLinearMap.pow_succ_apply', hy']
  · rcases lt_or_gt_of_ne hmn with h | h
    · exact Or.inr fun z hz =>
        ContinuousLinearMap.range_pow_anti _ h (mapsTo_range_pow K μ n hz)
    · exact Or.inl fun z hz =>
        ContinuousLinearMap.range_pow_anti _ h (mapsTo_range_pow K μ m hz)

/-- **The Riesz index of a nonzero `μ` for a compact `K`.** There is a least `ν` at which the
chain of null spaces of the powers of `μ • 1 - K` stops growing; before `ν` the chain increases
strictly, from `ν` on it is constant, the chain of ranges is constant from `ν` on as well, and the
space is the direct sum of `ker ((μ • 1 - K) ^ ν)` and `range ((μ • 1 - K) ^ ν)`.
This is [han2009theoretical], Theorem 2.8.12 clauses (3) and (5).

Both chains are finite by `IsCompactOperator.exists_le_of_chain`. The decomposition holds first at
`max ν q` with `q` an index where the ranges have stabilized, and that decomposition is what shows
the ranges have in fact stabilized already at `ν`: an element of `range ((μ • 1 - K) ^ ν)` is
`(μ • 1 - K) ^ ν` applied to a vector whose null-space part is killed, and whose range part is in
`range ((μ • 1 - K) ^ (max ν q + 1))`. -/
theorem exists_riesz_index {K : X →L[𝕜] X} (hK : IsCompactOperator K) {μ : 𝕜} (hμ : μ ≠ 0) :
    ∃ ν : ℕ,
      (∀ j < ν, ((μ • (1 : X →L[𝕜] X) - K) ^ j).ker
        < ((μ • (1 : X →L[𝕜] X) - K) ^ (j + 1)).ker) ∧
      (∀ j, ν ≤ j → ((μ • (1 : X →L[𝕜] X) - K) ^ j).ker
        = ((μ • (1 : X →L[𝕜] X) - K) ^ ν).ker) ∧
      (∀ j, ν ≤ j → ((μ • (1 : X →L[𝕜] X) - K) ^ j).range
        = ((μ • (1 : X →L[𝕜] X) - K) ^ ν).range) ∧
      IsCompl (((μ • (1 : X →L[𝕜] X) - K) ^ ν).ker)
        (((μ • (1 : X →L[𝕜] X) - K) ^ ν).range) := by
  classical
  obtain ⟨p, hp⟩ := hK.exists_ker_pow_succ_le hμ
  obtain ⟨q, hq⟩ := hK.exists_range_pow_le_succ hμ
  have hexP : ∃ n, ((μ • (1 : X →L[𝕜] X) - K) ^ (n + 1)).ker
      ≤ ((μ • (1 : X →L[𝕜] X) - K) ^ n).ker := ⟨p, hp⟩
  set A : X →L[𝕜] X := μ • (1 : X →L[𝕜] X) - K with hAdef
  set ν := Nat.find hexP with hνdef
  have hνspec : (A ^ (ν + 1)).ker ≤ (A ^ ν).ker := Nat.find_spec hexP
  have hkerstab : ∀ j, ν ≤ j → (A ^ j).ker = (A ^ ν).ker :=
    fun j hj => A.ker_pow_eq_of_ker_pow_succ_le hνspec hj
  have hrangestabq : ∀ j, q ≤ j → (A ^ j).range = (A ^ q).range :=
    fun j hj => A.range_pow_eq_of_range_pow_succ_le hq hj
  set m := max ν q with hmdef
  have hνm : ν ≤ m := le_max_left _ _
  have hqm : q ≤ m := le_max_right _ _
  have hcomplm : IsCompl (A ^ m).ker (A ^ m).range := by
    refine ⟨A.disjoint_ker_range_pow ?_, A.codisjoint_ker_range_pow ?_⟩
    · exact ((hkerstab (m + m) (by omega)).trans (hkerstab m hνm).symm).le
    · exact ((hrangestabq m hqm).trans (hrangestabq (m + m) (by omega)).symm).le
  have hrangeν : (A ^ ν).range ≤ (A ^ (ν + 1)).range := by
    intro x hx
    obtain ⟨y, hy⟩ := hx
    have hy' : (A ^ ν) y = x := hy
    have hytop : y ∈ (A ^ m).ker ⊔ (A ^ m).range := by
      rw [hcomplm.sup_eq_top]; trivial
    obtain ⟨u, hu, r, hr, hur⟩ := Submodule.mem_sup.1 hytop
    have hu0 : (A ^ ν) u = 0 := by
      have humem : u ∈ (A ^ ν).ker := (hkerstab m hνm) ▸ hu
      exact humem
    have hrmem : r ∈ (A ^ (m + 1)).range := by
      rw [hrangestabq (m + 1) (by omega), ← hrangestabq m hqm]
      exact hr
    obtain ⟨s, hs⟩ := hrmem
    have hs' : (A ^ (m + 1)) s = r := hs
    refine ⟨(A ^ m) s, ?_⟩
    have hAr : A ((A ^ m) s) = r := by rw [← A.pow_succ_apply' m s]; exact hs'
    change (A ^ (ν + 1)) ((A ^ m) s) = x
    rw [A.pow_succ_apply ν ((A ^ m) s), hAr, ← hy', ← hur, map_add, hu0, zero_add]
  have hrangestabν : ∀ j, ν ≤ j → (A ^ j).range = (A ^ ν).range :=
    fun j hj => A.range_pow_eq_of_range_pow_succ_le hrangeν hj
  have hcomplν : IsCompl (A ^ ν).ker (A ^ ν).range := by
    rw [← hkerstab m hνm, ← hrangestabν m hνm]
    exact hcomplm
  exact ⟨ν, fun j hj =>
    lt_of_le_not_ge (A.ker_pow_mono (Nat.le_succ j)) (Nat.find_min hexP hj),
    hkerstab, hrangestabν, hcomplν⟩

/-- `μ ^ m • 1 - K ^ m` factors through `μ • 1 - K`, with a cofactor that commutes with `K`.
This is `a ^ m - b ^ m = (a - b) ∑ aⁱ bᵐ⁻¹⁻ⁱ` for the commuting `a = μ • 1` and `b = K`, written
as a recursion so that no geometric sum is needed. -/
theorem exists_factor_pow_smul_sub (K : X →L[𝕜] X) (μ : 𝕜) (m : ℕ) :
    ∃ S : X →L[𝕜] X, Commute S K ∧
      μ ^ m • (1 : X →L[𝕜] X) - K ^ m = (μ • (1 : X →L[𝕜] X) - K) * S := by
  induction m with
  | zero => exact ⟨0, Commute.zero_left K, by simp⟩
  | succ m ih =>
    obtain ⟨S, hSc, hS⟩ := ih
    refine ⟨μ • S + K ^ m, (hSc.smul_left μ).add_left ((Commute.refl K).pow_left m), ?_⟩
    have hexpand : (μ • (1 : X →L[𝕜] X) - K) * (μ • S + K ^ m)
        = μ • ((μ • (1 : X →L[𝕜] X) - K) * S) + (μ • K ^ m - K ^ (m + 1)) := by
      rw [mul_add, mul_smul_comm]
      congr 1
      rw [sub_mul, smul_mul_assoc, one_mul, ← pow_succ']
    rw [hexpand, ← hS, smul_sub, smul_smul, ← pow_succ']
    abel

variable [CompleteSpace 𝕜]

/-- **The Fredholm alternative for an operator with a compact power.** If some power `K ^ m` of
a bounded operator on a Banach space is compact and `μ ≠ 0`, then `μ • 1 - K` is invertible as
soon as it is injective — the Fredholm alternative survives with only a power of the operator
compact.

The Riesz decomposition `X = ker (B ^ ν) ⊕ range (B ^ ν)` for the compact perturbation
`B = μ ^ m • 1 - K ^ m` does it: `μ • 1 - K` commutes with `B`, so it preserves both summands; on
the finite-dimensional first summand injectivity gives surjectivity, and on the second `B` is onto
and factors as `(μ • 1 - K) * S` with `S` preserving that summand.
This is [han2009theoretical], Theorem 2.8.12 (6). -/
theorem isUnit_smul_one_sub_of_isCompactOperator_pow [CompleteSpace X] {K : X →L[𝕜] X} {m : ℕ}
    (hK : IsCompactOperator (K ^ m)) {μ : 𝕜} (hμ : μ ≠ 0)
    (hinj : ∀ u : X, (μ • (1 : X →L[𝕜] X) - K) u = 0 → u = 0) :
    IsUnit (μ • (1 : X →L[𝕜] X) - K) := by
  obtain ⟨S, hSc, hS⟩ := exists_factor_pow_smul_sub K μ m
  obtain ⟨ν, -, -, hrange, hcompl⟩ := hK.exists_riesz_index (pow_ne_zero m hμ)
  set A : X →L[𝕜] X := μ • (1 : X →L[𝕜] X) - K with hAdef
  set B : X →L[𝕜] X := μ ^ m • (1 : X →L[𝕜] X) - K ^ m with hBdef
  have hAinj : Function.Injective A := fun a b hab =>
    sub_eq_zero.1 (hinj (a - b) (by rw [map_sub, hab, sub_self]))
  have hcommAB : Commute A B :=
    (((Commute.one_left B).smul_left μ).sub_left
      (((Commute.one_right K).smul_right (μ ^ m)).sub_right ((Commute.refl K).pow_right m)))
  have hcommSB : Commute S B :=
    ((Commute.one_right S).smul_right (μ ^ m)).sub_right (hSc.pow_right m)
  have hApow : ∀ x : X, (B ^ ν) (A x) = A ((B ^ ν) x) := fun x =>
    congrArg (fun T : X →L[𝕜] X => T x) (hcommAB.pow_right ν).symm
  have hSpow : ∀ x : X, (B ^ ν) (S x) = S ((B ^ ν) x) := fun x =>
    congrArg (fun T : X →L[𝕜] X => T x) (hcommSB.pow_right ν).symm
  -- the null-space summand
  have hNmaps : ∀ v ∈ (B ^ ν).ker, (A : X →ₗ[𝕜] X) v ∈ (B ^ ν).ker := by
    intro v hv
    have hv' : (B ^ ν) v = 0 := hv
    change (B ^ ν) (A v) = 0
    rw [hApow, hv', map_zero]
  have hNfd : FiniteDimensional 𝕜 (B ^ ν).ker := hK.finiteDimensional_ker_pow (pow_ne_zero m hμ) ν
  have hNsurj : ∀ u ∈ (B ^ ν).ker, ∃ v ∈ (B ^ ν).ker, A v = u := by
    have hinj' : Function.Injective ((A : X →ₗ[𝕜] X).restrict hNmaps) := fun a b hab =>
      Subtype.ext (hAinj (congrArg Subtype.val hab))
    intro u hu
    obtain ⟨v, hv⟩ := LinearMap.injective_iff_surjective.1 hinj' ⟨u, hu⟩
    exact ⟨v.1, v.2, congrArg Subtype.val hv⟩
  -- the range summand
  have hRsurj : ∀ y ∈ (B ^ ν).range, ∃ v ∈ (B ^ ν).range, A v = y := by
    intro y hy
    have hy' : y ∈ (B ^ (ν + 1)).range := by rw [hrange (ν + 1) (Nat.le_succ ν)]; exact hy
    obtain ⟨z, hz⟩ := hy'
    have hz' : (B ^ (ν + 1)) z = y := hz
    refine ⟨S ((B ^ ν) z), ⟨S z, ?_⟩, ?_⟩
    · change (B ^ ν) (S z) = S ((B ^ ν) z)
      exact hSpow z
    · have hBz : B ((B ^ ν) z) = y := by rw [← ContinuousLinearMap.pow_succ_apply' B ν z]; exact hz'
      have hfac : B ((B ^ ν) z) = A (S ((B ^ ν) z)) :=
        congrArg (fun T : X →L[𝕜] X => T ((B ^ ν) z)) hS
      rw [← hfac, hBz]
  -- surjectivity, hence bijectivity
  have hAsurj : Function.Surjective A := by
    intro x
    have hxtop : x ∈ (B ^ ν).ker ⊔ (B ^ ν).range := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨u, hu, r, hr, hur⟩ := Submodule.mem_sup.1 hxtop
    obtain ⟨u', -, hu'⟩ := hNsurj u hu
    obtain ⟨r', -, hr'⟩ := hRsurj r hr
    exact ⟨u' + r', by rw [map_add, hu', hr', hur]⟩
  exact ContinuousLinearMap.isUnit_iff_bijective.2 ⟨hAinj, hAsurj⟩

/-- **The Fredholm alternative for an operator with a compact power**, in the form of Mathlib's
`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`: if some power of `K` is compact and
`μ ≠ 0`, then `μ` is either an eigenvalue of `K` or in its resolvent set.
This is [han2009theoretical], Theorem 2.8.12 (6). -/
theorem hasEigenvalue_or_mem_resolventSet_of_isCompactOperator_pow [CompleteSpace X]
    {K : X →L[𝕜] X} {m : ℕ} (hK : IsCompactOperator (K ^ m)) {μ : 𝕜} (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (K : Module.End 𝕜 X) μ ∨ μ ∈ resolventSet 𝕜 K := by
  by_cases hev : Module.End.HasEigenvalue (K : Module.End 𝕜 X) μ
  · exact Or.inl hev
  refine Or.inr ?_
  have hbot : Module.End.eigenspace (K : Module.End 𝕜 X) μ = ⊥ := not_not.1 hev
  have hinj : ∀ u : X, (μ • (1 : X →L[𝕜] X) - K) u = 0 → u = 0 := by
    intro u hu
    have humem : u ∈ Module.End.eigenspace (K : Module.End 𝕜 X) μ := by
      rw [Module.End.mem_eigenspace_iff]
      have hu' : μ • u - K u = 0 := by simpa using hu
      exact (sub_eq_zero.1 hu').symm
    simpa [hbot] using humem
  rw [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one]
  exact hK.isUnit_smul_one_sub_of_isCompactOperator_pow hμ hinj

/-! ### The Fredholm index of `μ • 1 - K` on a Hilbert space -/

section Hilbert

open Module

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [CompleteSpace X]

omit [CompleteSpace X] in
/-- If one finite-dimensional subspace has strictly smaller dimension than another, there is an
injective linear map of the first into the second whose range misses a vector of the second. -/
private theorem exists_injective_of_finrank_lt {N M : Submodule 𝕜 X}
    [FiniteDimensional 𝕜 N] [FiniteDimensional 𝕜 M] (h : finrank 𝕜 N < finrank 𝕜 M) :
    ∃ e : N →ₗ[𝕜] X, Function.Injective e ∧ (∀ v, e v ∈ M) ∧ ∃ w ∈ M, ∀ v, e v ≠ w := by
  classical
  set n := finrank 𝕜 N with hn
  set m := finrank 𝕜 M with hm
  set bN : Basis (Fin n) 𝕜 N := finBasis 𝕜 N with hbN
  set bM : Basis (Fin m) 𝕜 M := finBasis 𝕜 M with hbM
  set g : Fin n → Fin m := Fin.castLE h.le with hg
  have hginj : Function.Injective g := Fin.castLE_injective h.le
  set e₀ : N →ₗ[𝕜] M :=
    (bM.repr.symm.toLinearMap).comp ((Finsupp.lmapDomain 𝕜 𝕜 g).comp bN.repr.toLinearMap) with he₀
  have hrepr : ∀ v : N, bM.repr (e₀ v) = Finsupp.mapDomain g (bN.repr v) := by
    intro v
    have hv : e₀ v = bM.repr.symm (Finsupp.lmapDomain 𝕜 𝕜 g (bN.repr v)) := rfl
    rw [hv, LinearEquiv.apply_symm_apply, Finsupp.lmapDomain_apply]
  have he₀inj : Function.Injective e₀ := by
    intro a b hab
    refine bN.repr.injective (Finsupp.mapDomain_injective hginj ?_)
    rw [← hrepr a, ← hrepr b, hab]
  have hnot : (⟨n, h⟩ : Fin m) ∉ Set.range g := by
    rintro ⟨i, hi⟩
    have : (i : ℕ) = n := congrArg Fin.val hi
    omega
  refine ⟨M.subtype.comp e₀, fun a b hab => he₀inj (Subtype.ext hab), fun v => (e₀ v).2,
    ⟨(bM ⟨n, h⟩ : X), (bM ⟨n, h⟩).2, fun v hv => ?_⟩⟩
  have heq : e₀ v = bM ⟨n, h⟩ := Subtype.ext hv
  have h1 : Finsupp.mapDomain g (bN.repr v) = Finsupp.single (⟨n, h⟩ : Fin m) 1 := by
    rw [← hrepr v, heq, bM.repr_self]
  have h2 : Finsupp.mapDomain g (bN.repr v) (⟨n, h⟩ : Fin m) = 0 :=
    Finsupp.mapDomain_of_notMem_range _ _ hnot
  rw [h1] at h2
  simp at h2

/-- **One half of the Fredholm index-zero statement**: on a Hilbert space, the null space of
`conj μ • 1 - K†` is no larger than that of `μ • 1 - K`.

If it were larger, an injective map `e` of `ker (μ • 1 - K)` into `ker (conj μ • 1 - K†)` with
proper range, composed with the orthogonal projection onto `ker (μ • 1 - K)`, would be a finite-rank
`F` for which `μ • 1 - (K - F)` is injective — its kernel would have to lie in
`range (μ • 1 - K) ⊓ ker (conj μ • 1 - K†) = ⊥` — hence bijective by the Fredholm alternative,
while its range misses every vector of `ker (conj μ • 1 - K†)` outside `range e`. -/
theorem finrank_ker_adjoint_le {K : X →L[𝕜] X} (hK : IsCompactOperator K) {μ : 𝕜} (hμ : μ ≠ 0) :
    finrank 𝕜 (((starRingEnd 𝕜) μ • (1 : X →L[𝕜] X) - ContinuousLinearMap.adjoint K).ker)
      ≤ finrank 𝕜 ((μ • (1 : X →L[𝕜] X) - K).ker) := by
  by_contra hlt
  rw [not_le] at hlt
  have hμ' : (starRingEnd 𝕜) μ ≠ 0 := by simpa using hμ
  set N := (μ • (1 : X →L[𝕜] X) - K).ker with hN
  set M := ((starRingEnd 𝕜) μ • (1 : X →L[𝕜] X) - ContinuousLinearMap.adjoint K).ker with hM
  have hNfd : FiniteDimensional 𝕜 N := by
    have h := hK.finiteDimensional_ker_pow hμ 1
    rwa [pow_one] at h
  have hMfd : FiniteDimensional 𝕜 M := by
    have h := hK.adjoint.finiteDimensional_ker_pow hμ' 1
    rwa [pow_one] at h
  have hrange : (μ • (1 : X →L[𝕜] X) - K).range = Mᗮ :=
    hK.range_smul_sub_eq_orthogonal_ker_adjoint hμ
  obtain ⟨e, heinj, heM, w, hwM, hw⟩ := exists_injective_of_finrank_lt hlt
  set F : X →L[𝕜] X := (LinearMap.toContinuousLinearMap e).comp N.orthogonalProjectionOnto with hF
  have hFapply : ∀ x, F x = e (N.orthogonalProjectionOnto x) := fun _ => rfl
  have hFmem : ∀ x, F x ∈ M := by
    intro x
    rw [hFapply x]
    exact heM _
  have hFself : ∀ (x : X) (hx : x ∈ N), F x = e ⟨x, hx⟩ := by
    intro x hx
    have hproj : N.orthogonalProjectionOnto x = (⟨x, hx⟩ : N) :=
      Subtype.ext (Submodule.starProjection_eq_self_iff.2 hx)
    rw [hFapply x, hproj]
  have hFfd : FiniteDimensional 𝕜 (LinearMap.range (F : X →ₗ[𝕜] X)) := by
    have hle : LinearMap.range (F : X →ₗ[𝕜] X) ≤ M := by
      rintro _ ⟨x, rfl⟩
      exact hFmem x
    exact Submodule.finiteDimensional_of_le hle
  have hFcompact : IsCompactOperator F := IsCompactOperator.of_finiteDimensional_range F
  have hKF : IsCompactOperator (((K - F) ^ 1 : X →L[𝕜] X)) := by
    rw [pow_one]
    exact hK.sub hFcompact
  have hdisj : ∀ v : X, v ∈ M → v ∈ Mᗮ → v = 0 := fun v h1 h2 =>
    inner_self_eq_zero.1 (h2 v h1)
  have hsplit : ∀ x : X, (μ • (1 : X →L[𝕜] X) - (K - F)) x
      = (μ • (1 : X →L[𝕜] X) - K) x + F x := by
    intro x
    simp only [sub_apply, smul_apply, one_apply_eq_self]
    abel
  have hinj : ∀ u : X, (μ • (1 : X →L[𝕜] X) - (K - F)) u = 0 → u = 0 := by
    intro u hu
    rw [hsplit u] at hu
    have hAuM : (μ • (1 : X →L[𝕜] X) - K) u ∈ M := by
      have heq : (μ • (1 : X →L[𝕜] X) - K) u = -F u := by
        linear_combination (norm := module) hu
      rw [heq]
      exact M.neg_mem (hFmem u)
    have hAu : (μ • (1 : X →L[𝕜] X) - K) u ∈ Mᗮ := by
      rw [← hrange]
      exact ⟨u, rfl⟩
    have hA0 : (μ • (1 : X →L[𝕜] X) - K) u = 0 := hdisj _ hAuM hAu
    have huN : u ∈ N := hA0
    have hF0 : F u = 0 := by
      rw [hA0, zero_add] at hu
      exact hu
    rw [hFself u huN] at hF0
    have hz : (⟨u, huN⟩ : N) = 0 := heinj (by simpa using hF0)
    simpa using congrArg Subtype.val hz
  obtain ⟨x, hx⟩ :=
    (ContinuousLinearMap.isUnit_iff_bijective.1
      (hKF.isUnit_smul_one_sub_of_isCompactOperator_pow hμ hinj)).2 w
  rw [hsplit x] at hx
  have hAxM : (μ • (1 : X →L[𝕜] X) - K) x ∈ M := by
    have heq : (μ • (1 : X →L[𝕜] X) - K) x = w - F x := by
      linear_combination (norm := module) hx
    rw [heq]
    exact M.sub_mem hwM (hFmem x)
  have hAx : (μ • (1 : X →L[𝕜] X) - K) x ∈ Mᗮ := by
    rw [← hrange]
    exact ⟨x, rfl⟩
  have hA0 : (μ • (1 : X →L[𝕜] X) - K) x = 0 := hdisj _ hAxM hAx
  rw [hA0, zero_add] at hx
  exact hw (N.orthogonalProjectionOnto x) (by rw [← hFapply x]; exact hx)

/-- **The Fredholm index of `μ • 1 - K` is zero** for a compact `K` and `μ ≠ 0`: on a Hilbert
space the null spaces of `μ • 1 - K` and of `conj μ • 1 - K†` have the same dimension.
This is [han2009theoretical], Theorem 2.8.14 (1). -/
theorem finrank_ker_eq_finrank_ker_adjoint {K : X →L[𝕜] X} (hK : IsCompactOperator K) {μ : 𝕜}
    (hμ : μ ≠ 0) :
    finrank 𝕜 ((μ • (1 : X →L[𝕜] X) - K).ker)
      = finrank 𝕜 (((starRingEnd 𝕜) μ • (1 : X →L[𝕜] X) - ContinuousLinearMap.adjoint K).ker) := by
  refine le_antisymm ?_ (hK.finrank_ker_adjoint_le hμ)
  have hμ' : (starRingEnd 𝕜) μ ≠ 0 := by simpa using hμ
  have h := hK.adjoint.finrank_ker_adjoint_le hμ'
  rw [RingHomCompTriple.comp_apply, RingHom.id_apply,
    ContinuousLinearMap.adjoint_adjoint] at h
  exact h

end Hilbert

end IsCompactOperator
