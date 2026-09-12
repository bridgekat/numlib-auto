import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Semicontinuity.Basic
import Numlib.Analysis.InnerProductSpace.WeakCompactness
import Numlib.Analysis.Normed.Module.Reflexive
import Numlib.Analysis.Normed.Module.WeakDual
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Variational.Minimization

/-!
# Existence of minimizers by weak sequential compactness

The direct method of the calculus of variations: a functional that is lower semicontinuous *for the
weak topology* attains its infimum on a set that is bounded and closed *for the weak topology*.
Norm-closed bounded sets are almost never norm-compact in infinite dimensions, so the
finite-dimensional argument of `Numlib.Variational.Minimization` does not carry over; what replaces
compactness is the extraction of a weakly convergent subsequence from a bounded sequence.

## The standing hypothesis on the space

The classical hypothesis is that the space is a **reflexive** Banach space. What the argument uses
is not reflexivity itself but its sequential consequence, that every norm-bounded sequence has a
weakly convergent subsequence — the Eberlein–Šmulian and Kakutani theorems make the two equivalent
for a Banach space, and it is in this equivalent form that [han2009theoretical] state reflexivity
(their Thm 2.7.5) before using it. So the hypothesis is carried here by the class
`WeaklySeqCompactSpace`, which says exactly that, and the theorems below are the classical ones
with reflexivity replaced by its characterization.

Reflexivity itself is `NormedSpace.IsReflexive` of `Numlib.Analysis.Normed.Module.Reflexive`, and
`WeaklySeqCompactSpace.of_isReflexive` below derives this class from it, so the direct method
applies to **every reflexive real Banach space**: that instance is the easy half of the equivalence,
`NormedSpace.exists_subseq_forall_dual_tendsto`, read through `WeakSeqTendsto`. In particular every
Hilbert space is covered, by `NormedSpace.instIsReflexiveOfInnerProductSpace`, and that is where the
applications in this library live; `Lᵖ` for `1 < p < ∞` and every uniformly convex Banach space are
reflexive too, by theorems this library does not have. Mathlib has no reflexivity class of its own.

## Main definitions

* `WeakSeqTendsto u w` — weak sequential convergence `uₙ ⇀ w`, spelled out as `ℓ (uₙ) → ℓ w` for
  every bounded linear functional; `weakSeqTendsto_iff_tendsto_toWeakSpace` identifies it with
  convergence in Mathlib's `WeakSpace`.
* `WeaklySeqCompactSpace V` — every norm-bounded sequence in `V` has a weakly convergent
  subsequence.
* `IsWeakSeqClosed K` — `K` contains the weak limit of every weakly convergent sequence of its
  points.
* `WeakSeqLowerSemicontinuousOn f K` — `f` is lower semicontinuous along weakly convergent sequences
  of `K`, in the same `∀ y < f w, ∀ᶠ n, y < f (uₙ)` form as Mathlib's
  `LowerSemicontinuousWithinAt`.

## Main statements

* `WeaklySeqCompactSpace.of_isReflexive` — every reflexive real normed space satisfies the standing
  hypothesis, so every theorem below applies to it.
* `exists_seq_convexCombination_tendsto` — **Mazur's lemma**: from a weakly convergent sequence one
  can form convex combinations of its tails that converge in norm.
* `Convex.isWeakSeqClosed`, `ConvexOn.weakSeqLowerSemicontinuousOn` — the two corollaries of Mazur's
  lemma that make convexity a substitute for weak hypotheses: a closed convex set is weakly
  sequentially closed, and a lower semicontinuous convex functional is weakly sequentially lower
  semicontinuous.
* `exists_isMinOn_of_isWeakSeqClosed` — the direct method on a bounded set.
* `exists_isMinOn_of_isCoerciveFunctionalOn` — the same for an unbounded set and a coercive
  functional.
* `exists_isMinOn_of_convexOn` — the convex form, whose hypotheses are on the norm topology alone.
* `exists_isBestApprox_of_convex` — every point has a best approximation from a nonempty closed
  convex set.

## References

[han2009theoretical], §3.3: Theorems 3.3.8, 3.3.10, 3.3.11, 3.3.12 and 3.3.14.
-/

open Bornology Filter Topology

section Defs

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Weak sequential convergence** `uₙ ⇀ w`: `ℓ (uₙ) → ℓ w` for every bounded linear functional
`ℓ`.

Mathlib carries the weak *topology* as `WeakSpace ℝ V`, and `weakSeqTendsto_iff_tendsto_toWeakSpace`
says the two agree; the pointwise form is the one in which the hypotheses of the direct method are
stated and verified. -/
def WeakSeqTendsto (u : ℕ → V) (w : V) : Prop :=
  ∀ ℓ : StrongDual ℝ V, Tendsto (fun n => ℓ (u n)) atTop (𝓝 (ℓ w))

/-- Weak sequential convergence is convergence in Mathlib's `WeakSpace` topology. -/
theorem weakSeqTendsto_iff_tendsto_toWeakSpace {u : ℕ → V} {w : V} :
    WeakSeqTendsto u w ↔
      Tendsto (fun n => toWeakSpace ℝ V (u n)) atTop (𝓝 (toWeakSpace ℝ V w)) :=
  tendsto_toWeakSpace_iff.symm

/-- A subsequence of a weakly convergent sequence converges weakly to the same limit. -/
theorem WeakSeqTendsto.comp {u : ℕ → V} {w : V} (h : WeakSeqTendsto u w) {σ : ℕ → ℕ}
    (hσ : StrictMono σ) : WeakSeqTendsto (u ∘ σ) w :=
  fun ℓ => (h ℓ).comp hσ.tendsto_atTop

/-- A norm-convergent sequence converges weakly to the same limit. -/
theorem WeakSeqTendsto.of_tendsto {u : ℕ → V} {w : V} (h : Tendsto u atTop (𝓝 w)) :
    WeakSeqTendsto u w :=
  fun ℓ => (ℓ.continuous.tendsto w).comp h

/-- **Bounded sequences have weakly convergent subsequences.** This is the property that the direct
method of the calculus of variations needs of the underlying space, and, for a Banach space, it is
equivalent to reflexivity by the theorems of Eberlein–Šmulian and Kakutani; it is the form in which
[han2009theoretical] Thm 2.7.5 states reflexivity.

The class is the hypothesis of the theorems below rather than reflexivity itself because it is what
their proofs use, and because only the easy half of the equivalence is available here; every
reflexive space is an instance, by `WeaklySeqCompactSpace.of_isReflexive`. -/
class WeaklySeqCompactSpace (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] : Prop where
  /-- Every norm-bounded sequence has a weakly convergent subsequence. -/
  exists_subseq_weakSeqTendsto : ∀ (u : ℕ → V) (C : ℝ), (∀ n, ‖u n‖ ≤ C) →
    ∃ (σ : ℕ → ℕ) (w : V), StrictMono σ ∧ WeakSeqTendsto (u ∘ σ) w

/-- A set is **weakly sequentially closed** when it contains the weak limit of every weakly
convergent sequence of its points. It is the hypothesis on the constraint set in the direct method;
`Convex.isWeakSeqClosed` is the source of examples. -/
def IsWeakSeqClosed (K : Set V) : Prop :=
  ∀ (u : ℕ → V) (w : V), (∀ n, u n ∈ K) → WeakSeqTendsto u w → w ∈ K

/-- A functional is **weakly sequentially lower semicontinuous on a set** when it is lower
semicontinuous along the weakly convergent sequences of that set, in the same form as Mathlib's
`LowerSemicontinuousWithinAt`: no value strictly below `f w` bounds `f (uₙ)` from above eventually.

Stated this way rather than as `f w ≤ liminf f (uₙ)` because a real `liminf` is junk when the
sequence is unbounded below, which is exactly the case the existence proof must rule out. -/
def WeakSeqLowerSemicontinuousOn (f : V → ℝ) (K : Set V) : Prop :=
  ∀ (u : ℕ → V) (w : V), (∀ n, u n ∈ K) → w ∈ K → WeakSeqTendsto u w →
    ∀ y < f w, ∀ᶠ n in atTop, y < f (u n)

/-- Weak sequential lower semicontinuity is inherited by subsets. -/
theorem WeakSeqLowerSemicontinuousOn.mono {f : V → ℝ} {K K' : Set V}
    (h : WeakSeqLowerSemicontinuousOn f K) (hKK : K' ⊆ K) :
    WeakSeqLowerSemicontinuousOn f K' :=
  fun u w hu hw => h u w (fun n => hKK (hu n)) (hKK hw)

end Defs

/-! ### Reflexive spaces are weakly sequentially compact -/

/-- **Every reflexive real normed space is weakly sequentially compact on bounded sets.** This is
the easy half of the classical equivalence, `NormedSpace.exists_subseq_forall_dual_tendsto`, whose
conclusion is `WeakSeqTendsto` with the quantifier over the dual moved outside; the converse, that
weak sequential compactness forces reflexivity, is Kakutani's theorem and is not available here.

Through `NormedSpace.instIsReflexiveOfInnerProductSpace` this covers every Hilbert space, so it
subsumes the direct route through the Riesz representation and `exists_subseq_weak_tendsto`. It is
the only instance of the class, so its priority is the default one; it is stated for `ℝ` because
`WeakSeqTendsto` is, the direct method being an argument about real-valued functionals. -/
instance WeaklySeqCompactSpace.of_isReflexive {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedSpace.IsReflexive ℝ V] : WeaklySeqCompactSpace V where
  exists_subseq_weakSeqTendsto u C hC := by
    obtain ⟨w, σ, hσ, h⟩ := NormedSpace.exists_subseq_forall_dual_tendsto (𝕜 := ℝ) hC
    exact ⟨σ, w, hσ, h⟩

/-! ### Mazur's lemma -/

section Mazur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Mazur's lemma**, one tail at a time: if `vₙ ⇀ u` then, for every `n` and every `ε > 0`, some
convex combination of `vₙ, …, v_N` lies within `ε` of `u` in norm.

The tail `{vᵢ : i ≥ n}` still converges weakly to `u`, so `u` lies in the closed convex hull of the
tail (`mem_of_weak_tendsto_of_convex`), and a point of a convex hull is a finite convex combination
of points of the set. -/
theorem exists_convexCombination_norm_sub_lt {v : ℕ → E} {u : E} (h : WeakSeqTendsto v u) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (lam : ℕ → ℝ), n ≤ N ∧ (∀ i, 0 ≤ lam i) ∧
      ∑ i ∈ Finset.Icc n N, lam i = 1 ∧ ‖(∑ i ∈ Finset.Icc n N, lam i • v i) - u‖ < ε := by
  classical
  -- `u` lies in the closed convex hull of the tail `{vᵢ : i ≥ n}`.
  set S : Set E := convexHull ℝ (v '' Set.Ici n) with hS
  have hmemS : ∀ k : ℕ, v (k + n) ∈ S :=
    fun k => subset_convexHull ℝ _ ⟨k + n, Set.mem_Ici.2 (Nat.le_add_left n k), rfl⟩
  have hucl : u ∈ closure S :=
    mem_of_weak_tendsto_of_convex (convex_convexHull ℝ _).closure isClosed_closure
      (fun k => subset_closure (hmemS k))
      (fun ℓ => (h ℓ).comp (tendsto_add_atTop_nat n))
  obtain ⟨b, hbS, hbu⟩ := Metric.mem_closure_iff.1 hucl ε hε
  -- A point of the convex hull is a finite convex combination of points of the tail.
  rw [hS, convexHull_eq] at hbS
  obtain ⟨ι, t, wt, z, hwt0, hwt1, hz, hcm⟩ := hbS
  choose! j hjn hjv using hz
  set T : Finset ℕ := t.image j with hT
  have hmaps : ∀ i ∈ t, j i ∈ T := fun i hi => Finset.mem_image_of_mem j hi
  set lam : ℕ → ℝ := fun k => ∑ i ∈ t with j i = k, wt i with hlam
  have hlam0 : ∀ k, 0 ≤ lam k :=
    fun k => Finset.sum_nonneg fun i hi => hwt0 i (Finset.mem_filter.1 hi).1
  have hsum1 : ∑ k ∈ T, lam k = 1 := by
    rw [hlam, Finset.sum_fiberwise_of_maps_to hmaps, hwt1]
  have hcomb : ∑ k ∈ T, lam k • v k = b := by
    have hstep : ∀ k ∈ T, lam k • v k = ∑ i ∈ t with j i = k, wt i • z i := by
      intro k _
      rw [hlam, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i hi => ?_
      obtain ⟨hit, hik⟩ := Finset.mem_filter.1 hi
      rw [← hik, hjv i hit]
    rw [Finset.sum_congr rfl hstep, Finset.sum_fiberwise_of_maps_to hmaps,
      ← Finset.centerMass_eq_of_sum_1 _ _ hwt1, hcm]
  -- Pad the combination out to the interval `Icc n N`.
  have hsub : T ⊆ Finset.Icc n (max n (T.sup id)) := by
    intro k hk
    obtain ⟨i, hit, rfl⟩ := Finset.mem_image.1 hk
    exact Finset.mem_Icc.2
      ⟨Set.mem_Ici.1 (hjn i hit), le_max_of_le_right (Finset.le_sup (f := id) hk)⟩
  refine ⟨max n (T.sup id), fun k => if k ∈ T then lam k else 0, le_max_left _ _,
    fun k => by dsimp only; split_ifs with hk; exacts [hlam0 k, le_rfl], ?_, ?_⟩
  · rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub, hsum1]
  · have hpad : ∑ k ∈ Finset.Icc n (max n (T.sup id)), (if k ∈ T then lam k else 0) • v k
        = ∑ k ∈ T, lam k • v k := by
      rw [← Finset.sum_subset hsub (fun k _ hk => by simp [hk])]
      exact Finset.sum_congr rfl fun k hk => by simp [hk]
    rw [hpad, hcomb, ← norm_neg, neg_sub]
    simpa [dist_eq_norm] using hbu

/-- **Mazur's lemma** ([han2009theoretical], Thm 3.3.11). If `vₙ ⇀ u` weakly then there are convex
combinations `uₙ = ∑_{i = n}^{N(n)} λᵢ⁽ⁿ⁾ vᵢ` of the tails of the sequence with `uₙ → u` in norm. -/
theorem exists_seq_convexCombination_tendsto {v : ℕ → E} {u : E} (h : WeakSeqTendsto v u) :
    ∃ (N : ℕ → ℕ) (lam : ℕ → ℕ → ℝ), (∀ n, n ≤ N n) ∧ (∀ n i, 0 ≤ lam n i) ∧
      (∀ n, ∑ i ∈ Finset.Icc n (N n), lam n i = 1) ∧
      Tendsto (fun n => ∑ i ∈ Finset.Icc n (N n), lam n i • v i) atTop (𝓝 u) := by
  choose N lam hN hlam0 hlam1 hlt using fun n : ℕ =>
    exists_convexCombination_norm_sub_lt h n (Nat.one_div_pos_of_nat (n := n))
  refine ⟨N, lam, hN, hlam0, hlam1, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hlt n).le) ?_
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- **A closed convex set is weakly sequentially closed** — the first corollary of Mazur's lemma
([han2009theoretical], after Thm 3.3.11). -/
theorem Convex.isWeakSeqClosed {K : Set E} (hconv : Convex ℝ K) (hcl : IsClosed K) :
    IsWeakSeqClosed K :=
  fun _ _ hu hw => mem_of_weak_tendsto_of_convex hconv hcl hu hw

/-- **A lower semicontinuous convex functional is weakly sequentially lower semicontinuous** — the
second corollary of Mazur's lemma ([han2009theoretical], after Thm 3.3.11).

The sublevel set `S = {x ∈ K | f x ≤ y}` is convex, so its closure is a closed convex set and
contains the weak limit `w`; lower semicontinuity along `K` at `w` then forbids `f w > y`, because
every neighbourhood of `w` meets `S`, where `f ≤ y`. Nothing is asked of `K` itself: the closure is
taken of the sublevel set, not of `K`. -/
theorem ConvexOn.weakSeqLowerSemicontinuousOn {f : E → ℝ} {K : Set E}
    (hf : ConvexOn ℝ K f) (hlsc : LowerSemicontinuousOn f K) :
    WeakSeqLowerSemicontinuousOn f K := by
  intro u w hu hw hlim y hy
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨σ, hσ, hσy⟩ := extraction_of_frequently_atTop hcon
  set S : Set E := {x ∈ K | f x ≤ y} with hS
  have hmem : w ∈ closure S :=
    mem_of_weak_tendsto_of_convex (hf.convex_le y).closure isClosed_closure
      (fun k => subset_closure ⟨hu (σ k), not_lt.1 (hσy k)⟩) (hlim.comp hσ)
  have : (𝓝[S] w).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hmem
  have hev : ∀ᶠ x in 𝓝[S] w, y < f x :=
    (hlsc w hw y hy).filter_mono (nhdsWithin_mono w fun x hx => hx.1)
  obtain ⟨x, hx1, hx2⟩ := (hev.and eventually_mem_nhdsWithin).exists
  exact absurd hx2.2 (not_le.2 hx1)

end Mazur

/-! ### The direct method -/

section DirectMethod

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [WeaklySeqCompactSpace V]

/-- The compactness step of the direct method: a sequence in a bounded, weakly sequentially closed
set has a subsequence converging weakly to a point of the set. -/
theorem IsWeakSeqClosed.exists_subseq_weakSeqTendsto {K : Set V} (hbd : IsBounded K)
    (hKc : IsWeakSeqClosed K) {u : ℕ → V} (hu : ∀ n, u n ∈ K) :
    ∃ (σ : ℕ → ℕ) (w : V), StrictMono σ ∧ w ∈ K ∧ WeakSeqTendsto (u ∘ σ) w := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hbd
  obtain ⟨σ, w, hσ, hlim⟩ :=
    WeaklySeqCompactSpace.exists_subseq_weakSeqTendsto u C fun n => hC _ (hu n)
  exact ⟨σ, w, hσ, hKc _ w (fun k => hu (σ k)) hlim, hlim⟩

/-- **Existence of a minimizer on a bounded set** ([han2009theoretical], Thm 3.3.8): a weakly
sequentially lower semicontinuous functional on a nonempty bounded weakly sequentially closed set
attains its minimum.

A minimizing sequence has a weakly convergent subsequence, whose limit stays in `K` and at which
lower semicontinuity forces the value to be no larger than the infimum. That the infimum is finite
is part of the argument: a sequence on which `f` tended to `-∞` would have a weak limit point in `K`
at which lower semicontinuity fails. -/
theorem exists_isMinOn_of_isWeakSeqClosed {K : Set V} {f : V → ℝ} (hne : K.Nonempty)
    (hbd : IsBounded K) (hKc : IsWeakSeqClosed K) (hf : WeakSeqLowerSemicontinuousOn f K) :
    ∃ u ∈ K, IsMinOn f K u := by
  classical
  -- `f` is bounded below on `K`
  have hbdd : BddBelow (f '' K) := by
    by_contra hcon
    rw [not_bddBelow_iff] at hcon
    have hcon' : ∀ m : ℝ, ∃ x ∈ K, f x < m := by
      intro m
      obtain ⟨y, hy, hym⟩ := hcon m
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, hx, hym⟩
    choose d hdK hdf using hcon'
    set c : ℕ → V := fun n => d (-(n : ℝ)) with hc
    have hcK : ∀ n, c n ∈ K := fun n => hdK _
    have hcf : ∀ n : ℕ, f (c n) < -(n : ℝ) := fun n => hdf _
    obtain ⟨σ, w, hσ, hwK, hlim⟩ := hKc.exists_subseq_weakSeqTendsto hbd hcK
    have h1 := hf (c ∘ σ) w (fun k => hcK (σ k)) hwK hlim (f w - 1) (by linarith)
    have h2 : ∀ᶠ k in atTop, f ((c ∘ σ) k) < f w - 1 := by
      have hten : Tendsto (fun k : ℕ => -((σ k : ℕ) : ℝ)) atTop atBot := by
        refine tendsto_neg_atTop_atBot.comp ?_
        exact tendsto_natCast_atTop_atTop.comp hσ.tendsto_atTop
      filter_upwards [hten.eventually_lt_atBot (f w - 1)] with k hk
      exact lt_trans (hcf (σ k)) hk
    obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
    exact absurd hk1 (not_lt.2 hk2.le)
  -- a minimizing sequence
  obtain ⟨v₀, hv₀⟩ := hne
  have hAne : (f '' K).Nonempty := ⟨f v₀, v₀, hv₀, rfl⟩
  set m : ℝ := sInf (f '' K) with hm
  have hchoice : ∀ n : ℕ, ∃ x ∈ K, f x < m + 1 / (n + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := Nat.one_div_pos_of_nat
    obtain ⟨y, hy, hylt⟩ := (csInf_lt_iff hbdd hAne).1 (show m < m + 1 / (n + 1) by linarith)
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, hylt⟩
  choose c hcK hcf using hchoice
  obtain ⟨σ, w, hσ, hwK, hlim⟩ := hKc.exists_subseq_weakSeqTendsto hbd hcK
  refine ⟨w, hwK, isMinOn_iff.2 fun x hx => le_trans ?_ (csInf_le hbdd ⟨x, hx, rfl⟩)⟩
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨y, hmy, hyw⟩ := exists_between hcon
  have h1 := hf (c ∘ σ) w (fun k => hcK (σ k)) hwK hlim y hyw
  have h2 : ∀ᶠ k in atTop, f ((c ∘ σ) k) < y := by
    have hten : Tendsto (fun k : ℕ => m + 1 / ((σ k : ℕ) + 1 : ℝ)) atTop (𝓝 (m + 0)) :=
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.comp hσ.tendsto_atTop)
    rw [add_zero] at hten
    filter_upwards [hten.eventually_lt_const hmy] with k hk
    exact lt_trans (hcf (σ k)) hk
  obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
  exact absurd hk1 (not_lt.2 hk2.le)

/-- **Existence of a minimizer of a coercive functional** ([han2009theoretical], Thm 3.3.10): the
set need not be bounded if the functional grows at infinity along it.

The sublevel set below the value at any one point of `K` is bounded by coercivity, weakly
sequentially closed by lower semicontinuity, and a minimizer there is a minimizer on `K`. -/
theorem exists_isMinOn_of_isCoerciveFunctionalOn {K : Set V} {f : V → ℝ} (hne : K.Nonempty)
    (hKc : IsWeakSeqClosed K) (hf : WeakSeqLowerSemicontinuousOn f K)
    (hcoer : IsCoerciveFunctionalOn f K) : ∃ u ∈ K, IsMinOn f K u := by
  obtain ⟨v₀, hv₀⟩ := hne
  set K₀ : Set V := {x ∈ K | f x ≤ f v₀} with hK₀
  have hsub : K₀ ⊆ K := fun _ hx => hx.1
  have hne₀ : K₀.Nonempty := ⟨v₀, hv₀, le_rfl⟩
  -- coercivity confines the search to `K₀`
  obtain ⟨R, hR⟩ := hcoer (f v₀ + 1)
  have hbd : IsBounded K₀ := by
    refine (Metric.isBounded_closedBall (x := (0 : V)) (r := R)).subset fun x hx => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hxR
    exact absurd (hR x hx.1 (not_le.1 hxR).le) (by linarith [hx.2])
  -- and `K₀` is weakly sequentially closed
  have hKc₀ : IsWeakSeqClosed K₀ := by
    intro u w hu hlim
    refine ⟨hKc u w (fun n => (hu n).1) hlim, ?_⟩
    by_contra hcon
    obtain ⟨k, hk⟩ := (hf u w (fun n => (hu n).1) (hKc u w (fun n => (hu n).1) hlim) hlim (f v₀)
      (not_le.1 hcon)).exists
    exact absurd (hu k).2 (not_le.2 hk)
  obtain ⟨u, hu, hmin⟩ :=
    exists_isMinOn_of_isWeakSeqClosed hne₀ hbd hKc₀ (hf.mono hsub)
  refine ⟨u, hsub hu, isMinOn_iff.2 fun x hx => ?_⟩
  by_cases hfx : f x ≤ f v₀
  · exact isMinOn_iff.1 hmin x ⟨hx, hfx⟩
  · exact le_trans (isMinOn_iff.1 hmin v₀ ⟨hv₀, le_rfl⟩) (not_le.1 hfx).le

/-- **Existence of a minimizer of a convex functional** ([han2009theoretical], Thm 3.3.12): on a
nonempty closed convex set, a lower semicontinuous convex functional attains its minimum as soon as
the set is bounded or the functional is coercive. Every hypothesis is for the norm topology; the two
corollaries of Mazur's lemma turn them into the weak hypotheses of Theorems 3.3.8 and 3.3.10.

Uniqueness under strict convexity is `IsMinOn.eq_of_strictConvexOn`. -/
theorem exists_isMinOn_of_convexOn {K : Set V} {f : V → ℝ} (hne : K.Nonempty) (hcl : IsClosed K)
    (hconv : Convex ℝ K) (hf : ConvexOn ℝ K f) (hlsc : LowerSemicontinuousOn f K)
    (h : IsBounded K ∨ IsCoerciveFunctionalOn f K) : ∃ u ∈ K, IsMinOn f K u :=
  h.elim
    (fun hbd => exists_isMinOn_of_isWeakSeqClosed hne hbd (hconv.isWeakSeqClosed hcl)
      (hf.weakSeqLowerSemicontinuousOn hlsc))
    (fun hcoer => exists_isMinOn_of_isCoerciveFunctionalOn hne (hconv.isWeakSeqClosed hcl)
      (hf.weakSeqLowerSemicontinuousOn hlsc) hcoer)

/-- **Existence of a best approximation from a closed convex set** ([han2009theoretical],
Thm 3.3.14). The distance to `u` is convex, continuous and coercive, so this is the coercive case of
`exists_isMinOn_of_convexOn`.

No completeness or inner product is needed beyond the weak sequential compactness of bounded
sequences; in a Hilbert space this is the projection theorem. -/
theorem exists_isBestApprox_of_convex {K : Set V} (hne : K.Nonempty) (hcl : IsClosed K)
    (hconv : Convex ℝ K) (u : V) : ∃ v, IsBestApprox K u v := by
  set f : V → ℝ := fun v => ‖u - v‖ with hf
  have hconvf : ConvexOn ℝ K f := by
    refine ⟨hconv, fun x _ y _ a b ha hb hab => ?_⟩
    have hcomb : a • (u - x) + b • (u - y) = u - (a • x + b • y) := by
      rw [smul_sub, smul_sub, ← add_sub_add_comm, ← add_smul, hab, one_smul]
    rw [hf]
    calc ‖u - (a • x + b • y)‖ = ‖a • (u - x) + b • (u - y)‖ := by rw [hcomb]
      _ ≤ ‖a • (u - x)‖ + ‖b • (u - y)‖ := norm_add_le _ _
      _ = a • ‖u - x‖ + b • ‖u - y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
            abs_of_nonneg hb, smul_eq_mul, smul_eq_mul]
  have hcoer : IsCoerciveFunctionalOn f K := by
    intro M
    refine ⟨M + ‖u‖, fun x _ hx => ?_⟩
    have h1 : ‖x‖ - ‖u‖ ≤ ‖x - u‖ := norm_sub_norm_le x u
    have h2 : ‖x - u‖ = ‖u - x‖ := norm_sub_rev x u
    change M ≤ ‖u - x‖
    linarith
  obtain ⟨v, hv, hmin⟩ := exists_isMinOn_of_convexOn hne hcl hconv hconvf
    ((continuous_const.sub continuous_id).norm.lowerSemicontinuous.lowerSemicontinuousOn K)
    (Or.inr hcoer)
  exact ⟨v, hv, fun w hw => isMinOn_iff.1 hmin w hw⟩

end DirectMethod
