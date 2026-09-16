import Numlib.Analysis.Convex.HellyRefined
import NumlibSurface.Rockafellar.Common.Euclidean

/-!
# Rockafellar §21: Helly's theorem and systems of inequalities

Surface file for R. Tyrrell Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §21:
existence theorems for systems of convex inequalities, stated as pairs of mutually exclusive
alternatives, and the four forms of Helly's theorem that come out of them.

All ten numbered results of §21 are formalized over `Rn n = ℝⁿ`: Theorems 21.1–21.6 and
Corollaries 21.3.1, 21.3.2, 21.6.1, 21.6.2, together with the unnumbered exercise after Corollary
21.3.2 (`helly_recession_iff_exists_isBounded`). Theorems 21.1, 21.2 and 21.3 read "one and only
one of the following alternatives holds": `theorem_21_k` is the disjunction, the half with content,
and `theorem_21_k_exclusive` says the alternatives cannot both hold.

Two hypotheses look like slips and are not. **Theorem 21.1 asks `dom fᵢ ⊇ ri C`, not
`dom fᵢ ⊇ C`**: separation produces the inequality only where every `fᵢ` is finite, and Corollary
7.3.3 carries it from `ri C` to `cl C ⊇ C`. **Alternative (b) is read in `EReal`, where
`0 · (+∞) = 0`**; without that convention a vanishing multiplier could not drop a constraint whose
`fᵢ` is `+∞` somewhere, and Corollary 21.6.2, which extends a short multiplier vector by zeros,
would be false as stated. No `0⁺` bookkeeping appears in this section.

The "Corollary 21.3.3" cited in the book's Comments and References for Part IV does not exist; the
intended reference is Corollary 21.3.2, Helly's theorem.

## Main definitions

* `ConvexSystem` — a **system of convex inequalities**: `fᵢ(x) ≤ αᵢ` for `i ∈ I₁` together with
  `fᵢ(x) < αᵢ` for `i ∈ I₂`, with arbitrary index sets and `-∞ ≤ αᵢ ≤ +∞`. Its solution set is
  `ConvexSystem.solutions` and the book's "consistent" is `ConvexSystem.Consistent`. Every numbered
  theorem is stated with right-hand sides `0`, which `solutions_normalize` justifies.
* `IsAffineFn` — the book's "`fᵢ` is an affine function" for an `EReal`-valued function on all of
  `ℝⁿ`, bridged by `isAffineFn_iff_eq_affineFn`.

## Main results

* `theorem_21_1`, `theorem_21_1_exclusive` — the basic alternative: either the system has a
  solution in `C`, or a non-trivial non-negative combination of the `fᵢ` is non-negative on `C`.
* `theorem_21_2`, `theorem_21_2_exclusive` — the same for a system mixing convex and affine
  constraints.
* `theorem_21_3`, `theorem_21_3_exclusive`, `corollary_21_3_1`, `corollary_21_3_2` — the
  infinite-system alternative under a recession hypothesis, and Helly's theorem as its corollary.
* `theorem_21_4`, `theorem_21_4_subsystem`, `theorem_21_5` — the polyhedral refinements: the
  recession hypothesis may be weakened when all but finitely many constraints are affine.
* `theorem_21_6`, `corollary_21_6_1`, `corollary_21_6_2`, `corollary_21_6_2_affine` — the finite
  form of Helly's theorem without closedness, and the bound of `n + 1` non-zero multipliers.
* `helly_recession_iff_exists_isBounded` — the unnumbered exercise after Corollary 21.3.2.
* `convex_solutions`, `isClosed_solutions`, `solutions_eq_iInter`, `solutions_normalize`,
  `pairing_eq_iff` — the elementary facts about solution sets that the section opens with.
-/

open Set

namespace Rockafellar

open ConvexAnalysis

variable {n : ℕ}

/-! ### A system of convex inequalities -/

/-- Rockafellar's **system of convex inequalities** in `ℝⁿ`: `fᵢ(x) ≤ αᵢ` for `i ∈ I₁` together
with `fᵢ(x) < αᵢ` for `i ∈ I₂`, with `I₁`, `I₂` arbitrary and `-∞ ≤ αᵢ ≤ +∞`. Convexity of the `fᵢ`
is not a field: the book's own statements about the solution set carry it as a hypothesis. -/
structure ConvexSystem (n : ℕ) (ι κ : Type*) where
  /-- The functions of the weak part, `fᵢ(x) ≤ αᵢ` for `i ∈ I₁`. -/
  weakFn : ι → Rn n → EReal
  /-- The right-hand sides `αᵢ` of the weak part, allowed to be `±∞`. -/
  weakBound : ι → EReal
  /-- The functions of the strict part, `fᵢ(x) < αᵢ` for `i ∈ I₂`. -/
  strictFn : κ → Rn n → EReal
  /-- The right-hand sides `αᵢ` of the strict part, allowed to be `±∞`. -/
  strictBound : κ → EReal

namespace ConvexSystem

variable {ι κ : Type*}

/-- The set of solutions `x` of a system of convex inequalities. -/
def solutions (S : ConvexSystem n ι κ) : Set (Rn n) :=
  {x | (∀ i, S.weakFn i x ≤ S.weakBound i) ∧ ∀ j, S.strictFn j x < S.strictBound j}

/-- The book's **consistent**: the system has at least one solution. -/
def Consistent (S : ConvexSystem n ι κ) : Prop := S.solutions.Nonempty

/-- **§21 (p. 185).** The solution set is the intersection of the level sets of the
constraints. -/
theorem solutions_eq_iInter (S : ConvexSystem n ι κ) :
    S.solutions = (⋂ i, {x | S.weakFn i x ≤ S.weakBound i})
      ∩ ⋂ j, {x | S.strictFn j x < S.strictBound j} := by
  ext x
  simp [solutions]

/-- **§21 (p. 185).** The solution set of a system of convex inequalities is convex. -/
theorem convex_solutions (S : ConvexSystem n ι κ) (hw : ∀ i, ConvexFn (S.weakFn i))
    (hs : ∀ j, ConvexFn (S.strictFn j)) : Convex ℝ S.solutions := by
  rw [solutions_eq_iInter]
  exact Convex.inter (convex_iInter fun i => (hw i).convex_le _)
    (convex_iInter fun j => (hs j).convex_lt _)

/-- A level set `{x | f x ≤ α}` of a closed function is closed, for an *extended-real* level `α`;
`lowerSemicontinuous_iff_isClosed_le` covers only the finite levels. -/
theorem isClosed_setOf_le {f : Rn n → EReal} (hf : ClosedFn f) (a : EReal) :
    IsClosed {x : Rn n | f x ≤ a} := by
  induction a using EReal.rec with
  | bot =>
    rcases closedFn_iff.1 hf with rfl | ⟨-, hne⟩
    · simp
    · have hempty : {x : Rn n | f x ≤ ⊥} = (∅ : Set (Rn n)) := by
        ext x
        simpa using hne x
      rw [hempty]
      exact isClosed_empty
  | coe r => exact lowerSemicontinuous_iff_isClosed_le.1 hf.lowerSemicontinuous r
  | top => simp

/-- **§21 (p. 185).** With no strict inequalities and every `fᵢ` closed, the solution set is
closed. -/
theorem isClosed_solutions [IsEmpty κ] (S : ConvexSystem n ι κ)
    (hw : ∀ i, ClosedFn (S.weakFn i)) : IsClosed S.solutions := by
  rw [solutions_eq_iInter]
  have hstrict : (⋂ j, {x : Rn n | S.strictFn j x < S.strictBound j}) = (univ : Set (Rn n)) := by
    simp
  rw [hstrict, Set.inter_univ]
  exact isClosed_iInter fun i => isClosed_setOf_le (hw i) _

/-- **§21 (p. 186).** For a *finite* right-hand side `α`, `f(x) ≤ α` is `g(x) ≤ 0` for `g = f - α`,
and likewise for the strict form. This is why every numbered theorem takes right-hand sides `0`. -/
theorem solutions_normalize (f : Rn n → EReal) (a : ℝ) (x : Rn n) :
    (f x ≤ (a : EReal) ↔ f x - (a : EReal) ≤ 0) ∧ (f x < (a : EReal) ↔ f x - (a : EReal) < 0) := by
  generalize f x = y
  induction y using EReal.rec with
  | bot => simp
  | coe r =>
    rw [← EReal.coe_sub]
    norm_cast
    exact ⟨⟨fun h => by linarith, fun h => by linarith⟩,
      ⟨fun h => by linarith, fun h => by linarith⟩⟩
  | top => simp

end ConvexSystem

/-- **§21 (p. 186).** A linear equation enters a system of convex inequalities as a pair of
inequalities: `⟨x, b⟩ = β` is `⟨x, b⟩ ≤ β` and `⟨x, -b⟩ ≤ -β`. -/
theorem pairing_eq_iff (x b : Rn n) (β : ℝ) :
    pairing n x b = β ↔ pairing n x b ≤ β ∧ pairing n x (-b) ≤ -β := by
  rw [map_neg]
  constructor
  · rintro h
    simp [h]
  · rintro ⟨h₁, h₂⟩
    linarith

/-! ### Theorem 21.1 -/

/-- **Theorem 21.1**. For `C` convex and `f₁, …, f_m` proper convex with `dom fᵢ ⊇ ri C`, one and
only one of the following holds:

(a) `f₁(x) < 0, …, f_m(x) < 0` for some `x ∈ C`;

(b) `λ₁f₁(x) + ⋯ + λ_mf_m(x) ≥ 0` for every `x ∈ C`, for some `λᵢ ≥ 0` not all zero.

This is the disjunction; `theorem_21_1_exclusive` is the exclusivity. The hypothesis is `ri C` and
not `C`, and the weighted sum is read in `EReal`, where `0 · (+∞) = 0`. -/
theorem theorem_21_1 {ι : Type*} [Fintype ι] [Nonempty ι] {C : Set (Rn n)}
    {f : ι → Rn n → EReal} (hC : Convex ℝ C) (hf : ∀ i, ConvexFn (f i)) (hp : ∀ i, Proper (f i))
    (hdom : ∀ i, ri C ⊆ dom (f i)) :
    (∃ x ∈ C, ∀ i, f i x < 0) ∨
      ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ l ≠ 0 ∧
        ∀ x ∈ C, (0 : EReal) ≤ ∑ i, (l i : EReal) * f i x :=
  alternative_of_convex_system hC hf hp hdom

/-- **Theorem 21.1**, the "only one" half: (a) and (b) cannot both hold. Nothing is assumed about
the `fᵢ` or `C` — at a point where every `fᵢ` is negative, every term `λᵢfᵢ(x)` is non-positive and
those with `λᵢ ≠ 0` are strictly negative. -/
theorem theorem_21_1_exclusive {ι : Type*} [Fintype ι] {C : Set (Rn n)} {f : ι → Rn n → EReal}
    {l : ι → ℝ} (hl : ∀ i, 0 ≤ l i) (hl0 : l ≠ 0)
    (h : ∀ x ∈ C, (0 : EReal) ≤ ∑ i, (l i : EReal) * f i x) :
    ¬ ∃ x ∈ C, ∀ i, f i x < 0 :=
  not_exists_forall_neg_of_forall_zero_le_weighted hl hl0 h

/-! ### Theorem 21.2 -/

/-- **Theorem 21.2**. For `C` convex, `f₁, …, f_k` proper convex with `dom fᵢ ⊇ ri C`, and
`f_{k+1}, …, f_m` affine with `f_{k+1}(x) ≤ 0, …, f_m(x) ≤ 0` solvable in `ri C`, one and only one
of the following holds:

(a) `x ∈ C` with `f₁(x) < 0, …, f_k(x) < 0` and `f_{k+1}(x) ≤ 0, …, f_m(x) ≤ 0`;

(b) non-negative `λ₁, …, λ_m`, at least one of `λ₁, …, λ_k` non-zero, with
`λ₁f₁(x) + ⋯ + λ_mf_m(x) ≥ 0` for every `x ∈ C`.

The convex constraints are indexed by `ι` and the affine ones by `κ`, the latter as `Rn n →ᵃ[ℝ] ℝ`.
Theorem 21.1 is the case `κ = Empty` but is not derived from this one: 21.1 needs only Theorem
11.3, while 21.2 needs the polyhedral separation of Theorem 20.2. -/
theorem theorem_21_2 {ι κ : Type*} [Fintype ι] [Fintype κ] {C : Set (Rn n)}
    {f : ι → Rn n → EReal} {a : κ → (Rn n →ᵃ[ℝ] ℝ)} (hC : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hp : ∀ i, Proper (f i)) (hdom : ∀ i, ri C ⊆ dom (f i))
    (hfeas : ∃ x ∈ ri C, ∀ j, a j x ≤ 0) :
    (∃ x ∈ C, (∀ i, f i x < 0) ∧ ∀ j, a j x ≤ 0) ∨
      ∃ (l : ι → ℝ) (μ : κ → ℝ), (∀ i, 0 ≤ l i) ∧ (∀ j, 0 ≤ μ j) ∧ l ≠ 0 ∧
        ∀ x ∈ C, (0 : EReal)
          ≤ (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * a j x : ℝ) : EReal) :=
  alternative_of_convex_system_affine hC hf hp hdom hfeas

/-- **Theorem 21.2**, the "only one" half: at a point of `C` solving the mixed system the convex
part of the weighted sum is strictly negative and the affine part is non-positive. -/
theorem theorem_21_2_exclusive {ι κ : Type*} [Fintype ι] [Fintype κ] {C : Set (Rn n)}
    {f : ι → Rn n → EReal} {a : κ → (Rn n →ᵃ[ℝ] ℝ)} {l : ι → ℝ} {μ : κ → ℝ}
    (hl : ∀ i, 0 ≤ l i) (hμ : ∀ j, 0 ≤ μ j) (hl0 : l ≠ 0)
    (h : ∀ x ∈ C, (0 : EReal)
      ≤ (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * a j x : ℝ) : EReal)) :
    ¬ ∃ x ∈ C, (∀ i, f i x < 0) ∧ ∀ j, a j x ≤ 0 := by
  rintro ⟨x, hx, hneg, haff⟩
  have hconv : ¬ (0 : EReal) ≤ ∑ i, (l i : EReal) * f i x := by
    intro hle
    refine not_exists_forall_neg_of_forall_zero_le_weighted (C := ({x} : Set (Rn n))) hl hl0
      (fun y hy => ?_) ⟨x, rfl, hneg⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hle
  have haffsum : (∑ j, μ j * a j x) ≤ 0 := by
    refine Finset.sum_nonpos fun j _ => ?_
    have h₁ := hμ j
    have h₂ := haff j
    nlinarith
  have hlt : (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * a j x : ℝ) : EReal) < 0 := by
    calc (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * a j x : ℝ) : EReal)
        ≤ (∑ i, (l i : EReal) * f i x) + 0 := by
          have h0 : ((∑ j, μ j * a j x : ℝ) : EReal) ≤ 0 := by exact_mod_cast haffsum
          exact add_le_add le_rfl h0
      _ = ∑ i, (l i : EReal) * f i x := add_zero _
      _ < 0 := not_le.1 hconv
  exact absurd (h x hx) (not_le.2 hlt)

/-! ### Theorem 21.3 and its corollaries -/

/-- **Theorem 21.3**. Let `{fᵢ | i ∈ I}` be closed proper convex functions on `ℝⁿ`, `I` arbitrary,
and `C` a non-empty closed convex set; assume the `fᵢ` have no common direction of recession which
also recedes in `C`. Then one and only one of the following holds:

(a) `x ∈ C` with `fᵢ(x) ≤ 0` for every `i ∈ I`;

(b) non-negative `λᵢ`, finitely many non-zero, and `ε > 0` with `∑ᵢ λᵢfᵢ(x) ≥ ε` for every `x ∈ C`.

In case (b) at most `n + 1` of the `λᵢ` need be non-zero, which is the `t.card ≤ n + 1` clause. -/
theorem theorem_21_3 {ι : Type*} {C : Set (Rn n)} {f : ι → Rn n → EReal}
    (hf : ∀ i, ClosedProperConvexFn (f i)) (hC : Convex ℝ C) (hCc : IsClosed C) (hCne : C.Nonempty)
    (hrec : ∀ y : Rn n, (∀ i, recessionFn (f i) y ≤ 0) → y ∈ recessionCone C → y = 0) :
    (∃ x ∈ C, ∀ i, f i x ≤ 0) ∨
      ∃ (t : Finset ι) (l : ι → ℝ) (ε : ℝ), (∀ i, 0 ≤ l i) ∧ (∀ i ∉ t, l i = 0) ∧ 0 < ε ∧
        t.card ≤ n + 1 ∧ ∀ x ∈ C, (ε : EReal) ≤ ∑ i ∈ t, (l i : EReal) * f i x := by
  simpa only [finrank_euclideanSpace_fin] using
    alternative_infinite_system (B := pairing n) hf hC hCc hCne hrec

/-- **Theorem 21.3**, the "only one" half: at a solution of the weak system every term `λᵢfᵢ(x)` is
non-positive, so the sum cannot be bounded below by a positive `ε`. -/
theorem theorem_21_3_exclusive {ι : Type*} {C : Set (Rn n)} {f : ι → Rn n → EReal}
    {t : Finset ι} {l : ι → ℝ} {ε : ℝ} (hl : ∀ i, 0 ≤ l i) (hε : 0 < ε)
    (h : ∀ x ∈ C, (ε : EReal) ≤ ∑ i ∈ t, (l i : EReal) * f i x) :
    ¬ ∃ x ∈ C, ∀ i, f i x ≤ 0 := by
  rintro ⟨x, hx, hle⟩
  have hsum : ∑ i ∈ t, (l i : EReal) * f i x ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => ?_
    calc (l i : EReal) * f i x
        ≤ (l i : EReal) * 0 := by
          refine mul_le_mul_of_nonneg_left (hle i) ?_
          exact_mod_cast hl i
      _ = 0 := by simp
  have hle0 : ((ε : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) := by
    simpa using le_trans (h x hx) hsum
  exact absurd (EReal.coe_le_coe_iff.1 hle0) (not_le.2 hε)

/-- **Corollary 21.3.1**. Under the recession hypothesis of Theorem 21.3, existence for an
infinite system reduces to existence for its finite subsystems: if for every `ε > 0` and every set
of at most `n + 1` indices the system `f_{i₁}(x) < ε, …, f_{i_m}(x) < ε` is solvable in `C`, then
`fᵢ(x) ≤ 0` for all `i ∈ I` is solvable in `C`. -/
theorem corollary_21_3_1 {ι : Type*} {C : Set (Rn n)} {f : ι → Rn n → EReal}
    (hf : ∀ i, ClosedProperConvexFn (f i)) (hC : Convex ℝ C) (hCc : IsClosed C) (hCne : C.Nonempty)
    (hrec : ∀ y : Rn n, (∀ i, recessionFn (f i) y ≤ 0) → y ∈ recessionCone C → y = 0)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ S : Finset ι, S.card ≤ n + 1 →
      ∃ x ∈ C, ∀ i ∈ S, f i x < (ε : EReal)) :
    ∃ x ∈ C, ∀ i, f i x ≤ 0 := by
  refine exists_forall_le_zero_of_forall_subsystem (B := pairing n) hf hC hCc hCne hrec ?_
  simpa only [finrank_euclideanSpace_fin] using hsub

/-- **Corollary 21.3.2** (Helly's Theorem). Let `{Cᵢ | i ∈ I}` be non-empty closed convex sets in
`ℝⁿ`, `I` arbitrary, with no common direction of recession. If every subcollection of `n + 1` or
fewer sets has non-empty intersection, so does the whole collection. The recession hypothesis
cannot be dropped. Compare `theorem_21_6`, where the collection is finite and neither closedness
nor a recession hypothesis is needed. -/
theorem corollary_21_3_2 {ι : Type*} {K : ι → Set (Rn n)} (hconv : ∀ i, Convex ℝ (K i))
    (hcl : ∀ i, IsClosed (K i)) (hne : ∀ i, (K i).Nonempty)
    (hrec : ∀ y : Rn n, (∀ i, y ∈ recessionCone (K i)) → y = 0)
    (hinter : ∀ S : Finset ι, S.card ≤ n + 1 → (⋂ i ∈ S, K i).Nonempty) :
    (⋂ i, K i).Nonempty := by
  refine helly_of_no_common_recession (B := pairing n) hconv hcl hne hrec ?_
  simpa only [finrank_euclideanSpace_fin] using hinter

/-- **§21**, the unnumbered exercise after Corollary 21.3.2: assuming every finite subcollection
has a non-empty intersection, the recession hypothesis of Helly's theorem holds if and only if some
finite subcollection has a bounded intersection. Taking `S = {i}` recovers the sentence before it,
that the hypothesis holds as soon as one `Cᵢ` is bounded. -/
theorem helly_recession_iff_exists_isBounded {ι : Type*} {K : ι → Set (Rn n)}
    (hconv : ∀ i, Convex ℝ (K i)) (hcl : ∀ i, IsClosed (K i))
    (hne : ∀ S : Finset ι, (⋂ i ∈ S, K i).Nonempty) :
    (∀ y : Rn n, (∀ i, y ∈ recessionCone (K i)) → y = 0) ↔
      ∃ S : Finset ι, Bornology.IsBounded (⋂ i ∈ S, K i) := by
  have hbridge : ⋂ i, recessionCone (K i) = {0} ↔
      ∀ y : Rn n, (∀ i, y ∈ recessionCone (K i)) → y = 0 := by
    simp [Set.eq_singleton_iff_unique_mem, mem_iInter]
  rw [← hbridge]
  exact iInter_recessionCone_eq_zero_iff_exists_isBounded hconv hcl hne

/-! ### Theorems 21.4 and 21.5: the polyhedral refinements -/

/-- The book's "`fᵢ` is an affine function", for a function `EReal`-valued on all of `ℝⁿ`:
`f(x) = ⟨x, b⟩ - β`. -/
def IsAffineFn (f : Rn n → EReal) : Prop :=
  ∃ (b : Rn n) (β : ℝ), ∀ x, f x = ((inner ℝ x b - β : ℝ) : EReal)

/-- An affine function of `ℝⁿ` in the book's sense is exactly an `affineFn` of the pairing. -/
theorem isAffineFn_iff_eq_affineFn {f : Rn n → EReal} :
    IsAffineFn f ↔ ∃ (b : Rn n) (β : ℝ), f = affineFn (pairing n) b β := by
  constructor
  · rintro ⟨b, β, h⟩
    exact ⟨b, β, funext fun x => by rw [h x, affineFn_eq_coe, pairing_apply]⟩
  · rintro ⟨b, β, rfl⟩
    exact ⟨b, β, fun x => by rw [affineFn_eq_coe, pairing_apply]⟩

/-- **Theorem 21.4**. When `C = ℝⁿ`, the recession hypothesis of Theorem 21.3 and Corollary 21.3.1
may be weakened to: there is a finite `I₀ ⊆ I` with `fᵢ` affine for `i ∈ I₀`, such that every
direction of recession common to all the `fᵢ` is a direction in which `fᵢ` is constant for each
`i ∈ I \ I₀`. "Direction in which `fᵢ` is constant" is `constancySpace (f i)`; `theorem_21_3` is
the case `I₀ = ∅`, since `0` lies in every constancy space. -/
theorem theorem_21_4 {ι : Type*} {f : ι → Rn n → EReal} (hf : ∀ i, ClosedProperConvexFn (f i))
    (I₀ : Finset ι) (haff : ∀ i ∈ I₀, IsAffineFn (f i))
    (hrec : ∀ y : Rn n, (∀ i, recessionFn (f i) y ≤ 0) → ∀ i ∉ I₀, y ∈ constancySpace (f i)) :
    (∃ x : Rn n, ∀ i, f i x ≤ 0) ∨
      ∃ (t : Finset ι) (l : ι → ℝ) (ε : ℝ), (∀ i, 0 ≤ l i) ∧ (∀ i ∉ t, l i = 0) ∧ 0 < ε ∧
        t.card ≤ n + 1 ∧ ∀ x : Rn n, (ε : EReal) ≤ ∑ i ∈ t, (l i : EReal) * f i x := by
  have hB := separatingRight_pairing n
  simpa only [finrank_euclideanSpace_fin] using
    alternative_infinite_system_univ_of_affine_tail (B := pairing n) hB hf I₀
      (fun i hi => isAffineFn_iff_eq_affineFn.1 (haff i hi)) hrec

/-- **Theorem 21.4** for Corollary 21.3.1: under the affine-tail hypothesis, an infinite system of
weak convex inequalities on `ℝⁿ` is solvable as soon as every subsystem of at most `n + 1` of the
inequalities is solvable to within an arbitrarily small tolerance. -/
theorem theorem_21_4_subsystem {ι : Type*} {f : ι → Rn n → EReal}
    (hf : ∀ i, ClosedProperConvexFn (f i)) (I₀ : Finset ι) (haff : ∀ i ∈ I₀, IsAffineFn (f i))
    (hrec : ∀ y : Rn n, (∀ i, recessionFn (f i) y ≤ 0) → ∀ i ∉ I₀, y ∈ constancySpace (f i))
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ S : Finset ι, S.card ≤ n + 1 →
      ∃ x : Rn n, ∀ i ∈ S, f i x < (ε : EReal)) :
    ∃ x : Rn n, ∀ i, f i x ≤ 0 := by
  have hB := separatingRight_pairing n
  refine exists_forall_le_zero_of_forall_subsystem_of_affine_tail (B := pairing n) hB hf I₀
    (fun i hi => isAffineFn_iff_eq_affineFn.1 (haff i hi)) hrec ?_
  simpa only [finrank_euclideanSpace_fin] using hsub

/-- **Theorem 21.5**. The recession hypothesis in Helly's theorem may be weakened to: there is a
finite `I₀ ⊆ I` with `Cᵢ` polyhedral for `i ∈ I₀`, such that every direction of recession common to
all the `Cᵢ` is a direction in which `Cᵢ` is linear for each `i ∈ I \ I₀`. "Direction in which `Cᵢ`
is linear" is `linealitySpace (K i)`. -/
theorem theorem_21_5 {ι : Type*} {K : ι → Set (Rn n)} (hconv : ∀ i, Convex ℝ (K i))
    (hcl : ∀ i, IsClosed (K i)) (hne : ∀ i, (K i).Nonempty) (I₀ : Finset ι)
    (hpoly : ∀ i ∈ I₀, Polyhedral (K i))
    (hrec : ∀ y : Rn n, (∀ i, y ∈ recessionCone (K i)) → ∀ i ∉ I₀, y ∈ linealitySpace (K i))
    (hinter : ∀ S : Finset ι, S.card ≤ n + 1 → (⋂ i ∈ S, K i).Nonempty) :
    (⋂ i, K i).Nonempty := by
  have hB := separatingRight_pairing n
  refine helly_of_polyhedral_tail (B := pairing n) hB hconv hcl hne I₀ hpoly hrec ?_
  simpa only [finrank_euclideanSpace_fin] using hinter

/-! ### Theorem 21.6 and its corollaries: finite collections -/

/-- **Theorem 21.6**. For a *finite* collection of convex sets in `ℝⁿ`, not necessarily closed, if
every subcollection of `n + 1` or fewer sets has non-empty intersection then so does the whole
collection. Rockafellar derives this from Corollary 21.3.2; the proof here goes through Radon's
theorem instead, so Corollaries 21.6.1 and 21.6.2 do not depend on Theorem 21.3. -/
theorem theorem_21_6 {ι : Type*} {K : ι → Set (Rn n)} {s : Finset ι}
    (hconv : ∀ i ∈ s, Convex ℝ (K i))
    (hinter : ∀ t ⊆ s, t.card ≤ n + 1 → (⋂ i ∈ t, K i).Nonempty) :
    (⋂ i ∈ s, K i).Nonempty := by
  refine helly_finite hconv ?_
  simpa only [finrank_euclideanSpace_fin] using hinter

/-- **Corollary 21.6.1**. For a system `f₁(x) < 0, …, f_k(x) < 0, f_{k+1}(x) ≤ 0, …, f_m(x) ≤ 0`
with every `fᵢ` convex on `ℝⁿ`: if every subsystem of `n + 1` or fewer inequalities has a solution
in a convex set `C`, the whole system has one in `C`. The book's `1, …, k` is the index type `ι`
and its `k+1, …, m` is `κ`, so "`n + 1` or fewer inequalities" is `S.card + T.card ≤ n + 1`. -/
theorem corollary_21_6_1 {ι κ : Type*} [Finite ι] [Finite κ] {C : Set (Rn n)}
    {f : ι → Rn n → EReal} {g : κ → Rn n → EReal} (hC : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hg : ∀ j, ConvexFn (g j))
    (hsub : ∀ (S : Finset ι) (T : Finset κ), S.card + T.card ≤ n + 1 →
      ∃ x ∈ C, (∀ i ∈ S, f i x < 0) ∧ ∀ j ∈ T, g j x ≤ 0) :
    ∃ x ∈ C, (∀ i, f i x < 0) ∧ ∀ j, g j x ≤ 0 := by
  refine exists_mem_of_forall_subsystem hC hf hg ?_
  simpa only [finrank_euclideanSpace_fin] using hsub

/-- **Corollary 21.6.2**. If alternative (b) of Theorem 21.1 holds, the `λᵢ` may be chosen with at
most `n + 1` of them non-zero. The sparsity is stated as a `Finset` `S` of size at most `n + 1`
outside which every `λᵢ` vanishes, which avoids deciding `λᵢ ≠ 0`; extending a short multiplier
vector by zeros is harmless precisely because `0 · (+∞) = 0` in `EReal`. The book states this for
Theorem 21.2 as well — that half is `corollary_21_6_2_affine`. -/
theorem corollary_21_6_2 {ι : Type*} [Fintype ι] [Nonempty ι] {C : Set (Rn n)}
    {f : ι → Rn n → EReal} (hC : Convex ℝ C) (hf : ∀ i, ConvexFn (f i)) (hp : ∀ i, Proper (f i))
    (hdom : ∀ i, ri C ⊆ dom (f i)) :
    (∃ x ∈ C, ∀ i, f i x < 0) ∨
      ∃ (S : Finset ι) (l : ι → ℝ), S.card ≤ n + 1 ∧ (∀ i ∉ S, l i = 0) ∧
        (∀ i, 0 ≤ l i) ∧ l ≠ 0 ∧ ∀ x ∈ C, (0 : EReal) ≤ ∑ i, (l i : EReal) * f i x := by
  simpa only [finrank_euclideanSpace_fin] using
    sparse_alternative_of_convex_system hC hf hp hdom

/-- A real affine function of `ℝⁿ`, read into `EReal`, is convex. This is what lets the affine
constraints of Theorem 21.2 enter Corollary 21.6.1's collection of convex sets. -/
theorem convexFn_coe_affineMap (g : Rn n →ᵃ[ℝ] ℝ) : ConvexFn (fun x => ((g x : ℝ) : EReal)) := by
  refine convexFn_of_epi_combo fun x y p q hx hy s t hs ht hst => ?_
  rw [EReal.coe_le_coe_iff] at hx hy ⊢
  rw [Convex.combo_affine_apply hst]
  simp only [smul_eq_mul]
  nlinarith

/-- **Corollary 21.6.2** for **Theorem 21.2**: if alternative (b) holds there, at most `n + 1` of
`λ₁, …, λ_m` need be non-zero, the count running over the affine multipliers as well as the convex
ones, since the book's `λ₁, …, λ_m` is one list. The book's proof, verbatim: if (a) fails it
already fails for a subsystem of at most `n + 1` inequalities, and Theorem 21.2 applied to that
subsystem produces multipliers which extend by zero. -/
theorem corollary_21_6_2_affine {ι κ : Type*} [Fintype ι] [Fintype κ] {C : Set (Rn n)}
    {f : ι → Rn n → EReal} {a : κ → (Rn n →ᵃ[ℝ] ℝ)} (hC : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hp : ∀ i, Proper (f i)) (hdom : ∀ i, ri C ⊆ dom (f i))
    (hfeas : ∃ x ∈ ri C, ∀ j, a j x ≤ 0) :
    (∃ x ∈ C, (∀ i, f i x < 0) ∧ ∀ j, a j x ≤ 0) ∨
      ∃ (S : Finset ι) (T : Finset κ) (l : ι → ℝ) (μ : κ → ℝ),
        S.card + T.card ≤ n + 1 ∧ (∀ i ∉ S, l i = 0) ∧ (∀ j ∉ T, μ j = 0) ∧
          (∀ i, 0 ≤ l i) ∧ (∀ j, 0 ≤ μ j) ∧ l ≠ 0 ∧
          ∀ x ∈ C, (0 : EReal)
            ≤ (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * a j x : ℝ) : EReal) := by
  classical
  by_cases halt : ∃ x ∈ C, (∀ i, f i x < 0) ∧ ∀ j, a j x ≤ 0
  · exact Or.inl halt
  refine Or.inr ?_
  have hsmall : ∃ (S : Finset ι) (T : Finset κ), S.card + T.card ≤ n + 1 ∧
      ¬ ∃ x ∈ C, (∀ i ∈ S, f i x < 0) ∧ ∀ j ∈ T, a j x ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have hsub : ∀ (S : Finset ι) (T : Finset κ), S.card + T.card ≤ n + 1 →
        ∃ x ∈ C, (∀ i ∈ S, f i x < 0) ∧ ∀ j ∈ T, ((a j x : ℝ) : EReal) ≤ 0 := by
      intro S T hST
      obtain ⟨x, hx, hxf, hxa⟩ := hcon S T hST
      exact ⟨x, hx, hxf, fun j hj => by exact_mod_cast hxa j hj⟩
    obtain ⟨x, hx, hxf, hxa⟩ :=
      corollary_21_6_1 (g := fun j x => ((a j x : ℝ) : EReal)) hC hf
        (fun j => convexFn_coe_affineMap (a j)) hsub
    exact halt ⟨x, hx, hxf, fun j => by exact_mod_cast hxa j⟩
  obtain ⟨S, T, hcard, hSalt⟩ := hsmall
  obtain ⟨y₀, hy₀, hy₀a⟩ := hfeas
  rcases theorem_21_2 (ι := ↥S) (κ := ↥T) (f := fun i : ↥S => f i) (a := fun j : ↥T => a j) hC
      (fun i => hf i) (fun i => hp i) (fun i => hdom i) ⟨y₀, hy₀, fun j => hy₀a j⟩ with
    ⟨x, hx, hxf, hxa⟩ | ⟨l', μ', hl'0, hμ'0, hl'ne, hl'⟩
  · exact absurd ⟨x, hx, fun i hi => hxf ⟨i, hi⟩, fun j hj => hxa ⟨j, hj⟩⟩ hSalt
  refine ⟨S, T, fun i => if h : i ∈ S then l' ⟨i, h⟩ else 0,
    fun j => if h : j ∈ T then μ' ⟨j, h⟩ else 0, hcard, fun i hi => by simp [hi],
    fun j hj => by simp [hj], ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases h : i ∈ S
    · simpa [h] using hl'0 ⟨i, h⟩
    · simp [h]
  · intro j
    by_cases h : j ∈ T
    · simpa [h] using hμ'0 ⟨j, h⟩
    · simp [h]
  · intro hzero
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : ↥S, l' i₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hl'ne (funext hcon)
    have h := congrFun hzero (i₀ : ι)
    simp only [i₀.2, Pi.zero_apply, Subtype.coe_eta, ↓reduceDIte] at h
    exact hi₀ h
  · intro x hx
    have hshrinkl : ∑ i, ((if h : i ∈ S then l' ⟨i, h⟩ else 0 : ℝ) : EReal) * f i x
        = ∑ i ∈ S, ((if h : i ∈ S then l' ⟨i, h⟩ else 0 : ℝ) : EReal) * f i x := by
      refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
      intro i _ hi
      simp [hi]
    have hshrinkm : ∑ j, (if h : j ∈ T then μ' ⟨j, h⟩ else 0 : ℝ) * a j x
        = ∑ j ∈ T, (if h : j ∈ T then μ' ⟨j, h⟩ else 0 : ℝ) * a j x := by
      refine (Finset.sum_subset (Finset.subset_univ T) ?_).symm
      intro j _ hj
      simp [hj]
    rw [hshrinkl, hshrinkm, ← Finset.sum_coe_sort S, ← Finset.sum_coe_sort T]
    have hcl : ∀ i : ↥S, ((if h : (i : ι) ∈ S then l' ⟨(i : ι), h⟩ else 0 : ℝ) : EReal)
        * f i x = (l' i : EReal) * f i x := by
      intro i
      simp only [i.2, Subtype.coe_eta, ↓reduceDIte]
    have hcm : ∀ j : ↥T, (if h : (j : κ) ∈ T then μ' ⟨(j : κ), h⟩ else 0 : ℝ) * a j x
        = μ' j * a j x := by
      intro j
      simp only [j.2, Subtype.coe_eta, ↓reduceDIte]
    rw [Finset.sum_congr rfl fun i _ => hcl i, Finset.sum_congr rfl fun j _ => hcm j]
    exact hl' x hx

end Rockafellar
