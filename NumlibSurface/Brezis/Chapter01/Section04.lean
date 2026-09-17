import Numlib.Analysis.Convex.Duality.Continuity
import Numlib.Analysis.Convex.Extremum.Fenchel
import NumlibSurface.Brezis.Chapter01.Section03

/-!
# Brezis §1.4: a quick introduction to the theory of conjugate convex functions

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §1.4, over a real normed space `E` with dual
`E* = StrongDual ℝ E`. Everything is the backbone's convex library (`Numlib/Analysis/Convex/…`,
the Rockafellar development) read over the pairing `⟨f, x⟩ = f x` of `E` with `E*`.

## Correspondence

* The book's `φ : E → (-∞, +∞]` is a function `φ : E → EReal` with `∀ x, φ x ≠ ⊥`; `φ ≢ +∞` is
  `(ConvexAnalysis.dom φ).Nonempty`, and the two together are `ConvexAnalysis.Proper φ`. The
  domain `D(φ)` and the epigraph `epi φ` are `ConvexAnalysis.dom` and `ConvexAnalysis.epi`
  (`mem_domain_iff`, `mem_epigraph_iff`).
* "l.s.c." is Mathlib's `LowerSemicontinuous` (`lowerSemicontinuous_iff` is the book's
  definition by sublevel sets), which for a function never equal to `⊥` is the backbone's
  `ClosedFn` (`closedFn_iff_lowerSemicontinuous`). "Convex" is `ConvexAnalysis.ConvexFn`,
  convexity of the epigraph (`convexFn_iff` is the book's inequality).
* The pairing is `dualPairing E := (topDualPairing ℝ E).flip`, `E` on the left as the backbone's
  `conj` wants; the conjugate `φ* : E* → (-∞, +∞]` is `conjugate φ := conj (dualPairing E) φ`
  and the biconjugate *restricted to `E`* is `biconjugate φ := biconj (dualPairing E) φ`, which
  is why the backbone's `biconj` uses `B.flip` rather than a second copy of `B`.
* The instance `instIsCompatiblePairingTopDual` makes `E` compatibly paired with its dual in its
  own norm topology, so Fenchel–Moreau (`biconj_eq_clFn_topDual`) applies with no reflexivity
  assumption, exactly as in the book; the constraint qualification of Theorem 1.12 is the
  backbone's `IsExactSum.of_continuousAt`. No new backbone module was needed.

## Main results

* `lowerSemicontinuous_iff`, `convexFn_iff`, `mem_domain_iff`, `mem_epigraph_iff` — the
  definitions of §1.4 identified with the backbone's.
* `conjugate`, `conjugate_apply`, `conjugate_convexFn`, `conjugate_lowerSemicontinuous`,
  `remark_1_7`, `remark_1_7_classical` — the conjugate function and Young's inequality.
* `proposition_1_10`, `proposition_1_10_affine` — `φ* ≢ +∞`, and the continuous affine minorant.
* `biconjugate`, `theorem_1_11` — Fenchel–Moreau, `φ** = φ`.
* `theorem_1_12`, `theorem_1_12_max`, `lemma_1_4`, `lemma_1_4_convex` — Fenchel–Rockafellar.
* `example_1_1_conj`, `example_1_1_biconj`, `example_1_2_convexFn_iff`,
  `example_1_2_lowerSemicontinuous_iff`, `example_1_2_conj`, `example_1_2_biconj`,
  `example_1_2_orthogonal`, `example_1_3`, `example_1_3_submodule`,
  `example_1_3_submodule_of_example_1_3`, `example_1_4` — the four examples, with
  `polarCone_dualPairing_eq` bridging the convex library's polar cones to the orthogonals of
  §1.3.

The two lists of elementary facts on l.s.c. and convex functions are not numbered results
(Mathlib's `lowerSemicontinuous_iff_isClosed_epigraph`, `LowerSemicontinuous.add`,
`lowerSemicontinuous_iSup`, `LowerSemicontinuousOn.exists_isMinOn`, the backbone's
`ConvexFn.convex_le`, `convexFn_add_coe`, `convexFn_iSup`); Remark 8 is discussion.
-/

open ConvexAnalysis Metric Set

namespace Brezis.Chapter01

/-! ### Lower semicontinuous and convex functions -/

/-- **The Notation of §1.4, the domain.** For `φ : E → (-∞, +∞]`, `D(φ) = {x ∈ E | φ x < +∞}` is
the backbone's `dom φ`. -/
theorem mem_domain_iff {E : Type*} (φ : E → EReal) (x : E) : x ∈ dom φ ↔ φ x < ⊤ :=
  mem_dom

/-- **The Notation of §1.4, the epigraph.** `epi φ = {[x, λ] ∈ E × ℝ | φ x ≤ λ}` is the
backbone's `epi φ`, a subset of `E × ℝ` — `λ` does not take the value `+∞` (footnote 5). -/
theorem mem_epigraph_iff {E : Type*} (φ : E → EReal) (x : E) (l : ℝ) :
    (x, l) ∈ epi φ ↔ φ x ≤ (l : EReal) :=
  mk_mem_epi

/-- **The Definition of lower semicontinuity.** On a topological space `E`, a function
`φ : E → (-∞, +∞]` is l.s.c. iff for every `λ ∈ ℝ` the sublevel set `[φ ≤ λ]` is closed. The
book's notion is Mathlib's `LowerSemicontinuous` (the section's fact 2, `φ y ≥ φ x - ε` near
`x`). -/
theorem lowerSemicontinuous_iff {E : Type*} [TopologicalSpace E] (φ : E → EReal) :
    LowerSemicontinuous φ ↔ ∀ l : ℝ, IsClosed {x | φ x ≤ (l : EReal)} :=
  lowerSemicontinuous_iff_isClosed_le

/-- **The Definition of a convex function.** On a vector space `E`, a function
`φ : E → (-∞, +∞]` is convex iff `φ (t x + (1 - t) y) ≤ t φ x + (1 - t) φ y` for all `x, y` and
`t ∈ (0, 1)`. The book's notion is the backbone's `ConvexFn` — convexity of the epigraph, the
section's fact 1 on convex functions. -/
theorem convexFn_iff {E : Type*} [AddCommGroup E] [Module ℝ E] {φ : E → EReal}
    (hφ : ∀ x, φ x ≠ ⊥) :
    ConvexFn φ ↔ ∀ x y (t : ℝ), 0 < t → t < 1 →
      φ (t • x + (1 - t) • y) ≤ (t : EReal) * φ x + ((1 - t : ℝ) : EReal) * φ y := by
  rw [convexFn_iff_le hφ]
  constructor
  · intro h x y t ht ht1
    exact h x y t (1 - t) ht (by linarith) (by ring)
  · intro h x y a b ha hb hab
    obtain rfl : b = 1 - a := by linarith
    exact h x y a ha (by linarith)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The conjugate function -/

/-- **The scalar product of the duality `E*, E`**, `⟨f, x⟩ = f x`, written with `E` on the left as
the backbone's `conj` wants: `dualPairing E x f = f x`. An `abbrev` of
`(topDualPairing ℝ E).flip`, so that the backbone's instances `instIsCompatiblePairingTopDual`
(`E` compatibly paired with `E*` in its norm topology) and `instIsContinuousPairingTopDualNorm`
(`E*` continuously paired with `E` in the norm topology of `E*`) are found on it. -/
noncomputable abbrev dualPairing (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    E →ₗ[ℝ] StrongDual ℝ E →ₗ[ℝ] ℝ :=
  (topDualPairing ℝ E).flip

@[simp] theorem dualPairing_apply (x : E) (f : StrongDual ℝ E) : dualPairing E x f = f x := rfl

theorem flip_dualPairing : (dualPairing E).flip = topDualPairing ℝ E := rfl

/-- **The Definition of the conjugate function.** For `φ : E → (-∞, +∞]`,
`φ* : E* → (-∞, +∞]` is `φ* f = sup_{x ∈ E} (⟨f, x⟩ - φ x)`: the backbone's
`conj (dualPairing E) φ`. The book assumes `φ ≢ +∞`; the backbone defines `conj` for every `φ`
(`conj_eq_bot_iff`: `φ* ≡ -∞` exactly when `φ ≡ +∞`), and the hypothesis reappears where it
matters (`remark_1_7`, `proposition_1_10`). -/
noncomputable def conjugate (φ : E → EReal) : StrongDual ℝ E → EReal :=
  conj (dualPairing E) φ

theorem conjugate_eq_conj (φ : E → EReal) : conjugate φ = conj (dualPairing E) φ := rfl

theorem conjugate_apply (φ : E → EReal) (f : StrongDual ℝ E) :
    conjugate φ f = ⨆ x, ((f x : ℝ) : EReal) - φ x := rfl

/-- "Note that `φ*` is convex and l.s.c. on `E*`", first half: `φ*` is convex, for every `φ`. -/
theorem conjugate_convexFn (φ : E → EReal) : ConvexFn (conjugate φ) :=
  convexFn_conj _ _

/-- "Note that `φ*` is convex and l.s.c. on `E*`", second half: `φ*` is l.s.c. in the norm
topology of `E*` — the superior envelope of the continuous affine functions `f ↦ ⟨f, x⟩ - φ x`
(the section's fact 4). -/
theorem conjugate_lowerSemicontinuous (φ : E → EReal) : LowerSemicontinuous (conjugate φ) :=
  (closedFn_conj (B := dualPairing E) (f := φ)).lowerSemicontinuous

/-- **Remark 7, Young's inequality (11).** `⟨f, x⟩ ≤ φ x + φ* f` for all `x ∈ E`, `f ∈ E*`, when
`φ x ≠ -∞` and `φ ≢ +∞`; "obvious with our definition of `φ*`" (in `EReal` the two hypotheses are
what keeps the right-hand side from collapsing to `-∞`). -/
theorem remark_1_7 {φ : E → EReal} (hφ : ∀ x, φ x ≠ ⊥) (hdom : (dom φ).Nonempty) (x : E)
    (f : StrongDual ℝ E) : ((f x : ℝ) : EReal) ≤ φ x + conjugate φ f :=
  le_add_conj (B := dualPairing E) (hφ x) hdom f

/-- **Remark 7, the classical Young inequality (12).** For `a, b ≥ 0`, `1 < p < ∞` and
`1/p + 1/p' = 1`, `a b ≤ a^p / p + b^{p'} / p'`. That it is (11) for `φ t = |t|^p / p` on
`E = ℝ` (Exercise 1.18 (h)) is not formalized. -/
theorem remark_1_7_classical {a b p p' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 1 < p)
    (hpp' : 1 / p + 1 / p' = 1) : a * b ≤ a ^ p / p + b ^ p' / p' :=
  Real.young_inequality_of_nonneg ha hb
    (Real.holderConjugate_iff.2 ⟨hp, by simpa only [one_div] using hpp'⟩)

/-! ### Proposition 1.10 and Theorem 1.11 -/

/-- **Proposition 1.10, first clause.** If `φ : E → (-∞, +∞]` is convex, l.s.c. and `φ ≢ +∞`,
then `φ* ≢ +∞`. -/
theorem proposition_1_10 {φ : E → EReal} (hφ : ConvexFn φ) (hl : LowerSemicontinuous φ)
    (hbot : ∀ x, φ x ≠ ⊥) (hdom : (dom φ).Nonempty) : (dom (conjugate φ)).Nonempty :=
  ((proper_conj_iff (B := dualPairing E) hφ
    ((closedFn_iff_lowerSemicontinuous hbot).2 hl)).2 ⟨hdom, hbot⟩).dom_nonempty

/-- **Proposition 1.10, "in particular".** Under the same hypotheses `φ` is bounded below by a
continuous affine function: there are `f ∈ E*` and `c ∈ ℝ` with `⟨f, x⟩ - c ≤ φ x` for all
`x`. -/
theorem proposition_1_10_affine {φ : E → EReal} (hφ : ConvexFn φ) (hl : LowerSemicontinuous φ)
    (hbot : ∀ x, φ x ≠ ⊥) (hdom : (dom φ).Nonempty) :
    ∃ (f : StrongDual ℝ E) (c : ℝ), ∀ x, ((f x - c : ℝ) : EReal) ≤ φ x := by
  obtain ⟨f, c, hfc⟩ := exists_affine_le_of_closed_proper
    ⟨hφ, (closedFn_iff_lowerSemicontinuous hbot).2 hl, ⟨hdom, hbot⟩⟩
  exact ⟨f, c, fun x => by rw [EReal.coe_sub]; exact hfc x⟩

/-- **The biconjugate restricted to `E`**, as the book defines it before Theorem 1.11:
`φ** x = sup_{f ∈ E*} (⟨f, x⟩ - φ* f)` for `x ∈ E` — the backbone's `biconj (dualPairing E) φ`,
which is `conj (topDualPairing ℝ E) (conjugate φ)`. Iterating `*` instead would give a function
on `E**`; that is why the backbone's `biconj` is `conj B.flip ∘ conj B` and not `conj ∘ conj`. -/
noncomputable def biconjugate (φ : E → EReal) : E → EReal :=
  biconj (dualPairing E) φ

theorem biconjugate_eq_conj (φ : E → EReal) :
    biconjugate φ = conj (topDualPairing ℝ E) (conjugate φ) := rfl

theorem biconjugate_apply (φ : E → EReal) (x : E) :
    biconjugate φ x = ⨆ f : StrongDual ℝ E, ((f x : ℝ) : EReal) - conjugate φ f := rfl

/-- **Theorem 1.11 (Fenchel–Moreau).** If `φ : E → (-∞, +∞]` is convex, l.s.c. and `φ ≢ +∞`,
then `φ** = φ`. No reflexivity is needed: `E` is compatibly paired with `E*` in its own norm
topology (`instIsCompatiblePairingTopDual`). The backbone's statement does not need `φ ≢ +∞`
(then `φ* ≡ -∞` and `φ** ≡ +∞`); the hypothesis is kept as the book states it. -/
theorem theorem_1_11 {φ : E → EReal} (hφ : ConvexFn φ) (hl : LowerSemicontinuous φ)
    (hbot : ∀ x, φ x ≠ ⊥) (_hdom : (dom φ).Nonempty) : biconjugate φ = φ :=
  biconj_eq_self (B := dualPairing E) hφ ((closedFn_iff_lowerSemicontinuous hbot).2 hl)

/-! ### Example 1: the norm -/

/-- **Example 1.** For `φ x = ‖x‖`, `φ* f = 0` if `‖f‖ ≤ 1` and `φ* f = +∞` if `‖f‖ > 1`: the
indicator function of the closed unit ball of `E*`. -/
theorem example_1_1_conj :
    conjugate (fun x : E => (‖x‖ : EReal)) = indicatorFn (closedBall (0 : StrongDual ℝ E) 1) := by
  funext f
  rw [conjugate_apply]
  by_cases hf : ‖f‖ ≤ 1
  · rw [indicatorFn_of_mem (mem_closedBall_zero_iff.2 hf)]
    refine le_antisymm (iSup_le fun x => ?_) (le_iSup_of_le 0 (by simp))
    rw [← EReal.coe_sub, ← EReal.coe_zero, EReal.coe_le_coe_iff, sub_nonpos]
    calc f x ≤ ‖f x‖ := Real.le_norm_self _
      _ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
      _ ≤ 1 * ‖x‖ := by gcongr
      _ = ‖x‖ := one_mul _
  · rw [indicatorFn_of_notMem fun h => hf (mem_closedBall_zero_iff.1 h)]
    rw [not_le] at hf
    -- a direction along which `f x - ‖x‖ > 0`; scaling it sends the supremum to `+∞`
    obtain ⟨x, hx1, hfx⟩ := f.exists_lt_apply_of_lt_opNorm hf
    obtain ⟨y, hy⟩ : ∃ y : E, ‖y‖ < f y := by
      rcases le_or_gt 0 (f x) with h | h
      · exact ⟨x, hx1.trans (by rwa [Real.norm_eq_abs, abs_of_nonneg h] at hfx)⟩
      · refine ⟨-x, ?_⟩
        rw [norm_neg, map_neg]
        exact hx1.trans (by rwa [Real.norm_eq_abs, abs_of_neg h] at hfx)
    have hd : 0 < f y - ‖y‖ := sub_pos.2 hy
    refine top_unique (le_of_forall_lt fun b hb => ?_)
    obtain ⟨r, hr, -⟩ := EReal.lt_iff_exists_real_btwn.1 hb
    set t : ℝ := (|r| + 1) / (f y - ‖y‖) with ht
    have ht0 : 0 ≤ t := div_nonneg (by positivity) hd.le
    refine lt_of_lt_of_le ?_ (le_iSup (fun x : E => ((f x : ℝ) : EReal) - (‖x‖ : EReal)) (t • y))
    rw [map_smul, norm_smul, Real.norm_of_nonneg ht0, smul_eq_mul, ← EReal.coe_sub]
    refine lt_of_lt_of_le hr (EReal.coe_le_coe_iff.2 ?_)
    rw [← mul_sub, ht, div_mul_cancel₀ _ hd.ne']
    exact (le_abs_self r).trans (by linarith)

/-- **Example 1, continued.** `φ** x = sup_{‖f‖ ≤ 1} ⟨f, x⟩` for the norm `φ`, and, `φ` being
convex and continuous, `φ** = φ` (Theorem 1.11) gives `‖x‖ = sup_{‖f‖ ≤ 1} ⟨f, x⟩` — "we obtain
again part of Corollary 1.4" (`corollary_1_4` states the supremum of `|⟨f, x⟩|`; over the
symmetric ball the two agree). -/
theorem example_1_1_biconj (x : E) :
    biconjugate (fun x : E => (‖x‖ : EReal)) x =
        ⨆ f ∈ closedBall (0 : StrongDual ℝ E) 1, ((f x : ℝ) : EReal) ∧
      (‖x‖ : EReal) = ⨆ f ∈ closedBall (0 : StrongDual ℝ E) 1, ((f x : ℝ) : EReal) := by
  have h : biconjugate (fun x : E => (‖x‖ : EReal)) x =
      ⨆ f ∈ closedBall (0 : StrongDual ℝ E) 1, ((f x : ℝ) : EReal) := by
    rw [biconjugate_apply, example_1_1_conj]
    refine iSup_congr fun f => ?_
    by_cases hf : f ∈ closedBall (0 : StrongDual ℝ E) 1
    · rw [iSup_pos hf, indicatorFn_of_mem hf, sub_zero]
    · rw [iSup_neg hf, indicatorFn_of_notMem hf, EReal.sub_top]
  refine ⟨h, ?_⟩
  have h11 := theorem_1_11 (φ := fun x : E => (‖x‖ : EReal))
    (convexOn_norm (convex_univ : Convex ℝ (univ : Set E))).convexFn_coe
    (EReal.continuous_coe_iff.2 continuous_norm).lowerSemicontinuous
    (fun x => EReal.coe_ne_bot ‖x‖) ⟨0, EReal.coe_lt_top _⟩
  exact (congrFun h11 x).symm.trans h

/-! ### Example 2: indicator functions and orthogonals -/

/-- **Example 2.** The indicator function `I_K` of a set `K ⊆ E` (`0` on `K`, `+∞` off `K`; the
backbone's `indicatorFn K`, not to be confused with the characteristic function `χ_K`) is convex
iff `K` is convex. -/
theorem example_1_2_convexFn_iff (K : Set E) : ConvexFn (indicatorFn K) ↔ Convex ℝ K :=
  convexFn_indicatorFn

omit [NormedSpace ℝ E] in
/-- **Example 2.** `I_K` is l.s.c. iff `K` is closed. -/
theorem example_1_2_lowerSemicontinuous_iff (K : Set E) :
    LowerSemicontinuous (indicatorFn K) ↔ IsClosed K := by
  refine ⟨fun hl => ?_, fun hK => (closedFn_indicatorFn hK).lowerSemicontinuous⟩
  have hK : {x | indicatorFn K x ≤ ((0 : ℝ) : EReal)} = K := by
    ext x
    by_cases hx : x ∈ K <;> simp [hx]
  rw [← hK]
  exact (lowerSemicontinuous_iff _).1 hl 0

/-- **The polar cones of the convex library are the orthogonals of §1.3.** For a subspace
`M ⊆ E`, the polar cone of `M` under `dualPairing E` is `M^⊥ ⊆ E*`; for a subspace `N ⊆ E*`,
the polar cone of `N` under `topDualPairing ℝ E` is `N^⊥ ⊆ E`. -/
theorem polarCone_dualPairing_eq :
    (∀ M : Submodule ℝ E,
        polarCone (dualPairing E) (M : Set E) =
          (M.strongDualAnnihilator : Set (StrongDual ℝ E))) ∧
      ∀ N : Submodule ℝ (StrongDual ℝ E),
        polarCone (topDualPairing ℝ E) (N : Set (StrongDual ℝ E)) =
          (N.strongDualCoannihilator : Set E) := by
  constructor
  · intro M
    rw [polarCone_coe_submodule']
    ext f
    simp only [SetLike.mem_coe, Submodule.mem_strongDualAnnihilator, dualPairing_apply]
    exact Iff.rfl
  · intro N
    rw [polarCone_coe_submodule']
    ext x
    simp only [SetLike.mem_coe, Submodule.mem_strongDualCoannihilator, topDualPairing_apply]
    exact Iff.rfl

/-- **Example 2.** For a linear subspace `M ⊆ E`, `(I_M)* = I_{M^⊥}`. -/
theorem example_1_2_conj (M : Submodule ℝ E) :
    conjugate (indicatorFn (M : Set E)) =
      indicatorFn (M.strongDualAnnihilator : Set (StrongDual ℝ E)) := by
  rw [conjugate_eq_conj,
    conj_indicatorFn_eq_indicatorFn_polarCone (fun _ ha => smul_coe_submodule M ha)
      ⟨0, M.zero_mem⟩, polarCone_dualPairing_eq.1 M]

/-- **Example 2.** For a linear subspace `M ⊆ E`, `(I_M)** = I_{(M^⊥)^⊥}`. -/
theorem example_1_2_biconj (M : Submodule ℝ E) :
    biconjugate (indicatorFn (M : Set E)) =
      indicatorFn (M.strongDualAnnihilator.strongDualCoannihilator : Set E) := by
  rw [biconjugate_eq_conj, example_1_2_conj,
    conj_indicatorFn_eq_indicatorFn_polarCone (fun _ ha => smul_coe_submodule _ ha)
      ⟨0, Submodule.zero_mem _⟩, polarCone_dualPairing_eq.2]

/-- **Example 2, the conclusion.** For a *closed* linear subspace `M ⊆ E`, writing
`(I_M)** = I_M` (Theorem 1.11) gives `(M^⊥)^⊥ = M`: "Theorem 1.11 can be viewed as a counterpart
of Proposition 1.9" (`proposition_1_9` says `(M^⊥)^⊥ = closure M`). Proved the book's way, by
reading `example_1_2_biconj` through `theorem_1_11`. -/
theorem example_1_2_orthogonal {M : Submodule ℝ E} (hM : IsClosed (M : Set E)) :
    M.strongDualAnnihilator.strongDualCoannihilator = M := by
  have h := theorem_1_11 (convexFn_indicatorFn.2 M.convex)
    ((example_1_2_lowerSemicontinuous_iff (M : Set E)).2 hM) (indicatorFn_ne_bot _)
    ⟨0, by rw [dom_indicatorFn]; exact M.zero_mem⟩
  rw [example_1_2_biconj] at h
  have h' := congrArg dom h
  rw [dom_indicatorFn, dom_indicatorFn] at h'
  exact SetLike.coe_injective h'

/-! ### Theorem 1.12 -/

/-- **Theorem 1.12 (Fenchel–Rockafellar), the duality.** Let `φ, ψ : E → (-∞, +∞]` be convex,
and let `x₀ ∈ D(φ) ∩ D(ψ)` be a point at which `φ` is continuous. Then
`inf_{x ∈ E} (φ x + ψ x) = sup_{f ∈ E*} (-φ*(-f) - ψ* f)`. The case `a = -∞` the book treats
separately is absorbed by the `EReal` formulation. -/
theorem theorem_1_12 {φ ψ : E → EReal} (hφ : ConvexFn φ) (hψ : ConvexFn ψ)
    (hφb : ∀ x, φ x ≠ ⊥) (hψb : ∀ x, ψ x ≠ ⊥) {x₀ : E} (hx₀φ : x₀ ∈ dom φ) (hx₀ψ : x₀ ∈ dom ψ)
    (hcont : ContinuousAt φ x₀) :
    (⨅ x, φ x + ψ x) = ⨆ f : StrongDual ℝ E, -(conjugate φ (-f)) - conjugate ψ f := by
  have hex : IsExactSum (dualPairing E) φ ψ :=
    IsExactSum.of_continuousAt hφ ⟨⟨x₀, hx₀φ⟩, hφb⟩ hψ ⟨⟨x₀, hx₀ψ⟩, hψb⟩ hx₀φ hx₀ψ hcont
  have h1 : (⨅ x, φ x + ψ x) = -(conj (dualPairing E) (φ + ψ) 0) :=
    iInf_eq_neg_conj_zero (dualPairing E) (φ + ψ)
  rw [h1, hex.conj_add_apply 0, EReal.neg_iInf]
  refine iSup_congr fun f => ?_
  rw [zero_sub]
  exact EReal.neg_add (Or.inl (hex.conj_left_ne_bot (-f))) (Or.inr (hex.conj_right_ne_bot f))

/-- **Theorem 1.12 (Fenchel–Rockafellar), the attainment.** Under the same hypotheses the
supremum is a maximum: there is `f ∈ E*` with `-φ*(-f) - ψ* f = inf_{x ∈ E} (φ x + ψ x)`, and
(the book's last expression) the same `f` realizes `inf (φ + ψ) = -min_{f} (φ*(-f) + ψ* f)`. -/
theorem theorem_1_12_max {φ ψ : E → EReal} (hφ : ConvexFn φ) (hψ : ConvexFn ψ)
    (hφb : ∀ x, φ x ≠ ⊥) (hψb : ∀ x, ψ x ≠ ⊥) {x₀ : E} (hx₀φ : x₀ ∈ dom φ) (hx₀ψ : x₀ ∈ dom ψ)
    (hcont : ContinuousAt φ x₀) :
    ∃ f : StrongDual ℝ E, -(conjugate φ (-f)) - conjugate ψ f = (⨅ x, φ x + ψ x) ∧
      conjugate φ (-f) + conjugate ψ f = -(⨅ x, φ x + ψ x) := by
  have hex : IsExactSum (dualPairing E) φ ψ :=
    IsExactSum.of_continuousAt hφ ⟨⟨x₀, hx₀φ⟩, hφb⟩ hψ ⟨⟨x₀, hx₀ψ⟩, hψb⟩ hx₀φ hx₀ψ hcont
  have h1 : (⨅ x, φ x + ψ x) = -(conj (dualPairing E) (φ + ψ) 0) :=
    iInf_eq_neg_conj_zero (dualPairing E) (φ + ψ)
  obtain ⟨y₁, y₂, hy, hval⟩ := hex.exists_conj_add_eq 0
  obtain rfl : y₁ = -y₂ := eq_neg_of_add_eq_zero_left hy
  refine ⟨y₂, ?_, ?_⟩
  · rw [h1, ← hval,
      EReal.neg_add (Or.inl (hex.conj_left_ne_bot (-y₂))) (Or.inr (hex.conj_right_ne_bot y₂))]
    rfl
  · rw [h1, neg_neg]
    exact hval

/-- **Lemma 1.4, first clause.** If `C ⊆ E` is convex then so is `Int C`. -/
theorem lemma_1_4_convex {C : Set E} (hC : Convex ℝ C) : Convex ℝ (interior C) :=
  hC.interior

/-- **Lemma 1.4, main clause.** If `C ⊆ E` is convex and `Int C ≠ ∅`, then
`closure C = closure (Int C)` (the book refers to Exercise 1.7 for the proof). -/
theorem lemma_1_4 {C : Set E} (hC : Convex ℝ C) (hne : (interior C).Nonempty) :
    closure C = closure (interior C) :=
  (hC.closure_interior_eq_closure_of_nonempty_interior hne).symm

/-! ### Examples 3 and 4 -/

/-- The conjugate of `x ↦ ‖x - x₀‖` at `-f`: `example_1_1_conj` translated by the conjugacy
table's translation row (`conj_comp_sub`), the unit ball being symmetric. -/
private theorem conjugate_norm_sub_neg (x₀ : E) (f : StrongDual ℝ E) :
    conjugate (fun x : E => (‖x - x₀‖ : EReal)) (-f) =
      indicatorFn (closedBall (0 : StrongDual ℝ E) 1) f - ((f x₀ : ℝ) : EReal) := by
  have h := conj_comp_sub (dualPairing E) (fun x : E => (‖x‖ : EReal)) x₀ (-f)
  rw [conjugate_eq_conj, h, ← conjugate_eq_conj, example_1_1_conj, dualPairing_apply,
    neg_apply, EReal.coe_neg, ← sub_eq_add_neg]
  congr 1
  by_cases hf : f ∈ closedBall (0 : StrongDual ℝ E) 1
  · rw [indicatorFn_of_mem hf, indicatorFn_of_mem (by simpa using hf)]
  · rw [indicatorFn_of_notMem hf, indicatorFn_of_notMem (by simpa using hf)]

/-- **Example 3, formula (19).** For a nonempty convex `K ⊆ E` and `x₀ ∈ E`,
`dist (x₀, K) = inf_{x ∈ K} ‖x - x₀‖ = max_{‖f‖ ≤ 1} (⟨f, x₀⟩ - I_K* f)`: the distance is the
infimum (Mathlib's `infDist`), it is the supremum over the closed unit ball of `E*` of
`⟨f, x₀⟩ - I_K* f`, and the supremum is attained. Theorem 1.12 with `φ x = ‖x - x₀‖` and
`ψ = I_K`. -/
theorem example_1_3 {K : Set E} (hK : Convex ℝ K) (hne : K.Nonempty) (x₀ : E) :
    ((infDist x₀ K : ℝ) : EReal) = ⨅ x ∈ K, (‖x - x₀‖ : EReal) ∧
      ((infDist x₀ K : ℝ) : EReal) =
        ⨆ f ∈ closedBall (0 : StrongDual ℝ E) 1,
          ((f x₀ : ℝ) : EReal) - conjugate (indicatorFn K) f ∧
      ∃ f : StrongDual ℝ E, ‖f‖ ≤ 1 ∧
        ((f x₀ : ℝ) : EReal) - conjugate (indicatorFn K) f = ((infDist x₀ K : ℝ) : EReal) := by
  set φ : E → EReal := fun x => (‖x - x₀‖ : EReal) with hφ
  -- the distance as the book's infimum
  have hA : ((infDist x₀ K : ℝ) : EReal) = ⨅ x ∈ K, (‖x - x₀‖ : EReal) := by
    have hinf : infDist x₀ K = sInf ((fun x => ‖x - x₀‖) '' K) := by
      rw [infDist_eq_iInf, sInf_image']
      exact iInf_congr fun y => by rw [dist_comm, dist_eq_norm]
    have hbdd : BddBelow ((fun x => ‖x - x₀‖) '' K) :=
      ⟨0, by rintro _ ⟨y, -, rfl⟩; exact norm_nonneg _⟩
    rw [hinf, EReal.coe_sInf_of_bddBelow (hne.image _) hbdd, iInf_image]
  -- the constrained infimum as an unconstrained one
  have hB : (⨅ x ∈ K, (‖x - x₀‖ : EReal)) = ⨅ x, φ x + indicatorFn K x :=
    iInf_mem_eq_iInf_add_indicatorFn φ K fun _ => EReal.coe_ne_bot _
  -- the hypotheses of Theorem 1.12
  have hφc : ConvexFn φ := by
    have h : ConvexOn ℝ univ fun x : E => ‖x - x₀‖ := by
      simpa only [dist_eq_norm] using convexOn_dist x₀ (convex_univ (𝕜 := ℝ) (E := E))
    exact h.convexFn_coe
  have hφcont : Continuous φ :=
    EReal.continuous_coe_iff.2 (continuous_id.sub continuous_const).norm
  obtain ⟨x₁, hx₁⟩ := hne
  have hx₁ψ : x₁ ∈ dom (indicatorFn K) := by rw [dom_indicatorFn]; exact hx₁
  -- the dual side, term by term
  have hC : ∀ f : StrongDual ℝ E, -(conjugate φ (-f)) - conjugate (indicatorFn K) f =
      ⨆ _ : f ∈ closedBall (0 : StrongDual ℝ E) 1,
        ((f x₀ : ℝ) : EReal) - conjugate (indicatorFn K) f := by
    intro f
    rw [hφ, conjugate_norm_sub_neg]
    by_cases hf : f ∈ closedBall (0 : StrongDual ℝ E) 1
    · rw [iSup_pos hf, indicatorFn_of_mem hf, zero_sub, neg_neg]
    · rw [iSup_neg hf, indicatorFn_of_notMem hf, EReal.top_sub_coe, EReal.neg_top, EReal.bot_sub]
  refine ⟨hA, ?_, ?_⟩
  · rw [hA, hB, theorem_1_12 hφc (convexFn_indicatorFn.2 hK) (fun _ => EReal.coe_ne_bot _)
      (indicatorFn_ne_bot _) (EReal.coe_lt_top _) hx₁ψ hφcont.continuousAt]
    exact iSup_congr hC
  · obtain ⟨f, hf, -⟩ := theorem_1_12_max hφc (convexFn_indicatorFn.2 hK)
      (fun _ => EReal.coe_ne_bot _) (indicatorFn_ne_bot _) (EReal.coe_lt_top _) hx₁ψ
      hφcont.continuousAt
    rw [hC f, ← hB, ← hA] at hf
    by_cases h1 : f ∈ closedBall (0 : StrongDual ℝ E) 1
    · rw [iSup_pos h1] at hf
      exact ⟨f, mem_closedBall_zero_iff.1 h1, hf⟩
    · rw [iSup_neg h1] at hf
      exact absurd hf.symm (EReal.coe_ne_bot _)

/-- **Example 3, the subspace case.** For a linear subspace `M ⊆ E` and `x₀ ∈ E`,
`dist (x₀, M) = max_{f ∈ M^⊥, ‖f‖ ≤ 1} ⟨f, x₀⟩`: the supremum of `⟨f, x₀⟩` over the functionals
of `M^⊥` of norm at most one is `dist (x₀, M)`, and it is attained. The backbone proves this by
Hahn–Banach in `E ⧸ closure M`; the book derives it from (19) with `(I_M)* = I_{M^⊥}`
(`example_1_2_conj`). -/
theorem example_1_3_submodule (M : Submodule ℝ E) (x₀ : E) :
    infDist x₀ M = sSup ((fun f : StrongDual ℝ E => f x₀) ''
        {f | f ∈ M.strongDualAnnihilator ∧ ‖f‖ ≤ 1}) ∧
      ∃ f ∈ M.strongDualAnnihilator, ‖f‖ ≤ 1 ∧ f x₀ = infDist x₀ M := by
  obtain ⟨f, hfM, hf1, hfx⟩ := M.exists_mem_strongDualAnnihilator_norm_le_one_apply_eq_infDist x₀
  rw [RCLike.ofReal_real_eq_id, id] at hfx
  have hgreat : IsGreatest ((fun f : StrongDual ℝ E => f x₀) ''
      {f | f ∈ M.strongDualAnnihilator ∧ ‖f‖ ≤ 1}) (infDist x₀ M) := by
    refine ⟨⟨f, ⟨hfM, hf1⟩, hfx⟩, ?_⟩
    rintro _ ⟨g, ⟨hgM, hg1⟩, rfl⟩
    exact (Real.le_norm_self _).trans
      (Submodule.norm_apply_le_infDist_of_mem_strongDualAnnihilator hgM hg1 x₀)
  exact ⟨hgreat.csSup_eq.symm, f, hfM, hf1, hfx⟩

/-- **Example 3, the subspace case derived from (19)**, the book's way: with `(I_M)* = I_{M^⊥}`
(`example_1_2_conj`), formula (19) for `K = M` reads
`dist (x₀, M) = max_{f ∈ M^⊥, ‖f‖ ≤ 1} ⟨f, x₀⟩` — here in `EReal`, the supremum over
`{f ∈ M^⊥ | ‖f‖ ≤ 1}` and its attainment. `example_1_3_submodule` is the same statement in `ℝ`,
proved from the backbone's Hahn–Banach argument instead. -/
theorem example_1_3_submodule_of_example_1_3 (M : Submodule ℝ E) (x₀ : E) :
    ((infDist x₀ M : ℝ) : EReal) =
        ⨆ f ∈ {f : StrongDual ℝ E | f ∈ M.strongDualAnnihilator ∧ ‖f‖ ≤ 1},
          ((f x₀ : ℝ) : EReal) ∧
      ∃ f ∈ M.strongDualAnnihilator, ‖f‖ ≤ 1 ∧ ((f x₀ : ℝ) : EReal) = infDist x₀ M := by
  obtain ⟨-, h19, f, hf1, hfx⟩ := example_1_3 M.convex ⟨0, M.zero_mem⟩ x₀
  rw [example_1_2_conj] at h19 hfx
  constructor
  · rw [h19]
    refine iSup_congr fun g => ?_
    by_cases hg1 : g ∈ closedBall (0 : StrongDual ℝ E) 1
    · rw [iSup_pos hg1]
      by_cases hgM : g ∈ M.strongDualAnnihilator
      · rw [iSup_pos (show g ∈ {f : StrongDual ℝ E | f ∈ M.strongDualAnnihilator ∧ ‖f‖ ≤ 1} from
          ⟨hgM, mem_closedBall_zero_iff.1 hg1⟩), indicatorFn_of_mem (SetLike.mem_coe.2 hgM),
          sub_zero]
      · rw [iSup_neg (show g ∉ {f : StrongDual ℝ E | f ∈ M.strongDualAnnihilator ∧ ‖f‖ ≤ 1} from
          fun h => hgM h.1), indicatorFn_of_notMem (fun h => hgM (SetLike.mem_coe.1 h)),
          EReal.sub_top]
    · rw [iSup_neg hg1, iSup_neg (show g ∉ {f : StrongDual ℝ E | f ∈ M.strongDualAnnihilator ∧
        ‖f‖ ≤ 1} from fun h => hg1 (mem_closedBall_zero_iff.2 h.2))]
  · by_cases hfM : f ∈ M.strongDualAnnihilator
    · rw [indicatorFn_of_mem (SetLike.mem_coe.2 hfM), sub_zero] at hfx
      exact ⟨f, hfM, hf1, hfx⟩
    · rw [indicatorFn_of_notMem (fun h => hfM (SetLike.mem_coe.1 h)), EReal.sub_top] at hfx
      exact absurd hfx.symm (EReal.coe_ne_bot _)

/-- **Example 4.** Let `φ : E → ℝ` be convex and continuous and `M ⊆ E` a linear subspace. Then
`inf_{x ∈ M} φ x = -min_{f ∈ M^⊥} φ* f`: the identity, and the attainment of the minimum.
Theorem 1.12 with `ψ = I_M`, in the backbone's subspace form
`iInf_mem_submodule_eq_neg_iInf_mem_polarCone`. -/
theorem example_1_4 {φ : E → ℝ} (hφ : ConvexOn ℝ univ φ) (hc : Continuous φ)
    (M : Submodule ℝ E) :
    (⨅ x ∈ M, ((φ x : ℝ) : EReal)) =
        -(⨅ f ∈ M.strongDualAnnihilator, conjugate (fun x => ((φ x : ℝ) : EReal)) f) ∧
      ∃ f ∈ M.strongDualAnnihilator, conjugate (fun x => ((φ x : ℝ) : EReal)) f =
        ⨅ g ∈ M.strongDualAnnihilator, conjugate (fun x => ((φ x : ℝ) : EReal)) g := by
  have hex : IsExactSum (dualPairing E) (fun x => ((φ x : ℝ) : EReal)) (indicatorFn (M : Set E)) :=
    IsExactSum.of_continuousAt hφ.convexFn_coe (proper_coe φ) (convexFn_indicatorFn.2 M.convex)
      (proper_indicatorFn.2 ⟨0, M.zero_mem⟩) (x₀ := 0) (EReal.coe_lt_top _)
      (by rw [dom_indicatorFn]; exact M.zero_mem) (EReal.continuous_coe_iff.2 hc).continuousAt
  have hpol := polarCone_dualPairing_eq.1 M
  constructor
  · have h := iInf_mem_submodule_eq_neg_iInf_mem_polarCone hex
    rw [hpol] at h
    exact h
  · have h := exists_mem_neg_polarCone_conj_eq_iInf hex (fun _ ha => smul_coe_submodule M ha)
      ⟨0, M.zero_mem⟩
    rw [neg_polarCone_coe_submodule, hpol] at h
    exact h

end Brezis.Chapter01
