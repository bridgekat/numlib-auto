import Numlib.Analysis.Convex.Saddle.Real
import Numlib.Variational.Minimax
import NumlibSurface.AtkinsonHan.Chapter03.Section03

/-!
# Atkinson–Han §8.6: mixed and dual formulations

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §8.6.

Almost all of §8.6 is a worked derivation for the model Dirichlet problem for the Poisson
equation and needs `H¹₀(Ω)`, `L²(Ω)^d` and `H(div; Ω)`; three items are abstract, and they are the
contents of this file.  `A` and `B` are bare sets and `L` an arbitrary real function, so nothing
here needs a function space until Theorem 8.6.3, whose `V` and `Q` are reflexive Banach spaces.

## Main results

* `IsSaddlePoint` — Definition 8.6.1, (8.6.10), in the book's own shape
  `L(u, q) ≤ L(u, p) ≤ L(v, p)`, with `isSaddlePoint_iff` identifying it with the backbone's
  `ConvexAnalysis.IsSaddlePointOn` and `isSaddlePoint_iff_isSaddlePointOn` with Mathlib's
  `IsSaddlePointOn`.  The backbone's Rockafellar convention maximizes the first variable and
  minimizes the second, with an `EReal`-valued kernel, so the book's `(u, p)` on `A × B` is the
  backbone's `(p, u)` on `B × A` for the transposed kernel `(q, v) ↦ L(v, q)`; Mathlib's
  `IsSaddlePointOn A B L u p` is the book's convention, `L(u, q) ≤ L(v, p)` for all `v ∈ A`,
  `q ∈ B`.
* `primalObjective`, `dualObjective` — the primal problem (8.6.12) `min_{v ∈ A} sup_{q ∈ B} L(v, q)`
  and the dual problem (8.6.13) `max_{q ∈ B} inf_{v ∈ A} L(v, q)`.
* `proposition_8_6_2` — (8.6.11): `(u, p)` is a saddle point exactly when `u` solves the primal
  problem, `p` solves the dual problem, and the common extremal value is `L(u, p)`; the equality
  of the two extremal values is (8.6.14), which `equation_8_6_14` states on its own.
* `theorem_8_6_3` — the existence of a saddle point (Ekeland–Temam): `V`, `Q` reflexive, `A`, `B`
  nonempty closed convex, `L` convex lower semicontinuous in `v` and concave upper semicontinuous
  in `q`, and the two coercivity conditions (f) and (g).  The uniqueness clauses are
  `theorem_8_6_3_unique_fst` and `theorem_8_6_3_unique_snd`, and the variants with (f) replaced by
  (f)' or (g) by (g)' are `theorem_8_6_3_sup` and `theorem_8_6_3_inf`.  All of them are the
  backbone's `Numlib.Variational.Minimax`: Sion's minimax theorem in the weak topologies of the
  two spaces, where closed bounded convex sets are compact by Kakutani's theorem, then truncation
  to a large ball for the coercive cases.

The two `BddAbove`/`BddBelow` hypotheses of Proposition 8.6.2 are not decoration: `sSup` and
`sInf` take junk values on unbounded sets, and without them the extremal problems say nothing.

## Theorem 8.6.3

The book states the theorem without proof, citing Ekeland–Temam.  Its hypotheses are transcribed
as printed.  Reflexivity (a) is `NormedSpace.IsReflexive ℝ V`, the book's Definition 2.7.4 by
`Chapter02.definition_2_7_4_iff_isReflexive`, and "Banach" needs no hypothesis of its own, a
reflexive space being complete.  The limit in (f), "`L(v, q₀) → ∞` as `‖v‖ → ∞`, `v ∈ A`", is
`Chapter03.definition_3_3_9 A (L · q₀)`, the book's Definition 3.3.9 of a coercive functional;
the limit in (g) is the same limit to `-∞`, spelled out with `Filter.atBot`.  The suprema and
infima of (f)' and (g)' are taken in `EReal`, because `sup_{q ∈ B} L(v, q)` may well be `+∞` for
some `v` and the book's condition allows it.

The book says "the same conclusions hold when (f) is replaced by (f)' **or** when (g) is replaced
by (g)'", and the disjunction is essential: with (f)' and (g)' assumed *together* the statement is
false — `L(v, q) = q - v` on `ℝ × ℝ` has `sup_q L(v, q) = +∞` and `inf_v L(v, q) = -∞` throughout,
so both limits hold, and no saddle point.

## Not formalized here

* The abstract mixed formulation (8.6.21)–(8.6.22): the book states the problem and refers to
  Brezzi for every theorem about it, so there is nothing to formalize.
* The model-problem computations (8.6.1)–(8.6.20) and Exercises 8.6.1–8.6.4, all of which are
  about `H¹₀(Ω)`, `H(div; Ω)` or the Stokes equations.
-/

open Bornology Filter Topology

namespace AtkinsonHan.Chapter08

variable {α β : Type*} {L : α → β → ℝ} {A : Set α} {B : Set β} {u : α} {p : β}

/-- **Definition 8.6.1**, (8.6.10).  A pair `(u, p) ∈ A × B` is a *saddle point* of
`L : A × B → ℝ` when

  `L(u, q) ≤ L(u, p) ≤ L(v, p)`  for every `(v, q) ∈ A × B`,

so that `p` maximizes `L(u, ·)` over `B` while `u` minimizes `L(·, p)` over `A`.  The book writes
the two inequalities as one chain, which is what is transcribed here;
`isSaddlePoint_iff` splits it into the backbone's four clauses. -/
def IsSaddlePoint (L : α → β → ℝ) (A : Set α) (B : Set β) (u : α) (p : β) : Prop :=
  u ∈ A ∧ p ∈ B ∧ ∀ v ∈ A, ∀ q ∈ B, L u q ≤ L u p ∧ L u p ≤ L v p

/-- Definition 8.6.1 is the backbone's `ConvexAnalysis.IsSaddlePointOn`, for the transposed
kernel `(q, v) ↦ L(v, q)` read in `EReal`, relative to `B × A`, at the point `(p, u)`: the
backbone maximizes its first variable and minimizes its second, which is the book's convention
with the two variables exchanged.  The book's chain quantifies over `v ∈ A` and `q ∈ B` at once;
splitting it is legitimate because `u ∈ A` and `p ∈ B` make each half instantiable on its own. -/
theorem isSaddlePoint_iff :
    IsSaddlePoint L A B u p ↔
      ConvexAnalysis.IsSaddlePointOn (fun q : β × α => ((L q.2 q.1 : ℝ) : EReal)) B A (p, u) := by
  constructor
  · rintro ⟨hu, hp, h⟩
    exact ⟨hp, hu, fun q hq => EReal.coe_le_coe_iff.2 (h u hu q hq).1,
      fun v hv => EReal.coe_le_coe_iff.2 (h v hv p hp).2⟩
  · rintro ⟨hp, hu, h₁, h₂⟩
    exact ⟨hu, hp, fun v hv q hq =>
      ⟨EReal.coe_le_coe_iff.1 (h₁ q hq), EReal.coe_le_coe_iff.1 (h₂ v hv)⟩⟩

/-- Definition 8.6.1 is Mathlib's `IsSaddlePointOn A B L u p` — the single inequality
`L(u, q) ≤ L(v, p)` for all `v ∈ A`, `q ∈ B`, which does not record `u ∈ A` and `p ∈ B` —
together with the two memberships.  The book's chain gives the single inequality by transitivity,
and the single inequality gives the chain by taking `v = u`, respectively `q = p`. -/
theorem isSaddlePoint_iff_isSaddlePointOn :
    IsSaddlePoint L A B u p ↔ u ∈ A ∧ p ∈ B ∧ IsSaddlePointOn A B L u p := by
  constructor
  · rintro ⟨hu, hp, h⟩
    exact ⟨hu, hp, fun v hv q hq => (h v hv q hq).1.trans (h v hv q hq).2⟩
  · rintro ⟨hu, hp, h⟩
    exact ⟨hu, hp, fun v hv q hq => ⟨h u hu q hq, h v hv p hp⟩⟩

/-- The objective of the primal problem (8.6.12): `J(v) = sup_{q ∈ B} L(v, q)`, to be minimized
over `A`. -/
noncomputable def primalObjective (L : α → β → ℝ) (B : Set β) (v : α) : ℝ := sSup (L v '' B)

/-- The objective of the dual problem (8.6.13): `G(q) = inf_{v ∈ A} L(v, q)`, to be maximized
over `B`. -/
noncomputable def dualObjective (L : α → β → ℝ) (A : Set α) (q : β) : ℝ :=
  sInf ((fun v => L v q) '' A)

/-- At a saddle point the primal objective takes the value `L(u, p)`: `sup_{q ∈ B} L(u, q)` is
attained at `q = p`. -/
theorem primalObjective_eq (h : IsSaddlePoint L A B u p) : primalObjective L B u = L u p :=
  (isSaddlePoint_iff.mp h).sSup_image_coe_eq

/-- At a saddle point the dual objective takes the value `L(u, p)`: `inf_{v ∈ A} L(v, p)` is
attained at `v = u`. -/
theorem dualObjective_eq (h : IsSaddlePoint L A B u p) : dualObjective L A p = L u p :=
  (isSaddlePoint_iff.mp h).sInf_image_coe_eq

/-- **Proposition 8.6.2**, (8.6.11).  A pair `(u, p) ∈ A × B` is a saddle point of `L` if and only
if `u` solves the primal problem (8.6.12), `p` solves the dual problem (8.6.13), and the common
extremal value is `L(u, p)`:

  `min_{v ∈ A} sup_{q ∈ B} L(v, q) = L(u, p) = max_{q ∈ B} inf_{v ∈ A} L(v, q)`,

the minimum attained at `u` and the maximum at `p`.  The equality of the two extremal values is
(8.6.14), which is `equation_8_6_14`. -/
theorem proposition_8_6_2 (hu : u ∈ A) (hp : p ∈ B) (hbddA : ∀ v ∈ A, BddAbove (L v '' B))
    (hbddB : ∀ q ∈ B, BddBelow ((fun v => L v q) '' A)) :
    IsSaddlePoint L A B u p ↔
      (primalObjective L B u = L u p ∧ IsLeast (primalObjective L B '' A) (L u p)) ∧
        dualObjective L A p = L u p ∧ IsGreatest (dualObjective L A '' B) (L u p) := by
  constructor
  · intro h
    have h' := isSaddlePoint_iff.mp h
    exact ⟨⟨primalObjective_eq h, h'.isLeast_sSup_coe hbddA⟩,
      dualObjective_eq h, h'.isGreatest_sInf_coe hbddB⟩
  · rintro ⟨⟨hpu, hleast⟩, hdp, hgreatest⟩
    refine isSaddlePoint_iff.mpr
      (ConvexAnalysis.isSaddlePointOn_coe_of_isLeast_of_isGreatest hp hu (hbddA u hu) (hbddB p hp)
        ?_ ?_ ?_)
    · change IsLeast (primalObjective L B '' A) (primalObjective L B u)
      rw [hpu]
      exact hleast
    · change IsGreatest (dualObjective L A '' B) (dualObjective L A p)
      rw [hdp]
      exact hgreatest
    · exact hleast.csInf_eq.trans hgreatest.csSup_eq.symm

/-- **(8.6.14)**: at a saddle point the primal and the dual problem have the same value, which is
`L(u, p)`.  There is no duality gap. -/
theorem equation_8_6_14 (h : IsSaddlePoint L A B u p) (hbddA : ∀ v ∈ A, BddAbove (L v '' B))
    (hbddB : ∀ q ∈ B, BddBelow ((fun v => L v q) '' A)) :
    sInf (primalObjective L B '' A) = sSup (dualObjective L A '' B) :=
  (isSaddlePoint_iff.mp h).sInf_sSup_eq_sSup_sInf_coe hbddA hbddB

/-! ### Theorem 8.6.3: existence and uniqueness of a saddle point -/

section Existence

variable {V Q : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Q]
  [NormedSpace ℝ Q] {L : V → Q → ℝ} {A : Set V} {B : Set Q}

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
/-- Condition (f) of Theorem 8.6.3, "`A` is bounded, or `L(v, q₀) → ∞` as `‖v‖ → ∞` in `A` for
some `q₀ ∈ B`", read as the backbone's hypothesis: some slice `L(·, q₀)` is coercive on `A`, a
bounded set making every functional coercive vacuously.  `B` must be nonempty for the bounded
case to name a `q₀`. -/
theorem exists_isCoerciveFunctionalOn_of_bounded_or_tendsto (hBne : B.Nonempty)
    (hf : IsBounded A ∨ ∃ q₀ ∈ B, Chapter03.definition_3_3_9 A fun v => L v q₀) :
    ∃ q₀ ∈ B, IsCoerciveFunctionalOn (fun v => L v q₀) A := by
  rcases hf with hbd | ⟨q₀, hq₀, h⟩
  · obtain ⟨q₀, hq₀⟩ := hBne
    exact ⟨q₀, hq₀, IsCoerciveFunctionalOn.of_isBounded hbd⟩
  · exact ⟨q₀, hq₀, (Chapter03.definition_3_3_9_iff _ _).1 h⟩

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- Condition (g) of Theorem 8.6.3, "`B` is bounded, or `L(v₀, q) → -∞` as `‖q‖ → ∞` in `B` for
some `v₀ ∈ A`", read as the backbone's hypothesis: some slice `-L(v₀, ·)` is coercive on `B`. -/
theorem exists_isCoerciveFunctionalOn_neg_of_bounded_or_tendsto (hAne : A.Nonempty)
    (hg : IsBounded B ∨ ∃ v₀ ∈ A, Tendsto (fun q => L v₀ q) (comap norm atTop ⊓ 𝓟 B) atBot) :
    ∃ v₀ ∈ A, IsCoerciveFunctionalOn (fun q => -L v₀ q) B := by
  rcases hg with hbd | ⟨v₀, hv₀, h⟩
  · obtain ⟨v₀, hv₀⟩ := hAne
    exact ⟨v₀, hv₀, IsCoerciveFunctionalOn.of_isBounded hbd⟩
  · refine ⟨v₀, hv₀, (Chapter03.definition_3_3_9_iff B fun q => -L v₀ q).1 ?_⟩
    exact tendsto_neg_atBot_atTop.comp h

omit [NormedSpace ℝ V] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
/-- Condition (f)' of Theorem 8.6.3, "`A` is bounded, or `sup_{q ∈ B} L(v, q) → ∞` as `‖v‖ → ∞`
in `A`", the supremum taken in `EReal`, read as the backbone's hypothesis: beyond some radius
every `v ∈ A` has a `q ∈ B` with `L(v, q) ≥ M`. -/
theorem forall_exists_le_of_bounded_or_biSup_tendsto
    (hf : IsBounded A ∨
      Tendsto (fun v => ⨆ q ∈ B, (L v q : EReal)) (comap norm atTop ⊓ 𝓟 A) atTop) :
    ∀ M : ℝ, ∃ R : ℝ, ∀ v ∈ A, R ≤ ‖v‖ → ∃ q ∈ B, M ≤ L v q := by
  intro M
  rcases hf with hbd | h
  · obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hbd
    exact ⟨C + 1, fun v hv hRv => absurd (hC v hv) (by linarith)⟩
  · have := tendsto_atTop.1 h ((M + 1 : ℝ) : EReal)
    rw [eventually_inf_principal, eventually_comap, eventually_atTop] at this
    obtain ⟨R, hR⟩ := this
    refine ⟨R, fun v hv hRv => ?_⟩
    have := lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (lt_add_one M)) (hR ‖v‖ hRv v rfl hv)
    simp only [lt_iSup_iff, EReal.coe_lt_coe_iff] at this
    obtain ⟨q, hq, hMq⟩ := this
    exact ⟨q, hq, hMq.le⟩

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℝ Q] in
/-- Condition (g)' of Theorem 8.6.3, "`B` is bounded, or `inf_{v ∈ A} L(v, q) → -∞` as
`‖q‖ → ∞` in `B`", the infimum taken in `EReal`, read as the backbone's hypothesis. -/
theorem forall_exists_le_of_bounded_or_biInf_tendsto
    (hg : IsBounded B ∨
      Tendsto (fun q => ⨅ v ∈ A, (L v q : EReal)) (comap norm atTop ⊓ 𝓟 B) atBot) :
    ∀ M : ℝ, ∃ R : ℝ, ∀ q ∈ B, R ≤ ‖q‖ → ∃ v ∈ A, L v q ≤ M := by
  intro M
  rcases hg with hbd | h
  · obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hbd
    exact ⟨C + 1, fun q hq hRq => absurd (hC q hq) (by linarith)⟩
  · have := tendsto_atBot.1 h ((M - 1 : ℝ) : EReal)
    rw [eventually_inf_principal, eventually_comap, eventually_atTop] at this
    obtain ⟨R, hR⟩ := this
    refine ⟨R, fun q hq hRq => ?_⟩
    have := lt_of_le_of_lt (hR ‖q‖ hRq q rfl hq) (EReal.coe_lt_coe_iff.2 (sub_one_lt M))
    simp only [iInf_lt_iff, EReal.coe_lt_coe_iff] at this
    obtain ⟨v, hv, hvM⟩ := this
    exact ⟨v, hv, hvM.le⟩

variable [NormedSpace.IsReflexive ℝ V] [NormedSpace.IsReflexive ℝ Q]

/-- **Theorem 8.6.3**, existence.  Assume

(a) `V` and `Q` are reflexive Banach spaces (`NormedSpace.IsReflexive ℝ V`, the book's
    Definition 2.7.4 by `Chapter02.definition_2_7_4_iff_isReflexive`; completeness follows);
(b) `A ⊆ V` is nonempty, closed and convex;
(c) `B ⊆ Q` is nonempty, closed and convex;
(d) for every `q ∈ B`, `v ↦ L(v, q)` is convex and lower semicontinuous on `A`;
(e) for every `v ∈ A`, `q ↦ L(v, q)` is concave and upper semicontinuous on `B`;
(f) `A` is bounded, or there is `q₀ ∈ B` with `L(v, q₀) → ∞` as `‖v‖ → ∞`, `v ∈ A`
    (`Chapter03.definition_3_3_9`);
(g) `B` is bounded, or there is `v₀ ∈ A` with `L(v₀, q) → -∞` as `‖q‖ → ∞`, `q ∈ B`.

Then `L` has a saddle point `(u, p) ∈ A × B`.  The uniqueness clauses are
`theorem_8_6_3_unique_fst` and `theorem_8_6_3_unique_snd`; (f) may be replaced by (f)'
(`theorem_8_6_3_sup`) or (g) by (g)' (`theorem_8_6_3_inf`).

This is the backbone's `exists_isSaddlePointOn_of_isCoerciveFunctionalOn`: Sion's minimax theorem
applied in the weak topologies of `V` and `Q`, where the truncations of `A` and `B` by a large
closed ball are compact (Kakutani) and the semicontinuity hypotheses persist (Mazur), followed by
the observation that the coercivity conditions keep the saddle point of the truncated problem
strictly inside the ball, where it is a saddle point of the original problem. -/
theorem theorem_8_6_3 (hAne : A.Nonempty) (hAcl : IsClosed A) (hAconv : Convex ℝ A)
    (hBne : B.Nonempty) (hBcl : IsClosed B) (hBconv : Convex ℝ B)
    (hd : ∀ q ∈ B, ConvexOn ℝ A (fun v => L v q) ∧ LowerSemicontinuousOn (fun v => L v q) A)
    (he : ∀ v ∈ A, ConcaveOn ℝ B (L v) ∧ UpperSemicontinuousOn (L v) B)
    (hf : IsBounded A ∨ ∃ q₀ ∈ B, Chapter03.definition_3_3_9 A fun v => L v q₀)
    (hg : IsBounded B ∨ ∃ v₀ ∈ A, Tendsto (fun q => L v₀ q) (comap norm atTop ⊓ 𝓟 B) atBot) :
    ∃ u p, IsSaddlePoint L A B u p := by
  obtain ⟨u, hu, p, hp, h⟩ := exists_isSaddlePointOn_of_isCoerciveFunctionalOn hAcl hAconv hBcl
    hBconv (fun q hq => (hd q hq).1) (fun q hq => (hd q hq).2) (fun v hv => (he v hv).1)
    (fun v hv => (he v hv).2) (exists_isCoerciveFunctionalOn_of_bounded_or_tendsto hBne hf)
    (exists_isCoerciveFunctionalOn_neg_of_bounded_or_tendsto hAne hg)
  exact ⟨u, p, isSaddlePoint_iff_isSaddlePointOn.2 ⟨hu, hp, h⟩⟩

/-- **Theorem 8.6.3**, the variant with (f) replaced by (f)': "`A` is bounded, or
`lim_{‖v‖ → ∞, v ∈ A} sup_{q ∈ B} L(v, q) = ∞`", the supremum taken in `EReal` since it may be
`+∞`.  Conditions (a)–(e) and (g) are those of `theorem_8_6_3`.  This is the backbone's
`exists_isSaddlePointOn_of_sup_coercive`: only `A` is truncated, and the bound
`L(u, q) ≤ L(v₀, p) ≤ max_{q ∈ B} L(v₀, q)` for the truncated saddle point `(u, p)` keeps `u`
inside a fixed ball. -/
theorem theorem_8_6_3_sup (hAne : A.Nonempty) (hAcl : IsClosed A) (hAconv : Convex ℝ A)
    (hBne : B.Nonempty) (hBcl : IsClosed B) (hBconv : Convex ℝ B)
    (hd : ∀ q ∈ B, ConvexOn ℝ A (fun v => L v q) ∧ LowerSemicontinuousOn (fun v => L v q) A)
    (he : ∀ v ∈ A, ConcaveOn ℝ B (L v) ∧ UpperSemicontinuousOn (L v) B)
    (hf : IsBounded A ∨
      Tendsto (fun v => ⨆ q ∈ B, (L v q : EReal)) (comap norm atTop ⊓ 𝓟 A) atTop)
    (hg : IsBounded B ∨ ∃ v₀ ∈ A, Tendsto (fun q => L v₀ q) (comap norm atTop ⊓ 𝓟 B) atBot) :
    ∃ u p, IsSaddlePoint L A B u p := by
  obtain ⟨u, hu, p, hp, h⟩ := exists_isSaddlePointOn_of_sup_coercive hAcl hAconv hBne hBcl
    hBconv (fun q hq => (hd q hq).1) (fun q hq => (hd q hq).2) (fun v hv => (he v hv).1)
    (fun v hv => (he v hv).2) (forall_exists_le_of_bounded_or_biSup_tendsto hf)
    (exists_isCoerciveFunctionalOn_neg_of_bounded_or_tendsto hAne hg)
  exact ⟨u, p, isSaddlePoint_iff_isSaddlePointOn.2 ⟨hu, hp, h⟩⟩

/-- **Theorem 8.6.3**, the variant with (g) replaced by (g)': "`B` is bounded, or
`lim_{‖q‖ → ∞, q ∈ B} inf_{v ∈ A} L(v, q) = -∞`", the infimum taken in `EReal`.  Conditions
(a)–(f) are those of `theorem_8_6_3`.  This is the backbone's
`exists_isSaddlePointOn_of_inf_coercive`, the transposed form of `theorem_8_6_3_sup`.  (f)' and
(g)' cannot be assumed together: see the module documentation. -/
theorem theorem_8_6_3_inf (hAne : A.Nonempty) (hAcl : IsClosed A) (hAconv : Convex ℝ A)
    (hBne : B.Nonempty) (hBcl : IsClosed B) (hBconv : Convex ℝ B)
    (hd : ∀ q ∈ B, ConvexOn ℝ A (fun v => L v q) ∧ LowerSemicontinuousOn (fun v => L v q) A)
    (he : ∀ v ∈ A, ConcaveOn ℝ B (L v) ∧ UpperSemicontinuousOn (L v) B)
    (hf : IsBounded A ∨ ∃ q₀ ∈ B, Chapter03.definition_3_3_9 A fun v => L v q₀)
    (hg : IsBounded B ∨
      Tendsto (fun q => ⨅ v ∈ A, (L v q : EReal)) (comap norm atTop ⊓ 𝓟 B) atBot) :
    ∃ u p, IsSaddlePoint L A B u p := by
  obtain ⟨u, hu, p, hp, h⟩ := exists_isSaddlePointOn_of_inf_coercive hAne hAcl hAconv hBcl
    hBconv (fun q hq => (hd q hq).1) (fun q hq => (hd q hq).2) (fun v hv => (he v hv).1)
    (fun v hv => (he v hv).2) (exists_isCoerciveFunctionalOn_of_bounded_or_tendsto hBne hf)
    (forall_exists_le_of_bounded_or_biInf_tendsto hg)
  exact ⟨u, p, isSaddlePoint_iff_isSaddlePointOn.2 ⟨hu, hp, h⟩⟩

end Existence

section Uniqueness

variable {V Q : Type*} [AddCommMonoid V] [SMul ℝ V] [AddCommMonoid Q] [SMul ℝ Q]
  {L : V → Q → ℝ} {A : Set V} {B : Set Q} {u u' : V} {p p' : Q}

omit [AddCommMonoid Q] [SMul ℝ Q] in
/-- **Theorem 8.6.3**, uniqueness of the first component: if the convexity in (d) is strengthened
to strict convexity — `v ↦ L(v, q)` strictly convex on `A` for every `q ∈ B` — then the first
component `u` of a saddle point is unique.  Only the strict convexity of `L(·, p)` at the second
component `p` of one of the two saddle points is used
(`IsSaddlePointOn.fst_eq_of_strictConvexOn`); no topology enters. -/
theorem theorem_8_6_3_unique_fst (hd : ∀ q ∈ B, StrictConvexOn ℝ A fun v => L v q)
    (h : IsSaddlePoint L A B u p) (h' : IsSaddlePoint L A B u' p') : u = u' := by
  obtain ⟨hu, hp, h⟩ := isSaddlePoint_iff_isSaddlePointOn.1 h
  obtain ⟨hu', hp', h'⟩ := isSaddlePoint_iff_isSaddlePointOn.1 h'
  exact h.fst_eq_of_strictConvexOn (hd p hp) hu hu' hp hp' h'

omit [AddCommMonoid V] [SMul ℝ V] in
/-- **Theorem 8.6.3**, uniqueness of the second component: if the concavity in (e) is strengthened
to strict concavity — `q ↦ L(v, q)` strictly concave on `B` for every `v ∈ A` — then the second
component `p` of a saddle point is unique (`IsSaddlePointOn.snd_eq_of_strictConcaveOn`). -/
theorem theorem_8_6_3_unique_snd (he : ∀ v ∈ A, StrictConcaveOn ℝ B (L v))
    (h : IsSaddlePoint L A B u p) (h' : IsSaddlePoint L A B u' p') : p = p' := by
  obtain ⟨hu, hp, h⟩ := isSaddlePoint_iff_isSaddlePointOn.1 h
  obtain ⟨hu', hp', h'⟩ := isSaddlePoint_iff_isSaddlePointOn.1 h'
  exact h.snd_eq_of_strictConcaveOn (he u hu) hu hu' hp hp' h'

end Uniqueness

end AtkinsonHan.Chapter08
