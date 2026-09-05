import Numlib.Analysis.Convex.SaddlePoint

/-!
# Atkinson–Han §8.6: mixed and dual formulations

Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009.

Almost all of §8.6 is a worked derivation for the model Dirichlet problem for the Poisson
equation and needs `H¹₀(Ω)`, `L²(Ω)^d` and `H(div; Ω)`; two items are abstract, and they are the
contents of this file.  `A` and `B` are bare sets and `L` an arbitrary real function, so nothing
here needs a function space.

## Main results

* `IsSaddlePoint` — Definition 8.6.1, (8.6.10), in the book's own shape
  `L(u, q) ≤ L(u, p) ≤ L(v, p)`, with `isSaddlePoint_iff` identifying it with the backbone's
  `_root_.IsSaddlePoint`.
* `primalObjective`, `dualObjective` — the primal problem (8.6.12) `min_{v ∈ A} sup_{q ∈ B} L(v, q)`
  and the dual problem (8.6.13) `max_{q ∈ B} inf_{v ∈ A} L(v, q)`.
* `proposition_8_6_2` — (8.6.11): `(u, p)` is a saddle point exactly when `u` solves the primal
  problem, `p` solves the dual problem, and the common extremal value is `L(u, p)`; the equality
  of the two extremal values is (8.6.14), which `equation_8_6_14` states on its own.

The two `BddAbove`/`BddBelow` hypotheses are not decoration: `sSup` and `sInf` take junk values on
unbounded sets, and without them the extremal problems say nothing.

## Not formalized here

* Theorem 8.6.3 (Ekeland–Temam), the existence of a saddle point for a convex–concave
  lower/upper semicontinuous `L` on closed convex subsets of reflexive Banach spaces: it needs
  weak compactness of bounded sets in a reflexive space, which Mathlib does not have.
* The abstract mixed formulation (8.6.21)–(8.6.22): the book states the problem and refers to
  Brezzi for every theorem about it, so there is nothing to formalize.
* The model-problem computations (8.6.1)–(8.6.20) and Exercises 8.6.1–8.6.4, all of which are
  about `H¹₀(Ω)`, `H(div; Ω)` or the Stokes equations.
-/

namespace AtkinsonHan.Ch08

variable {α β : Type*} {L : α → β → ℝ} {A : Set α} {B : Set β} {u : α} {p : β}

/-- **Definition 8.6.1**, (8.6.10).  A pair `(u, p) ∈ A × B` is a *saddle point* of
`L : A × B → ℝ` when

  `L(u, q) ≤ L(u, p) ≤ L(v, p)`  for every `(v, q) ∈ A × B`,

so that `p` maximizes `L(u, ·)` over `B` while `u` minimizes `L(·, p)` over `A`.  The book writes
the two inequalities as one chain, which is what is transcribed here;
`isSaddlePoint_iff` splits it into the backbone's four fields. -/
def IsSaddlePoint (L : α → β → ℝ) (A : Set α) (B : Set β) (u : α) (p : β) : Prop :=
  u ∈ A ∧ p ∈ B ∧ ∀ v ∈ A, ∀ q ∈ B, L u q ≤ L u p ∧ L u p ≤ L v p

/-- Definition 8.6.1 is the backbone's `_root_.IsSaddlePoint`.  The book's chain quantifies over
`v ∈ A` and `q ∈ B` at once; splitting it is legitimate because `u ∈ A` and `p ∈ B` make each
half instantiable on its own. -/
theorem isSaddlePoint_iff : IsSaddlePoint L A B u p ↔ _root_.IsSaddlePoint L A B u p := by
  constructor
  · rintro ⟨hu, hp, h⟩
    exact ⟨hu, hp, fun q hq => (h u hu q hq).1, fun v hv => (h v hv p hp).2⟩
  · intro h
    exact ⟨h.mem_left, h.mem_right,
      fun v hv q hq => ⟨h.apply_le q hq, h.le_apply v hv⟩⟩

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
  (isSaddlePoint_iff.mp h).sSup_image_eq

/-- At a saddle point the dual objective takes the value `L(u, p)`: `inf_{v ∈ A} L(v, p)` is
attained at `v = u`. -/
theorem dualObjective_eq (h : IsSaddlePoint L A B u p) : dualObjective L A p = L u p :=
  (isSaddlePoint_iff.mp h).sInf_image_eq

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
    exact ⟨⟨primalObjective_eq h, h'.isLeast_sSup hbddA⟩,
      dualObjective_eq h, h'.isGreatest_sInf hbddB⟩
  · rintro ⟨⟨hpu, hleast⟩, hdp, hgreatest⟩
    refine isSaddlePoint_iff.mpr
      (isSaddlePoint_of_isLeast_of_isGreatest hu hp (hbddA u hu) (hbddB p hp) ?_ ?_ ?_)
    · have h1 : IsLeast (primalObjective L B '' A) (primalObjective L B u) := by
        rw [hpu]; exact hleast
      exact h1
    · have h2 : IsGreatest (dualObjective L A '' B) (dualObjective L A p) := by
        rw [hdp]; exact hgreatest
      exact h2
    · exact hleast.csInf_eq.trans hgreatest.csSup_eq.symm

/-- **(8.6.14)**: at a saddle point the primal and the dual problem have the same value, which is
`L(u, p)`.  There is no duality gap. -/
theorem equation_8_6_14 (h : IsSaddlePoint L A B u p) (hbddA : ∀ v ∈ A, BddAbove (L v '' B))
    (hbddB : ∀ q ∈ B, BddBelow ((fun v => L v q) '' A)) :
    sInf (primalObjective L B '' A) = sSup (dualObjective L A '' B) := by
  have h' := isSaddlePoint_iff.mp h
  exact (h'.isLeast_sSup hbddA).csInf_eq.trans ((h'.isGreatest_sInf hbddB).csSup_eq).symm

end AtkinsonHan.Ch08
