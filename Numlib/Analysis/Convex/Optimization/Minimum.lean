import Numlib.Analysis.Convex.Polyhedral.Function
import Numlib.Analysis.Convex.Polyhedral.Recession
import Numlib.Analysis.Convex.Recession.Closedness
import Numlib.Analysis.Convex.Recession.Conjugate
import Numlib.Analysis.Convex.Subgradient.Approx
import Numlib.Analysis.Convex.Subgradient.Calculus
import Numlib.Analysis.Convex.Subgradient.Existence
import Numlib.Analysis.Convex.Subgradient.Uniqueness

/-!
# The minimum of a convex function

A point `x` minimises `f` exactly when `0 ∈ ∂f x`, the subgradient inequality read at `y = 0`; that
is why subgradients are the engine here. Dually `inf f = -f*(0)` with no hypothesis at all, and for
closed proper convex `f` the minimum set *is* `∂f*(0)`, so every question about minimisers becomes
one about the conjugate near the origin. Existence comes from recession: a closed proper convex
function with no direction of recession has compact level sets and attains its infimum; that
relaxes to a constrained problem, with a further weakening when the constraint set is
polyhedral.

## Main definitions

* `argmin f` — the *minimum set* `{x | ∀ z, f x ≤ f z}`.

## Main results

* `mem_argmin_iff_zero_mem_subgradient` — `x` minimises `f` exactly when `0 ∈ ∂f x`.
* `conj_zero_eq_neg_iInf`, `argmin_eq_subgradient_conj_zero`,
  `iInf_ne_bot_and_argmin_eq_empty_iff`,
  `argmin_nonempty_and_isBounded_iff_zero_mem_interior_dom_conj`, `supportFn_setOf_le`,
  `argmin_eq_singleton_iff_hasGradientAtFn_conj_zero`, `supportFn_argmin`,
  `recessionCone_setOf_le_eq_polarCone_dom_conj`, `iInf_supportFn_setOf_le` — the minimum set and
  the optimal value read off the conjugate at the origin (Theorem 27.1 in [^1], clauses (a)–(h)).
* `isCompact_setOf_le` — a level set of a closed proper convex function with no direction of
  recession is compact; `argmin_nonempty_of_recessionConeFn_eq_zero`,
  `isCompact_argmin_of_recessionConeFn_eq_zero`, `exists_pos_forall_exists_mem_argmin_dist_lt` —
  existence of a minimiser, and well-posedness (Theorem 27.2 in [^1]); `tendsto_infDist_argmin`
  and `tendsto_of_argmin_eq_singleton` — the behaviour of minimising nets.
* `exists_forall_le_of_recessionConeFn_inter_eq_zero`,
  `exists_forall_le_of_inter_subset_constancySpace_inter_linealitySpace`,
  `exists_forall_le_of_polyhedral_of_inter_subset_constancySpace` — attainment over a closed convex
  set in its basic, general and polyhedral forms (Theorem 27.3 in [^1]), with
  `argmin_nonempty_of_polyhedralFn` for a polyhedral objective.
* `le_of_mem_subgradient_of_neg_mem_normalCone`, `exists_mem_subgradient_neg_mem_normalCone` — the
  optimality condition for minimising over a convex set, sufficiency and necessity.
* `argmin_sepSum`, `dom_sepSum` — a **separable** objective `x ↦ ∑ᵢ hᵢ(xᵢ)` on a dependent finite
  product is minimised coordinatewise: the *decomposition principle*.

## Implementation notes

The minimum set is `{x | ∀ z, f x ≤ f z}` rather than `IsMinOn f Set.univ`, because that unfolds to
the subgradient inequality at `y = 0`; `mem_argmin_iff_isMinOn` bridges to Mathlib. Necessity of
the optimality condition is stated against `IsExactSum B h (indicatorFn C)`, which both of the
book's hypotheses instantiate. Minimising results are stated for an arbitrary filter where the book
uses sequences, except `isBounded_range_of_tendsto_iInf`, whose conclusion is about a range.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §27. Both level-set
  formulas of clause (i) are in `Duality/Level.lean`.
-/

open Set Pointwise

namespace ConvexAnalysis

/-! ### The minimum set -/

section Defs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x : E}

/-- The **minimum set** of `f`: the points where `f` attains its infimum. Rockafellar's
`lev_{inf f} f`. -/
def argmin (f : E → EReal) : Set E := {x | ∀ z, f x ≤ f z}

omit [AddCommGroup E] [Module ℝ E] in
theorem mem_argmin_iff : x ∈ argmin f ↔ ∀ z, f x ≤ f z := Iff.rfl

omit [AddCommGroup E] [Module ℝ E] in
theorem mem_argmin_iff_isMinOn : x ∈ argmin f ↔ IsMinOn f Set.univ x := by
  rw [isMinOn_univ_iff]
  exact Iff.rfl

omit [AddCommGroup E] [Module ℝ E] in
theorem mem_argmin_iff_le_iInf : x ∈ argmin f ↔ f x ≤ ⨅ z, f z := le_iInf_iff.symm

omit [AddCommGroup E] [Module ℝ E] in
/-- The infimum of `f` is its value at any minimiser. -/
theorem iInf_eq_of_mem_argmin {a : E} (ha : a ∈ argmin f) : (⨅ z, f z) = f a :=
  le_antisymm (iInf_le _ _) (mem_argmin_iff_le_iInf.1 ha)

omit [AddCommGroup E] [Module ℝ E] in
/-- A point minimises exactly when its value *is* the infimum. The equational form of
`mem_argmin_iff_le_iInf`, which is what a statement identifying an optimal value with `inf F 0`
wants to rewrite with. -/
theorem mem_argmin_iff_eq_iInf : x ∈ argmin f ↔ f x = ⨅ z, f z :=
  ⟨fun h => (iInf_eq_of_mem_argmin h).symm, fun h => mem_argmin_iff_le_iInf.2 h.le⟩

omit [AddCommGroup E] [Module ℝ E] in
/-- Rockafellar's `lev_{inf f} f`: once the infimum is attained and finite, the minimum set is
literally a level set of `f`. -/
theorem argmin_eq_setOf_le {a : E} (ha : a ∈ argmin f) {μ : ℝ} (hμ : f a = (μ : EReal)) :
    argmin f = {z : E | f z ≤ (μ : EReal)} := by
  ext z
  constructor
  · intro hz
    rw [← hμ]
    exact hz a
  · intro hz w
    rw [Set.mem_ofPred_eq, ← hμ] at hz
    exact le_trans hz (ha w)

/-- The **maximum set** of `g`: the points where `g` attains its supremum. The concave mirror of
`argmin`, and what "optimal solution" means for a concave program. -/
def argmax (g : E → EReal) : Set E := {x | ∀ z, g z ≤ g x}

omit [AddCommGroup E] [Module ℝ E] in
theorem mem_argmax_iff {g : E → EReal} : x ∈ argmax g ↔ ∀ z, g z ≤ g x := Iff.rfl

omit [AddCommGroup E] [Module ℝ E] in
/-- A point maximises exactly when its value *is* the supremum. The mirror of
`mem_argmin_iff_eq_iInf`, and the step every statement of the form "`v` is an optimal solution to
the concave program `(P*)`" pays: `argmax` is a family of inequalities and the dual optimal value is
a supremum. -/
theorem mem_argmax_iff_eq_iSup {g : E → EReal} : x ∈ argmax g ↔ g x = ⨆ z, g z :=
  ⟨fun h => le_antisymm (le_iSup g x) (iSup_le h), fun h z => by rw [h]; exact le_iSup g z⟩

omit [AddCommGroup E] [Module ℝ E] in
/-- Maximising `g` is minimising `-g`. -/
theorem argmax_eq_argmin_neg (g : E → EReal) : argmax g = argmin fun z => -(g z) :=
  Set.ext fun _ => forall_congr' fun _ => EReal.neg_le_neg_iff.symm

/-- Minimising is `0 ∈ ∂f x`, by the definition of a subgradient. -/
theorem mem_argmin_iff_zero_mem_subgradient (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) :
    x ∈ argmin f ↔ (0 : F) ∈ subgradient B f x := by
  constructor
  · intro h z; simpa using h z
  · intro h z; simpa using h z

/-- The conjugate at the origin is the negated infimum: `f*(0) = -inf f`. No hypothesis at all. -/
theorem conj_zero_eq_neg_iInf (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) :
    conj B f 0 = -(⨅ x, f x) := by
  rw [EReal.neg_iInf]
  refine iSup_congr fun x => ?_
  simp

/-- The same the other way round: `inf f = -f*(0)`. -/
theorem iInf_eq_neg_conj_zero (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) :
    (⨅ x, f x) = -(conj B f 0) := by
  rw [conj_zero_eq_neg_iInf, neg_neg]

/-- `f` is bounded below exactly when `f*` is finite at the origin. -/
theorem zero_mem_dom_conj_iff (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) :
    (0 : F) ∈ dom (conj B f) ↔ (⊥ : EReal) < ⨅ x, f x := by
  rw [mem_dom, conj_zero_eq_neg_iInf, lt_top_iff_ne_top, bot_lt_iff_ne_bot, ne_eq, ne_eq,
    EReal.neg_eq_top_iff]

/-- The minimum set is convex. -/
theorem convex_argmin (hf : ConvexFn f) : Convex ℝ (argmin f) := by
  rcases eq_or_ne (argmin f) ∅ with hE | hE
  · rw [hE]; exact convex_empty
  · obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 hE
    have hset : argmin f = {z : E | f z ≤ f a} := by
      ext z
      exact ⟨fun hz => hz a, fun hz w => le_trans hz (ha w)⟩
    rw [hset]
    exact hf.convex_le _

/-- **The minimum set transports along a surjection**: `x ↦ g (e x)` is minimised exactly at the
`e`-preimages of the minimisers of `g`. Surjectivity makes the two quantifiers agree and is all the
proof uses; composed with `argmin_sepSum` it is the decomposition principle. -/
theorem argmin_comp_of_surjective {α β : Type*} {g : β → EReal} {e : α → β}
    (he : Function.Surjective e) : argmin (fun x => g (e x)) = e ⁻¹' argmin g := by
  ext x
  exact ⟨fun hx w => by obtain ⟨z, rfl⟩ := he w; exact hx z, fun hx z => hx (e z)⟩

end Defs

/-! ### Separable sums on a finite product

A **separable** objective `x ↦ ∑ᵢ hᵢ(xᵢ)` on a dependent finite product `∀ i, E i` has its minimum
set and its effective domain given coordinatewise. This is the content of the *decomposition
principle*: once a Kuhn–Tucker vector has reduced a program to minimising `h₁ + ⋯ + h_s`
over `C¹ × ⋯ × C^s`, the problem splits into `s` independent problems. Both statements are about
the dependent product itself; no isometry with `ℝⁿ`, no relative interior and no linear structure
enter, since `argmin` and `dom` are order-theoretic. -/

section Pi

variable {ι : Type*} [Fintype ι] {E : ι → Type*} {h : ∀ i, E i → EReal}

/-- **The effective domain of a separable sum is the product of the effective domains**. The only
hypothesis is that no summand takes `⊥`, and it cannot be dropped: since `⊥ + ⊤ = ⊥`, a sum can be
finite while a summand is `+∞`, which breaks `⊆`. The `⊇` direction is unconditional. -/
theorem dom_sepSum (hb : ∀ i (z : E i), h i z ≠ ⊥) :
    dom (fun x : ∀ i, E i => ∑ i, h i (x i)) = univ.pi fun i => dom (h i) := by
  ext x
  constructor
  · intro hx i _
    exact lt_top_iff_ne_top.2
      (EReal.forall_ne_top_of_sum_ne_top _ _ (fun j _ => hb j (x j))
        (lt_top_iff_ne_top.1 hx) i (Finset.mem_univ i))
  · intro hx
    choose c hc using fun j =>
      EReal.exists_coe_of_ne_bot_of_lt_top (hb j (x j)) (hx j (mem_univ j))
    have hsum : ∑ j, h j (x j) = ((∑ j, c j : ℝ) : EReal) := by
      rw [EReal.coe_sum]
      exact Finset.sum_congr rfl fun j _ => hc j
    change ∑ j, h j (x j) < ⊤
    rw [hsum]
    exact EReal.coe_lt_top _

/-- **A separable sum is minimised coordinatewise**: the minimum set of `x ↦ ∑ᵢ hᵢ(xᵢ)` on a finite
product is the product of the minimum sets of the summands.

`⊇` needs no hypothesis. `⊆` needs every summand proper, and both halves of properness carry
weight: a common domain point makes every `hⱼ(xⱼ)` finite, and finiteness is what allows the
`j ≠ i` part of the sum to be cancelled off both sides, `EReal` not being cancellative. Without the
domain point the statement is false — for `ι = Fin 2` with `h 0 ≡ ⊤` and `h 1 = id` on `ℝ`, the
left side is everything and the right side is empty. -/
theorem argmin_sepSum (hp : ∀ i, Proper (h i)) :
    argmin (fun x : ∀ i, E i => ∑ i, h i (x i)) = univ.pi fun i => argmin (h i) := by
  classical
  ext x
  refine ⟨fun hx i _ z => ?_, fun hx z => Finset.sum_le_sum fun i _ => hx i (mem_univ i) (z i)⟩
  -- a common domain point certifies that the value at `x` is finite
  choose y hy using fun j => (hp j).dom_nonempty
  choose r hr using fun j =>
    EReal.exists_coe_of_ne_bot_of_lt_top ((hp j).ne_bot (y j)) (hy j)
  have hxle : ∑ j, h j (x j) ≤ ((∑ j, r j : ℝ) : EReal) := by
    rw [EReal.coe_sum]
    exact (hx y).trans (le_of_eq (Finset.sum_congr rfl fun j _ => hr j))
  have hxdom : x ∈ dom fun w : ∀ i, E i => ∑ j, h j (w j) :=
    lt_of_le_of_lt hxle (EReal.coe_lt_top _)
  have hxpi := (dom_sepSum fun j z => (hp j).ne_bot z).subset hxdom
  choose c hc using fun j =>
    EReal.exists_coe_of_ne_bot_of_lt_top ((hp j).ne_bot (x j)) (hxpi j (mem_univ j))
  -- off the `i`-th coordinate the sum is a real, so it cancels
  have hrest : ∑ j ∈ Finset.univ.erase i, h j (x j)
      = ((∑ j ∈ Finset.univ.erase i, c j : ℝ) : EReal) := by
    rw [EReal.coe_sum]
    exact Finset.sum_congr rfl fun j _ => hc j
  have hupdsum : ∑ j ∈ Finset.univ.erase i, h j (Function.update x i z j)
      = ∑ j ∈ Finset.univ.erase i, h j (x j) :=
    Finset.sum_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hupd : ∑ j, h j (x j) ≤ ∑ j, h j (Function.update x i z j) :=
    hx (Function.update x i z)
  rw [← Finset.add_sum_erase _ (fun j => h j (x j)) (Finset.mem_univ i),
    ← Finset.add_sum_erase _ (fun j => h j (Function.update x i z j)) (Finset.mem_univ i),
    Function.update_self, hupdsum, hrest] at hupd
  exact (EReal.addLECancellable_coe _).add_le_add_iff_right.1 hupd

end Pi

/-! ### The minimum set as a subdifferential of the conjugate -/

section FenchelMoreau

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f : E → EReal}

/-- **The minimum set of a closed convex function is `∂f*(0)`**; in particular the infimum is
attained exactly when `f*` is subdifferentiable at the origin. This is the subgradient inequality
for `f*` at the origin, where Fenchel–Moreau turns `f**` back into `f`. -/
theorem argmin_eq_subgradient_conj_zero (hf : ConvexFn f) (hc : ClosedFn f) :
    argmin f = subgradient B.flip (conj B f) 0 := by
  ext x
  have hbi : conj B.flip (conj B f) x = f x := congrFun (biconj_eq_self hf hc) x
  have hpair : ((B.flip 0 x : ℝ) : EReal) = 0 := by simp
  rw [mem_argmin_iff_le_iInf, iInf_eq_neg_conj_zero B, mem_subgradient_iff_add_conj_le, hbi,
    hpair, ← EReal.le_sub_iff_add_le (.inr (by simp)) (.inr (by simp)), zero_sub,
    EReal.le_neg]

/-- Every nonempty level set of a closed proper convex function has the same recession cone, the
polar of `dom f*`. -/
theorem recessionCone_setOf_le_eq_polarCone_dom_conj (hf : ConvexFn f) (hc : ClosedFn f)
    (hp : Proper f) {α : ℝ} (hne : {z : E | f z ≤ (α : EReal)}.Nonempty) :
    recessionCone {z : E | f z ≤ (α : EReal)} = polarCone B.flip (dom (conj B f)) := by
  rw [recessionCone_setOf_le hf (ClosedProperConvexFn.isClosed_epi ⟨hf, hc, hp⟩) hne,
    recessionConeFn_eq_polarCone_dom_conj (B := B) hf hc hp]

/-- The same for the minimum set: when the infimum is attained the minimum set is a level set, so
it too has the polar of `dom f*` as its recession cone. -/
theorem recessionCone_argmin_eq_polarCone_dom_conj (hf : ConvexFn f) (hc : ClosedFn f)
    (hp : Proper f) {a : E} (ha : a ∈ argmin f) {μ : ℝ} (hμ : f a = (μ : EReal)) :
    recessionCone (argmin f) = polarCone B.flip (dom (conj B f)) := by
  rw [argmin_eq_setOf_le ha hμ]
  exact recessionCone_setOf_le_eq_polarCone_dom_conj hf hc hp ⟨a, le_of_eq hμ⟩

end FenchelMoreau

/-! ### Minimising over a convex set -/

section Optimality

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {h : E → EReal} {C : Set E} {x : E} {y : F}

/-- **Sufficiency of the optimality condition**: if some `y ∈ ∂h x` has `-y` normal to `C` at `x`,
then `h` attains its infimum over `C` at `x`. No hypothesis is needed — the subgradient inequality
and the normality inequality simply add. -/
theorem le_of_mem_subgradient_of_neg_mem_normalCone (hy : y ∈ subgradient B h x)
    (hn : -y ∈ normalCone B C x) {z : E} (hz : z ∈ C) : h x ≤ h z := by
  have h2 : B (z - x) (-y) ≤ 0 := hn z hz
  rw [map_neg, neg_nonpos] at h2
  calc h x ≤ h x + ((B (z - x) y : ℝ) : EReal) :=
        le_add_of_nonneg_right (by exact_mod_cast h2)
    _ ≤ h z := hy z

omit [AddCommGroup E] [Module ℝ E] in
/-- Minimising `h` over `C` is minimising `h + δ(· | C)` over the whole space. -/
theorem mem_argmin_add_indicatorFn_of_forall (hp : Proper h) (hx : x ∈ C)
    (hmin : ∀ z ∈ C, h x ≤ h z) : x ∈ argmin (h + indicatorFn C) := by
  intro z
  by_cases hzC : z ∈ C
  · simpa [indicatorFn_of_mem hx, indicatorFn_of_mem hzC] using hmin z hzC
  · have hrhs : (h + indicatorFn C) z = ⊤ := by
      rw [Pi.add_apply, indicatorFn_of_notMem hzC]
      exact EReal.add_top_of_ne_bot (hp.ne_bot z)
    rw [hrhs]
    exact le_top

omit [AddCommGroup E] [Module ℝ E] in
/-- The converse of `mem_argmin_add_indicatorFn_of_forall`: a minimiser of `h + δ(· | C)` that lies
in `C` minimises `h` over `C`. -/
theorem forall_le_of_mem_argmin_add_indicatorFn (hx : x ∈ argmin (h + indicatorFn C))
    (hxC : x ∈ C) {z : E} (hz : z ∈ C) : h x ≤ h z := by
  have hle := hx z
  rwa [Pi.add_apply, Pi.add_apply, indicatorFn_of_mem hxC, indicatorFn_of_mem hz, add_zero,
    add_zero] at hle

/-- **Necessity**: when the sum `h + δ(· | C)` is exact, every point where `h` attains its infimum
over `C` carries a subgradient `y ∈ ∂h x` with `-y` normal to `C`. The book's two hypotheses are
two ways of supplying that exactness. -/
theorem exists_mem_subgradient_neg_mem_normalCone (hex : IsExactSum B h (indicatorFn C))
    (hx : x ∈ C) (hmin : ∀ z ∈ C, h x ≤ h z) :
    ∃ y ∈ subgradient B h x, -y ∈ normalCone B C x := by
  have hzero : (0 : F) ∈ subgradient B (h + indicatorFn C) x :=
    (mem_argmin_iff_zero_mem_subgradient B _ x).1
      (mem_argmin_add_indicatorFn_of_forall hex.proper_left hx hmin)
  rw [hex.subgradient_add x, subgradient_indicatorFn hx] at hzero
  obtain ⟨y, hy, n, hn, hsum⟩ := hzero
  have hs : y + n = 0 := hsum
  have hny : -y = n := by
    rw [eq_comm, eq_neg_iff_add_eq_zero, add_comm]
    exact hs
  exact ⟨y, hy, hny ▸ hn⟩

end Optimality

/-! ### Existence of a minimiser -/

section Existence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- **The level set that carries the existence argument**: nonempty, closed, convex, and — when `f`
has no direction of recession — compact. Only the `⇒` direction is packaged here. -/
theorem isCompact_setOf_le (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f)
    (hrec : recessionConeFn f = {0}) {α : ℝ} (hne : {z : E | f z ≤ (α : EReal)}.Nonempty) :
    IsCompact {z : E | f z ≤ (α : EReal)} := by
  have hlsc : LowerSemicontinuous f := (closedFn_iff_lowerSemicontinuous hp.ne_bot).1 hc
  have hepi : IsClosed (epi f) := lowerSemicontinuous_iff_isClosed_epi.1 hlsc
  refine (isCompact_iff_recessionCone_eq_zero (hf.convex_le _)
    (lowerSemicontinuous_iff_isClosed_le.1 hlsc α) hne).2 ?_
  rw [recessionCone_setOf_le hf hepi hne]
  exact hrec

/-- A closed proper convex function with no direction of recession attains its infimum. Any level
set of `f` is nonempty, closed, convex and compact, so lower semicontinuity attains a minimum on
it, and off that level set `f` is larger. -/
theorem argmin_nonempty_of_recessionConeFn_eq_zero (hf : ConvexFn f) (hc : ClosedFn f)
    (hp : Proper f) (hrec : recessionConeFn f = {0}) : (argmin f).Nonempty := by
  have hlsc : LowerSemicontinuous f := (closedFn_iff_lowerSemicontinuous hp.ne_bot).1 hc
  obtain ⟨x₀, hx₀⟩ := hp.dom_nonempty
  obtain ⟨α, hα⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x₀) (mem_dom.1 hx₀)
  set L : Set E := {z : E | f z ≤ (α : EReal)} with hL
  have hLne : L.Nonempty := ⟨x₀, le_of_eq hα⟩
  obtain ⟨a, haL, hamin⟩ := LowerSemicontinuousOn.exists_isMinOn hLne
    (isCompact_setOf_le hf hc hp hrec hLne) (hlsc.lowerSemicontinuousOn L)
  refine ⟨a, fun z => ?_⟩
  by_cases hzL : z ∈ L
  · exact isMinOn_iff.1 hamin z hzL
  · exact le_trans haL (le_of_lt (not_le.1 hzL))

/-- The minimum set is then a nonempty compact convex set. -/
theorem isCompact_argmin_of_recessionConeFn_eq_zero (hf : ConvexFn f) (hc : ClosedFn f)
    (hp : Proper f) (hrec : recessionConeFn f = {0}) : IsCompact (argmin f) := by
  obtain ⟨a, ha⟩ := argmin_nonempty_of_recessionConeFn_eq_zero hf hc hp hrec
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot a)
    (lt_of_le_of_lt (ha _) (mem_dom.1 hp.dom_nonempty.choose_spec))
  have hset : argmin f = {z : E | f z ≤ (μ : EReal)} := by
    ext z
    constructor
    · intro hz; exact le_trans (hz a) (le_of_eq hμ)
    · intro hz w; exact le_trans (hμ ▸ hz) (ha w)
  rw [hset]
  exact isCompact_setOf_le hf hc hp hrec ⟨a, le_of_eq hμ⟩

/-- With no direction of recession, the infimum of a closed proper convex function is real. -/
theorem exists_iInf_eq_coe (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f)
    (hrec : recessionConeFn f = {0}) : ∃ μ : ℝ, (⨅ z, f z) = (μ : EReal) := by
  obtain ⟨a, ha⟩ := argmin_nonempty_of_recessionConeFn_eq_zero hf hc hp hrec
  obtain ⟨x₀, hx₀⟩ := hp.dom_nonempty
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot a)
    (lt_of_le_of_lt (ha x₀) (mem_dom.1 hx₀))
  exact ⟨μ, by rw [iInf_eq_of_mem_argmin ha, hμ]⟩

/-- The minimum is then *well posed*: for every `ε > 0` there is a `δ > 0` with the level set
`{x | f x ≤ inf f + δ}` lying within `ε` of the minimum set. One application of the extreme value
theorem to the compact `{f ≤ inf f + 1} \ (M + ε·int B)` gives `δ` directly, in place of the
book's nested-compactness argument. -/
theorem exists_pos_forall_exists_mem_argmin_dist_lt (hf : ConvexFn f) (hc : ClosedFn f)
    (hp : Proper f) (hrec : recessionConeFn f = {0}) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, f x ≤ (⨅ z, f z) + (δ : EReal) → ∃ z ∈ argmin f, dist x z < ε := by
  have hlsc : LowerSemicontinuous f := (closedFn_iff_lowerSemicontinuous hp.ne_bot).1 hc
  obtain ⟨a, ha⟩ := argmin_nonempty_of_recessionConeFn_eq_zero hf hc hp hrec
  obtain ⟨x₀, hx₀⟩ := hp.dom_nonempty
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot a)
    (lt_of_le_of_lt (ha x₀) (mem_dom.1 hx₀))
  have hinf : (⨅ z, f z) = (μ : EReal) := by rw [iInf_eq_of_mem_argmin ha, hμ]
  set U : Set E := ⋃ w ∈ argmin f, Metric.ball w ε with hUdef
  have hUopen : IsOpen U := isOpen_biUnion fun w _ => Metric.isOpen_ball
  have hmemU : ∀ x : E, x ∈ U ↔ ∃ z ∈ argmin f, dist x z < ε := by
    intro x
    simp [hUdef, Metric.mem_ball]
  have haL : a ∈ {z : E | f z ≤ ((μ + 1 : ℝ) : EReal)} := by
    rw [Set.mem_ofPred_eq, hμ]
    exact_mod_cast (by linarith : μ ≤ μ + 1)
  have hLcomp : IsCompact {z : E | f z ≤ ((μ + 1 : ℝ) : EReal)} :=
    isCompact_setOf_le hf hc hp hrec ⟨a, haL⟩
  set K : Set E := {z : E | f z ≤ ((μ + 1 : ℝ) : EReal)} \ U with hKdef
  have hKcomp : IsCompact K := by
    rw [hKdef, Set.sdiff_eq]
    exact hLcomp.inter_right (isClosed_compl_iff.2 hUopen)
  have hfinish : ∀ d : ℝ, 0 < d → d ≤ 1 →
      (∀ x : E, x ∈ K → ¬ f x ≤ ((μ + d : ℝ) : EReal)) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x, f x ≤ (⨅ z, f z) + (δ : EReal) → ∃ z ∈ argmin f, dist x z < ε := by
    intro d hd0 hd1 hout
    refine ⟨d, hd0, fun x hx => ?_⟩
    rw [hinf, ← EReal.coe_add] at hx
    have hxL : x ∈ {z : E | f z ≤ ((μ + 1 : ℝ) : EReal)} :=
      le_trans hx (by exact_mod_cast (by linarith : μ + d ≤ μ + 1))
    refine (hmemU x).1 ?_
    by_contra hxU
    exact hout x ⟨hxL, hxU⟩ hx
  rcases Set.eq_empty_or_nonempty K with hKe | hKne
  · exact hfinish 1 one_pos le_rfl fun x hxK => absurd hxK (by rw [hKe]; exact Set.notMem_empty x)
  · obtain ⟨b, hbK, hbmin⟩ :=
      LowerSemicontinuousOn.exists_isMinOn hKne hKcomp (hlsc.lowerSemicontinuousOn K)
    have hbnot : b ∉ argmin f := fun hb => hbK.2 ((hmemU b).2 ⟨b, hb, by simpa using hε⟩)
    obtain ⟨w, hw⟩ : ∃ w, f w < f b := by
      by_contra hcon
      push Not at hcon
      exact hbnot fun z => hcon z
    have hμb : (μ : EReal) < f b := lt_of_le_of_lt (by rw [← hμ]; exact ha w) hw
    obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot b)
      (lt_of_le_of_lt hbK.1 (EReal.coe_lt_top (μ + 1)))
    have hμr : μ < r := by
      rw [hr] at hμb
      exact_mod_cast hμb
    refine hfinish (min 1 ((r - μ) / 2)) (lt_min one_pos (by linarith)) (min_le_left _ _) ?_
    intro x hxK hxle
    have hble : ((r : ℝ) : EReal) ≤ ((μ + min 1 ((r - μ) / 2) : ℝ) : EReal) := by
      rw [← hr]
      exact le_trans (isMinOn_iff.1 hbmin x hxK) hxle
    rw [EReal.coe_le_coe_iff] at hble
    have hhalf : min 1 ((r - μ) / 2) ≤ (r - μ) / 2 := min_le_right _ _
    linarith

/-- **Minimising nets approach the minimum set**: along any such net the distance to it tends to
`0`. Stated for an arbitrary filter — `atTop` on `ℕ` is the sequential case. -/
theorem tendsto_infDist_argmin (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f)
    (hrec : recessionConeFn f = {0}) {ι : Type*} {l : Filter ι} {u : ι → E}
    (hu : Filter.Tendsto (fun i => f (u i)) l (nhds (⨅ z, f z))) :
    Filter.Tendsto (fun i => Metric.infDist (u i) (argmin f)) l (nhds 0) := by
  obtain ⟨μ, hμ⟩ := exists_iInf_eq_coe hf hc hp hrec
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hmain⟩ := exists_pos_forall_exists_mem_argmin_dist_lt hf hc hp hrec hε
  have hlt : (⨅ z, f z) < (⨅ z, f z) + (δ : EReal) := by
    rw [hμ, ← EReal.coe_add]
    exact_mod_cast (by linarith : μ < μ + δ)
  filter_upwards [hu (Iio_mem_nhds hlt)] with i hi
  obtain ⟨z, hz, hdz⟩ := hmain (u i) (le_of_lt hi)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg]
  exact lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hz) hdz

/-- Every cluster point of a minimising net belongs to the minimum set. -/
theorem mem_argmin_of_mapClusterPt (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f)
    (hrec : recessionConeFn f = {0}) {ι : Type*} {l : Filter ι} {u : ι → E}
    (hu : Filter.Tendsto (fun i => f (u i)) l (nhds (⨅ z, f z))) {x : E}
    (hx : MapClusterPt x l u) : x ∈ argmin f := by
  obtain ⟨μ, hμ⟩ := exists_iInf_eq_coe hf hc hp hrec
  have hMcomp : IsCompact (argmin f) := isCompact_argmin_of_recessionConeFn_eq_zero hf hc hp hrec
  have hMne : (argmin f).Nonempty := argmin_nonempty_of_recessionConeFn_eq_zero hf hc hp hrec
  refine (hMcomp.isClosed.mem_iff_infDist_zero hMne).2 ?_
  have key : ∀ ε : ℝ, 0 < ε → Metric.infDist x (argmin f) < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hmain⟩ :=
      exists_pos_forall_exists_mem_argmin_dist_lt hf hc hp hrec (half_pos hε)
    have hlt : (⨅ z, f z) < (⨅ z, f z) + (δ : EReal) := by
      rw [hμ, ← EReal.coe_add]
      exact_mod_cast (by linarith : μ < μ + δ)
    have hV : {z : E | f z < (⨅ z, f z) + (δ : EReal)} ∈ Filter.map u l :=
      hu (Iio_mem_nhds hlt)
    obtain ⟨y, hy1, hy2⟩ :=
      clusterPt_iff_nonempty.1 hx (Metric.ball_mem_nhds x (half_pos hε)) hV
    obtain ⟨z, hz, hdz⟩ := hmain y (le_of_lt hy2)
    have hxy : dist x y < ε / 2 := by rwa [Metric.mem_ball, dist_comm] at hy1
    have hyz : Metric.infDist y (argmin f) ≤ dist y z := Metric.infDist_le_dist_of_mem hz
    calc Metric.infDist x (argmin f) ≤ Metric.infDist y (argmin f) + dist x y :=
          Metric.infDist_le_infDist_add_dist
      _ < ε := by linarith
  rcases lt_or_ge 0 (Metric.infDist x (argmin f)) with hpos | hnonpos
  · exact absurd (key _ hpos) (lt_irrefl _)
  · exact le_antisymm hnonpos Metric.infDist_nonneg

/-- A minimising sequence is bounded. -/
theorem isBounded_range_of_tendsto_iInf (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f)
    (hrec : recessionConeFn f = {0}) {u : ℕ → E}
    (hu : Filter.Tendsto (fun i => f (u i)) Filter.atTop (nhds (⨅ z, f z))) :
    Bornology.IsBounded (Set.range u) := by
  have hMcomp : IsCompact (argmin f) := isCompact_argmin_of_recessionConeFn_eq_zero hf hc hp hrec
  have hMne : (argmin f).Nonempty := argmin_nonempty_of_recessionConeFn_eq_zero hf hc hp hrec
  obtain ⟨R, hR⟩ := hMcomp.isBounded.subset_closedBall (0 : E)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (Metric.tendsto_nhds.1 (tendsto_infDist_argmin hf hc hp hrec hu) 1 one_pos)
  have hsub : ∀ i, N ≤ i → u i ∈ Metric.closedBall (0 : E) (R + 1) := by
    intro i hi
    obtain ⟨w, hw, hdw⟩ := hMcomp.exists_infDist_eq_dist hMne (u i)
    have h1 : Metric.infDist (u i) (argmin f) < 1 := by
      have h2 := hN i hi
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg] at h2
    have h3 : dist (u i) w < 1 := by rwa [← hdw]
    have h4 : dist w 0 ≤ R := Metric.mem_closedBall.1 (hR hw)
    rw [Metric.mem_closedBall]
    calc dist (u i) 0 ≤ dist (u i) w + dist w 0 := dist_triangle _ _ _
      _ ≤ R + 1 := by linarith
  have hsplit : Set.range u ⊆ (u '' Set.Iio N) ∪ Metric.closedBall (0 : E) (R + 1) := by
    rintro _ ⟨i, rfl⟩
    rcases lt_or_ge i N with hi | hi
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr (hsub i hi)
  exact Bornology.IsBounded.subset
    (((Set.finite_Iio N).image u).isBounded.union Metric.isBounded_closedBall) hsplit

/-- If a closed proper convex function attains its infimum at a unique point, every minimising net
converges to that point. No recession hypothesis is needed: a one-point minimum set is a level set,
and a bounded level set forces the recession cone to be `{0}`. -/
theorem tendsto_of_argmin_eq_singleton (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f)
    {a : E} (hM : argmin f = {a}) {ι : Type*} {l : Filter ι} {u : ι → E}
    (hu : Filter.Tendsto (fun i => f (u i)) l (nhds (⨅ z, f z))) :
    Filter.Tendsto u l (nhds a) := by
  have haM : a ∈ argmin f := by rw [hM]; exact Set.mem_singleton a
  obtain ⟨x₀, hx₀⟩ := hp.dom_nonempty
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot a)
    (lt_of_le_of_lt (haM x₀) (mem_dom.1 hx₀))
  have hlsc : LowerSemicontinuous f := (closedFn_iff_lowerSemicontinuous hp.ne_bot).1 hc
  have hne : {z : E | f z ≤ (μ : EReal)}.Nonempty := ⟨a, le_of_eq hμ⟩
  have hrec : recessionConeFn f = {0} := by
    rw [← recessionCone_setOf_le hf (lowerSemicontinuous_iff_isClosed_epi.1 hlsc) hne,
      ← argmin_eq_setOf_le haM hμ, hM, recessionCone_singleton]
  have hlim := tendsto_infDist_argmin hf hc hp hrec hu
  rw [hM] at hlim
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [Metric.infDist_singleton] using hlim

end Existence

/-! ### Minimising over a closed convex set -/

section Constrained

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {h : E → EReal} {C : Set E}

omit [FiniteDimensional ℝ E] in
/-- The indicator of a nonempty closed convex set is a closed proper convex function. -/
theorem closedProperConvexFn_indicatorFn (hC : Convex ℝ C) (hCc : IsClosed C) (hCne : C.Nonempty) :
    ClosedProperConvexFn (indicatorFn C) :=
  ⟨convexFn_indicatorFn.2 hC, closedFn_indicatorFn hCc,
    ⟨by rw [dom_indicatorFn]; exact hCne, indicatorFn_ne_bot C⟩⟩

omit [FiniteDimensional ℝ E] in
/-- The directions of recession of `h + δ(· | C)` are exactly the directions of recession common to
`h` and to `C`. This is the recession formula for a sum read against an indicator: `δ(· | C)0⁺` is
`δ(· | 0⁺C)`, which is `0` on `0⁺C` and `⊤` off it. -/
theorem recessionConeFn_add_indicatorFn (hh : ClosedProperConvexFn h) (hC : Convex ℝ C)
    (hCc : IsClosed C) (hCne : C.Nonempty) (hne : (dom (h + indicatorFn C)).Nonempty) :
    recessionConeFn (h + indicatorFn C) = recessionConeFn h ∩ recessionCone C := by
  have hsum := recessionFn_add hh (closedProperConvexFn_indicatorFn hC hCc hCne) hne
  ext y
  rw [Set.mem_inter_iff, mem_recessionConeFn, mem_recessionConeFn, hsum, Pi.add_apply,
    recessionFn_indicatorFn hCne]
  by_cases hy : y ∈ recessionCone C
  · rw [indicatorFn_of_mem hy, add_zero]
    simp [hy]
  · rw [indicatorFn_of_notMem hy,
      EReal.add_top_of_ne_bot (recessionFn_ne_bot hh.proper y)]
    simp [hy]

/-- **The non-polyhedral case**: a closed proper convex `h` attains its infimum over a nonempty
closed convex `C` as soon as `h` and `C` have no direction of recession in common. The directions
of recession of `h + δ(· | C)` are the common ones, so unconstrained existence applies; when
`dom h ∩ C = ∅` the function is `+∞` throughout `C` and every point minimises. -/
theorem exists_forall_le_of_recessionConeFn_inter_eq_zero (hh : ClosedProperConvexFn h)
    (hC : Convex ℝ C) (hCc : IsClosed C) (hCne : C.Nonempty)
    (hrec : recessionConeFn h ∩ recessionCone C = {0}) :
    ∃ x ∈ C, ∀ z ∈ C, h x ≤ h z := by
  by_cases hne : (dom (h + indicatorFn C)).Nonempty
  · have hsum : ClosedProperConvexFn (h + indicatorFn C) :=
      hh.add (closedProperConvexFn_indicatorFn hC hCc hCne) hne
    obtain ⟨x, hx⟩ := argmin_nonempty_of_recessionConeFn_eq_zero hsum.convex hsum.closed
      hsum.proper (by rw [recessionConeFn_add_indicatorFn hh hC hCc hCne hne]; exact hrec)
    obtain ⟨w, hw⟩ := hne
    have hxdom : x ∈ dom (h + indicatorFn C) := mem_dom.2 (lt_of_le_of_lt (hx w) (mem_dom.1 hw))
    rw [dom_add hh.proper.ne_bot (indicatorFn_ne_bot C), dom_indicatorFn] at hxdom
    exact ⟨x, hxdom.2, fun z hz => forall_le_of_mem_argmin_add_indicatorFn hx hxdom.2 hz⟩
  · obtain ⟨x, hx⟩ := hCne
    refine ⟨x, hx, fun z hz => ?_⟩
    have hempty : dom h ∩ C = ∅ := by
      rw [← dom_indicatorFn C, ← dom_add hh.proper.ne_bot (indicatorFn_ne_bot C)]
      exact Set.not_nonempty_iff_eq_empty.1 hne
    have hz' : h z = ⊤ := by
      by_contra hcon
      exact Set.eq_empty_iff_forall_notMem.1 hempty z
        ⟨mem_dom.2 (lt_top_iff_ne_top.2 hcon), hz⟩
    rw [hz']
    exact le_top

/-- The same for an inequality system: a closed proper convex `h` attains its infimum subject to a
consistent system of constraints `g i x ≤ 0` when `h` and the `g i` have no direction of recession
in common. The index type is arbitrary. -/
theorem exists_forall_le_of_forall_le_zero {ι : Type*} {g : ι → E → EReal}
    (hh : ClosedProperConvexFn h) (hg : ∀ i, ClosedProperConvexFn (g i))
    (hCne : {x : E | ∀ i, g i x ≤ 0}.Nonempty)
    (hrec : recessionConeFn h ∩ ⋂ i, recessionConeFn (g i) = {0}) :
    ∃ x, (∀ i, g i x ≤ 0) ∧ ∀ z, (∀ i, g i z ≤ 0) → h x ≤ h z := by
  obtain ⟨x₀, hx₀⟩ := hCne
  have hCeq : {x : E | ∀ i, g i x ≤ 0} = ⋂ i, {z : E | g i z ≤ ((0 : ℝ) : EReal)} := by
    ext z
    simp
  have hconv : ∀ i, Convex ℝ {z : E | g i z ≤ ((0 : ℝ) : EReal)} := fun i =>
    (hg i).convex.convex_le _
  have hclosed : ∀ i, IsClosed {z : E | g i z ≤ ((0 : ℝ) : EReal)} := fun i =>
    lowerSemicontinuous_iff_isClosed_le.1 (hg i).lowerSemicontinuous 0
  have hx₀' : x₀ ∈ ⋂ i, {z : E | g i z ≤ ((0 : ℝ) : EReal)} := hCeq ▸ hx₀
  have hCrec : recessionCone {x : E | ∀ i, g i x ≤ 0} = ⋂ i, recessionConeFn (g i) := by
    rw [hCeq, recessionCone_iInter hconv hclosed ⟨x₀, hx₀'⟩]
    exact Set.iInter_congr fun i =>
      recessionCone_setOf_le (hg i).convex (hg i).isClosed_epi ⟨x₀, Set.mem_iInter.1 hx₀' i⟩
  obtain ⟨x, hxC, hmin⟩ := exists_forall_le_of_recessionConeFn_inter_eq_zero hh
    (by rw [hCeq]; exact convex_iInter hconv) (by rw [hCeq]; exact isClosed_iInter hclosed)
    ⟨x₀, hx₀⟩ (by rw [hCrec]; exact hrec)
  exact ⟨x, hxC, hmin⟩

end Constrained

/-! ### The polyhedral refinement

For polyhedral `C` the recession hypothesis weakens from "`h` and `C` have no direction of
recession in common" to "every common direction of recession is one in which `h` is *constant*".
Where the book derives this from Helly's theorem, the proof here projects `E` along the constancy
space of `h`, which leaves `h` untouched and shrinks the common recession cone to `{0}`.
Polyhedrality of `C` enters exactly once: a linear map commutes with `0⁺` on a polyhedral set and
on no other kind. -/

section ConstancyReduction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {h : E → EReal} {C : Set E}

omit [FiniteDimensional ℝ E] in
/-- Two points differing by a direction of constancy carry the same value. This is
`mem_constancySpace_iff_forall_eq` read as a statement about a *pair* of points rather than about
a direction. -/
theorem eq_of_sub_mem_constancySpace {x y : E} (hxy : x - y ∈ constancySpace h) : h x = h y := by
  have hxy' : y + (1 : ℝ) • (x - y) = x := by rw [one_smul]; abel
  have hval := (mem_constancySpace_iff_forall_eq.1 hxy) y 1
  rwa [hxy'] at hval

omit [FiniteDimensional ℝ E] in
/-- **Every subspace is the kernel of a linear projection.** For a subspace `M` there is a linear
`A : E →ₗ[ℝ] E` and a complement `N` such that `A` moves points only by directions of `M`,
annihilates `M`, lands in `N` and fixes `N` pointwise. This is how "quotient out a subspace"
arguments run without leaving `E`, keeping a function constant along `M` unchanged. -/
theorem exists_linearProj (M : Submodule ℝ E) :
    ∃ (A : E →ₗ[ℝ] E) (N : Submodule ℝ E), (∀ x, x - A x ∈ M) ∧ (∀ y ∈ M, A y = 0) ∧
      (∀ x, A x ∈ N) ∧ ∀ y ∈ N, A y = y := by
  obtain ⟨N, hN⟩ := Submodule.exists_isCompl M
  refine ⟨(LinearMap.id : E →ₗ[ℝ] E) - M.projection N hN, N, fun x => ?_, fun y hy => ?_,
    fun x => ?_, fun y hy => ?_⟩
  · have hval : x - ((LinearMap.id : E →ₗ[ℝ] E) - M.projection N hN) x
        = M.projection N hN x := by simp
    rw [hval, ← Submodule.coe_projectionOnto_apply]
    exact (M.projectionOnto N hN x).2
  · have hfix : M.projection N hN y = y := by
      rw [← Submodule.coe_projectionOnto_apply, Submodule.projectionOnto_apply_of_mem_left hN hy]
    simp [hfix]
  · have hval : ((LinearMap.id : E →ₗ[ℝ] E) - M.projection N hN) x = x - M.projection N hN x := by
      simp
    rw [hval, ← Submodule.projectionOnto_apply_eq_zero_iff hN, map_sub,
      Submodule.projectionOnto_projection hN, sub_self]
  · have hzero : M.projection N hN y = 0 := by
      rw [← Submodule.coe_projectionOnto_apply, Submodule.projectionOnto_apply_of_mem_right hN hy,
        Submodule.coe_zero]
    simp [hzero]

/-- **The general form**: a closed proper convex `h` attains its infimum over a nonempty closed
convex `C` as soon as every direction of recession common to `h` and `C` is *both* one in which `h`
is constant *and* a direction of linearity of `C`. The common recession cone may now be any such
subspace, not only `{0}`. The proof projects along
`constancySubmodule h ⊓ linealitySubmodule C`, where the image of `C` is `C ∩ N`. -/
theorem exists_forall_le_of_inter_subset_constancySpace_inter_linealitySpace
    (hh : ClosedProperConvexFn h) (hC : Convex ℝ C) (hCc : IsClosed C) (hCne : C.Nonempty)
    (hrec : recessionConeFn h ∩ recessionCone C ⊆ constancySpace h ∩ linealitySpace C) :
    ∃ x ∈ C, ∀ z ∈ C, h x ≤ h z := by
  obtain ⟨A, N, hsub, hA0, hAN, hAfix⟩ :=
    exists_linearProj (constancySubmodule h ⊓ linealitySubmodule C)
  have hsubc : ∀ x, x - A x ∈ constancySpace h := fun x =>
    mem_constancySubmodule.1 (Submodule.mem_inf.1 (hsub x)).1
  have hsubl : ∀ x, x - A x ∈ linealitySpace C := fun x =>
    mem_linealitySubmodule.1 (Submodule.mem_inf.1 (hsub x)).2
  have hmemC : ∀ x ∈ C, A x ∈ C := by
    intro x hx
    have hneg : -(x - A x) ∈ recessionCone C := (mem_linealitySpace.1 (hsubl x)).2
    have := add_mem_of_mem_recessionCone hneg hx
    rwa [show x + -(x - A x) = A x by abel] at this
  have himg : A '' C = C ∩ (N : Set E) := by
    refine Set.Subset.antisymm ?_ fun y hy => ⟨y, hy.1, hAfix y hy.2⟩
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hmemC x hx, hAN x⟩
  obtain ⟨x₀, hx₀⟩ := hCne
  have hne : (C ∩ (N : Set E)).Nonempty := ⟨A x₀, hmemC x₀ hx₀, hAN x₀⟩
  have hrecimg : recessionCone (A '' C) = recessionCone C ∩ (N : Set E) := by
    rw [himg, recessionCone_inter hC hCc N.convex N.closed_of_finiteDimensional hne,
      recessionCone_coe_submodule]
  have hrec' : recessionConeFn h ∩ recessionCone (A '' C) = {0} := by
    refine Set.Subset.antisymm (fun y hy => ?_) fun y hy => ?_
    · obtain ⟨hy1, hy2⟩ := hy
      rw [hrecimg] at hy2
      obtain ⟨hy2C, hy2N⟩ := hy2
      have hyM : y ∈ constancySubmodule h ⊓ linealitySubmodule C := by
        obtain ⟨hc, hl⟩ := hrec ⟨hy1, hy2C⟩
        exact Submodule.mem_inf.2 ⟨mem_constancySubmodule.2 hc, mem_linealitySubmodule.2 hl⟩
      have h1 : A y = 0 := hA0 y hyM
      have h2 : A y = y := hAfix y hy2N
      exact Set.mem_singleton_iff.2 (by rw [← h2, h1])
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨recessionFn_apply_zero_le h, zero_mem_recessionCone _⟩
  have hCimgconv : Convex ℝ (A '' C) := by rw [himg]; exact hC.inter N.convex
  have hCimgcl : IsClosed (A '' C) := by
    rw [himg]; exact hCc.inter N.closed_of_finiteDimensional
  obtain ⟨x', hx'C, hx'min⟩ := exists_forall_le_of_recessionConeFn_inter_eq_zero hh
    hCimgconv hCimgcl ⟨A x₀, ⟨x₀, hx₀, rfl⟩⟩ hrec'
  obtain ⟨x, hxC, rfl⟩ := hx'C
  refine ⟨x, hxC, fun z hz => ?_⟩
  rw [eq_of_sub_mem_constancySpace (hsubc x), eq_of_sub_mem_constancySpace (hsubc z)]
  exact hx'min (A z) ⟨z, hz, rfl⟩

/-- **The polyhedral refinement**: a closed proper convex `h` attains its infimum over a nonempty
**polyhedral** convex `C` as soon as every direction of recession common to `h` and `C` is one in
which `h` is constant.

Polyhedrality of `C` pays for the weakened hypothesis and cannot be dropped: on `ℝ²` with
`h(x₁, x₂) = x₂` and the closed convex `C = {x | x₁ ≥ x₂²}`, the common recession cone is
`{(a, 0) | a ≥ 0}`, along which `h` is constant, yet `inf_C h = -∞`. The proof replaces `C` by its
image under a projection killing the constancy space of `h`; the image is polyhedral, `h` is
unchanged along the fibres, and the common recession cone collapses to `{0}`. -/
theorem exists_forall_le_of_polyhedral_of_inter_subset_constancySpace
    (hh : ClosedProperConvexFn h) (hC : Polyhedral C) (hCne : C.Nonempty)
    (hrec : recessionConeFn h ∩ recessionCone C ⊆ constancySpace h) :
    ∃ x ∈ C, ∀ z ∈ C, h x ≤ h z := by
  obtain ⟨A, -, hsub', hA0, -, -⟩ := exists_linearProj (constancySubmodule h)
  have hsub : ∀ x, x - A x ∈ constancySpace h := fun x => mem_constancySubmodule.1 (hsub' x)
  have hCimg : Polyhedral (A '' C) := hC.image A
  have hCimgne : (A '' C).Nonempty := hCne.image A
  have hrec' : recessionConeFn h ∩ recessionCone (A '' C) = {0} := by
    refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨hy1, hy2⟩ := hy
      rw [hC.recessionCone_image hCne A] at hy2
      obtain ⟨y', hy', rfl⟩ := hy2
      have hdrec : y' - A y' ∈ recessionConeFn h := (mem_constancySpace.1 (hsub y')).1
      have hy'rec : y' ∈ recessionConeFn h := by
        have hadd : A y' + (y' - A y') ∈ recessionConeFn h :=
          (recessionPointedConeFn h).add_mem hy1 hdrec
        have heq : A y' + (y' - A y') = y' := by abel
        rwa [heq] at hadd
      exact Set.mem_singleton_iff.2
        (hA0 y' (mem_constancySubmodule.2 (hrec ⟨hy'rec, hy'⟩)))
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨recessionFn_apply_zero_le h, zero_mem_recessionCone _⟩
  obtain ⟨x', hx'C, hx'min⟩ := exists_forall_le_of_recessionConeFn_inter_eq_zero hh
    hCimg.convex hCimg.isClosed hCimgne hrec'
  obtain ⟨x, hxC, rfl⟩ := hx'C
  refine ⟨x, hxC, fun z hz => ?_⟩
  rw [eq_of_sub_mem_constancySpace (hsub x), eq_of_sub_mem_constancySpace (hsub z)]
  exact hx'min (A z) ⟨z, hz, rfl⟩

/-- A closed proper convex `h` all of whose directions of recession are directions in which `h` is
*affine* attains its infimum relative to any nonempty polyhedral convex `C` on which it is bounded
below.

The hypothesis `recessionConeFn h ⊆ linealitySpaceFn h` is weaker than the constancy hypothesis
above, and the price is the lower bound on `C`: a direction of recession in which `h` is affine has
slope `ν = (h0⁺) y ≤ 0`, and a lower bound along the half-lines of `C` in that direction forces
`ν = 0`, which is constancy. The lower bound cannot be dropped — `h(x₁, x₂) = x₁` on `ℝ²` is affine
in every direction and its infimum over `C = {x | x₂ = 0}` is `-∞`. The hypothesis holds for every
affine or convex quadratic `h`, and whenever `dom h*` is affine. -/
theorem exists_forall_le_of_polyhedral_of_recessionConeFn_subset_linealitySpaceFn
    (hh : ClosedProperConvexFn h) (hC : Polyhedral C) (hCne : C.Nonempty)
    (hrec : recessionConeFn h ⊆ linealitySpaceFn h) {β : ℝ}
    (hbdd : ∀ x ∈ C, (β : EReal) ≤ h x) : ∃ x ∈ C, ∀ z ∈ C, h x ≤ h z := by
  rcases Set.eq_empty_or_nonempty (C ∩ dom h) with hemp | ⟨x₀, hx₀C, hx₀⟩
  · obtain ⟨x, hx⟩ := hCne
    have htop : ∀ z ∈ C, h z = ⊤ := fun z hz => by
      by_contra hcon
      exact (Set.eq_empty_iff_forall_notMem.1 hemp z) ⟨hz, lt_top_iff_ne_top.2 hcon⟩
    exact ⟨x, hx, fun z hz => by rw [htop x hx, htop z hz]⟩
  · refine exists_forall_le_of_polyhedral_of_inter_subset_constancySpace hh hC hCne ?_
    rintro y ⟨hy1, hy2⟩
    exact mem_constancySpace_of_mem_linealitySpaceFn hh.proper hy1 (hrec hy1) hx₀
      fun a ha => hbdd _ (hy2 x₀ hx₀C a ha)

/-- The unconstrained case of the polyhedral refinement: a closed proper convex function whose
recession cone consists entirely of directions of constancy — equivalently, is a subspace —
attains its infimum. Existence with no direction of recession is the case of the subspace `{0}`. -/
theorem argmin_nonempty_of_recessionConeFn_subset_constancySpace (hh : ClosedProperConvexFn h)
    (hrec : recessionConeFn h ⊆ constancySpace h) : (argmin h).Nonempty := by
  obtain ⟨x, -, hx⟩ := exists_forall_le_of_polyhedral_of_inter_subset_constancySpace hh
    polyhedral_univ ⟨0, Set.mem_univ 0⟩ fun y hy => hrec hy.1
  exact ⟨x, mem_argmin_iff.2 fun z => hx z (Set.mem_univ z)⟩

end ConstancyReduction


/-! ### Polyhedral minimisation -/

section Polyhedral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- **A polyhedral convex function bounded below attains its infimum.** In the finitely generated
description `epi f = conv P + cone D` a lower bound forces every generating direction to point
upward, so the vertical coordinate is minimised at one of the finitely many generating points.
Neither closedness nor properness is assumed. -/
theorem argmin_nonempty_of_polyhedralFn (hf : PolyhedralFn f) (hbdd : ⊥ < ⨅ x, f x) :
    (argmin f).Nonempty := by
  classical
  have hbot : ∀ x, f x ≠ ⊥ := by
    intro x hx
    have hle : (⨅ z, f z) ≤ (⊥ : EReal) := by rw [← hx]; exact iInf_le f x
    exact absurd hle (not_le.2 hbdd)
  rcases eq_top_or_lt_top (⨅ x, f x) with htop | htop
  · refine ⟨0, fun z => ?_⟩
    have hz : f z = ⊤ := by
      refine top_le_iff.1 ?_
      rw [← htop]
      exact iInf_le f z
    rw [hz]
    exact le_top
  obtain ⟨β, hβ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (ne_of_gt hbdd) htop
  have hβle : ∀ x, (β : EReal) ≤ f x := by
    intro x
    rw [← hβ]
    exact iInf_le f x
  obtain ⟨P, D, hPD⟩ := Polyhedral.finitelyGenerated (hf : Polyhedral (epi f))
  -- the epigraph is non-empty, so there is at least one generating point
  have hepine : (epi f).Nonempty := by
    obtain ⟨x, hx⟩ := iInf_lt_iff.1 htop
    obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hbot x) hx
    exact ⟨(x, r), mk_mem_epi.2 (le_of_eq hr)⟩
  have hPne : (P : Finset (E × ℝ)).Nonempty := by
    rcases Finset.eq_empty_or_nonempty P with rfl | hne
    · exfalso
      rw [hPD] at hepine
      simp only [Finset.coe_empty, convexHull_empty, Set.empty_add] at hepine
      exact hepine.ne_empty rfl
    · exact hne
  obtain ⟨p₀, hp₀⟩ := hPne
  have hmem_epi : ∀ p ∈ P, (p : E × ℝ) ∈ epi f := by
    intro p hp
    rw [hPD]
    exact ⟨p, subset_convexHull ℝ _ (by exact_mod_cast hp), 0, Submodule.zero_mem _, by simp⟩
  -- every generating direction points upward
  have hDnonneg : ∀ d ∈ D, (0 : ℝ) ≤ (d : E × ℝ).2 := by
    intro d hd
    by_contra hneg
    push Not at hneg
    have hβp₀ : (β : EReal) ≤ (p₀.2 : EReal) := le_trans (hβle p₀.1) (hmem_epi p₀ hp₀)
    have hβp₀' : β ≤ p₀.2 := by exact_mod_cast hβp₀
    have hdne : d.2 ≠ 0 := ne_of_lt hneg
    have htpos : 0 < (p₀.2 - β + 1) / (-d.2) := div_pos (by linarith) (by linarith)
    have hmemd : ((p₀.2 - β + 1) / (-d.2)) • (d : E × ℝ) ∈
        (PointedCone.hull ℝ (D : Set (E × ℝ)) : Set (E × ℝ)) :=
      Submodule.smul_mem _ (⟨(p₀.2 - β + 1) / (-d.2), htpos.le⟩ : {c : ℝ // 0 ≤ c})
        (PointedCone.subset_hull (by exact_mod_cast hd))
    have hsum : (p₀ : E × ℝ) + ((p₀.2 - β + 1) / (-d.2)) • (d : E × ℝ) ∈ epi f := by
      rw [hPD]
      exact ⟨p₀, subset_convexHull ℝ _ (by exact_mod_cast hp₀), _, hmemd, rfl⟩
    have hval : ((p₀ : E × ℝ) + ((p₀.2 - β + 1) / (-d.2)) • (d : E × ℝ)).2
        = p₀.2 + ((p₀.2 - β + 1) / (-d.2)) * d.2 := rfl
    have hle := le_trans (hβle _) hsum
    rw [hval] at hle
    have hle' : β ≤ p₀.2 + ((p₀.2 - β + 1) / (-d.2)) * d.2 := by exact_mod_cast hle
    have hcancel : ((p₀.2 - β + 1) / (-d.2)) * d.2 = -(p₀.2 - β + 1) := by
      field_simp
    rw [hcancel] at hle'
    linarith
  have hBall : ∀ b ∈ (PointedCone.hull ℝ (D : Set (E × ℝ)) : Set (E × ℝ)),
      (0 : ℝ) ≤ (b : E × ℝ).2 := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem z hz => exact hDnonneg z (by exact_mod_cast hz)
    | zero => exact le_refl 0
    | add z w _ _ hz hw =>
        have hadd : ((z + w : E × ℝ)).2 = z.2 + w.2 := rfl
        rw [hadd]
        linarith
    | smul c z _ hz =>
        have hc : (0 : ℝ) ≤ (c : ℝ) := c.2
        have hval : ((c • z : E × ℝ)).2 = (c : ℝ) * z.2 := rfl
        rw [hval]
        exact mul_nonneg hc hz
  -- the vertical coordinate is minimised over the generating points
  obtain ⟨pm, hpmP, hpmmin⟩ := P.exists_min_image (fun p : E × ℝ => p.2) ⟨p₀, hp₀⟩
  have hlow : ∀ q ∈ epi f, pm.2 ≤ (q : E × ℝ).2 := by
    intro q hq
    rw [hPD] at hq
    obtain ⟨a, ha, b, hb, hab⟩ := hq
    have hA : pm.2 ≤ a.2 := by
      have hsub : convexHull ℝ (P : Set (E × ℝ)) ⊆ {z : E × ℝ | pm.2 ≤ z.2} :=
        convexHull_min (fun p hp => hpmmin p (by exact_mod_cast hp))
          (convex_halfSpace_ge (LinearMap.isLinear (LinearMap.snd ℝ E ℝ)) pm.2)
      exact hsub ha
    have hB : (0 : ℝ) ≤ b.2 := hBall b hb
    have hq2 : (q : E × ℝ).2 = a.2 + b.2 := by rw [← hab]; rfl
    rw [hq2]
    linarith
  refine ⟨pm.1, fun z => ?_⟩
  have h1 : f pm.1 ≤ (pm.2 : EReal) := hmem_epi pm hpmP
  rcases eq_top_or_lt_top (f z) with hz | hz
  · rw [hz]
    exact le_top
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hbot z) hz
  have hzepi : ((z, r) : E × ℝ) ∈ epi f := mk_mem_epi.2 (le_of_eq hr)
  have hmr : pm.2 ≤ r := hlow _ hzepi
  calc f pm.1 ≤ (pm.2 : EReal) := h1
    _ ≤ (r : EReal) := by exact_mod_cast hmr
    _ = f z := hr.symm

/-- A polyhedral convex function attains its infimum relative to any non-empty polyhedral convex
set on which it is bounded below. Restricting `f` to `C` cuts the epigraph down by the vertical
prism over `C`, so the restriction is again polyhedral. The book derives this from the
affine-recession form above, and hence from Helly's theorem; this argument needs neither. -/
theorem exists_forall_le_of_polyhedralFn_of_polyhedral (hf : PolyhedralFn f) {C : Set E}
    (hC : Polyhedral C) (hCne : C.Nonempty) (hbdd : ⊥ < ⨅ x ∈ C, f x) :
    ∃ x ∈ C, ∀ z ∈ C, f x ≤ f z := by
  classical
  set g : E → EReal := fun x => ⨅ _ : x ∈ C, f x with hgdef
  have hgin : ∀ x ∈ C, g x = f x := fun x hx => iInf_pos hx
  have hgout : ∀ x ∉ C, g x = ⊤ := fun x hx => iInf_neg hx
  have hgpoly : PolyhedralFn g := by
    have hepi : epi g = epi f ∩ (C ×ˢ (Set.univ : Set ℝ)) := by
      ext p
      rw [mem_epi, Set.mem_inter_iff, mem_epi, Set.mem_prod]
      by_cases hx : p.1 ∈ C
      · rw [hgin _ hx]
        simp [hx]
      · rw [hgout _ hx, top_le_iff]
        simp [hx]
    change Polyhedral (epi g)
    rw [hepi]
    exact Polyhedral.inter hf (Polyhedral.prod hC polyhedral_univ)
  obtain ⟨x, hx⟩ := argmin_nonempty_of_polyhedralFn hgpoly hbdd
  by_cases hxC : x ∈ C
  · refine ⟨x, hxC, fun z hz => ?_⟩
    have h := hx z
    rwa [hgin _ hxC, hgin _ hz] at h
  · obtain ⟨x₀, hx₀⟩ := hCne
    refine ⟨x₀, hx₀, fun z hz => ?_⟩
    have h := hx z
    rw [hgout _ hxC, hgin _ hz, top_le_iff] at h
    rw [h]
    exact le_top

end Polyhedral

/-! ### The conjugate at the origin

Three readings of `f*` near the origin: the interior of `dom f*` governs boundedness of the
minimum set, and the support functions of the level sets are read off `f*` by homogenisation and
by a limit of directional derivatives. -/

section ConjugateAtZero

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] [IsCompatiblePairing B.flip] {f : E → EReal}

omit [FiniteDimensional ℝ E] in
/-- The origin is interior to `dom f*` exactly when `f` has no direction of recession: the
recession cone is the polar of `dom f*`, which is trivial exactly then. -/
theorem zero_mem_interior_dom_conj_iff_recessionConeFn_eq_zero (hf : ConvexFn f) (hc : ClosedFn f)
    (hp : Proper f) :
    (0 : F) ∈ interior (dom (conj B f)) ↔ recessionConeFn f = {(0 : E)} := by
  rw [zero_mem_interior_iff_polarCone_eq_zero (B := B) (convexFn_conj B f).convex_dom
      (proper_conj ⟨hf, hc, hp⟩).dom_nonempty,
    ← recessionConeFn_eq_polarCone_dom_conj (B := B) hf hc hp]

omit [FiniteDimensional ℝ E] in
/-- The origin is in the *relative* interior of `dom f*` exactly when every direction of recession
of `f` is one in which `f` is constant. The relative-interior criterion for `dom f*`, read at the
origin, collapses to `0⁺f ⊆ constancy space`. -/
theorem zero_mem_relint_dom_conj_iff_recessionConeFn_subset_constancySpace (hf : ConvexFn f)
    (hc : ClosedFn f) (hp : Proper f) :
    (0 : F) ∈ ri (dom (conj B f)) ↔ recessionConeFn f ⊆ constancySpace f := by
  rw [mem_relint_dom_conj_iff (B := B) ⟨hf, hc, hp⟩ 0]
  simp only [map_zero, EReal.coe_zero]
  constructor
  · rintro ⟨h1, h2⟩ y hy
    have hy0 : recessionFn f y = 0 := le_antisymm hy (h1 y)
    have hne : ¬ (-recessionFn f (-y) ≠ recessionFn f y) := fun hcon =>
      absurd (h2 y hcon) (by rw [hy0]; exact lt_irrefl 0)
    rw [not_ne_iff, hy0] at hne
    have hneg : recessionFn f (-y) = 0 := by
      rw [← neg_neg (recessionFn f (-y)), hne, neg_zero]
    exact mem_constancySpace.2 ⟨hy, le_of_eq hneg⟩
  · intro H
    have h1 : ∀ y : E, (0 : EReal) ≤ recessionFn f y := by
      intro y
      rcases le_or_gt (recessionFn f y) 0 with hle | hlt
      · have hneg : recessionFn f (-y) ≤ ((-(0 : ℝ) : ℝ) : EReal) := by
          simpa using (mem_constancySpace.1 (H (mem_recessionConeFn.2 hle))).2
        simpa using le_recessionFn_of_neg_le hp hneg
      · exact hlt.le
    refine ⟨h1, fun y hy => ?_⟩
    rcases (h1 y).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hyrec : y ∈ recessionConeFn f := mem_recessionConeFn.2 (le_of_eq heq.symm)
      have hneg0 : recessionFn f (-y) = 0 :=
        le_antisymm (mem_constancySpace.1 (H hyrec)).2 (h1 (-y))
      exact hy (by rw [hneg0, ← heq, neg_zero])

/-- The minimum set of a closed proper convex function is non-empty and bounded exactly when the
origin is interior to `dom f*`. Both directions pass through "no direction of recession": a bounded
level set has trivial recession cone one way, and existence of a minimiser the other. -/
theorem argmin_nonempty_and_isBounded_iff_zero_mem_interior_dom_conj (hf : ConvexFn f)
    (hc : ClosedFn f) (hp : Proper f) :
    ((argmin f).Nonempty ∧ Bornology.IsBounded (argmin f))
      ↔ (0 : F) ∈ interior (dom (conj B f)) := by
  rw [zero_mem_interior_dom_conj_iff_recessionConeFn_eq_zero (B := B) hf hc hp]
  have hlsc : LowerSemicontinuous f := (closedFn_iff_lowerSemicontinuous hp.ne_bot).1 hc
  constructor
  · rintro ⟨⟨a, ha⟩, hbd⟩
    obtain ⟨x₀, hx₀⟩ := hp.dom_nonempty
    obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot a)
      (lt_of_le_of_lt (ha x₀) (mem_dom.1 hx₀))
    have hset : argmin f = {z : E | f z ≤ (μ : EReal)} := argmin_eq_setOf_le ha hμ
    have hne : {z : E | f z ≤ (μ : EReal)}.Nonempty := ⟨a, le_of_eq hμ⟩
    have hbd' : Bornology.IsBounded {z : E | f z ≤ (μ : EReal)} := by rw [← hset]; exact hbd
    have hrec := (isBounded_iff_recessionCone_eq_zero (hf.convex_le _)
      (lowerSemicontinuous_iff_isClosed_le.1 hlsc μ) hne).1 hbd'
    rwa [recessionCone_setOf_le hf (lowerSemicontinuous_iff_isClosed_epi.1 hlsc) hne] at hrec
  · intro hrec
    exact ⟨argmin_nonempty_of_recessionConeFn_eq_zero hf hc hp hrec,
      (isCompact_argmin_of_recessionConeFn_eq_zero hf hc hp hrec).isBounded⟩

/-- The same in level-set form: *some* level set of `f` is non-empty and bounded exactly when the
origin is interior to `dom f*`. Here "some" is as good as "every", since all non-empty level sets
share the recession cone of `f`. -/
theorem exists_setOf_le_nonempty_and_isBounded_iff_zero_mem_interior_dom_conj (hf : ConvexFn f)
    (hc : ClosedFn f) (hp : Proper f) :
    (∃ α : ℝ, {x : E | f x ≤ (α : EReal)}.Nonempty ∧
        Bornology.IsBounded {x : E | f x ≤ (α : EReal)})
      ↔ (0 : F) ∈ interior (dom (conj B f)) := by
  rw [zero_mem_interior_dom_conj_iff_recessionConeFn_eq_zero (B := B) hf hc hp]
  have hlsc : LowerSemicontinuous f := (closedFn_iff_lowerSemicontinuous hp.ne_bot).1 hc
  constructor
  · rintro ⟨α, hne, hbd⟩
    have hrec := (isBounded_iff_recessionCone_eq_zero (hf.convex_le _)
      (lowerSemicontinuous_iff_isClosed_le.1 hlsc α) hne).1 hbd
    rwa [recessionCone_setOf_le hf (lowerSemicontinuous_iff_isClosed_epi.1 hlsc) hne] at hrec
  · intro hrec
    obtain ⟨a, ha⟩ := argmin_nonempty_of_recessionConeFn_eq_zero hf hc hp hrec
    obtain ⟨x₀, hx₀⟩ := hp.dom_nonempty
    obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot a)
      (lt_of_le_of_lt (ha x₀) (mem_dom.1 hx₀))
    refine ⟨μ, ⟨a, le_of_eq hμ⟩, ?_⟩
    rw [← argmin_eq_setOf_le ha hμ]
    exact (isCompact_argmin_of_recessionConeFn_eq_zero hf hc hp hrec).isBounded

include B in
/-- For the objective function of a convex program: the minimum set is non-empty and bounded
exactly when some level set is. Both say `0 ∈ int (dom f*)`. -/
theorem argmin_nonempty_and_isBounded_iff_exists_setOf_le (hf : ConvexFn f) (hc : ClosedFn f)
    (hp : Proper f) :
    ((argmin f).Nonempty ∧ Bornology.IsBounded (argmin f))
      ↔ ∃ α : ℝ, {x : E | f x ≤ (α : EReal)}.Nonempty ∧
          Bornology.IsBounded {x : E | f x ≤ (α : EReal)} :=
  (argmin_nonempty_and_isBounded_iff_zero_mem_interior_dom_conj (B := B) hf hc hp).trans
    (exists_setOf_le_nonempty_and_isBounded_iff_zero_mem_interior_dom_conj (B := B) hf hc hp).symm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsCompatiblePairing B]
  [IsCompatiblePairing B.flip] in
/-- Raising the conjugate by a real constant lowers the biconjugate by the same constant. This is
`conj_add_const` read on the dual pair. -/
theorem conj_flip_conj_add_coe (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (α : ℝ) (x : E) :
    conj B.flip (fun y => conj B f y + (α : EReal)) x = biconj B f x - (α : EReal) :=
  conj_add_const B.flip (conj B f) α x

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- For each real `α` the support function of the level set `{f ≤ α}` is the closure of the
positively homogeneous convex function generated by `f* + α`. -/
theorem supportFn_setOf_le (hf : ConvexFn f) (hc : ClosedFn f) (α : ℝ) :
    supportFn B {x : E | f x ≤ (α : EReal)}
      = clFn (posHomGen fun y => conj B f y + (α : EReal)) := by
  rw [clFn_posHomGen (B := B) fun y => conj B f y + (α : EReal)]
  congr 1
  ext x
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, conj_flip_conj_add_coe,
    show biconj B f x = f x from congrFun (biconj_eq_self hf hc) x,
    EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot α))
      (.inl (EReal.coe_ne_top α)), zero_add]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- When `f` is bounded below, the support function of its minimum set is the closure of the
directional derivative of `f*` at the origin. -/
theorem supportFn_argmin (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f)
    (hbdd : conj B f 0 ≠ ⊤) :
    supportFn B (argmin f) = clFn (dirDeriv (conj B f) 0) := by
  rw [argmin_eq_subgradient_conj_zero (B := B) hf hc,
    clFn_dirDeriv (B := B.flip) (convexFn_conj B f) hbdd (conj_ne_bot hp.dom_nonempty 0),
    LinearMap.flip_flip]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsCompatiblePairing B.flip] in
/-- The level sets of `f` above its infimum are exactly the ε-subdifferentials of `f*` at the
origin. Fenchel–Moreau plus `f*(0) = -inf f`: `z ∈ ∂_ε f*(0)` says `⟨z, y⟩ - f*(y) ≤ inf f + ε` for
every `y`, whose supremum on the left is `f**(z) = f(z)`. -/
theorem epsSubgradient_conj_zero (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f)
    {μ : ℝ} (hμ : (⨅ x, f x) = (μ : EReal)) (ε : ℝ) :
    epsSubgradient B.flip ε (conj B f) 0 = {z : E | f z ≤ ((μ + ε : ℝ) : EReal)} := by
  have hc0 : conj B f 0 = ((-μ : ℝ) : EReal) := by
    rw [conj_zero_eq_neg_iInf, hμ, EReal.coe_neg]
  ext z
  rw [Set.mem_ofPred_eq, mem_epsSubgradient]
  have hstep : ∀ y : F, (conj B f 0 + ((B.flip (y - 0) z : ℝ) : EReal)
        ≤ conj B f y + (ε : EReal))
      ↔ (((B.flip y z : ℝ) : EReal) - conj B f y ≤ ((μ + ε : ℝ) : EReal)) := fun y => by
    rw [sub_zero, hc0, coe_add_le_add_coe_iff,
      EReal.sub_le_iff_le_add (.inl (conj_ne_bot hp.dom_nonempty y))
        (.inr (EReal.coe_ne_bot _)),
      add_comm (((μ + ε : ℝ) : EReal)) (conj B f y), show ε - -μ = μ + ε from by ring]
  simp only [hstep]
  have hbi : (⨆ y : F, ((B.flip y z : ℝ) : EReal) - conj B f y) = f z := by
    rw [← conj_apply]
    exact congrFun (biconj_eq_self hf hc) z
  rw [← iSup_le_iff, hbi]

omit [FiniteDimensional ℝ E] in
/-- As the level shrinks to the infimum, the support functions of the level sets of `f` converge to
the directional derivative of `f*` at the origin. The ε-subdifferentials of `f*` at the origin are
exactly those level sets; the limit is an infimum because `ε ↦ ∂_ε f*(0)` is monotone. -/
theorem iInf_supportFn_setOf_le (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f)
    {μ : ℝ} (hμ : (⨅ x, f x) = (μ : EReal)) (y : F) :
    (⨅ ε ∈ Set.Ioi (0 : ℝ), supportFn B {z : E | f z ≤ ((μ + ε : ℝ) : EReal)} y)
      = dirDeriv (conj B f) 0 y := by
  have hcp : Proper (conj B f) := proper_conj ⟨hf, hc, hp⟩
  have hc0 : conj B f 0 = ((-μ : ℝ) : EReal) := by
    rw [conj_zero_eq_neg_iInf, hμ, EReal.coe_neg]
  have hepi : IsClosed (epi (conj B f)) :=
    ClosedProperConvexFn.isClosed_epi ⟨convexFn_conj B f, closedFn_conj, hcp⟩
  rw [← dirDeriv_eq_iInf_supportFn_epsSubgradient (B := B.flip) (convexFn_conj B f) hcp hepi hc0 y]
  refine iInf_congr fun ε => iInf_congr fun hε => ?_
  rw [epsSubgradient_conj_zero hf hc hp hμ ε, LinearMap.flip_flip]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A proper function takes a value below `⊤` somewhere, so its infimum is never `⊤`. Together
with `conj_ne_bot` this is why "finite" costs only one inequality on each side below. -/
theorem iInf_ne_top (hp : Proper f) : (⨅ x, f x) ≠ ⊤ := by
  obtain ⟨x₀, hx₀⟩ := hp.dom_nonempty
  exact (lt_of_le_of_lt (iInf_le _ x₀) (mem_dom.1 hx₀)).ne

omit [FiniteDimensional ℝ E] in
/-- The infimum of a closed proper convex function is finite but *unattained* exactly when `f*(0)`
is finite and `f*'(0; ·)` takes `−∞` somewhere. Only one bound appears on each side, because
`f*(0) ≠ ⊥` and `⨅ f ≠ ⊤` hold for every proper `f`. -/
theorem iInf_ne_bot_and_argmin_eq_empty_iff (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) :
    ((⨅ x, f x) ≠ ⊥ ∧ argmin f = ∅)
      ↔ (conj B f 0 ≠ ⊤ ∧ ∃ y : F, dirDeriv (conj B f) 0 y = ⊥) := by
  have hb : conj B f 0 ≠ ⊥ := conj_ne_bot hp.dom_nonempty 0
  have hiff : (⨅ x, f x) ≠ ⊥ ↔ conj B f 0 ≠ ⊤ := by
    rw [conj_zero_eq_neg_iInf, ne_eq, ne_eq, EReal.neg_eq_top_iff]
  rw [hiff, and_congr_right_iff]
  intro ht
  rw [argmin_eq_subgradient_conj_zero (B := B) hf hc,
    subgradient_eq_empty_iff_exists_dirDeriv_eq_bot (B := B.flip) (convexFn_conj B f) ht hb]

end ConjugateAtZero

/-! ### A unique minimiser is a gradient of the conjugate

The minimum set *is* `∂f*(0)`, and a subdifferential is a singleton exactly at a point of
differentiability; what follows is the two composed. No reflexivity is needed: the subdifferential
in question is `subgradient B.flip (conj B f) 0`, a subset of `E`. -/

section UniqueMinimiser

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] [IsCompatiblePairing B.flip] {f : E → EReal}
  {x : E}

/-- **Necessity**: if the minimum set of `f` is the single vector `x`, then `f*` is differentiable
at the origin with `∇f*(0) = ⟨·, x⟩`. The finite-dimensionality is `F`'s, not `E`'s — it is the
space `f*` lives on. -/
theorem hasGradientAtFn_conj_zero_of_argmin_eq_singleton (hf : ConvexFn f) (hc : ClosedFn f)
    (hp : Proper f) (h : argmin f = {x}) :
    HasGradientAtFn (conj B f) (evalCLM B.flip x) 0 :=
  hasGradientAtFn_evalCLM_of_subgradient_eq_singleton (B := B.flip) (convexFn_conj B f)
    (proper_conj ⟨hf, hc, hp⟩)
    (by rw [← argmin_eq_subgradient_conj_zero (B := B) hf hc]; exact h)

omit [FiniteDimensional ℝ F] in
/-- **Sufficiency**: if `f*` is differentiable at the origin with `∇f*(0) = ⟨·, x⟩`, then `x` is
the unique minimiser of `f`.

Properness of `f` is not needed: differentiability of `f*` at the origin already forces `f*` proper,
hence `f*(0)` finite, which is all the uniqueness argument consumes. The separation that argument
needs is free from `IsCompatiblePairing B`, and it is not an artefact — if `B x = 0` for some
`x ≠ 0` then every level set of `f = f**` is invariant under translation by `x` and no minimum set
is ever a singleton. Finite-dimensionality of `F` is not used on this side. -/
theorem argmin_eq_singleton_of_hasGradientAtFn_conj_zero (hf : ConvexFn f) (hc : ClosedFn f)
    (h : HasGradientAtFn (conj B f) (evalCLM B.flip x) 0) : argmin f = {x} := by
  have hcf : ConvexFn (conj B f) := convexFn_conj B f
  have hprop : Proper (conj B f) := HasGradientAtFn.proper hcf h
  rw [argmin_eq_subgradient_conj_zero (B := B) hf hc]
  refine subgradient_eq_singleton_of_dirDeriv_eq (B := B.flip)
    (injective_of_separatingDual B)
    ((mem_dom.1 (interior_subset (HasGradientAtFn.mem_interior_dom h))).ne) (hprop.ne_bot 0)
    fun v => ?_
  rw [HasGradientAtFn.dirDeriv_eq hcf h v]
  rfl

/-- The minimum set of a closed proper convex `f` is the single vector `x` exactly when `f*` is
differentiable at the origin with `∇f*(0) = ⟨·, x⟩`. -/
theorem argmin_eq_singleton_iff_hasGradientAtFn_conj_zero (hf : ConvexFn f) (hc : ClosedFn f)
    (hp : Proper f) : argmin f = {x} ↔ HasGradientAtFn (conj B f) (evalCLM B.flip x) 0 :=
  ⟨hasGradientAtFn_conj_zero_of_argmin_eq_singleton hf hc hp,
    argmin_eq_singleton_of_hasGradientAtFn_conj_zero hf hc⟩

/-- The existential form: the infimum of `f` is attained at a *unique* point exactly when `f*` is
differentiable at the origin. Passing from the functional `∇f*(0)` to the vector `x : E`
representing it is the surjectivity half of `IsCompatiblePairing B.flip`. -/
theorem exists_argmin_eq_singleton_iff_differentiableAtFn_conj_zero (hf : ConvexFn f)
    (hc : ClosedFn f) (hp : Proper f) :
    (∃ x : E, argmin f = {x}) ↔ DifferentiableAtFn (conj B f) 0 := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨_, hasGradientAtFn_conj_zero_of_argmin_eq_singleton hf hc hp hx⟩
  · rintro ⟨g, hg⟩
    obtain ⟨x, hx⟩ := IsCompatiblePairing.surjective_eval B.flip g
    exact ⟨x, argmin_eq_singleton_of_hasGradientAtFn_conj_zero hf hc (by rw [hx]; exact hg)⟩

end UniqueMinimiser

end ConvexAnalysis
