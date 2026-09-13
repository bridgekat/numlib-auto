import Numlib.Analysis.Convex.Subgradient.Existence

/-!
# Monotonicity of the subdifferential

The subdifferential of a proper convex function is not merely *monotone* —
`⟨x₁ - x₂, y₁ - y₂⟩ ≥ 0` whenever `yᵢ ∈ ∂f xᵢ` — but **cyclically monotone**: every finite cycle
`(x₀, y₀), …, (x_m, y_m)` in its graph satisfies

```
⟨x₁ - x₀, y₀⟩ + ⟨x₂ - x₁, y₁⟩ + ⋯ + ⟨x₀ - x_m, y_m⟩ ≤ 0.
```

That is the whole story: a multivalued mapping is cyclically monotone exactly when it is contained
in the subdifferential of a closed proper convex function, and that function can be written down as
the supremum of the telescoping sums above, read as affine functions of a free endpoint. Since a
closed proper convex function is determined by its subdifferential up to an additive constant, the
maximal cyclically monotone mappings are precisely the subdifferentials — a different condition
from maximal monotonicity, neither implying the other.

## Main definitions

* `IsMonotoneRel`, `IsMaximalMonotoneRel`, `IsCyclicallyMonotone`, `IsMaximalCyclicallyMonotone`.
* `cyclicPotential B ρ s` — the convex function reconstructed from a cyclically monotone `ρ`.

## Main results

* `isCyclicallyMonotone_iff_exists_convexFn` — cyclic monotonicity *is* containment in some `∂f`.
* `isClosed_subgradientRel` — the graph of `∂f` is closed.
* `eq_add_coe_of_subgradientRel_subset` — rigidity: `∂f ⊆ ∂g` forces `g = f + α`, by subdivision.
* `isMaximalCyclicallyMonotone_iff_exists_closedProperConvexFn` — the maximal cyclically monotone
  mappings are exactly the subdifferentials.

## Implementation notes

A cycle is a `List (E × F)` with the starting pair carried separately, so that every proof is a
list induction. `chainVal B s l x` keeps the free endpoint last, which makes `cyclicPotential` a
supremum of affine functions of `x` and the cycle condition read `chainVal B s l s.1 ≤ 0`.
Closedness of the graph asks for *joint* continuity of the pairing,
`Continuous fun p : E × F => B p.1 p.2`: continuity of `⟨·, y⟩` for each fixed `y` is not enough to
pass to the limit in `⟨z - xᵢ, yᵢ⟩` when both arguments move. In `ℝⁿ` the hypothesis is automatic.

Maximal monotonicity of `∂f` for a closed proper convex `f` is not here: it is
`isMaximalMonotoneRel_subgradientRel` in `Optimization/Prox.lean`, because its proof is Moreau's
theorem and that file is downstream of this one.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §24.
* R. T. Rockafellar, *Characterization of the subdifferentials of convex functions*, Pacific J.
  Math. **17** (1966) 497–510.
-/

open Set Filter Topology

namespace ConvexAnalysis

/-! ### Chains and cyclic monotonicity -/

section Chain

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The telescoping sum along a finite chain in the graph of a multivalued mapping. The chain
starts at the pair `s = (x₀, y₀)`, runs through `l = [(x₁, y₁), …, (x_m, y_m)]` and ends at the
free point `x`:

```
chainVal B s l x = ⟨x₁ - x₀, y₀⟩ + ⟨x₂ - x₁, y₁⟩ + ⋯ + ⟨x - x_m, y_m⟩.
```

Taking `x = x₀` closes the chain into a cycle. -/
def chainVal (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : E × F → List (E × F) → E → ℝ
  | s, [], x => B (x - s.1) s.2
  | s, q :: l, x => B (q.1 - s.1) s.2 + chainVal B q l x

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}

@[simp] theorem chainVal_nil (s : E × F) (x : E) : chainVal B s [] x = B (x - s.1) s.2 := rfl

@[simp] theorem chainVal_cons (s q : E × F) (l : List (E × F)) (x : E) :
    chainVal B s (q :: l) x = B (q.1 - s.1) s.2 + chainVal B q l x := rfl

/-- Appending one more edge to a chain: the value along `l ++ [q]` ending at `z` is the value along
`l` ending at `q.1`, plus the last edge. This is the step that makes a chain into a longer chain in
the reconstruction below. -/
theorem chainVal_append_singleton (s q : E × F) (l : List (E × F)) (z : E) :
    chainVal B s (l ++ [q]) z = chainVal B s l q.1 + B (z - q.1) q.2 := by
  induction l generalizing s with
  | nil => simp
  | cons r l ih => simp only [List.cons_append, chainVal_cons, ih]; ring

/-- A chain is affine in its free endpoint: `chainVal B s l x = ⟨x, y⟩ - c` for a `(y, c)` that
depends only on the chain. This is why `cyclicPotential` is a supremum of affine functions. -/
theorem exists_chainVal_eq (l : List (E × F)) (s : E × F) :
    ∃ (y : F) (c : ℝ), ∀ x, chainVal B s l x = B x y - c := by
  induction l generalizing s with
  | nil =>
    refine ⟨s.2, B s.1 s.2, fun x => ?_⟩
    rw [chainVal_nil, map_sub, LinearMap.sub_apply]
  | cons q l ih =>
    obtain ⟨y, c, h⟩ := ih q
    refine ⟨y, c - B (q.1 - s.1) s.2, fun x => ?_⟩
    rw [chainVal_cons, h x]
    ring

end Chain

/-! ### Monotone and cyclically monotone multivalued mappings -/

section Monotone

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {ρ σ : SetRel E F}

/-- A multivalued mapping is **monotone** when `⟨x₁ - x₂, y₁ - y₂⟩ ≥ 0` for all pairs in its
graph. -/
def IsMonotoneRel (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) : Prop :=
  ∀ p ∈ ρ, ∀ q ∈ ρ, 0 ≤ B (p.1 - q.1) (p.2 - q.2)

/-- A multivalued mapping is **cyclically monotone** when every finite cycle in its graph has
non-positive telescoping sum. The cycle is written as a starting pair `s` followed by a list `l`;
`chainVal B s l s.1` is the sum around it. -/
def IsCyclicallyMonotone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) : Prop :=
  ∀ s ∈ ρ, ∀ l : List (E × F), (∀ q ∈ l, q ∈ ρ) → chainVal B s l s.1 ≤ 0

/-- A monotone mapping is **maximal** when no strictly larger monotone mapping contains it. -/
def IsMaximalMonotoneRel (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) : Prop :=
  IsMonotoneRel B ρ ∧ ∀ σ : SetRel E F, IsMonotoneRel B σ → ρ ⊆ σ → σ ⊆ ρ

/-- A cyclically monotone mapping is **maximal** when no strictly larger cyclically monotone
mapping contains it. These turn out to be exactly the subdifferentials. -/
def IsMaximalCyclicallyMonotone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) : Prop :=
  IsCyclicallyMonotone B ρ ∧ ∀ σ : SetRel E F, IsCyclicallyMonotone B σ → ρ ⊆ σ → σ ⊆ ρ

/-- Monotonicity passes to sub-mappings. -/
theorem IsMonotoneRel.mono (h : IsMonotoneRel B σ) (hsub : ρ ⊆ σ) : IsMonotoneRel B ρ :=
  fun p hp q hq => h p (hsub hp) q (hsub hq)

/-- Cyclic monotonicity passes to sub-mappings. -/
theorem IsCyclicallyMonotone.mono (h : IsCyclicallyMonotone B σ) (hsub : ρ ⊆ σ) :
    IsCyclicallyMonotone B ρ :=
  fun s hs l hl => h s (hsub hs) l fun q hq => hsub (hl q hq)

/-- **Cyclic monotonicity implies monotonicity**: a two-element cycle is exactly the monotonicity
inequality. -/
theorem IsCyclicallyMonotone.isMonotoneRel (h : IsCyclicallyMonotone B ρ) : IsMonotoneRel B ρ := by
  intro p hp q hq
  have hcyc := h p hp [q] (by simpa using hq)
  rw [chainVal_cons, chainVal_nil] at hcyc
  have hexp : B (p.1 - q.1) (p.2 - q.2) = -(B (q.1 - p.1) p.2 + B (p.1 - q.1) q.2) := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  rw [hexp]
  linarith

/-- A one-element mapping is cyclically monotone: every cycle in it has all its edges equal to
zero. Used only to see that a maximal cyclically monotone mapping is nonempty. -/
theorem isCyclicallyMonotone_singleton (p : E × F) : IsCyclicallyMonotone B {p} := by
  have key : ∀ l : List (E × F), (∀ q ∈ l, q ∈ ({p} : Set (E × F))) → chainVal B p l p.1 = 0 := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons q l ih =>
      intro hl
      have hq : q = p := hl q (by simp)
      subst hq
      rw [chainVal_cons, ih fun r hr => hl r (by simp [hr])]
      simp
  intro s hs l hl
  rw [Set.mem_singleton_iff] at hs
  subst hs
  exact le_of_eq (key l hl)

/-- A maximal cyclically monotone mapping is nonempty: the empty mapping is strictly contained in
the cyclically monotone `{(0, 0)}`. -/
theorem IsMaximalCyclicallyMonotone.nonempty (h : IsMaximalCyclicallyMonotone B ρ) :
    ρ.Nonempty := by
  rcases ρ.eq_empty_or_nonempty with hem | hne
  · have hsub := h.2 {((0 : E), (0 : F))} (isCyclicallyMonotone_singleton _)
      (by rw [hem]; exact Set.empty_subset _)
    rw [hem] at hsub
    exact absurd (hsub rfl) (Set.notMem_empty _)
  · exact hne

end Monotone

/-! ### Necessity: `∂f` is cyclically monotone -/

section Necessity

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- The telescoping estimate: walking a chain of subgradients from `s` to `x` cannot gain more than
the increase of `f`. The chain of inequalities
`⟨x_{i+1} - x_i, y_i⟩ ≤ f x_{i+1} - f x_i`, summed. -/
theorem le_of_chain_mem_subgradientRel :
    ∀ (l : List (E × F)) (s : E × F), s ∈ subgradientRel B f →
      (∀ q ∈ l, q ∈ subgradientRel B f) →
        ∀ x, f s.1 + ((chainVal B s l x : ℝ) : EReal) ≤ f x := by
  intro l
  induction l with
  | nil => intro s hs _ x; simpa using hs x
  | cons q l ih =>
    intro s hs hl x
    have h₁ : f s.1 + ((B (q.1 - s.1) s.2 : ℝ) : EReal) ≤ f q.1 := hs q.1
    have h₂ : f q.1 + ((chainVal B q l x : ℝ) : EReal) ≤ f x :=
      ih q (hl q (by simp)) (fun r hr => hl r (by simp [hr])) x
    calc f s.1 + ((chainVal B s (q :: l) x : ℝ) : EReal)
        = f s.1 + ((B (q.1 - s.1) s.2 : ℝ) : EReal) + ((chainVal B q l x : ℝ) : EReal) := by
          rw [chainVal_cons, _root_.EReal.coe_add, add_assoc]
      _ ≤ f q.1 + ((chainVal B q l x : ℝ) : EReal) := add_le_add h₁ (le_refl _)
      _ ≤ f x := h₂

/-- The graph of `∂f` is cyclically monotone. Convexity of `f` is not used; properness is, and
only to know that `f` is finite at the base point of the cycle. -/
theorem isCyclicallyMonotone_subgradientRel (hp : Proper f) :
    IsCyclicallyMonotone B (subgradientRel B f) := by
  intro s hs l hl
  have hkey := le_of_chain_mem_subgradientRel l s hs hl s.1
  have hdom : s.1 ∈ dom f := by
    by_contra hcon
    have hmem : s.2 ∈ subgradient B f s.1 := hs
    rw [subgradient_eq_empty_of_notMem_dom hp hcon] at hmem
    exact hmem
  have hcoe : (((f s.1).toReal : ℝ) : EReal) = f s.1 :=
    _root_.EReal.coe_toReal (ne_of_lt hdom) (hp.ne_bot s.1)
  rw [← hcoe, ← _root_.EReal.coe_add, _root_.EReal.coe_le_coe_iff] at hkey
  linarith

/-- **The subdifferential is monotone**, the classical inequality
`⟨x₁ - x₂, y₁ - y₂⟩ ≥ 0`. -/
theorem isMonotoneRel_subgradientRel (hp : Proper f) :
    IsMonotoneRel B (subgradientRel B f) :=
  (isCyclicallyMonotone_subgradientRel hp).isMonotoneRel

end Necessity

/-! ### Sufficiency: the potential -/

section Potential

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {ρ : SetRel E F} {s : E × F}

/-- The potential of a multivalued mapping `ρ`: the supremum of the telescoping sums of all finite
chains in `ρ` that start at `s` and end at `x`. Being a supremum of affine functions of `x` it is a
closed convex function, and cyclic monotonicity of `ρ` is exactly what keeps it from being `+∞` at
`s.1`. -/
noncomputable def cyclicPotential (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) (s : E × F)
    (x : E) : EReal :=
  ⨆ l ∈ {l : List (E × F) | ∀ q ∈ l, q ∈ ρ}, ((chainVal B s l x : ℝ) : EReal)

theorem le_cyclicPotential {l : List (E × F)} (hl : ∀ q ∈ l, q ∈ ρ) (s : E × F) (x : E) :
    ((chainVal B s l x : ℝ) : EReal) ≤ cyclicPotential B ρ s x :=
  le_iSup₂ (f := fun l (_ : l ∈ {l : List (E × F) | ∀ q ∈ l, q ∈ ρ}) =>
    ((chainVal B s l x : ℝ) : EReal)) l hl

theorem cyclicPotential_le {c : EReal} {x : E}
    (h : ∀ l : List (E × F), (∀ q ∈ l, q ∈ ρ) → ((chainVal B s l x : ℝ) : EReal) ≤ c) :
    cyclicPotential B ρ s x ≤ c :=
  iSup₂_le h

/-- The potential is convex: it is a supremum of affine functions. -/
theorem convexFn_cyclicPotential (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) (s : E × F) :
    ConvexFn (cyclicPotential B ρ s) := by
  refine convexFn_biSup fun l _ => ?_
  obtain ⟨y, c, h⟩ := exists_chainVal_eq (B := B) l s
  have hfun : (fun x => ((chainVal B s l x : ℝ) : EReal)) = affineFn B y c := by
    funext x
    rw [h x, affineFn_eq_coe]
  rw [hfun]
  exact convexFn_affineFn y c

/-- The potential never takes the value `-∞`: the empty chain already gives it a real lower
bound. -/
theorem cyclicPotential_ne_bot (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (ρ : SetRel E F) (s : E × F) (x : E) :
    cyclicPotential B ρ s x ≠ ⊥ := by
  intro h
  have hle := le_cyclicPotential (B := B) (ρ := ρ) (l := []) (by simp) s x
  rw [h, le_bot_iff] at hle
  exact _root_.EReal.coe_ne_bot _ hle

/-- **Cyclic monotonicity is exactly what makes the potential finite at its base point**, where it
vanishes. -/
theorem cyclicPotential_eq_zero (hρ : IsCyclicallyMonotone B ρ) (hs : s ∈ ρ) :
    cyclicPotential B ρ s s.1 = 0 := by
  refine le_antisymm (cyclicPotential_le fun l hl => ?_) ?_
  · exact_mod_cast hρ s hs l hl
  · have hle := le_cyclicPotential (B := B) (ρ := ρ) (l := []) (by simp) s s.1
    simpa using hle

/-- The potential is proper. -/
theorem proper_cyclicPotential (hρ : IsCyclicallyMonotone B ρ) (hs : s ∈ ρ) :
    Proper (cyclicPotential B ρ s) := by
  refine ⟨⟨s.1, ?_⟩, cyclicPotential_ne_bot B ρ s⟩
  change cyclicPotential B ρ s s.1 < ⊤
  rw [cyclicPotential_eq_zero hρ hs, ← _root_.EReal.coe_zero]
  exact _root_.EReal.coe_lt_top 0

/-- **Every pair of `ρ` is a subgradient of the potential.** A chain
ending at `x` followed by the edge `(x, y)` is again a chain, so the supremum defining
`f z` dominates `chainVal … x + ⟨z - x, y⟩` for every chain, hence `f x + ⟨z - x, y⟩ ≤ f z`. -/
theorem mem_subgradient_cyclicPotential {p : E × F} (hp : p ∈ ρ) :
    p.2 ∈ subgradient B (cyclicPotential B ρ s) p.1 := by
  intro z
  have key : cyclicPotential B ρ s p.1
      ≤ cyclicPotential B ρ s z - ((B (z - p.1) p.2 : ℝ) : EReal) := by
    refine cyclicPotential_le fun l hl => ?_
    have hvalid : ∀ q ∈ l ++ [p], q ∈ ρ := by
      intro q hq
      rcases List.mem_append.1 hq with h | h
      · exact hl q h
      · rw [List.mem_singleton.1 h]
        exact hp
    have hle := le_cyclicPotential (B := B) hvalid s z
    rw [chainVal_append_singleton, _root_.EReal.coe_add] at hle
    exact (_root_.EReal.le_sub_iff_add_le (b := ((B (z - p.1) p.2 : ℝ) : EReal))
      (c := cyclicPotential B ρ s z) (.inl (_root_.EReal.coe_ne_bot _))
      (.inl (_root_.EReal.coe_ne_top _))).2 hle
  exact (_root_.EReal.le_sub_iff_add_le (b := ((B (z - p.1) p.2 : ℝ) : EReal))
    (c := cyclicPotential B ρ s z) (.inl (_root_.EReal.coe_ne_bot _))
    (.inl (_root_.EReal.coe_ne_top _))).1 key

end Potential

/-! ### Cyclically monotone mappings and subdifferentials -/

section Main

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}
  {ρ : SetRel E F}

/-- A nonempty cyclically monotone multivalued mapping is contained in the subdifferential of a
closed proper convex function. -/
theorem exists_convexFn_subgradientRel_of_isCyclicallyMonotone [IsContinuousPairing B]
    (hρ : IsCyclicallyMonotone B ρ) (hne : ρ.Nonempty) :
    ∃ f : E → EReal, ConvexFn f ∧ ClosedFn f ∧ Proper f ∧ ρ ⊆ subgradientRel B f := by
  obtain ⟨s, hs⟩ := hne
  refine ⟨cyclicPotential B ρ s, convexFn_cyclicPotential B ρ s, ?_,
    proper_cyclicPotential hρ hs, fun p hp => mem_subgradient_cyclicPotential hp⟩
  refine (closedFn_iff_lowerSemicontinuous (cyclicPotential_ne_bot B ρ s)).2 ?_
  refine lowerSemicontinuous_biSup fun l _ => ?_
  obtain ⟨y, c, h⟩ := exists_chainVal_eq (B := B) l s
  have hfun : (fun x => ((chainVal B s l x : ℝ) : EReal)) = affineFn B y c := by
    funext x
    rw [h x, affineFn_eq_coe]
  rw [hfun]
  exact lowerSemicontinuous_affineFn (continuous_pairing B y)

/-- For a nonempty multivalued mapping, being contained in a subdifferential and being
cyclically monotone are the same thing. -/
theorem isCyclicallyMonotone_iff_exists_convexFn [IsContinuousPairing B] (hne : ρ.Nonempty) :
    IsCyclicallyMonotone B ρ ↔
      ∃ f : E → EReal, ConvexFn f ∧ ClosedFn f ∧ Proper f ∧ ρ ⊆ subgradientRel B f :=
  ⟨fun h => exists_convexFn_subgradientRel_of_isCyclicallyMonotone h hne,
    fun ⟨_, _, _, hp, hsub⟩ => (isCyclicallyMonotone_subgradientRel hp).mono hsub⟩

/-- The half the reconstruction gives at once: a maximal cyclically monotone multivalued mapping
*is* the subdifferential of a closed proper convex function. -/
theorem exists_eq_subgradientRel_of_isMaximalCyclicallyMonotone [IsContinuousPairing B]
    (h : IsMaximalCyclicallyMonotone B ρ) :
    ∃ f : E → EReal, ConvexFn f ∧ ClosedFn f ∧ Proper f ∧ ρ = subgradientRel B f := by
  obtain ⟨f, hconv, hclosed, hproper, hsub⟩ :=
    exists_convexFn_subgradientRel_of_isCyclicallyMonotone h.1 h.nonempty
  exact ⟨f, hconv, hclosed, hproper,
    Subset.antisymm hsub (h.2 _ (isCyclicallyMonotone_subgradientRel hproper) hsub)⟩

end Main

/-! ### The graph of `∂f` is closed -/

section GraphClosed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [AddCommGroup F]
  [Module ℝ F] [TopologicalSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- The graph of `∂f` is closed in `E × F`; equivalently `xᵢ* ∈ ∂f xᵢ`,
`xᵢ → x` and `xᵢ* → x*` force `x* ∈ ∂f x`. Convexity of `f` is not used. Lower semicontinuity is,
and so is joint continuity of the pairing: the subgradient inequality at `xᵢ` involves
`⟨z - xᵢ, xᵢ*⟩`, where both arguments move. -/
theorem isClosed_subgradientRel [IsTopologicalAddGroup E]
    (hB : Continuous fun p : E × F => B p.1 p.2) (hp : Proper f)
    (hlsc : LowerSemicontinuous f) : IsClosed (subgradientRel B f) := by
  have hepi : IsClosed (epi f) := lowerSemicontinuous_iff_isClosed_epi.1 hlsc
  have hrw : subgradientRel B f
      = ⋂ z : E, {p : E × F | f p.1 + ((B (z - p.1) p.2 : ℝ) : EReal) ≤ f z} := by
    ext p
    simp only [Set.mem_iInter]
    exact Iff.rfl
  rw [hrw]
  refine isClosed_iInter fun z => ?_
  rcases eq_or_ne (f z) ⊤ with hz | hz
  · convert isClosed_univ
    ext p
    simp [hz]
  · set r : ℝ := (f z).toReal with hrdef
    have hrz : ((r : ℝ) : EReal) = f z := _root_.EReal.coe_toReal hz (hp.ne_bot z)
    have hset : {p : E × F | f p.1 + ((B (z - p.1) p.2 : ℝ) : EReal) ≤ f z}
        = (fun p : E × F => (p.1, r - B (z - p.1) p.2)) ⁻¹' epi f := by
      ext p
      rw [Set.mem_preimage, mem_epi, Set.mem_ofPred_eq, ← hrz, _root_.EReal.coe_sub]
      exact (_root_.EReal.le_sub_iff_add_le (b := ((B (z - p.1) p.2 : ℝ) : EReal))
        (c := ((r : ℝ) : EReal)) (.inl (_root_.EReal.coe_ne_bot _))
        (.inl (_root_.EReal.coe_ne_top _))).symm
    rw [hset]
    refine hepi.preimage (continuous_fst.prodMk ?_)
    exact continuous_const.sub
      (hB.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd))

end GraphClosed

/-! ### Increments along a chain of subgradients -/

section Increment

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

/-- One half of the subgradient inequality, read as a bound on an increment of `f`: a subgradient
at the *left* endpoint underestimates the increment. -/
theorem pairing_le_sub_of_mem_subgradient {p q : E} {a b : ℝ} {u : F}
    (hp : f p = (a : EReal)) (hq : f q = (b : EReal)) (hu : u ∈ subgradient B f p) :
    B (q - p) u ≤ b - a := by
  have h := hu q
  rw [hp, hq, ← _root_.EReal.coe_add, _root_.EReal.coe_le_coe_iff] at h
  linarith

/-- The other half: a subgradient at the *right* endpoint overestimates the increment. -/
theorem sub_le_pairing_of_mem_subgradient {p q : E} {a b : ℝ} {v : F}
    (hp : f p = (a : EReal)) (hq : f q = (b : EReal)) (hv : v ∈ subgradient B f q) :
    b - a ≤ B (q - p) v := by
  have h := hv p
  rw [hq, hp, ← _root_.EReal.coe_add, _root_.EReal.coe_le_coe_iff] at h
  have hexp : B (p - q) v = -(B (q - p) v) := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  rw [hexp] at h
  linarith

/-- The subdivision estimate. Along a chain of equally spaced points `x 0, …, x N` with common
step `d`, with `v i ∈ ∂f (x i)` and `∂f ⊆ ∂g`, the increments of `f` and of `g` across the chain
differ by at most `⟨d, v N - v 0⟩`: both are trapped between the *same* two telescoping sums, since
the subgradients of `f` serve `g` as well. Halving the step halves the bound while leaving the ends
of the chain alone, which is what forces the two increments to agree. -/
theorem abs_sub_increment_le (hsub : subgradientRel B f ⊆ subgradientRel B g)
    {x : ℕ → E} {v : ℕ → F} {a b : ℕ → ℝ} {d : E} {N : ℕ}
    (hx : ∀ i < N, x (i + 1) = x i + d)
    (hv : ∀ i ≤ N, v i ∈ subgradient B f (x i))
    (ha : ∀ i ≤ N, f (x i) = ((a i : ℝ) : EReal))
    (hb : ∀ i ≤ N, g (x i) = ((b i : ℝ) : EReal)) :
    |(a N - a 0) - (b N - b 0)| ≤ B d (v N - v 0) := by
  have step : ∀ i, i < N →
      |(a (i + 1) - a i) - (b (i + 1) - b i)| ≤ B d (v (i + 1)) - B d (v i) := by
    intro i hi
    have hi' : i ≤ N := hi.le
    have hd : x (i + 1) - x i = d := by rw [hx i hi]; abel
    have hvi : v i ∈ subgradient B f (x i) := hv i hi'
    have hvi1 : v (i + 1) ∈ subgradient B f (x (i + 1)) := hv (i + 1) hi
    have hgi : v i ∈ subgradient B g (x i) :=
      hsub (show ((x i, v i) : E × F) ∈ subgradientRel B f from hvi)
    have hgi1 : v (i + 1) ∈ subgradient B g (x (i + 1)) :=
      hsub (show ((x (i + 1), v (i + 1)) : E × F) ∈ subgradientRel B f from hvi1)
    have h1 := pairing_le_sub_of_mem_subgradient (ha i hi') (ha (i + 1) hi) hvi
    have h2 := sub_le_pairing_of_mem_subgradient (ha i hi') (ha (i + 1) hi) hvi1
    have h3 := pairing_le_sub_of_mem_subgradient (hb i hi') (hb (i + 1) hi) hgi
    have h4 := sub_le_pairing_of_mem_subgradient (hb i hi') (hb (i + 1) hi) hgi1
    rw [hd] at h1 h2 h3 h4
    rw [abs_le]
    constructor <;> linarith
  have hsum : ∑ i ∈ Finset.range N, ((a (i + 1) - a i) - (b (i + 1) - b i))
      = (a N - a 0) - (b N - b 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub a N, Finset.sum_range_sub b N]
  calc |(a N - a 0) - (b N - b 0)|
      = |∑ i ∈ Finset.range N, ((a (i + 1) - a i) - (b (i + 1) - b i))| := by rw [hsum]
    _ ≤ ∑ i ∈ Finset.range N, |(a (i + 1) - a i) - (b (i + 1) - b i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range N, (B d (v (i + 1)) - B d (v i)) :=
        Finset.sum_le_sum fun i hi => step i (Finset.mem_range.1 hi)
    _ = B d (v N) - B d (v 0) := Finset.sum_range_sub (fun i => B d (v i)) N
    _ = B d (v N - v 0) := (map_sub (B d) _ _).symm

end Increment

/-! ### Raising a function by a constant -/

section AddConst

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **Raising a function by a real constant lowers its conjugate by that constant.** This is the
one piece of conjugacy the rigidity argument needs beyond Fenchel–Moreau: `∂f ⊆ ∂g` pins `g` to
`f + α` only after the same relation on the conjugate side has been turned back into an inequality
on `E`. -/
theorem conj_add_coe (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (α : ℝ) :
    conj B (fun x => f x + (α : EReal)) = fun y => conj B f y + ((-α : ℝ) : EReal) := by
  funext y
  rw [conj_apply, conj_apply, EReal.iSup_add_coe]
  exact iSup_congr fun x => EReal.coe_sub_add_coe' _ _ _

end AddConst

/-! ### `∂f` determines `f` up to an additive constant -/

section Uniqueness

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

omit [FiniteDimensional ℝ E] in
/-- A point at which a proper function is subdifferentiable is a point where it is finite. -/
theorem exists_coe_of_subgradient_nonempty (hpg : Proper g) {x : E}
    (h : (subgradient B g x).Nonempty) : ∃ c : ℝ, g x = (c : EReal) := by
  have hxdom : x ∈ dom g := by
    by_contra hc
    rw [subgradient_eq_empty_of_notMem_dom hpg hc] at h
    exact absurd h Set.not_nonempty_empty
  exact EReal.exists_coe_of_ne_bot_of_lt_top (hpg.ne_bot x) hxdom

/-- The analytic core: if `∂f ⊆ ∂g` then `f` and `g` have the same increments between relative
interior points of `dom f`. The classical proof integrates the common one-sided derivative along
the segment, through the one-dimensional theory; the argument here needs none of it. Subdivide
`[x₁, x₂]` into `N` equal steps and pick `v i ∈ ∂f (x i)` at each node; each step
traps both increments in `[⟨d, v i⟩, ⟨d, v (i+1)⟩]`, so the two differ by at most the telescoping
total `N⁻¹ ⟨x₂ - x₁, v N - v 0⟩`, which tends to `0`. -/
theorem increment_eq_of_subgradientRel_subset [IsCompatiblePairing B]
    (hf : ConvexFn f) (hpf : Proper f) (hpg : Proper g)
    (hsub : subgradientRel B f ⊆ subgradientRel B g)
    {x₁ x₂ : E} {a₁ a₂ b₁ b₂ : ℝ} (h₁ : x₁ ∈ ri (dom f)) (h₂ : x₂ ∈ ri (dom f))
    (hfa₁ : f x₁ = (a₁ : EReal)) (hfa₂ : f x₂ = (a₂ : EReal))
    (hgb₁ : g x₁ = (b₁ : EReal)) (hgb₂ : g x₂ = (b₂ : EReal)) :
    a₂ - a₁ = b₂ - b₁ := by
  obtain ⟨u₀, hu₀⟩ := subgradient_nonempty_of_mem_relint_dom (B := B) hf hpf h₁
  obtain ⟨u₁, hu₁⟩ := subgradient_nonempty_of_mem_relint_dom (B := B) hf hpf h₂
  set C : ℝ := B (x₂ - x₁) (u₁ - u₀) with hC
  have key : ∀ N : ℕ, 0 < N → |(a₂ - a₁) - (b₂ - b₁)| ≤ (N : ℝ)⁻¹ * C := by
    intro N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
    set d : E := (N : ℝ)⁻¹ • (x₂ - x₁) with hd
    set x : ℕ → E := fun i => x₁ + (i : ℝ) • d with hxdef
    have hx0 : x 0 = x₁ := by simp [hxdef]
    have hxN : x N = x₂ := by
      simp only [hxdef, hd, smul_smul, mul_inv_cancel₀ hN0, one_smul]
      abel
    have hxstep : ∀ i < N, x (i + 1) = x i + d := by
      intro i _
      simp only [hxdef]
      push_cast
      rw [add_smul, one_smul]
      abel
    have hxmem : ∀ i ≤ N, x i ∈ ri (dom f) := by
      intro i hi
      have ht0 : (0 : ℝ) ≤ (i : ℝ) / (N : ℝ) := by positivity
      have ht1 : (i : ℝ) / (N : ℝ) ≤ 1 := by
        rw [div_le_one hNpos]
        exact_mod_cast hi
      have heq : x i = (1 - (i : ℝ) / (N : ℝ)) • x₁ + ((i : ℝ) / (N : ℝ)) • x₂ := by
        have hxi : x i = x₁ + ((i : ℝ) / (N : ℝ)) • (x₂ - x₁) := by
          simp only [hxdef, hd, smul_smul, div_eq_mul_inv]
        rw [hxi]
        module
      rw [heq]
      exact Convex.relint hf.convex_dom h₁ h₂ (by linarith) ht0 (by ring)
    have hex : ∀ i, ∃ u : F, i ≤ N → u ∈ subgradient B f (x i) := by
      intro i
      by_cases hi : i ≤ N
      · obtain ⟨u, hu⟩ := subgradient_nonempty_of_mem_relint_dom (B := B) hf hpf (hxmem i hi)
        exact ⟨u, fun _ => hu⟩
      · exact ⟨0, fun hc => absurd hc hi⟩
    choose u hu using hex
    set v : ℕ → F := fun i => if i = 0 then u₀ else if i = N then u₁ else u i with hvdef
    have hvmem : ∀ i ≤ N, v i ∈ subgradient B f (x i) := by
      intro i hi
      simp only [hvdef]
      split
      · rename_i hi0
        subst hi0
        rw [hx0]
        exact hu₀
      · split
        · rename_i hiN
          subst hiN
          rw [hxN]
          exact hu₁
        · exact hu i hi
    have hfa : ∀ i ≤ N, f (x i) = (((f (x i)).toReal : ℝ) : EReal) := by
      intro i hi
      refine (_root_.EReal.coe_toReal ?_ (hpf.ne_bot _)).symm
      exact (mem_dom.1 (intrinsicInterior_subset (hxmem i hi))).ne
    have hgb : ∀ i ≤ N, g (x i) = (((g (x i)).toReal : ℝ) : EReal) := by
      intro i hi
      obtain ⟨c, hc⟩ := exists_coe_of_subgradient_nonempty hpg
        ⟨v i, hsub (show ((x i, v i) : E × F) ∈ subgradientRel B f from hvmem i hi)⟩
      rw [hc]
      simp
    have hchain := abs_sub_increment_le hsub (x := x) (v := v)
      (a := fun i => (f (x i)).toReal) (b := fun i => (g (x i)).toReal) (d := d) (N := N)
      hxstep hvmem hfa hgb
    have hv0 : v 0 = u₀ := by simp [hvdef]
    have hvN : v N = u₁ := by simp [hvdef, hN.ne']
    have hBd : B d (v N - v 0) = (N : ℝ)⁻¹ * C := by
      rw [hvN, hv0, hd, map_smul, LinearMap.smul_apply, smul_eq_mul, hC]
    have ha0 : (f (x 0)).toReal = a₁ := by rw [hx0, hfa₁]; simp
    have haN : (f (x N)).toReal = a₂ := by rw [hxN, hfa₂]; simp
    have hb0 : (g (x 0)).toReal = b₁ := by rw [hx0, hgb₁]; simp
    have hbN : (g (x N)).toReal = b₂ := by rw [hxN, hgb₂]; simp
    simp only [ha0, haN, hb0, hbN, hBd] at hchain
    exact hchain
  have hlim : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * C) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_nhds_zero_nat.mul_const C
  have hle : |(a₂ - a₁) - (b₂ - b₁)| ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_gt_atTop 0] with N hN using key N hN
  have hzero := abs_nonpos_iff.1 hle
  linarith

/-- The geometric half: if `∂f ⊆ ∂g` then `g ≤ f + α` for a real constant `α`, with equality on
`cl (dom f)`. Agreement of the increments on `ri (dom f)` fixes `α`, and a closed convex function
is the limit of its values along a segment running into a boundary point, which carries the
identity out to `cl (dom f)`. Off `cl (dom f)` the right-hand side is `⊤`. -/
theorem exists_forall_le_add_coe_of_subgradientRel_subset [IsCompatiblePairing B]
    (hf : ConvexFn f) (hpf : Proper f) (hcf : ClosedFn f)
    (hg : ConvexFn g) (hpg : Proper g) (hlg : LowerSemicontinuous g)
    (hsub : subgradientRel B f ⊆ subgradientRel B g) :
    ∃ α : ℝ, (∀ y, g y ≤ f y + (α : EReal)) ∧
      ∀ y ∈ closure (dom f), g y = f y + (α : EReal) := by
  obtain ⟨z, hz⟩ := Convex.relint_nonempty hf.convex_dom hpf.dom_nonempty
  have hfinf : ∀ x ∈ ri (dom f), f x = (((f x).toReal : ℝ) : EReal) := fun x hx =>
    (_root_.EReal.coe_toReal (mem_dom.1 (intrinsicInterior_subset hx)).ne (hpf.ne_bot x)).symm
  have hfing : ∀ x ∈ ri (dom f), g x = (((g x).toReal : ℝ) : EReal) := by
    intro x hx
    obtain ⟨u, hu⟩ := subgradient_nonempty_of_mem_relint_dom (B := B) hf hpf hx
    obtain ⟨c, hc⟩ := exists_coe_of_subgradient_nonempty hpg
      ⟨u, hsub (show ((x, u) : E × F) ∈ subgradientRel B f from hu)⟩
    rw [hc]
    simp
  set α : ℝ := (g z).toReal - (f z).toReal with hα
  have claim1 : ∀ x ∈ ri (dom f), g x = f x + (α : EReal) := by
    intro x hx
    have h := increment_eq_of_subgradientRel_subset hf hpf hpg hsub hz hx
      (hfinf z hz) (hfinf x hx) (hfing z hz) (hfing x hx)
    rw [hfinf x hx, hfing x hx, ← _root_.EReal.coe_add, _root_.EReal.coe_eq_coe_iff, hα]
    linarith
  have hcf' : clFn f = f := hcf
  have claim2 : ∀ y ∈ closure (dom f), g y = f y + (α : EReal) := by
    intro y hy
    have hseg : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ),
        g ((1 - a) • z + a • y) = f ((1 - a) • z + a • y) + (α : EReal) := by
      filter_upwards [eventually_mem_Ico_nhdsLT_one] with a ha
      exact claim1 _ (Convex.segment_mem_relint hf.convex_dom hz hy ha.1 ha.2)
    have hftend : Tendsto (fun a : ℝ => f ((1 - a) • z + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (f y)) := by
      have h := hf.tendsto_clFn_along_segment_relint hpf hz y
      rwa [hcf'] at h
    refine le_antisymm ?_ ?_
    · by_contra hcon
      rw [not_le] at hcon
      obtain ⟨c, hc1, hc2⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hcon
      have hfyt : f y ≠ ⊤ := by
        intro h
        rw [h, _root_.EReal.top_add_coe] at hc1
        exact absurd hc1 not_top_lt
      obtain ⟨t, ht⟩ :=
        EReal.exists_coe_of_ne_bot_of_lt_top (hpf.ne_bot y) (lt_top_iff_ne_top.2 hfyt)
      rw [ht, ← _root_.EReal.coe_add, _root_.EReal.coe_lt_coe_iff] at hc1
      have h1 : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), f ((1 - a) • z + a • y) < ((c - α : ℝ) : EReal) := by
        refine hftend.eventually_lt_const ?_
        rw [ht, _root_.EReal.coe_lt_coe_iff]
        linarith
      have h2 : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), ((c : ℝ) : EReal) < g ((1 - a) • z + a • y) :=
        (tendsto_segment z y).eventually (hlg y (c : EReal) hc2)
      obtain ⟨a, ⟨ha1, ha2⟩, ha3⟩ := ((h1.and h2).and hseg).exists
      have hlt : g ((1 - a) • z + a • y) < ((c : ℝ) : EReal) := by
        rw [ha3]
        have h := _root_.EReal.add_lt_add_right_coe ha1 α
        rwa [← _root_.EReal.coe_add, show c - α + α = c by ring] at h
      exact absurd (ha2.trans hlt) (lt_irrefl _)
    · by_contra hcon
      rw [not_le] at hcon
      obtain ⟨c, hc1, hc2⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hcon
      obtain ⟨s, hs⟩ :=
        EReal.exists_coe_of_ne_bot_of_lt_top (hpg.ne_bot y) (lt_top_iff_ne_top.2 hc1.ne_top)
      have hsc : s < c := by rw [hs, _root_.EReal.coe_lt_coe_iff] at hc1; exact hc1
      have hfy : ((c - α : ℝ) : EReal) < f y := by
        by_contra hle
        rw [not_lt] at hle
        have h : f y + (α : EReal) ≤ ((c - α : ℝ) : EReal) + (α : EReal) := add_le_add hle le_rfl
        rw [← _root_.EReal.coe_add, show c - α + α = c by ring] at h
        exact absurd (hc2.trans_le h) (lt_irrefl _)
      have h1 : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), ((c - α : ℝ) : EReal) < f ((1 - a) • z + a • y) :=
        hftend.eventually_const_lt hfy
      have h2 : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ),
          g ((1 - a) • z + a • y) ≤ (((1 - a) * (g z).toReal + a * s : ℝ) : EReal) := by
        filter_upwards [eventually_mem_Ico_nhdsLT_one] with a ha
        exact hg.epi_combo (le_of_eq (hfing z hz)) (le_of_eq hs) (by linarith [ha.2]) ha.1
          (by ring)
      have h3 : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), ((1 - a) * (g z).toReal + a * s : ℝ) < c :=
        (tendsto_affine_nhdsLT_one _ s).eventually_lt_const hsc
      obtain ⟨a, ⟨ha1, ha2⟩, ha3, ha4⟩ := ((h1.and h2).and (h3.and hseg)).exists
      have hlt1 : ((c : ℝ) : EReal) < g ((1 - a) • z + a • y) := by
        rw [ha4]
        have h := _root_.EReal.add_lt_add_right_coe ha1 α
        rwa [← _root_.EReal.coe_add, show c - α + α = c by ring] at h
      have hlt2 : g ((1 - a) • z + a • y) < ((c : ℝ) : EReal) :=
        lt_of_le_of_lt ha2 (by exact_mod_cast ha3)
      exact absurd (hlt1.trans hlt2) (lt_irrefl _)
  refine ⟨α, fun y => ?_, claim2⟩
  by_cases hy : y ∈ closure (dom f)
  · exact le_of_eq (claim2 y hy)
  · have hyd : y ∉ dom f := fun hc => hy (subset_closure hc)
    have htop : f y = ⊤ := by
      by_contra hc
      exact hyd (mem_dom.2 (lt_top_iff_ne_top.2 hc))
    rw [htop, _root_.EReal.top_add_coe]
    exact le_top

end Uniqueness

/-! ### Maximality of the subdifferential -/

section MaximalCyclic

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- Raising a function by a real constant does not change its subdifferential. -/
@[simp] theorem subgradient_add_coe (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (α : ℝ) (x : E) :
    subgradient B (fun x => f x + (α : EReal)) x = subgradient B f x := by
  ext y
  simp only [mem_subgradient]
  refine forall_congr' fun z => ?_
  rw [add_right_comm]
  exact (_root_.EReal.addLECancellable_coe α).add_le_add_iff_right

/-- The graph form of `subgradient_add_coe`. -/
theorem subgradientRel_add_coe (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (α : ℝ) :
    subgradientRel B (fun x => f x + (α : EReal)) = subgradientRel B f :=
  Set.ext fun p => by
    simp only [subgradientRel, Set.mem_ofPred_eq, subgradient_add_coe]

end MaximalCyclic

section Maximality

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

/-- A closed proper convex function is determined by its subdifferential up to an additive
constant, and already by the *inclusion* `∂f ⊆ ∂g`.

The geometric half gives `g ≤ f + α` with equality on `cl (dom f)`; inverting the subdifferential
turns `∂f ⊆ ∂g` into `∂f* ⊆ ∂g*` and repeats it on the conjugate side, giving `g* ≤ f* + β`.
Equality in Fenchel's inequality at a pair of the graph of `∂f`, where both hold, forces `β = -α`,
and conjugating `g* ≤ (f + α)*` back gives `g ≥ f + α`. -/
theorem eq_add_coe_of_subgradientRel_subset [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : ClosedProperConvexFn f) (hg : ClosedProperConvexFn g)
    (hsub : subgradientRel B f ⊆ subgradientRel B g) :
    ∃ α : ℝ, ∀ x, g x = f x + (α : EReal) := by
  obtain ⟨α, hle, heq⟩ := exists_forall_le_add_coe_of_subgradientRel_subset hf.convex hf.proper
    hf.closed hg.convex hg.proper hg.lowerSemicontinuous hsub
  have hfstar : ClosedProperConvexFn (conj B f) :=
    ⟨convexFn_conj B f, closedFn_conj, proper_conj hf⟩
  have hgstar : ClosedProperConvexFn (conj B g) :=
    ⟨convexFn_conj B g, closedFn_conj, proper_conj hg⟩
  have hsub' : subgradientRel B.flip (conj B f) ⊆ subgradientRel B.flip (conj B g) := by
    rw [subgradientRel_conj_eq_inv hf.convex hf.closed,
      subgradientRel_conj_eq_inv hg.convex hg.closed]
    exact fun p hp => hsub hp
  obtain ⟨β, hleβ, heqβ⟩ := exists_forall_le_add_coe_of_subgradientRel_subset hfstar.convex
    hfstar.proper hfstar.closed hgstar.convex hgstar.proper hgstar.lowerSemicontinuous hsub'
  -- The two constants are opposite: use equality in Fenchel's inequality on the graph of `∂f`.
  obtain ⟨x, hx⟩ := Convex.relint_nonempty hf.convex.convex_dom hf.proper.dom_nonempty
  obtain ⟨y, hy⟩ := subgradient_nonempty_of_mem_relint_dom (B := B) hf.convex hf.proper hx
  have hxdom : x ∈ dom f := intrinsicInterior_subset hx
  have hfx : f x + conj B f y = ((B x y : ℝ) : EReal) :=
    (Proper.mem_subgradient_iff_add_conj_eq hf.proper).1 hy
  have hgx : g x + conj B g y = ((B x y : ℝ) : EReal) :=
    (Proper.mem_subgradient_iff_add_conj_eq hg.proper).1
      (hsub (show ((x, y) : E × F) ∈ subgradientRel B f from hy))
  obtain ⟨p, hp⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot x) hxdom
  have hqbot : conj B f y ≠ ⊥ := conj_ne_bot (B := B) hf.proper.dom_nonempty y
  have hqtop : conj B f y ≠ ⊤ := by
    intro hc
    rw [hp, hc, _root_.EReal.coe_add_top] at hfx
    exact absurd hfx.symm (_root_.EReal.coe_ne_top _)
  obtain ⟨q, hq⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hqbot (lt_top_iff_ne_top.2 hqtop)
  have hydom : y ∈ dom (conj B f) := mem_dom.2 (lt_top_iff_ne_top.2 hqtop)
  have hgxval : g x = ((p + α : ℝ) : EReal) := by
    rw [heq x (subset_closure hxdom), hp, ← _root_.EReal.coe_add]
  have hgyval : conj B g y = ((q + β : ℝ) : EReal) := by
    rw [heqβ y (subset_closure hydom), hq, ← _root_.EReal.coe_add]
  rw [hp, hq, ← _root_.EReal.coe_add, _root_.EReal.coe_eq_coe_iff] at hfx
  rw [hgxval, hgyval, ← _root_.EReal.coe_add, _root_.EReal.coe_eq_coe_iff] at hgx
  have hβ : β = -α := by linarith
  -- Conjugating `g* ≤ (f + α)*` back to `E`.
  have hstar : conj B (fun x => f x + (α : EReal)) = fun y => conj B f y + ((-α : ℝ) : EReal) :=
    conj_add_coe B f α
  have hgle : conj B g ≤ conj B (fun x => f x + (α : EReal)) := by
    rw [hstar]
    intro y
    rw [← hβ]
    exact hleβ y
  have hbcf : conj B.flip (conj B f) = f := biconj_eq_self hf.convex hf.closed
  have hbcg : conj B.flip (conj B g) = g := biconj_eq_self hg.convex hg.closed
  have hbih : conj B.flip (conj B (fun x => f x + (α : EReal))) = fun x => f x + (α : EReal) := by
    rw [hstar, conj_add_coe B.flip (conj B f) (-α), neg_neg]
    funext x
    rw [congrFun hbcf x]
  have hge := conj_antitone B.flip hgle
  rw [hbih, hbcg] at hge
  exact ⟨α, fun x => le_antisymm (hle x) (Pi.le_def.1 hge x)⟩

/-- The subdifferential of a closed proper convex function is a *maximal* cyclically monotone
mapping. If `∂f ⊆ σ` with `σ` cyclically monotone then the reconstruction puts `σ ⊆ ∂g` for some
closed proper convex `g`; uniqueness makes `g = f + α`, and a constant does not change a
subdifferential. -/
theorem isMaximalCyclicallyMonotone_subgradientRel [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (hf : ClosedProperConvexFn f) :
    IsMaximalCyclicallyMonotone B (subgradientRel B f) := by
  refine ⟨isCyclicallyMonotone_subgradientRel hf.proper, fun σ hσ hsub => ?_⟩
  obtain ⟨x, hx⟩ := Convex.relint_nonempty hf.convex.convex_dom hf.proper.dom_nonempty
  obtain ⟨y, hy⟩ := subgradient_nonempty_of_mem_relint_dom (B := B) hf.convex hf.proper hx
  obtain ⟨g, hgconv, hgclosed, hgproper, hgsub⟩ :=
    exists_convexFn_subgradientRel_of_isCyclicallyMonotone hσ
      ⟨(x, y), hsub (show ((x, y) : E × F) ∈ subgradientRel B f from hy)⟩
  obtain ⟨α, hα⟩ := eq_add_coe_of_subgradientRel_subset hf ⟨hgconv, hgclosed, hgproper⟩
    (hsub.trans hgsub)
  have hgeq : g = fun x => f x + (α : EReal) := funext hα
  rw [hgeq, subgradientRel_add_coe] at hgsub
  exact hgsub

/-- In full: on a finite-dimensional space the maximal cyclically monotone mappings are exactly
the subdifferentials of the closed proper convex functions. -/
theorem isMaximalCyclicallyMonotone_iff_exists_closedProperConvexFn [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] {ρ : SetRel E F} :
    IsMaximalCyclicallyMonotone B ρ ↔
      ∃ f : E → EReal, ClosedProperConvexFn f ∧ ρ = subgradientRel B f := by
  constructor
  · intro h
    obtain ⟨f, hconv, hclosed, hproper, heq⟩ :=
      exists_eq_subgradientRel_of_isMaximalCyclicallyMonotone h
    exact ⟨f, ⟨hconv, hclosed, hproper⟩, heq⟩
  · rintro ⟨f, hf, rfl⟩
    exact isMaximalCyclicallyMonotone_subgradientRel hf

end Maximality

end ConvexAnalysis
