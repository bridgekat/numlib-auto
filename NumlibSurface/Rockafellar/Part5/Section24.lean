import Numlib.Analysis.Convex.Subdifferential.Bounded
import Numlib.Analysis.Convex.Subdifferential.Convergence
import Numlib.Analysis.Convex.Subdifferential.Integral
import Numlib.Analysis.Convex.Subdifferential.Primitive
import NumlibSurface.Common.Euclidean

/-!
# Rockafellar, §24: Differential Continuity and Monotonicity

The continuity and monotonicity properties of `∂f`, first on the line and then on `ℝⁿ`, ending with
the characterisation of the subdifferentials as the maximal cyclically monotone mappings.

All eleven numbered results of §24 are formalized: Theorems 24.1–24.9 and Corollaries 24.2.1,
24.5.1.

**Two ambient spaces.** Theorems 24.1–24.3 are about a closed proper convex function on `R`, and
are stated here over `ℝ` itself rather than over `Rn 1`: that is the book's own reading, since a
one-sided derivative, a non-decreasing function and a subset of `R²` are real-analytic objects
rather than coordinate ones. The pairing on the line is `innerₗ ℝ`, which is multiplication.
Theorems 24.4–24.9 are over `Rn n` with `pairing n`.

`f'₊` and `f'₋` are the backbone's `rightDeriv` and `leftDeriv`, whose definitions already carry
Rockafellar's extension by `+∞` to the right of `dom f` and `-∞` to the left, so nothing here
case-splits on the position of `x`. Where `f` is finite the guard is inert, and `f'₊(x) = f'(x; 1)`,
`f'₋(x) = -f'(x; -1)`.

The book gives two descriptions of a **complete non-decreasing curve** in `R²`: as
`Γ = {(x, x*) | φ₋(x) ≤ x* ≤ φ₊(x)}` for a non-decreasing `φ` not everywhere infinite, and as a
maximal totally ordered subset of `R²` for the coordinatewise ordering. The second is taken here as
`IsCompleteNonDecreasingCurve`, Mathlib's `IsMaxChain (· ≤ ·)` on `ℝ × ℝ`; the first is the
backbone's `monotoneCurve`, and `isCompleteNonDecreasingCurve_iff_exists_monotone` is the
equivalence, which the book asserts without proof.

**Maximal cyclic monotonicity is not maximal monotonicity.** Rockafellar warns explicitly that
Corollary 31.5.2 does *not* follow from Theorem 24.9 together with "cyclically monotone implies
monotone", since a mapping maximal in the smaller class need not be maximal in the larger. So
`theorem_24_9` is about maximal *cyclic* monotonicity only, `isMonotoneRel_subgradientRel_rn` about
plain monotonicity, and nothing here bridges them. On the line the two classes do coincide
(`isMonotoneRel_iff_isCyclicallyMonotone_line`), which is why Theorem 24.3 can speak of maximal
chains at all.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §24.
-/

open Set Filter Topology
open scoped Pointwise RealInnerProductSpace

namespace Rockafellar

open ConvexAnalysis NumlibSurface

/-! ### Theorem 24.1: the one-sided derivatives on the line -/

section OneDim

variable {f : ℝ → EReal}

/-- **Theorem 24.1**: `f'₊` is non-decreasing on `R`. Closedness is not needed here nor in the next
three clauses: the interlacing chain is an inequality between difference quotients. -/
theorem theorem_24_1_monotone_rightDeriv (hf : ConvexFn f) (hp : Proper f) :
    Monotone (rightDeriv f) :=
  monotone_rightDeriv hf hp

/-- **Rockafellar, Theorem 24.1**: `f'₋` is a non-decreasing function on `R`. -/
theorem theorem_24_1_monotone_leftDeriv (hf : ConvexFn f) (hp : Proper f) :
    Monotone (leftDeriv f) :=
  monotone_leftDeriv hf hp

/-- **Theorem 24.1**: `f'₊` and `f'₋` are finite exactly on `int (dom f)`. The book says "finite on
the interior"; the biconditional says slightly more, that finiteness *characterises* it. -/
theorem theorem_24_1_finite_iff (hf : ConvexFn f) (hp : Proper f) {x : ℝ} :
    (⊥ < leftDeriv f x ∧ rightDeriv f x < ⊤) ↔ x ∈ interior (dom f) :=
  bot_lt_leftDeriv_and_rightDeriv_lt_top_iff hf hp

/-- **Rockafellar, Theorem 24.1**, the interlacing chain:
`f'₊(z₁) ≤ f'₋(x) ≤ f'₊(x) ≤ f'₋(z₂)` when `z₁ < x < z₂`. -/
theorem theorem_24_1_chain (hf : ConvexFn f) (hp : Proper f) {z₁ x z₂ : ℝ} (h₁ : z₁ < x)
    (h₂ : x < z₂) :
    rightDeriv f z₁ ≤ leftDeriv f x ∧ leftDeriv f x ≤ rightDeriv f x ∧
      rightDeriv f x ≤ leftDeriv f z₂ :=
  ⟨rightDeriv_le_leftDeriv hp h₁, leftDeriv_le_rightDeriv hf hp x, rightDeriv_le_leftDeriv hp h₂⟩

/-- **Theorem 24.1**, first limit formula: `lim_{z ↓ x} f'₊(z) = f'₊(x)`. Closedness is essential
here and in the three companions: for the proper convex `f` that is `1` at `0`, `0` on `(0, ∞)` and
`+∞` on `(-∞, 0)`, `f'₊` is `-∞` at `0` and `0` to the right of it. -/
theorem theorem_24_1_tendsto_rightDeriv_Ioi (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (rightDeriv f) (𝓝[>] x) (𝓝 (rightDeriv f x)) :=
  tendsto_rightDeriv_nhdsWithin_Ioi hf x

/-- **Rockafellar, Theorem 24.1**, second limit formula: `lim_{z ↑ x} f'₊(z) = f'₋(x)`. -/
theorem theorem_24_1_tendsto_rightDeriv_Iio (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (rightDeriv f) (𝓝[<] x) (𝓝 (leftDeriv f x)) :=
  tendsto_rightDeriv_nhdsWithin_Iio hf x

/-- **Rockafellar, Theorem 24.1**, third limit formula: `lim_{z ↓ x} f'₋(z) = f'₊(x)`. -/
theorem theorem_24_1_tendsto_leftDeriv_Ioi (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (leftDeriv f) (𝓝[>] x) (𝓝 (rightDeriv f x)) :=
  tendsto_leftDeriv_nhdsWithin_Ioi hf x

/-- **Rockafellar, Theorem 24.1**, fourth limit formula: `lim_{z ↑ x} f'₋(z) = f'₋(x)`. -/
theorem theorem_24_1_tendsto_leftDeriv_Iio (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (leftDeriv f) (𝓝[<] x) (𝓝 (leftDeriv f x)) :=
  tendsto_leftDeriv_nhdsWithin_Iio hf x

/-- **§24**, the remark after Theorem 24.1: `∂f(x) = {x* ∈ R | f'₋(x) ≤ x* ≤ f'₊(x)}`. Only
properness is needed. -/
theorem theorem_24_1_subdifferential (hp : Proper f) (x : ℝ) :
    subdifferential (innerₗ ℝ) f x
      = {y : ℝ | leftDeriv f x ≤ (y : EReal) ∧ (y : EReal) ≤ rightDeriv f x} :=
  Set.ext fun _ => mem_subdifferential_iff_le_rightDeriv hp

end OneDim

/-! ### Theorem 24.2 and Corollary 24.2.1: the primitive of a non-decreasing function -/

section Primitive

variable {φ : ℝ → EReal}

/-- **Theorem 24.2**, existence with the identification of the one-sided derivatives: for a
non-decreasing `φ` finite at `a` there is a closed proper convex `f` on `R` with `f'₋ = φ₋` and
`f'₊ = φ₊`, where `φ₋(x) = lim_{z ↑ x} φ(z)` and `φ₊(x) = lim_{z ↓ x} φ(z)`. The book exhibits `f`
as `∫ₐˣ φ(t) dt`; here it is built from the graph `Γ(φ)`, a maximal monotone relation. -/
theorem theorem_24_2_exists (hφ : Monotone φ) {a : ℝ} (hb : φ a ≠ ⊥) (ht : φ a ≠ ⊤) :
    ∃ f : ℝ → EReal, ClosedProperConvexFn f ∧
      (∀ x, leftDeriv f x = ⨆ z ∈ Iio x, φ z) ∧ (∀ x, rightDeriv f x = ⨅ z ∈ Ioi x, φ z) :=
  exists_closedProperConvexFn_leftDeriv_eq_rightDeriv_eq hφ hb ht

/-- **Theorem 24.2**, uniqueness: two closed proper convex functions on `R` squeezed around the
same `φ` differ by a constant. The two squeezes force `∂f = ∂g`, and a subdifferential determines a
closed proper convex function up to an additive constant. -/
theorem theorem_24_2_unique {f g : ℝ → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g) (hf₁ : ∀ x, leftDeriv f x ≤ φ x) (hf₂ : ∀ x, φ x ≤ rightDeriv f x)
    (hg₁ : ∀ x, leftDeriv g x ≤ φ x) (hg₂ : ∀ x, φ x ≤ rightDeriv g x) :
    ∃ α : ℝ, ∀ x, g x = f x + (α : EReal) :=
  exists_eq_add_coe_of_le_le hf hg hf₁ hf₂ hg₁ hg₂

/-- **Theorem 24.2** as the book states it, minus the integral formula: for a non-decreasing `φ`
finite at `a` there is a closed proper convex `f` on `R` with `f'₋ ≤ φ ≤ f'₊`, unique up to an
additive constant. -/
theorem theorem_24_2 (hφ : Monotone φ) {a : ℝ} (hb : φ a ≠ ⊥) (ht : φ a ≠ ⊤) :
    ∃ f : ℝ → EReal, ClosedProperConvexFn f ∧ (∀ x, leftDeriv f x ≤ φ x) ∧
      (∀ x, φ x ≤ rightDeriv f x) ∧
      ∀ g : ℝ → EReal, ClosedProperConvexFn g → (∀ x, leftDeriv g x ≤ φ x) →
        (∀ x, φ x ≤ rightDeriv g x) → ∃ α : ℝ, ∀ x, g x = f x + (α : EReal) :=
  exists_closedProperConvexFn_forall_le_le hφ hb ht

/-- **Corollary 24.2.1**, right-derivative half: on the interior of its effective domain a proper
convex function on `R` is the integral of `f'₊`,

```
f(y) - f(x) = ∫ₓʸ f'₊(t) dt.
```

The integrand is the derivative of a function already convex and finite on an open interval, so
this is the fundamental theorem of calculus and needs no theory of monotone functions. -/
theorem corollary_24_2_1_rightDeriv {f : ℝ → EReal} (hf : ConvexFn f) (hp : Proper f) {x y : ℝ}
    (hx : x ∈ interior (dom f)) (hy : y ∈ interior (dom f)) :
    (f y).toReal - (f x).toReal = ∫ t in x..y, (rightDeriv f t).toReal :=
  sub_eq_intervalIntegral_rightDeriv hf hp hx hy

/-- **Corollary 24.2.1**, left-derivative half: `f(y) - f(x) = ∫ₓʸ f'₋(t) dt`. The two one-sided
derivatives differ only on the jump set of `f'₊`, which is countable and hence null. -/
theorem corollary_24_2_1_leftDeriv {f : ℝ → EReal} (hf : ConvexFn f) (hp : Proper f) {x y : ℝ}
    (hx : x ∈ interior (dom f)) (hy : y ∈ interior (dom f)) :
    (f y).toReal - (f x).toReal = ∫ t in x..y, (leftDeriv f t).toReal :=
  sub_eq_intervalIntegral_leftDeriv hf hp hx hy

end Primitive

/-! ### Theorem 24.3: the complete non-decreasing curves -/

section Curve

variable {Γ : Set (ℝ × ℝ)}

/-- **§24.** A **complete non-decreasing curve** in `R²` is a maximal totally ordered subset for
the coordinatewise partial ordering — a maximal chain. The book introduces the notion by the
formula `Γ = {(x, x*) | φ₋(x) ≤ x* ≤ φ₊(x)}` and then records this description as equivalent. -/
def IsCompleteNonDecreasingCurve (Γ : Set (ℝ × ℝ)) : Prop :=
  IsMaxChain (· ≤ ·) Γ

/-- **The bridge to the backbone**: a maximal chain of `ℝ × ℝ` is exactly a maximal monotone
relation on the line. Monotonicity of a relation on `R` *is* total ordering of its graph, the only
difference being that `IsChain` excuses the diagonal, which `le_refl` supplies. -/
theorem isCompleteNonDecreasingCurve_iff_isMaximalMonotoneRel :
    IsCompleteNonDecreasingCurve Γ ↔ IsMaximalMonotoneRel (innerₗ ℝ) Γ := by
  have hchain : ∀ σ : Set (ℝ × ℝ), IsChain (· ≤ ·) σ ↔ IsMonotoneRel (innerₗ ℝ) σ := by
    intro σ
    rw [isMonotoneRel_iff_forall_le_or_le]
    refine ⟨fun h p hp q hq => ?_, fun h => fun p hp q hq _ => h p hp q hq⟩
    rcases eq_or_ne p q with rfl | hne
    · exact Or.inl le_rfl
    · exact h hp hq hne
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨(hchain Γ).1 h₁, fun σ hσ hsub => ((h₂ ((hchain σ).2 hσ) hsub) ▸ subset_rfl : σ ⊆ Γ)⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨(hchain Γ).2 h₁, fun σ hσ hsub =>
      Subset.antisymm hsub (h₂ σ ((hchain σ).1 hσ) hsub)⟩

/-- **§24**, the book's defining formula implies the order-theoretic description: the region between
the two one-sided limits of a non-decreasing `φ` that is finite somewhere is a complete
non-decreasing curve. Maximality of `Γ(φ)` is what produces the primitive in Theorem 24.2. -/
theorem isCompleteNonDecreasingCurve_monotoneCurve {φ : ℝ → EReal} (hφ : Monotone φ) {a : ℝ}
    (hb : φ a ≠ ⊥) (ht : φ a ≠ ⊤) : IsCompleteNonDecreasingCurve (monotoneCurve φ) :=
  isCompleteNonDecreasingCurve_iff_isMaximalMonotoneRel.2
    (isMaximalMonotoneRel_monotoneCurve hφ hb ht)

/-- **Rockafellar, Theorem 24.3**: the graphs of the subdifferential mappings of the closed proper
convex functions on `R` are precisely the complete non-decreasing curves in `R²`. -/
theorem theorem_24_3 :
    IsCompleteNonDecreasingCurve Γ ↔
      ∃ f : ℝ → EReal, ClosedProperConvexFn f ∧ Γ = subgradientRel (innerₗ ℝ) f := by
  rw [isCompleteNonDecreasingCurve_iff_isMaximalMonotoneRel]
  exact isMaximalMonotoneRel_iff_exists_closedProperConvexFn

/-- **§24**, the converse: every complete non-decreasing curve is the region between the two
one-sided limits of a non-decreasing `φ` that is finite somewhere. Theorem 24.3 turns the maximal
chain into a subdifferential, which is the curve of the right derivative with its value at one
relative interior point of the domain replaced by a subgradient there. -/
theorem exists_monotone_monotoneCurve_eq (h : IsCompleteNonDecreasingCurve Γ) :
    ∃ φ : ℝ → EReal, Monotone φ ∧ (∃ a, φ a ≠ ⊥ ∧ φ a ≠ ⊤) ∧ Γ = monotoneCurve φ := by
  obtain ⟨f, hf, rfl⟩ := theorem_24_3.1 h
  exact exists_monotone_ne_bot_ne_top_monotoneCurve_eq hf

/-- **§24**: the book's two descriptions of a complete non-decreasing curve agree. The book states
the order-theoretic one without proof, immediately after the defining formula. -/
theorem isCompleteNonDecreasingCurve_iff_exists_monotone :
    IsCompleteNonDecreasingCurve Γ ↔
      ∃ φ : ℝ → EReal, Monotone φ ∧ (∃ a, φ a ≠ ⊥ ∧ φ a ≠ ⊤) ∧ Γ = monotoneCurve φ := by
  refine ⟨exists_monotone_monotoneCurve_eq, ?_⟩
  rintro ⟨φ, hφ, ⟨a, hb, ht⟩, hΓ⟩
  rw [hΓ]
  exact isCompleteNonDecreasingCurve_monotoneCurve hφ hb ht

/-- **Theorem 24.3**, second clause: `f` is determined by `Γ` up to an additive constant. The
backbone needs only the *inclusion* `∂f ⊆ ∂g`, which is what Theorem 24.9's maximality argument
consumes. -/
theorem theorem_24_3_unique {f g : ℝ → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g)
    (h : subgradientRel (innerₗ ℝ) f = subgradientRel (innerₗ ℝ) g) :
    ∃ α : ℝ, ∀ x, g x = f x + (α : EReal) := by
  have : IsCompatiblePairing ((innerₗ ℝ).flip) := by rw [flip_innerₗ]; infer_instance
  exact eq_add_coe_of_subgradientRel_subset hf hg h.subset

/-- **Theorem 24.3**, the converse direction in the book's own vocabulary: the graph of `∂f` *is*
the region between the two one-sided limits of `f'₊`. -/
theorem theorem_24_3_subgradientRel_eq_monotoneCurve {f : ℝ → EReal} (hf : ClosedProperConvexFn f) :
    subgradientRel (innerₗ ℝ) f = monotoneCurve (rightDeriv f) :=
  subgradientRel_eq_monotoneCurve_rightDeriv hf

/-- **§24**, the remark after Theorem 24.3: if `Γ` is a complete non-decreasing curve then so is
`Γ* = {(x*, x) | (x, x*) ∈ Γ}`. The book proves it by conjugacy, `Γ* = graph ∂f*`;
order-theoretically it is free, `Prod.swap` being an order isomorphism of `ℝ × ℝ`. -/
theorem theorem_24_3_swap (h : IsCompleteNonDecreasingCurve Γ) :
    IsCompleteNonDecreasingCurve (Prod.swap '' Γ) := by
  have hswap : ∀ p q : ℝ × ℝ, p.swap ≤ q.swap ↔ p ≤ q := fun p q => by
    simp only [Prod.le_def, Prod.fst_swap, Prod.snd_swap]
    exact and_comm
  have hchain : ∀ σ : Set (ℝ × ℝ), IsChain (· ≤ ·) σ → IsChain (· ≤ ·) (Prod.swap '' σ) := by
    rintro σ hσ _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne
    have hpq : p ≠ q := fun h => hne (by rw [h])
    rcases hσ hp hq hpq with hle | hle
    · exact Or.inl ((hswap p q).2 hle)
    · exact Or.inr ((hswap q p).2 hle)
  refine ⟨hchain Γ h.1, fun t ht hsub => ?_⟩
  have hpre : Γ ⊆ Prod.swap '' t := by
    rintro p hp
    exact ⟨p.swap, hsub ⟨p, hp, rfl⟩, by simp⟩
  have hEq : Γ = Prod.swap '' t := h.2 (hchain t ht) hpre
  rw [hEq, ← Set.image_comp]
  simp

end Curve

/-! ### Theorem 24.4: the graph of `∂f` is closed -/

section GraphClosed

variable {n : ℕ} {f : Rn n → EReal}

/-- **Theorem 24.4**: the graph of `∂f` is a closed subset of `Rⁿ × Rⁿ`. **Convexity is not used,
and closedness of `f` enters only through lower semicontinuity**: the book's proof runs through
Theorem 23.5 and the conjugate, whereas the graph is written here as an intersection of preimages
of `epi f`. -/
theorem theorem_24_4 (hf : ClosedProperConvexFn f) : IsClosed (subgradientRel (pairing n) f) :=
  isClosed_subgradientRel continuous_inner hf.proper hf.lowerSemicontinuous

/-- **Rockafellar, Theorem 24.4** in the book's own words: if `xᵢ* ∈ ∂f(xᵢ)` with `xᵢ → x` and
`xᵢ* → x*`, then `x* ∈ ∂f(x)`. -/
theorem theorem_24_4_seq (hf : ClosedProperConvexFn f) {xs ys : ℕ → Rn n} {x y : Rn n}
    (hmem : ∀ i, ys i ∈ subdifferential (pairing n) f (xs i)) (hx : Tendsto xs atTop (𝓝 x))
    (hy : Tendsto ys atTop (𝓝 y)) : y ∈ subdifferential (pairing n) f x := by
  have hp : Tendsto (fun i => ((xs i, ys i) : Rn n × Rn n)) atTop (𝓝 (x, y)) := by
    rw [nhds_prod_eq]
    exact hx.prodMk hy
  exact (theorem_24_4 hf).mem_of_tendsto hp (Filter.Eventually.of_forall hmem)

end GraphClosed

/-! ### Theorem 24.5 and Corollary 24.5.1: convergence of directional derivatives -/

section Convergence

variable {n : ℕ} {C : Set (Rn n)} {f : ℕ → Rn n → EReal} {g : Rn n → EReal}

/-- **Finiteness on a non-empty open set forces properness** (Theorem 7.2), and supplies
`C ⊆ dom f` at the same time. This is what lets Theorem 24.5 be stated with the book's own
hypotheses. -/
private theorem proper_of_finite_on_isOpen {g : Rn n → EReal} (hg : ConvexFn g) (hC : IsOpen C)
    (hfin : ∀ z ∈ C, g z ≠ ⊥ ∧ g z ≠ ⊤) {x : Rn n} (hx : x ∈ C) : Proper g ∧ C ⊆ dom g := by
  have hCdom : C ⊆ dom g := fun z hz => mem_dom.2 (lt_top_iff_ne_top.2 (hfin z hz).2)
  refine ⟨?_, hCdom⟩
  by_contra hp
  have hxi : x ∈ interior (dom g) := hC.subset_interior_iff.2 hCdom hx
  exact (hfin x hx).1 (hg.eq_bot_of_mem_relint_dom hp
    (Convex.interior_subset_relint hg.convex_dom ⟨x, hxi⟩ hxi))

/-- **Theorem 24.5**, first assertion without junk values: every real `μ` above `f'(x; y)`
eventually bounds `fᵢ'(xᵢ; yᵢ)`. This is the book's `limsup` inequality with the extended-real limit
superior replaced by its defining property; `theorem_24_5_limsup` is the literal statement. The
hypotheses are the book's — the `fᵢ` and `g` convex on `Rⁿ` and *finite on* the open convex `C`. -/
theorem theorem_24_5_lt (hC : IsOpen C) (hCc : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hfin : ∀ i, ∀ z ∈ C, f i z ≠ ⊥ ∧ f i z ≠ ⊤) (hg : ConvexFn g)
    (hgfin : ∀ z ∈ C, g z ≠ ⊥ ∧ g z ≠ ⊤)
    (hconv : ∀ z ∈ C, Tendsto (fun i => f i z) atTop (𝓝 (g z))) {x : Rn n}
    (hx : x ∈ C) {xs : ℕ → Rn n} (hxs : Tendsto xs atTop (𝓝 x)) {y : Rn n} {ys : ℕ → Rn n}
    (hys : Tendsto ys atTop (𝓝 y)) {μ : ℝ} (hμ : dirDeriv g x y < (μ : EReal)) :
    ∀ᶠ i in atTop, dirDeriv (f i) (xs i) (ys i) < (μ : EReal) := by
  obtain ⟨hgp, hgC⟩ := proper_of_finite_on_isOpen hg hC hgfin hx
  have h := fun i => proper_of_finite_on_isOpen (hf i) hC (hfin i) hx
  exact eventually_dirDeriv_lt hC hCc hf (fun i => (h i).1) (fun i => (h i).2) hg hgp hgC hconv hx
    hxs hys hμ

/-- **Theorem 24.5**, first assertion literally: `limsup_i fᵢ'(xᵢ; yᵢ) ≤ f'(x; y)`. Equality can
fail: `fᵢ(x) = |x|^{pᵢ}` with `pᵢ ↓ 1` converges pointwise to `|x|` on `R` with every
`fᵢ'(0; 1) = 0` while `f'(0; 1) = 1`. -/
theorem theorem_24_5_limsup (hC : IsOpen C) (hCc : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hfin : ∀ i, ∀ z ∈ C, f i z ≠ ⊥ ∧ f i z ≠ ⊤) (hg : ConvexFn g)
    (hgfin : ∀ z ∈ C, g z ≠ ⊥ ∧ g z ≠ ⊤)
    (hconv : ∀ z ∈ C, Tendsto (fun i => f i z) atTop (𝓝 (g z))) {x : Rn n}
    (hx : x ∈ C) {xs : ℕ → Rn n} (hxs : Tendsto xs atTop (𝓝 x)) {y : Rn n} {ys : ℕ → Rn n}
    (hys : Tendsto ys atTop (𝓝 y)) :
    limsup (fun i => dirDeriv (f i) (xs i) (ys i)) atTop ≤ dirDeriv g x y := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  obtain ⟨μ, hμ₁, hμ₂⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  have hev : ∀ᶠ i in atTop, dirDeriv (f i) (xs i) (ys i) ≤ (μ : EReal) :=
    (theorem_24_5_lt hC hCc hf hfin hg hgfin hconv hx hxs hys hμ₁).mono fun _ h => h.le
  exact le_trans (limsup_le_of_le (h := hev)) hμ₂.le

/-- **Rockafellar, Theorem 24.5**, second assertion: given `ε > 0` there is an index `i₀` with
`∂fᵢ(xᵢ) ⊆ ∂f(x) + εB` for all `i ≥ i₀`, `B` the Euclidean unit ball. -/
theorem theorem_24_5_subdifferential (hC : IsOpen C) (hCc : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hfin : ∀ i, ∀ z ∈ C, f i z ≠ ⊥ ∧ f i z ≠ ⊤) (hg : ConvexFn g)
    (hgfin : ∀ z ∈ C, g z ≠ ⊥ ∧ g z ≠ ⊤)
    (hconv : ∀ z ∈ C, Tendsto (fun i => f i z) atTop (𝓝 (g z))) {x : Rn n}
    (hx : x ∈ C) {xs : ℕ → Rn n} (hxs : Tendsto xs atTop (𝓝 x)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, subdifferential (pairing n) (f i) (xs i)
      ⊆ subdifferential (pairing n) g x + Metric.closedBall (0 : Rn n) ε := by
  obtain ⟨hgp, hgC⟩ := proper_of_finite_on_isOpen hg hC hgfin hx
  have h := fun i => proper_of_finite_on_isOpen (hf i) hC (hfin i) hx
  exact eventually_subdifferential_subset_add_closedBall hC hCc hf (fun i => (h i).1)
    (fun i => (h i).2) hg hgp hgC hconv hx hxs hε

/-- **Corollary 24.5.1**, first assertion: `f'(x; y)` is upper semicontinuous in
`(x, y) ∈ int (dom f) × Rⁿ` — the constant sequence in Theorem 24.5. It cannot be strengthened to
continuity in `x`, though it is continuous in `y` for each fixed interior `x`. -/
theorem corollary_24_5_1_upperSemicontinuous {f : Rn n → EReal} (hf : ConvexFn f) (hfp : Proper f)
    {x : Rn n} (hx : x ∈ interior (dom f)) (y : Rn n) :
    UpperSemicontinuousAt (fun p : Rn n × Rn n => dirDeriv f p.1 p.2) (x, y) :=
  upperSemicontinuousAt_dirDeriv hf hfp hx y

/-- **Rockafellar, Corollary 24.5.1**, second assertion: for `x ∈ int (dom f)` and `ε > 0` there is
a `δ > 0` with `∂f(z) ⊆ ∂f(x) + εB` for every `z` within `δ` of `x`. -/
theorem corollary_24_5_1_subdifferential {f : Rn n → EReal} (hf : ConvexFn f) (hfp : Proper f)
    {x : Rn n} (hx : x ∈ interior (dom f)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ Metric.ball x δ, subdifferential (pairing n) f z
      ⊆ subdifferential (pairing n) f x + Metric.closedBall (0 : Rn n) ε := by
  obtain ⟨δ, hδ, hmem⟩ := Metric.eventually_nhds_iff.1
    (eventually_nhds_subdifferential_subset_add_closedBall hf hfp hx hε)
  exact ⟨δ, hδ, fun z hz => hmem (by simpa [Metric.mem_ball] using hz)⟩

end Convergence

/-! ### Theorem 24.6: approach to a point of `dom f` along a direction -/

section Boundary

variable {n : ℕ} {f : Rn n → EReal} {x y : Rn n}

/-- **§24.** `∂f(x)_y` is the set of points `x* ∈ ∂f(x)` at which `y` is *normal* to `∂f(x)`;
equivalently (`subdifferentialNormal_eq_sep`) the face of `∂f(x)` exposed by `y`. -/
def subdifferentialNormal (f : Rn n → EReal) (x y : Rn n) : Set (Rn n) :=
  {v ∈ subdifferential (pairing n) f x |
    y ∈ normalCone (pairing n) (subdifferential (pairing n) f x) v}

/-- **The bridge**: `y` is normal to a set at `v` exactly when `v` maximises `⟨y, ·⟩` over it. -/
theorem subdifferentialNormal_eq_sep (f : Rn n → EReal) (x y : Rn n) :
    subdifferentialNormal f x y
      = {v ∈ subdifferential (pairing n) f x |
          ∀ w ∈ subdifferential (pairing n) f x, ⟪y, w⟫ ≤ ⟪y, v⟫} := by
  have key : ∀ w : Rn n, pairing n w y = ⟪y, w⟫ := fun w => by
    rw [pairing_apply]; exact real_inner_comm _ _
  ext v
  simp only [subdifferentialNormal, Set.mem_sep_iff, mem_normalCone, map_sub, LinearMap.sub_apply,
    sub_nonpos, key]

/-- **Theorem 24.6**, first assertion without junk values: every real `μ` above the second-order
derivative `f'(x; y; z) = dirDeriv (dirDeriv f x) y z` eventually bounds `f'(xᵢ; z)`. Rockafellar
assumes `f` closed; that is not needed here, because the vanishing step `|xᵢ - x|` is replaced by a
fixed larger one, so only continuity of `f` at interior points is used. -/
theorem theorem_24_6_lt (hf : ConvexFn f) (hfp : Proper f) (hx : x ∈ dom f) {xs : ℕ → Rn n}
    (hxsdom : ∀ i, xs i ∈ dom f) (hxsne : ∀ i, xs i ≠ x) (hxs : Tendsto xs atTop (𝓝 x))
    (hdir : Tendsto (fun i => ‖xs i - x‖⁻¹ • (xs i - x)) atTop (𝓝 y)) (hy : dirDeriv f x y ≠ ⊥)
    {α : ℝ} (hα : 0 < α) (hαy : x + α • y ∈ interior (dom f)) {z : Rn n} {μ : ℝ}
    (hμ : dirDeriv (dirDeriv f x) y z < (μ : EReal)) :
    ∀ᶠ i in atTop, dirDeriv f (xs i) z < (μ : EReal) :=
  eventually_dirDeriv_lt_of_tendsto_dir hf hfp hx hxsdom hxsne hxs hdir hy hα hαy hμ

/-- **Rockafellar, Theorem 24.6**, first assertion, literally:
`limsup_i f'(xᵢ; z) ≤ f'(x; y; z)` for every `z`. -/
theorem theorem_24_6_limsup (hf : ConvexFn f) (hfp : Proper f) (hx : x ∈ dom f) {xs : ℕ → Rn n}
    (hxsdom : ∀ i, xs i ∈ dom f) (hxsne : ∀ i, xs i ≠ x) (hxs : Tendsto xs atTop (𝓝 x))
    (hdir : Tendsto (fun i => ‖xs i - x‖⁻¹ • (xs i - x)) atTop (𝓝 y)) (hy : dirDeriv f x y ≠ ⊥)
    {α : ℝ} (hα : 0 < α) (hαy : x + α • y ∈ interior (dom f)) (z : Rn n) :
    limsup (fun i => dirDeriv f (xs i) z) atTop ≤ dirDeriv (dirDeriv f x) y z := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  obtain ⟨μ, hμ₁, hμ₂⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  have hev : ∀ᶠ i in atTop, dirDeriv f (xs i) z ≤ (μ : EReal) :=
    (theorem_24_6_lt hf hfp hx hxsdom hxsne hxs hdir hy hα hαy hμ₁).mono fun _ h => h.le
  exact le_trans (limsup_le_of_le (h := hev)) hμ₂.le

/-- **Rockafellar, Theorem 24.6**, second assertion: given `ε > 0` there is an index `i₀` with
`∂f(xᵢ) ⊆ ∂f(x)_y + εB` for all `i ≥ i₀`. -/
theorem theorem_24_6_subdifferential (hf : ConvexFn f) (hfp : Proper f) (hx : x ∈ dom f)
    {xs : ℕ → Rn n} (hxsdom : ∀ i, xs i ∈ dom f) (hxsne : ∀ i, xs i ≠ x)
    (hxs : Tendsto xs atTop (𝓝 x))
    (hdir : Tendsto (fun i => ‖xs i - x‖⁻¹ • (xs i - x)) atTop (𝓝 y)) (hy : dirDeriv f x y ≠ ⊥)
    {α : ℝ} (hα : 0 < α) (hαy : x + α • y ∈ interior (dom f)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, subdifferential (pairing n) f (xs i)
      ⊆ subdifferentialNormal f x y + Metric.closedBall (0 : Rn n) ε := by
  rw [subdifferentialNormal_eq_sep]
  exact eventually_subdifferential_subset_exposed_add_closedBall hf hfp hx hxsdom hxsne hxs hdir hy
    hα hαy hε

end Boundary

/-! ### Theorem 24.7: local boundedness of `∂f` and the Lipschitz property -/

section Bounded

variable {n : ℕ} {f : Rn n → EReal} {S : Set (Rn n)}

/-- **Theorem 24.7**, quantitative half: a single `α` bounds the subgradients over a compact
`S ⊆ int (dom f)`, bounds the directional derivatives there, and is a Lipschitz constant for `f` on
`S`. The book takes `α = sup {|x*| : x* ∈ ∂f(S)}`; what is asserted here is the existence of *some*
such `α`, which is implied by, but weaker than, the book's sharper reading. -/
theorem theorem_24_7_bound (hf : ConvexFn f) (hp : Proper f) (hS : IsCompact S)
    (hSD : S ⊆ interior (dom f)) :
    ∃ α : NNReal, LipschitzOnWith α (fun x => (f x).toReal) S ∧
      (∀ x ∈ S, ∀ v ∈ subdifferential (pairing n) f x, ‖v‖ ≤ (α : ℝ)) ∧
      ∀ x ∈ S, ∀ z : Rn n, dirDeriv f x z ≤ (((α : ℝ) * ‖z‖ : ℝ) : EReal) := by
  obtain ⟨α, hlip, hpair, hdir⟩ :=
    exists_lipschitz_forall_pairing_le_of_isCompact (B := pairing n) hf hp hS hSD
  refine ⟨α, hlip, fun x hx v hv => ?_, hdir⟩
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have h := hpair x hx v hv v
  rw [pairing_apply, real_inner_self_eq_norm_mul_norm] at h
  exact le_of_mul_le_mul_right (by linarith) (norm_pos_iff.2 hv0)

/-- **Rockafellar, Theorem 24.7**: `∂f(S) = ⋃ {∂f(x) | x ∈ S}` is non-empty for a non-empty
`S ⊆ int (dom f)`. This is Theorem 23.4 applied at any point of `S`. -/
theorem theorem_24_7_nonempty (hf : ConvexFn f) (hp : Proper f) (hne : S.Nonempty)
    (hSD : S ⊆ interior (dom f)) : ((subgradientRel (pairing n) f).image S).Nonempty :=
  image_subgradientRel_nonempty hf hp hne hSD

/-- **Rockafellar, Theorem 24.7**, topological half: `∂f(S)` is compact for a closed proper convex
`f` and a compact `S ⊆ int (dom f)`. Closedness of `∂f(S)` is Theorem 24.4. -/
theorem theorem_24_7_isCompact (hf : ClosedProperConvexFn f) (hS : IsCompact S)
    (hSD : S ⊆ interior (dom f)) : IsCompact ((subgradientRel (pairing n) f).image S) :=
  isCompact_image_subgradientRel hf hS hSD

/-- **Rockafellar, Theorem 24.7**: `∂f(S)` is closed. -/
theorem theorem_24_7_isClosed (hf : ClosedProperConvexFn f) (hS : IsCompact S)
    (hSD : S ⊆ interior (dom f)) : IsClosed ((subgradientRel (pairing n) f).image S) :=
  (theorem_24_7_isCompact hf hS hSD).isClosed

/-- **Rockafellar, Theorem 24.7**: `∂f(S)` is bounded. -/
theorem theorem_24_7_isBounded (hf : ClosedProperConvexFn f) (hS : IsCompact S)
    (hSD : S ⊆ interior (dom f)) :
    Bornology.IsBounded ((subgradientRel (pairing n) f).image S) :=
  (theorem_24_7_isCompact hf hS hSD).isBounded

end Bounded

/-! ### Theorems 24.8 and 24.9: cyclic monotonicity -/

section Cyclic

variable {n : ℕ} {ρ : SetRel (Rn n) (Rn n)} {f : Rn n → EReal}

/-- A closed proper convex function on `Rⁿ` exists: the zero function. This is what makes Theorem
24.8 true for the empty mapping, which Rockafellar's proof sets aside. -/
private theorem closedProperConvexFn_zero (n : ℕ) :
    ClosedProperConvexFn (affineFn (pairing n) 0 0) :=
  ⟨convexFn_affineFn 0 0, closedFn_affineFn (continuous_pairing (pairing n) 0),
    proper_affineFn 0 0⟩

/-- **Theorem 24.8**, sufficiency: a cyclically monotone multivalued mapping from `Rⁿ` to `Rⁿ` is
contained in the subdifferential of a closed proper convex function. The empty mapping is included,
which Rockafellar's own proof excludes by fiat. -/
theorem theorem_24_8_of_isCyclicallyMonotone (hρ : IsCyclicallyMonotone (pairing n) ρ) :
    ∃ f : Rn n → EReal, ClosedProperConvexFn f ∧ ρ ⊆ subgradientRel (pairing n) f := by
  rcases Set.eq_empty_or_nonempty ρ with rfl | hne
  · exact ⟨affineFn (pairing n) 0 0, closedProperConvexFn_zero n, Set.empty_subset _⟩
  obtain ⟨g, hconv, hclosed, hproper, hsub⟩ :=
    exists_convexFn_subgradientRel_of_isCyclicallyMonotone hρ hne
  exact ⟨g, ⟨hconv, hclosed, hproper⟩, hsub⟩

/-- **Rockafellar, Theorem 24.8**: a multivalued mapping from `Rⁿ` to `Rⁿ` is contained in the
subdifferential of a closed proper convex function if and only if it is cyclically monotone. -/
theorem theorem_24_8 :
    (∃ f : Rn n → EReal, ClosedProperConvexFn f ∧ ρ ⊆ subgradientRel (pairing n) f) ↔
      IsCyclicallyMonotone (pairing n) ρ :=
  ⟨fun ⟨_, hf, hsub⟩ => (isCyclicallyMonotone_subgradientRel hf.proper).mono hsub,
    theorem_24_8_of_isCyclicallyMonotone⟩

/-- **Theorem 24.9**, one half: the subdifferential of a closed proper convex function is a maximal
cyclically monotone mapping — **not** a statement about maximal *monotonicity*. -/
theorem theorem_24_9_subgradientRel (hf : ClosedProperConvexFn f) :
    IsMaximalCyclicallyMonotone (pairing n) (subgradientRel (pairing n) f) :=
  isMaximalCyclicallyMonotone_subgradientRel hf

/-- **Rockafellar, Theorem 24.9**: the subdifferential mappings of the closed proper convex
functions on `Rⁿ` are exactly the maximal cyclically monotone mappings from `Rⁿ` to `Rⁿ`. -/
theorem theorem_24_9 :
    IsMaximalCyclicallyMonotone (pairing n) ρ ↔
      ∃ f : Rn n → EReal, ClosedProperConvexFn f ∧ ρ = subgradientRel (pairing n) f :=
  isMaximalCyclicallyMonotone_iff_exists_closedProperConvexFn

/-- **Theorem 24.9**, second clause: the function is determined by its subdifferential mapping up
to an additive constant. The backbone assumes only the inclusion `∂f ⊆ ∂g`. -/
theorem theorem_24_9_unique {g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g)
    (h : subgradientRel (pairing n) f = subgradientRel (pairing n) g) :
    ∃ α : ℝ, ∀ x, g x = f x + (α : EReal) :=
  eq_add_coe_of_subgradientRel_subset hf hg h.subset

/-- **§24**: `∂f` is a monotone mapping, the case `m = 1` of cyclic monotonicity. Kept deliberately
separate from `theorem_24_9`: maximal monotonicity of `∂f`, Corollary 31.5.2, does **not** follow
from Theorem 24.9 together with "cyclically monotone implies monotone". -/
theorem isMonotoneRel_subgradientRel_rn (hp : Proper f) :
    IsMonotoneRel (pairing n) (subgradientRel (pairing n) f) :=
  isMonotoneRel_subgradientRel hp

/-- **§24**: when `n = 1` the monotone and the cyclically monotone mappings are the same. The book
derives this from Theorems 24.3 and 24.9; the proof here rotates a cycle so that the pair
maximising `x + x*` comes first and deletes it. For `n > 1` it is false: a linear `ρ` with matrix
`Q` is monotone as soon as the symmetric part of `Q` is positive semi-definite, and cyclically
monotone only if `Q` itself is symmetric. -/
theorem isMonotoneRel_iff_isCyclicallyMonotone_line {σ : SetRel ℝ ℝ} :
    IsMonotoneRel (innerₗ ℝ) σ ↔ IsCyclicallyMonotone (innerₗ ℝ) σ :=
  ⟨IsMonotoneRel.isCyclicallyMonotone, IsCyclicallyMonotone.isMonotoneRel⟩

end Cyclic

end Rockafellar
