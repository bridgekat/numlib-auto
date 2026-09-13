import Numlib.Analysis.Convex.Duality.Relint
import Numlib.Analysis.Convex.Helly
import Numlib.Analysis.Convex.Optimization.Minimum

/-!
# Ordinary convex programs and Lagrange multipliers

An *ordinary convex program* minimises `f₀` over `C = dom f₀` subject to finitely many convex
inequalities `fᵢ x ≤ 0` and finitely many affine constraints. The main result is the **existence of
Kuhn–Tucker vectors under Slater's condition**: if the optimal value is not `-∞` and some point of
`ri C` satisfies every non-affine constraint strictly, then non-negative multipliers exist for
which the infimum of the Lagrangian equals the optimal value.

The two families of constraints are kept apart by role. Those indexed by `ι` are the ones Slater's
condition asks a *strict* inequality of — the indices where `fᵢ` is not affine — and are
`EReal`-valued convex functions; those indexed by `κ` are affine maps `E →ᵃ[ℝ] ℝ` asked only for a
weak inequality. That is the split the theorem of the alternative is stated against, so the
existence theorem applies it directly and the affine-only case is `ι = Empty`.

## Main definitions

* `feasibleSet`, `programLagrangian`, `optimalValue`, `IsKuhnTuckerVector` — the vocabulary.

## Main results

* `exists_isKuhnTuckerVector_of_slater` — the existence theorem (Theorem 28.2 in [^1]).
* `exists_isKuhnTuckerVector_of_mem_dom` — when every constraint holds strictly somewhere in `C`,
  the Slater point need not lie in `ri C`.
* `exists_isKuhnTuckerVector_of_affine` — with only affine constraints, a feasible point in `ri C`
  suffices.
* `exists_multipliers_of_slater_eq` — the same for affine *equality* constraints, whose
  multipliers are then of unrestricted sign.
* `subgradient_add_sum_coe_mul`, `mem_argmin_add_sum_coe_mul_of_zero_mem`,
  `isKuhnTuckerVector_of_kuhnTucker` — the Kuhn–Tucker conditions (Theorem 28.3 in [^1]): the
  subgradient of `f₀ + λ₁f₁ + ⋯ + λₘfₘ` decomposes as `∂f₀ + ∑ λᵢ ∂fᵢ`, and the conditions make
  `x̄` optimal and `λ` a Kuhn–Tucker vector.

## Implementation notes

The standing hypothesis `hsub : dom f₀ ⊆ dom (f i)` makes every `fᵢ` finite on `C`; that is what
turns the multiplier inequality into one between real numbers, which may be divided by the
multiplier of the objective.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §28.
-/

namespace ConvexAnalysis

open Set Filter Topology

section Defs

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The set of **feasible solutions** of the constraint system `fᵢ x ≤ 0`, `bⱼ x ≤ 0`. -/
def feasibleSet (f : ι → E → EReal) (b : κ → E →ᵃ[ℝ] ℝ) : Set E :=
  {x | (∀ i, f i x ≤ 0) ∧ ∀ j, b j x ≤ 0}

omit [Fintype ι] [Fintype κ] in
@[simp] theorem mem_feasibleSet {f : ι → E → EReal} {b : κ → E →ᵃ[ℝ] ℝ} {x : E} :
    x ∈ feasibleSet f b ↔ (∀ i, f i x ≤ 0) ∧ ∀ j, b j x ≤ 0 := Iff.rfl

/-- The **Lagrangian** of an ordinary convex program at the multipliers `(l, μ)`, namely
`f₀ + λ₁f₁ + ⋯ + λ_m f_m`. The perturbational Lagrangian of a bifunction is `lagrangian`. -/
noncomputable def programLagrangian (f₀ : E → EReal) (f : ι → E → EReal) (b : κ → E →ᵃ[ℝ] ℝ)
    (l : ι → ℝ) (μ : κ → ℝ) : E → EReal :=
  fun x => f₀ x + (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * b j x : ℝ) : EReal)

theorem programLagrangian_apply (f₀ : E → EReal) (f : ι → E → EReal) (b : κ → E →ᵃ[ℝ] ℝ)
    (l : ι → ℝ) (μ : κ → ℝ) (x : E) :
    programLagrangian f₀ f b l μ x
      = f₀ x + (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * b j x : ℝ) : EReal) := rfl

/-- The **optimal value** of the program: the infimum of the objective over the feasible set. -/
noncomputable def optimalValue (f₀ : E → EReal) (f : ι → E → EReal) (b : κ → E →ᵃ[ℝ] ℝ) : EReal :=
  ⨅ x ∈ feasibleSet f b, f₀ x

omit [Fintype ι] [Fintype κ] in
theorem optimalValue_le {f₀ : E → EReal} {f : ι → E → EReal} {b : κ → E →ᵃ[ℝ] ℝ} {x : E}
    (hx : x ∈ feasibleSet f b) : optimalValue f₀ f b ≤ f₀ x :=
  iInf₂_le x hx

/-- `(l, μ)` is a vector of **Kuhn–Tucker coefficients**: the multipliers are non-negative, and the
infimum of the Lagrangian is finite and equal to the optimal value. This is the direct definition,
not the equivalent perturbational inequality `p u + ⟨λ, u⟩ ≥ p 0`. -/
structure IsKuhnTuckerVector (f₀ : E → EReal) (f : ι → E → EReal) (b : κ → E →ᵃ[ℝ] ℝ)
    (l : ι → ℝ) (μ : κ → ℝ) : Prop where
  /-- The multipliers of the convex constraints are non-negative. -/
  nonneg : ∀ i, 0 ≤ l i
  /-- The multipliers of the affine inequality constraints are non-negative. -/
  nonneg_affine : ∀ j, 0 ≤ μ j
  /-- The infimum of the Lagrangian is not `-∞`. -/
  ne_bot : (⨅ x, programLagrangian f₀ f b l μ x) ≠ ⊥
  /-- The infimum of the Lagrangian is not `+∞`. -/
  ne_top : (⨅ x, programLagrangian f₀ f b l μ x) ≠ ⊤
  /-- The infimum of the Lagrangian is the optimal value in the program. -/
  iInf_eq : (⨅ x, programLagrangian f₀ f b l μ x) = optimalValue f₀ f b

end Defs

section Elementary

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {f₀ : E → EReal} {f : ι → E → EReal} {b : κ → E →ᵃ[ℝ] ℝ} {l : ι → ℝ} {μ : κ → ℝ}

/-- A non-negative real multiple of a non-positive `EReal` is non-positive; the coefficient `0` is
harmless under the convention `0 · ∞ = 0`. -/
theorem coe_mul_nonpos {c : ℝ} (hc : 0 ≤ c) {z : EReal} (hz : z ≤ 0) : (c : EReal) * z ≤ 0 := by
  rcases eq_or_lt_of_le hc with h | h
  · rw [← h]; simp
  · calc (c : EReal) * z ≤ (c : EReal) * 0 := by
          refine mul_le_mul_of_nonneg_left hz ?_
          exact_mod_cast hc
      _ = 0 := by simp

/-- A non-negatively weighted sum of strictly negative values with one non-zero weight is strictly
negative; this rules out a vanishing multiplier on the objective. -/
theorem sum_coe_mul_neg (hl : ∀ i, 0 ≤ l i) {v : ι → EReal} (hv : ∀ i, v i < 0) {i₀ : ι}
    (hi₀ : l i₀ ≠ 0) : (∑ i, (l i : EReal) * v i) < 0 := by
  classical
  have hpos : 0 < l i₀ := lt_of_le_of_ne (hl i₀) (Ne.symm hi₀)
  have hterm : (l i₀ : EReal) * v i₀ < 0 := by
    have hlt : ¬ ((l i₀ : EReal) * 0 ≤ (l i₀ : EReal) * v i₀) := by
      rw [EReal.coe_mul_le_coe_mul_iff hpos]
      exact not_le.2 (hv i₀)
    simpa using not_le.1 hlt
  have hrest : ∑ i ∈ Finset.univ.erase i₀, (l i : EReal) * v i ≤ 0 :=
    Finset.sum_nonpos fun i _ => coe_mul_nonpos (hl i) (hv i).le
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  calc (l i₀ : EReal) * v i₀ + ∑ i ∈ Finset.univ.erase i₀, (l i : EReal) * v i
      ≤ (l i₀ : EReal) * v i₀ + 0 := add_le_add (le_refl _) hrest
    _ = (l i₀ : EReal) * v i₀ := add_zero _
    _ < 0 := hterm

/-- On the feasible set every constraint term is non-positive, so `L ≤ f₀`. -/
theorem programLagrangian_le_of_mem_feasibleSet (hl : ∀ i, 0 ≤ l i) (hμ : ∀ j, 0 ≤ μ j)
    {x : E} (hx : x ∈ feasibleSet f b) : programLagrangian f₀ f b l μ x ≤ f₀ x := by
  have hsum : (∑ i, (l i : EReal) * f i x) ≤ 0 :=
    Finset.sum_nonpos fun i _ => coe_mul_nonpos (hl i) (hx.1 i)
  have haff : ((∑ j, μ j * b j x : ℝ) : EReal) ≤ 0 := by
    have h : (∑ j, μ j * b j x) ≤ 0 :=
      Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hμ j) (hx.2 j)
    exact_mod_cast h
  calc programLagrangian f₀ f b l μ x
      ≤ f₀ x + (∑ i, (l i : EReal) * f i x) + 0 := add_le_add (le_refl _) haff
    _ = f₀ x + (∑ i, (l i : EReal) * f i x) := add_zero _
    _ ≤ f₀ x + 0 := add_le_add (le_refl _) hsum
    _ = f₀ x := add_zero _

/-- Off `dom f₀` the Lagrangian is `+∞`: no constraint term can be `-∞`, since the `fᵢ` never take
`-∞` and the multipliers are non-negative. -/
theorem programLagrangian_eq_top (hl : ∀ i, 0 ≤ l i) (hbot : ∀ i x, f i x ≠ ⊥) {x : E}
    (hx : f₀ x = ⊤) : programLagrangian f₀ f b l μ x = ⊤ := by
  have hsum : (∑ i, (l i : EReal) * f i x) ≠ ⊥ :=
    EReal.sum_ne_bot fun i _ => EReal.coe_mul_ne_bot (hl i) (hbot i x)
  rw [programLagrangian_apply, hx, EReal.top_add_of_ne_bot hsum,
    EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]

/-- The Lagrangian where objective and constraints are all finite, as a single real number. -/
theorem programLagrangian_eq_coe {x : E} {r₀ : ℝ} (h₀ : f₀ x = (r₀ : EReal)) {r : ι → ℝ}
    (hr : ∀ i, f i x = (r i : EReal)) :
    programLagrangian f₀ f b l μ x
      = ((r₀ + (∑ i, l i * r i) + ∑ j, μ j * b j x : ℝ) : EReal) := by
  have hterm : ∀ i, (l i : EReal) * f i x = ((l i * r i : ℝ) : EReal) := fun i => by
    rw [hr i, ← EReal.coe_mul]
  rw [programLagrangian_apply, h₀, Finset.sum_congr rfl (fun i _ => hterm i),
    ← EReal.coe_sum, ← EReal.coe_add, ← EReal.coe_add]

end Elementary

section Slater

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {f₀ : E → EReal} {f : ι → E → EReal} {b : κ → E →ᵃ[ℝ] ℝ}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι] [Fintype κ] in
private theorem add_neg_coe_lt_zero_iff {u : EReal} {a : ℝ} :
    u + ((-a : ℝ) : EReal) < 0 ↔ u < (a : EReal) := by
  induction u with
  | bot => simp
  | top => simp
  | coe r =>
    rw [← EReal.coe_add, ← EReal.coe_zero, EReal.coe_lt_coe_iff,
      EReal.coe_lt_coe_iff]
    constructor <;> intro h <;> linarith

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι] [Fintype κ] in
private theorem add_neg_coe_lt_top_iff {u : EReal} {a : ℝ} :
    u + ((-a : ℝ) : EReal) < ⊤ ↔ u < ⊤ := by
  induction u with
  | bot => simp
  | top => simp
  | coe r =>
    rw [← EReal.coe_add]
    exact iff_of_true (EReal.coe_lt_top _) (EReal.coe_lt_top _)

/-- **Existence of Kuhn–Tucker coefficients under Slater's condition.** If the optimal value is
not `-∞` and the program has a feasible solution in `ri C`, `C = dom f₀`, satisfying *strictly*
every constraint of the first family, then a vector of Kuhn–Tucker coefficients exists. -/
theorem exists_isKuhnTuckerVector_of_slater (hf₀ : ConvexFn f₀) (hp₀ : Proper f₀)
    (hf : ∀ i, ConvexFn (f i)) (hp : ∀ i, Proper (f i)) (hsub : ∀ i, dom f₀ ⊆ dom (f i))
    (hbot : optimalValue f₀ f b ≠ ⊥)
    (hslater : ∃ x ∈ ri (dom f₀), (∀ i, f i x < 0) ∧ ∀ j, b j x ≤ 0) :
    ∃ (l : ι → ℝ) (μ : κ → ℝ), IsKuhnTuckerVector f₀ f b l μ := by
  classical
  obtain ⟨z, hzri, hzf, hzb⟩ := hslater
  have hzC : z ∈ dom f₀ := intrinsicInterior_subset hzri
  have hzfeas : z ∈ feasibleSet f b := ⟨fun i => (hzf i).le, hzb⟩
  -- the optimal value is a real number
  have htop : optimalValue f₀ f b < ⊤ :=
    lt_of_le_of_lt (optimalValue_le hzfeas) (mem_dom.1 hzC)
  obtain ⟨α, hα⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hbot htop
  -- the shifted system, indexed by `Option ι`
  set g : Option ι → E → EReal := fun i' x => i'.elim (f₀ x + ((-α : ℝ) : EReal)) (fun i => f i x)
    with hgdef
  have hgnone : g none = fun x => f₀ x + ((-α : ℝ) : EReal) := rfl
  have hgsome : ∀ i, g (some i) = f i := fun _ => rfl
  have hgconv : ∀ i', ConvexFn (g i') := by
    rintro (_ | i)
    · have : ConvexFn (f₀ + fun _ : E => ((-α : ℝ) : EReal)) :=
        hf₀.add (convexFn_const _) hp₀.ne_bot (fun _ => EReal.coe_ne_bot _)
      exact this
    · exact hf i
  have hgproper : ∀ i', Proper (g i') := by
    rintro (_ | i)
    · refine ⟨⟨z, ?_⟩, fun x => ?_⟩
      · exact mem_dom.2 (add_neg_coe_lt_top_iff.2 (mem_dom.1 hzC))
      · exact EReal.add_ne_bot_iff.2 ⟨hp₀.ne_bot x, EReal.coe_ne_bot _⟩
    · exact hp i
  have hgdom : ∀ i', ri (dom f₀) ⊆ dom (g i') := by
    rintro (_ | i) x hx
    · exact mem_dom.2 (add_neg_coe_lt_top_iff.2 (mem_dom.1 (intrinsicInterior_subset hx)))
    · exact hsub i (intrinsicInterior_subset hx)
  -- the strict system is unsolvable, so the theorem of the alternative produces multipliers
  have hnoalt : ¬ ∃ x ∈ dom f₀, (∀ i', g i' x < 0) ∧ ∀ j, b j x ≤ 0 := by
    rintro ⟨x, _, hxg, hxb⟩
    have hx0 : f₀ x < (α : EReal) := add_neg_coe_lt_zero_iff.1 (hxg none)
    have hxfeas : x ∈ feasibleSet f b := ⟨fun i => (hxg (some i)).le, hxb⟩
    have hle : (α : EReal) ≤ f₀ x := hα ▸ optimalValue_le (f₀ := f₀) hxfeas
    exact absurd (lt_of_le_of_lt hle hx0) (lt_irrefl _)
  obtain ⟨c, μ, hcnonneg, hμnonneg, hcne, hkey⟩ :=
    (alternative_of_convex_system_affine (C := dom f₀) (f := g) (a := b) hf₀.convex_dom hgconv
      hgproper hgdom ⟨z, hzri, hzb⟩).resolve_left hnoalt
  -- the multiplier of the objective is positive
  have hcpos : 0 < c none := by
    rcases eq_or_lt_of_le (hcnonneg none) with h0 | h0
    · exfalso
      obtain ⟨i₀, hi₀⟩ : ∃ i₀ : ι, c (some i₀) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hcne (funext fun i' => by
          cases i' with
          | none => exact h0.symm
          | some i => exact hcon i)
      have hz' := hkey z hzC
      rw [Fintype.sum_option] at hz'
      have hfirst : (c none : EReal) * g none z = 0 := by
        rw [← h0]; simp
      have hsecond : (∑ i, (c (some i) : EReal) * g (some i) z) < 0 := by
        refine sum_coe_mul_neg (l := fun i => c (some i)) (fun i => hcnonneg (some i))
          (v := fun i => g (some i) z) (fun i => ?_) hi₀
        rw [hgsome i]; exact hzf i
      have hthird : ((∑ j, μ j * b j z : ℝ) : EReal) ≤ 0 := by
        have h : (∑ j, μ j * b j z) ≤ 0 :=
          Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hμnonneg j) (hzb j)
        exact_mod_cast h
      rw [hfirst, zero_add] at hz'
      have : (∑ i, (c (some i) : EReal) * g (some i) z) + ((∑ j, μ j * b j z : ℝ) : EReal) < 0 :=
        lt_of_le_of_lt (add_le_add (le_refl _) hthird) (by simpa using hsecond)
      exact absurd hz' (not_le.2 this)
    · exact h0
  -- normalise: divide every multiplier by the one on the objective
  set l : ι → ℝ := fun i => c (some i) / c none with hldef
  set ν : κ → ℝ := fun j => μ j / c none with hνdef
  have hlnonneg : ∀ i, 0 ≤ l i := fun i => div_nonneg (hcnonneg (some i)) hcpos.le
  have hνnonneg : ∀ j, 0 ≤ ν j := fun j => div_nonneg (hμnonneg j) hcpos.le
  have hL : ∀ x, (α : EReal) ≤ programLagrangian f₀ f b l ν x := by
    intro x
    by_cases hxC : x ∈ dom f₀
    · obtain ⟨r₀, hr₀⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp₀.ne_bot x) (mem_dom.1 hxC)
      have hrfin : ∀ i, ∃ r : ℝ, f i x = (r : EReal) := fun i =>
        EReal.exists_coe_of_ne_bot_of_lt_top ((hp i).ne_bot x) (mem_dom.1 (hsub i hxC))
      choose r hr using hrfin
      have hx' := hkey x hxC
      rw [Fintype.sum_option] at hx'
      have hnone : (c none : EReal) * g none x = ((c none * (r₀ + -α) : ℝ) : EReal) := by
        change (c none : EReal) * (f₀ x + ((-α : ℝ) : EReal)) = _
        rw [hr₀, ← EReal.coe_add, ← EReal.coe_mul]
      have hsome : ∀ i, (c (some i) : EReal) * g (some i) x = ((c (some i) * r i : ℝ) : EReal) := by
        intro i; rw [hgsome i, hr i, ← EReal.coe_mul]
      rw [hnone, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hsome i),
        ← EReal.coe_sum, ← EReal.coe_add, ← EReal.coe_add,
        ← EReal.coe_zero, EReal.coe_le_coe_iff] at hx'
      rw [programLagrangian_eq_coe hr₀ hr, EReal.coe_le_coe_iff]
      refine le_of_mul_le_mul_left ?_ hcpos
      have hsumfield : c none * (∑ i, l i * r i) = ∑ i, c (some i) * r i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hldef]
        field_simp
      have haffield : c none * (∑ j, ν j * b j x) = ∑ j, μ j * b j x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hνdef]
        field_simp
      have hexp : c none * (r₀ + (∑ i, l i * r i) + ∑ j, ν j * b j x)
          = c none * r₀ + c none * (∑ i, l i * r i) + c none * (∑ j, ν j * b j x) := by ring
      have hshift : c none * (r₀ + -α) = c none * r₀ - c none * α := by ring
      rw [hexp, hsumfield, haffield]
      rw [hshift] at hx'
      linarith
    · have htopx : f₀ x = ⊤ := by
        rcases lt_or_eq_of_le (le_top : f₀ x ≤ ⊤) with h | h
        · exact absurd (mem_dom.2 h) hxC
        · exact h
      rw [programLagrangian_eq_top hlnonneg (fun i y => (hp i).ne_bot y) htopx]
      exact le_top
  have hiInf : (⨅ x, programLagrangian f₀ f b l ν x) = (α : EReal) := by
    refine le_antisymm ?_ (le_iInf hL)
    rw [← hα]
    exact le_iInf₂ fun x hx =>
      (iInf_le _ x).trans (programLagrangian_le_of_mem_feasibleSet hlnonneg hνnonneg hx)
  exact ⟨l, ν, hlnonneg, hνnonneg, by rw [hiInf]; exact EReal.coe_ne_bot _,
    by rw [hiInf]; exact EReal.coe_ne_top _, by rw [hiInf, hα]⟩

/-- With only affine constraints a feasible solution in `ri C` suffices: the existence theorem
with an empty family of strict constraints. -/
theorem exists_isKuhnTuckerVector_of_affine [IsEmpty ι] (hf₀ : ConvexFn f₀) (hp₀ : Proper f₀)
    (hbot : optimalValue f₀ f b ≠ ⊥) (hfeas : ∃ x ∈ ri (dom f₀), ∀ j, b j x ≤ 0) :
    ∃ (l : ι → ℝ) (μ : κ → ℝ), IsKuhnTuckerVector f₀ f b l μ := by
  obtain ⟨x, hx, hxb⟩ := hfeas
  exact exists_isKuhnTuckerVector_of_slater hf₀ hp₀ (fun i => isEmptyElim i)
    (fun i => isEmptyElim i) (fun i => isEmptyElim i) hbot ⟨x, hx, fun i => isEmptyElim i, hxb⟩

omit [FiniteDimensional ℝ E] [Fintype ι] [Fintype κ] in
/-- An affine map along the segment from `y` to `z`, as used in the prolongation of a Slater
point. -/
theorem affineMap_segment (g : E →ᵃ[ℝ] ℝ) (y z : E) (a : ℝ) :
    g ((1 - a) • y + a • z) = (1 - a) * g y + a * g z := by
  have hseg : (1 - a) • y + a • z = AffineMap.lineMap y z a := by
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
    abel
  rw [hseg, AffineMap.apply_lineMap, AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, smul_eq_mul]
  ring

/-- When every constraint holds *strictly* at some point of `C`, that point need not lie in
`ri C`: prolonging it towards a relative interior point produces a Slater point.

The book states this for a program with no affine constraints; affine constraints are allowed here,
at the price of asking strict inequality of them too, which is what survives the prolongation. The
hypothesis `hri` is what following `fᵢ` along the segment needs. -/
theorem exists_isKuhnTuckerVector_of_mem_dom (hf₀ : ConvexFn f₀) (hp₀ : Proper f₀)
    (hf : ∀ i, ConvexFn (f i)) (hp : ∀ i, Proper (f i)) (hsub : ∀ i, dom f₀ ⊆ dom (f i))
    (hri : ∀ i, ri (dom f₀) ⊆ ri (dom (f i))) (hbot : optimalValue f₀ f b ≠ ⊥)
    (hslater : ∃ x ∈ dom f₀, (∀ i, f i x < 0) ∧ ∀ j, b j x < 0) :
    ∃ (l : ι → ℝ) (μ : κ → ℝ), IsKuhnTuckerVector f₀ f b l μ := by
  classical
  obtain ⟨z, hz, hzf, hzb⟩ := hslater
  obtain ⟨y, hy⟩ := Convex.relint_nonempty hf₀.convex_dom ⟨z, hz⟩
  -- along the segment from `y` to `z`, every constraint stays strict near the far end
  have hmem : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), (1 - a) • y + a • z ∈ ri (dom f₀) := by
    filter_upwards [(eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with a ha ha'
    exact Convex.segment_mem_relint hf₀.convex_dom hy (subset_closure hz) ha.le ha'
  have hcon : ∀ i, ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), f i ((1 - a) • y + a • z) < 0 := by
    intro i
    have hlim := (hf i).tendsto_lscHull_along_segment_relint (hri i hy) z
    exact hlim.eventually_lt_const (lt_of_le_of_lt (lscHull_le (f i) z) (hzf i))
  have haff : ∀ j, ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), b j ((1 - a) • y + a • z) < 0 := by
    intro j
    have hlim : Filter.Tendsto (fun a : ℝ => b j ((1 - a) • y + a • z)) (𝓝[<] (1 : ℝ))
        (𝓝 (b j z)) := by
      have : Filter.Tendsto (fun a : ℝ => (1 - a) * b j y + a * b j z) (𝓝 (1 : ℝ))
          (𝓝 ((1 - 1) * b j y + 1 * b j z)) :=
        (((tendsto_const_nhds.sub tendsto_id).mul tendsto_const_nhds).add
          (tendsto_id.mul tendsto_const_nhds))
      simp only [sub_self, zero_mul, one_mul, zero_add] at this
      exact (this.mono_left nhdsWithin_le_nhds).congr fun a => (affineMap_segment (b j) y z a).symm
    exact hlim.eventually_lt_const (hzb j)
  obtain ⟨a, hamem, hafeas⟩ :=
    ((hmem.and ((Filter.eventually_all).2 hcon)).and ((Filter.eventually_all).2 haff)).exists
  exact exists_isKuhnTuckerVector_of_slater hf₀ hp₀ hf hp hsub hbot
    ⟨_, hamem.1, hamem.2, fun j => (hafeas j).le⟩

/-- The same for a program whose affine constraints are *equations*. Their multipliers are then of
unrestricted sign, obtained as `μ' - μ''` from the two inequalities each equation splits into. -/
theorem exists_multipliers_of_slater_eq {σ : Type*} [Fintype σ] {a : σ → E →ᵃ[ℝ] ℝ}
    (hf₀ : ConvexFn f₀) (hp₀ : Proper f₀) (hf : ∀ i, ConvexFn (f i)) (hp : ∀ i, Proper (f i))
    (hsub : ∀ i, dom f₀ ⊆ dom (f i))
    (hbot : optimalValue f₀ f (Sum.elim a fun k => -(a k)) ≠ ⊥)
    (hslater : ∃ x ∈ ri (dom f₀), (∀ i, f i x < 0) ∧ ∀ k, a k x = 0) :
    ∃ (l : ι → ℝ) (ρ : σ → ℝ), (∀ i, 0 ≤ l i) ∧
      (⨅ x, f₀ x + (∑ i, (l i : EReal) * f i x) + ((∑ k, ρ k * a k x : ℝ) : EReal))
        = ⨅ x ∈ {x | (∀ i, f i x ≤ 0) ∧ ∀ k, a k x = 0}, f₀ x := by
  classical
  set b' : σ ⊕ σ → E →ᵃ[ℝ] ℝ := Sum.elim a fun k => -(a k) with hb'
  have hinl : ∀ (k : σ) (x : E), b' (Sum.inl k) x = a k x := fun _ _ => rfl
  have hinr : ∀ (k : σ) (x : E), b' (Sum.inr k) x = -(a k x) := fun _ _ => rfl
  have hsplit : ∀ (x : E), (∀ j, b' j x ≤ 0) ↔ ∀ k, a k x = 0 := by
    intro x
    constructor
    · intro h k
      have h₁ := h (Sum.inl k)
      have h₂ := h (Sum.inr k)
      rw [hinl k x] at h₁
      rw [hinr k x] at h₂
      linarith
    · rintro h (k | k)
      · rw [hinl k x, h k]
      · rw [hinr k x, h k, neg_zero]
  have hfeasEq : feasibleSet f b' = {x | (∀ i, f i x ≤ 0) ∧ ∀ k, a k x = 0} := by
    ext x
    exact and_congr_right fun _ => hsplit x
  obtain ⟨x₀, hx₀, hx₀f, hx₀a⟩ := hslater
  obtain ⟨l, μ, hkt⟩ := exists_isKuhnTuckerVector_of_slater (b := b') hf₀ hp₀ hf hp hsub hbot
    ⟨x₀, hx₀, hx₀f, (hsplit x₀).2 hx₀a⟩
  refine ⟨l, fun k => μ (Sum.inl k) - μ (Sum.inr k), hkt.nonneg, ?_⟩
  have hlag : ∀ x, f₀ x + (∑ i, (l i : EReal) * f i x)
      + ((∑ k, (μ (Sum.inl k) - μ (Sum.inr k)) * a k x : ℝ) : EReal)
      = programLagrangian f₀ f b' l μ x := by
    intro x
    rw [programLagrangian_apply]
    congr 2
    rw [Fintype.sum_sum_type]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hb', Sum.elim_inl, Sum.elim_inr, AffineMap.coe_neg, Pi.neg_apply]
    ring
  rw [iInf_congr hlag, hkt.iInf_eq, optimalValue, hfeasEq]

end Slater

/-! ### The Kuhn–Tucker conditions

Rockafellar's Theorem 28.3 (*Convex Analysis*, §28) characterises the pairs (Kuhn–Tucker vector,
optimal solution) of an ordinary convex program by three conditions on the point `x̄` and the
multipliers `λᵢ`: (a) `λᵢ ≥ 0`, `fᵢ(x̄) ≤ 0` and `λᵢ fᵢ(x̄) = 0` for the inequality constraints;
(b) `fᵢ(x̄) = 0` for the (affine) equality constraints;
(c) `0 ∈ ∂f₀(x̄) + λ₁∂f₁(x̄) + ⋯ + λₘ∂fₘ(x̄)`, the terms with `λᵢ = 0` omitted. Its general content
is two statements about Rockafellar's `h = f₀ + λ₁f₁ + ⋯ + λₘfₘ`, the objective plus the weighted
constraints at fixed multipliers:

* `subgradient_add_sum_coe_mul` — the subgradient of `h` decomposes as in (c), by the sum rule
  for subgradients (Theorem 23.8 in [^1]) under the constraint qualification that the effective
  domains share a relative interior point;
* `mem_argmin_add_sum_coe_mul_of_zero_mem` and `add_sum_coe_mul_eq_of_forall_mul_eq_zero` —
  condition (c) makes `x̄` a minimiser of `h`, and complementary slackness makes `h(x̄) = f₀(x̄)`;
  together these are the sufficiency half of Theorem 28.3, for any program whose Lagrange
  function has this shape.

Both are stated for one finite family of summands `λᵢ fᵢ`, each **admissible** in the sense of
`IsLagrangeSummand`: either `fᵢ` is convex and proper and `λᵢ ≥ 0`, or `fᵢ` is affine and `λᵢ` has
any sign — the two kinds of constraint of an ordinary convex program — and for any dual pair.
`isKuhnTuckerVector_of_kuhnTucker` is the same sufficiency read in the vocabulary of this file,
where the affine constraints form the separate family `b`. -/

section LagrangeSummand

open scoped Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {x₀ : E}

/-- The summand `λ g` of a Lagrange function is **admissible** at the reference point `x₀` when it
is a proper convex function with `x₀` in the relative interior of its effective domain: either
`g` is convex and proper, `λ ≥ 0` and `x₀ ∈ ri (dom g)`, or `g` is affine — its linear part
represented through the pairing by some `v` with `⟨w, v⟩ = a.linear w` — and `λ` is arbitrary.
These are the inequality and the equality constraints of an ordinary convex program. -/
def IsLagrangeSummand (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (x₀ : E) (l : ℝ) (g : E → EReal) : Prop :=
  (0 ≤ l ∧ ConvexFn g ∧ Proper g ∧ x₀ ∈ ri (dom g)) ∨
    ∃ (a : E →ᵃ[ℝ] ℝ) (v : F), (∀ y, g y = a y) ∧ ∀ w, B w v = a.linear w

/-- A real multiple of an affine function is a convex, proper, everywhere finite function. -/
theorem convexFn_proper_coe_mul_affineMap (c : ℝ) (a : E →ᵃ[ℝ] ℝ) :
    ConvexFn (fun y => (c : EReal) * ((a y : ℝ) : EReal)) ∧
      Proper (fun y => (c : EReal) * ((a y : ℝ) : EReal)) ∧
      dom (fun y => (c : EReal) * ((a y : ℝ) : EReal)) = univ := by
  have hrw : (fun y => (c : EReal) * ((a y : ℝ) : EReal))
      = fun y => (((c • a) y : ℝ) : EReal) := by
    funext y
    rw [← EReal.coe_mul, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [hrw]
  refine ⟨?_, proper_coe _, dom_coe _⟩
  refine ConvexOn.convexFn_coe ⟨convex_univ, fun x _ y _ p q hp hq hpq => ?_⟩
  rw [Convex.combo_affine_apply hpq]

/-- An admissible summand is a proper convex function whose effective domain has `x₀` in its
relative interior — the hypotheses of the sum rule for subgradients. -/
theorem IsLagrangeSummand.convexFn_proper_mem_relint {c : ℝ} {g : E → EReal}
    (h : IsLagrangeSummand B x₀ c g) :
    ConvexFn (fun y => (c : EReal) * g y) ∧ Proper (fun y => (c : EReal) * g y) ∧
      x₀ ∈ ri (dom fun y => (c : EReal) * g y) := by
  rcases h with ⟨hc, hg, hp, hx₀⟩ | ⟨a, v, hga, -⟩
  · refine ⟨convexFn_coe_mul hc hg, proper_coe_mul hc hp, ?_⟩
    rcases hc.eq_or_lt with rfl | hpos
    · have hdom : dom (fun y => ((0 : ℝ) : EReal) * g y) = univ :=
        eq_univ_of_forall fun y => by simp
      rw [hdom, intrinsicInterior_univ]
      exact mem_univ _
    · rwa [dom_coe_mul hpos]
  · have hg : g = fun y => ((a y : ℝ) : EReal) := funext hga
    subst hg
    obtain ⟨h₁, h₂, h₃⟩ := convexFn_proper_coe_mul_affineMap c a
    refine ⟨h₁, h₂, ?_⟩
    rw [h₃, intrinsicInterior_univ]
    exact mem_univ _

/-- The subgradient of an admissible summand with a non-zero multiplier is the multiple of the
subgradient: `∂(λg) = λ ∂g` for `λ > 0`, and for every `λ` when `g` is affine. -/
theorem IsLagrangeSummand.subgradient_coe_mul (hsep : Function.Injective B.flip) {c : ℝ}
    {g : E → EReal} (h : IsLagrangeSummand B x₀ c g) (hc : c ≠ 0) (x : E) :
    subgradient B (fun y => (c : EReal) * g y) x = c • subgradient B g x := by
  rcases h with ⟨hc0, -, -, -⟩ | ⟨a, v, hga, hv⟩
  · exact ConvexAnalysis.subgradient_coe_mul (lt_of_le_of_ne hc0 (Ne.symm hc)) g x
  · have hg : g = fun y => ((a y : ℝ) : EReal) := funext hga
    subst hg
    exact subgradient_coe_mul_affineMap hsep c a hv x

end LagrangeSummand

section KuhnTucker

open scoped Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {ι : Type*} {s : Finset ι} {f₀ : E → EReal} {f : ι → E → EReal}
  {l : ι → ℝ} {x₀ : E}

/-- **The subgradient of `h = f₀ + λ₁f₁ + ⋯ + λₘfₘ`**, Theorem 23.8 applied to the summands of the
Lagrange function: when the effective domains share a relative interior point `x₀`,
`∂h(x) = ∂f₀(x) + ∑ λᵢ ∂fᵢ(x)`, the sum over the indices with `λᵢ ≠ 0`. The omission is not
cosmetic — `∂fᵢ(x)` can be empty at a boundary point of `dom fᵢ`, and then `0 · ∂fᵢ(x)` would be
empty rather than `{0}`. -/
theorem subgradient_add_sum_coe_mul [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hsep : Function.Injective B.flip) (hf₀ : ConvexFn f₀) (hp₀ : Proper f₀)
    (hx₀ : x₀ ∈ ri (dom f₀)) (hf : ∀ i ∈ s, IsLagrangeSummand B x₀ (l i) (f i)) (x : E) :
    subgradient B (fun y => f₀ y + ∑ i ∈ s, (l i : EReal) * f i y) x
      = subgradient B f₀ x + ∑ i ∈ s with l i ≠ 0, l i • subgradient B (f i) x := by
  classical
  set g : Option ι → E → EReal := fun o => o.elim f₀ fun i y => (l i : EReal) * f i y with hg
  have hsum : (fun y => f₀ y + ∑ i ∈ s, (l i : EReal) * f i y) = ∑ o ∈ s.insertNone, g o := by
    funext y
    rw [Finset.sum_apply, Finset.sum_insertNone]
    rfl
  have hprop : ∀ o ∈ s.insertNone, ConvexFn (g o) ∧ Proper (g o) ∧ x₀ ∈ ri (dom (g o)) := by
    intro o ho
    cases o with
    | none => exact ⟨hf₀, hp₀, hx₀⟩
    | some i => exact (hf i (Finset.some_mem_insertNone.1 ho)).convexFn_proper_mem_relint
  have hex : IsExactFinsetSum B s.insertNone g :=
    IsExactFinsetSum.of_relint ⟨none, Finset.mem_insertNone.2 (by simp)⟩
      (fun o ho => (hprop o ho).1) (fun o ho => (hprop o ho).2.1) fun o ho => (hprop o ho).2.2
  rw [hsum, hex.subgradient_finsetSum x, Finset.sum_insertNone, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  split_ifs with hli
  · exact (hf i hi).subgradient_coe_mul hsep hli x
  · push Not at hli
    change subgradient B (fun y => (l i : EReal) * f i y) x = 0
    rw [hli, subgradient_zero_mul hsep, Set.singleton_zero]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- **Complementary slackness**: when every product `λᵢ fᵢ(x)` vanishes, `h(x) = f₀(x)`. -/
theorem add_sum_coe_mul_eq_of_forall_mul_eq_zero {x : E}
    (h : ∀ i ∈ s, (l i : EReal) * f i x = 0) :
    f₀ x + ∑ i ∈ s, (l i : EReal) * f i x = f₀ x := by
  rw [Finset.sum_eq_zero h, add_zero]

/-- **Condition (c) of the Kuhn–Tucker conditions makes `x` a minimiser of `h`**: if
`0 ∈ ∂f₀(x) + ∑ λᵢ ∂fᵢ(x)`, the sum over the `λᵢ ≠ 0`, then `x ∈ argmin h`. -/
theorem mem_argmin_add_sum_coe_mul_of_zero_mem [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (hsep : Function.Injective B.flip) (hf₀ : ConvexFn f₀)
    (hp₀ : Proper f₀) (hx₀ : x₀ ∈ ri (dom f₀)) (hf : ∀ i ∈ s, IsLagrangeSummand B x₀ (l i) (f i))
    {x : E}
    (h : (0 : F) ∈ subgradient B f₀ x + ∑ i ∈ s with l i ≠ 0, l i • subgradient B (f i) x) :
    x ∈ argmin fun y => f₀ y + ∑ i ∈ s, (l i : EReal) * f i y := by
  rw [mem_argmin_iff_zero_mem_subgradient B, subgradient_add_sum_coe_mul hsep hf₀ hp₀ hx₀ hf]
  exact h

end KuhnTucker

section KuhnTuckerProgram

open scoped Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {ι κ : Type*} [Fintype ι] [Fintype κ]
  {f₀ : E → EReal} {f : ι → E → EReal} {b : κ → E →ᵃ[ℝ] ℝ} {l : ι → ℝ} {μ : κ → ℝ}

/-- The affine part `x ↦ ∑ⱼ μⱼ bⱼ(x)` of the Lagrangian, as one affine map. -/
def affineSum (b : κ → E →ᵃ[ℝ] ℝ) (μ : κ → ℝ) : E →ᵃ[ℝ] ℝ where
  toFun y := ∑ j, μ j * b j y
  linear := ∑ j, μ j • (b j).linear
  map_vadd' p v := by
    simp only [vadd_eq_add, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      ← Finset.sum_add_distrib, ← mul_add]
    exact Finset.sum_congr rfl fun j _ => by rw [← vadd_eq_add, AffineMap.map_vadd, vadd_eq_add]

omit [FiniteDimensional ℝ E] in
@[simp] theorem affineSum_apply (b : κ → E →ᵃ[ℝ] ℝ) (μ : κ → ℝ) (y : E) :
    affineSum b μ y = ∑ j, μ j * b j y := rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem affineSum_linear (b : κ → E →ᵃ[ℝ] ℝ) (μ : κ → ℝ) :
    (affineSum b μ).linear = ∑ j, μ j • (b j).linear := rfl

omit [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- The Lagrangian of this file is `h` for the family `f` together with the single affine summand
`affineSum b μ`, indexed by `Option ι` with the affine part in the `none` slot and multiplier
`1`. -/
theorem programLagrangian_eq_add_sum_option (f₀ : E → EReal) (f : ι → E → EReal)
    (b : κ → E →ᵃ[ℝ] ℝ) (l : ι → ℝ) (μ : κ → ℝ) :
    programLagrangian f₀ f b l μ = fun x => f₀ x + ∑ o : Option ι,
      ((o.elim (1 : ℝ) l : ℝ) : EReal) *
        o.elim (fun y => ((affineSum b μ y : ℝ) : EReal)) f x := by
  funext x
  rw [programLagrangian_apply, Fintype.sum_option]
  simp only [Option.elim, EReal.coe_one, one_mul]
  rw [affineSum_apply, add_assoc, add_comm (∑ i, (l i : EReal) * f i x)]

/-- **Sufficiency of the Kuhn–Tucker conditions** for the programs of this file: if `x` is
feasible, the multipliers are non-negative with `λᵢ fᵢ(x) = 0` and `μⱼ bⱼ(x) = 0`, and
`0 ∈ ∂f₀(x) + ∑ λᵢ ∂fᵢ(x) + {∑ μⱼ aⱼ}` — the sum over the `λᵢ ≠ 0`, the vector `aⱼ` representing
the linear part of `bⱼ` through the pairing — then `(l, μ)` is a Kuhn–Tucker vector and `x` is an
optimal solution: `f₀ x` is the optimal value. This is the "if" half of Rockafellar's
Theorem 28.3, which needs no constraint qualification beyond a relative interior point `x₀` of
`dom f₀` lying in `ri (dom fᵢ)` for every `i`. -/
theorem isKuhnTuckerVector_of_kuhnTucker [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hsep : Function.Injective B.flip) (hf₀ : ConvexFn f₀) (hp₀ : Proper f₀)
    (hf : ∀ i, ConvexFn (f i)) (hpf : ∀ i, Proper (f i)) {x₀ : E} (hx₀ : x₀ ∈ ri (dom f₀))
    (hri : ∀ i, x₀ ∈ ri (dom (f i))) {a : κ → F} (ha : ∀ j w, B w (a j) = (b j).linear w) {x : E}
    (hl : ∀ i, 0 ≤ l i ∧ f i x ≤ 0 ∧ (l i : EReal) * f i x = 0)
    (hμ : ∀ j, 0 ≤ μ j ∧ b j x ≤ 0 ∧ μ j * b j x = 0)
    (hc : (0 : F) ∈ subgradient B f₀ x + ∑ i with l i ≠ 0, l i • subgradient B (f i) x
      + {∑ j, μ j • a j}) :
    IsKuhnTuckerVector f₀ f b l μ ∧ x ∈ feasibleSet f b ∧ f₀ x = optimalValue f₀ f b := by
  classical
  -- the Lagrangian as `h` over `Option ι`
  set l' : Option ι → ℝ := fun o => o.elim 1 l with hl'
  set g : Option ι → E → EReal := fun o => o.elim (fun y => ((affineSum b μ y : ℝ) : EReal)) f
    with hg
  have hlag : programLagrangian f₀ f b l μ = fun y => f₀ y + ∑ o, (l' o : EReal) * g o y :=
    programLagrangian_eq_add_sum_option f₀ f b l μ
  have hlin : ∀ w, B w (∑ j, μ j • a j) = (affineSum b μ).linear w := fun w => by
    simp only [map_sum, map_smul, smul_eq_mul, affineSum_linear, LinearMap.sum_apply,
      LinearMap.smul_apply, ha]
  have hadm : ∀ o ∈ (Finset.univ : Finset (Option ι)), IsLagrangeSummand B x₀ (l' o) (g o) := by
    intro o _
    cases o with
    | none => exact Or.inr ⟨affineSum b μ, ∑ j, μ j • a j, fun y => rfl, hlin⟩
    | some i => exact Or.inl ⟨(hl i).1, hf i, hpf i, hri i⟩
  -- condition (c) in the `Option ι` shape
  have hfilter : (Finset.univ.filter fun o : Option ι => l' o ≠ 0)
      = insert none ((Finset.univ.filter fun i => l i ≠ 0).map Function.Embedding.some) := by
    ext o
    cases o <;> simp [hl']
  have hc' : (0 : F) ∈ subgradient B f₀ x + ∑ o with l' o ≠ 0, l' o • subgradient B (g o) x := by
    rw [hfilter, Finset.sum_insert (by simp), Finset.sum_map]
    have hnone : subgradient B (fun y => ((affineSum b μ y : ℝ) : EReal)) x = {∑ j, μ j • a j} :=
      subgradient_coe_affineMap hsep (affineSum b μ) hlin x
    simp only [hl', hg, Option.elim, Function.Embedding.some_apply, one_smul]
    rw [hnone, add_comm ({∑ j, μ j • a j} : Set F), ← add_assoc]
    exact hc
  have hmin : x ∈ argmin (programLagrangian f₀ f b l μ) := by
    rw [hlag]
    exact mem_argmin_add_sum_coe_mul_of_zero_mem hsep hf₀ hp₀ hx₀ hadm hc'
  -- complementary slackness: `L x = f₀ x`
  have hslack : ∀ o ∈ (Finset.univ : Finset (Option ι)), (l' o : EReal) * g o x = 0 := by
    intro o _
    cases o with
    | none =>
      have : affineSum b μ x = 0 := by
        rw [affineSum_apply]
        exact Finset.sum_eq_zero fun j _ => (hμ j).2.2
      simp only [hl', hg, Option.elim, this, EReal.coe_zero, mul_zero]
    | some i => exact (hl i).2.2
  have hLx : programLagrangian f₀ f b l μ x = f₀ x := by
    rw [hlag]
    exact add_sum_coe_mul_eq_of_forall_mul_eq_zero hslack
  -- `x` is feasible and in `dom f₀`
  have hfeas : x ∈ feasibleSet f b := ⟨fun i => (hl i).2.1, fun j => (hμ j).2.1⟩
  have hxdom : x ∈ dom f₀ := by
    obtain ⟨w, hw, -, -, -⟩ := Set.mem_add.1 hc
    obtain ⟨v₀, hv₀, -, -, -⟩ := Set.mem_add.1 hw
    exact mem_dom_of_mem_subgradient hp₀ hv₀
  have hinf : (⨅ y, programLagrangian f₀ f b l μ y) = f₀ x := by
    rw [iInf_eq_of_mem_argmin hmin, hLx]
  have hopt : f₀ x = optimalValue f₀ f b := by
    refine le_antisymm ?_ (optimalValue_le hfeas)
    refine le_iInf₂ fun y hy => ?_
    calc f₀ x = programLagrangian f₀ f b l μ x := hLx.symm
      _ ≤ programLagrangian f₀ f b l μ y := hmin y
      _ ≤ f₀ y :=
        programLagrangian_le_of_mem_feasibleSet (fun i => (hl i).1) (fun j => (hμ j).1) hy
  refine ⟨⟨fun i => (hl i).1, fun j => (hμ j).1, ?_, ?_, ?_⟩, hfeas, hopt⟩
  · rw [hinf]; exact hp₀.ne_bot x
  · rw [hinf]; exact (mem_dom.1 hxdom).ne
  · rw [hinf, hopt]

end KuhnTuckerProgram

end ConvexAnalysis

