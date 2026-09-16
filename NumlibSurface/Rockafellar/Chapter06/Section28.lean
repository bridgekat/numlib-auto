import Numlib.Analysis.Convex.Optimization.Lagrangian
import Numlib.Analysis.Convex.Optimization.Program
import Numlib.Analysis.Convex.Saddle.Minimax
import NumlibSurface.Rockafellar.Common.Euclidean
import NumlibSurface.Rockafellar.Chapter05.Section23

/-!
# Rockafellar, §28: Ordinary Convex Programs and Lagrange Multipliers

The ordinary convex program `(P)`, its Kuhn–Tucker coefficients, its Lagrangian `L`, and the
equivalence between solving `(P)` and finding a saddle-point of `L`.

All nine numbered results of §28 are formalized: Theorems 28.1, 28.2, 28.3 and 28.4 and
Corollaries 28.1.1, 28.2.1, 28.2.2, 28.3.1 and 28.4.1, together with the three Kuhn–Tucker
conditions (a), (b), (c) of Theorem 28.3, the decomposition principle, and the section's two
counterexamples `ex1` and `ex2`.

## Implementation notes

**A program is the tuple, not the objective function.** `OrdinaryConvexProgram n m` carries
Rockafellar's `(m + 3)`-tuple `(C, f₀, f₁, …, f_m, r)` and his two blanket assumptions on it,
because two programs with the same objective `f₀ + δ(· | C₀)` can have different Kuhn–Tucker
coefficients. `eq_of_programLagrangian_eq` recovers the whole tuple from the Lagrangian alone.

**`r` counts the inequality constraints**, not the equalities: `f₁ ≤ 0, …, f_r ≤ 0` and
`f_{r+1} = 0, …, f_m = 0`.

`lagrangeFn u` is Rockafellar's `h = f₀ + λ₁f₁ + ⋯ + λ_m f_m`, which is *not* the Lagrangian: that
is `programLagrangian`, and `saddleFn` is the same function read on `ℝᵐ × ℝⁿ`, the shape
`IsSaddlePoint`, `maximin` and `minimax` take. `activeIndices u` is `{i | λᵢ ≠ 0}`, the book's
"(Omit terms with `λᵢ = 0`.)" — an omission that is not cosmetic, since `∂fᵢ(x̄)` can be empty at a
boundary point of `dom fᵢ` and `0 · ∅ = ∅ ≠ {0}`.

## References

* [rockafellar1970convex] §28 (pp. 273–290).
  Corollaries 28.2.2, 28.3.1 and 28.4.1 are stated there with no printed proof.
-/

open Set Pointwise

namespace Rockafellar

open ConvexAnalysis

variable {m n : ℕ}

/-! ### The ordinary convex program -/

/-- **Rockafellar's ordinary convex program** (§28): the `(m + 3)`-tuple `(C, f₀, f₁, …, f_m,
r)`. -/
structure OrdinaryConvexProgram (n m : ℕ) where
  /-- The non-empty convex set `C` over which the objective is minimised. -/
  C : Set (Rn n)
  /-- The objective `f₀`, a proper convex function with `dom f₀ = C`. -/
  f₀ : Rn n → EReal
  /-- The constraint functions `f₁, …, f_m`. -/
  f : Fin m → Rn n → EReal
  /-- The number of *inequality* constraints: `f₁ ≤ 0, …, f_r ≤ 0` and `f_{r+1} = 0, …, f_m = 0`. -/
  r : ℕ
  /-- `0 ≤ r ≤ m`. -/
  r_le : r ≤ m
  /-- `f₀` is convex. -/
  convexFn_f₀ : ConvexFn f₀
  /-- `f₀` is proper. -/
  proper_f₀ : Proper f₀
  /-- Rockafellar's extension convention (a): `dom f₀ = C`. -/
  dom_f₀ : dom f₀ = C
  /-- The inequality constraints are convex. -/
  convexFn_f : ∀ i : Fin m, (i : ℕ) < r → ConvexFn (f i)
  /-- The inequality constraints are proper. -/
  proper_f : ∀ i : Fin m, (i : ℕ) < r → Proper (f i)
  /-- Rockafellar's extension convention (b), first half: `dom fᵢ ⊇ C`. -/
  subset_dom_f : ∀ i : Fin m, (i : ℕ) < r → C ⊆ dom (f i)
  /-- Rockafellar's extension convention (b), second half: `ri (dom fᵢ) ⊇ ri C`. -/
  relint_subset : ∀ i : Fin m, (i : ℕ) < r → ri C ⊆ ri (dom (f i))
  /-- Rockafellar's extension convention (c): the equality constraints are affine on all of `ℝⁿ`. -/
  exists_affine :
    ∀ i : Fin m, r ≤ (i : ℕ) → ∃ a : Rn n →ᵃ[ℝ] ℝ, ∀ x, f i x = ((a x : ℝ) : EReal)

namespace OrdinaryConvexProgram

variable (P : OrdinaryConvexProgram n m)

/-- `C` is convex: it is the effective domain of a convex function. -/
theorem convex_C : Convex ℝ P.C := by
  rw [← P.dom_f₀]; exact P.convexFn_f₀.convex_dom

/-- `C` is non-empty: it is the effective domain of a proper function. -/
theorem nonempty_C : P.C.Nonempty := by
  rw [← P.dom_f₀]; exact P.proper_f₀.dom_nonempty

/-- A non-empty convex set in `ℝⁿ` has a non-empty relative interior (Theorem 6.2). -/
theorem relint_C_nonempty : (ri P.C).Nonempty :=
  Convex.relint_nonempty P.convex_C P.nonempty_C

@[simp] theorem mem_C_iff {x : Rn n} : x ∈ P.C ↔ P.f₀ x < ⊤ := by
  rw [← P.dom_f₀]; exact mem_dom

theorem f₀_eq_top_of_notMem {x : Rn n} (hx : x ∉ P.C) : P.f₀ x = ⊤ := by
  by_contra hc
  exact hx (P.mem_C_iff.2 (lt_of_le_of_ne le_top hc))

/-- No constraint function ever takes the value `-∞`: those with `i ≤ r` are proper and those with
`i > r` are real-valued. -/
theorem f_ne_bot (i : Fin m) (x : Rn n) : P.f i x ≠ ⊥ := by
  rcases lt_or_ge (i : ℕ) P.r with hi | hi
  · exact (P.proper_f i hi).ne_bot x
  · obtain ⟨a, ha⟩ := P.exists_affine i hi
    rw [ha x]; exact EReal.coe_ne_bot _

/-- Every constraint function is finite on `C`: Rockafellar's convention (b) is exactly what makes
the Lagrangian an inequality between real numbers. -/
theorem exists_coe_f {x : Rn n} (hx : x ∈ P.C) (i : Fin m) : ∃ c : ℝ, P.f i x = (c : EReal) := by
  rcases lt_or_ge (i : ℕ) P.r with hi | hi
  · exact EReal.exists_coe_of_ne_bot_of_lt_top ((P.proper_f i hi).ne_bot x)
      (mem_dom.1 (P.subset_dom_f i hi hx))
  · obtain ⟨a, ha⟩ := P.exists_affine i hi
    exact ⟨a x, ha x⟩

/-! ### Feasible solutions, the objective function and the optimal value -/

/-- **§28**: the set `C₀` of **feasible solutions** to `(P)`. -/
def feasibleSet : Set (Rn n) :=
  {x | x ∈ P.C ∧ (∀ i : Fin m, (i : ℕ) < P.r → P.f i x ≤ 0) ∧
    ∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i x = 0}

@[simp] theorem mem_feasibleSet {x : Rn n} :
    x ∈ P.feasibleSet ↔ x ∈ P.C ∧ (∀ i : Fin m, (i : ℕ) < P.r → P.f i x ≤ 0) ∧
      ∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i x = 0 := Iff.rfl

theorem feasibleSet_subset_C : P.feasibleSet ⊆ P.C := fun _ hx => hx.1

/-- **§28**: the intersection `C₁ ∩ ⋯ ∩ C_m` of the sets cut out by the `m` constraints, with
`Cᵢ = {x | fᵢ x ≤ 0}` for `i ≤ r` and `Cᵢ = {x | fᵢ x = 0}` for `i > r`. The feasible set is
`C ∩ C₁ ∩ ⋯ ∩ C_m`. -/
def constraintSet : Set (Rn n) :=
  {x | (∀ i : Fin m, (i : ℕ) < P.r → P.f i x ≤ 0) ∧ ∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i x = 0}

theorem feasibleSet_eq_inter : P.feasibleSet = P.C ∩ P.constraintSet := rfl

/-- `C₁ ∩ ⋯ ∩ C_m` is convex: the inequality constraints are convex and the equality constraints are
affine. -/
theorem convex_constraintSet : Convex ℝ P.constraintSet := by
  rintro x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩ a b ha hb hab
  refine ⟨fun i hi => (P.convexFn_f i hi).convex_le 0 (hx₁ i hi) (hy₁ i hi) ha hb hab,
    fun i hi => ?_⟩
  obtain ⟨g, hg⟩ := P.exists_affine i hi
  have hxg : g x = 0 := by
    have := hx₂ i hi; rw [hg] at this; exact_mod_cast this
  have hyg : g y = 0 := by
    have := hy₂ i hi; rw [hg] at this; exact_mod_cast this
  have hab' : a • x + b • y = (1 - b) • x + b • y := by rw [show (1 : ℝ) - b = a by linarith]
  rw [hg, hab', affineMap_segment g x y b, hxg, hyg]
  norm_num

/-- **§28**: the **objective function** `f = f₀ + δ(· ∣ C₀)`. -/
noncomputable def objective : Rn n → EReal := fun x => P.f₀ x + indicatorFn P.feasibleSet x

@[simp] theorem objective_of_mem {x : Rn n} (hx : x ∈ P.feasibleSet) :
    P.objective x = P.f₀ x := by
  rw [objective, indicatorFn_of_mem hx, add_zero]

@[simp] theorem objective_of_notMem {x : Rn n} (hx : x ∉ P.feasibleSet) : P.objective x = ⊤ := by
  rw [objective, indicatorFn_of_notMem hx,
    EReal.add_top_of_ne_bot (P.proper_f₀.ne_bot x)]

/-- The objective function is `f₀` restricted to `C₁ ∩ ⋯ ∩ C_m`: the constraint `x ∈ C` is
automatic, because `f₀` is already `+∞` off `C`. This is the form in which convexity and closedness
of the objective are read off. -/
theorem objective_eq_restrictFn :
    P.objective = ConvexAnalysis.restrictFn P.constraintSet P.f₀ := by
  funext x
  by_cases hx : x ∈ P.constraintSet
  · by_cases hC : x ∈ P.C
    · rw [P.objective_of_mem ⟨hC, hx⟩, restrictFn_of_mem hx]
    · rw [P.objective_of_notMem (fun h => hC h.1), restrictFn_of_mem hx,
        P.f₀_eq_top_of_notMem hC]
  · rw [P.objective_of_notMem (fun h => hx h.2), restrictFn_of_notMem hx]

theorem convexFn_objective : ConvexFn P.objective := by
  rw [P.objective_eq_restrictFn]
  exact P.convexFn_f₀.restrictFn P.convex_constraintSet

/-- **§28**: the objective function is closed when `f₀, f₁, …, f_r` are. -/
theorem closedFn_objective (hcl₀ : ClosedFn P.f₀)
    (hcl : ∀ i : Fin m, (i : ℕ) < P.r → ClosedFn (P.f i)) : ClosedFn P.objective := by
  have hclosed : IsClosed P.constraintSet := by
    have h₁ : P.constraintSet = (⋂ i : Fin m, ⋂ _ : (i : ℕ) < P.r, {x | P.f i x ≤ 0})
        ∩ ⋂ i : Fin m, ⋂ _ : P.r ≤ (i : ℕ), {x | P.f i x = 0} := by
      ext x; simp only [constraintSet, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [h₁]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun hi => ?_)
      (isClosed_iInter fun i => isClosed_iInter fun hi => ?_)
    · exact lowerSemicontinuous_iff_isClosed_le.1
        ((closedFn_iff_lowerSemicontinuous (P.proper_f i hi).ne_bot).1 (hcl i hi)) 0
    · obtain ⟨g, hg⟩ := P.exists_affine i hi
      have hset : {x : Rn n | P.f i x = 0} = g ⁻¹' {0} := by
        ext x
        rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, hg]
        exact ⟨fun h => by exact_mod_cast h, fun h => by rw [h]; rfl⟩
      rw [hset]
      exact IsClosed.preimage g.continuous_of_finiteDimensional isClosed_singleton
  rw [P.objective_eq_restrictFn]
  exact ClosedFn.restrictFn hcl₀ P.proper_f₀.ne_bot hclosed

theorem objective_ne_bot (x : Rn n) : P.objective x ≠ ⊥ := by
  by_cases hx : x ∈ P.feasibleSet
  · rw [P.objective_of_mem hx]; exact P.proper_f₀.ne_bot x
  · rw [P.objective_of_notMem hx]; exact top_ne_bot

/-- **§28**: the **optimal value** in `(P)` is the infimum of the objective function. -/
noncomputable def optimalValue : EReal := ⨅ x, P.objective x

/-- The optimal value is the infimum of `f₀` over the feasible solutions. -/
theorem optimalValue_eq_biInf : P.optimalValue = ⨅ x ∈ P.feasibleSet, P.f₀ x := by
  refine le_antisymm (le_iInf₂ fun x hx => ?_) (le_iInf fun x => ?_)
  · exact (iInf_le _ x).trans (le_of_eq (P.objective_of_mem hx))
  · by_cases hx : x ∈ P.feasibleSet
    · exact (iInf₂_le x hx).trans (le_of_eq (P.objective_of_mem hx).symm)
    · rw [P.objective_of_notMem hx]; exact le_top

theorem optimalValue_le {x : Rn n} (hx : x ∈ P.feasibleSet) : P.optimalValue ≤ P.f₀ x := by
  rw [P.optimalValue_eq_biInf]; exact iInf₂_le x hx

/-- **§28**: the **optimal solutions** are the points at which the objective function attains its
infimum. The book adds the proviso "provided that `f` is not identically `+∞`"; where that fails —
no feasible solution at all — `argmin` is all of `ℝⁿ` rather than empty, and every theorem below
that speaks of optimal solutions carries a hypothesis ruling the degenerate case out. -/
def optimalSolutions : Set (Rn n) := argmin P.objective

theorem mem_optimalSolutions_iff {x : Rn n} :
    x ∈ P.optimalSolutions ↔ P.objective x = P.optimalValue :=
  ⟨fun hx => (iInf_eq_of_mem_argmin hx).symm, fun hx z => by
    rw [hx, optimalValue]; exact iInf_le _ z⟩

/-- An optimal solution at which the optimal value is not `+∞` is feasible and attains it. -/
theorem mem_optimalSolutions_iff_of_ne_top (h : P.optimalValue ≠ ⊤) {x : Rn n} :
    x ∈ P.optimalSolutions ↔ x ∈ P.feasibleSet ∧ P.f₀ x = P.optimalValue := by
  rw [P.mem_optimalSolutions_iff]
  constructor
  · intro hx
    by_cases hf : x ∈ P.feasibleSet
    · exact ⟨hf, by rwa [P.objective_of_mem hf] at hx⟩
    · exact absurd (by rw [← hx, P.objective_of_notMem hf]) h
  · rintro ⟨hf, hv⟩; rw [P.objective_of_mem hf, hv]

/-! ### Kuhn–Tucker vectors -/

/-- Rockafellar's `h = f₀ + λ₁f₁ + ⋯ + λ_m f_m` (§28), the function whose infimum a vector of
Kuhn–Tucker coefficients is required to bring down to the optimal value. -/
noncomputable def lagrangeFn (u : Rn m) : Rn n → EReal :=
  fun x => P.f₀ x + ∑ i, (u i : EReal) * P.f i x

theorem lagrangeFn_apply (u : Rn m) (x : Rn n) :
    P.lagrangeFn u x = P.f₀ x + ∑ i, (u i : EReal) * P.f i x := rfl

/-- **§28**: `(λ₁, …, λ_m)` is a vector of **Kuhn–Tucker coefficients** for `(P)` — a **Kuhn–Tucker
vector** — when `λᵢ ≥ 0` for `i = 1, …, r` and the infimum of `f₀ + λ₁f₁ + ⋯ + λ_m f_m` is finite
and equal to the optimal value in `(P)`. This is the book's own definition, not the perturbational
inequality of §29 it is equivalent to; `mem_kuhnTucker_ineqBifun_iff` is the bridge. -/
structure IsKuhnTuckerVector (P : OrdinaryConvexProgram n m) (u : Rn m) : Prop where
  /-- The multipliers of the inequality constraints are non-negative. -/
  nonneg : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i
  /-- The infimum of `h` is not `-∞`. -/
  ne_bot : (⨅ x, P.lagrangeFn u x) ≠ ⊥
  /-- The infimum of `h` is not `+∞`. -/
  ne_top : (⨅ x, P.lagrangeFn u x) ≠ ⊤
  /-- The infimum of `h` is the optimal value in `(P)`. -/
  iInf_eq : (⨅ x, P.lagrangeFn u x) = P.optimalValue

/-! ### `h` as a finite sum, and its convexity, properness and closedness -/

/-- The `m + 1` summands of `h = f₀ + λ₁f₁ + ⋯ + λ_m f_m`, indexed by `Option (Fin m)` with the
objective in the `none` slot. Theorem 23.8 is stated for a finite family, so this is the shape in
which the subdifferential of `h` is computed. -/
noncomputable def lagrangeSummand (u : Rn m) (i : Option (Fin m)) : Rn n → EReal :=
  i.elim P.f₀ fun j x => (u j : EReal) * P.f j x

@[simp] theorem lagrangeSummand_none (u : Rn m) : P.lagrangeSummand u none = P.f₀ := rfl

@[simp] theorem lagrangeSummand_some (u : Rn m) (j : Fin m) :
    P.lagrangeSummand u (some j) = fun x => (u j : EReal) * P.f j x := rfl

theorem lagrangeFn_eq_finsetSum (u : Rn m) :
    P.lagrangeFn u = ∑ i : Option (Fin m), P.lagrangeSummand u i := by
  funext x
  rw [Finset.sum_apply, Fintype.sum_option]
  rfl

theorem convexFn_lagrangeSummand {u : Rn m} (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i)
    (i : Option (Fin m)) : ConvexFn (P.lagrangeSummand u i) := by
  cases i with
  | none => exact P.convexFn_f₀
  | some j =>
    rcases lt_or_ge (j : ℕ) P.r with hj | hj
    · exact convexFn_coe_mul (hu j hj) (P.convexFn_f j hj)
    · obtain ⟨g, hg⟩ := P.exists_affine j hj
      have hrw : P.lagrangeSummand u (some j) = fun x => (((u j • g) x : ℝ) : EReal) := by
        funext x
        simp only [lagrangeSummand_some]
        rw [hg x, ← EReal.coe_mul, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [hrw]
      exact (closedProperConvexFn_coe_affineMap
        (u j • g).continuous_of_finiteDimensional).convex

theorem proper_lagrangeSummand {u : Rn m} (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i)
    (i : Option (Fin m)) : Proper (P.lagrangeSummand u i) := by
  cases i with
  | none => exact P.proper_f₀
  | some j =>
    rcases lt_or_ge (j : ℕ) P.r with hj | hj
    · exact proper_coe_mul (hu j hj) (P.proper_f j hj)
    · obtain ⟨g, hg⟩ := P.exists_affine j hj
      have hrw : P.lagrangeSummand u (some j) = fun x => (((u j • g) x : ℝ) : EReal) := by
        funext x
        simp only [lagrangeSummand_some]
        rw [hg x, ← EReal.coe_mul, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [hrw]
      exact (closedProperConvexFn_coe_affineMap
        (u j • g).continuous_of_finiteDimensional).proper

theorem closedFn_lagrangeSummand (hcl₀ : ClosedFn P.f₀)
    (hcl : ∀ i : Fin m, (i : ℕ) < P.r → ClosedFn (P.f i)) {u : Rn m}
    (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i) (i : Option (Fin m)) :
    ClosedFn (P.lagrangeSummand u i) := by
  cases i with
  | none => exact hcl₀
  | some j =>
    rcases lt_or_ge (j : ℕ) P.r with hj | hj
    · exact closedFn_coe_mul (hu j hj) (hcl j hj) (P.proper_f j hj).ne_bot
    · obtain ⟨g, hg⟩ := P.exists_affine j hj
      have hrw : P.lagrangeSummand u (some j) = fun x => (((u j • g) x : ℝ) : EReal) := by
        funext x
        simp only [lagrangeSummand_some]
        rw [hg x, ← EReal.coe_mul, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [hrw]
      exact (closedProperConvexFn_coe_affineMap
        (u j • g).continuous_of_finiteDimensional).closed

theorem mem_dom_lagrangeSummand (u : Rn m) {x : Rn n} (hx : x ∈ P.C) (i : Option (Fin m)) :
    x ∈ dom (P.lagrangeSummand u i) := by
  cases i with
  | none => rw [lagrangeSummand_none, P.dom_f₀]; exact hx
  | some j =>
    obtain ⟨c, hc⟩ := P.exists_coe_f hx j
    rw [mem_dom]
    simp only [lagrangeSummand_some]
    rw [hc, ← EReal.coe_mul]
    exact EReal.coe_lt_top _

theorem convexFn_lagrangeFn {u : Rn m} (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i) :
    ConvexFn (P.lagrangeFn u) := by
  obtain ⟨x₀, hx₀⟩ := P.nonempty_C
  rw [P.lagrangeFn_eq_finsetSum u]
  exact (properConvexFn_finsetSum (fun i _ => P.convexFn_lagrangeSummand hu i)
    (fun i _ => P.proper_lagrangeSummand hu i)
    (fun i _ => P.mem_dom_lagrangeSummand u hx₀ i)).1

theorem proper_lagrangeFn {u : Rn m} (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i) :
    Proper (P.lagrangeFn u) := by
  obtain ⟨x₀, hx₀⟩ := P.nonempty_C
  rw [P.lagrangeFn_eq_finsetSum u]
  exact (properConvexFn_finsetSum (fun i _ => P.convexFn_lagrangeSummand hu i)
    (fun i _ => P.proper_lagrangeSummand hu i)
    (fun i _ => P.mem_dom_lagrangeSummand u hx₀ i)).2.1

/-- **Corollary 28.1.1**, first step: `h` is closed when `f₀, f₁, …, f_r` are. -/
theorem closedProperConvexFn_lagrangeFn (hcl₀ : ClosedFn P.f₀)
    (hcl : ∀ i : Fin m, (i : ℕ) < P.r → ClosedFn (P.f i)) {u : Rn m}
    (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i) : ClosedProperConvexFn (P.lagrangeFn u) := by
  obtain ⟨x₀, hx₀⟩ := P.nonempty_C
  rw [P.lagrangeFn_eq_finsetSum u]
  exact closedProperConvexFn_finsetSum
    (fun i _ => ⟨P.convexFn_lagrangeSummand hu i, P.closedFn_lagrangeSummand hcl₀ hcl hu i,
      P.proper_lagrangeSummand hu i⟩)
    (fun i _ => P.mem_dom_lagrangeSummand u hx₀ i)

/-! ### Elementary properties of `h` -/

theorem sum_coe_mul_f_ne_bot {u : Rn m} (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i) (x : Rn n) :
    (∑ i, (u i : EReal) * P.f i x) ≠ ⊥ := by
  refine EReal.sum_ne_bot fun i _ => ?_
  rcases lt_or_ge (i : ℕ) P.r with hi | hi
  · exact EReal.coe_mul_ne_bot (hu i hi) (P.f_ne_bot i x)
  · obtain ⟨g, hg⟩ := P.exists_affine i hi
    rw [hg x, ← EReal.coe_mul]
    exact EReal.coe_ne_bot _

theorem lagrangeFn_ne_bot {u : Rn m} (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i) (x : Rn n) :
    P.lagrangeFn u x ≠ ⊥ :=
  EReal.add_ne_bot_iff.2 ⟨P.proper_f₀.ne_bot x, P.sum_coe_mul_f_ne_bot hu x⟩

theorem lagrangeFn_eq_top_of_notMem_C {u : Rn m} (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i)
    {x : Rn n} (hx : x ∉ P.C) : P.lagrangeFn u x = ⊤ := by
  rw [lagrangeFn_apply, P.f₀_eq_top_of_notMem hx,
    EReal.top_add_of_ne_bot (P.sum_coe_mul_f_ne_bot hu x)]

/-- `h` at a point of `C`, read as a single real number. -/
theorem lagrangeFn_eq_coe {u : Rn m} {x : Rn n} {c₀ : ℝ} (h₀ : P.f₀ x = (c₀ : EReal))
    {c : Fin m → ℝ} (hc : ∀ i, P.f i x = (c i : EReal)) :
    P.lagrangeFn u x = ((c₀ + ∑ i, u i * c i : ℝ) : EReal) := by
  rw [lagrangeFn_apply, h₀,
    Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by rw [hc i, ← EReal.coe_mul]),
    ← EReal.coe_sum, ← EReal.coe_add]

/-- When every multiplier term vanishes, `h` agrees with the objective `f₀`. -/
theorem lagrangeFn_eq_f₀ {u : Rn m} {x : Rn n} (h : ∀ i : Fin m, (u i : EReal) * P.f i x = 0) :
    P.lagrangeFn u x = P.f₀ x := by
  rw [lagrangeFn_apply, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h i),
    Finset.sum_const_zero, add_zero]

/-- **Theorem 28.1**, the inequality the proof rests on: on the feasible set every constraint term
is non-positive, so `h ≤ f₀`. -/
theorem lagrangeFn_le_f₀ {u : Rn m} (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i) {x : Rn n}
    (hx : x ∈ P.feasibleSet) : P.lagrangeFn u x ≤ P.f₀ x := by
  have hsum : (∑ i, (u i : EReal) * P.f i x) ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => ?_
    rcases lt_or_ge (i : ℕ) P.r with hi | hi
    · exact coe_mul_nonpos (hu i hi) (hx.2.1 i hi)
    · rw [hx.2.2 i hi]; simp
  calc P.lagrangeFn u x ≤ P.f₀ x + 0 := add_le_add (le_refl _) hsum
    _ = P.f₀ x := add_zero _

/-- `h ≤ f` everywhere: below the feasible set by `lagrangeFn_le_f₀`, and off it because the
objective function is `+∞` there. -/
theorem lagrangeFn_le_objective {u : Rn m} (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i)
    (x : Rn n) : P.lagrangeFn u x ≤ P.objective x := by
  by_cases hx : x ∈ P.feasibleSet
  · rw [P.objective_of_mem hx]; exact P.lagrangeFn_le_f₀ hu hx
  · rw [P.objective_of_notMem hx]; exact le_top

theorem iInf_lagrangeFn_le_optimalValue {u : Rn m}
    (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i) : (⨅ x, P.lagrangeFn u x) ≤ P.optimalValue :=
  le_iInf fun x => (iInf_le _ x).trans (P.lagrangeFn_le_objective hu x)

theorem IsKuhnTuckerVector.optimalValue_ne_top {u : Rn m} (hu : P.IsKuhnTuckerVector u) :
    P.optimalValue ≠ ⊤ := by rw [← hu.iInf_eq]; exact hu.ne_top

theorem IsKuhnTuckerVector.optimalValue_ne_bot {u : Rn m} (hu : P.IsKuhnTuckerVector u) :
    P.optimalValue ≠ ⊥ := by rw [← hu.iInf_eq]; exact hu.ne_bot

end OrdinaryConvexProgram

variable (P : OrdinaryConvexProgram n m)

/-! ### Theorem 28.1: solving `(P)` by minimising `h` -/

/-- **Theorem 28.1**. Let `(λ₁, …, λ_m)` be a Kuhn–Tucker vector for `(P)`, let `D` be the set of
minimisers of `h = f₀ + λ₁f₁ + ⋯ + λ_m f_m` over `ℝⁿ`, let `I` be the set of `i ≤ r` with `λᵢ = 0`
and `J` its complement in `{1, …, m}`. Then the optimal solutions of `(P)` are exactly the `x̄ ∈ D`
with `fᵢ(x̄) = 0` for `i ∈ J` and `fᵢ(x̄) ≤ 0` for `i ∈ I`.

Rockafellar's summary "`h ≤ f` everywhere, with equality if and only if `x` is a feasible solution
such that `λᵢfᵢ(x) = 0`" is very slightly too strong: outside `C` both functions are `+∞`, so
equality holds there too although the point is infeasible. Nothing is lost, because `inf h` is
finite and so no such point lies in either minimum set. -/
theorem theorem_28_1 {u : Rn m} (hu : P.IsKuhnTuckerVector u) :
    {x : Rn n | x ∈ argmin (P.lagrangeFn u) ∧
        (∀ i : Fin m, ((i : ℕ) < P.r ∧ u i = 0) → P.f i x ≤ 0) ∧
        ∀ i : Fin m, ¬((i : ℕ) < P.r ∧ u i = 0) → P.f i x = 0}
      = P.optimalSolutions := by
  ext x
  constructor
  · rintro ⟨hD, hI, hJ⟩
    have hhx : P.lagrangeFn u x = ⨅ z, P.lagrangeFn u z := (iInf_eq_of_mem_argmin hD).symm
    have hxC : x ∈ P.C := by
      by_contra hc
      rw [P.lagrangeFn_eq_top_of_notMem_C hu.nonneg hc] at hhx
      exact hu.ne_top hhx.symm
    have hfeas : x ∈ P.feasibleSet := by
      refine ⟨hxC, fun i hi => ?_, fun i hi => hJ i fun hc => absurd hc.1 (by omega)⟩
      by_cases h0 : u i = 0
      · exact hI i ⟨hi, h0⟩
      · exact le_of_eq (hJ i fun hc => h0 hc.2)
    have hcs : ∀ i : Fin m, (u i : EReal) * P.f i x = 0 := by
      intro i
      by_cases h0 : (i : ℕ) < P.r ∧ u i = 0
      · rw [h0.2]; simp
      · rw [hJ i h0]; simp
    have hf₀ : P.f₀ x = P.optimalValue := by
      rw [← P.lagrangeFn_eq_f₀ hcs, hhx, hu.iInf_eq]
    rw [P.mem_optimalSolutions_iff, P.objective_of_mem hfeas, hf₀]
  · intro hx
    obtain ⟨hfeas, hf₀⟩ := (P.mem_optimalSolutions_iff_of_ne_top hu.optimalValue_ne_top).1 hx
    have hD : x ∈ argmin (P.lagrangeFn u) := by
      refine mem_argmin_iff_le_iInf.2 ?_
      rw [hu.iInf_eq, ← hf₀]
      exact P.lagrangeFn_le_f₀ hu.nonneg hfeas
    have heq : P.lagrangeFn u x = P.f₀ x := by
      refine le_antisymm (P.lagrangeFn_le_f₀ hu.nonneg hfeas) ?_
      rw [hf₀, ← hu.iInf_eq]
      exact iInf_le _ x
    -- read the identity `h x = f₀ x` as an identity between real numbers
    obtain ⟨c₀, hc₀⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (P.proper_f₀.ne_bot x)
      (P.mem_C_iff.1 hfeas.1)
    choose c hc using P.exists_coe_f hfeas.1
    have hzero : ∑ i, u i * c i = 0 := by
      have h := P.lagrangeFn_eq_coe (u := u) hc₀ hc
      rw [heq, hc₀, EReal.coe_eq_coe_iff] at h
      linarith
    have hnonpos : ∀ i ∈ Finset.univ, u i * c i ≤ 0 := by
      intro i _
      rcases lt_or_ge (i : ℕ) P.r with hi | hi
      · have hci : c i ≤ 0 := by
          have := hfeas.2.1 i hi
          rw [hc i] at this
          exact_mod_cast this
        exact mul_nonpos_of_nonneg_of_nonpos (hu.nonneg i hi) hci
      · have hci : c i = 0 := by
          have := hfeas.2.2 i hi
          rw [hc i] at this
          exact_mod_cast this
        rw [hci, mul_zero]
    have hterm := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).1 hzero
    refine ⟨hD, fun i hi => hfeas.2.1 i hi.1, fun i hi => ?_⟩
    rcases lt_or_ge (i : ℕ) P.r with h | h
    · have h0 : u i ≠ 0 := fun hc' => hi ⟨h, hc'⟩
      have := hterm i (Finset.mem_univ i)
      rw [hc i]
      exact_mod_cast (mul_eq_zero.1 this).resolve_left h0
    · exact hfeas.2.2 i h

/-- **Corollary 28.1.1**. If the `fᵢ` are all closed and the infimum of `h` is attained at a unique
point `w`, then `w` is the unique optimal solution to `(P)`. Uniqueness is Theorem 28.1; the content
is *existence*, which follows because `epi f ⊆ epi h` gives the objective no direction of recession
either, so Theorem 27.2 applies. -/
theorem corollary_28_1_1 (hcl₀ : ClosedFn P.f₀)
    (hcl : ∀ i : Fin m, (i : ℕ) < P.r → ClosedFn (P.f i)) {u : Rn m}
    (hu : P.IsKuhnTuckerVector u) {w : Rn n} (hmin : argmin (P.lagrangeFn u) = {w}) :
    P.optimalSolutions = {w} := by
  have hh : ClosedProperConvexFn (P.lagrangeFn u) :=
    P.closedProperConvexFn_lagrangeFn hcl₀ hcl hu.nonneg
  have hw : w ∈ argmin (P.lagrangeFn u) := by rw [hmin]; rfl
  have hwval : P.lagrangeFn u w = P.optimalValue := by
    rw [(iInf_eq_of_mem_argmin hw).symm, hu.iInf_eq]
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hh.proper.ne_bot w)
    (by rw [hwval]; exact lt_of_le_of_ne le_top hu.optimalValue_ne_top)
  -- `h` has no directions of recession, because its minimum set is a single point
  have hneμ : {z : Rn n | P.lagrangeFn u z ≤ (μ : EReal)}.Nonempty := ⟨w, le_of_eq hμ⟩
  have hrec : recessionConeFn (P.lagrangeFn u) = {(0 : Rn n)} := by
    rw [← recessionCone_setOf_le hh.convex hh.isClosed_epi hneμ, ← argmin_eq_setOf_le hw hμ, hmin]
    exact (isCompact_iff_recessionCone_eq_zero (convex_singleton w) isClosed_singleton
      ⟨w, rfl⟩).1 isCompact_singleton
  -- a level set of the objective at a level above the optimal value
  have hlt : P.optimalValue < ((μ + 1 : ℝ) : EReal) := by
    rw [← hwval, hμ, EReal.coe_lt_coe_iff]; linarith
  obtain ⟨z₀, hz₀⟩ : ∃ z, P.objective z < ((μ + 1 : ℝ) : EReal) := iInf_lt_iff.1 hlt
  have hfobj : ClosedProperConvexFn P.objective :=
    ⟨P.convexFn_objective, P.closedFn_objective hcl₀ hcl,
      ⟨⟨z₀, mem_dom.2 (hz₀.trans (EReal.coe_lt_top _))⟩, P.objective_ne_bot⟩⟩
  have hneβ : {z : Rn n | P.objective z ≤ ((μ + 1 : ℝ) : EReal)}.Nonempty := ⟨z₀, hz₀.le⟩
  have hneβh : {z : Rn n | P.lagrangeFn u z ≤ ((μ + 1 : ℝ) : EReal)}.Nonempty :=
    ⟨z₀, (P.lagrangeFn_le_objective hu.nonneg z₀).trans hz₀.le⟩
  have hclosedf : IsClosed {z : Rn n | P.objective z ≤ ((μ + 1 : ℝ) : EReal)} :=
    lowerSemicontinuous_iff_isClosed_le.1 hfobj.lowerSemicontinuous _
  have hcomph : IsCompact {z : Rn n | P.lagrangeFn u z ≤ ((μ + 1 : ℝ) : EReal)} :=
    isCompact_setOf_le hh.convex hh.closed hh.proper hrec hneβh
  have hcompf : IsCompact {z : Rn n | P.objective z ≤ ((μ + 1 : ℝ) : EReal)} :=
    hcomph.of_isClosed_subset hclosedf
      fun z hz => (P.lagrangeFn_le_objective hu.nonneg z).trans hz
  have hrecf : recessionConeFn P.objective = {(0 : Rn n)} := by
    rw [← recessionCone_setOf_le hfobj.convex hfobj.isClosed_epi hneβ]
    exact (isCompact_iff_recessionCone_eq_zero (hfobj.convex.convex_le _) hclosedf hneβ).1 hcompf
  have hne' : P.optimalSolutions.Nonempty :=
    argmin_nonempty_of_recessionConeFn_eq_zero hfobj.convex hfobj.closed hfobj.proper hrecf
  refine (hne'.subset_singleton_iff).1 ?_
  rw [← theorem_28_1 P hu]
  rintro x ⟨hD, -, -⟩
  rw [← hmin]
  exact hD

/-! ### The perturbation function and the bifunction of `(P)` -/

namespace OrdinaryConvexProgram

/-- The **bifunction of an ordinary convex program**, which is what makes `(P)` a *generalized*
convex program in the sense of §29: `F u x` is `f₀ x` when `x` satisfies the constraints of the
perturbed program `(P_u)` — `fᵢ x ≤ vᵢ` for `i ≤ r` and `fᵢ x = vᵢ` for `i > r` — and `+∞`
otherwise. The constraint `x ∈ C` is not imposed: `f₀` is already `+∞` off `C`. -/
noncomputable def ineqBifun : Bifun (Rn m) (Rn n) := fun u =>
  ConvexAnalysis.restrictFn
    {y | (∀ i : Fin m, (i : ℕ) < P.r → P.f i y ≤ (u i : EReal)) ∧
      ∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i y = (u i : EReal)} P.f₀

theorem ineqBifun_of_mem {u : Rn m} {x : Rn n}
    (h : (∀ i : Fin m, (i : ℕ) < P.r → P.f i x ≤ (u i : EReal)) ∧
      ∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i x = (u i : EReal)) :
    P.ineqBifun u x = P.f₀ x := restrictFn_of_mem h

theorem ineqBifun_of_notMem {u : Rn m} {x : Rn n}
    (h : ¬((∀ i : Fin m, (i : ℕ) < P.r → P.f i x ≤ (u i : EReal)) ∧
      ∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i x = (u i : EReal))) :
    P.ineqBifun u x = ⊤ := restrictFn_of_notMem h

theorem ineqBifun_eq_top_of_notMem_C {x : Rn n} (hx : x ∉ P.C) (u : Rn m) :
    P.ineqBifun u x = ⊤ := by
  by_cases h : (∀ i : Fin m, (i : ℕ) < P.r → P.f i x ≤ (u i : EReal)) ∧
      ∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i x = (u i : EReal)
  · rw [P.ineqBifun_of_mem h]; exact P.f₀_eq_top_of_notMem hx
  · exact P.ineqBifun_of_notMem h

/-- At the unperturbed parameter the bifunction is the objective function of `(P)`. -/
@[simp] theorem ineqBifun_zero : P.ineqBifun 0 = P.objective := by
  have hz : ∀ i : Fin m, ((0 : Rn m) i : EReal) = 0 := fun i => by norm_num
  rw [P.objective_eq_restrictFn]
  funext x
  by_cases hx : x ∈ P.constraintSet
  · rw [P.ineqBifun_of_mem ⟨fun i hi => by rw [hz i]; exact hx.1 i hi,
      fun i hi => by rw [hz i]; exact hx.2 i hi⟩, restrictFn_of_mem hx]
  · refine (P.ineqBifun_of_notMem fun hc => hx ⟨fun i hi => ?_, fun i hi => ?_⟩).trans
      (restrictFn_of_notMem hx).symm
    · have := hc.1 i hi; rwa [hz i] at this
    · have := hc.2 i hi; rwa [hz i] at this

/-- **§28**: the **perturbation function** `p` of `(P)`. `p u` is the optimal value of the perturbed
program `(P_u)`, and `p 0` is the optimal value of `(P)`. -/
noncomputable def perturbFn : Rn m → EReal := infBifun P.ineqBifun

theorem perturbFn_apply (u : Rn m) : P.perturbFn u = ⨅ x, P.ineqBifun u x := rfl

/-- **§28**: "of course, `p(0)` is the optimal value in `(P)`". -/
@[simp] theorem perturbFn_zero : P.perturbFn 0 = P.optimalValue := by
  rw [perturbFn_apply, P.ineqBifun_zero]; rfl

end OrdinaryConvexProgram

/-! ### Theorem 28.2: existence of Kuhn–Tucker vectors -/

namespace OrdinaryConvexProgram

/-- The optimal value read as an infimum over `C₁ ∩ ⋯ ∩ C_m` rather than over `C₀`: `f₀` is `+∞` off
`C`, so the two infima agree. This is the form the backbone's `optimalValue` takes. -/
theorem optimalValue_eq_biInf_constraintSet :
    P.optimalValue = ⨅ x ∈ P.constraintSet, P.f₀ x := by
  have h : P.optimalValue = ⨅ x, P.objective x := rfl
  rw [h, P.objective_eq_restrictFn]
  rfl

end OrdinaryConvexProgram

/-- **Theorem 28.2**. Let `I` be a set of indices containing every `i` at which `fᵢ` fails to be
affine — so `I` contains no equality constraint. If the optimal value in `(P)` is not `-∞` and
`(P)` has a feasible solution in `ri C` satisfying with strict inequality all the inequality
constraints for `i ∈ I`, then `(P)` has a Kuhn–Tucker vector.

`I` is taken as a `Finset (Fin m)` with the book's condition split into its two halves. The proof
translates the book's single family split at `r` into the backbone's role-split families of
`exists_isKuhnTuckerVector_of_slater`: an equality constraint becomes two weak inequalities, and
its multiplier is recovered as their difference — Rockafellar's own reduction. -/
theorem theorem_28_2 {I : Finset (Fin m)}
    (hIr : ∀ i : Fin m, P.r ≤ (i : ℕ) → i ∉ I)
    (hIaff : ∀ i : Fin m, (i : ℕ) < P.r → i ∉ I →
      ∃ a : Rn n →ᵃ[ℝ] ℝ, ∀ x, P.f i x = ((a x : ℝ) : EReal))
    (hbot : P.optimalValue ≠ ⊥)
    (hslater : ∃ x ∈ ri P.C, (∀ i ∈ I, P.f i x < 0) ∧ x ∈ P.constraintSet) :
    ∃ u : Rn m, P.IsKuhnTuckerVector u := by
  classical
  have hIlt : ∀ i : Fin m, i ∈ I → (i : ℕ) < P.r := fun i hi => by
    by_contra hc; exact hIr i (not_lt.1 hc) hi
  -- a total affine datum, with junk on `I`
  have haff : ∀ i : Fin m, ∃ a : Rn n →ᵃ[ℝ] ℝ, i ∉ I → ∀ x, P.f i x = ((a x : ℝ) : EReal) := by
    intro i
    by_cases hI : i ∈ I
    · exact ⟨AffineMap.const ℝ (Rn n) 0, fun hc => absurd hI hc⟩
    · rcases lt_or_ge (i : ℕ) P.r with hi | hi
      · obtain ⟨a, hax⟩ := hIaff i hi hI; exact ⟨a, fun _ => hax⟩
      · obtain ⟨a, hax⟩ := P.exists_affine i hi; exact ⟨a, fun _ => hax⟩
  choose a ha using haff
  -- the backbone's two families
  set g : {i : Fin m // i ∈ I} → Rn n → EReal := fun i => P.f i with hgdef
  set b : Fin m ⊕ Fin m → Rn n →ᵃ[ℝ] ℝ :=
    Sum.elim (fun i => if i ∈ I then 0 else a i)
      (fun i => if (i : ℕ) < P.r then 0 else -(a i)) with hbdef
  have hbl : ∀ (i : Fin m), i ∈ I → ∀ x, b (Sum.inl i) x = 0 := by
    intro i hi x; simp [hbdef, hi]
  have hbl' : ∀ (i : Fin m), i ∉ I → ∀ x, b (Sum.inl i) x = a i x := by
    intro i hi x; simp [hbdef, hi]
  have hbr : ∀ (i : Fin m), (i : ℕ) < P.r → ∀ x, b (Sum.inr i) x = 0 := by
    intro i hi x; simp [hbdef, hi]
  have hbr' : ∀ (i : Fin m), P.r ≤ (i : ℕ) → ∀ x, b (Sum.inr i) x = -(a i x) := by
    intro i hi x; simp [hbdef, not_lt.2 hi]
  -- the two descriptions of the feasible set agree
  have hfeas : ConvexAnalysis.feasibleSet g b = P.constraintSet := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · by_cases hI : i ∈ I
        · exact h1 ⟨i, hI⟩
        · have hb := h2 (Sum.inl i)
          rw [hbl' i hI x] at hb
          rw [ha i hI x]
          exact_mod_cast hb
      · have hI : i ∉ I := hIr i hi
        have h₁ := h2 (Sum.inl i)
        have h₂ := h2 (Sum.inr i)
        rw [hbl' i hI x] at h₁
        rw [hbr' i hi x] at h₂
        have hzero : a i x = 0 := by linarith
        rw [ha i hI x, hzero]
        rfl
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => h1 (i : Fin m) (hIlt i i.2), fun j => ?_⟩
      cases j with
      | inl i =>
        by_cases hI : i ∈ I
        · rw [hbl i hI x]
        · rw [hbl' i hI x]
          rcases lt_or_ge (i : ℕ) P.r with hi | hi
          · have hb := h1 i hi; rw [ha i hI x] at hb; exact_mod_cast hb
          · have hb := h2 i hi
            rw [ha i hI x] at hb
            have hz : a i x = 0 := by exact_mod_cast hb
            rw [hz]
      | inr i =>
        rcases lt_or_ge (i : ℕ) P.r with hi | hi
        · rw [hbr i hi x]
        · rw [hbr' i hi x]
          have hI : i ∉ I := hIr i hi
          have hb := h2 i hi
          rw [ha i hI x] at hb
          have hz : a i x = 0 := by exact_mod_cast hb
          rw [hz, neg_zero]
  have hoval : ConvexAnalysis.optimalValue P.f₀ g b = P.optimalValue := by
    have h : ConvexAnalysis.optimalValue P.f₀ g b
        = ⨅ x ∈ ConvexAnalysis.feasibleSet g b, P.f₀ x := rfl
    rw [h, hfeas, P.optimalValue_eq_biInf_constraintSet]
  obtain ⟨x₀, hx₀ri, hx₀I, hx₀C⟩ := hslater
  have hx₀feas : x₀ ∈ ConvexAnalysis.feasibleSet g b := by rw [hfeas]; exact hx₀C
  obtain ⟨l, μ, hkt⟩ := exists_isKuhnTuckerVector_of_slater (f₀ := P.f₀) (f := g) (b := b)
    P.convexFn_f₀ P.proper_f₀ (fun i => P.convexFn_f (i : Fin m) (hIlt i i.2))
    (fun i => P.proper_f (i : Fin m) (hIlt i i.2))
    (fun i => by rw [P.dom_f₀]; exact P.subset_dom_f (i : Fin m) (hIlt i i.2))
    (by rw [hoval]; exact hbot)
    ⟨x₀, by rw [P.dom_f₀]; exact hx₀ri, fun i => hx₀I (i : Fin m) i.2, hx₀feas.2⟩
  -- assemble the Kuhn–Tucker vector of `(P)`
  set uv : Fin m → ℝ := fun i =>
    if h : i ∈ I then l ⟨i, h⟩
    else if (i : ℕ) < P.r then μ (Sum.inl i) else μ (Sum.inl i) - μ (Sum.inr i) with huv
  have huvI : ∀ (i : Fin m) (h : i ∈ I), uv i = l ⟨i, h⟩ := fun i h => by simp [huv, h]
  have huvLt : ∀ i : Fin m, i ∉ I → (i : ℕ) < P.r → uv i = μ (Sum.inl i) := by
    intro i hI hi; simp [huv, hI, hi]
  have huvGe : ∀ i : Fin m, i ∉ I → P.r ≤ (i : ℕ) →
      uv i = μ (Sum.inl i) - μ (Sum.inr i) := by
    intro i hI hi; simp [huv, hI, not_lt.2 hi]
  have hnn : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ (WithLp.toLp 2 uv : Rn m) i := by
    intro i hi
    change 0 ≤ uv i
    by_cases hI : i ∈ I
    · rw [huvI i hI]; exact hkt.nonneg _
    · rw [huvLt i hI hi]; exact hkt.nonneg_affine _
  -- the two Lagrangians agree
  have hlag : P.lagrangeFn (WithLp.toLp 2 uv)
      = ConvexAnalysis.programLagrangian P.f₀ g b l μ := by
    funext x
    by_cases hxC : x ∈ P.C
    · obtain ⟨c₀, hc₀⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (P.proper_f₀.ne_bot x)
        (P.mem_C_iff.1 hxC)
      choose c hc using P.exists_coe_f hxC
      have hac : ∀ i : Fin m, i ∉ I → a i x = c i := by
        intro i hI
        have h := ha i hI x
        rw [hc i] at h
        exact_mod_cast h.symm
      have key : ∀ i : Fin m,
          (if i ∈ I then uv i * c i else 0) + (μ (Sum.inl i) * b (Sum.inl i) x
            + μ (Sum.inr i) * b (Sum.inr i) x) = uv i * c i := by
        intro i
        by_cases hI : i ∈ I
        · rw [hbl i hI x, hbr i (hIlt i hI) x]
          simp [hI]
        · rcases lt_or_ge (i : ℕ) P.r with hi | hi
          · rw [hbl' i hI x, hbr i hi x, hac i hI, huvLt i hI hi]
            simp [hI]
          · rw [hbl' i hI x, hbr' i hi x, hac i hI, huvGe i hI hi]
            simp [hI]
            ring
      have hA : ∑ i : Fin m, (if i ∈ I then uv i * c i else 0)
          = ∑ i : {i : Fin m // i ∈ I}, l i * c (i : Fin m) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter,
          ← Finset.sum_coe_sort I fun i => uv i * c i]
        exact Finset.sum_congr rfl fun i _ => by rw [huvI (i : Fin m) i.2]
      have hBC : (∑ j, μ j * b j x)
          = (∑ i : Fin m, μ (Sum.inl i) * b (Sum.inl i) x)
            + ∑ i : Fin m, μ (Sum.inr i) * b (Sum.inr i) x := Fintype.sum_sum_type _
      have hsplit : ∑ i : Fin m, uv i * c i
          = (∑ i : {i : Fin m // i ∈ I}, l i * c (i : Fin m)) + ∑ j, μ j * b j x :=
        calc ∑ i : Fin m, uv i * c i
            = ∑ i : Fin m, ((if i ∈ I then uv i * c i else 0)
                + (μ (Sum.inl i) * b (Sum.inl i) x
                  + μ (Sum.inr i) * b (Sum.inr i) x)) :=
              Finset.sum_congr rfl fun i _ => (key i).symm
          _ = (∑ i : Fin m, (if i ∈ I then uv i * c i else 0))
                + ∑ i : Fin m, (μ (Sum.inl i) * b (Sum.inl i) x
                  + μ (Sum.inr i) * b (Sum.inr i) x) := Finset.sum_add_distrib
          _ = (∑ i : {i : Fin m // i ∈ I}, l i * c (i : Fin m)) + ∑ j, μ j * b j x := by
              rw [hA, hBC, Finset.sum_add_distrib]
      rw [P.lagrangeFn_eq_coe hc₀ hc,
        programLagrangian_eq_coe (f := g) (b := b) (l := l) (μ := μ) hc₀
          (r := fun i : {i : Fin m // i ∈ I} => c (i : Fin m)) (fun i => hc (i : Fin m)),
        EReal.coe_eq_coe_iff, hsplit]
      ring
    · rw [P.lagrangeFn_eq_top_of_notMem_C hnn hxC,
        programLagrangian_eq_top (f := g) (b := b) (μ := μ) hkt.nonneg
          (fun i y => P.f_ne_bot (i : Fin m) y) (P.f₀_eq_top_of_notMem hxC)]
  exact ⟨WithLp.toLp 2 uv, hnn, by rw [hlag]; exact hkt.ne_bot, by rw [hlag]; exact hkt.ne_top,
    by rw [hlag, hkt.iInf_eq, hoval]⟩

/-- **Corollary 28.2.1**. For a program with only inequality constraints the Slater point need not
lie in `ri C`: some `x ∈ C` with `f₁(x) < 0, …, f_m(x) < 0` is enough. It is a special case of
Theorem 28.2 and not a substitute for it, since it needs `r = m` and a point satisfying *every*
constraint strictly. -/
theorem corollary_28_2_1 (hrm : P.r = m) (hbot : P.optimalValue ≠ ⊥)
    (hslater : ∃ x ∈ P.C, ∀ i : Fin m, P.f i x < 0) :
    ∃ u : Rn m, P.IsKuhnTuckerVector u := by
  have hlt : ∀ i : Fin m, (i : ℕ) < P.r := fun i => by rw [hrm]; exact i.isLt
  set b : Empty → Rn n →ᵃ[ℝ] ℝ := fun j => j.elim with hbdef
  have hfeas : ConvexAnalysis.feasibleSet P.f b = P.constraintSet := by
    ext x
    exact ⟨fun h => ⟨fun i _ => h.1 i, fun i hi => absurd (hlt i) (not_lt.2 hi)⟩,
      fun h => ⟨fun i => h.1 i (hlt i), fun j => j.elim⟩⟩
  have hoval : ConvexAnalysis.optimalValue P.f₀ P.f b = P.optimalValue := by
    have h : ConvexAnalysis.optimalValue P.f₀ P.f b
        = ⨅ x ∈ ConvexAnalysis.feasibleSet P.f b, P.f₀ x := rfl
    rw [h, hfeas, P.optimalValue_eq_biInf_constraintSet]
  obtain ⟨x₀, hx₀C, hx₀⟩ := hslater
  obtain ⟨l, μ, hkt⟩ := exists_isKuhnTuckerVector_of_mem_dom (f₀ := P.f₀) (f := P.f) (b := b)
    P.convexFn_f₀ P.proper_f₀ (fun i => P.convexFn_f i (hlt i)) (fun i => P.proper_f i (hlt i))
    (fun i => by rw [P.dom_f₀]; exact P.subset_dom_f i (hlt i))
    (fun i => by rw [P.dom_f₀]; exact P.relint_subset i (hlt i))
    (by rw [hoval]; exact hbot)
    ⟨x₀, by rw [P.dom_f₀]; exact hx₀C, hx₀, fun j => j.elim⟩
  have hlag : P.lagrangeFn (WithLp.toLp 2 l)
      = ConvexAnalysis.programLagrangian P.f₀ P.f b l μ := by
    funext x
    rw [OrdinaryConvexProgram.lagrangeFn_apply, programLagrangian_apply]
    simp
  exact ⟨WithLp.toLp 2 l, fun i _ => hkt.nonneg i, by rw [hlag]; exact hkt.ne_bot,
    by rw [hlag]; exact hkt.ne_top, by rw [hlag, hkt.iInf_eq, hoval]⟩

/-- The book's linear constraint `⟨a, x⟩ - α`, read as an affine function on `ℝⁿ`. -/
noncomputable def linConstraint (v : Rn n) (α : ℝ) : Rn n →ᵃ[ℝ] ℝ :=
  (linFn v).toLinearMap.toAffineMap - AffineMap.const ℝ (Rn n) α

@[simp] theorem linConstraint_apply (v : Rn n) (α : ℝ) (x : Rn n) :
    linConstraint v α x = pairing n x v - α := by
  simp only [linConstraint, AffineMap.coe_sub, Pi.sub_apply, AffineMap.const_apply,
    LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe, linFn_apply]

/-- **Corollary 28.2.2**, stated in the book with **no proof**. A program whose constraints are all
*linear*, `fᵢ(x) = ⟨aᵢ, x⟩ - αᵢ`, needs nothing beyond a feasible solution in `ri C`. It is Theorem
28.2 at `I = ∅`: with no non-affine constraint there is nothing to satisfy strictly. -/
theorem corollary_28_2_2
    (hlin : ∀ i : Fin m, ∃ (v : Rn n) (α : ℝ), ∀ x, P.f i x = ((pairing n x v - α : ℝ) : EReal))
    (hbot : P.optimalValue ≠ ⊥) (hfeas : ∃ x ∈ ri P.C, x ∈ P.constraintSet) :
    ∃ u : Rn m, P.IsKuhnTuckerVector u := by
  obtain ⟨x₀, hx₀ri, hx₀C⟩ := hfeas
  refine theorem_28_2 P (I := ∅) (fun i _ => Finset.notMem_empty i)
    (fun i _ _ => ?_) hbot ⟨x₀, hx₀ri, fun i hi => absurd hi (Finset.notMem_empty i), hx₀C⟩
  obtain ⟨v, α, hv⟩ := hlin i
  exact ⟨linConstraint v α, fun x => by rw [hv x, linConstraint_apply]⟩

/-! ### The Lagrangian of an ordinary convex program -/

namespace OrdinaryConvexProgram

/-- **§28**: the cone `E_r = {u* = (v₁*, …, v_m*) ∈ ℝᵐ | vᵢ* ≥ 0, i = 1, …, r}` of admissible
Lagrange multiplier vectors. `vᵢ*` is the **Lagrange multiplier** associated with the `i`-th
constraint of `(P)`. -/
def multiplierCone : Set (Rn m) := {u | ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i}

@[simp] theorem mem_multiplierCone {u : Rn m} :
    u ∈ P.multiplierCone ↔ ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i := Iff.rfl

theorem zero_mem_multiplierCone : (0 : Rn m) ∈ P.multiplierCone := by intro i _; simp

/-- `eᵢ`, the `i`-th row of the `m × m` identity matrix (§28). -/
noncomputable def unitVec (m : ℕ) (i : Fin m) : Rn m := EuclideanSpace.single i (1 : ℝ)

@[simp] theorem unitVec_apply (m : ℕ) (i j : Fin m) :
    unitVec m i j = if j = i then (1 : ℝ) else 0 := by
  simp [unitVec]

theorem unitVec_mem_multiplierCone (i : Fin m) : unitVec m i ∈ P.multiplierCone := by
  intro j _
  rw [unitVec_apply]
  by_cases h : j = i <;> simp [h]

/-- `f₀` is finite on `C`. -/
theorem exists_coe_f₀ {x : Rn n} (hx : x ∈ P.C) : ∃ c : ℝ, P.f₀ x = (c : EReal) :=
  EReal.exists_coe_of_ne_bot_of_lt_top (P.proper_f₀.ne_bot x) (P.mem_C_iff.1 hx)

/-- `h = f₀ + λ₁f₁ + ⋯ + λ_m f_m` is finite at every point of `C`, whatever the multipliers. -/
theorem exists_coe_lagrangeFn (u : Rn m) {x : Rn n} (hx : x ∈ P.C) :
    ∃ c : ℝ, P.lagrangeFn u x = (c : EReal) := by
  obtain ⟨c₀, h₀⟩ := P.exists_coe_f₀ hx
  choose c hc using P.exists_coe_f hx
  exact ⟨c₀ + ∑ i, u i * c i, P.lagrangeFn_eq_coe h₀ hc⟩

@[simp] theorem lagrangeFn_zero (x : Rn n) : P.lagrangeFn 0 x = P.f₀ x := by
  refine P.lagrangeFn_eq_f₀ fun i => ?_
  have h : (((0 : Rn m) i : ℝ) : EReal) = 0 := by simp
  rw [h, zero_mul]

theorem lagrangeFn_unitVec (i : Fin m) (x : Rn n) :
    P.lagrangeFn (unitVec m i) x = P.f₀ x + P.f i x := by
  rw [lagrangeFn_apply]
  congr 1
  have hsum : (∑ j, ((unitVec m i j : ℝ) : EReal) * P.f j x)
      = ((unitVec m i i : ℝ) : EReal) * P.f i x := by
    refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun hj => absurd (Finset.mem_univ i) hj)
    have h : ((unitVec m i j : ℝ) : EReal) = 0 := by rw [unitVec_apply]; simp [hj]
    rw [h, zero_mul]
  rw [hsum]
  have h1 : ((unitVec m i i : ℝ) : EReal) = 1 := by rw [unitVec_apply]; simp
  rw [h1, one_mul]

/-- **§28**: the **Lagrangian** `L` of `(P)`, a function on `ℝᵐ × ℝⁿ`: `h(x)` when `u* ∈ E_r` and
`x ∈ C`, `-∞` when `u* ∉ E_r` and `x ∈ C`, `+∞` when `x ∉ C`. -/
noncomputable def programLagrangian (u : Rn m) (x : Rn n) : EReal :=
  ⨅ _ : x ∈ P.C, ⨆ _ : u ∈ P.multiplierCone, P.lagrangeFn u x

theorem programLagrangian_eq_lagrangeFn {u : Rn m} {x : Rn n} (hx : x ∈ P.C)
    (hu : u ∈ P.multiplierCone) : P.programLagrangian u x = P.lagrangeFn u x := by
  rw [programLagrangian, iInf_pos hx, iSup_pos hu]

theorem programLagrangian_eq_bot {u : Rn m} {x : Rn n} (hx : x ∈ P.C)
    (hu : u ∉ P.multiplierCone) : P.programLagrangian u x = ⊥ := by
  rw [programLagrangian, iInf_pos hx, iSup_neg hu]

theorem programLagrangian_eq_top {x : Rn n} (hx : x ∉ P.C) (u : Rn m) :
    P.programLagrangian u x = ⊤ := by
  rw [programLagrangian, iInf_neg hx]

/-- The Lagrangian read as a saddle-function on `ℝᵐ × ℝⁿ`, which is the shape §36's minimax theory
and the backbone's `IsSaddlePoint`, `maximin` and `minimax` are stated in. -/
noncomputable def saddleFn : Rn m × Rn n → EReal := fun q => P.programLagrangian q.1 q.2

theorem saddleFn_apply (q : Rn m × Rn n) : P.saddleFn q = P.programLagrangian q.1 q.2 := rfl

/-! #### The program is recovered from its Lagrangian

"`L` reflects all the structure of `(P)`, because the `(m + 3)`-tuple `(C, f₀, …, f_m, r)` can be
recovered completely from `L`" — stated here as three theorems and one consequence. -/

/-- `C` is where `L` is not `+∞`. -/
theorem mem_C_iff_programLagrangian_ne_top {x : Rn n} :
    x ∈ P.C ↔ P.programLagrangian 0 x ≠ ⊤ := by
  constructor
  · intro hx
    rw [P.programLagrangian_eq_lagrangeFn hx P.zero_mem_multiplierCone, P.lagrangeFn_zero]
    exact (P.mem_C_iff.1 hx).ne
  · intro hne
    by_contra hx
    exact hne (P.programLagrangian_eq_top hx 0)

/-- `E_r` is where `L(·, x)` is not `-∞`, for any `x ∈ C`. -/
theorem mem_multiplierCone_iff_programLagrangian_ne_bot {u : Rn m} {x : Rn n} (hx : x ∈ P.C) :
    u ∈ P.multiplierCone ↔ P.programLagrangian u x ≠ ⊥ := by
  constructor
  · intro hu
    obtain ⟨c, hc⟩ := P.exists_coe_lagrangeFn u hx
    rw [P.programLagrangian_eq_lagrangeFn hx hu, hc]
    exact EReal.coe_ne_bot c
  · intro hne
    by_contra hu
    exact hne (P.programLagrangian_eq_bot hx hu)

/-- **§28**: "the set of points where `L` is finite is `E_r × C`". -/
theorem setOf_programLagrangian_finite :
    {q : Rn m × Rn n | P.programLagrangian q.1 q.2 ≠ ⊥ ∧ P.programLagrangian q.1 q.2 ≠ ⊤}
      = P.multiplierCone ×ˢ P.C := by
  ext q
  rw [Set.mem_ofPred_eq, Set.mem_prod]
  constructor
  · rintro ⟨hb, ht⟩
    have hC : q.2 ∈ P.C := by
      by_contra hc
      exact ht (P.programLagrangian_eq_top hc q.1)
    exact ⟨(P.mem_multiplierCone_iff_programLagrangian_ne_bot hC).2 hb, hC⟩
  · rintro ⟨hu, hC⟩
    obtain ⟨c, hc⟩ := P.exists_coe_lagrangeFn q.1 hC
    rw [P.programLagrangian_eq_lagrangeFn hC hu, hc]
    exact ⟨EReal.coe_ne_bot c, EReal.coe_ne_top c⟩

/-- **§28**: `f₀(x) = L(0, x)` for `x ∈ C`. -/
theorem f₀_eq_programLagrangian {x : Rn n} (hx : x ∈ P.C) : P.f₀ x = P.programLagrangian 0 x := by
  rw [P.programLagrangian_eq_lagrangeFn hx P.zero_mem_multiplierCone, P.lagrangeFn_zero]

/-- **§28**: `fᵢ(x) = L(eᵢ, x) - L(0, x)` for `x ∈ C`. -/
theorem f_eq_programLagrangian_sub {x : Rn n} (hx : x ∈ P.C) (i : Fin m) :
    P.f i x = P.programLagrangian (unitVec m i) x - P.programLagrangian 0 x := by
  obtain ⟨c₀, h₀⟩ := P.exists_coe_f₀ hx
  obtain ⟨c, hc⟩ := P.exists_coe_f hx i
  rw [P.programLagrangian_eq_lagrangeFn hx (P.unitVec_mem_multiplierCone i),
    P.programLagrangian_eq_lagrangeFn hx P.zero_mem_multiplierCone, P.lagrangeFn_zero,
    P.lagrangeFn_unitVec, h₀, hc, ← EReal.coe_add, ← EReal.coe_sub]
  norm_num

private theorem r_le_of_multiplierCone_subset {P₁ P₂ : OrdinaryConvexProgram n m}
    (h : P₁.multiplierCone ⊆ P₂.multiplierCone) : P₂.r ≤ P₁.r := by
  by_contra hlt
  have hc : P₁.r < P₂.r := by omega
  have him : P₁.r < m := lt_of_lt_of_le hc P₂.r_le
  set i : Fin m := ⟨P₁.r, him⟩ with hi
  have hmem : -unitVec m i ∈ P₁.multiplierCone := by
    intro j hj
    have hne : j ≠ i := by
      rintro rfl
      exact absurd hj (by rw [hi]; exact lt_irrefl _)
    have hval : (-unitVec m i) j = -(unitVec m i j) := rfl
    rw [hval, unitVec_apply]
    simp [hne]
  have hneg := h hmem i (by rw [hi]; exact hc)
  have hval : (-unitVec m i) i = -(unitVec m i i) := rfl
  rw [hval, unitVec_apply] at hneg
  norm_num at hneg

/-- `r` is recovered from `L` as well, because `E_r` is. -/
theorem r_eq_of_multiplierCone_eq {P₁ P₂ : OrdinaryConvexProgram n m}
    (h : P₁.multiplierCone = P₂.multiplierCone) : P₁.r = P₂.r :=
  le_antisymm (r_le_of_multiplierCone_subset h.symm.subset)
    (r_le_of_multiplierCone_subset h.subset)

/-- **§28**: "There is thus a one-to-one correspondence between ordinary convex programs and their
Lagrangians." Two ordinary convex programs with the same Lagrangian have the same `C`, the same `r`,
and the same `f₀, f₁, …, f_m` **on `C`** — which is all the data the tuple carries, the values of
`fᵢ` off `C` being irrelevant to `(P)`. -/
theorem eq_of_programLagrangian_eq {P₁ P₂ : OrdinaryConvexProgram n m}
    (h : P₁.programLagrangian = P₂.programLagrangian) :
    P₁.C = P₂.C ∧ P₁.r = P₂.r ∧ (∀ x ∈ P₁.C, P₁.f₀ x = P₂.f₀ x) ∧
      ∀ x ∈ P₁.C, ∀ i : Fin m, P₁.f i x = P₂.f i x := by
  have hC : P₁.C = P₂.C := by
    ext x
    rw [P₁.mem_C_iff_programLagrangian_ne_top, P₂.mem_C_iff_programLagrangian_ne_top,
      show P₁.programLagrangian 0 x = P₂.programLagrangian 0 x from by rw [h]]
  obtain ⟨x₀, hx₀⟩ := P₁.nonempty_C
  have hcone : P₁.multiplierCone = P₂.multiplierCone := by
    ext u
    rw [P₁.mem_multiplierCone_iff_programLagrangian_ne_bot hx₀,
      P₂.mem_multiplierCone_iff_programLagrangian_ne_bot (hC ▸ hx₀),
      show P₁.programLagrangian u x₀ = P₂.programLagrangian u x₀ from by rw [h]]
  refine ⟨hC, r_eq_of_multiplierCone_eq hcone, fun x hx => ?_, fun x hx i => ?_⟩
  · rw [P₁.f₀_eq_programLagrangian hx, P₂.f₀_eq_programLagrangian (hC ▸ hx), h]
  · rw [P₁.f_eq_programLagrangian_sub hx i, P₂.f_eq_programLagrangian_sub (hC ▸ hx) i, h]

end OrdinaryConvexProgram

/-! #### The Lagrangian is the §29 Lagrangian of `ineqBifun`

Rockafellar's `L(u*, x) = inf {f₀(x) + v₁*v₁ + ⋯ + v_m*v_m | u ∈ U_x}` *is* the §29 definition of
the Lagrangian of the bifunction of `(P)`, so `programLagrangian` agrees with the backbone's
`lagrangian` and everything §29 proves about the latter applies. -/

namespace OrdinaryConvexProgram

private theorem pairing_unitVec {k : ℕ} (i : Fin k) (u : Rn k) :
    pairing k (unitVec k i) u = u i := by
  rw [pairing_eq_sum]
  refine (Finset.sum_eq_single i (fun j _ hj => ?_)
    (fun hj => absurd (Finset.mem_univ i) hj)).trans ?_
  · rw [unitVec_apply]; simp [hj]
  · rw [unitVec_apply]; simp

/-- **§28**: the Lagrangian of `(P)` is the §29 Lagrangian of the bifunction of `(P)`, taken with
the Euclidean pairing on `ℝᵐ`. -/
theorem lagrangian_ineqBifun :
    ConvexAnalysis.lagrangian (pairing m) P.ineqBifun = P.programLagrangian := by
  funext u x
  rw [lagrangian_apply]
  by_cases hx : x ∈ P.C
  · obtain ⟨c₀, h₀⟩ := P.exists_coe_f₀ hx
    choose c hc using P.exists_coe_f hx
    set cVec : Rn m := WithLp.toLp 2 c with hcVec
    have hcApp : ∀ i, cVec i = c i := fun _ => rfl
    have hcMem : ∀ w : Rn m, (∀ i : Fin m, (i : ℕ) < P.r → c i ≤ w i) →
        (∀ i : Fin m, P.r ≤ (i : ℕ) → c i = w i) →
        (∀ i : Fin m, (i : ℕ) < P.r → P.f i x ≤ ((w i : ℝ) : EReal)) ∧
          ∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i x = ((w i : ℝ) : EReal) :=
      fun w h1 h2 => ⟨fun i hi => by rw [hc i]; exact_mod_cast h1 i hi,
        fun i hi => by rw [hc i]; exact_mod_cast h2 i hi⟩
    by_cases hu : u ∈ P.multiplierCone
    · rw [P.programLagrangian_eq_lagrangeFn hx hu, P.lagrangeFn_eq_coe h₀ hc]
      refine le_antisymm ?_ (le_iInf fun w => ?_)
      · refine le_trans (iInf_le _ cVec) (le_of_eq ?_)
        rw [P.ineqBifun_of_mem (hcMem cVec (fun i _ => le_of_eq (hcApp i).symm)
          (fun i _ => (hcApp i).symm)), h₀, pairing_eq_sum, ← EReal.coe_add]
        congr 1
        rw [add_comm]
        exact congrArg (fun t => c₀ + t)
          (Finset.sum_congr rfl fun i _ => by rw [hcApp i]; ring)
      · by_cases hw : (∀ i : Fin m, (i : ℕ) < P.r → P.f i x ≤ ((w i : ℝ) : EReal)) ∧
            ∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i x = ((w i : ℝ) : EReal)
        · rw [P.ineqBifun_of_mem hw, h₀, pairing_eq_sum, ← EReal.coe_add,
            EReal.coe_le_coe_iff]
          have hle : ∑ i, u i * c i ≤ ∑ i, w i * u i := by
            refine Finset.sum_le_sum fun i _ => ?_
            rcases lt_or_ge (i : ℕ) P.r with hi | hi
            · have h1 : c i ≤ w i := by
                have := hw.1 i hi; rw [hc i] at this; exact_mod_cast this
              rw [mul_comm (w i)]
              exact mul_le_mul_of_nonneg_left h1 (hu i hi)
            · have h1 : c i = w i := by
                have := hw.2 i hi; rw [hc i] at this; exact_mod_cast this
              rw [h1, mul_comm]
          linarith
        · rw [P.ineqBifun_of_notMem hw, EReal.coe_add_top]
          exact le_top
    · rw [P.programLagrangian_eq_bot hx hu]
      obtain ⟨i₀, hi₀r, hi₀neg⟩ : ∃ i : Fin m, (i : ℕ) < P.r ∧ u i < 0 := by
        by_contra hcon
        exact hu fun i hi => by
          by_contra hlt
          exact hcon ⟨i, hi, not_le.1 hlt⟩
      have hkey : ∀ β : ℝ, ∃ w : Rn m,
          ((pairing m w u : ℝ) : EReal) + P.ineqBifun w x < ((β : ℝ) : EReal) := by
        intro β
        set S : ℝ := ∑ i, c i * u i with hS
        set K : ℝ := (β - S - c₀) / u i₀ with hK
        set t : ℝ := max 0 (K + 1) with hT
        have ht0 : 0 ≤ t := le_max_left _ _
        have htK : K < t := lt_of_lt_of_le (lt_add_one K) (le_max_right _ _)
        refine ⟨cVec + t • unitVec m i₀, ?_⟩
        have hwApp : ∀ i : Fin m, (cVec + t • unitVec m i₀ : Rn m) i
            = c i + t * unitVec m i₀ i := fun _ => rfl
        have hmem1 : ∀ i : Fin m, (i : ℕ) < P.r → c i ≤ (cVec + t • unitVec m i₀ : Rn m) i := by
          intro i _
          rw [hwApp i]
          have hnn : (0 : ℝ) ≤ t * unitVec m i₀ i := by
            rw [unitVec_apply]
            by_cases h : i = i₀ <;> simp [h, ht0]
          linarith
        have hmem2 : ∀ i : Fin m, P.r ≤ (i : ℕ) → c i = (cVec + t • unitVec m i₀ : Rn m) i := by
          intro i hi
          rw [hwApp i]
          have hne : i ≠ i₀ := fun hie => absurd (hie ▸ hi₀r) (by omega)
          rw [unitVec_apply]
          simp [hne]
        rw [P.ineqBifun_of_mem (hcMem _ hmem1 hmem2), h₀]
        have hp : pairing m (cVec + t • unitVec m i₀) u = S + t * u i₀ := by
          rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
            pairing_unitVec, pairing_eq_sum]
        rw [hp, ← EReal.coe_add, EReal.coe_lt_coe_iff]
        have hmul : t * u i₀ < K * u i₀ := mul_lt_mul_of_neg_right htK hi₀neg
        have hKu : K * u i₀ = β - S - c₀ := div_mul_cancel₀ _ (ne_of_lt hi₀neg)
        linarith
      refine iInf_eq_bot.2 fun b hb => ?_
      induction b using EReal.rec with
      | bot => exact absurd hb (lt_irrefl _)
      | coe β => obtain ⟨w, hw⟩ := hkey β; exact ⟨w, hw⟩
      | top =>
        obtain ⟨w, hw⟩ := hkey 0
        exact ⟨w, lt_trans hw (EReal.coe_lt_top 0)⟩
  · rw [P.programLagrangian_eq_top hx u]
    refine le_antisymm le_top (le_iInf fun w => ?_)
    rw [P.ineqBifun_eq_top_of_notMem_C hx w, EReal.coe_add_top]

/-- The §29 saddle-Lagrangian of `(P)`'s bifunction, read on `ℝᵐ × ℝⁿ`, is `L`. -/
theorem saddleLagrangian_ineqBifun :
    ConvexAnalysis.saddleLagrangian (pairing m) P.ineqBifun
      = fun q : Rn m × Rn n => P.programLagrangian q.1 q.2 := by
  funext q
  rw [saddleLagrangian_apply, show ConvexAnalysis.lagrangian (pairing m) P.ineqBifun q.1 q.2
    = P.programLagrangian q.1 q.2 from by rw [P.lagrangian_ineqBifun]]

/-- **§28**: "`L` is concave in `u*` for each `x`". Free from §29: the Lagrangian of a bifunction is
a concave conjugate in the price variable. -/
theorem concaveFn_programLagrangian (x : Rn n) :
    ConcaveFn fun u : Rn m => P.programLagrangian u x := by
  rw [show (fun u : Rn m => P.programLagrangian u x)
    = fun u : Rn m => ConvexAnalysis.lagrangian (pairing m) P.ineqBifun u x from
      funext fun u => by rw [P.lagrangian_ineqBifun]]
  exact concaveFn_lagrangian (pairing m) P.ineqBifun x

end OrdinaryConvexProgram

/-! ### Theorem 28.3: saddle-points of the Lagrangian and the Kuhn–Tucker conditions -/

/-- The indices `i` with `λᵢ ≠ 0`: Rockafellar's parenthesis "(Omit terms with `λᵢ = 0`.)" in
condition (c) of Theorem 28.3. The omission is not cosmetic — `∂fᵢ(x̄)` can be empty at a boundary
point of `dom fᵢ`, and then `0 · ∂fᵢ(x̄)` would be empty rather than `{0}`. -/
noncomputable def activeIndices {m : ℕ} (u : Rn m) : Finset (Fin m) :=
  @Finset.filter _ (fun i => u i ≠ 0) (Classical.decPred _) Finset.univ

theorem mem_activeIndices {m : ℕ} {u : Rn m} {i : Fin m} :
    i ∈ activeIndices u ↔ u i ≠ 0 := by
  simp [activeIndices]

namespace OrdinaryConvexProgram

/-- **§28**: `sup_{u*} L(u*, x) = f₀(x) + δ(x | C₀)`, the objective function of `(P)`, whatever `x`
is. -/
theorem iSup_programLagrangian (x : Rn n) :
    (⨆ u : Rn m, P.programLagrangian u x) = P.objective x := by
  by_cases hC : x ∈ P.C
  · by_cases hF : x ∈ P.feasibleSet
    · rw [P.objective_of_mem hF]
      refine le_antisymm (iSup_le fun u => ?_) ?_
      · by_cases hu : u ∈ P.multiplierCone
        · rw [P.programLagrangian_eq_lagrangeFn hC hu]
          exact P.lagrangeFn_le_f₀ hu hF
        · rw [P.programLagrangian_eq_bot hC hu]
          exact bot_le
      · refine le_trans (le_of_eq ?_) (le_iSup (fun u => P.programLagrangian u x) (0 : Rn m))
        rw [P.programLagrangian_eq_lagrangeFn hC P.zero_mem_multiplierCone, P.lagrangeFn_zero]
    · rw [P.objective_of_notMem hF]
      obtain ⟨c₀, h₀⟩ := P.exists_coe_f₀ hC
      choose c hc using P.exists_coe_f hC
      have hmemA : ∀ (i : Fin m) (t s : ℝ), 0 ≤ t → 0 ≤ s →
          (t * s) • unitVec m i ∈ P.multiplierCone := by
        intro i t s ht hs j _
        have hval : ((t * s) • unitVec m i : Rn m) j = (t * s) * unitVec m i j := rfl
        rw [hval, unitVec_apply]
        by_cases h : j = i <;> simp [h, mul_nonneg ht hs]
      have hmemB : ∀ i : Fin m, P.r ≤ (i : ℕ) → ∀ t s : ℝ,
          (t * s) • unitVec m i ∈ P.multiplierCone := by
        intro i hi t s j hj
        have hval : ((t * s) • unitVec m i : Rn m) j = (t * s) * unitVec m i j := rfl
        have hne : j ≠ i := fun hje => absurd (hje ▸ hj) (by omega)
        rw [hval, unitVec_apply]
        simp [hne]
      obtain ⟨i, s, hsmem, hspos⟩ : ∃ (i : Fin m) (s : ℝ),
          (∀ t : ℝ, 0 ≤ t → (t * s) • unitVec m i ∈ P.multiplierCone) ∧ 0 < s * c i := by
        by_contra hcon
        refine hF ⟨hC, fun i hi => ?_, fun i hi => ?_⟩
        · rw [hc i]
          have hle : c i ≤ 0 := by
            by_contra hpos
            exact hcon ⟨i, 1, fun t ht => hmemA i t 1 ht zero_le_one,
              by rw [one_mul]; exact not_le.1 hpos⟩
          exact_mod_cast hle
        · rw [hc i]
          have heq : c i = 0 := by
            by_contra hne
            rcases lt_or_gt_of_ne hne with hneg | hpos
            · exact hcon ⟨i, -1, fun t _ => hmemB i hi t (-1), by nlinarith⟩
            · exact hcon ⟨i, 1, fun t _ => hmemB i hi t 1, by nlinarith⟩
          rw [heq]
          norm_num
      refine iSup_eq_top.2 fun b hb => ?_
      induction b using EReal.rec with
      | bot =>
        refine ⟨0, ?_⟩
        rw [P.programLagrangian_eq_lagrangeFn hC P.zero_mem_multiplierCone, P.lagrangeFn_zero, h₀]
        exact EReal.bot_lt_coe c₀
      | coe β =>
        set K : ℝ := (β - c₀) / (s * c i) with hK
        set t : ℝ := max 0 (K + 1) with hT
        refine ⟨(t * s) • unitVec m i, ?_⟩
        rw [P.programLagrangian_eq_lagrangeFn hC (hsmem t (le_max_left _ _)),
          P.lagrangeFn_eq_coe h₀ hc, EReal.coe_lt_coe_iff]
        have hsum : (∑ j, ((t * s) • unitVec m i : Rn m) j * c j) = (t * s) * c i := by
          have h1 : (∑ j, ((t * s) • unitVec m i : Rn m) j * c j)
              = ((t * s) • unitVec m i : Rn m) i * c i := by
            refine Finset.sum_eq_single i (fun j _ hj => ?_)
              (fun hj => absurd (Finset.mem_univ i) hj)
            have hval : ((t * s) • unitVec m i : Rn m) j = (t * s) * unitVec m i j := rfl
            rw [hval, unitVec_apply]
            simp [hj]
          rw [h1]
          have hval : ((t * s) • unitVec m i : Rn m) i = (t * s) * unitVec m i i := rfl
          rw [hval, unitVec_apply]
          simp
        rw [hsum]
        have hKu : K * (s * c i) = β - c₀ := div_mul_cancel₀ _ (ne_of_gt hspos)
        have htK : K + 1 ≤ t := le_max_right _ _
        have hmono : (K + 1) * (s * c i) ≤ t * (s * c i) :=
          mul_le_mul_of_nonneg_right htK (le_of_lt hspos)
        nlinarith
      | top => exact absurd hb (lt_irrefl _)
  · rw [P.objective_of_notMem fun hc => hC hc.1]
    refine le_antisymm le_top (le_trans (le_of_eq (P.programLagrangian_eq_top hC 0).symm)
      (le_iSup (fun u => P.programLagrangian u x) (0 : Rn m)))

/-- **§28**, the case `ū* ∈ E_r`: the infimum of `L(ū*, ·)` is the infimum of `h`. -/
theorem iInf_programLagrangian_of_mem {u : Rn m} (hu : u ∈ P.multiplierCone) :
    (⨅ x, P.programLagrangian u x) = ⨅ x, P.lagrangeFn u x := by
  refine iInf_congr fun x => ?_
  by_cases hC : x ∈ P.C
  · exact P.programLagrangian_eq_lagrangeFn hC hu
  · rw [P.programLagrangian_eq_top hC u, P.lagrangeFn_eq_top_of_notMem_C hu hC]

/-- **§28**, the case `ū* ∉ E_r`: the infimum of `L(ū*, ·)` is `-∞`. -/
theorem iInf_programLagrangian_of_notMem {u : Rn m} (hu : u ∉ P.multiplierCone) :
    (⨅ x, P.programLagrangian u x) = ⊥ := by
  obtain ⟨x₀, hx₀⟩ := P.nonempty_C
  exact le_bot_iff.1 ((iInf_le (fun x => P.programLagrangian u x) x₀).trans
    (le_of_eq (P.programLagrangian_eq_bot hx₀ hu)))

/-- `inf h` is never `+∞`: `h` is finite at every point of the non-empty set `C`. -/
theorem iInf_lagrangeFn_ne_top (u : Rn m) : (⨅ z, P.lagrangeFn u z) ≠ ⊤ := by
  obtain ⟨x₀, hx₀⟩ := P.nonempty_C
  obtain ⟨c, hcc⟩ := P.exists_coe_lagrangeFn u hx₀
  refine ne_of_lt (lt_of_le_of_lt (iInf_le (fun z => P.lagrangeFn u z) x₀) ?_)
  rw [hcc]
  exact EReal.coe_lt_top c

/-- **§28**, condition (d): `(ū*, x̄)` is a saddle-point of `L` exactly when `ū* ∈ E_r`, `x̄` is a
feasible solution, and `inf h = f₀(x̄)`. -/
theorem isSaddlePoint_programLagrangian_iff {u : Rn m} {x : Rn n} :
    IsSaddlePoint P.saddleFn (u, x) ↔
      u ∈ P.multiplierCone ∧ x ∈ P.feasibleSet ∧ (⨅ z, P.lagrangeFn u z) = P.f₀ x := by
  rw [isSaddlePoint_iff_iSup_eq_iInf]
  have hsup : (⨆ u' : Rn m, P.programLagrangian u' x) = P.objective x := P.iSup_programLagrangian x
  constructor
  · intro h
    have h' : P.objective x = ⨅ z, P.programLagrangian u z := by rw [← hsup]; exact h
    by_cases hu : u ∈ P.multiplierCone
    · rw [P.iInf_programLagrangian_of_mem hu] at h'
      have hne : P.objective x ≠ ⊤ := by rw [h']; exact P.iInf_lagrangeFn_ne_top u
      have hF : x ∈ P.feasibleSet := by
        by_contra hc
        exact hne (P.objective_of_notMem hc)
      exact ⟨hu, hF, by rw [← h', P.objective_of_mem hF]⟩
    · rw [P.iInf_programLagrangian_of_notMem hu] at h'
      exact absurd h' (P.objective_ne_bot x)
  · rintro ⟨hu, hF, heq⟩
    change (⨆ u' : Rn m, P.programLagrangian u' x) = ⨅ z, P.programLagrangian u z
    rw [hsup, P.iInf_programLagrangian_of_mem hu, heq, P.objective_of_mem hF]

/-- **Theorem 28.3**. In order that `ū*` be a Kuhn–Tucker vector for `(P)` and `x̄` be an optimal
solution to `(P)`, it is necessary and sufficient that `(ū*, x̄)` be a saddle-point of the
Lagrangian `L` of `(P)`. -/
theorem theorem_28_3 {u : Rn m} {x : Rn n} :
    (P.IsKuhnTuckerVector u ∧ x ∈ P.optimalSolutions) ↔
      IsSaddlePoint P.saddleFn (u, x) := by
  rw [P.isSaddlePoint_programLagrangian_iff]
  constructor
  · rintro ⟨hkt, hopt⟩
    obtain ⟨hF, hval⟩ := (P.mem_optimalSolutions_iff_of_ne_top hkt.optimalValue_ne_top).1 hopt
    exact ⟨hkt.nonneg, hF, by rw [hkt.iInf_eq, hval]⟩
  · rintro ⟨hu, hF, heq⟩
    have hle : (⨅ z, P.lagrangeFn u z) ≤ P.optimalValue := P.iInf_lagrangeFn_le_optimalValue hu
    have hge : P.optimalValue ≤ P.f₀ x := P.optimalValue_le hF
    have h1 : (⨅ z, P.lagrangeFn u z) = P.optimalValue :=
      le_antisymm hle (by rw [heq]; exact hge)
    have hkt : P.IsKuhnTuckerVector u :=
      { nonneg := hu
        ne_bot := by rw [heq]; exact P.proper_f₀.ne_bot x
        ne_top := P.iInf_lagrangeFn_ne_top u
        iInf_eq := h1 }
    refine ⟨hkt, P.mem_optimalSolutions_iff.2 ?_⟩
    rw [P.objective_of_mem hF, ← heq, h1]

/-! #### The Kuhn–Tucker conditions (a), (b), (c) -/

/-- Every summand `λᵢ fᵢ` of `h` is admissible in the sense of the backbone's
`IsLagrangeSummand`, at any relative interior point of `C`: the inequality constraints are
convex, proper and carry non-negative multipliers, and Rockafellar's convention (b) puts `ri C`
inside `ri (dom fᵢ)`; the equality constraints are affine, their linear part a vector of `ℝⁿ` by
Fréchet–Riesz. -/
theorem isLagrangeSummand {u : Rn m} (hu : u ∈ P.multiplierCone) {x₀ : Rn n}
    (hx₀ : x₀ ∈ ri P.C) (i : Fin m) : IsLagrangeSummand (pairing n) x₀ (u i) (P.f i) := by
  rcases lt_or_ge (i : ℕ) P.r with hi | hi
  · exact Or.inl ⟨hu i hi, P.convexFn_f i hi, P.proper_f i hi, P.relint_subset i hi hx₀⟩
  · obtain ⟨a, ha⟩ := P.exists_affine i hi
    obtain ⟨b, hb⟩ := exists_linFn (LinearMap.toContinuousLinearMap a.linear)
    exact Or.inr ⟨a, b, ha, fun w => by rw [← linFn_apply b w, hb]; rfl⟩

/-- **§28**, the subdifferential of `h` decomposed by Theorem 23.8. The multiplier terms with
`λᵢ = 0` contribute `{0}` and are omitted, exactly as the book's parenthesis in condition (c) says.
This is the backbone's `subdifferential_add_sum_coe_mul` for the family `f₁, …, f_m`. -/
theorem subdifferential_lagrangeFn {u : Rn m} (hu : u ∈ P.multiplierCone) (x : Rn n) :
    subdifferential (pairing n) (P.lagrangeFn u) x
      = subdifferential (pairing n) P.f₀ x
        + ∑ i ∈ activeIndices u, u i • subdifferential (pairing n) (P.f i) x := by
  obtain ⟨x₀, hx₀⟩ := P.relint_C_nonempty
  have hsep : Function.Injective (pairing n).flip :=
    LinearMap.ker_eq_bot.1
      (LinearMap.separatingRight_iff_flip_ker_eq_bot.1 (separatingRight_pairing n))
  have hactive : activeIndices u = Finset.univ.filter fun i => u i ≠ 0 :=
    Finset.ext fun i => by simp [activeIndices]
  have hfn : P.lagrangeFn u = fun y => P.f₀ y + ∑ i, (u i : EReal) * P.f i y :=
    funext fun y => P.lagrangeFn_apply u y
  rw [hactive, hfn]
  exact subdifferential_add_sum_coe_mul hsep P.convexFn_f₀ P.proper_f₀ (P.dom_f₀ ▸ hx₀)
    (fun i _ => P.isLagrangeSummand hu hx₀ i) x

/-- **Theorem 28.3**, second half: the saddle-point condition holds if
and only if `x̄` and the multipliers `λᵢ` satisfy the **Kuhn–Tucker conditions**

* (a) `λᵢ ≥ 0`, `fᵢ(x̄) ≤ 0` and `λᵢfᵢ(x̄) = 0` for `i = 1, …, r`;
* (b) `fᵢ(x̄) = 0` for `i = r + 1, …, m`;
* (c) `0 ∈ ∂f₀(x̄) + λ₁∂f₁(x̄) + ⋯ + λ_m∂f_m(x̄)` (terms with `λᵢ = 0` omitted).

`x̄ ∈ C` is not a separate clause: it follows from (c), because `∂f₀(x̄)` is non-empty there and
`dom f₀ = C`. -/
theorem theorem_28_3_kuhnTucker {u : Rn m} {x : Rn n} :
    (P.IsKuhnTuckerVector u ∧ x ∈ P.optimalSolutions) ↔
      ((∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i ∧ P.f i x ≤ 0 ∧ (u i : EReal) * P.f i x = 0) ∧
        (∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i x = 0) ∧
        (0 : Rn n) ∈ subdifferential (pairing n) P.f₀ x
          + ∑ i ∈ activeIndices u, u i • subdifferential (pairing n) (P.f i) x) := by
  rw [P.theorem_28_3, P.isSaddlePoint_programLagrangian_iff]
  constructor
  · rintro ⟨hu, hF, heq⟩
    obtain ⟨c₀, h₀⟩ := P.exists_coe_f₀ hF.1
    choose c hc using P.exists_coe_f hF.1
    -- `h(x̄) = f₀(x̄)`, so every multiplier term vanishes
    have hhx : P.lagrangeFn u x = P.f₀ x :=
      le_antisymm (P.lagrangeFn_le_f₀ hu hF)
        (by rw [← heq]; exact iInf_le (fun z => P.lagrangeFn u z) x)
    have hsum : ∑ i, u i * c i = 0 := by
      have h1 : ((c₀ + ∑ i, u i * c i : ℝ) : EReal) = ((c₀ : ℝ) : EReal) := by
        rw [← P.lagrangeFn_eq_coe h₀ hc, hhx, h₀]
      have h2 : c₀ + ∑ i, u i * c i = c₀ := by exact_mod_cast h1
      linarith
    have hnonpos : ∀ i ∈ (Finset.univ : Finset (Fin m)), u i * c i ≤ 0 := by
      intro i _
      rcases lt_or_ge (i : ℕ) P.r with hi | hi
      · have h1 : c i ≤ 0 := by have := hF.2.1 i hi; rw [hc i] at this; exact_mod_cast this
        exact mul_nonpos_of_nonneg_of_nonpos (hu i hi) h1
      · have h1 : c i = 0 := by have := hF.2.2 i hi; rw [hc i] at this; exact_mod_cast this
        rw [h1, mul_zero]
    have hzero : ∀ i : Fin m, u i * c i = 0 :=
      fun i => (Finset.sum_eq_zero_iff_of_nonpos hnonpos).1 hsum i (Finset.mem_univ i)
    refine ⟨fun i hi => ⟨hu i hi, hF.2.1 i hi, ?_⟩, fun i hi => hF.2.2 i hi, ?_⟩
    · rw [hc i, ← EReal.coe_mul, hzero i]
      norm_num
    · rw [← P.subdifferential_lagrangeFn hu x,
        ← mem_argmin_iff_zero_mem_subdifferential (pairing n) (P.lagrangeFn u) x]
      intro z
      rw [hhx, ← heq]
      exact iInf_le (fun w => P.lagrangeFn u w) z
  · rintro ⟨ha, hb, hcond⟩
    -- `x̄ ∈ C`, because `∂f₀(x̄)` is non-empty
    obtain ⟨v₀, hv₀, -, -, -⟩ := Set.mem_add.1 hcond
    have hxC : x ∈ P.C := by
      rw [← P.dom_f₀]
      exact mem_dom_of_mem_subdifferential P.proper_f₀ hv₀
    have hu : u ∈ P.multiplierCone := fun i hi => (ha i hi).1
    have hF : x ∈ P.feasibleSet := ⟨hxC, fun i hi => (ha i hi).2.1, hb⟩
    have hhx : P.lagrangeFn u x = P.f₀ x := by
      refine P.lagrangeFn_eq_f₀ fun i => ?_
      rcases lt_or_ge (i : ℕ) P.r with hi | hi
      · exact (ha i hi).2.2
      · rw [hb i hi, mul_zero]
    have hmin : x ∈ argmin (P.lagrangeFn u) := by
      rw [mem_argmin_iff_zero_mem_subdifferential (pairing n) (P.lagrangeFn u) x,
        P.subdifferential_lagrangeFn hu x]
      exact hcond
    exact ⟨hu, hF, by rw [← hhx]; exact iInf_eq_of_mem_argmin hmin⟩

/-- **Corollary 28.3.1**, the Kuhn–Tucker Theorem. For a program with at least one Kuhn–Tucker
vector, `x̄` is an optimal solution if and only if some `ū*` makes `(ū*, x̄)` a saddle-point of `L`.
**No proof is printed in the book.** The book's hypothesis is "satisfying the hypothesis of Theorem
28.2"; only its *conclusion* is used, so that is the hypothesis carried here. -/
theorem corollary_28_3_1 (hkt : ∃ u : Rn m, P.IsKuhnTuckerVector u) {x : Rn n} :
    x ∈ P.optimalSolutions ↔
      ∃ u : Rn m, IsSaddlePoint P.saddleFn (u, x) := by
  constructor
  · rintro hx
    obtain ⟨u, hu⟩ := hkt
    exact ⟨u, (P.theorem_28_3).1 ⟨hu, hx⟩⟩
  · rintro ⟨u, hs⟩
    exact ((P.theorem_28_3).2 hs).2

/-- **Corollary 28.3.1**, second form: optimality is equivalent to the existence of Lagrange
multiplier values satisfying the Kuhn–Tucker conditions. -/
theorem corollary_28_3_1_kuhnTucker (hkt : ∃ u : Rn m, P.IsKuhnTuckerVector u) {x : Rn n} :
    x ∈ P.optimalSolutions ↔
      ∃ u : Rn m,
        (∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i ∧ P.f i x ≤ 0 ∧ (u i : EReal) * P.f i x = 0) ∧
        (∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i x = 0) ∧
        (0 : Rn n) ∈ subdifferential (pairing n) P.f₀ x
          + ∑ i ∈ activeIndices u, u i • subdifferential (pairing n) (P.f i) x := by
  constructor
  · intro hx
    obtain ⟨u, hu⟩ := hkt
    exact ⟨u, (P.theorem_28_3_kuhnTucker).1 ⟨hu, hx⟩⟩
  · rintro ⟨u, hs⟩
    exact ((P.theorem_28_3_kuhnTucker).2 hs).2

end OrdinaryConvexProgram

/-! ### Theorem 28.4: the optimal value as a saddle-value -/

namespace OrdinaryConvexProgram

/-- **§28**: `g(u*) = inf_x L(u*, x)`, the concave function whose maximisation over `ℝᵐ` is dual to
`(P)`. -/
noncomputable def dualFn : Rn m → EReal := fun u => ⨅ x, P.programLagrangian u x

theorem dualFn_apply (u : Rn m) : P.dualFn u = ⨅ x, P.programLagrangian u x := rfl

/-- **§28**: `inf_x sup_{u*} L(u*, x)` is the optimal value in `(P)`. -/
theorem minimax_saddleFn : minimax P.saddleFn = P.optimalValue := by
  rw [minimax_apply]
  refine iInf_congr fun x => ?_
  exact P.iSup_programLagrangian x

theorem maximin_saddleFn_eq_iSup_dualFn : maximin P.saddleFn = ⨆ u, P.dualFn u := rfl

/-- Weak duality: `sup inf ≤ inf sup = α`. -/
theorem maximin_saddleFn_le : maximin P.saddleFn ≤ P.optimalValue :=
  le_of_le_of_eq (maximin_le_minimax P.saddleFn) P.minimax_saddleFn

/-- **Theorem 28.4**, first sentence: at a Kuhn–Tucker vector and an optimal solution the
saddle-value `L(ū*, x̄)` is the optimal value in `(P)`. -/
theorem theorem_28_4_saddleValue {u : Rn m} {x : Rn n} (hu : P.IsKuhnTuckerVector u)
    (hx : x ∈ P.optimalSolutions) : P.programLagrangian u x = P.optimalValue := by
  have hs := (P.theorem_28_3).1 ⟨hu, hx⟩
  have h1 : (⨅ x' : Rn n, P.programLagrangian u x') = P.programLagrangian u x := hs.iInf_eq
  rw [← h1, P.iInf_programLagrangian_of_mem hu.nonneg, hu.iInf_eq]

/-- **Theorem 28.4**. `ū*` is a Kuhn–Tucker vector for `(P)` if and only if
`-∞ < inf_x L(ū*, x) = sup_{u*} inf_x L(u*, x) = inf_x sup_{u*} L(u*, x)`, and the common extremum
value is then the optimal value in `(P)`. -/
theorem theorem_28_4 {u : Rn m} :
    P.IsKuhnTuckerVector u ↔
      (⊥ < ⨅ x, P.programLagrangian u x) ∧
        (⨅ x, P.programLagrangian u x) = maximin P.saddleFn ∧
        maximin P.saddleFn = minimax P.saddleFn := by
  constructor
  · intro hu
    have hi : (⨅ x, P.programLagrangian u x) = P.optimalValue := by
      rw [P.iInf_programLagrangian_of_mem hu.nonneg, hu.iInf_eq]
    have hmax : maximin P.saddleFn = P.optimalValue := by
      refine le_antisymm P.maximin_saddleFn_le ?_
      rw [← hi]
      exact iInf_slice_le_maximin P.saddleFn u
    refine ⟨?_, by rw [hi, hmax], by rw [hmax, P.minimax_saddleFn]⟩
    rw [hi]
    exact lt_of_le_of_ne bot_le (Ne.symm hu.optimalValue_ne_bot)
  · rintro ⟨hbot, h1, h2⟩
    have hu : u ∈ P.multiplierCone := by
      by_contra hc
      rw [P.iInf_programLagrangian_of_notMem hc] at hbot
      exact absurd hbot (lt_irrefl _)
    have hval : (⨅ x, P.programLagrangian u x) = P.optimalValue := by
      rw [h1, h2, P.minimax_saddleFn]
    rw [P.iInf_programLagrangian_of_mem hu] at hval hbot
    exact ⟨hu, hbot.ne', P.iInf_lagrangeFn_ne_top u, hval⟩

/-- The common value in Theorem 28.4 is the optimal value in `(P)`. -/
theorem theorem_28_4_value {u : Rn m} (hu : P.IsKuhnTuckerVector u) :
    maximin P.saddleFn = P.optimalValue ∧ minimax P.saddleFn = P.optimalValue := by
  obtain ⟨-, h1, h2⟩ := (P.theorem_28_4).1 hu
  have hi : (⨅ x, P.programLagrangian u x) = P.optimalValue := by
    rw [P.iInf_programLagrangian_of_mem hu.nonneg, hu.iInf_eq]
  exact ⟨by rw [← h1, hi], P.minimax_saddleFn⟩

/-- `g` is the concave conjugate of `-p`, which is Rockafellar's remark in the form the backbone
states it. -/
theorem dualFn_eq_concaveConj :
    P.dualFn = concaveConj (pairing m) fun w => -(P.perturbFn w) := by
  funext u
  have h : (fun x => P.programLagrangian u x)
      = fun x => ConvexAnalysis.lagrangian (pairing m) P.ineqBifun u x :=
    funext fun x => by rw [P.lagrangian_ineqBifun]
  rw [dualFn_apply, h, iInf_lagrangian, concaveConj_apply]
  refine iInf_congr fun w => ?_
  rw [sub_eq_add_neg, neg_neg]
  rfl

/-- **§28**: "The concavity of `g` … is immediate." Here it is immediate from §29 instead: `g` is a
concave conjugate. -/
theorem concaveFn_dualFn : ConcaveFn P.dualFn := by
  rw [P.dualFn_eq_concaveConj]
  exact concaveFn_concaveConj (pairing m) _

/-- **§28**: `g(u*) = -p*(-u*)`, where `p` is the perturbation function of `(P)`. -/
theorem dualFn_eq_neg_conj_perturbFn (u : Rn m) :
    P.dualFn u = -(conj (pairing m) P.perturbFn (-u)) := by
  rw [P.dualFn_eq_concaveConj, concaveConj_eq_neg_conj_neg]
  simp only [neg_neg]

/-- **Corollary 28.4.1**. For a program with at least one Kuhn–Tucker vector, the Kuhn–Tucker
vectors are precisely the points where the concave function `g(u*) = inf_x L(u*, x)` attains its
supremum over `ℝᵐ`. **No proof is printed in the book**: weak duality gives `g ≤ α` everywhere, the
assumed Kuhn–Tucker vector gives a point where `g = α`, and `g(ū*) = α` with `α` finite is the
definition of a Kuhn–Tucker vector. -/
theorem corollary_28_4_1 (hkt : ∃ u : Rn m, P.IsKuhnTuckerVector u) {u : Rn m} :
    P.IsKuhnTuckerVector u ↔ u ∈ argmax P.dualFn := by
  have hweak : ∀ v : Rn m, P.dualFn v ≤ P.optimalValue := by
    intro v
    by_cases hv : v ∈ P.multiplierCone
    · rw [dualFn_apply, P.iInf_programLagrangian_of_mem hv]
      exact P.iInf_lagrangeFn_le_optimalValue hv
    · rw [dualFn_apply, P.iInf_programLagrangian_of_notMem hv]
      exact bot_le
  constructor
  · intro hu v
    have hgu : P.dualFn u = P.optimalValue := by
      rw [dualFn_apply, P.iInf_programLagrangian_of_mem hu.nonneg, hu.iInf_eq]
    rw [hgu]
    exact hweak v
  · intro hmax
    obtain ⟨u₀, hu₀⟩ := hkt
    have hgu₀ : P.dualFn u₀ = P.optimalValue := by
      rw [dualFn_apply, P.iInf_programLagrangian_of_mem hu₀.nonneg, hu₀.iInf_eq]
    have heq : P.dualFn u = P.optimalValue :=
      le_antisymm (hweak u) (by rw [← hgu₀]; exact hmax u₀)
    have hu : u ∈ P.multiplierCone := by
      by_contra hc
      rw [dualFn_apply, P.iInf_programLagrangian_of_notMem hc] at heq
      have hnb := hu₀.optimalValue_ne_bot
      exact hnb heq.symm
    rw [dualFn_apply, P.iInf_programLagrangian_of_mem hu] at heq
    have hnb : (⨅ z, P.lagrangeFn u z) ≠ ⊥ := by
      rw [heq]; exact hu₀.optimalValue_ne_bot
    exact ⟨hu, hnb, P.iInf_lagrangeFn_ne_top u, heq⟩

end OrdinaryConvexProgram

/-! ### The decomposition principle

Suppose the coordinates of `ℝⁿ` split as `x = (x₁, …, x_s)` with `x_k ∈ ℝ^{n_k}` and every `fᵢ`
separable in that splitting. Once a Kuhn–Tucker vector has reduced `(P)` to minimising
`h = f₀ + λ₁f₁ + ⋯ + λ_m f_m` over `C` (Theorem 28.1), `h` is separable too, and the problem splits
into the `s` independent problems "minimise `h_k` over `C^k`", `C^k = dom h_k`.

The splitting is hypothesised as a linear equivalence `e` from `ℝ^{n₁} × ⋯ × ℝ^{n_s}` to `ℝⁿ`:
linearity is what carries `n₁ + ⋯ + n_s = n`, since a bare bijection between these two types exists
whatever the `n_k` are. Separability of `h` is hypothesised in the form the book asserts it rather
than derived from separability of each `fᵢ`, because distributing `λᵢ · ∑ₖ fᵢₖ(xₖ)` over the sum
would need `EReal` to be a semiring. -/

namespace OrdinaryConvexProgram

variable {s : ℕ} {nk : Fin s → ℕ}

/-- The effective domain of the Lagrangian `h = f₀ + λ₁f₁ + ⋯ + λ_m f_m` is `C`.

Off `C` it is `+∞` because `f₀` is and the multipliers of the inequality constraints are
non-negative; on `C` it is a real number, because Rockafellar's convention (b) makes every `fᵢ`
finite there. This is the sense in which "minimise `h` over `C`" is an unconstrained problem. -/
theorem dom_lagrangeFn {u : Rn m} (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i) :
    dom (P.lagrangeFn u) = P.C := by
  ext x
  refine ⟨fun hx => ?_, fun hx => mem_dom.2 ?_⟩
  · by_contra hc
    exact absurd (P.lagrangeFn_eq_top_of_notMem_C hu hc) (mem_dom.1 hx).ne
  · obtain ⟨c₀, hc₀⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (P.proper_f₀.ne_bot x)
      (P.mem_C_iff.1 hx)
    choose c hc using fun i => P.exists_coe_f hx i
    rw [P.lagrangeFn_eq_coe hc₀ hc]
    exact EReal.coe_lt_top _

/-- **§28**: in the coordinates `x = (x₁, …, x_s)` the set `C` is the
product of the sets `C^k = dom h_k`.

This is `dom_sepSum` read through `e`, on the strength of `dom_lagrangeFn`. Properness of the
`h_k` is not needed — only that none of them takes the value `−∞`, which is automatic for the
`h_k` the principle produces. -/
theorem decomposition_C (e : (∀ k, Rn (nk k)) ≃ₗ[ℝ] Rn n) {u : Rn m}
    (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i) {h : ∀ k, Rn (nk k) → EReal}
    (hb : ∀ k (z : Rn (nk k)), h k z ≠ ⊥)
    (hsep : ∀ x, P.lagrangeFn u (e x) = ∑ k, h k (x k)) :
    ⇑e ⁻¹' P.C = univ.pi fun k => dom (h k) := by
  rw [← P.dom_lagrangeFn hu, ← dom_sepSum hb]
  exact congrArg dom (funext hsep)

/-- **§28**, the decomposition principle itself: minimising `h` over `C`
is the `s` independent problems "minimise `h_k` over `C^k`".

With `theorem_28_1` this is the assertion about `(P)`: the optimal solutions of `(P)` are the
points of `argmin h` that satisfy complementary slackness, and `argmin h` is now a product. Each
factor is a problem in `ℝ^{n_k}`, while by Corollary 28.4.1 finding `u` is a problem in `ℝᵐ` —
which is the reduction in dimensionality the passage is about. -/
theorem decomposition_argmin_lagrangeFn (e : (∀ k, Rn (nk k)) ≃ₗ[ℝ] Rn n) {u : Rn m}
    {h : ∀ k, Rn (nk k) → EReal} (hp : ∀ k, Proper (h k))
    (hsep : ∀ x, P.lagrangeFn u (e x) = ∑ k, h k (x k)) :
    ⇑e ⁻¹' argmin (P.lagrangeFn u) = univ.pi fun k => argmin (h k) := by
  rw [← argmin_comp_of_surjective (g := P.lagrangeFn u) e.surjective, ← argmin_sepSum hp]
  exact congrArg argmin (funext hsep)

end OrdinaryConvexProgram

/-! ### Two programs with no Kuhn-Tucker vector

Two unnumbered counterexamples of §28, both justifying the constraint qualification in
Theorem 28.2. The first has a unique optimal solution, a finite optimal value and no Kuhn–Tucker
vector; the second has only *linear* constraints, so it satisfies every hypothesis of
Corollary 28.2.2 except the feasible point in `ri C`, and it too has none. -/

/-- The `j`-th coordinate of `ℝⁿ`, as an affine function. -/
noncomputable def coordAffine (n : ℕ) (j : Fin n) : Rn n →ᵃ[ℝ] ℝ :=
  LinearMap.toAffineMap ⟨⟨fun x => x j, fun _ _ => rfl⟩, fun _ _ => rfl⟩

@[simp] theorem coordAffine_apply (n : ℕ) (j : Fin n) (x : Rn n) : coordAffine n j x = x j := rfl

private theorem fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  rcases i with ⟨_ | _ | k, hk⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · omega

/-- `ξ₁² - ξ₂` is convex on `ℝ²`. -/
private theorem convexOn_sqSub : ConvexOn ℝ Set.univ fun x : Rn 2 => x 0 ^ 2 - x 1 := by
  refine ⟨convex_univ, fun u _ v _ a b ha hb _ => ?_⟩
  have h0 : (a • u + b • v) 0 = a * u 0 + b * v 0 := rfl
  have h1 : (a • u + b • v) 1 = a * u 1 + b * v 1 := rfl
  simp only [h0, h1, smul_eq_mul]
  nlinarith [sq_nonneg (u 0 - v 0), mul_nonneg ha hb]

/-! #### A program with a unique optimal solution and no Kuhn–Tucker vector -/

/-- The constraint `f₁(ξ₁, ξ₂) = ξ₂` of the counterexample. -/
noncomputable def ex1Constraint₁ : Rn 2 → EReal := fun x => ((x 1 : ℝ) : EReal)

/-- The constraint `f₂(ξ₁, ξ₂) = ξ₁² - ξ₂` of the counterexample. -/
noncomputable def ex1Constraint₂ : Rn 2 → EReal := fun x => ((x 0 ^ 2 - x 1 : ℝ) : EReal)

private theorem ex1_dom_f (i : Fin 2) :
    dom (![ex1Constraint₁, ex1Constraint₂] i) = Set.univ := by
  rcases fin_two_cases i with rfl | rfl
  · exact dom_coe (fun x : Rn 2 => x 1)
  · exact dom_coe (fun x : Rn 2 => x 0 ^ 2 - x 1)

/-- **§28**, first counterexample: the program with `C = ℝ²`, `f₀(ξ₁, ξ₂) = ξ₁`, `f₁(ξ₁, ξ₂) = ξ₂`,
`f₂(ξ₁, ξ₂) = ξ₁² - ξ₂` and `r = 2`. Its only feasible solution, hence its unique optimal solution,
is the origin and its optimal value is `0`; but it has **no Kuhn–Tucker vector**
(`ex1_not_exists_isKuhnTuckerVector`), because no point has `f₁ ≤ 0` and `f₂ < 0`. -/
noncomputable def ex1 : OrdinaryConvexProgram 2 2 where
  C := Set.univ
  f₀ := fun x => ((x 0 : ℝ) : EReal)
  f := ![ex1Constraint₁, ex1Constraint₂]
  r := 2
  r_le := le_refl 2
  convexFn_f₀ :=
    (closedProperConvexFn_coe_affineMap
      (coordAffine 2 0).continuous_of_finiteDimensional).convex
  proper_f₀ := proper_coe _
  dom_f₀ := dom_coe _
  convexFn_f := by
    intro i _
    rcases fin_two_cases i with rfl | rfl
    · exact (closedProperConvexFn_coe_affineMap
        (coordAffine 2 1).continuous_of_finiteDimensional).convex
    · exact convexOn_sqSub.convexFn_coe
  proper_f := by
    intro i _
    rcases fin_two_cases i with rfl | rfl
    · exact proper_coe (fun x : Rn 2 => x 1)
    · exact proper_coe (fun x : Rn 2 => x 0 ^ 2 - x 1)
  subset_dom_f := fun i _ => (ex1_dom_f i).ge
  relint_subset := fun i _ => by rw [ex1_dom_f i]
  exists_affine := by intro i hi; exact absurd i.isLt (by omega)

@[simp] theorem ex1_C : ex1.C = Set.univ := rfl

@[simp] theorem ex1_r : ex1.r = 2 := rfl

@[simp] theorem ex1_f₀ (x : Rn 2) : ex1.f₀ x = ((x 0 : ℝ) : EReal) := rfl

@[simp] theorem ex1_f_zero (x : Rn 2) : ex1.f 0 x = ((x 1 : ℝ) : EReal) := rfl

@[simp] theorem ex1_f_one (x : Rn 2) : ex1.f 1 x = ((x 0 ^ 2 - x 1 : ℝ) : EReal) := rfl

/-- The only point satisfying `ξ₂ ≤ 0` and `ξ₁² - ξ₂ ≤ 0` is the origin. -/
theorem ex1_feasibleSet : ex1.feasibleSet = {0} := by
  ext x
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, h1, -⟩
    have hA : x 1 ≤ 0 := by
      have h := h1 0 (by norm_num)
      rw [ex1_f_zero] at h
      exact EReal.coe_nonpos.1 h
    have hB : x 0 ^ 2 - x 1 ≤ 0 := by
      have h := h1 1 (by norm_num)
      rw [ex1_f_one] at h
      exact EReal.coe_nonpos.1 h
    have h10 : x 1 = 0 := by nlinarith [sq_nonneg (x 0)]
    have h00 : x 0 = 0 := by nlinarith [sq_nonneg (x 0)]
    ext i
    rcases fin_two_cases i with rfl | rfl
    · simpa using h00
    · simpa using h10
  · rintro rfl
    refine ⟨trivial, fun i _ => ?_, fun i hi => ?_⟩
    · rcases fin_two_cases i with rfl | rfl
      · rw [ex1_f_zero]; exact EReal.coe_nonpos.2 (le_of_eq rfl)
      · rw [ex1_f_one]; exact EReal.coe_nonpos.2 (by norm_num)
    · rw [ex1_r] at hi; exact absurd i.isLt (by omega)

theorem ex1_optimalValue : ex1.optimalValue = 0 := by
  rw [ex1.optimalValue_eq_biInf, ex1_feasibleSet]
  have h0 : (0 : Rn 2) ∈ ({0} : Set (Rn 2)) := rfl
  refine le_antisymm ?_ (le_iInf₂ fun x hx => ?_)
  · refine le_trans (iInf_le _ (0 : Rn 2)) (le_trans (iInf_le _ h0) ?_)
    rw [ex1_f₀]; norm_num
  · rw [Set.mem_singleton_iff] at hx
    rw [hx, ex1_f₀]
    norm_num

/-- **§28**: the program has `(0, 0)` as its unique optimal solution. -/
theorem ex1_optimalSolutions : ex1.optimalSolutions = {0} := by
  have hne : ex1.optimalValue ≠ ⊤ := by rw [ex1_optimalValue]; exact (EReal.zero_lt_top).ne
  rw [← ex1_feasibleSet]
  ext x
  rw [ex1.mem_optimalSolutions_iff_of_ne_top hne]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rw [ex1_feasibleSet, Set.mem_singleton_iff] at h
  rw [h, ex1_f₀, ex1_optimalValue]
  norm_num

private theorem ex1_lagrangeFn (u : Rn 2) (x : Rn 2) :
    ex1.lagrangeFn u x = ((x 0 + u 0 * x 1 + u 1 * (x 0 ^ 2 - x 1) : ℝ) : EReal) := by
  rw [OrdinaryConvexProgram.lagrangeFn_apply, Fin.sum_univ_two, ex1_f₀, ex1_f_zero, ex1_f_one,
    ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ←
    EReal.coe_add]
  congr 1
  ring

/-- **§28**: the program has **no Kuhn–Tucker vector**, although its
optimal value is finite and its optimal solution is unique.

If `(λ₁, λ₂)` were one, then `ξ₁ + λ₁ξ₂ + λ₂(ξ₁² - ξ₂) ≥ 0` for every `(ξ₁, ξ₂)`. Taking
`ξ₁ = 0` and `ξ₂ = λ₂ - λ₁` forces `λ₁ = λ₂ =: λ`; then `ξ₁ = -1/(λ + 1)`, `ξ₂ = 0` makes the
left side `-1/(λ + 1)² < 0`. -/
theorem ex1_not_exists_isKuhnTuckerVector : ¬ ∃ u : Rn 2, ex1.IsKuhnTuckerVector u := by
  rintro ⟨u, hu⟩
  have hreal : ∀ x : Rn 2, 0 ≤ x 0 + u 0 * x 1 + u 1 * (x 0 ^ 2 - x 1) := by
    intro x
    have h : (0 : EReal) ≤ ex1.lagrangeFn u x := by
      rw [← ex1_optimalValue, ← hu.iInf_eq]
      exact iInf_le _ x
    rw [ex1_lagrangeFn] at h
    exact EReal.coe_nonneg.1 h
  have hnn : (0 : ℝ) ≤ u 0 := hu.nonneg 0 (by norm_num)
  -- the two multipliers must agree
  have heq : u 0 = u 1 := by
    have h := hreal (WithLp.toLp 2 ![0, -(u 0 - u 1)])
    have e0 : (WithLp.toLp 2 ![(0 : ℝ), -(u 0 - u 1)] : Rn 2) 0 = 0 := rfl
    have e1 : (WithLp.toLp 2 ![(0 : ℝ), -(u 0 - u 1)] : Rn 2) 1 = -(u 0 - u 1) := rfl
    rw [e0, e1] at h
    nlinarith [sq_nonneg (u 0 - u 1)]
  -- and then no such multiplier can exist
  have hd : (0 : ℝ) < u 0 + 1 := by linarith
  have h := hreal (WithLp.toLp 2 ![-(1 / (u 0 + 1)), 0])
  have e0 : (WithLp.toLp 2 ![-(1 / (u 0 + 1)), (0 : ℝ)] : Rn 2) 0 = -(1 / (u 0 + 1)) := rfl
  have e1 : (WithLp.toLp 2 ![-(1 / (u 0 + 1)), (0 : ℝ)] : Rn 2) 1 = 0 := rfl
  rw [e0, e1, ← heq] at h
  have hexpr : -(1 / (u 0 + 1)) + u 0 * 0 + u 0 * ((-(1 / (u 0 + 1))) ^ 2 - 0)
      = -(1 / (u 0 + 1) ^ 2) := by
    field_simp
    ring
  rw [hexpr] at h
  have hpos : (0 : ℝ) < 1 / (u 0 + 1) ^ 2 := by positivity
  linarith

/-! #### A program with linear constraints and no Kuhn–Tucker vector -/

/-- The set `C = {(ξ₁, ξ₂) | ξ₁² - ξ₂ ≤ 0}` of the counterexample: a parabolic region whose relative
interior misses the whole feasible set `{ξ₂ = 0}`. -/
def ex2Set : Set (Rn 2) := {x | x 0 ^ 2 - x 1 ≤ 0}

theorem mem_ex2Set {x : Rn 2} : x ∈ ex2Set ↔ x 0 ^ 2 - x 1 ≤ 0 := Iff.rfl

theorem convex_ex2Set : Convex ℝ ex2Set := by
  have h := convexOn_sqSub.convex_le 0
  have he : {x ∈ (Set.univ : Set (Rn 2)) | x 0 ^ 2 - x 1 ≤ 0} = ex2Set := by
    ext x; simp only [Set.mem_univ, true_and, mem_ex2Set, Set.mem_ofPred_eq]
  rwa [he] at h

/-- **§28**, second counterexample: the program with `C = {(ξ₁, ξ₂) | ξ₁² - ξ₂ ≤ 0}`,
`f₀(ξ₁, ξ₂) = ξ₁`, `f₁(ξ₁, ξ₂) = ξ₂` and `r = 0`. `f₀` is linear on `C` and the single constraint is
the linear equation `ξ₂ = 0`, so every hypothesis of Corollary 28.2.2 holds except the
relative-interior one: the feasible set is `{0}` and `0 ∉ ri C`. Again `(0, 0)` is the unique
optimal solution, `0` is the optimal value, and there is **no Kuhn–Tucker vector**
(`ex2_not_exists_isKuhnTuckerVector`). This is what shows the relative-interior condition in Theorem
28.2 and Corollary 28.2.2 cannot be dropped. -/
noncomputable def ex2 : OrdinaryConvexProgram 2 1 where
  C := ex2Set
  f₀ := ConvexAnalysis.restrictFn ex2Set fun x => ((x 0 : ℝ) : EReal)
  f := fun _ x => ((x 1 : ℝ) : EReal)
  r := 0
  r_le := Nat.zero_le 1
  convexFn_f₀ := (convexOn_iff_convexFn ex2Set _).1
    ⟨convex_ex2Set, fun _ _ _ _ _ _ _ _ _ => le_of_eq rfl⟩
  proper_f₀ := proper_restrictFn_coe ⟨0, by rw [mem_ex2Set]; norm_num⟩ _
  dom_f₀ := dom_restrictFn_coe _ _
  convexFn_f := fun _ hi => absurd hi (by omega)
  proper_f := fun _ hi => absurd hi (by omega)
  subset_dom_f := fun _ hi => absurd hi (by omega)
  relint_subset := fun _ hi => absurd hi (by omega)
  exists_affine := fun _ _ => ⟨coordAffine 2 1, fun _ => rfl⟩

@[simp] theorem ex2_C : ex2.C = ex2Set := rfl

@[simp] theorem ex2_r : ex2.r = 0 := rfl

@[simp] theorem ex2_f (i : Fin 1) (x : Rn 2) : ex2.f i x = ((x 1 : ℝ) : EReal) := rfl

theorem ex2_f₀_of_mem {x : Rn 2} (hx : x ∈ ex2Set) : ex2.f₀ x = ((x 0 : ℝ) : EReal) :=
  restrictFn_of_mem (f := fun y : Rn 2 => ((y 0 : ℝ) : EReal)) hx

/-- The only point of `C` with `ξ₂ = 0` is the origin. -/
theorem ex2_feasibleSet : ex2.feasibleSet = {0} := by
  ext x
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hC, -, h2⟩
    have hB : x 0 ^ 2 - x 1 ≤ 0 := mem_ex2Set.1 hC
    have h10 : x 1 = 0 := by
      have h := h2 0 (Nat.zero_le _)
      rw [ex2_f] at h
      exact_mod_cast h
    have h00 : x 0 = 0 := by nlinarith [sq_nonneg (x 0)]
    ext i
    rcases fin_two_cases i with rfl | rfl
    · simpa using h00
    · simpa using h10
  · rintro rfl
    refine ⟨by rw [ex2_C, mem_ex2Set]; norm_num, fun i hi => ?_, fun i _ => ?_⟩
    · rw [ex2_r] at hi; exact absurd hi (Nat.not_lt_zero _)
    rw [ex2_f]
    norm_num

theorem ex2_optimalValue : ex2.optimalValue = 0 := by
  have h0 : (0 : Rn 2) ∈ ({0} : Set (Rn 2)) := rfl
  have hC : (0 : Rn 2) ∈ ex2Set := by rw [mem_ex2Set]; norm_num
  rw [ex2.optimalValue_eq_biInf, ex2_feasibleSet]
  refine le_antisymm ?_ (le_iInf₂ fun x hx => ?_)
  · refine le_trans (iInf_le _ (0 : Rn 2)) (le_trans (iInf_le _ h0) ?_)
    rw [ex2_f₀_of_mem hC]; norm_num
  · rw [Set.mem_singleton_iff] at hx
    rw [hx, ex2_f₀_of_mem hC]
    norm_num

/-- **§28**: `(0, 0)` is again the unique optimal solution. -/
theorem ex2_optimalSolutions : ex2.optimalSolutions = {0} := by
  have hne : ex2.optimalValue ≠ ⊤ := by rw [ex2_optimalValue]; exact (EReal.zero_lt_top).ne
  have hC : (0 : Rn 2) ∈ ex2Set := by rw [mem_ex2Set]; norm_num
  rw [← ex2_feasibleSet]
  ext x
  rw [ex2.mem_optimalSolutions_iff_of_ne_top hne]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rw [ex2_feasibleSet, Set.mem_singleton_iff] at h
  rw [h, ex2_f₀_of_mem hC, ex2_optimalValue]
  norm_num

private theorem ex2_lagrangeFn_of_mem (u : Rn 1) {x : Rn 2} (hx : x ∈ ex2Set) :
    ex2.lagrangeFn u x = ((x 0 + u 0 * x 1 : ℝ) : EReal) := by
  rw [OrdinaryConvexProgram.lagrangeFn_apply, Fin.sum_univ_one, ex2_f₀_of_mem hx, ex2_f,
    ← EReal.coe_mul, ← EReal.coe_add]

/-- **§28**: the program has **no Kuhn–Tucker vector**, even though its
objective is linear on `C` and its only constraint is a linear equation.

A Kuhn–Tucker vector would be a single `λ₁` with `0 ≤ ξ₁ + λ₁ξ₂` for every `(ξ₁, ξ₂) ∈ C`. The
points `(-t, t²)` lie in `C` for every `t > 0`, and there they give `t ≤ λ₁t²`, i.e. `λ₁t ≥ 1`,
which fails at `t = 1/(|λ₁| + 1)`. -/
theorem ex2_not_exists_isKuhnTuckerVector : ¬ ∃ u : Rn 1, ex2.IsKuhnTuckerVector u := by
  rintro ⟨u, hu⟩
  have hreal : ∀ x : Rn 2, x ∈ ex2Set → 0 ≤ x 0 + u 0 * x 1 := by
    intro x hx
    have h : (0 : EReal) ≤ ex2.lagrangeFn u x := by
      rw [← ex2_optimalValue, ← hu.iInf_eq]
      exact iInf_le _ x
    rw [ex2_lagrangeFn_of_mem u hx] at h
    exact EReal.coe_nonneg.1 h
  have hd : (0 : ℝ) < |u 0| + 1 := by positivity
  set t : ℝ := 1 / (|u 0| + 1) with ht
  have htpos : (0 : ℝ) < t := by rw [ht]; positivity
  have e0 : (WithLp.toLp 2 ![-t, t ^ 2] : Rn 2) 0 = -t := rfl
  have e1 : (WithLp.toLp 2 ![-t, t ^ 2] : Rn 2) 1 = t ^ 2 := rfl
  have hmem : (WithLp.toLp 2 ![-t, t ^ 2] : Rn 2) ∈ ex2Set := by
    rw [mem_ex2Set, e0, e1]; ring_nf; exact le_refl 0
  have h := hreal _ hmem
  rw [e0, e1] at h
  have habs : |u 0| * t = 1 - t := by
    rw [ht]; field_simp; ring
  have h1 : u 0 * t ^ 2 ≤ |u 0| * t ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg t)
  have h2 : |u 0| * t ^ 2 = t - t ^ 2 := by
    calc |u 0| * t ^ 2 = |u 0| * t * t := by ring
      _ = (1 - t) * t := by rw [habs]
      _ = t - t ^ 2 := by ring
  have h3 : (0 : ℝ) < t ^ 2 := by positivity
  linarith

end Rockafellar
