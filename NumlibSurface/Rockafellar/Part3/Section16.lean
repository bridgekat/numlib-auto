import Numlib.Analysis.Convex.Duality.Exact
import Numlib.Analysis.Convex.Duality.FiniteProduct
import Numlib.Analysis.Convex.Duality.Ops
import Numlib.Analysis.Convex.Duality.Polar
import Numlib.Analysis.Convex.Duality.Relint
import Numlib.Analysis.Convex.Duality.RelintSeparation
import Numlib.Analysis.Convex.Polyhedral.Duality
import Numlib.Analysis.Convex.Recession.Closedness
import NumlibSurface.Rockafellar.Part3.Section13

/-!
# Rockafellar, §16: Dual Operations

The dual-operations dictionary: every operation of §5 has a dual operation, and conjugacy exchanges
the two. All 15 numbered results of §16 are formalized.

## The uniform shape of the section

Each of the four theorems is really three statements, and this module keeps them apart:

* the **identity**, valid for arbitrary functions with no hypothesis and no closure
  (`theorem_16_1_left`, `theorem_16_3_image`, `theorem_16_4_infConv`, `theorem_16_5_convFn`);
* the **closure form**, `(op of closures)* = cl (dual op of conjugates)`, which is the honest
  general statement (`theorem_16_3_closure`, `theorem_16_4_closure`, `theorem_16_5_closure`);
* the **exact form**, in which a relative-interior qualification removes the closure and makes the
  infimum attained (`theorem_16_3_exact`, `theorem_16_3_attained`, `theorem_16_4_exact`,
  `theorem_16_4_attained`), together with the *polyhedral* form of the same qualification, which
  Rockafellar states here as a remark and proves only in §19 (`theorem_16_3_polyhedral`).

## Notation

`A*` is `LinearMap.adjoint A` throughout: `isAdjointPair_adjoint` says that Mathlib's adjoint is
Rockafellar's, so no statement here carries an `IsAdjointPair` hypothesis even though every
backbone statement it specialises does. `λf` is `fun x => (l : EReal) * f x` and `fλ` is
`smulRight f l`, both from §5.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §16.
-/

open Set Pointwise

namespace Rockafellar

open ConvexAnalysis NumlibSurface

variable {m n : ℕ}

/-! ### The conjugate of the zero function

Rockafellar's proof of Theorem 16.1 at `λ = 0` is the single sentence "the constant function `0`
is conjugate to the indicator function `δ(· | 0)`". Both halves of that sentence are used below. -/

/-- **Rockafellar, §16, p. 141**: the conjugate of the constant function `0` is `δ(· | 0)`.

`Rn n` is a `SeparatingDual`, asserted in the shared header. -/
theorem conj_zero_rn : conj (pairing n) (0 : Rn n → EReal) = indicatorFn ({0} : Set (Rn n)) := by
  have h := conj_zero_eq_indicatorFn (B := pairing n) (E := Rn n) (F := Rn n)
  rwa [flip_pairing] at h

/-- The conjugate of `δ(· | 0)` is the constant function `0`, the other half of the same sentence.
Specialises `conj_indicatorFn_zero`. -/
theorem conj_indicatorFn_zero_rn :
    conj (pairing n) (indicatorFn ({0} : Set (Rn n))) = 0 :=
  conj_indicatorFn_zero (pairing n)

/-- The half-space `{x | ⟨x, x*⟩ ≤ 1}` cutting out a polar set is convex, which is why polarity
does not see a convex hull. -/
theorem convex_setOf_pairing_le_one (y : Rn n) : Convex ℝ {x : Rn n | pairing n x y ≤ 1} := by
  have hlin : IsLinearMap ℝ fun x : Rn n => pairing n x y :=
    ⟨fun a b => by simp, fun c a => by simp⟩
  exact convex_halfSpace_le hlin 1

/-! ### Theorem 16.1: scalar multiplication -/

/-- **Theorem 16.1.** For any proper convex function `f` one has `(λf)* = f*λ`,
`0 ≤ λ < ∞`. This is the case `λ > 0`, where no hypothesis on `f` is needed at all. -/
theorem theorem_16_1_left (f : Rn n → EReal) {l : ℝ} (hl : 0 < l) :
    conj (pairing n) (fun x => (l : EReal) * f x) = smulRight (conj (pairing n) f) l :=
  conj_smul hl (pairing n) f

/-- **Theorem 16.1**, the other formula: `(fλ)* = λf*`, `0 < λ < ∞`. -/
theorem theorem_16_1_right (f : Rn n → EReal) {l : ℝ} (hl : 0 < l) :
    conj (pairing n) (smulRight f l) = fun y => (l : EReal) * conj (pairing n) f y :=
  conj_smulRight hl (pairing n) f

/-- **Theorem 16.1** at `λ = 0`: `(0f)* = f*0`. Left multiplication by `0` sends any
`f` to the constant function `0`, right multiplication by `0` sends `f*` to `δ(· | 0)`, and the two
are conjugate. This is the clause the book's proof singles out. -/
theorem theorem_16_1_left_zero {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) :
    conj (pairing n) (fun x => (0 : EReal) * f x) = smulRight (conj (pairing n) f) 0 := by
  have hdom : (dom (conj (pairing n) f)).Nonempty :=
    (proper_conj_of_proper hf hp).dom_nonempty
  simp only [zero_mul]
  rw [smulRight_zero hdom]
  exact conj_zero_rn

/-- **Theorem 16.1** at `λ = 0`, the other formula: `(f0)* = 0f*`. -/
theorem theorem_16_1_right_zero {f : Rn n → EReal} (hp : Proper f) :
    conj (pairing n) (smulRight f 0) = fun y => (0 : EReal) * conj (pairing n) f y := by
  rw [smulRight_zero hp.dom_nonempty, conj_indicatorFn_zero_rn]
  funext y
  simp

/-- **Corollary 16.1.1.** For any non-empty convex set `C`,
`δ*(x* | λC) = λ δ*(x* | C)` for `0 ≤ λ < ∞`.

Convexity is not used: the identity is the indicator instance of Theorem 16.1 and holds for any
non-empty `C`. Specialises `supportFn_smul`, with the `λ = 0` case read off `0 • C = {0}`. -/
theorem corollary_16_1_1 {C : Set (Rn n)} (hC : C.Nonempty) {l : ℝ} (hl : 0 ≤ l) (y : Rn n) :
    supportFn (pairing n) (l • C) y = (l : EReal) * supportFn (pairing n) C y := by
  rcases hl.lt_or_eq with hlt | heq
  · exact supportFn_smul (pairing n) hlt C y
  · rw [← heq, zero_smul_set hC, ← Set.singleton_zero, supportFn_singleton]
    simp

/-- **Corollary 16.1.2.** For any non-empty convex set `C`, `(λC)° = λ⁻¹C°` for
`0 < λ < ∞`.

The book derives it from Corollary 16.1.1 through `C° = {x* | δ*(x* | C) ≤ 1}`; here it is one
unfolding of `polarSet`, since `⟨λx, x*⟩ = ⟨x, λx*⟩`. -/
theorem corollary_16_1_2 (C : Set (Rn n)) {l : ℝ} (hl : 0 < l) :
    polarSet (pairing n) (l • C) = l⁻¹ • polarSet (pairing n) C := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hl.ne'), inv_inv, mem_polarSet,
    mem_polarSet]
  have key : ∀ x : Rn n, pairing n (l • x) y = pairing n x (l • y) := fun x => by
    simp only [pairing_apply, real_inner_smul_left, real_inner_smul_right]
  constructor
  · intro h x hx
    have hx' := h (l • x) (Set.smul_mem_smul_set hx)
    rwa [key] at hx'
  · rintro h _ ⟨x, hx, rfl⟩
    change pairing n (l • x) y ≤ 1
    rw [key]
    exact h x hx

/-! ### Lemma 16.2: the constraint qualifications of §9, dualized -/

/-- **Lemma 16.2.** Let `L` be a subspace of `ℝⁿ` and let `f` be a proper convex
function. Then `L` meets `ri (dom f)` if and only if there exists no vector `x* ∈ Lᗮ` such that
`(f* 0⁺)(x*) ≤ 0` and `(f* 0⁺)(-x*) > 0`.

`Lᗮ` *is* the annihilator of `L` for the pairing, definitionally. -/
theorem lemma_16_2 (L : Submodule ℝ (Rn n)) {f : Rn n → EReal} (hf : ConvexFn f) (hp : Proper f) :
    ((L : Set (Rn n)) ∩ ri (dom f)).Nonempty ↔
      ¬ ∃ x' ∈ Lᗮ, recessionFn (conj (pairing n) f) x' ≤ 0 ∧
        0 < recessionFn (conj (pairing n) f) (-x') :=
  submodule_inter_relint_dom_nonempty_iff (B := pairing n) L hf hp (proper_conj_of_proper hf hp)

/-- **Corollary 16.2.1.** Let `A` be a linear transformation from `ℝⁿ` to `ℝᵐ` and let `g` be a
proper convex function on `ℝᵐ`. In order that there exist no vector `y* ∈ ℝᵐ` with `A*y* = 0`,
`(g* 0⁺)(y*) ≤ 0` and `(g* 0⁺)(-y*) > 0`, it is necessary and sufficient that `Ax ∈ ri (dom g)` for
at least one `x ∈ ℝⁿ`. Lemma 16.2 for the subspace `L = range A`, whose orthogonal complement is
`ker A*`. -/
theorem corollary_16_2_1 (A : Rn n →ₗ[ℝ] Rn m) {g : Rn m → EReal} (hg : ConvexFn g)
    (hp : Proper g) :
    (¬ ∃ y' : Rn m, LinearMap.adjoint A y' = 0 ∧
        recessionFn (conj (pairing m) g) y' ≤ 0 ∧
        0 < recessionFn (conj (pairing m) g) (-y')) ↔ ∃ x, A x ∈ ri (dom g) :=
  (exists_apply_mem_relint_dom_iff (separatingRight_pairing n) (isAdjointPair_adjoint A) hg hp
    (proper_conj_of_proper hg hp)).symm

/-- **Corollary 16.2.2.** Let `f₁, …, fₘ` be proper convex functions on `ℝⁿ`. In
order that there exist no vectors `x₁*, …, xₘ*` with

`x₁* + ⋯ + xₘ* = 0`,
`(f₁* 0⁺)(x₁*) + ⋯ + (fₘ* 0⁺)(xₘ*) ≤ 0`,
`(f₁* 0⁺)(-x₁*) + ⋯ + (fₘ* 0⁺)(-xₘ*) > 0`,

it is necessary and sufficient that `ri (dom f₁) ∩ ⋯ ∩ ri (dom fₘ) ≠ ∅`.

This is Lemma 16.2 inside `ℝᵐⁿ` for the diagonal subspace `L = {x | x₁ = ⋯ = xₘ}`, whose
orthogonal complement is `{x* | x₁* + ⋯ + xₘ* = 0}`. -/
theorem corollary_16_2_2 {ι : Type*} [Fintype ι] (f : ι → Rn n → EReal)
    (hf : ∀ i, ConvexFn (f i)) (hp : ∀ i, Proper (f i)) :
    (¬ ∃ x' : ι → Rn n, (∑ i, x' i = 0) ∧
        (∑ i, recessionFn (conj (pairing n) (f i)) (x' i)) ≤ 0 ∧
        0 < ∑ i, recessionFn (conj (pairing n) (f i)) (-(x' i)))
      ↔ (⋂ i, ri (dom (f i))).Nonempty :=
  (iInter_relint_dom_nonempty_iff (separatingRight_pairing n) f hf hp
    fun i => proper_conj_of_proper (hf i) (hp i)).symm

/-! ### Theorem 16.3: linear transformations -/

/-- **Theorem 16.3**, first formula: for a linear transformation `A` from `ℝⁿ` to
`ℝᵐ` and any convex function `f` on `ℝⁿ`, `(Af)* = f*A*`.

Unconditional: no convexity, no properness, no closure. Specialises `conj_mapLin`, whose only
input is the adjointness datum, supplied by `isAdjointPair_adjoint`. -/
theorem theorem_16_3_image (A : Rn n →ₗ[ℝ] Rn m) (f : Rn n → EReal) :
    conj (pairing m) (mapLin A f) = compLin (conj (pairing n) f) (LinearMap.adjoint A) :=
  conj_mapLin (isAdjointPair_adjoint A) f

/-- **Theorem 16.3**, second formula: `((cl g)A)* = cl(A*g*)` for any convex `g`
on `ℝᵐ`.

Specialises `conj_compLin_eq_clFn_mapLin`, applied to `cl g` (which is closed convex) and read
back through `(cl g)* = g*`. -/
theorem theorem_16_3_closure (A : Rn n →ₗ[ℝ] Rn m) {g : Rn m → EReal} (hg : ConvexFn g) :
    conj (pairing n) (compLin (clFn g) A)
      = clFn (mapLin (LinearMap.adjoint A) (conj (pairing m) g)) := by
  rw [conj_compLin_eq_clFn_mapLin (isAdjointPair_adjoint A) (convexFn_clFn hg)
    (closedFn_clFn g), conj_clFn]

/-- **Theorem 16.3**, the exact half: if there is an `x` with `Ax ∈ ri (dom g)`, the closure
operation can be omitted and `(gA)* = A*g*`. The book's hypotheses are `g` proper convex, not
closed. -/
theorem theorem_16_3_exact (A : Rn n →ₗ[ℝ] Rn m) {g : Rn m → EReal} (hg : ConvexFn g)
    (hp : Proper g) {x₀ : Rn n} (hx₀ : A x₀ ∈ ri (dom g)) :
    conj (pairing n) (compLin g A) = mapLin (LinearMap.adjoint A) (conj (pairing m) g) :=
  (IsExactImage.of_relint (isAdjointPair_adjoint A) hg hp hx₀).conj_compLin

/-- **Theorem 16.3**, the attainment: under the same qualification, for each `x*` the infimum
`inf {g*(y*) | A*y* = x*}` is attained (or is `+∞` vacuously). The backbone's guard `< ⊤` is exactly
the book's "or is `+∞` vacuously". -/
theorem theorem_16_3_attained (A : Rn n →ₗ[ℝ] Rn m) {g : Rn m → EReal} (hg : ConvexFn g)
    (hp : Proper g) {x₀ : Rn n} (hx₀ : A x₀ ∈ ri (dom g)) {y : Rn n}
    (hy : conj (pairing n) (compLin g A) y < ⊤) :
    ∃ z : Rn m, LinearMap.adjoint A z = y ∧
      conj (pairing m) g z = conj (pairing n) (compLin g A) y :=
  (IsExactImage.of_relint (isAdjointPair_adjoint A) hg hp hx₀).exists_conj_compLin_eq hy

/-- **Rockafellar, §16**, the unnumbered remark: when `g` is *polyhedral*, the
qualification `Ax ∈ ri (dom g)` of Theorem 16.3 weakens to `Ax ∈ dom g`, and the conclusion is
unchanged.

Rockafellar states this as a remark just after Corollary 16.3.1 and defers the proof to
Corollary 19.3.1: `g*` is polyhedral by Theorem 19.2, so `A*g*` is polyhedral and hence closed,
and the closure in the second formula has nothing left to close. -/
theorem theorem_16_3_polyhedral (A : Rn n →ₗ[ℝ] Rn m) {g : Rn m → EReal} (hg : PolyhedralFn g)
    (hp : Proper g) {x₀ : Rn n} (hx₀ : A x₀ ∈ dom g) :
    conj (pairing n) (compLin g A) = mapLin (LinearMap.adjoint A) (conj (pairing m) g) :=
  (IsExactImage.of_polyhedral (isAdjointPair_adjoint A) hg hp hx₀).conj_compLin

/-- **Rockafellar, §16**, the same remark, attainment clause under the weakened
qualification: for a polyhedral `g` the infimum `inf {g*(y*) | A*y* = x*}` is still attained
wherever it is finite. -/
theorem theorem_16_3_polyhedral_attained (A : Rn n →ₗ[ℝ] Rn m) {g : Rn m → EReal}
    (hg : PolyhedralFn g) (hp : Proper g) {x₀ : Rn n} (hx₀ : A x₀ ∈ dom g) {y : Rn n}
    (hy : conj (pairing n) (compLin g A) y < ⊤) :
    ∃ z : Rn m, LinearMap.adjoint A z = y ∧
      conj (pairing m) g z = conj (pairing n) (compLin g A) y :=
  (IsExactImage.of_polyhedral (isAdjointPair_adjoint A) hg hp hx₀).exists_conj_compLin_eq hy

/-- **Corollary 16.3.1**, first formula: `δ*(y* | AC) = δ*(A*y* | C)` for any convex set `C` in
`ℝⁿ`. The indicator instance of `theorem_16_3_image`, via `mapLin_indicatorFn`. Convexity is not
used. -/
theorem corollary_16_3_1_image (A : Rn n →ₗ[ℝ] Rn m) (C : Set (Rn n)) (y : Rn m) :
    supportFn (pairing m) (A '' C) y = supportFn (pairing n) C (LinearMap.adjoint A y) := by
  have h : supportFn (pairing m) (A '' C)
      = compLin (supportFn (pairing n) C) (LinearMap.adjoint A) := by
    rw [supportFn_eq_conj_indicatorFn, supportFn_eq_conj_indicatorFn, ← mapLin_indicatorFn,
      theorem_16_3_image]
  rw [h, compLin_apply]

/-- **Corollary 16.3.1**, second formula: for any convex set `D` in `ℝᵐ`,
`δ*(· | A⁻¹(cl D)) = cl(A* δ*(· | D))`.

The indicator instance of `theorem_16_3_closure`, via `clFn_indicatorFn` and
`compLin_indicatorFn`. -/
theorem corollary_16_3_1_closure (A : Rn n →ₗ[ℝ] Rn m) {D : Set (Rn m)} (hD : Convex ℝ D) :
    supportFn (pairing n) (A ⁻¹' closure D)
      = clFn (mapLin (LinearMap.adjoint A) (supportFn (pairing m) D)) := by
  rw [supportFn_eq_conj_indicatorFn, supportFn_eq_conj_indicatorFn, ← compLin_indicatorFn,
    ← clFn_indicatorFn]
  exact theorem_16_3_closure A (convexFn_indicatorFn.2 hD)

/-- **Corollary 16.3.1**, the exact half: if some `Ax ∈ ri D`, the closure operation
can be omitted and `δ*(x* | A⁻¹D) = inf {δ*(y* | D) | A*y* = x*}`, the infimum being attained. -/
theorem corollary_16_3_1_exact (A : Rn n →ₗ[ℝ] Rn m) {D : Set (Rn m)} (hD : Convex ℝ D)
    (hne : D.Nonempty) {x₀ : Rn n} (hx₀ : A x₀ ∈ ri D) :
    supportFn (pairing n) (A ⁻¹' D)
      = mapLin (LinearMap.adjoint A) (supportFn (pairing m) D) := by
  rw [supportFn_eq_conj_indicatorFn, supportFn_eq_conj_indicatorFn, ← compLin_indicatorFn]
  refine theorem_16_3_exact A (convexFn_indicatorFn.2 hD)
    ⟨by rw [dom_indicatorFn]; exact hne, indicatorFn_ne_bot D⟩ (x₀ := x₀) ?_
  rw [dom_indicatorFn]
  exact hx₀

/-- **Corollary 16.3.2**, first formula: `(AC)° = A*⁻¹(C°)` for any convex set `C` in `ℝⁿ`. One
unfolding of `polarSet` through the adjointness `⟨Ax, y*⟩ = ⟨x, A*y*⟩`. -/
theorem corollary_16_3_2_image (A : Rn n →ₗ[ℝ] Rn m) (C : Set (Rn n)) :
    polarSet (pairing m) (A '' C) = LinearMap.adjoint A ⁻¹' polarSet (pairing n) C := by
  ext y
  simp only [mem_polarSet, Set.mem_preimage, Set.forall_mem_image]
  exact forall₂_congr fun x _ => by rw [isAdjointPair_adjoint A x y]

/-- **Corollary 16.3.2**, the unconditional half of the second formula:
`A*(D°) ⊆ (A⁻¹D)°`. Equality holds after a closure, and without one under Corollary 16.3.1's
qualification; see the module docstring for why the closed form is not here. -/
theorem corollary_16_3_2_preimage (A : Rn n →ₗ[ℝ] Rn m) (D : Set (Rn m)) :
    LinearMap.adjoint A '' polarSet (pairing m) D ⊆ polarSet (pairing n) (A ⁻¹' D) := by
  rintro _ ⟨y, hy, rfl⟩ x hx
  rw [← isAdjointPair_adjoint A x y]
  exact hy (A x) hx

/-! ### Theorem 16.4: addition and infimal convolution -/

/-- **Theorem 16.4**, first formula, in the book's own `m`-ary form:
`(f₁ □ ⋯ □ fₘ)* = f₁* + ⋯ + fₘ*`.

The `□`-product is the `AddCommMonoid` sum of `InfConvFn`. Properness is *not* needed, and must
not be assumed at the intermediate stages, since `□` does not preserve it. -/
theorem theorem_16_4_infConv_finset {ι : Type*} (s : Finset ι) (f : ι → Rn n → EReal) :
    conj (pairing n) (ofInfConvFn (∑ i ∈ s, toInfConvFn (f i)))
      = ∑ i ∈ s, conj (pairing n) (f i) :=
  conj_sum_toInfConvFn (pairing n) s f

/-- **Theorem 16.4**, first formula for `m = 2`: `(f □ g)* = f* + g*`. -/
theorem theorem_16_4_infConv (f g : Rn n → EReal) :
    conj (pairing n) (infConv f g) = conj (pairing n) f + conj (pairing n) g :=
  conj_infConv (pairing n) f g

/-- **Theorem 16.4**, second formula: `(cl f + cl g)* = cl(f* □ g*)`. Specialises
`conj_add_eq_clFn_infConv`, applied to the closures. -/
theorem theorem_16_4_closure {f g : Rn n → EReal} (hf : ConvexFn f) (hg : ConvexFn g) :
    conj (pairing n) (clFn f + clFn g)
      = clFn (infConv (conj (pairing n) f) (conj (pairing n) g)) := by
  rw [conj_add_eq_clFn_infConv (convexFn_clFn hf) (closedFn_clFn f) (convexFn_clFn hg)
    (closedFn_clFn g), conj_clFn, conj_clFn]

/-- **Theorem 16.4**, the exact half: if `ri (dom f)` and `ri (dom g)` have a point in common, the
closure operation can be omitted and `(f + g)* = f* □ g*`. Closedness is not assumed, as in the
book. -/
theorem theorem_16_4_exact {f g : Rn n → EReal} (hf : ConvexFn f) (hpf : Proper f)
    (hg : ConvexFn g) (hpg : Proper g) {x₀ : Rn n} (hxf : x₀ ∈ ri (dom f))
    (hxg : x₀ ∈ ri (dom g)) :
    conj (pairing n) (f + g) = infConv (conj (pairing n) f) (conj (pairing n) g) :=
  (IsExactSum.of_relint hf hpf hg hpg hxf hxg).conj_add

/-- **Theorem 16.4**, the attainment: under the same qualification, for each `x*` the
infimum `inf {f*(x₁*) + g*(x₂*) | x₁* + x₂* = x*}` is attained. -/
theorem theorem_16_4_attained {f g : Rn n → EReal} (hf : ConvexFn f) (hpf : Proper f)
    (hg : ConvexFn g) (hpg : Proper g) {x₀ : Rn n} (hxf : x₀ ∈ ri (dom f))
    (hxg : x₀ ∈ ri (dom g)) (y : Rn n) :
    ∃ y₁ y₂ : Rn n, y₁ + y₂ = y ∧
      conj (pairing n) f y₁ + conj (pairing n) g y₂ = conj (pairing n) (f + g) y :=
  (IsExactSum.of_relint hf hpf hg hpg hxf hxg).exists_conj_add_eq y

/-- **Corollary 16.4.1**, first formula for `m = 2`:
`δ*(· | C₁ + C₂) = δ*(· | C₁) + δ*(· | C₂)`.

Unlike the function statement this needs no qualification: two suprema over sets never interact
through an `∞ - ∞`. -/
theorem corollary_16_4_1_add (C D : Set (Rn n)) :
    supportFn (pairing n) (C + D) = supportFn (pairing n) C + supportFn (pairing n) D :=
  supportFn_add (pairing n) C D

/-- **Corollary 16.4.1**, first formula in the book's `m`-ary form:
`δ*(· | C₁ + ⋯ + Cₘ) = δ*(· | C₁) + ⋯ + δ*(· | Cₘ)`. -/
theorem corollary_16_4_1_add_finset {ι : Type*} (s : Finset ι) (C : ι → Set (Rn n)) :
    supportFn (pairing n) (∑ i ∈ s, C i) = ∑ i ∈ s, supportFn (pairing n) (C i) := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, ← Set.singleton_zero, supportFn_singleton]
    funext y
    simp
  | cons i t hi ih => rw [Finset.sum_cons, Finset.sum_cons, corollary_16_4_1_add, ih]

/-- **Corollary 16.4.1**, second formula: `δ*(· | cl C₁ ∩ cl C₂) = cl(δ*(· | C₁) □ δ*(· | C₂))`. The
indicator instance of `theorem_16_4_closure`: adding indicators intersects the sets. -/
theorem corollary_16_4_1_closure {C D : Set (Rn n)} (hC : Convex ℝ C) (hD : Convex ℝ D) :
    supportFn (pairing n) (closure C ∩ closure D)
      = clFn (infConv (supportFn (pairing n) C) (supportFn (pairing n) D)) := by
  rw [supportFn_eq_conj_indicatorFn, supportFn_eq_conj_indicatorFn,
    supportFn_eq_conj_indicatorFn, ← indicatorFn_add, ← clFn_indicatorFn, ← clFn_indicatorFn]
  exact theorem_16_4_closure (convexFn_indicatorFn.2 hC) (convexFn_indicatorFn.2 hD)

/-- **Corollary 16.4.1**, the exact half: if `ri C₁` and `ri C₂` have a point in
common, `δ*(x* | C₁ ∩ C₂) = inf {δ*(x₁* | C₁) + δ*(x₂* | C₂) | x₁* + x₂* = x*}`, the infimum being
attained. -/
theorem corollary_16_4_1_exact {C D : Set (Rn n)} (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hCne : C.Nonempty) (hDne : D.Nonempty) {x₀ : Rn n} (hxC : x₀ ∈ ri C) (hxD : x₀ ∈ ri D) :
    supportFn (pairing n) (C ∩ D)
      = infConv (supportFn (pairing n) C) (supportFn (pairing n) D) := by
  rw [supportFn_eq_conj_indicatorFn, supportFn_eq_conj_indicatorFn,
    supportFn_eq_conj_indicatorFn, ← indicatorFn_add]
  refine theorem_16_4_exact (convexFn_indicatorFn.2 hC)
    ⟨by rw [dom_indicatorFn]; exact hCne, indicatorFn_ne_bot C⟩ (convexFn_indicatorFn.2 hD)
    ⟨by rw [dom_indicatorFn]; exact hDne, indicatorFn_ne_bot D⟩ (x₀ := x₀) ?_ ?_
  · rw [dom_indicatorFn]; exact hxC
  · rw [dom_indicatorFn]; exact hxD

/-- **Corollary 16.4.2**, first formula: `(K₁ + K₂)° = K₁° ∩ K₂°` for non-empty
convex cones.

The support function of a cone is the indicator of its polar, adding indicators intersects, and
an indicator determines its set. Only the cone property is used, not convexity. -/
theorem corollary_16_4_2_add {K L : Set (Rn n)} (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hK : ∀ a : ℝ, 0 < a → a • K = K) (hL : ∀ a : ℝ, 0 < a → a • L = L) :
    polarCone (pairing n) (K + L)
      = polarCone (pairing n) K ∩ polarCone (pairing n) L := by
  have hdist : ∀ (a : ℝ) (s t : Set (Rn n)), a • (s + t) = a • s + a • t := by
    intro a s t
    ext z
    simp only [Set.mem_smul_set, Set.mem_add]
    constructor
    · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨a • x, ⟨x, hx, rfl⟩, a • y, ⟨y, hy, rfl⟩, (smul_add a x y).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨x + y, ⟨x, hx, y, hy, rfl⟩, smul_add a x y⟩
  have hKL : ∀ a : ℝ, 0 < a → a • (K + L) = K + L := fun a ha => by
    rw [hdist, hK a ha, hL a ha]
  have h := corollary_16_4_1_add K L
  rw [supportFn_eq_indicatorFn_polarCone hKL (hKne.add hLne),
    supportFn_eq_indicatorFn_polarCone hK hKne,
    supportFn_eq_indicatorFn_polarCone hL hLne, indicatorFn_add] at h
  ext y
  have hy := congrFun h y
  constructor
  · intro h₁
    by_contra h₂
    rw [indicatorFn_of_mem h₁, indicatorFn_of_notMem h₂] at hy
    exact absurd hy (by simp)
  · intro h₂
    by_contra h₁
    rw [indicatorFn_of_notMem h₁, indicatorFn_of_mem h₂] at hy
    exact absurd hy (by simp)

/-- **Theorem 16.4**, the exact half in the book's own `m`-ary form: if the sets
`ri (dom fᵢ)`, `i = 1, …, m`, have a point in common, the closure operation can be omitted from
the second formula and `(f₁ + ⋯ + fₘ)* = f₁* □ ⋯ □ fₘ*`.

The family is indexed by a `Finset` rather than by `Fin m`, so `m = 0` is the vacuous empty
family and the book's `m ≥ 1` is `hs`. -/
theorem theorem_16_4_exact_finset {ι : Type*} {s : Finset ι} {f : ι → Rn n → EReal}
    (hs : s.Nonempty) (hf : ∀ i ∈ s, ConvexFn (f i)) (hpf : ∀ i ∈ s, Proper (f i))
    {x₀ : Rn n} (hx₀ : ∀ i ∈ s, x₀ ∈ ri (dom (f i))) :
    conj (pairing n) (∑ i ∈ s, f i)
      = ofInfConvFn (∑ i ∈ s, toInfConvFn (conj (pairing n) (f i))) :=
  (IsExactFinsetSum.of_relint (B := pairing n) hs hf hpf hx₀).conj_finsetSum

/-- **Theorem 16.4**, the attainment for `m` summands: under the same qualification,
for each `x*` the infimum `inf {f₁*(x₁*) + ⋯ + fₘ*(xₘ*) | x₁* + ⋯ + xₘ* = x*}` is attained. -/
theorem theorem_16_4_attained_finset {ι : Type*} {s : Finset ι} {f : ι → Rn n → EReal}
    (hs : s.Nonempty) (hf : ∀ i ∈ s, ConvexFn (f i)) (hpf : ∀ i ∈ s, Proper (f i))
    {x₀ : Rn n} (hx₀ : ∀ i ∈ s, x₀ ∈ ri (dom (f i))) (y : Rn n) :
    ∃ y' : ι → Rn n, ∑ i ∈ s, y' i = y ∧
      ∑ i ∈ s, conj (pairing n) (f i) (y' i) = conj (pairing n) (∑ i ∈ s, f i) y :=
  (IsExactFinsetSum.of_relint (B := pairing n) hs hf hpf hx₀).exists_conj_finsetSum_eq y

/-- Adding indicator functions over a `Finset` intersects the sets: the `m`-ary form of
`indicatorFn_add`. The empty intersection is `ℝⁿ`, whose indicator is the zero function, so no
non-emptiness is needed. -/
private theorem sum_indicatorFn_finset {ι : Type*} (s : Finset ι) (C : ι → Set (Rn n)) :
    ∑ i ∈ s, indicatorFn (C i) = indicatorFn (⋂ i ∈ s, C i) := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty]
    funext x
    simp
  | cons i t hi ih =>
    rw [Finset.sum_cons, ih, indicatorFn_add]
    congr 1
    ext x
    simp [Finset.mem_cons]

/-- **Corollary 16.4.1**, the exact half in the book's `m`-ary form: if the sets
`ri Cᵢ` have a point in common, the closure operation can be omitted and
`δ*(· | C₁ ∩ ⋯ ∩ Cₘ) = δ*(· | C₁) □ ⋯ □ δ*(· | Cₘ)`.

Non-emptiness of the `Cᵢ` is not a hypothesis here although it is in the book: a common point of
the relative interiors already supplies it. -/
theorem corollary_16_4_1_exact_finset {ι : Type*} {s : Finset ι} {C : ι → Set (Rn n)}
    (hs : s.Nonempty) (hC : ∀ i ∈ s, Convex ℝ (C i)) {x₀ : Rn n} (hx₀ : ∀ i ∈ s, x₀ ∈ ri (C i)) :
    supportFn (pairing n) (⋂ i ∈ s, C i)
      = ofInfConvFn (∑ i ∈ s, toInfConvFn (supportFn (pairing n) (C i))) := by
  have hconj : ∀ i, supportFn (pairing n) (C i) = conj (pairing n) (indicatorFn (C i)) :=
    fun i => supportFn_eq_conj_indicatorFn (pairing n) (C i)
  rw [supportFn_eq_conj_indicatorFn, ← sum_indicatorFn_finset,
    theorem_16_4_exact_finset (f := fun i => indicatorFn (C i)) hs
      (fun i hi => convexFn_indicatorFn.2 (hC i hi))
      (fun i hi => ⟨⟨x₀, by rw [dom_indicatorFn]; exact intrinsicInterior_subset (hx₀ i hi)⟩,
        indicatorFn_ne_bot (C i)⟩)
      (fun i hi => by rw [dom_indicatorFn]; exact hx₀ i hi)]
  simp only [hconj]

/-- **Corollary 16.4.1**, the attainment for `m` sets: under the same qualification,
for each `x*` the infimum `inf {δ*(x₁* | C₁) + ⋯ + δ*(xₘ* | Cₘ) | x₁* + ⋯ + xₘ* = x*}` is
attained. -/
theorem corollary_16_4_1_attained_finset {ι : Type*} {s : Finset ι} {C : ι → Set (Rn n)}
    (hs : s.Nonempty) (hC : ∀ i ∈ s, Convex ℝ (C i)) {x₀ : Rn n} (hx₀ : ∀ i ∈ s, x₀ ∈ ri (C i))
    (y : Rn n) :
    ∃ y' : ι → Rn n, ∑ i ∈ s, y' i = y ∧
      ∑ i ∈ s, supportFn (pairing n) (C i) (y' i)
        = supportFn (pairing n) (⋂ i ∈ s, C i) y := by
  have hconj : ∀ i, supportFn (pairing n) (C i) = conj (pairing n) (indicatorFn (C i)) :=
    fun i => supportFn_eq_conj_indicatorFn (pairing n) (C i)
  obtain ⟨y', hy', hval⟩ :=
    theorem_16_4_attained_finset (f := fun i => indicatorFn (C i)) hs
      (fun i hi => convexFn_indicatorFn.2 (hC i hi))
      (fun i hi => ⟨⟨x₀, by rw [dom_indicatorFn]; exact intrinsicInterior_subset (hx₀ i hi)⟩,
        indicatorFn_ne_bot (C i)⟩)
      (fun i hi => by rw [dom_indicatorFn]; exact hx₀ i hi) y
  refine ⟨y', hy', ?_⟩
  rw [supportFn_eq_conj_indicatorFn, ← sum_indicatorFn_finset, ← hval]
  simp only [hconj]

/-! ### Theorem 16.5: pointwise suprema and convex hulls -/

/-- **Theorem 16.5**, first formula: `(conv {fᵢ | i ∈ I})* = sup {fᵢ* | i ∈ I}` for an arbitrary
index set `I`. Unconditional; the empty family is not an exception. Specialises `conj_convFn`. -/
theorem theorem_16_5_convFn {ι : Sort*} (f : ι → Rn n → EReal) :
    conj (pairing n) (convFn f) = ⨆ i, conj (pairing n) (f i) :=
  conj_convFn (pairing n) f

/-- **Theorem 16.5**, second formula: `(sup {cl fᵢ | i ∈ I})* = cl (conv {fᵢ* | i ∈ I})`.
Specialises `conj_iSup_eq_clFn_convFn`, applied to the closures. -/
theorem theorem_16_5_closure {ι : Sort*} {f : ι → Rn n → EReal} (hf : ∀ i, ConvexFn (f i)) :
    conj (pairing n) (⨆ i, clFn (f i))
      = clFn (convFn fun i => conj (pairing n) (f i)) := by
  rw [conj_iSup_eq_clFn_convFn (fun i => convexFn_clFn (hf i)) (fun i => closedFn_clFn (f i))]
  simp only [conj_clFn]

/-- **Corollary 16.5.1**, first formula: the support function of the convex hull `D`
of the union of the sets `Cᵢ` is `sup {δ*(· | Cᵢ) | i ∈ I}`. -/
theorem corollary_16_5_1_hull {ι : Sort*} (C : ι → Set (Rn n)) :
    supportFn (pairing n) (convexHull ℝ (⋃ i, C i))
      = fun y => ⨆ i, supportFn (pairing n) (C i) y := by
  rw [supportFn_convexHull, supportFn_iUnion]

/-- **Corollary 16.5.1**, second formula: the support function of the intersection of
the sets `cl Cᵢ` is `cl (conv {δ*(· | Cᵢ) | i ∈ I})`.

The indicator instance of `theorem_16_5_closure`. The index set must be non-empty: over an empty
family the book's `⋂ cl Cᵢ` is all of `ℝⁿ` while `sup {δ(· | Cᵢ)}` is `-∞`. -/
theorem corollary_16_5_1_closure {ι : Sort*} [Nonempty ι] {C : ι → Set (Rn n)}
    (hC : ∀ i, Convex ℝ (C i)) :
    supportFn (pairing n) (⋂ i, closure (C i))
      = clFn (convFn fun i => supportFn (pairing n) (C i)) := by
  have hind : (⨆ i, clFn (indicatorFn (C i))) = indicatorFn (⋂ i, closure (C i)) := by
    simp only [clFn_indicatorFn]
    funext x
    rw [iSup_apply]
    by_cases hx : x ∈ ⋂ i, closure (C i)
    · rw [indicatorFn_of_mem hx]
      refine le_antisymm (iSup_le fun i => ?_) (le_iSup_of_le (Classical.arbitrary ι) ?_)
      · rw [indicatorFn_of_mem (Set.mem_iInter.1 hx i)]
      · rw [indicatorFn_of_mem (Set.mem_iInter.1 hx _)]
    · rw [indicatorFn_of_notMem hx]
      obtain ⟨i, hi⟩ := not_forall.1 (fun h => hx (Set.mem_iInter.2 h))
      exact le_antisymm le_top (le_iSup_of_le i (by rw [indicatorFn_of_notMem hi]))
  simp only [supportFn_eq_conj_indicatorFn]
  rw [← hind]
  exact theorem_16_5_closure fun i => convexFn_indicatorFn.2 (hC i)

/-- **Corollary 16.5.2**, first formula:
`(conv {Cᵢ | i ∈ I})° = ⋂ {Cᵢ° | i ∈ I}`.

Polarity is order-inverting and `{x | ⟨x, x*⟩ ≤ 1}` is convex, so the convex hull is invisible to
it; this is the book's own second proof. -/
theorem corollary_16_5_2_hull {ι : Sort*} (C : ι → Set (Rn n)) :
    polarSet (pairing n) (convexHull ℝ (⋃ i, C i)) = ⋂ i, polarSet (pairing n) (C i) := by
  ext y
  simp only [Set.mem_iInter, mem_polarSet]
  constructor
  · intro hy i x hx
    exact hy x (subset_convexHull ℝ _ (Set.mem_iUnion.2 ⟨i, hx⟩))
  · intro hy
    have hsub : (⋃ i, C i) ⊆ {x : Rn n | pairing n x y ≤ 1} := by
      rintro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      exact hy i x hi
    exact fun x hx => convexHull_min hsub (convex_setOf_pairing_le_one y) hx

/-- **Corollary 16.5.2**, the unconditional half of the second formula: each `Cᵢ°` is
contained in `(⋂ Cⱼ)°`, hence so is the convex hull of their union. Equality with the polar of
`⋂ cl Cⱼ` holds after a closure; see the module docstring. -/
theorem corollary_16_5_2_inter {ι : Sort*} (C : ι → Set (Rn n)) (i : ι) :
    polarSet (pairing n) (C i) ⊆ polarSet (pairing n) (⋂ j, C j) :=
  polarSet_anti (Set.iInter_subset C i)

end Rockafellar
