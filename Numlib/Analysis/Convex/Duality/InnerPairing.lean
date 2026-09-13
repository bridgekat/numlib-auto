import Numlib.Analysis.Convex.Duality.Pairing

/-!
# Self-pairings of inner-product type

A pairing of a space with **itself** that is symmetric and positive definite behaves like an inner
product in every way the theory needs, without carrying a `NormedAddCommGroup` structure of its
own. That matters because Moreau's theorem gets applied on `U × X`, which carries the *supremum*
norm and so has no `InnerProductSpace ℝ` instance, even though `prodPairing (innerₗ U) (innerₗ X)`
is a perfectly good inner product on it. Moving to `WithLp 2 (U × X)` instead would replace the
topology *instance*, so `ClosedFn`, `Continuous` and `IsClosed` would stop transferring
definitionally; generalising the pairing costs one class and leaves the topology alone.

## Main definitions

* `IsInnerPairing B` — `B` is symmetric, positive semidefinite, and definite.
* `IsContinuousInnerPairing B` — an inner pairing whose quadratic form `x ↦ B x x` is continuous.
  This is the only topological fact Moreau's theorem needs, and it holds for `innerₗ E` on any real
  inner-product space, with no finite-dimensionality.
* `pairingNorm B x` — the induced norm `√(B x x)`.

## Main results

* `flip_eq_self`, `separatingRight_of_isInnerPairing`, `injective_flip_of_isInnerPairing` — an
  inner pairing is its own flip and separates on the right, which is what the duality theory asks
  of a self-pairing.
* `exists_innerSL_eq`, `toDual_eq_innerSL`, `innerSL_eq_zero_iff`, `toDual_apply_eq_innerL` — the
  Fréchet–Riesz dictionary between a vector `b` and the functional `⟨·, b⟩`, in the form a
  finite-dimensional surface reads its books through.
* `self_pairing_add`, `self_pairing_sub`, `self_pairing_combo_le` — the quadratic expansions, and
  convexity of `½ B z z` with its defect visible. These replace `norm_add_sq_real` and friends.
* `pairing_sq_le_mul` — **Cauchy–Schwarz** for a positive semidefinite symmetric form. Only
  `self_nonneg` is used, not definiteness: the proof splits on `B y y = 0`, and semidefiniteness
  alone forces `B x y = 0` in that branch.
* `pairingNorm_add_le` — the triangle inequality, so `pairingNorm` is a genuine norm.
* `exists_pairingNorm_le_and_le_pairingNorm` — in **finite dimensions** the induced norm is
  equivalent to the ambient one, so nothing stated through `pairingNorm` says anything new about
  the topology.

## Implementation notes

`IsInnerPairing` is a `Prop`-class rather than a structure carrying data: the form `B` is already a
`LinearMap`, and the class only records the three properties, so an inner-product space's own
`innerₗ E` picks the instance up automatically. Definiteness is stated as `B x x = 0 → x = 0`,
which is the form proofs apply; `self_pos` supplies the other.

No `InnerProductSpace` instance is manufactured from `IsInnerPairing`: doing so through
`InnerProductSpace.ofCore` would produce a second `NormedAddCommGroup` on `E`, which is the clash
this module exists to avoid.
-/

namespace ConvexAnalysis

open scoped RealInnerProductSpace

section Defs

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A pairing of `E` with itself that is **symmetric and positive definite** — an inner product in
all but the `NormedAddCommGroup` structure. -/
class IsInnerPairing (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : Prop where
  /-- The pairing is symmetric. -/
  pairing_comm (B) : ∀ x y : E, B x y = B y x
  /-- The pairing is positive semidefinite. -/
  self_nonneg (B) : ∀ x : E, 0 ≤ B x x
  /-- The pairing is definite. -/
  eq_zero_of_self_eq_zero (B) : ∀ x : E, B x x = 0 → x = 0

variable {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ} [IsInnerPairing B] {x y : E}

theorem pairing_comm (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) [IsInnerPairing B] (x y : E) : B x y = B y x :=
  IsInnerPairing.pairing_comm B x y

theorem self_pairing_nonneg (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) [IsInnerPairing B] (x : E) : 0 ≤ B x x :=
  IsInnerPairing.self_nonneg B x

/-- A symmetric pairing is its own flip. This is what lets `closedFn_conj` — which asks for
`IsContinuousPairing B.flip` — be applied to an inner pairing without a detour. -/
@[simp] theorem flip_eq_self (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) [IsInnerPairing B] : B.flip = B :=
  LinearMap.ext fun x => LinearMap.ext fun y => pairing_comm B y x

@[simp] theorem self_pairing_eq_zero_iff : B x x = 0 ↔ x = 0 :=
  ⟨IsInnerPairing.eq_zero_of_self_eq_zero B x, fun h => by rw [h]; simp⟩

/-- Positive definiteness in the form the analysis uses. -/
theorem self_pairing_pos (hx : x ≠ 0) : 0 < B x x :=
  lt_of_le_of_ne (self_pairing_nonneg B x) fun h => hx (self_pairing_eq_zero_iff.1 h.symm)

/-- An inner pairing **separates on the right**: `B x y = 0` for every `x` forces `y = 0`, by
testing against `y` itself. This is the hypothesis the level-set and recession duality asks for in
place of a book's "`y ≠ 0`". -/
theorem separatingRight_of_isInnerPairing (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) [IsInnerPairing B] :
    B.SeparatingRight := fun y h => IsInnerPairing.eq_zero_of_self_eq_zero B y (h y)

/-- The flip of an inner pairing is injective — the form in which the subgradient calculus asks
for separation. -/
theorem injective_flip_of_isInnerPairing (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) [IsInnerPairing B] :
    Function.Injective B.flip :=
  LinearMap.ker_eq_bot.1
    (LinearMap.separatingRight_iff_flip_ker_eq_bot.1 (separatingRight_of_isInnerPairing B))

/-- The quadratic expansion the discriminant argument runs on. -/
theorem self_pairing_add_smul (t : ℝ) (x y : E) :
    B (x + t • y) (x + t • y) = B x x + 2 * t * B x y + t ^ 2 * B y y := by
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [pairing_comm B y x]
  ring

/-! #### Expansions

The quadratic identities `‖x ± y‖² = ‖x‖² ± 2⟪x, y⟫ + ‖y‖²` and their companions. -/

theorem self_pairing_add (x y : E) : B (x + y) (x + y) = B x x + 2 * B x y + B y y := by
  have h := self_pairing_add_smul (B := B) 1 x y
  rw [one_smul] at h
  rw [h]; ring

theorem self_pairing_sub (x y : E) : B (x - y) (x - y) = B x x - 2 * B x y + B y y := by
  have h := self_pairing_add_smul (B := B) (-1) x y
  rw [neg_one_smul, ← sub_eq_add_neg] at h
  rw [h]; ring

omit [IsInnerPairing B] in
@[simp] theorem self_pairing_neg (x : E) : B (-x) (-x) = B x x := by
  simp only [map_neg, LinearMap.neg_apply, neg_neg]

omit [IsInnerPairing B] in
theorem self_pairing_sub_rev (x y : E) : B (x - y) (x - y) = B (y - x) (y - x) := by
  rw [show y - x = -(x - y) by abel, self_pairing_neg]

omit [IsInnerPairing B] in
theorem self_pairing_smul (a : ℝ) (x : E) : B (a • x) (a • x) = a ^ 2 * B x x := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring

/-- **Convexity of the quadratic form**, with the defect `a b B (u - v) (u - v) ≥ 0` visible. This
is the one inequality that makes `w z = ½ B z z` a convex function. -/
theorem self_pairing_combo_le {u v : E} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    B (a • u + b • v) (a • u + b • v) / 2 ≤ a * (B u u / 2) + b * (B v v / 2) := by
  have hexp : B (a • u + b • v) (a • u + b • v)
      = a ^ 2 * B u u + 2 * (a * b * B u v) + b ^ 2 * B v v := by
    rw [self_pairing_add, self_pairing_smul, self_pairing_smul]
    congr 1
    congr 1
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hdef : 0 ≤ a * b * (B u u - 2 * B u v + B v v) := by
    rw [← self_pairing_sub]
    exact mul_nonneg (mul_nonneg ha hb) (self_pairing_nonneg B (u - v))
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [hexp, hdef]

/-- **Cauchy–Schwarz** for a symmetric positive semidefinite pairing. Definiteness is not used. -/
theorem pairing_sq_le_mul (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) [IsInnerPairing B] (x y : E) :
    (B x y) ^ 2 ≤ B x x * B y y := by
  rcases eq_or_lt_of_le (self_pairing_nonneg B y) with hy | hy
  · -- `B y y = 0`: the quadratic is affine in `t`, so its slope must vanish.
    have hzero : B x y = 0 := by
      by_contra hne
      -- Pushing `t` far in the direction that decreases the value makes it negative.
      set c : ℝ := B x y with hc
      have hkey : ∀ t : ℝ, 0 ≤ B x x + 2 * t * c := fun t => by
        have h := self_pairing_nonneg B (x + t • y)
        rwa [self_pairing_add_smul t x y, ← hy, mul_zero, add_zero] at h
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · have := hkey ((B x x + 1) / (2 * -c))
        rw [show 2 * ((B x x + 1) / (2 * -c)) * c = -(B x x + 1) by
          field_simp] at this
        linarith
      · have := hkey (-(B x x + 1) / (2 * c))
        rw [show 2 * (-(B x x + 1) / (2 * c)) * c = -(B x x + 1) by
          field_simp] at this
        linarith
    rw [hzero, ← hy]
    simp
  · -- `B y y > 0`: complete the square at `t = -B x y / B y y`.
    have h := self_pairing_nonneg B (x + (-(B x y) / B y y) • y)
    rw [self_pairing_add_smul] at h
    have hne : B y y ≠ 0 := hy.ne'
    have hexp : B x x + 2 * (-(B x y) / B y y) * B x y + (-(B x y) / B y y) ^ 2 * B y y
        = B x x - (B x y) ^ 2 / B y y := by field_simp; ring
    rw [hexp, sub_nonneg, div_le_iff₀ hy] at h
    linarith

/-- The **norm induced by the pairing**, `√(B x x)`. -/
noncomputable def pairingNorm (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x : E) : ℝ := Real.sqrt (B x x)

theorem pairingNorm_nonneg (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x : E) : 0 ≤ pairingNorm B x :=
  Real.sqrt_nonneg _

@[simp] theorem pairingNorm_sq (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) [IsInnerPairing B] (x : E) :
    pairingNorm B x ^ 2 = B x x :=
  Real.sq_sqrt (self_pairing_nonneg B x)

@[simp] theorem pairingNorm_eq_zero_iff : pairingNorm B x = 0 ↔ x = 0 := by
  rw [pairingNorm, Real.sqrt_eq_zero (self_pairing_nonneg B x), self_pairing_eq_zero_iff]

@[simp] theorem pairingNorm_zero (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) [IsInnerPairing B] :
    pairingNorm B (0 : E) = 0 :=
  pairingNorm_eq_zero_iff.2 rfl

theorem pairingNorm_neg (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) [IsInnerPairing B] (x : E) :
    pairingNorm B (-x) = pairingNorm B x := by
  simp only [pairingNorm, map_neg, LinearMap.neg_apply, neg_neg]

/-- Cauchy–Schwarz in norm form. -/
theorem pairing_le_pairingNorm_mul (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) [IsInnerPairing B] (x y : E) :
    B x y ≤ pairingNorm B x * pairingNorm B y := by
  have hsq := pairing_sq_le_mul B x y
  have hprod : pairingNorm B x * pairingNorm B y = Real.sqrt (B x x * B y y) := by
    rw [pairingNorm, pairingNorm, ← Real.sqrt_mul (self_pairing_nonneg B x)]
  rw [hprod]
  calc B x y ≤ |B x y| := le_abs_self _
    _ = Real.sqrt ((B x y) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (B x x * B y y) := Real.sqrt_le_sqrt hsq

/-- The triangle inequality: `pairingNorm B` is a norm. -/
theorem pairingNorm_add_le (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) [IsInnerPairing B] (x y : E) :
    pairingNorm B (x + y) ≤ pairingNorm B x + pairingNorm B y := by
  have hexp : B (x + y) (x + y) = B x x + 2 * B x y + B y y := by
    have h := self_pairing_add_smul (B := B) 1 x y
    rw [one_smul] at h
    rw [h]; ring
  have hcs := pairing_le_pairingNorm_mul B x y
  have hsum : B (x + y) (x + y) ≤ (pairingNorm B x + pairingNorm B y) ^ 2 := by
    rw [hexp, add_sq, pairingNorm_sq, pairingNorm_sq]
    linarith
  rw [pairingNorm]
  calc Real.sqrt (B (x + y) (x + y))
      ≤ Real.sqrt ((pairingNorm B x + pairingNorm B y) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = pairingNorm B x + pairingNorm B y :=
        Real.sqrt_sq (add_nonneg (pairingNorm_nonneg B x) (pairingNorm_nonneg B y))

theorem pairingNorm_sub_le (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) [IsInnerPairing B] (x y z : E) :
    pairingNorm B (x - z) ≤ pairingNorm B (x - y) + pairingNorm B (y - z) := by
  have h := pairingNorm_add_le B (x - y) (y - z)
  rwa [show x - y + (y - z) = x - z by abel] at h

end Defs

/-! ### Inner pairings with a continuous quadratic form -/

section Continuous

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- An inner pairing whose **quadratic form is continuous**. This does not follow from
`IsContinuousPairing`, which gives continuity only in the first variable with the second held
fixed. -/
class IsContinuousInnerPairing (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : Prop extends IsInnerPairing B where
  /-- The quadratic form is continuous. -/
  continuous_self (B) : Continuous fun x : E => B x x

theorem continuous_self_pairing' (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) [IsContinuousInnerPairing B] :
    Continuous fun x : E => B x x :=
  IsContinuousInnerPairing.continuous_self B

variable [IsTopologicalAddGroup E]

/-- **Polarization makes the diagonal do all the work**: a symmetric form whose quadratic form is
continuous is continuous in each variable separately, so `IsContinuousInnerPairing` subsumes
`IsContinuousPairing`. -/
instance (priority := 100) isContinuousPairing_of_isContinuousInnerPairing
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) [IsContinuousInnerPairing B] : IsContinuousPairing B where
  continuous_left y := by
    have h : (fun x : E => B x y) = fun x : E => (B (x + y) (x + y) - B x x - B y y) / 2 := by
      funext x
      rw [self_pairing_add]
      ring
    rw [h]
    exact ((((continuous_self_pairing' B).comp (continuous_id.add continuous_const)).sub
      (continuous_self_pairing' B)).sub continuous_const).div_const 2

/-- The flip of an inner pairing is continuous, which instance search cannot see through
`LinearMap.flip` on its own. -/
instance isContinuousPairing_flip_of_isContinuousInnerPairing
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) [IsContinuousInnerPairing B] : IsContinuousPairing B.flip := by
  rw [flip_eq_self]
  infer_instance

/-- The flip of a compatible inner pairing is compatible: for a symmetric pairing the two
conditions coincide. -/
instance isCompatiblePairing_flip_of_isInnerPairing (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) [IsInnerPairing B]
    [IsCompatiblePairing B] : IsCompatiblePairing B.flip := by
  rw [flip_eq_self]
  infer_instance

end Continuous

/-! ### The inner product of an inner-product space -/

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inner product of a real inner-product space is an inner pairing. -/
instance isInnerPairing_innerL : IsInnerPairing (innerₗ E) where
  pairing_comm x y := by
    simp only [innerₗ_apply_apply]
    exact real_inner_comm y x
  self_nonneg x := by
    simp only [innerₗ_apply_apply]
    exact real_inner_self_nonneg
  eq_zero_of_self_eq_zero x h := by
    simp only [innerₗ_apply_apply] at h
    exact inner_self_eq_zero.1 h

@[simp] theorem pairingNorm_innerL (x : E) : pairingNorm (innerₗ E) x = ‖x‖ := by
  rw [pairingNorm, innerₗ_apply_apply, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg x)]

/-- The inner product of a real inner-product space has a continuous quadratic form, `‖·‖ ^ 2`,
with no finite-dimensionality needed. -/
instance isContinuousInnerPairing_innerL : IsContinuousInnerPairing (innerₗ E) where
  continuous_self := by
    have h : (fun x : E => (innerₗ E) x x) = fun x : E => ‖x‖ ^ 2 := by
      funext x
      rw [innerₗ_apply_apply, real_inner_self_eq_norm_sq]
    rw [h]
    exact (continuous_norm.pow 2)

/-- `innerₗ E` separates on the right. -/
theorem separatingRight_innerL : (innerₗ E).SeparatingRight :=
  separatingRight_of_isInnerPairing (innerₗ E)

/-! #### The vector picture of a linear functional

A book writes a linear function on `ℝⁿ` as `⟨·, b⟩` and quantifies over the vector `b`; the
backbone quantifies over a continuous linear functional, which is what separation produces. The
translation is Mathlib's `innerSL ℝ b`, which on a Hilbert space is the Fréchet–Riesz map
`InnerProductSpace.toDual ℝ E b`. -/

/-- `⟨·, b⟩` is the zero functional exactly when `b` is the zero vector: this is what makes
`b ≠ 0` and "`{x | ⟨x, b⟩ = β}` is a hyperplane" the same condition. -/
theorem _root_.innerSL_eq_zero_iff {b : E} : innerSL ℝ b = 0 ↔ b = 0 := by
  rw [← map_zero (innerSL ℝ (E := E))]
  exact innerSL_inj

/-- The Fréchet–Riesz map is `innerSL`. -/
theorem toDual_eq_innerSL [CompleteSpace E] (b : E) :
    InnerProductSpace.toDual ℝ E b = innerSL ℝ b := rfl

/-- **Fréchet–Riesz**: on a real Hilbert space every continuous linear functional is `⟨·, b⟩`. This
is what lets a surface statement quantify over vectors while its proof quantifies over
functionals. -/
theorem exists_innerSL_eq [CompleteSpace E] (f : E →L[ℝ] ℝ) : ∃ b : E, innerSL ℝ b = f :=
  ⟨(InnerProductSpace.toDual ℝ E).symm f, (InnerProductSpace.toDual ℝ E).apply_symm_apply f⟩

/-- The Riesz representative of `v` evaluated at `x` is `innerₗ E x v`: every backbone result
about `HasGradientAtFn` produces the left-hand side, and a statement in the book's `⟨x, v⟩` wants
the right. -/
theorem toDual_apply_eq_innerL [CompleteSpace E] (v x : E) :
    (InnerProductSpace.toDual ℝ E v) x = innerₗ E x v := by
  rw [InnerProductSpace.toDual_apply_apply, innerₗ_apply_apply]
  exact real_inner_comm x v

end Inner

/-! ### Products -/

section Prod

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  {Bu : U →ₗ[ℝ] U →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] X →ₗ[ℝ] ℝ}

/-- **A product of inner pairings is an inner pairing**: `U × X` has no `InnerProductSpace`
structure, but `prodPairing (innerₗ U) (innerₗ X)` is an inner pairing on it. -/
instance isInnerPairing_prodPairing [IsInnerPairing Bu] [IsInnerPairing Bx] :
    IsInnerPairing (prodPairing Bu Bx) where
  pairing_comm p q := by
    simp only [prodPairing_apply]
    rw [pairing_comm Bu, pairing_comm Bx]
  self_nonneg p := by
    simp only [prodPairing_apply]
    exact add_nonneg (self_pairing_nonneg Bu p.1) (self_pairing_nonneg Bx p.2)
  eq_zero_of_self_eq_zero p h := by
    simp only [prodPairing_apply] at h
    have h1 : Bu p.1 p.1 = 0 :=
      le_antisymm (by linarith [self_pairing_nonneg Bx p.2]) (self_pairing_nonneg Bu p.1)
    have h2 : Bx p.2 p.2 = 0 :=
      le_antisymm (by linarith [self_pairing_nonneg Bu p.1]) (self_pairing_nonneg Bx p.2)
    exact Prod.ext (self_pairing_eq_zero_iff.1 h1) (self_pairing_eq_zero_iff.1 h2)

/-- A product of continuous inner pairings has a continuous quadratic form. -/
instance isContinuousInnerPairing_prodPairing [TopologicalSpace U] [TopologicalSpace X]
    [IsContinuousInnerPairing Bu] [IsContinuousInnerPairing Bx] :
    IsContinuousInnerPairing (prodPairing Bu Bx) where
  continuous_self := by
    have h : (fun p : U × X => (prodPairing Bu Bx) p p)
        = fun p : U × X => Bu p.1 p.1 + Bx p.2 p.2 := rfl
    rw [h]
    exact ((continuous_self_pairing' Bu).comp continuous_fst).add
      ((continuous_self_pairing' Bx).comp continuous_snd)

end Prod

/-! ### Equivalence with the ambient norm, in finite dimensions -/

section Equivalence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ} [IsInnerPairing B]

omit [IsInnerPairing B] in
/-- `x ↦ B x x` is continuous, being a continuous bilinear form evaluated on the diagonal. No
`IsContinuousPairing` hypothesis is needed, since in finite dimensions every linear map out of `E`
is continuous. -/
theorem continuous_self_pairing : Continuous fun x : E => B x x := by
  set T : E →ₗ[ℝ] (E →L[ℝ] ℝ) :=
    (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).toLinearMap.comp B with hT
  have hTc : Continuous T := LinearMap.continuous_of_finiteDimensional T
  have heq : (fun x : E => B x x) = fun x : E => (T x) x := rfl
  rw [heq]
  exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := ℝ)).continuous.comp
    (hTc.prodMk continuous_id)

/-- In finite dimensions every inner pairing has a continuous quadratic form. -/
instance (priority := 100) isContinuousInnerPairing_of_finiteDimensional :
    IsContinuousInnerPairing B where
  continuous_self := continuous_self_pairing

omit [IsInnerPairing B] in
/-- `pairingNorm B` is continuous. -/
theorem continuous_pairingNorm : Continuous (pairingNorm B) :=
  Real.continuous_sqrt.comp continuous_self_pairing

/-- **The induced norm is equivalent to the ambient one.** Positive definiteness makes `B x x`
strictly positive on the unit sphere, which is compact in finite dimensions, so it has a positive
minimum and a finite maximum there; homogeneity spreads both bounds over all of `E`. -/
theorem exists_pairingNorm_le_and_le_pairingNorm (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) [IsInnerPairing B] :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ x : E, c * ‖x‖ ≤ pairingNorm B x) ∧ ∀ x : E, pairingNorm B x ≤ C * ‖x‖ := by
  classical
  rcases subsingleton_or_nontrivial E with hsub | hnt
  · -- Every vector is zero; both bounds are vacuous.
    refine ⟨1, 1, one_pos, one_pos, fun x => ?_, fun x => ?_⟩ <;>
      rw [Subsingleton.elim x (0 : E)] <;> simp
  have hsphere : IsCompact (Metric.sphere (0 : E) 1) :=
    isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : E) 1).Nonempty := by
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    exact ⟨‖v‖⁻¹ • v, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]⟩
  obtain ⟨p, hp, hpmin⟩ :=
    hsphere.exists_isMinOn hne (continuous_pairingNorm (B := B)).continuousOn
  obtain ⟨q, hq, hqmax⟩ :=
    hsphere.exists_isMaxOn hne (continuous_pairingNorm (B := B)).continuousOn
  have hp0 : p ≠ 0 := fun h => by
    rw [mem_sphere_zero_iff_norm, h, norm_zero] at hp
    exact absurd hp zero_ne_one
  have hcpos : 0 < pairingNorm B p :=
    lt_of_le_of_ne (pairingNorm_nonneg B p) fun h => hp0 (pairingNorm_eq_zero_iff.1 h.symm)
  have hCpos : 0 < pairingNorm B q + 1 := by linarith [pairingNorm_nonneg B q]
  -- Homogeneity: `pairingNorm B (a • x) = |a| * pairingNorm B x`.
  have hhom : ∀ (a : ℝ) (x : E), pairingNorm B (a • x) = |a| * pairingNorm B x := fun a x => by
    have hq : B (a • x) (a • x) = a ^ 2 * B x x := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
    rw [pairingNorm, pairingNorm, hq, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]
  have hunit : ∀ z : E, z ≠ 0 → ‖z‖⁻¹ • z ∈ Metric.sphere (0 : E) 1 := fun z hz => by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)]
  refine ⟨pairingNorm B p, pairingNorm B q + 1, hcpos, hCpos, fun x => ?_, fun x => ?_⟩
  · rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx
      have hle := isMinOn_iff.1 hpmin _ (hunit x hx)
      rw [hhom, abs_inv, abs_norm, inv_mul_eq_div, le_div_iff₀ hxpos] at hle
      exact hle
  · rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx
      have hle := isMaxOn_iff.1 hqmax _ (hunit x hx)
      rw [hhom, abs_inv, abs_norm, inv_mul_eq_div, div_le_iff₀ hxpos] at hle
      nlinarith

end Equivalence

end ConvexAnalysis
