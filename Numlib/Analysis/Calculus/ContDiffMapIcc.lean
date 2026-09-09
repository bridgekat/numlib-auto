import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# `Cᵏ[a, b]`, the continuously differentiable functions on a compact interval

The space of `k` times continuously differentiable real functions on a compact interval `[a, b]`,
normed by `‖u‖ = ∑_{j ≤ k} ‖u⁽ʲ⁾‖_∞`, as a Banach space, together with its closed subspace of the
functions vanishing at both endpoints.  The space is defined in Kendall Atkinson and Weimin Han,
*Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd edition, Springer, 2009,
§1.4, and the norm used here is the one that book writes as (2.1.2) in §2.1; §1.4 uses the
equivalent maximum `max_{j ≤ k} ‖u⁽ʲ⁾‖_∞` instead.

Mathlib has the case `k = 0` as `C(X, ℝ)` for a compact `X`, and nothing beyond it for a compact
interval.  `ContDiffMapSupportedIn` is a different space: its fields ask for `ContDiff ℝ n f` on
the whole of `ℝ` together with `EqOn f 0 Kᶜ`, so membership would force every derivative to vanish
at the endpoints, and it carries a family of seminorms rather than a norm.

## Main definitions

* `ContinuousMap.HasDerivIcc hab f g`: the continuous function `g` on `[a, b]` is the derivative of
  the continuous function `f` there, at the two endpoints as well.
* `ContinuousMap.antideriv hab g c`: the antiderivative `t ↦ c + ∫ₐᵗ g` of `g` on `[a, b]`.
* `ContDiffMapIcc hab k`: the space `Cᵏ[a, b]`, with `ContDiffMapIcc.deriv u j` the `j`-th
  derivative of `u`, `⇑u` the function `u` itself and `ContDiffMapIcc.extend u` that function read
  on all of `ℝ`.
* `ContDiffMapIcc.shift`, `ContDiffMapIcc.cons`: differentiation `d/dx : Cᵏ⁺¹[a, b] → Cᵏ[a, b]`,
  and its section prepending an antiderivative with a prescribed value at `a`.
* `ContDiffMapIcc.derivCLM`, `ContDiffMapIcc.shiftCLM`: those two as bounded linear maps of norm at
  most one.
* `ContDiffMapIcc.ofContDiff`, `ContDiffMapIcc.ofContDiffOn`: the two constructors from a function,
  one for a globally `Cᵏ` function on `ℝ` and one for a function `ContDiffOn` on `[a, b]`.
* `ContDiffMapIcc.zeroBoundary hab k`: the closed subspace `Cᵏ₀[a, b] = {v : v a = v b = 0}`.
* `ContDiffMapIcc.periodicBoundary hab k`: the closed subspace on which every derivative up to
  order `k` matches at the two endpoints — the periodic `Cᵏ` functions read on one period.

## Main results

* `ContDiffMapIcc.isClosed_submodule` and the `CompleteSpace` instance: `Cᵏ[a, b]` is a Banach
  space.
* `ContDiffMapIcc.deriv_eq_iteratedDerivWithin`, `ContDiffMapIcc.coe_injective`: the representation
  is faithful — the `j`-th entry of the tuple is `iteratedDerivWithin j u (Icc a b)`, so an element
  is determined by the function it is.
* `ContDiffMapIcc.contDiffOn` and `ContDiffMapIcc.ofContDiffOn`: the space is exactly the book's —
  every element is `k` times continuously differentiable on `[a, b]` in the sense of `ContDiffOn`,
  and conversely every such function is an element.
* `ContDiffMapIcc.exists_periodic_contDiff` and
  `ContDiffMapIcc.ofContDiff_mem_periodicBoundary`: the elements of `periodicBoundary` are exactly
  the restrictions to `[a, b]` of the `(b - a)`-periodic `Cᵏ` functions on `ℝ`.
* `ContinuousMap.hasDerivIcc_iff`: the fundamental theorem of calculus on `[a, b]`, which is what
  makes the defining condition a closed one.

## Implementation notes

An element is represented by the *tuple of its derivatives* `(u, u', …, u⁽ᵏ⁾)`, subject to each
entry being the derivative of the one before it.  Two alternatives were rejected.

* On `{u : ℝ → ℝ // ContDiffOn ℝ k u (Icc a b)}` the expression `∑_{j ≤ k} ‖u⁽ʲ⁾‖_∞` is only a
  *semi*norm, being blind to the values of `u` off `[a, b]`, so that carrier would need a quotient.
* Carrying a single function on the subtype `↥(Icc a b)` would need a calculus on that subtype,
  which Mathlib does not have.

The tuple avoids both: the norm `∑_j ‖p j‖_∞` is the norm of `PiLp 1 (Fin (k + 1) → C([a, b], ℝ))`,
which is already a Banach space, and the space is a *closed* subspace of it.

Closedness is where the work is.  It cannot be had from `hasDerivAt_of_tendstoUniformlyOn` or
`hasFDerivAt_of_tendstoUniformlyOn`, which require the set to be **open** and so say nothing at the
endpoints of `[a, b]`.  The route taken instead is the fundamental theorem of calculus: `g` is the
derivative of `f` on `[a, b]` if and only if `f t = f a + ∫ₐᵗ g`, an identity between two
continuous functions of `f` and `g` for the supremum norm, hence a closed condition.
-/
open Set MeasureTheory intervalIntegral

namespace ContinuousMap

variable {a b : ℝ}

/-- `f.HasDerivIcc hab g` says that the continuous function `g` on the compact interval `[a, b]`
is the derivative of the continuous function `f` there: at every `t ∈ [a, b]`, including the two
endpoints, `f` has derivative `g t` *within* `[a, b]`.

`f` is read as a function on all of `ℝ` through `ContinuousMap.IccExtend`, which is constant
outside `[a, b]`; since a derivative within `[a, b]` at a point of `[a, b]` sees only the values on
`[a, b]`, the choice of extension is immaterial. -/
def HasDerivIcc (hab : a ≤ b) (f g : C(Icc a b, ℝ)) : Prop :=
  ∀ t : Icc a b, HasDerivWithinAt (IccExtend hab f) (g t) (Icc a b) t

/-- Integration from `a` to `t` of a continuous function on `[a, b]`, extended constantly outside
the interval, as a bounded linear functional on `C([a, b], ℝ)` of norm at most `|t - a|`. -/
noncomputable def integralIccCLM (hab : a ≤ b) (t : ℝ) : C(Icc a b, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ s in a..t, IccExtend hab f s
      map_add' := fun f₁ f₂ => by
        rw [← integral_add ((IccExtend hab f₁).continuous.intervalIntegrable _ _)
          ((IccExtend hab f₂).continuous.intervalIntegrable _ _)]
        rfl
      map_smul' := fun c f => by
        simp only [RingHom.id_apply, ← intervalIntegral.integral_smul]
        rfl }
    |t - a| fun f => by
      refine (norm_integral_le_of_norm_le_const fun s _ => ?_).trans_eq (mul_comm _ _)
      exact norm_coe_le_norm f _

@[simp]
theorem integralIccCLM_apply (hab : a ≤ b) (t : ℝ) (f : C(Icc a b, ℝ)) :
    integralIccCLM hab t f = ∫ s in a..t, IccExtend hab f s :=
  rfl

variable {f g : C(Icc a b, ℝ)}

/-- One half of `ContinuousMap.hasDerivIcc_iff`: if `g` is the derivative of `f` on `[a, b]`, then
`f` is recovered from `g` by the fundamental theorem of calculus. -/
theorem HasDerivIcc.integral_eq {hab : a ≤ b} (h : HasDerivIcc hab f g) (t : Icc a b) :
    ∫ s in a..(t : ℝ), IccExtend hab g s = f t - f ⟨a, left_mem_Icc.2 hab⟩ := by
  have hderiv : ∀ x ∈ Ioo a (t : ℝ),
      HasDerivWithinAt (IccExtend hab f) (IccExtend hab g x) (Ioi x) x := by
    intro x hx
    have hxmem : x ∈ Icc a b := ⟨hx.1.le, hx.2.le.trans t.2.2⟩
    have hnhds : Icc a b ∈ nhds x := Icc_mem_nhds hx.1 (lt_of_lt_of_le hx.2 t.2.2)
    have hx' : (IccExtend hab g) x = g ⟨x, hxmem⟩ := by
      rw [ContinuousMap.coe_IccExtend]; exact Set.IccExtend_of_mem hab _ hxmem
    rw [hx']
    exact ((h ⟨x, hxmem⟩).hasDerivAt hnhds).hasDerivWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le t.2.1
    (IccExtend hab f).continuous.continuousOn hderiv
    ((IccExtend hab g).continuous.intervalIntegrable _ _)]
  rw [ContinuousMap.coe_IccExtend, Set.IccExtend_val, Set.IccExtend_left]

/-- **A continuous function on `[a, b]` is the derivative of another exactly when the second is the
first's integral.**  This is the fundamental theorem of calculus in the form used to prove that
`Cᵏ[a, b]` is complete: the right-hand side is a *closed* condition for the supremum norm, whereas
the left-hand side is not visibly one. -/
theorem hasDerivIcc_iff (hab : a ≤ b) :
    HasDerivIcc hab f g ↔
      ∀ t : Icc a b, f t = f ⟨a, left_mem_Icc.2 hab⟩ + integralIccCLM hab t g := by
  refine ⟨fun h t => by rw [integralIccCLM_apply, h.integral_eq t]; ring, fun h t => ?_⟩
  have hgt : (IccExtend hab g) (t : ℝ) = g t := by
    rw [ContinuousMap.coe_IccExtend]; exact Set.IccExtend_val hab _ t
  have hd : HasDerivAt (fun u : ℝ => f ⟨a, left_mem_Icc.2 hab⟩ + ∫ s in a..u, IccExtend hab g s)
      (g t) (t : ℝ) := by
    rw [← hgt]
    exact (((IccExtend hab g).continuous.integral_hasStrictDerivAt a t).hasDerivAt).const_add _
  refine (hd.hasDerivWithinAt (s := Icc a b)).congr (fun y hy => ?_) ?_
  · rw [ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem hab _ hy, h ⟨y, hy⟩]
    rfl
  · rw [ContinuousMap.coe_IccExtend, Set.IccExtend_val, h t]
    rfl

end ContinuousMap

namespace ContinuousMap

variable {a b : ℝ} {f₁ f₂ g₁ g₂ : C(Icc a b, ℝ)} {hab : a ≤ b}

theorem HasDerivIcc.add (hf : HasDerivIcc hab f₁ g₁) (hg : HasDerivIcc hab f₂ g₂) :
    HasDerivIcc hab (f₁ + f₂) (g₁ + g₂) := fun t => by
  have h := (hf t).add (hg t)
  rw [show ((g₁ + g₂) t : ℝ) = g₁ t + g₂ t from rfl]
  exact h

theorem HasDerivIcc.smul (c : ℝ) (hf : HasDerivIcc hab f₁ g₁) :
    HasDerivIcc hab (c • f₁) (c • g₁) := fun t => by
  have h := (hf t).const_smul c
  rw [show ((c • g₁) t : ℝ) = c • g₁ t from rfl]
  exact h

theorem hasDerivIcc_zero (hab : a ≤ b) : HasDerivIcc hab (0 : C(Icc a b, ℝ)) 0 := fun t => by
  rw [show ((0 : C(Icc a b, ℝ)) t : ℝ) = 0 from rfl]
  exact (hasDerivWithinAt_const _ _ (0 : ℝ))

/-- The antiderivative `t ↦ c + ∫ₐᵗ g` of a continuous function `g` on the compact interval
`[a, b]`, again a continuous function on `[a, b]`.  It is the unique continuous function with value
`c` at `a` whose derivative on `[a, b]` is `g` (`ContinuousMap.hasDerivIcc_antideriv` and
`ContinuousMap.HasDerivIcc.eq_antideriv`). -/
noncomputable def antideriv (hab : a ≤ b) (g : C(Icc a b, ℝ)) (c : ℝ) : C(Icc a b, ℝ) where
  toFun t := c + ∫ s in a..(t : ℝ), IccExtend hab g s
  continuous_toFun := by
    have h : Continuous fun t : ℝ => c + ∫ s in a..t, IccExtend hab g s :=
      continuous_const.add (continuous_iff_continuousAt.2 fun t =>
        (((IccExtend hab g).continuous.integral_hasStrictDerivAt a t).hasDerivAt).continuousAt)
    exact h.comp continuous_subtype_val

@[simp]
theorem antideriv_apply (hab : a ≤ b) (g : C(Icc a b, ℝ)) (c : ℝ) (t : Icc a b) :
    antideriv hab g c t = c + ∫ s in a..(t : ℝ), IccExtend hab g s := rfl

@[simp]
theorem antideriv_left (hab : a ≤ b) (g : C(Icc a b, ℝ)) (c : ℝ) :
    antideriv hab g c ⟨a, left_mem_Icc.2 hab⟩ = c := by
  simp

/-- **The fundamental theorem of calculus on `[a, b]`**: `g` is the derivative of its
antiderivative, at the endpoints too. -/
theorem hasDerivIcc_antideriv (hab : a ≤ b) (g : C(Icc a b, ℝ)) (c : ℝ) :
    HasDerivIcc hab (antideriv hab g c) g := by
  rw [hasDerivIcc_iff]
  intro t
  simp

/-- A continuous function on `[a, b]` with a derivative there is the antiderivative of that
derivative; in particular a function on `[a, b]` is determined by its derivative and its value at
`a`. -/
theorem HasDerivIcc.eq_antideriv {hab : a ≤ b} {f g : C(Icc a b, ℝ)} (h : HasDerivIcc hab f g) :
    f = antideriv hab g (f ⟨a, left_mem_Icc.2 hab⟩) := by
  ext t
  rw [antideriv_apply, ← integralIccCLM_apply]
  exact (hasDerivIcc_iff hab).1 h t

/-- The derivative of a constant function on `[a, b]` is `0`. -/
theorem hasDerivIcc_const (hab : a ≤ b) (c : ℝ) :
    HasDerivIcc hab (ContinuousMap.const (Icc a b) c) 0 := fun t => by
  rw [show ((0 : C(Icc a b, ℝ)) t : ℝ) = 0 from rfl]
  exact hasDerivWithinAt_const _ _ _

/-- On a nondegenerate interval the derivative on `[a, b]` is unique. -/
theorem HasDerivIcc.unique {hab : a ≤ b} (hlt : a < b) {f g₁ g₂ : C(Icc a b, ℝ)}
    (h₁ : HasDerivIcc hab f g₁) (h₂ : HasDerivIcc hab f g₂) : g₁ = g₂ := by
  ext t
  exact (uniqueDiffOn_Icc hlt t t.2).eq_deriv _ (h₁ t) (h₂ t)

end ContinuousMap

open ContinuousMap

variable {a b : ℝ}

/-- The tuples `(p 0, …, p k)` of continuous functions on `[a, b]` in which each entry is the
derivative of the one before it, as a submodule of `PiLp 1 (Fin (k + 1) → C([a, b], ℝ))`, the
`(k + 1)`-fold product carrying the norm `∑_j ‖p j‖_∞`.  This is the carrier of
`ContDiffMapIcc`. -/
def ContDiffMapIcc.submodule (hab : a ≤ b) (k : ℕ) :
    Submodule ℝ (PiLp 1 fun _ : Fin (k + 1) => C(Icc a b, ℝ)) where
  carrier := {p | ∀ j : Fin k, HasDerivIcc hab (p j.castSucc) (p j.succ)}
  add_mem' hp hq j := (hp j).add (hq j)
  zero_mem' _ := hasDerivIcc_zero hab
  smul_mem' c _ hp j := (hp j).smul c

/-- **`Cᵏ[a, b]`, the `k` times continuously differentiable real functions on the compact interval
`[a, b]`** (Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009, §1.4), as a Banach space under the norm
`‖u‖ = ∑_{j ≤ k} ‖u⁽ʲ⁾‖_∞`.

An element is represented by the *tuple of its derivatives* `(u, u', …, u⁽ᵏ⁾)`, each a continuous
function on `[a, b]`, subject to the requirement that each entry is the derivative of the one
before it on `[a, b]`, endpoints included (`ContinuousMap.HasDerivIcc`).  The representation is
forced: on `{u : ℝ → ℝ // ContDiffOn ℝ k u (Icc a b)}` the expression `∑_{j ≤ k} ‖u⁽ʲ⁾‖_∞` is only
a *semi*norm, being blind to the values of `u` off `[a, b]`, so the naive carrier would need a
quotient.  Carrying the derivatives instead makes the norm a genuine norm, and makes the space a
closed subspace of a finite product of copies of `C([a, b], ℝ)`, whence completeness.

`ContDiffMapIcc.deriv u j` is the `j`-th entry, `ContDiffMapIcc.deriv_eq_iteratedDerivWithin`
identifies it with `iteratedDerivWithin j u (Icc a b)` when `a < b`, and `⇑u` is the function `u`
itself. -/
def ContDiffMapIcc (hab : a ≤ b) (k : ℕ) : Type := ContDiffMapIcc.submodule hab k

namespace ContDiffMapIcc

variable {hab : a ≤ b} {k : ℕ}

noncomputable instance : NormedAddCommGroup (ContDiffMapIcc hab k) :=
  inferInstanceAs (NormedAddCommGroup (submodule hab k))

noncomputable instance : NormedSpace ℝ (ContDiffMapIcc hab k) :=
  inferInstanceAs (NormedSpace ℝ (submodule hab k))

/-- The `j`-th derivative of `u ∈ Cᵏ[a, b]`, as a continuous function on `[a, b]`; `j = 0` gives
`u` itself. -/
def deriv (u : ContDiffMapIcc hab k) (j : Fin (k + 1)) : C(Icc a b, ℝ) := u.1 j

/-- Every `u ∈ Cᵏ[a, b]` is a function on `[a, b]`, namely its own zeroth derivative. -/
instance : CoeFun (ContDiffMapIcc hab k) fun _ => Icc a b → ℝ := ⟨fun u => u.deriv 0⟩

theorem coe_def (u : ContDiffMapIcc hab k) : ⇑u = ⇑(u.deriv 0) := rfl

/-- `u ∈ Cᵏ[a, b]` read as a function on all of `ℝ`, constant outside `[a, b]`.  Statements about
the calculus of `u` are phrased through this extension: a derivative *within* `[a, b]` at a point
of `[a, b]` does not see the values outside, so nothing depends on the choice of extension. -/
noncomputable def extend (u : ContDiffMapIcc hab k) : C(ℝ, ℝ) :=
  ContinuousMap.IccExtend hab (u.deriv 0)

@[simp]
theorem extend_val (u : ContDiffMapIcc hab k) (t : Icc a b) : u.extend t = u t :=
  Set.IccExtend_val hab _ t

theorem extend_of_mem (u : ContDiffMapIcc hab k) {t : ℝ} (ht : t ∈ Icc a b) :
    u.extend t = u ⟨t, ht⟩ :=
  Set.IccExtend_of_mem hab _ ht

/-- Each entry of the tuple is the derivative of the one before it, on all of `[a, b]`. -/
theorem hasDerivIcc (u : ContDiffMapIcc hab k) (j : Fin k) :
    HasDerivIcc hab (u.deriv j.castSucc) (u.deriv j.succ) := u.2 j

@[ext]
theorem ext {u v : ContDiffMapIcc hab k} (h : ∀ j, u.deriv j = v.deriv j) : u = v :=
  Subtype.ext ((WithLp.ext_iff 1).2 (funext h))

@[simp]
theorem deriv_add (u v : ContDiffMapIcc hab k) (j : Fin (k + 1)) :
    (u + v).deriv j = u.deriv j + v.deriv j := rfl

@[simp]
theorem deriv_smul (c : ℝ) (u : ContDiffMapIcc hab k) (j : Fin (k + 1)) :
    (c • u).deriv j = c • u.deriv j := rfl

@[simp]
theorem deriv_zero (j : Fin (k + 1)) : (0 : ContDiffMapIcc hab k).deriv j = 0 := rfl

@[simp]
theorem deriv_sub (u v : ContDiffMapIcc hab k) (j : Fin (k + 1)) :
    (u - v).deriv j = u.deriv j - v.deriv j := rfl

/-- The norm of `Cᵏ[a, b]` is `‖u‖ = ∑_{j ≤ k} ‖u⁽ʲ⁾‖_∞`. -/
theorem norm_def (u : ContDiffMapIcc hab k) : ‖u‖ = ∑ j, ‖u.deriv j‖ := by
  have h : ‖u‖ = ‖(u.1 : PiLp 1 fun _ : Fin (k + 1) => C(Icc a b, ℝ))‖ := rfl
  rw [h, PiLp.norm_eq_of_L1]
  rfl

/-- Each derivative is bounded by the norm of `Cᵏ[a, b]`. -/
theorem norm_deriv_le (u : ContDiffMapIcc hab k) (j : Fin (k + 1)) : ‖u.deriv j‖ ≤ ‖u‖ := by
  rw [norm_def]
  exact Finset.single_le_sum (f := fun i => ‖u.deriv i‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ j)

/-- The defining condition of `Cᵏ[a, b]` is a *closed* condition on the tuple: by the fundamental
theorem of calculus (`ContinuousMap.hasDerivIcc_iff`) it says that each entry is the integral of
the next, and both sides of that identity are continuous for the supremum norm.

This is where completeness comes from, and it is the reason the fundamental theorem of calculus is
used rather than Mathlib's `hasDerivAt_of_tendstoUniformlyOn`, which needs an *open* set and so
says nothing at the endpoints of `[a, b]`. -/
theorem isClosed_submodule (hab : a ≤ b) (k : ℕ) :
    IsClosed (submodule hab k : Set (PiLp 1 fun _ : Fin (k + 1) => C(Icc a b, ℝ))) := by
  have hset : (submodule hab k : Set (PiLp 1 fun _ : Fin (k + 1) => C(Icc a b, ℝ))) =
      ⋂ (j : Fin k) (t : Icc a b),
        {p | p j.castSucc t
          = p j.castSucc ⟨a, left_mem_Icc.2 hab⟩ + integralIccCLM hab t (p j.succ)} := by
    ext p
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun hp j => (hasDerivIcc_iff hab).1 (hp j), fun hp j => (hasDerivIcc_iff hab).2 (hp j)⟩
  rw [hset]
  refine isClosed_iInter fun j => isClosed_iInter fun t => isClosed_eq ?_ ?_
  · exact (continuous_eval_const t).comp (PiLp.proj (𝕜 := ℝ) 1 _ j.castSucc).continuous
  · exact ((continuous_eval_const _).comp (PiLp.proj (𝕜 := ℝ) 1 _ j.castSucc).continuous).add
      ((integralIccCLM hab t).continuous.comp (PiLp.proj (𝕜 := ℝ) 1 _ j.succ).continuous)

/-- **`Cᵏ[a, b]` is a Banach space** (Atkinson and Han, *Theoretical Numerical Analysis*, 3rd
edition, §1.4): it is a closed subspace of a finite product of copies of the Banach space
`C([a, b], ℝ)`. -/
instance : CompleteSpace (ContDiffMapIcc hab k) := by
  have : IsClosed (submodule hab k : Set (PiLp 1 fun _ : Fin (k + 1) => C(Icc a b, ℝ))) :=
    isClosed_submodule hab k
  exact inferInstanceAs (CompleteSpace (submodule hab k))

/-- Build an element of `Cᵏ[a, b]` from the tuple of its derivatives: continuous functions
`p 0, …, p k` on `[a, b]` in which each is the derivative of the one before it. -/
def mk (hab : a ≤ b) {k : ℕ} (p : Fin (k + 1) → C(Icc a b, ℝ))
    (hp : ∀ j : Fin k, HasDerivIcc hab (p j.castSucc) (p j.succ)) : ContDiffMapIcc hab k :=
  ⟨WithLp.toLp 1 p, hp⟩

@[simp]
theorem deriv_mk (hab : a ≤ b) {k : ℕ} (p : Fin (k + 1) → C(Icc a b, ℝ))
    (hp : ∀ j : Fin k, HasDerivIcc hab (p j.castSucc) (p j.succ)) (j : Fin (k + 1)) :
    (mk hab p hp).deriv j = p j := rfl

/-- Taking the `j`-th derivative, `Cᵏ[a, b] → C([a, b], ℝ)`, as a bounded linear map of norm at
most `1`. -/
noncomputable def derivCLM (hab : a ≤ b) (k : ℕ) (j : Fin (k + 1)) :
    ContDiffMapIcc hab k →L[ℝ] C(Icc a b, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun u => u.deriv j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    1 fun u => (norm_deriv_le u j).trans_eq (one_mul _).symm

@[simp]
theorem derivCLM_apply (hab : a ≤ b) (k : ℕ) (j : Fin (k + 1)) (u : ContDiffMapIcc hab k) :
    derivCLM hab k j u = u.deriv j := rfl

/-- **Differentiation `d/dx : Cᵏ⁺¹[a, b] → Cᵏ[a, b]`**, which on the tuple of derivatives is the
shift dropping the zeroth entry. -/
def shift (u : ContDiffMapIcc hab (k + 1)) : ContDiffMapIcc hab k :=
  mk hab (fun j => u.deriv j.succ) fun j => by
    have h := u.hasDerivIcc j.succ
    rwa [← Fin.succ_castSucc] at h

@[simp]
theorem deriv_shift (u : ContDiffMapIcc hab (k + 1)) (j : Fin (k + 1)) :
    (shift u).deriv j = u.deriv j.succ := rfl

/-- Differentiation `d/dx : Cᵏ⁺¹[a, b] → Cᵏ[a, b]` as a bounded linear map of norm at most `1`. -/
noncomputable def shiftCLM (hab : a ≤ b) (k : ℕ) :
    ContDiffMapIcc hab (k + 1) →L[ℝ] ContDiffMapIcc hab k :=
  LinearMap.mkContinuous
    { toFun := shift, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    1 fun u => by
      simp only [one_mul, norm_def]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.image_subset_iff.2 fun _ _ => Finset.mem_univ _)
        (fun _ _ _ => norm_nonneg _) |>.trans_eq' (by
          rw [Finset.sum_image fun _ _ _ _ h => Fin.succ_injective _ h]
          rfl)

@[simp]
theorem shiftCLM_apply (hab : a ≤ b) (k : ℕ) (u : ContDiffMapIcc hab (k + 1)) :
    shiftCLM hab k u = shift u := rfl

/-- The `j`-th entry of the tuple is the `j`-th iterated derivative of `u` within `[a, b]`.  This
is what makes the representation faithful: `Cᵏ[a, b]` really is a space of functions, the higher
entries being determined by the zeroth.  A nondegenerate interval is needed, since a derivative
within a one-point set is not determined. -/
theorem deriv_eq_iteratedDerivWithin (hlt : a < b) (u : ContDiffMapIcc hab k) :
    ∀ {j : ℕ} (hj : j < k + 1) (t : Icc a b),
      u.deriv ⟨j, hj⟩ t = iteratedDerivWithin j u.extend (Icc a b) t := by
  intro j
  induction j with
  | zero =>
    intro hj t
    rw [iteratedDerivWithin_zero, extend_val]
    rfl
  | succ j ih =>
    intro hj t
    have hjk : j < k := by omega
    have hj' : j < k + 1 := by omega
    have hderiv : HasDerivWithinAt (iteratedDerivWithin j u.extend (Icc a b))
        (u.deriv ⟨j + 1, hj⟩ t) (Icc a b) t := by
      have h := u.hasDerivIcc ⟨j, hjk⟩ t
      rw [show (⟨j, hjk⟩ : Fin k).castSucc = ⟨j, hj'⟩ from rfl,
        show (⟨j, hjk⟩ : Fin k).succ = ⟨j + 1, hj⟩ from rfl] at h
      refine h.congr (fun y hy => ?_) ?_
      · rw [ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem hab _ hy, ih hj' ⟨y, hy⟩]
      · rw [ContinuousMap.coe_IccExtend, Set.IccExtend_val, ih hj' t]
    rw [iteratedDerivWithin_succ, ← hderiv.derivWithin (uniqueDiffOn_Icc hlt t t.2)]

/-- The derivative of `u ∈ Cᵏ⁺¹[a, b]` within `[a, b]`, at every point of `[a, b]` including the
two endpoints, is the first entry of the tuple. -/
theorem hasDerivWithinAt_extend (u : ContDiffMapIcc hab (k + 1)) (t : Icc a b) :
    HasDerivWithinAt u.extend (u.deriv 1 t) (Icc a b) t := by
  have h := u.hasDerivIcc 0 t
  rwa [show (0 : Fin (k + 1)).castSucc = 0 from rfl,
    show (0 : Fin (k + 1)).succ = 1 from rfl] at h

/-- An element of `Cᵏ[a, b]` is, as a function, `k` times continuously differentiable on `[a, b]`,
which is the book's definition of the space. -/
theorem contDiffOn (hlt : a < b) (u : ContDiffMapIcc hab k) :
    ContDiffOn ℝ k u.extend (Icc a b) := by
  induction k with
  | zero => exact contDiffOn_zero.2 u.extend.continuous.continuousOn
  | succ k ih =>
    have hcongr : ∀ t ∈ Icc a b,
        derivWithin u.extend (Icc a b) t = (shift u).extend t := by
      intro t ht
      rw [(u.hasDerivWithinAt_extend ⟨t, ht⟩).derivWithin (uniqueDiffOn_Icc hlt t ht),
        extend_of_mem]
      rfl
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by push_cast; ring,
      contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hlt)]
    exact ⟨fun t ht => (u.hasDerivWithinAt_extend ⟨t, ht⟩).differentiableWithinAt,
      fun h => absurd h (by simp), (ih (shift u)).congr hcongr⟩

@[simp]
theorem coe_add (u v : ContDiffMapIcc hab k) (t : Icc a b) : (u + v) t = u t + v t := rfl

@[simp]
theorem coe_smul (c : ℝ) (u : ContDiffMapIcc hab k) (t : Icc a b) : (c • u) t = c * u t := rfl

@[simp]
theorem coe_zero (t : Icc a b) : (0 : ContDiffMapIcc hab k) t = 0 := rfl

/-- One half of the equivalence between the norm `∑_{j ≤ k} ‖u⁽ʲ⁾‖_∞` carried here and the maximum
`max_{j ≤ k} ‖u⁽ʲ⁾‖_∞` that Atkinson and Han, *Theoretical Numerical Analysis*, 3rd edition, §1.4
uses instead. -/
theorem iSup_norm_deriv_le_norm (u : ContDiffMapIcc hab k) : ⨆ j, ‖u.deriv j‖ ≤ ‖u‖ :=
  ciSup_le fun j => norm_deriv_le u j

/-- The other half of the equivalence with the maximum norm of Atkinson and Han, *Theoretical
Numerical Analysis*, 3rd edition, §1.4: the sum of the `k + 1` supremum norms is at most `k + 1`
times their maximum. -/
theorem norm_le_iSup_norm_deriv (u : ContDiffMapIcc hab k) :
    ‖u‖ ≤ (k + 1) * ⨆ j, ‖u.deriv j‖ := by
  rw [norm_def]
  calc ∑ j, ‖u.deriv j‖ ≤ ∑ _j : Fin (k + 1), ⨆ i, ‖u.deriv i‖ :=
        Finset.sum_le_sum fun j _ =>
          le_ciSup (f := fun i => ‖u.deriv i‖) (Finite.bddAbove_range _) j
    _ = (k + 1) * ⨆ j, ‖u.deriv j‖ := by simp [Finset.sum_const]

/-- `C⁰[a, b]` is `C([a, b], ℝ)`: a tuple of length one carries no condition. -/
def ofContinuousMap (hab : a ≤ b) (f : C(Icc a b, ℝ)) : ContDiffMapIcc hab 0 :=
  mk hab (fun _ => f) fun j => j.elim0

@[simp]
theorem deriv_ofContinuousMap (hab : a ≤ b) (f : C(Icc a b, ℝ)) (j : Fin 1) :
    (ofContinuousMap hab f).deriv j = f := rfl

theorem ofContinuousMap_deriv (u : ContDiffMapIcc hab 0) : ofContinuousMap hab (u.deriv 0) = u :=
  ext fun j => by rw [Fin.fin_one_eq_zero j]; rfl

/-- On a nondegenerate interval an element of `Cᵏ[a, b]` is determined by the function it is: the
higher entries of the tuple are its iterated derivatives. -/
theorem coe_injective (hlt : a < b) :
    Function.Injective (fun u : ContDiffMapIcc hab k => ⇑u) := by
  intro u v huv
  have hext : u.extend = v.extend := by
    ext t
    simp only [extend, ContinuousMap.coe_IccExtend, Set.IccExtend, Function.comp_apply]
    exact congrFun huv _
  refine ext fun j => ContinuousMap.ext fun t => ?_
  rw [show j = ⟨(j : ℕ), j.2⟩ from rfl, u.deriv_eq_iteratedDerivWithin hlt j.2 t,
    v.deriv_eq_iteratedDerivWithin hlt j.2 t, hext]

/-- **Every function that is `k` times continuously differentiable on `[a, b]` is an element of
`Cᵏ[a, b]`**: the tuple of its iterated derivatives within `[a, b]`.  Together with
`ContDiffMapIcc.contDiffOn` this says that `Cᵏ[a, b]` is exactly the space Atkinson and Han,
*Theoretical Numerical Analysis*, 3rd edition, §1.4 defines — no more and no less. -/
noncomputable def ofContDiffOn (hab : a ≤ b) (hlt : a < b) {k : ℕ} {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ k f (Icc a b)) : ContDiffMapIcc hab k :=
  mk hab
    (fun j => ⟨(Icc a b).domRestrict (iteratedDerivWithin j f (Icc a b)),
      (hf.continuousOn_iteratedDerivWithin (mod_cast Nat.lt_succ_iff.1 j.2)
        (uniqueDiffOn_Icc hlt)).domRestrict⟩)
    fun j t => by
      have hd : DifferentiableOn ℝ (iteratedDerivWithin (j : ℕ) f (Icc a b)) (Icc a b) :=
        hf.differentiableOn_iteratedDerivWithin (mod_cast j.2) (uniqueDiffOn_Icc hlt)
      have h := ((hd t t.2).hasDerivWithinAt : HasDerivWithinAt _
        (derivWithin (iteratedDerivWithin (j : ℕ) f (Icc a b)) (Icc a b) t) (Icc a b) (t : ℝ))
      rw [← iteratedDerivWithin_succ] at h
      refine h.congr (fun y hy => ?_) ?_ |>.congr_deriv rfl
      · rw [ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem hab _ hy]; rfl
      · rw [ContinuousMap.coe_IccExtend, Set.IccExtend_val]; rfl

@[simp]
theorem deriv_ofContDiffOn (hab : a ≤ b) (hlt : a < b) {k : ℕ} {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ k f (Icc a b)) (j : Fin (k + 1)) (t : Icc a b) :
    (ofContDiffOn hab hlt hf).deriv j t = iteratedDerivWithin j f (Icc a b) t := rfl

@[simp]
theorem coe_ofContDiffOn (hab : a ≤ b) (hlt : a < b) {k : ℕ} {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ k f (Icc a b)) (t : Icc a b) : ofContDiffOn hab hlt hf t = f t := rfl

/-- Prepending an antiderivative: the element of `Cᵏ⁺¹[a, b]` whose derivative is `u` and whose
value at `a` is `c`.  Together with `ContDiffMapIcc.shift` it exhibits `Cᵏ⁺¹[a, b]` as
`Cᵏ[a, b] × ℝ`. -/
noncomputable def cons (u : ContDiffMapIcc hab k) (c : ℝ) : ContDiffMapIcc hab (k + 1) :=
  mk hab (Fin.cons (antideriv hab (u.deriv 0) c) u.deriv) fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hasDerivIcc_antideriv hab (u.deriv 0) c
    · simpa [← Fin.succ_castSucc] using u.hasDerivIcc j

@[simp]
theorem deriv_cons_zero (u : ContDiffMapIcc hab k) (c : ℝ) :
    (cons u c).deriv 0 = antideriv hab (u.deriv 0) c := rfl

@[simp]
theorem deriv_cons_succ (u : ContDiffMapIcc hab k) (c : ℝ) (j : Fin (k + 1)) :
    (cons u c).deriv j.succ = u.deriv j := rfl

@[simp]
theorem shift_cons (u : ContDiffMapIcc hab k) (c : ℝ) : shift (cons u c) = u := by
  ext j; rfl

@[simp]
theorem cons_left (u : ContDiffMapIcc hab k) (c : ℝ) :
    cons u c ⟨a, left_mem_Icc.2 hab⟩ = c := antideriv_left hab _ c

theorem cons_shift (v : ContDiffMapIcc hab (k + 1)) :
    cons (shift v) (v ⟨a, left_mem_Icc.2 hab⟩) = v := by
  refine ext fun j => ?_
  refine Fin.cases ?_ (fun _ => rfl) j
  have h := (v.hasDerivIcc 0).eq_antideriv
  rw [show (0 : Fin (k + 1)).castSucc = 0 from rfl,
    show (0 : Fin (k + 1)).succ = 1 from rfl] at h
  exact h.symm

/-- Evaluating the `j`-th derivative at a point of `[a, b]` is continuous on `Cᵏ[a, b]`.  This is
the one ingredient the closedness of `ContDiffMapIcc.zeroBoundary` and of
`ContDiffMapIcc.periodicBoundary` share: both subspaces are cut out by equations between such
evaluations. -/
theorem continuous_deriv_eval (hab : a ≤ b) (k : ℕ) (j : Fin (k + 1)) (t : Icc a b) :
    Continuous fun u : ContDiffMapIcc hab k => u.deriv j t :=
  (continuous_eval_const t).comp (derivCLM hab k j).continuous

/-- Evaluation at a point of `[a, b]` is continuous on `Cᵏ[a, b]`. -/
theorem continuous_eval (hab : a ≤ b) (k : ℕ) (t : Icc a b) :
    Continuous fun u : ContDiffMapIcc hab k => u t :=
  continuous_deriv_eval hab k 0 t

/-- The subspace `Cᵏ₀[a, b] = {v ∈ Cᵏ[a, b] : v a = v b = 0}` of the elements vanishing at both
endpoints.  For `k = 2` on `[0, 1]` this is the space `C²₀[0, 1]` in which the two-point boundary
value problem `u'' = f(t, u)`, `u(0) = u(1) = 0`, is posed (Atkinson and Han, *Theoretical
Numerical Analysis*, 3rd edition, §5.4.2). -/
def zeroBoundary (hab : a ≤ b) (k : ℕ) : Submodule ℝ (ContDiffMapIcc hab k) where
  carrier := {u | u ⟨a, left_mem_Icc.2 hab⟩ = 0 ∧ u ⟨b, right_mem_Icc.2 hab⟩ = 0}
  add_mem' hu hv := ⟨by simp [hu.1, hv.1], by simp [hu.2, hv.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' c _ hu := ⟨by simp [hu.1], by simp [hu.2]⟩

@[simp]
theorem mem_zeroBoundary {u : ContDiffMapIcc hab k} :
    u ∈ zeroBoundary hab k ↔
      u ⟨a, left_mem_Icc.2 hab⟩ = 0 ∧ u ⟨b, right_mem_Icc.2 hab⟩ = 0 := Iff.rfl

/-- `Cᵏ₀[a, b]` is closed in `Cᵏ[a, b]`, being cut out by two continuous conditions. -/
theorem isClosed_zeroBoundary (hab : a ≤ b) (k : ℕ) :
    IsClosed (zeroBoundary hab k : Set (ContDiffMapIcc hab k)) := by
  have hset : (zeroBoundary hab k : Set (ContDiffMapIcc hab k)) =
      {u : ContDiffMapIcc hab k | u ⟨a, left_mem_Icc.2 hab⟩ = 0} ∩
        {u : ContDiffMapIcc hab k | u ⟨b, right_mem_Icc.2 hab⟩ = 0} := rfl
  rw [hset]
  exact (isClosed_eq (continuous_eval hab k _) continuous_const).inter
    (isClosed_eq (continuous_eval hab k _) continuous_const)

/-- `Cᵏ₀[a, b]` is a Banach space, being a closed subspace of one. -/
instance : CompleteSpace (zeroBoundary hab k) := by
  have : IsClosed (zeroBoundary hab k : Set (ContDiffMapIcc hab k)) := isClosed_zeroBoundary hab k
  infer_instance

/-! ### Periodic boundary conditions -/

/-- The subspace of `Cᵏ[a, b]` cut out by matching the values of *every* derivative up to order `k`
at the two endpoints, `u⁽ʲ⁾(a) = u⁽ʲ⁾(b)` for `j ≤ k`.

Its elements are exactly the restrictions to one period of the `(b - a)`-periodic functions on `ℝ`
of class `Cᵏ` — the space that Atkinson and Han, *Theoretical Numerical Analysis*, 3rd edition,
§1.2 write `C_p^k(T)` — which is `ContDiffMapIcc.exists_periodic_contDiff` in one direction and
`ContDiffMapIcc.ofContDiff_mem_periodicBoundary` in the other.  Matching *all* orders up to `k`,
and not merely the values, is what makes the periodic extension `Cᵏ` rather than only continuous.

At `k = 0` this agrees with reading `C_p(T)` as `C(AddCircle T, ℝ)`: a continuous function on the
circle is the same thing as a continuous function on `[a, b]` taking equal values at the two ends.
The two readings do not conflict, and the circle one has no higher-order analogue here because
Mathlib carries no differential calculus on `AddCircle`. -/
def periodicBoundary (hab : a ≤ b) (k : ℕ) : Submodule ℝ (ContDiffMapIcc hab k) where
  carrier := {u | ∀ j, u.deriv j ⟨a, left_mem_Icc.2 hab⟩ = u.deriv j ⟨b, right_mem_Icc.2 hab⟩}
  add_mem' hu hv j := by simp [hu j, hv j]
  zero_mem' _ := rfl
  smul_mem' c _ hu j := by simp [hu j]

@[simp]
theorem mem_periodicBoundary {u : ContDiffMapIcc hab k} :
    u ∈ periodicBoundary hab k ↔
      ∀ j, u.deriv j ⟨a, left_mem_Icc.2 hab⟩ = u.deriv j ⟨b, right_mem_Icc.2 hab⟩ := Iff.rfl

/-- The periodic boundary conditions are closed in `Cᵏ[a, b]`: like `zeroBoundary`, the subspace is
cut out by equations between derivative evaluations, and each of those is continuous by
`ContDiffMapIcc.continuous_deriv_eval`. -/
theorem isClosed_periodicBoundary (hab : a ≤ b) (k : ℕ) :
    IsClosed (periodicBoundary hab k : Set (ContDiffMapIcc hab k)) := by
  have hset : (periodicBoundary hab k : Set (ContDiffMapIcc hab k)) =
      ⋂ j : Fin (k + 1), {u : ContDiffMapIcc hab k |
        u.deriv j ⟨a, left_mem_Icc.2 hab⟩ = u.deriv j ⟨b, right_mem_Icc.2 hab⟩} := by
    ext u; simp [Set.mem_iInter]
  rw [hset]
  exact isClosed_iInter fun j =>
    isClosed_eq (continuous_deriv_eval hab k j _) (continuous_deriv_eval hab k j _)

/-- The periodic `Cᵏ` functions on `[a, b]` form a Banach space, being a closed subspace of the
Banach space `Cᵏ[a, b]`. -/
instance : CompleteSpace (periodicBoundary hab k) := by
  have : IsClosed (periodicBoundary hab k : Set (ContDiffMapIcc hab k)) :=
    isClosed_periodicBoundary hab k
  infer_instance

/-- The restriction to `[a, b]` of a function that is `k` times continuously differentiable on all
of `ℝ`, as an element of `Cᵏ[a, b]`: the tuple of its iterated derivatives.

Unlike `ContDiffMapIcc.ofContDiffOn` this needs no nondegeneracy hypothesis, the derivatives being
the global `iteratedDeriv` rather than `iteratedDerivWithin`. -/
noncomputable def ofContDiff (hab : a ≤ b) {k : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ k f) :
    ContDiffMapIcc hab k :=
  mk hab
    (fun j => ⟨(Icc a b).domRestrict (iteratedDeriv j f),
      (hf.continuous_iteratedDeriv j (mod_cast Nat.lt_succ_iff.1 j.2)).comp continuous_subtype_val⟩)
    fun j t => by
      have hd : Differentiable ℝ (iteratedDeriv (j : ℕ) f) :=
        hf.differentiable_iteratedDeriv j (mod_cast j.2)
      have h : HasDerivAt (iteratedDeriv (j : ℕ) f)
          (iteratedDeriv ((j : ℕ) + 1) f (t : ℝ)) (t : ℝ) := by
        rw [iteratedDeriv_succ]
        exact (hd (t : ℝ)).hasDerivAt
      refine h.hasDerivWithinAt.congr (fun y hy => ?_) ?_
      · rw [ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem hab _ hy]; rfl
      · rw [ContinuousMap.coe_IccExtend, Set.IccExtend_val]; rfl

@[simp]
theorem deriv_ofContDiff (hab : a ≤ b) {k : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ k f)
    (j : Fin (k + 1)) (t : Icc a b) :
    (ofContDiff hab hf).deriv j t = iteratedDeriv j f t := rfl

@[simp]
theorem coe_ofContDiff (hab : a ≤ b) {k : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ k f) (t : Icc a b) :
    ofContDiff hab hf t = f t := rfl

/-- The derivative of a periodic real function is periodic.  A general fact, and an upstreaming
candidate: Mathlib has no periodicity lemma for `deriv`. -/
theorem _root_.Function.Periodic.deriv {f : ℝ → ℝ} {T : ℝ} (h : Function.Periodic f T) :
    Function.Periodic (_root_.deriv f) T := by
  intro x
  have hfun : (fun y => f (y + T)) = f := funext h
  have := deriv_comp_add_const f T x
  rw [hfun] at this
  exact this.symm

/-- Every iterated derivative of a periodic function is periodic. -/
theorem _root_.Function.Periodic.iteratedDeriv {f : ℝ → ℝ} {T : ℝ}
    (h : Function.Periodic f T) (n : ℕ) : Function.Periodic (iteratedDeriv n f) T := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- **The restriction of a `(b - a)`-periodic `Cᵏ` function on `ℝ` satisfies the periodic boundary
conditions.**  Together with `ContDiffMapIcc.exists_periodic_contDiff` this identifies
`ContDiffMapIcc.periodicBoundary` with the periodic `Cᵏ` functions. -/
theorem ofContDiff_mem_periodicBoundary (hab : a ≤ b) {k : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ k f)
    (hper : Function.Periodic f (b - a)) : ofContDiff hab hf ∈ periodicBoundary hab k := by
  intro j
  have h := hper.iteratedDeriv j a
  simp only [deriv_ofContDiff]
  rw [show a + (b - a) = b by ring] at h
  exact h.symm

/-- **Every element of `ContDiffMapIcc.periodicBoundary` is the restriction of a `(b - a)`-periodic
function on `ℝ` of class `Cᵏ`**, the converse of
`ContDiffMapIcc.ofContDiff_mem_periodicBoundary`.  The two together say that the periodic boundary
conditions describe exactly the periodic `Cᵏ` functions read on one period.

The extension is built by integrating downwards rather than by gluing translates, which is what
avoids a theorem about `Cᵏ` functions glued along a point.  The top derivative is extended
periodically as a *continuous* function, which needs only its two endpoint values to agree; each
lower one is then recovered as `x ↦ u⁽ʲ⁾(a) + ∫ₐˣ (the extension of u⁽ʲ⁺¹⁾)`, which is
automatically one degree smoother, and is periodic exactly because the integral of the extension of
`u⁽ʲ⁺¹⁾` over one period is `u⁽ʲ⁾(b) - u⁽ʲ⁾(a) = 0`.  So the matching at order `j + 1` is what
makes the extension of `u⁽ʲ⁾` periodic, and the matching at all orders up to `k` is used exactly
once each. -/
theorem exists_periodic_contDiff (hlt : a < b) :
    ∀ {k : ℕ} (u : ContDiffMapIcc hab k), u ∈ periodicBoundary hab k →
      ∃ f : ℝ → ℝ, Function.Periodic f (b - a) ∧ ContDiff ℝ k f ∧ ∀ t : Icc a b, f t = u t := by
  have hT : (0 : ℝ) < b - a := sub_pos.2 hlt
  have hab' : a + (b - a) = b := by ring
  intro k
  induction k with
  | zero =>
    intro u hu
    have hFact : Fact (0 < b - a) := ⟨hT⟩
    have hcircle : ((b : ℝ) : AddCircle (b - a)) = ((a : ℝ) : AddCircle (b - a)) := by
      have h := AddCircle.coe_add_period (b - a) a
      rwa [hab'] at h
    have hend : u.extend a = u.extend (a + (b - a)) := by
      rw [hab', extend_of_mem u (left_mem_Icc.2 hab), extend_of_mem u (right_mem_Icc.2 hab)]
      exact hu 0
    have hcont : Continuous fun x : ℝ =>
        AddCircle.liftIco (b - a) a u.extend ((x : ℝ) : AddCircle (b - a)) :=
      (AddCircle.liftIco_continuous hend u.extend.continuous.continuousOn).comp
        (AddCircle.continuous_mk' _)
    have hper : Function.Periodic
        (fun x : ℝ => AddCircle.liftIco (b - a) a u.extend ((x : ℝ) : AddCircle (b - a)))
        (b - a) := by
      intro x; simp only; rw [AddCircle.coe_add_period]
    have hval : ∀ t : Icc a b,
        AddCircle.liftIco (b - a) a u.extend ((t : ℝ) : AddCircle (b - a)) = u t := by
      intro t
      rcases eq_or_lt_of_le t.2.2 with hb | hb
      · rw [show ((t : ℝ) : AddCircle (b - a)) = ((a : ℝ) : AddCircle (b - a)) by
          rw [hb]; exact hcircle,
          AddCircle.liftIco_coe_apply (by rw [hab']; exact ⟨le_rfl, hlt⟩),
          extend_of_mem u (left_mem_Icc.2 hab),
          show t = (⟨b, right_mem_Icc.2 hab⟩ : Icc a b) from Subtype.ext hb]
        exact hu 0
      · rw [AddCircle.liftIco_coe_apply ⟨t.2.1, by rw [hab']; exact hb⟩]
        exact extend_val u t
    exact ⟨_, hper, contDiff_zero.2 hcont, hval⟩
  | succ k ih =>
    intro u hu
    obtain ⟨g, hgper, hgC, hgeq⟩ := ih (shift u) fun j => hu j.succ
    have hgper' : Function.Periodic g (b - a) := hgper
    have hgcont : Continuous g := hgC.continuous
    have hgEq : Set.EqOn g (ContinuousMap.IccExtend hab (u.deriv 1)) (Icc a b) := by
      intro y hy
      rw [ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem hab _ hy]
      exact hgeq ⟨y, hy⟩
    have hchain : ContinuousMap.HasDerivIcc hab (u.deriv 0) (u.deriv 1) := u.hasDerivIcc 0
    have hderiv : ∀ x : ℝ, HasDerivAt
        (fun y : ℝ => u.deriv 0 ⟨a, left_mem_Icc.2 hab⟩ + ∫ s in a..y, g s) (g x) x :=
      fun x => ((hgcont.integral_hasStrictDerivAt a x).hasDerivAt).const_add _
    have hval : ∀ t : Icc a b,
        (u.deriv 0 ⟨a, left_mem_Icc.2 hab⟩ + ∫ s in a..(t : ℝ), g s) = u t := by
      intro t
      have hsub : Set.uIcc a (t : ℝ) ⊆ Icc a b := by
        rw [Set.uIcc_of_le t.2.1]
        exact Icc_subset_Icc le_rfl t.2.2
      rw [intervalIntegral.integral_congr fun y hy => hgEq (hsub hy), hchain.integral_eq t]
      ring
    have hzero : ∫ s in a..b, g s = 0 := by
      have h1 := hval ⟨b, right_mem_Icc.2 hab⟩
      have h0 := hu 0
      simp only at h1 h0
      linarith
    have hper : Function.Periodic
        (fun y : ℝ => u.deriv 0 ⟨a, left_mem_Icc.2 hab⟩ + ∫ s in a..y, g s) (b - a) := by
      intro x
      simp only
      have hsplit : (∫ s in a..x, g s) + (∫ s in x..(x + (b - a)), g s)
          = ∫ s in a..(x + (b - a)), g s :=
        intervalIntegral.integral_add_adjacent_intervals
          (hgcont.intervalIntegrable _ _) (hgcont.intervalIntegrable _ _)
      rw [← hsplit, Function.Periodic.intervalIntegral_add_eq hgper' x a, hab', hzero]
      ring
    have hsmooth : ContDiff ℝ (k + 1 : ℕ)
        (fun y : ℝ => u.deriv 0 ⟨a, left_mem_Icc.2 hab⟩ + ∫ s in a..y, g s) := by
      rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by push_cast; ring,
        contDiff_succ_iff_deriv]
      refine ⟨fun x => (hderiv x).differentiableAt, fun h => absurd h (by simp), ?_⟩
      rw [funext fun x => (hderiv x).deriv]
      exact hgC
    exact ⟨_, hper, hsmooth, hval⟩

end ContDiffMapIcc
