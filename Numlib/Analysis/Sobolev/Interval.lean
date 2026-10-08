/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/MultiIndex.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Numlib.Analysis.Calculus.ContDiffMapIcc
import Numlib.Analysis.Sobolev.Interval.Basic
import Numlib.Analysis.Sobolev.Interval.Higher
import Numlib.Analysis.Sobolev.Interval.Zero

/-!
# Sobolev spaces on an interval

`H^m(a, b) = W^{m,2}(a, b)` and `H^1_0(a, b)`, with the one-dimensional facts that have no
analogue in higher dimension: every function of `H^1(a, b)` has an absolutely continuous
representative, `H^1(a, b)` embeds in `C[a, b]`, and Poincaré's inequality on `H^1_0(a, b)` holds
with the explicit constant `(b - a)/√2`.

`SobolevInterval m a b` is *not* a new space: it is `SobolevIntervalLp m 2 (Opens.Ioo a b)` of
`Numlib/Analysis/Sobolev/Interval/Basic.lean`, that is, the multi-index Sobolev space
`SobolevMultiIndex ℝ (Module.Basis.singleton Unit ℝ) m 2 (Opens.Ioo a b) volume` of
`Numlib/Analysis/Sobolev/MultiIndex.lean`, read on `E = ℝ` with the one-element basis, so that
its components are the weak derivatives `u, u', …, u^{(m)}` in `L²(a, b)` and it is a Hilbert
space for the inner product `(u, v)_{H^m} = ∑_{j ≤ m} (u^{(j)}, v^{(j)})_{L²}` on the nose
(`SobolevMultiIndex.inner_eq`). `H^1_0(a, b)` is accordingly `SobolevIntervalLpZero 1 2 _`, the
closure of the test functions in the multi-index space. The weak derivative on an interval,
`HasWeakDerivOn f w (Opens.Ioo a b)`, and the general theory of `W^{m,p}(I)` on an arbitrary open
`I ⊆ ℝ` live in `Interval/Basic.lean`; this module is the bounded `p = 2` layer over it. The
general-`p` theory is spread over the modules of `Interval/`: `Basic` (the weak derivative, the
spaces `W^{m,p}(I)`, the continuous representative), `Extension` (the extension operator),
`Embedding` (`W^{1,p}(I) ↪ C(Ī)` and its compactness), `Density` (the density of `C_c^∞`),
`Higher` (`W^{m,p}` as an iterated `W^{1,p}`, `C^k[a, b] → W^{k,p}(a, b)`, Poincaré's
inequality at every `p`), `Zero` (`W_0^{1,p}(I)`, its boundary characterization and cut-offs),
`DifferenceQuotient` and `Dual` (`W^{-1,p'}`).

This module adds only what is specific to `p = 2` or to a bounded interval, and otherwise reuses
that API: `SobolevInterval.fn`, `SobolevInterval.rep` (the continuous representative),
`SobolevInterval.toContinuousMap`, `SobolevInterval.evalCLM` and their lemmas are aliases
(`export`) of the `SobolevIntervalLp` declarations, not copies; `SobolevInterval.seminorm`,
`derivL`, `derivCLM`, `inclusionCLM` and `mk` are abbreviations of them at `p = 2`, with the
bounded-interval argument convention `m a b`; and `SobolevInterval.deriv u j` is
`SobolevIntervalLp.deriv u j` with its codomain spelled `Lp ℝ 2 (volume.restrict (Ioo a b))`, the
spelling the `L²(a, b)` lemmas rewrite with (whence the one-line restatements of its basic
lemmas). The statements kept here are the `p = 2` constants (`(b - a)/√2`,
`(b - a)^{-1/2} + (b - a)^{1/2}`), the Hilbert-space identities, and the bounded-interval forms of
the representative lemmas, stated on `[a, b]` rather than on the closure of an open interval.

## Main definitions

* `SobolevInterval m a b`, the space `H^m(a, b)`, with `MemSobolevInterval f m a b` the
  corresponding predicate on functions, `SobolevInterval.deriv u j` the `j`-th weak derivative in
  `L²(a, b)`, and `SobolevInterval.seminorm m a b` the seminorm `|u|_{H^m} = ‖u^{(m)}‖_{L²}`;
* `SobolevInterval.toContinuousMap hab`, the embedding `H^1(a, b) ↪ C[a, b]`, sending `u` to
  its continuous representative, and `SobolevInterval.nodalCLM hab t ht`, the evaluation of that
  representative at one point of `[a, b]` as a bounded linear functional;
* `SobolevIntervalZero a b`, the space `H^1_0(a, b)`;
* `SobolevInterval.derivCLM m a b`, weak differentiation `H^{m+1}(a, b) → H^m(a, b)`, and
  `ContDiffMapIcc.toSobolevInterval`, the inclusion `C^k[a, b] → H^k(a, b)`.

## Main statements

* `hasWeakDerivOn_integral`: the antiderivative of an integrable function is weakly
  differentiable; with du Bois-Reymond's lemma `HasWeakDerivOn.exists_ae_eq_const` it gives
  `HasWeakDerivOn.exists_ae_eq_integral`, **the absolutely continuous representative**: a
  function with an integrable weak derivative `w` on `(a, b)` agrees almost everywhere with
  `c + ∫_a^x w`.
* `SobolevInterval.norm_toContinuousMap_le`: **`H^1(a, b) ↪ C[a, b]`** with the constant
  `(b - a)^{-1/2} + (b - a)^{1/2}`; `SobolevInterval.toContinuousMap_sub_eq_integral`, the
  fundamental theorem of calculus in `H^1(a, b)`;
  `SobolevInterval.integral_deriv_mul_add_mul_deriv`, integration by parts (the product rule is
  `SobolevIntervalLp.memSobolevIntervalLp_mul`).
* `SobolevIntervalZero.norm_deriv_zero_le`: **Poincaré's inequality** on `H^1_0(a, b)` with the
  constant `(b - a)/√2` ([quarteroni2000numerical] (12.16)), and `mem_sobolevIntervalZero_iff`,
  the characterization `H^1_0(a, b) = {u ∈ H^1(a, b) : u(a) = u(b) = 0}`
  ([quarteroni2000numerical] (12.42)).
* `memSobolevInterval_of_piecewise_contDiffOn`: continuous piecewise-`C¹` functions lie in
  `H^1(a, b)`, which is what puts the finite element spaces inside `H^1`.

## Implementation notes

The whole one-dimensional theory rests on the representation `f = c + ∫_a^x w`; everything else
is an elementary integral estimate on it. Mathlib supplies the calculus of absolutely continuous
functions on this pin: `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`,
the Lebesgue differentiation theorem `IntervalIntegrable.ae_hasDerivAt_integral`, and the
integration by parts `AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul`, so the
Fubini identities the planning round anticipated are not needed: an antiderivative is weakly
differentiable by integration by parts against a test function, and the product rule in `H^1`
is Mathlib's product rule for absolutely continuous functions.

The converse direction of the boundary characterization of `H^1_0(a, b)` — a function of
`H^1(a, b)` vanishing at both endpoints lies in the closure of the test functions — is the case
`p = 2` of `SobolevIntervalLpZero.mem_of_rep_frontier_eq_zero_of_bounded`.

Conventions: `a < b` is a hypothesis of every theorem that needs it, never of the definitions;
the measure is `volume.restrict (Ioo a b)`; the `L²(a, b)` type is
`Lp ℝ 2 (volume.restrict (Ioo a b))`.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace Topology

noncomputable section

/-! ### Finite sums in `L^p` -/

/-- The coercion of a finite sum in `L^p` is almost everywhere the sum of the coercions. Mathlib
has `lp.coeFn_sum` for the sequence spaces `lp E p`, but nothing for `MeasureTheory.Lp`. -/
theorem MeasureTheory.Lp.coeFn_sum {μ : Measure ℝ} (s : Finset ℕ) (F : ℕ → Lp ℝ 2 μ) :
    ⇑(∑ i ∈ s, F i) =ᵐ[μ] fun t ↦ ∑ i ∈ s, F i t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℝ 2 μ
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ s, F j), ih] with t h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert hi]

/-! ### Antiderivatives, and the absolutely continuous representative -/

section Integral

variable {a b : ℝ} {f w : ℝ → ℝ}

/-- The antiderivative of a function integrable on `(a, b)` is absolutely continuous on
`[a, b]`. -/
theorem absolutelyContinuousOnInterval_integral (hab : a ≤ b) (hw : IntegrableOn w (Ioo a b))
    (c : ℝ) : AbsolutelyContinuousOnInterval (fun x ↦ c + ∫ t in a..x, w t) a b :=
  (contDiffOn_const (c := c)).absolutelyContinuousOnInterval.fun_add
    (IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
      (hw.intervalIntegrable_of_Ioo (left_mem_Icc.2 hab) (right_mem_Icc.2 hab)) left_mem_uIcc)

/-- The derivative of the antiderivative of a function integrable on `(a, b)` is that function
almost everywhere on `(a, b]`: the Lebesgue differentiation theorem. -/
theorem ae_deriv_integral_eq (hab : a ≤ b) (hw : IntegrableOn w (Ioo a b)) (c : ℝ) :
    ∀ᵐ x, x ∈ Ioc a b → deriv (fun x ↦ c + ∫ t in a..x, w t) x = w x := by
  filter_upwards [(hw.intervalIntegrable_of_Ioo (left_mem_Icc.2 hab)
    (right_mem_Icc.2 hab)).ae_hasDerivAt_integral] with x hx hxab
  have := (hx (uIcc_of_le hab ▸ Ioc_subset_Icc_self hxab) a (uIcc_of_le hab ▸ left_mem_Icc.2 hab))
  exact ((hasDerivAt_const x c).add this).deriv.trans (zero_add _)

/-- **The antiderivative of an integrable function is weakly differentiable**: for `w`
integrable on `(a, b)` and any constant `c`, `w` is the weak derivative of `c + ∫_a^x w` on
`(a, b)`. The proof is integration by parts for absolutely continuous functions against a test
function, together with the Lebesgue differentiation theorem. -/
theorem hasWeakDerivOn_integral (hab : a ≤ b) (hw : IntegrableOn w (Ioo a b)) (c : ℝ) :
    HasWeakDerivOn (fun x ↦ c + ∫ t in a..x, w t) w (Opens.Ioo a b) := by
  set g : ℝ → ℝ := fun x ↦ c + ∫ t in a..x, w t with hg
  refine hasWeakDerivOn_iff.2
    ⟨((intervalIntegral.continuousOn_integral_of_integrableOn_Ioo hab hw c).mono
      Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo, hw.locallyIntegrableOn,
    fun φ ↦ ?_⟩
  have hφ : AbsolutelyContinuousOnInterval φ a b :=
    (φ.contDiff.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have key := hφ.integral_mul_deriv_eq_deriv_mul (absolutelyContinuousOnInterval_integral hab hw c)
  have hφa : φ a = 0 := φ.eq_zero_of_notMem (by simp)
  have hφb : φ b = 0 := φ.eq_zero_of_notMem (by simp)
  rw [hφa, hφb, zero_mul, zero_mul, sub_zero, zero_sub] at key
  have e1 : ∫ x in a..b, φ x * deriv g x = ∫ x in a..b, φ x * w x := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_deriv_integral_eq hab hw c] with x hx hxI
    rw [hx (by rwa [uIoc_of_le hab] at hxI)]
  rw [e1, intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at key
  exact neg_eq_iff_eq_neg.1 key.symm

/-- **The absolutely continuous representative**: a function with an integrable weak derivative
`w` on `(a, b)` agrees almost everywhere on `(a, b)` with `c + ∫_a^x w` for some constant `c`.
The difference of `f` and the antiderivative has weak derivative `0`, so it is almost everywhere
constant by du Bois-Reymond's lemma `HasWeakDerivOn.exists_ae_eq_const`. -/
theorem HasWeakDerivOn.exists_ae_eq_integral (hab : a < b) (h : HasWeakDerivOn f w (Opens.Ioo a b))
    (hw : IntegrableOn w (Ioo a b)) :
    ∃ c : ℝ, f =ᵐ[volume.restrict (Ioo a b)] fun x ↦ c + ∫ t in a..x, w t := by
  have h1 := hasWeakDerivOn_integral hab.le hw 0
  have h2 : HasWeakDerivOn (fun x ↦ f x - (0 + ∫ t in a..x, w t)) 0 (Opens.Ioo a b) :=
    (h.sub h1).congr_ae (Eventually.of_forall fun x ↦ rfl)
      (Eventually.of_forall fun x ↦ sub_self _)
  obtain ⟨c, hc⟩ := h2.exists_ae_eq_const ordConnected_Ioo
  refine ⟨c, hc.mono fun x hx ↦ ?_⟩
  simp only [zero_add] at hx ⊢
  linarith

/-- The absolutely continuous representative, as a function continuous on `[a, b]` that is the
integral of the weak derivative between any two points of `[a, b]`. -/
theorem HasWeakDerivOn.exists_continuousOn_ae_eq (hab : a < b)
    (h : HasWeakDerivOn f w (Opens.Ioo a b))
    (hw : IntegrableOn w (Ioo a b)) :
    ∃ g : ℝ → ℝ, ContinuousOn g (Icc a b) ∧ f =ᵐ[volume.restrict (Ioo a b)] g ∧
      ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, g y - g x = ∫ t in x..y, w t := by
  obtain ⟨c, hc⟩ := h.exists_ae_eq_integral hab hw
  refine ⟨_, intervalIntegral.continuousOn_integral_of_integrableOn_Ioo hab.le hw c, hc,
    fun x hx y hy ↦ ?_⟩
  rw [add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
    (hw.intervalIntegrable_of_Ioo (left_mem_Icc.2 hab.le) hy)
    (hw.intervalIntegrable_of_Ioo (left_mem_Icc.2 hab.le) hx)]

end Integral

/-! ### The space `H^m(a, b)` -/

section Space

/-- **The Sobolev space `H^m(a, b) = W^{m,2}(a, b)`**: the space `SobolevIntervalLp m 2 I` of
`Numlib/Analysis/Sobolev/Interval/Basic.lean` on `I = (a, b)`, that is, the multi-index Sobolev
space `SobolevMultiIndex` of `Numlib/Analysis/Sobolev/MultiIndex.lean` on `E = ℝ` with the
one-element basis, whose multi-indices of order at most `m` are the derivative orders `0, …, m`.
Being an `abbrev`, it inherits the `InnerProductSpace ℝ` and `CompleteSpace` instances of the
multi-index space, and the whole `SobolevIntervalLp` API applies to it: it is a Hilbert space for
the inner product `(u, v)_{H^m} = ∑_{j ≤ m} (u^{(j)}, v^{(j)})_{L²(a, b)}`
(`SobolevIntervalLp.inner_eq`). -/
abbrev SobolevInterval (m : ℕ) (a b : ℝ) : Type :=
  SobolevIntervalLp m 2 (Opens.Ioo a b)

/-- `MemSobolevInterval f m a b` says that the function `f` belongs to `H^m(a, b)`: it lies in
`L²(a, b)` together with its weak derivatives of orders `1, …, m`. -/
abbrev MemSobolevInterval (f : ℝ → ℝ) (m : ℕ) (a b : ℝ) : Prop :=
  MemSobolevIntervalLp f m 2 (Opens.Ioo a b)

variable {m : ℕ} {a b : ℝ} {f : ℝ → ℝ}

/-- Membership of `H^m(a, b)` unfolded: `f ∈ L²(a, b)`, and for every `j ≤ m` the `j`-th weak
derivative of `f` on `(a, b)` exists and lies in `L²(a, b)` (`memSobolevIntervalLp_iff` at
`p = 2`). -/
theorem memSobolevInterval_iff :
    MemSobolevInterval f m a b ↔ MemLp f 2 (volume.restrict (Ioo a b)) ∧ ∀ j ≤ m,
      ∃ w : ℝ → ℝ, HasWeakIteratedDerivOn j f w (Opens.Ioo a b) ∧
        MemLp w 2 (volume.restrict (Ioo a b)) :=
  memSobolevIntervalLp_iff

/-- `H^0(a, b)` is `L²(a, b)` (`memSobolevIntervalLp_zero_iff` at `p = 2`). -/
theorem memSobolevInterval_zero_iff :
    MemSobolevInterval f 0 a b ↔ MemLp f 2 (volume.restrict (Ioo a b)) :=
  memSobolevIntervalLp_zero_iff

/-- **The recursive description of `H^{m+1}(a, b)`**: a function lies in `H^{m+1}(a, b)` exactly
when it lies in `L²(a, b)` and has a weak derivative lying in `H^m(a, b)`
(`memSobolevIntervalLp_succ_iff` at `p = 2`). -/
theorem memSobolevInterval_succ_iff :
    MemSobolevInterval f (m + 1) a b ↔ MemLp f 2 (volume.restrict (Ioo a b)) ∧
      ∃ w : ℝ → ℝ, HasWeakDerivOn f w (Opens.Ioo a b) ∧ MemSobolevInterval w m a b :=
  memSobolevIntervalLp_succ_iff

/-- `H^1(a, b)` is the space of `L²(a, b)` functions with a weak derivative in `L²(a, b)`:
[quarteroni2000numerical] (12.42), without the boundary condition. -/
theorem memSobolevInterval_one_iff :
    MemSobolevInterval f 1 a b ↔ MemLp f 2 (volume.restrict (Ioo a b)) ∧
      ∃ w : ℝ → ℝ, HasWeakDerivOn f w (Opens.Ioo a b) ∧ MemLp w 2 (volume.restrict (Ioo a b)) :=
  memSobolevIntervalLp_one_iff

namespace SobolevInterval

/- `H^m(a, b)` is `W^{m,2}(a, b)`, so the general API of `SobolevIntervalLp` applies to it. The
names below that do not mention `L²(a, b)` are aliases of that API, not new declarations. -/
export SobolevIntervalLp (fn fn_mk seminorm_le_norm fn_inclusionCLM norm_derivCLM_le
  norm_inclusionCLM_le)

/-- The `j`-th weak derivative `u^{(j)}` of `u ∈ H^m(a, b)`, as an element of `L²(a, b)`:
`SobolevIntervalLp.deriv u j`, with its codomain spelled `Lp ℝ 2 (volume.restrict (Ioo a b))`
rather than `Lp ℝ 2 (volume.restrict ↑(Opens.Ioo a b))`. The two are definitionally equal, but
the lemmas about `L²(a, b)` (`norm_sq_eq_integral_sq`, `ae_restrict_iff' measurableSet_Ioo`, …)
rewrite only with the first spelling; this is the reason the basic lemmas about `deriv` are
restated below, each a one-line instance of its `SobolevIntervalLp` counterpart. -/
abbrev deriv (u : SobolevInterval m a b) (j : Fin (m + 1)) : Lp ℝ 2 (volume.restrict (Ioo a b)) :=
  SobolevIntervalLp.deriv u j

/-- The derivative of order `0` is the function itself. -/
theorem deriv_zero (u : SobolevInterval m a b) : ⇑(deriv u 0) = fn u := rfl

/-- The weak derivatives of a sum. -/
theorem deriv_add (u v : SobolevInterval m a b) (j : Fin (m + 1)) :
    deriv (u + v) j = deriv u j + deriv v j := rfl

/-- The weak derivatives of a scalar multiple. -/
theorem deriv_smul (c : ℝ) (u : SobolevInterval m a b) (j : Fin (m + 1)) :
    deriv (c • u) j = c • deriv u j := rfl

/-- The weak derivatives of a difference. -/
theorem deriv_sub (u v : SobolevInterval m a b) (j : Fin (m + 1)) :
    deriv (u - v) j = deriv u j - deriv v j := rfl

/-- The weak derivatives of the zero element vanish. -/
theorem deriv_zero_elem (j : Fin (m + 1)) : deriv (0 : SobolevInterval m a b) j = 0 := rfl

/-- An element of `H^m(a, b)` is determined by its weak derivatives of orders `0, …, m`. -/
theorem ext {u v : SobolevInterval m a b} (h : ∀ j, deriv u j = deriv v j) : u = v :=
  SobolevIntervalLp.ext h

/-- The `j`-th component of an element of `H^m(a, b)` is the `j`-th weak derivative of its
function. -/
theorem hasWeakIteratedDerivOn_deriv (u : SobolevInterval m a b) (j : Fin (m + 1)) :
    HasWeakIteratedDerivOn j (fn u) (deriv u j) (Opens.Ioo a b) :=
  SobolevIntervalLp.hasWeakIteratedDerivOn_deriv u j

/-- The weak derivatives of an element of `H^m(a, b)` form a chain: `u^{(j+1)}` is the weak
derivative of `u^{(j)}`. -/
theorem hasWeakDerivOn_deriv_succ (u : SobolevInterval m a b) (j : Fin m) :
    HasWeakDerivOn (deriv u j.castSucc) (deriv u j.succ) (Opens.Ioo a b) :=
  SobolevIntervalLp.hasWeakDerivOn_deriv_succ u j

/-- The function of `u ∈ H^1(a, b)` has the weak derivative `u'`. -/
theorem hasWeakDerivOn_fn (u : SobolevInterval 1 a b) :
    HasWeakDerivOn (fn u) (deriv u 1) (Opens.Ioo a b) :=
  SobolevIntervalLp.hasWeakDerivOn_fn u

/-- Each weak derivative is bounded by the `H^m` norm. -/
theorem norm_deriv_le (u : SobolevInterval m a b) (j : Fin (m + 1)) : ‖deriv u j‖ ≤ ‖u‖ :=
  SobolevIntervalLp.norm_deriv_le u j

/-- **The inner product of `H^m(a, b)`**: `(u, v)_{H^m} = ∑_{j ≤ m} (u^{(j)}, v^{(j)})_{L²(a, b)}`,
the inner product (10.34) of [quarteroni2000numerical]. -/
theorem inner_eq (u v : SobolevInterval m a b) :
    ⟪u, v⟫_ℝ = ∑ j : Fin (m + 1), ⟪deriv u j, deriv v j⟫_ℝ :=
  SobolevIntervalLp.inner_eq u v

/-- Building an element of `H^m(a, b)` from `L²(a, b)` functions `v 0, …, v m` of which `v j` is
the `j`-th weak derivative of `v 0`: `SobolevIntervalLp.mk`. -/
abbrev mk (v : Fin (m + 1) → Lp ℝ 2 (volume.restrict (Ioo a b)))
    (hv : ∀ j : Fin (m + 1), HasWeakIteratedDerivOn (j : ℕ) (v 0) (v j) (Opens.Ioo a b)) :
    SobolevInterval m a b :=
  SobolevIntervalLp.mk v hv

/-- The weak derivatives of `SobolevInterval.mk v hv` are the `v j`. -/
@[simp]
theorem deriv_mk (v : Fin (m + 1) → Lp ℝ 2 (volume.restrict (Ioo a b)))
    (hv : ∀ j : Fin (m + 1), HasWeakIteratedDerivOn (j : ℕ) (v 0) (v j) (Opens.Ioo a b))
    (j : Fin (m + 1)) :
    deriv (mk v hv) j = v j := rfl

/-- **The norm of `H^m(a, b)`**: `‖u‖² = ∑_{j ≤ m} ‖u^{(j)}‖²_{L²(a, b)}`, the norm (10.35) of
[quarteroni2000numerical]; the square of `SobolevIntervalLp.norm_eq_sum` at `p = 2`. -/
theorem norm_sq_eq (u : SobolevInterval m a b) :
    ‖u‖ ^ 2 = ∑ j : Fin (m + 1), ‖deriv u j‖ ^ 2 := by
  rw [← Submodule.norm_coe, PiLp.norm_sq_eq_of_L2,
    ← (SobolevIntervalLp.derivIndexEquiv m).sum_comp]
  rfl

/-- `‖u‖_{H^1} ≤ ‖u‖_{L²} + ‖u'‖_{L²}`: `SobolevIntervalLp.norm_le_sum_norm_deriv` at `m = 1`. -/
theorem norm_le_add_norm_deriv (u : SobolevInterval 1 a b) :
    ‖u‖ ≤ ‖deriv u 0‖ + ‖deriv u 1‖ := by
  have h := SobolevIntervalLp.norm_le_sum_norm_deriv u
  rwa [Fin.sum_univ_two] at h

/-- **The inner product of `H^1(a, b)` as an integral**:
`(u, v)_{H¹} = ∫_a^b (u'(x) v'(x) + u(x) v(x)) dx`. It is `inner_eq` with the two
`L²(a, b)` inner products written out, the sum of the integrands being integrable by
`MeasureTheory.L2.integrable_inner`. -/
theorem inner_eq_intervalIntegral (hab : a ≤ b) (u v : SobolevInterval 1 a b) :
    inner ℝ u v = ∫ x in a..b, (deriv u 1 x * deriv v 1 x + fn u x * fn v x) := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    inner_eq, Fin.sum_univ_two, L2.inner_def, L2.inner_def,
    ← integral_add (L2.integrable_inner _ _) (L2.integrable_inner _ _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [RCLike.inner_apply, deriv_zero]
  ring

variable (m a b) in
/-- The `j`-th weak derivative as a continuous linear map `H^m(a, b) → L²(a, b)`, of norm at most
one: `SobolevIntervalLp.derivL` at `p = 2`. -/
abbrev derivL (j : Fin (m + 1)) :
    SobolevInterval m a b →L[ℝ] Lp ℝ 2 (volume.restrict (Ioo a b)) :=
  SobolevIntervalLp.derivL m 2 (Opens.Ioo a b) j

/-- `SobolevInterval.derivL` is the weak derivative. -/
@[simp]
theorem derivL_apply (j : Fin (m + 1)) (u : SobolevInterval m a b) :
    derivL m a b j u = deriv u j :=
  rfl

variable (m a b) in
/-- **The Sobolev seminorm** `|u|_{H^m(a, b)} = ‖u^{(m)}‖_{L²(a, b)}`, bundled as a `Seminorm` so
that the seminorm forms of Céa's and Strang's lemmas apply to it; it is the `|·|_{H¹(0,1)}` of
[quarteroni2000numerical] (12.49), and `SobolevIntervalLp.seminorm` at `p = 2`. -/
abbrev seminorm : Seminorm ℝ (SobolevInterval m a b) :=
  SobolevIntervalLp.seminorm m 2 (Opens.Ioo a b)

/-- The seminorm is the `L²` norm of the top derivative. -/
theorem seminorm_apply (u : SobolevInterval m a b) : seminorm m a b u = ‖deriv u (Fin.last m)‖ :=
  rfl

variable (m a b) in
/-- **Weak differentiation `d/dx : H^{m+1}(a, b) → H^m(a, b)`** as a continuous linear map, of
norm at most one: `SobolevIntervalLp.derivCLM` at `p = 2`. -/
abbrev derivCLM : SobolevInterval (m + 1) a b →L[ℝ] SobolevInterval m a b :=
  SobolevIntervalLp.derivCLM m 2 (Opens.Ioo a b)

/-- The weak derivatives of `u'` are those of `u`, shifted by one. -/
@[simp]
theorem deriv_derivCLM (u : SobolevInterval (m + 1) a b) (j : Fin (m + 1)) :
    deriv (derivCLM m a b u) j = deriv u j.succ := rfl

variable (m a b) in
/-- **The inclusion `H^{m+1}(a, b) → H^m(a, b)`**, forgetting the top derivative, as a continuous
linear map of norm at most one: `SobolevIntervalLp.inclusionCLM` at `p = 2`. -/
abbrev inclusionCLM : SobolevInterval (m + 1) a b →L[ℝ] SobolevInterval m a b :=
  SobolevIntervalLp.inclusionCLM m 2 (Opens.Ioo a b)

/-- The weak derivatives of the inclusion of `u` are those of `u`. -/
@[simp]
theorem deriv_inclusionCLM (u : SobolevInterval (m + 1) a b) (j : Fin (m + 1)) :
    deriv (inclusionCLM m a b u) j = deriv u j.castSucc := rfl

end SobolevInterval

end Space

/-! ### Cauchy–Schwarz on an interval -/

section CauchySchwarz

variable {a b : ℝ}

/-- Cauchy–Schwarz for a set integral of an `L²(a, b)` function:
`|∫_s f| ≤ √|s| ‖f‖_{L²(a, b)}` for a measurable `s ⊆ (a, b)`. -/
theorem abs_setIntegral_le_sqrt_mul_norm (f : Lp ℝ 2 (volume.restrict (Ioo a b))) {s : Set ℝ}
    (hs : MeasurableSet s) (hsub : s ⊆ Ioo a b) :
    |∫ x in s, f x| ≤ Real.sqrt (volume.real s) * ‖f‖ := by
  have e1 : ∫ x in s, f x = ∫ x in s, f x ∂(volume.restrict (Ioo a b)) := by
    rw [Measure.restrict_restrict hs, inter_eq_left.2 hsub]
  rw [e1, ← L2.inner_indicatorConstLp_one hs (measure_ne_top _ _) f]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, norm_one, one_mul,
    measureReal_restrict_apply hs, inter_eq_left.2 hsub, Real.sqrt_eq_rpow]
  simp

/-- Cauchy–Schwarz for an interval integral of an `L²(a, b)` function:
`|∫_x^y f| ≤ √(y - x) ‖f‖_{L²(a, b)}` for `a ≤ x ≤ y ≤ b`. -/
theorem abs_intervalIntegral_le_sqrt_mul_norm (f : Lp ℝ 2 (volume.restrict (Ioo a b))) {x y : ℝ}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    |∫ t in x..y, f t| ≤ Real.sqrt (y - x) * ‖f‖ := by
  rw [intervalIntegral.integral_of_le hxy, integral_Ioc_eq_integral_Ioo]
  have := abs_setIntegral_le_sqrt_mul_norm f measurableSet_Ioo (Ioo_subset_Ioo hx.1 hy.2)
  rwa [Real.volume_real_Ioo_of_le hxy] at this

/-- The `L¹(a, b)` norm of an `L²(a, b)` function is at most `√(b - a)` times its `L²` norm. -/
theorem integral_abs_le_sqrt_mul_norm (hab : a ≤ b) (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    ∫ x in Ioo a b, |f x| ≤ Real.sqrt (b - a) * ‖f‖ := by
  have e1 : ∫ x in Ioo a b, |f x| = ∫ x in Ioo a b, (|f| : Lp ℝ 2 (volume.restrict (Ioo a b))) x :=
    integral_congr_ae (Lp.coeFn_abs f).symm
  rw [e1, ← norm_abs_eq_norm f, ← Real.volume_real_Ioo_of_le hab]
  exact (le_abs_self _).trans (abs_setIntegral_le_sqrt_mul_norm |f| measurableSet_Ioo subset_rfl)

open intervalIntegral in
open scoped Interval in
/-- **Cauchy–Schwarz for an interval integral**: `|∫_s^t g| ≤ √(v - u) √(∫_u^v g²)` for
`s, t ∈ [u, v]` and `g` square integrable on `[u, v]`. -/
theorem abs_intervalIntegral_le_sqrt_mul_sqrt {u v : ℝ} (huv : u ≤ v) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume u v) (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume u v)
    {s t : ℝ} (hs : s ∈ Icc u v) (ht : t ∈ Icc u v) :
    |∫ r in s..t, g r| ≤ √(v - u) * √(∫ r in u..v, g r ^ 2) := by
  have hsub : Ι s t ⊆ Ι u v := by
    rw [← uIcc_of_le huv] at hs ht
    exact uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hs ht)
  have hgabs : IntervalIntegrable (fun r => |g r|) volume u v := hg.abs
  -- reduce to the integral of `|g|` over the whole panel
  have h1 : |∫ r in s..t, g r| ≤ ∫ r in u..v, |g r| := by
    calc |∫ r in s..t, g r| ≤ ∫ r in Ι s t, |g r| := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm_uIoc (f := g)
      _ ≤ ∫ r in Ι u v, |g r| :=
          setIntegral_mono_set hgabs.def' (Filter.Eventually.of_forall fun r => abs_nonneg _)
            hsub.eventuallyLE
      _ = ∫ r in u..v, |g r| := by rw [uIoc_of_le huv, integral_of_le huv]
  -- Hölder with `p = q = 2` against the constant `1`
  have h2 : ∫ r in u..v, |g r| ≤ √(v - u) * √(∫ r in u..v, g r ^ 2) := by
    rw [integral_of_le huv, integral_of_le huv]
    have hmeas : AEStronglyMeasurable g (volume.restrict (Ioc u v)) := hg.1.aestronglyMeasurable
    have hgL2 : MemLp (fun r => |g r|) (ENNReal.ofReal 2) (volume.restrict (Ioc u v)) := by
      rw [ENNReal.ofReal_ofNat]
      exact ((memLp_two_iff_integrable_sq hmeas).2 hg2.1).abs
    have h1L2 : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) (volume.restrict (Ioc u v)) :=
      memLp_const 1
    have := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun _ => zero_le_one)
      (Filter.Eventually.of_forall fun _ => abs_nonneg _) h1L2 hgL2
    simp only [one_mul, Real.rpow_two, one_pow, sq_abs, ← Real.sqrt_eq_rpow] at this
    rwa [setIntegral_const, Real.volume_real_Ioc_of_le huv, smul_eq_mul, mul_one] at this
  exact h1.trans h2

end CauchySchwarz

/-! ### The continuous representative, and `H^1(a, b) ↪ C[a, b]` -/

section Embedding

variable {a b : ℝ}

namespace SobolevInterval

open SobolevIntervalLp (ordConnected_coe_Ioo closure_coe_Ioo)

/- The continuous representative `rep u` of `u ∈ H^1(a, b)` and the embedding
`toContinuousMap hab : H^1(a, b) → C[a, b]` are those of `W^{1,p}(a, b)`
(`Numlib/Analysis/Sobolev/Interval/Basic.lean`, `…/Interval/Embedding.lean`) at `p = 2`: `rep` and
the lemmas below whose exponent is fixed by an argument are aliases of them. What follows are
their bounded-interval forms (on `[a, b]` rather than on the closure of an open interval) and the
`p = 2` constant of the embedding. -/
export SobolevIntervalLp (rep toContinuousMap_apply coe_toContinuousMap_ae_eq
  toContinuousMap_eq_of_continuousOn absolutelyContinuousOnInterval_toContinuousMap
  exists_toContinuousMap_eq evalCLM_apply)

/-- **The embedding `H^1(a, b) ↪ C[a, b]`**, `u ↦` its continuous representative on `[a, b]`:
`SobolevIntervalLp.toContinuousMap` at `p = 2` (an abbreviation, so that the exponent is fixed).
Its norm is at most `(b - a)^{-1/2} + (b - a)^{1/2}` (`SobolevInterval.norm_toContinuousMap_le`);
for `H^m(a, b)` with `m ≥ 1`, compose with `SobolevInterval.inclusionCLM`. -/
abbrev toContinuousMap (hab : a < b) : SobolevInterval 1 a b →L[ℝ] C(Icc a b, ℝ) :=
  SobolevIntervalLp.toContinuousMap hab

/-- **Point evaluation on `H^1(a, b)`** (2.5.7), `ℓ_c(v) = v(c)` for `c ∈ [a, b]`, as a bounded
linear functional: `SobolevIntervalLp.evalCLM` at `p = 2`. This is Atkinson–Han's
Exercise 2.5.5. -/
abbrev evalCLM (hab : a < b) (c : Icc a b) : StrongDual ℝ (SobolevInterval 1 a b) :=
  SobolevIntervalLp.evalCLM hab c

/-- **The fundamental theorem of calculus in `H^1(a, b)`**: the embedding of `u` into `C[a, b]`
is the integral of `u'` between any two points of `[a, b]`. -/
theorem toContinuousMap_sub_eq_integral (hab : a < b) (u : SobolevInterval 1 a b)
    (x y : Icc a b) :
    toContinuousMap hab u y - toContinuousMap hab u x = ∫ t in (x : ℝ)..y, deriv u 1 t :=
  SobolevIntervalLp.toContinuousMap_sub_eq_integral hab u x y

/-- **The embedding `H^1(a, b) ↪ C([a, b], ℝ)` is injective**. -/
theorem toContinuousMap_injective (hab : a < b) :
    Function.Injective (toContinuousMap hab) :=
  SobolevIntervalLp.toContinuousMap_injective hab

/-- The continuous representative is continuous on `[a, b]`. -/
theorem continuousOn_rep (hab : a ≤ b) (u : SobolevInterval 1 a b) :
    ContinuousOn (rep u) (Icc a b) := by
  rcases hab.lt_or_eq with hab | rfl
  · exact SobolevIntervalLp.continuousOn_rep_Icc hab u
  · rw [Icc_self]
    exact continuousOn_singleton _ _

/-- The continuous representative is absolutely continuous on `[a, b]`. -/
theorem absolutelyContinuousOnInterval_rep (hab : a ≤ b) (u : SobolevInterval 1 a b) :
    AbsolutelyContinuousOnInterval (rep u) a b := by
  rcases hab.lt_or_eq with hab | rfl
  · exact SobolevIntervalLp.absolutelyContinuousOnInterval_rep (ordConnected_coe_Ioo a b) u
      (by rw [closure_coe_Ioo hab]; exact left_mem_Icc.2 hab.le)
      (by rw [closure_coe_Ioo hab]; exact right_mem_Icc.2 hab.le)
  · exact .refl _ _

/-- The classical derivative of the continuous representative is `u'` almost everywhere on
`(a, b]`. -/
theorem ae_deriv_rep_eq (u : SobolevInterval 1 a b) :
    ∀ᵐ x, x ∈ Ioc a b → _root_.deriv (rep u) x = deriv u 1 x := by
  have hb : ∀ᵐ t : ℝ, t ≠ b := by simp [ae_iff, measure_singleton]
  filter_upwards [SobolevIntervalLp.ae_deriv_rep_eq (ordConnected_coe_Ioo a b) u, hb]
    with x hx hxb hxI
  exact hx ⟨hxI.1, lt_of_le_of_ne hxI.2 hxb⟩

/-- The function of `u ∈ H^1(a, b)` agrees almost everywhere on `(a, b)` with its continuous
representative (`SobolevIntervalLp.fn_ae_eq_rep` on `(a, b)`). -/
theorem fn_ae_eq_rep (u : SobolevInterval 1 a b) :
    fn u =ᵐ[volume.restrict (Ioo a b)] rep u :=
  SobolevIntervalLp.fn_ae_eq_rep (ordConnected_coe_Ioo a b) u

/-- The continuous representative is canonical: any function continuous on `[a, b]` that agrees
almost everywhere with `u` on `(a, b)` is the representative on all of `[a, b]`. -/
theorem rep_eq_of_continuousOn (hab : a < b) (u : SobolevInterval 1 a b) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) (hu : fn u =ᵐ[volume.restrict (Ioo a b)] g) :
    EqOn (rep u) g (Icc a b) := by
  have h := SobolevIntervalLp.rep_eq_of_continuousOn (ordConnected_coe_Ioo a b) u (g := g)
    (by rwa [closure_coe_Ioo hab]) hu
  rwa [closure_coe_Ioo hab] at h

/-- The continuous representative of a sum, on `[a, b]`. -/
theorem rep_add (hab : a < b) (u v : SobolevInterval 1 a b) :
    EqOn (rep (u + v)) (rep u + rep v) (Icc a b) :=
  fun _ hx ↦ SobolevIntervalLp.rep_add_Icc hab u v hx

/-- The continuous representative of a scalar multiple, on `[a, b]`. -/
theorem rep_smul (hab : a < b) (c : ℝ) (u : SobolevInterval 1 a b) :
    EqOn (rep (c • u)) (c • rep u) (Icc a b) :=
  fun _ hx ↦ SobolevIntervalLp.rep_smul_Icc hab c u hx

/-- **The product rule in `H^1(a, b)`**, weak derivative form: the product of the continuous
representatives has the weak derivative `u' g_v + g_u v'` on `(a, b)`
(`SobolevIntervalLp.hasWeakDerivOn_rep_mul` on `(a, b)`). -/
theorem hasWeakDerivOn_rep_mul (u v : SobolevInterval 1 a b) :
    HasWeakDerivOn (fun t ↦ rep u t * rep v t)
      (fun t ↦ deriv u 1 t * rep v t + rep u t * deriv v 1 t) (Opens.Ioo a b) :=
  SobolevIntervalLp.hasWeakDerivOn_rep_mul (ordConnected_coe_Ioo a b) u v

/-- The continuous representative of a finite linear combination in `H¹(a, b)`, on `[a, b]`. -/
theorem rep_finset_sum (hab : a < b) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (φ : ι → SobolevInterval 1 a b) {x : ℝ} (hx : x ∈ Icc a b) :
    rep (∑ j ∈ s, c j • φ j) x = ∑ j ∈ s, c j * rep (φ j) x :=
  SobolevIntervalLp.rep_finset_sum (ordConnected_coe_Ioo a b) s c φ
    (by rwa [closure_coe_Ioo hab])

/-- **The pointwise bound of the embedding `H^1(a, b) ↪ C[a, b]`**:
`|u(x)| ≤ ((b - a)^{-1/2} + (b - a)^{1/2}) ‖u‖_{H^1}` for `x ∈ [a, b]`, the case `p = 2` of
`SobolevIntervalLp.abs_rep_le_of_bounded`. -/
theorem abs_rep_le (hab : a < b) (u : SobolevInterval 1 a b) {x : ℝ} (hx : x ∈ Icc a b) :
    |rep u x| ≤ (1 / Real.sqrt (b - a) + Real.sqrt (b - a)) * ‖u‖ := by
  have hba : 0 < b - a := sub_pos.2 hab
  have h := SobolevIntervalLp.abs_rep_le_of_bounded hab u hx
  have e1 : (b - a) ^ (-(2 : ℝ≥0∞).toReal⁻¹) = 1 / Real.sqrt (b - a) := by
    rw [one_div, Real.sqrt_eq_rpow, ← Real.rpow_neg hba.le, ENNReal.toReal_ofNat]
    norm_num
  have e2 : (b - a) ^ (1 - (2 : ℝ≥0∞).toReal⁻¹) = Real.sqrt (b - a) := by
    rw [Real.sqrt_eq_rpow, ENNReal.toReal_ofNat]
    norm_num
  rw [e1, e2] at h
  refine h.trans ?_
  rw [add_mul]
  gcongr
  · exact norm_deriv_le u 0
  · exact norm_deriv_le u 1

/-- **The embedding constant of `H^1(a, b) ↪ C[a, b]`**:
`‖u‖_∞ ≤ ((b - a)^{-1/2} + (b - a)^{1/2}) ‖u‖_{H^1}`. -/
theorem norm_toContinuousMap_le (hab : a < b) (u : SobolevInterval 1 a b) :
    ‖toContinuousMap hab u‖ ≤ (1 / Real.sqrt (b - a) + Real.sqrt (b - a)) * ‖u‖ :=
  (ContinuousMap.norm_le _ (by positivity)).2 fun x ↦ by
    rw [Real.norm_eq_abs]; exact abs_rep_le hab u x.2

/-- The operator norm of the embedding `H^1(a, b) ↪ C[a, b]` is at most
`(b - a)^{-1/2} + (b - a)^{1/2}`. -/
theorem norm_toContinuousMap_le' (hab : a < b) :
    ‖(toContinuousMap hab : SobolevInterval 1 a b →L[ℝ] C(Icc a b, ℝ))‖
      ≤ 1 / Real.sqrt (b - a) + Real.sqrt (b - a) :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_toContinuousMap_le hab)

/-- **Evaluation of the continuous representative** at a point of `[a, b]`, as a bounded linear
functional on `H^1(a, b)`; it is what turns an argument about pointwise values into a linear one. -/
def nodalCLM (hab : a < b) (t : ℝ) (ht : t ∈ Icc a b) :
    SobolevInterval 1 a b →L[ℝ] ℝ :=
  evalCLM hab ⟨t, ht⟩

/-- Nodal evaluation is the continuous representative. -/
@[simp]
theorem nodalCLM_apply (hab : a < b) (t : ℝ) (ht : t ∈ Icc a b) (u : SobolevInterval 1 a b) :
    nodalCLM hab t ht u = rep u t := rfl

end SobolevInterval

end Embedding

/-! ### The `C^k` representative, and the seminorm as an interval integral -/

section Representative

open intervalIntegral
open scoped Interval

variable {a b : ℝ}

namespace SobolevInterval

/-- **The `C^k` representative of an element of `H^{k+1}(a, b)`**: a function `f` of class `C^k` on
all of `ℝ` that agrees almost everywhere on `(a, b)` with `u`, whose derivatives `f^{(j)}` for
`j ≤ k` agree almost everywhere with the weak derivatives `u^{(j)}`, and whose `k`-th derivative is
the integral of the top weak derivative `u^{(k+1)}` between any two points of `[a, b]`:
`SobolevIntervalLp.exists_contDiff_ae_eq` on `(a, b)`. -/
theorem exists_contDiff_ae_eq (hab : a < b) {k : ℕ} (u : SobolevInterval (k + 1) a b) :
    ∃ f : ℝ → ℝ, ContDiff ℝ k f ∧
      (∀ j : Fin (k + 1), deriv u j.castSucc =ᵐ[volume.restrict (Ioo a b)] iteratedDeriv j f) ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        iteratedDeriv k f t - iteratedDeriv k f s = ∫ r in s..t, deriv u (Fin.last (k + 1)) r := by
  have h := SobolevIntervalLp.exists_contDiff_ae_eq
    (SobolevIntervalLp.ordConnected_coe_Ioo a b) u
  rwa [SobolevIntervalLp.closure_coe_Ioo hab] at h

/-- The `L²(a, b)` norm of a weak derivative, as an interval integral. -/
theorem norm_deriv_sq_eq_integral (hab : a ≤ b) {m : ℕ} (u : SobolevInterval m a b)
    (j : Fin (m + 1)) : ‖deriv u j‖ ^ 2 = ∫ t in a..b, deriv u j t ^ 2 := by
  rw [norm_sq_eq_integral_sq, integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  simp only [sq_abs]

/-- **The Sobolev seminorm as an interval integral**: `|u|²_{H^m(a, b)} = ∫_a^b |u^{(m)}|²`. -/
theorem seminorm_sq_eq_integral (hab : a ≤ b) {m : ℕ} (u : SobolevInterval m a b) :
    seminorm m a b u ^ 2 = ∫ t in a..b, deriv u (Fin.last m) t ^ 2 := by
  rw [seminorm_apply, norm_deriv_sq_eq_integral hab]

/-- The weak derivatives are interval integrable on `[a, b]`. -/
theorem intervalIntegrable_deriv (hab : a ≤ b) {m : ℕ} (u : SobolevInterval m a b)
    (j : Fin (m + 1)) : IntervalIntegrable (deriv u j) volume a b :=
  (SobolevIntervalLp.integrableOn_deriv_Ioo u j).intervalIntegrable_of_Ioo (left_mem_Icc.2 hab)
    (right_mem_Icc.2 hab)

/-- The squares of the weak derivatives are interval integrable on `[a, b]`. -/
theorem intervalIntegrable_deriv_sq (hab : a ≤ b) {m : ℕ} (u : SobolevInterval m a b)
    (j : Fin (m + 1)) : IntervalIntegrable (fun t => deriv u j t ^ 2) volume a b := by
  have h : IntegrableOn (fun t => deriv u j t ^ 2) (Ioo a b) :=
    (memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable (deriv u j))).1 (Lp.memLp (deriv u j))
  exact h.intervalIntegrable_of_Ioo (left_mem_Icc.2 hab) (right_mem_Icc.2 hab)

end SobolevInterval

end Representative

/-! ### Integration by parts in `H^1(a, b)` -/

section Leibniz

variable {a b : ℝ}

/-- **The Leibniz identity for antiderivatives of integrable functions**: for `w₁, w₂` integrable
on `(a, b)`, `g_i = c_i + ∫_a^x w_i` and `x ∈ [a, b]`,
`g₁(x) g₂(x) - c₁ c₂ = ∫_a^x (w₁ g₂ + g₁ w₂)`. It is Mathlib's product rule for absolutely
continuous functions, `AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub`, with the
classical derivatives replaced by `w₁, w₂` through the Lebesgue differentiation theorem. -/
theorem integral_mul_add_mul_of_eq_integral (hab : a ≤ b) {w₁ w₂ : ℝ → ℝ}
    (hw₁ : IntegrableOn w₁ (Ioo a b)) (hw₂ : IntegrableOn w₂ (Ioo a b)) (c₁ c₂ : ℝ) {x : ℝ}
    (hx : x ∈ Icc a b) :
    (c₁ + ∫ t in a..x, w₁ t) * (c₂ + ∫ t in a..x, w₂ t) - c₁ * c₂ =
      ∫ t in a..x, (w₁ t * (c₂ + ∫ s in a..t, w₂ s) + (c₁ + ∫ s in a..t, w₁ s) * w₂ t) := by
  set g₁ : ℝ → ℝ := fun t ↦ c₁ + ∫ s in a..t, w₁ s with hg₁
  set g₂ : ℝ → ℝ := fun t ↦ c₂ + ∫ s in a..t, w₂ s with hg₂
  have hsub : uIcc a x ⊆ uIcc a b :=
    uIcc_subset_uIcc left_mem_uIcc (by rw [uIcc_of_le hab]; exact hx)
  have h₁ : AbsolutelyContinuousOnInterval g₁ a x :=
    (absolutelyContinuousOnInterval_integral hab hw₁ c₁).mono hsub
  have h₂ : AbsolutelyContinuousOnInterval g₂ a x :=
    (absolutelyContinuousOnInterval_integral hab hw₂ c₂).mono hsub
  have key := h₁.integral_deriv_mul_eq_sub h₂
  have e1 : g₁ a = c₁ := by simp [hg₁]
  have e2 : g₂ a = c₂ := by simp [hg₂]
  rw [e1, e2] at key
  rw [← key]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_deriv_integral_eq hab hw₁ c₁, ae_deriv_integral_eq hab hw₂ c₂] with t h1 h2 ht
  rw [uIoc_of_le hx.1] at ht
  have ht' : t ∈ Ioc a b := Ioc_subset_Ioc_right hx.2 ht
  rw [h1 ht', h2 ht']

namespace SobolevInterval

open SobolevIntervalLp (ordConnected_coe_Ioo closure_coe_Ioo)

/-- **Integration by parts in `H^1(a, b)`**: for `u, v ∈ H^1(a, b)` with continuous
representatives `g_u, g_v`, `∫_a^b (u' g_v + g_u v') = g_u(b) g_v(b) - g_u(a) g_v(a)`
(`SobolevIntervalLp.integral_deriv_mul_add_mul_deriv` on `[a, b]`). -/
theorem integral_deriv_mul_add_mul_deriv (hab : a < b) (u v : SobolevInterval 1 a b) :
    ∫ t in a..b, (deriv u 1 t * rep v t + rep u t * deriv v 1 t) =
      rep u b * rep v b - rep u a * rep v a :=
  SobolevIntervalLp.integral_deriv_mul_add_mul_deriv (ordConnected_coe_Ioo a b) u v
    (by rw [closure_coe_Ioo hab]; exact right_mem_Icc.2 hab.le)
    (by rw [closure_coe_Ioo hab]; exact left_mem_Icc.2 hab.le)

/-- **Integration by parts in `H^1(a, b)` against an absolutely continuous factor** `ψ`:
`∫_a^b u' ψ = [g_u ψ]_a^b - ∫_a^b g_u ψ'`, where `ψ'` is the classical derivative, which exists
almost everywhere. -/
theorem integral_deriv_mul_eq_sub_integral_mul_deriv (hab : a < b) (u : SobolevInterval 1 a b)
    {ψ : ℝ → ℝ} (hψ : AbsolutelyContinuousOnInterval ψ a b) :
    ∫ t in a..b, deriv u 1 t * ψ t =
      rep u b * ψ b - rep u a * ψ a - ∫ t in a..b, rep u t * _root_.deriv ψ t :=
  SobolevIntervalLp.integral_deriv_mul_eq_sub_integral_mul_deriv_of_absolutelyContinuousOnInterval
    (ordConnected_coe_Ioo a b) u (by rw [closure_coe_Ioo hab]; exact right_mem_Icc.2 hab.le)
    (by rw [closure_coe_Ioo hab]; exact left_mem_Icc.2 hab.le) hψ

/-- **Integration by parts in `H^1(a, b)` against a `C¹` factor** `ψ`, such as a coefficient of
a differential operator: `∫_a^b u' ψ = [g_u ψ]_a^b - ∫_a^b g_u ψ'`. -/
theorem integral_deriv_mul_contDiffOn (hab : a < b) (u : SobolevInterval 1 a b)
    {ψ : ℝ → ℝ} (hψ : ContDiffOn ℝ 1 ψ (Icc a b)) :
    ∫ t in a..b, deriv u 1 t * ψ t =
      rep u b * ψ b - rep u a * ψ a - ∫ t in a..b, rep u t * _root_.deriv ψ t :=
  integral_deriv_mul_eq_sub_integral_mul_deriv hab u
    (by rw [← uIcc_of_le hab.le] at hψ; exact hψ.absolutelyContinuousOnInterval)

end SobolevInterval

end Leibniz

/-! ### Poincaré's inequality, and `H^1_0(a, b)` -/

section Poincare

variable {a b : ℝ}

/-- `∫_a^b (x - a) dx = (b - a)²/2`. -/
theorem integral_Ioo_sub_left (hab : a ≤ b) : ∫ x in Ioo a b, (x - a) = (b - a) ^ 2 / 2 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_sub_right (fun x ↦ x) a, sub_self, integral_id]
  ring

/-- **Poincaré's inequality, elementary form**: for `w ∈ L²(a, b)`, an `L²` function `g` that is
almost everywhere the antiderivative `∫_a^x w` (so `g(a) = 0`) satisfies
`‖g‖_{L²(a, b)} ≤ ((b - a)/√2) ‖w‖_{L²(a, b)}`. By Cauchy–Schwarz
`|g(x)|² ≤ (x - a) ‖w‖²`, and `∫_a^b (x - a) dx = (b - a)²/2`. This covers the Poincaré inequality
(12.16) of [quarteroni2000numerical] for `C¹` functions vanishing at the endpoints without any
density argument, and is the form the finite-difference and finite-element estimates use. -/
theorem SobolevInterval.norm_le_of_eq_integral (hab : a ≤ b)
    {w g : Lp ℝ 2 (volume.restrict (Ioo a b))}
    (hg : g =ᵐ[volume.restrict (Ioo a b)] fun x ↦ ∫ t in a..x, w t) :
    ‖g‖ ≤ (b - a) / Real.sqrt 2 * ‖w‖ := by
  have hC : 0 ≤ (b - a) / Real.sqrt 2 := div_nonneg (sub_nonneg.2 hab) (Real.sqrt_nonneg _)
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, norm_sq_eq_integral_sq,
    mul_pow, div_pow, Real.sq_sqrt zero_le_two]
  have hpt : ∀ᵐ x ∂(volume.restrict (Ioo a b)), |g x| ^ 2 ≤ (x - a) * ‖w‖ ^ 2 := by
    filter_upwards [hg, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    rw [hx]
    have := abs_intervalIntegral_le_sqrt_mul_norm w (left_mem_Icc.2 hab) (Ioo_subset_Icc_self hxI)
      hxI.1.le
    calc |∫ t in a..x, w t| ^ 2 ≤ (Real.sqrt (x - a) * ‖w‖) ^ 2 := by
          gcongr
      _ = (x - a) * ‖w‖ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (sub_nonneg.2 hxI.1.le)]
  calc ∫ x in Ioo a b, |g x| ^ 2 ≤ ∫ x in Ioo a b, (x - a) * ‖w‖ ^ 2 := by
        refine integral_mono_ae ?_ ?_ hpt
        · have := (Lp.memLp g).integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
          simpa [Real.norm_eq_abs] using this
        · have hi : IntegrableOn (fun x ↦ x - a) (Ioo a b) :=
            (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioo_subset_Icc_self
          exact hi.mul_const _
    _ = (b - a) ^ 2 / 2 * ‖w‖ ^ 2 := by
        rw [integral_mul_const, integral_Ioo_sub_left hab]

/-- **The Sobolev space `H^1_0(a, b)`**, the closure of the test functions `C_0^∞(a, b)` in
`H^1(a, b)`: `SobolevIntervalLpZero 1 2 (a, b)`, that is, `SobolevMultiIndexZero` of
`Numlib/Analysis/Sobolev/MultiIndex.lean` on the interval. A closed subspace of a Hilbert space,
hence a Hilbert space. It is the space `V` of [quarteroni2000numerical] §12.4.1, and by
`mem_sobolevIntervalZero_iff` it is exactly the set (12.42) of functions of `H^1(a, b)` vanishing
at both endpoints. -/
abbrev SobolevIntervalZero (a b : ℝ) : Submodule ℝ (SobolevInterval 1 a b) :=
  SobolevIntervalLpZero 1 2 (Opens.Ioo a b)

namespace SobolevIntervalZero

/- The general facts about `W_0^{1,p}(a, b)` (`Numlib/Analysis/Sobolev/Interval/Zero.lean`) at
`p = 2`; these names are aliases of them. -/
export SobolevIntervalLpZero (mem_of_fn_ae_eq rep_left_eq_zero rep_right_eq_zero rep_eq_integral)

/-- Every test function on `(a, b)` is the function of an element of `H^1_0(a, b)`
(`SobolevIntervalLpZero.exists_mem_fn_ae_eq` at `p = 2`). -/
theorem exists_mem_fn_ae_eq (φ : 𝓓(Opens.Ioo a b, ℝ)) :
    ∃ u ∈ SobolevIntervalZero a b, SobolevInterval.fn u =ᵐ[volume.restrict (Ioo a b)] φ :=
  SobolevIntervalLpZero.exists_mem_fn_ae_eq φ

open SobolevInterval in
/-- **An element of `H^1_0(a, b)` vanishes at both endpoints**: the trace of `H^1_0(a, b)` is
zero. -/
theorem toContinuousMap_eq_zero (hab : a < b) {u : SobolevInterval 1 a b}
    (hu : u ∈ SobolevIntervalZero a b) :
    toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩ = 0 ∧
      toContinuousMap hab u ⟨b, right_mem_Icc.2 hab.le⟩ = 0 :=
  ⟨rep_left_eq_zero hab hu, rep_right_eq_zero hab hu⟩

open SobolevInterval in
/-- **Poincaré's inequality on `H^1_0(a, b)`**, [quarteroni2000numerical] (12.16) with the
explicit constant `C_P = (b - a)/√2`: `‖u‖_{L²(a, b)} ≤ ((b - a)/√2) ‖u'‖_{L²(a, b)}` — the case
`p = 2` of `SobolevIntervalLpZero.norm_deriv_zero_le`, whose constant `(b - a)/p^{1/p}` is
`(b - a)/√2`. -/
theorem norm_deriv_zero_le (hab : a < b) {u : SobolevInterval 1 a b}
    (hu : u ∈ SobolevIntervalZero a b) :
    ‖deriv u 0‖ ≤ (b - a) / Real.sqrt 2 * ‖deriv u 1‖ := by
  have h := SobolevIntervalLpZero.norm_deriv_zero_le hab hu
  rw [ENNReal.toReal_ofNat] at h
  rw [Real.sqrt_eq_rpow, one_div]
  exact h

open SobolevInterval in
/-- **The `H^1` norm and the `H^1` seminorm are equivalent on `H^1_0(a, b)`**:
`‖u‖_{H^1} ≤ √(1 + (b - a)²/2) |u|_{H^1}`, so that the seminorm `|·|_{H^1}` is a norm on
`H^1_0(a, b)` equivalent to `‖·‖_{H^1}`; it is what makes the Dirichlet form of
`Numlib/Variational/EllipticInterval` coercive for the `H^1` norm. -/
theorem norm_le_seminorm (hab : a < b) {u : SobolevInterval 1 a b}
    (hu : u ∈ SobolevIntervalZero a b) :
    ‖u‖ ≤ Real.sqrt (1 + (b - a) ^ 2 / 2) * seminorm 1 a b u := by
  have h := norm_deriv_zero_le hab hu
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, norm_sq_eq,
    Fin.sum_univ_two, mul_pow, Real.sq_sqrt (by positivity), seminorm_apply]
  have h' : ‖deriv u 0‖ ^ 2 ≤ ((b - a) / Real.sqrt 2) ^ 2 * ‖deriv u 1‖ ^ 2 := by
    rw [← mul_pow]; gcongr
  rw [div_pow, Real.sq_sqrt zero_le_two] at h'
  change ‖deriv u 0‖ ^ 2 + ‖deriv u (Fin.last 1)‖ ^ 2 ≤ _ * ‖deriv u (Fin.last 1)‖ ^ 2
  have e : deriv u (Fin.last 1) = deriv u 1 := rfl
  rw [e]
  nlinarith [h']

open SobolevInterval in
/-- The seminorm `|·|_{H^1}` is a norm on `H^1_0(a, b)`
(`SobolevIntervalLpZero.norm_deriv_one_eq_zero_iff` at `p = 2`). -/
theorem seminorm_eq_zero_iff (hab : a < b) {u : SobolevInterval 1 a b}
    (hu : u ∈ SobolevIntervalZero a b) : seminorm 1 a b u = 0 ↔ u = 0 :=
  SobolevIntervalLpZero.norm_deriv_one_eq_zero_iff hab hu

end SobolevIntervalZero

end Poincare

/-! ### Density of the test functions in `L²(a, b)`, and the boundary characterization of
`H^1_0(a, b)` -/

section Density

variable {a b : ℝ}

/-- **A smooth bounded function is approximated in `L²(a, b)` by its cut-offs to the interior.**
For `g` smooth with `|g| ≤ C` and `ε > 0` there is a test function `ψ` on `(a, b)` with
`‖g - ψ‖_{L²(a, b)} ≤ ε`: `ψ = g χ` for a bump `χ` equal to `1` on `[a + 2δ, b - 2δ]` and
supported in `(a + δ, b - δ)`, so that `|g - ψ| ≤ C` on a set of measure at most `4δ` and
vanishes elsewhere. -/
theorem exists_testFunction_eLpNorm_sub_le_of_contDiff (hab : a < b) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : 𝓓(Opens.Ioo a b, ℝ),
      eLpNorm (g - (ψ : ℝ → ℝ)) 2 (volume.restrict (Ioo a b)) ≤ ENNReal.ofReal ε := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  set r := (b - a) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  set η := (ε / (C + 1)) ^ 2 with hη
  have hη0 : 0 < η := by positivity
  set δ := min (η / 4) (r / 4) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδr : δ ≤ r / 4 := min_le_right _ _
  have hδη : 4 * δ ≤ η := by linarith [min_le_left (η / 4) (r / 4)]
  let χ : ContDiffBump ((a + b) / 2) := ⟨r - 2 * δ, r - δ, by linarith, by linarith⟩
  have hrIn : χ.rIn = r - 2 * δ := rfl
  have hrOut : χ.rOut = r - δ := rfl
  refine ⟨⟨fun x ↦ g x * χ x, hg.mul (χ.contDiff (n := ⊤)), χ.hasCompactSupport.mul_left, ?_⟩, ?_⟩
  · refine (tsupport_mul_subset_right).trans ?_
    rw [χ.tsupport_eq, hrOut]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
    exact ⟨by rw [hr] at hx; linarith [hx.1], by rw [hr] at hx; linarith [hx.2]⟩
  -- the pointwise bound by `C` on the set where the cut-off is not one
  set S : Set ℝ := (Metric.closedBall ((a + b) / 2) (r - 2 * δ))ᶜ with hS
  have hpt : ∀ᵐ x ∂(volume.restrict (Ioo a b)),
      ‖(g - fun x ↦ g x * χ x) x‖ ≤ ‖S.indicator (fun _ ↦ C) x‖ := by
    refine Eventually.of_forall fun x ↦ ?_
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    by_cases hx : x ∈ Metric.closedBall ((a + b) / 2) (r - 2 * δ)
    · rw [χ.one_of_mem_closedBall (by rwa [hrIn]), mul_one, sub_self, abs_zero]
      exact abs_nonneg _
    · rw [indicator_of_mem (by simpa [hS] using hx), abs_of_nonneg hC0]
      calc |g x - g x * χ x| = |g x| * (1 - χ x) := by
            rw [← mul_one_sub, abs_mul,
              abs_of_nonneg (a := 1 - χ x) (by linarith [χ.le_one (x := x)])]
        _ ≤ C * 1 := mul_le_mul (hC x) (by linarith [χ.nonneg (x := x)])
            (by linarith [χ.le_one (x := x)]) hC0
        _ = C := mul_one C
  -- the measure of that set within `(a, b)`
  have hμS : (volume.restrict (Ioo a b)) S ≤ ENNReal.ofReal (4 * δ) := by
    rw [Measure.restrict_apply' measurableSet_Ioo]
    have hsub : S ∩ Ioo a b ⊆ Ioo a (a + 2 * δ) ∪ Ioo (b - 2 * δ) b := by
      rintro x ⟨hxS, hxI⟩
      simp only [hS, mem_compl_iff, Metric.mem_closedBall, Real.dist_eq, not_le] at hxS
      rcases lt_abs.1 hxS with h | h
      · right; exact ⟨by rw [hr] at h; linarith, hxI.2⟩
      · left; exact ⟨hxI.1, by rw [hr] at h; linarith⟩
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    rw [Real.volume_Ioo, Real.volume_Ioo, ← ENNReal.ofReal_add (by linarith) (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc eLpNorm (g - fun x ↦ g x * χ x) 2 (volume.restrict (Ioo a b))
      ≤ eLpNorm (S.indicator fun _ ↦ C) 2 (volume.restrict (Ioo a b)) :=
        eLpNorm_mono_ae (hg.continuous.aestronglyMeasurable.sub
          (hg.continuous.mul χ.continuous).aestronglyMeasurable) hpt
    _ ≤ ‖C‖ₑ * (volume.restrict (Ioo a b)) S ^ (1 / (2 : ℝ≥0∞).toReal) :=
        eLpNorm_indicator_const_le C 2 (measurableSet_closedBall.compl.nullMeasurableSet)
    _ ≤ ENNReal.ofReal (C + 1) * ENNReal.ofReal (4 * δ) ^ (1 / (2 : ℝ)) := by
        rw [ENNReal.toReal_ofNat, Real.enorm_eq_ofReal hC0]
        gcongr
        linarith
    _ = ENNReal.ofReal ((C + 1) * Real.sqrt (4 * δ)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) (by norm_num), ← ENNReal.ofReal_mul
          (by linarith), Real.sqrt_eq_rpow]
    _ ≤ ENNReal.ofReal ε := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : Real.sqrt (4 * δ) ≤ ε / (C + 1) := by
          rw [Real.sqrt_le_left (by positivity)]
          exact hδη
        calc (C + 1) * Real.sqrt (4 * δ) ≤ (C + 1) * (ε / (C + 1)) := by gcongr
          _ = ε := mul_div_cancel₀ _ (by positivity)

/-- **The test functions `C_0^∞(a, b)` are dense in `L²(a, b)`**: Mathlib's smooth compactly
supported approximation `MeasureTheory.MemLp.exist_eLpNorm_sub_le`, followed by the cut-off to
the interior `exists_testFunction_eLpNorm_sub_le_of_contDiff`. -/
theorem exists_testFunction_eLpNorm_sub_le (hab : a < b) {w : ℝ → ℝ}
    (hw : MemLp w 2 (volume.restrict (Ioo a b))) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : 𝓓(Opens.Ioo a b, ℝ),
      eLpNorm (w - (ψ : ℝ → ℝ)) 2 (volume.restrict (Ioo a b)) ≤ ENNReal.ofReal ε := by
  obtain ⟨g, hgc, hg, hwg⟩ := hw.exist_eLpNorm_sub_le ENNReal.ofNat_ne_top one_le_two
    (half_pos hε)
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg.continuous
  obtain ⟨ψ, hψ⟩ := exists_testFunction_eLpNorm_sub_le_of_contDiff hab hg
    (fun x ↦ by rw [← Real.norm_eq_abs]; exact hC x) (half_pos hε)
  refine ⟨ψ, ?_⟩
  have e : w - ⇑ψ = (w - g) + (g - ⇑ψ) := by abel
  calc eLpNorm (w - ⇑ψ) 2 (volume.restrict (Ioo a b))
      ≤ eLpNorm (w - g) 2 (volume.restrict (Ioo a b))
        + eLpNorm (g - ⇑ψ) 2 (volume.restrict (Ioo a b)) := by
        rw [e]
        exact eLpNorm_add_le one_le_two
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hwg hψ
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

/-- Interval integrals over `[a, x] ⊆ [a, b]` only see the integrand almost everywhere on
`(a, b)`. -/
theorem intervalIntegral_congr_ae_Ioo {f g : ℝ → ℝ} (h : f =ᵐ[volume.restrict (Ioo a b)] g)
    {x : ℝ} (hx : x ∈ Icc a b) : ∫ t in a..x, f t = ∫ t in a..x, g t := by
  refine intervalIntegral.integral_congr_ae ?_
  have hb : ∀ᵐ t : ℝ, t ≠ b := by simp [ae_iff, measure_singleton]
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 h, hb] with t ht htb htI
  rw [uIoc_of_le hx.1] at htI
  exact ht ⟨htI.1, lt_of_le_of_ne (htI.2.trans hx.2) htb⟩

/-- A test function on `(a, b)` as an element of `L²(a, b)`. -/
def TestFunction.toLp₂ (ψ : 𝓓(Opens.Ioo a b, ℝ)) : Lp ℝ 2 (volume.restrict (Ioo a b)) :=
  (TestFunction.memLp ψ 2 _).toLp ψ

/-- The `L²(a, b)` element of a test function is the test function almost everywhere. -/
theorem TestFunction.coeFn_toLp₂ (ψ : 𝓓(Opens.Ioo a b, ℝ)) :
    ψ.toLp₂ =ᵐ[volume.restrict (Ioo a b)] ψ :=
  MemLp.coeFn_toLp _

/-- **The test functions are dense in `L²(a, b)`**, in the norm of `Lp`. -/
theorem exists_testFunction_norm_sub_toLp_le (hab : a < b)
    (w : Lp ℝ 2 (volume.restrict (Ioo a b))) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : 𝓓(Opens.Ioo a b, ℝ), ‖w - ψ.toLp₂‖ ≤ ε := by
  obtain ⟨ψ, hψ⟩ := exists_testFunction_eLpNorm_sub_le hab (Lp.memLp w) hε
  refine ⟨ψ, ?_⟩
  rw [Lp.norm_def]
  refine ENNReal.toReal_le_of_le_ofReal hε.le (le_of_eq_of_le (eLpNorm_congr_ae ?_) hψ)
  exact (Lp.coeFn_sub w ψ.toLp₂).trans (ψ.coeFn_toLp₂.mono fun x hx ↦ by
    simp only [Pi.sub_apply, hx])

open SobolevInterval in
/-- **A function of `H^1(a, b)` whose continuous representative vanishes at both endpoints lies
in `H^1_0(a, b)`**, the converse of `SobolevIntervalZero.toContinuousMap_eq_zero`: the case
`p = 2` of `SobolevIntervalLpZero.mem_of_rep_frontier_eq_zero_of_bounded` (Theorem 8.12 of
[brezis2011functional] on a bounded interval). -/
theorem SobolevIntervalZero.mem_of_rep_eq_zero (hab : a < b) (u : SobolevInterval 1 a b)
    (ha : rep u a = 0) (hb : rep u b = 0) : u ∈ SobolevIntervalZero a b :=
  SobolevIntervalLpZero.mem_of_rep_frontier_eq_zero_of_bounded hab (by norm_num) u ha hb

open SobolevInterval in
/-- **A function of `H^1(a, b)` vanishing at both endpoints lies in `H^1_0(a, b)`**, stated for
the embedding `SobolevInterval.toContinuousMap`. -/
theorem mem_sobolevIntervalZero_of_toContinuousMap_eq_zero (hab : a < b)
    (u : SobolevInterval 1 a b) (ha : toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩ = 0)
    (hb : toContinuousMap hab u ⟨b, right_mem_Icc.2 hab.le⟩ = 0) :
    u ∈ SobolevIntervalZero a b :=
  SobolevIntervalZero.mem_of_rep_eq_zero hab u ha hb

open SobolevInterval in
/-- **The boundary characterization of `H^1_0(a, b)`**: an element of `H^1(a, b)` lies in
`H^1_0(a, b)` exactly when its continuous representative vanishes at both endpoints. This is
[quarteroni2000numerical] (12.42), `H^1_0(0,1) = {v ∈ L² : v' ∈ L², v(0) = v(1) = 0}`. -/
theorem mem_sobolevIntervalZero_iff (hab : a < b) (u : SobolevInterval 1 a b) :
    u ∈ SobolevIntervalZero a b ↔ toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩ = 0 ∧
      toContinuousMap hab u ⟨b, right_mem_Icc.2 hab.le⟩ = 0 :=
  ⟨SobolevIntervalZero.toContinuousMap_eq_zero hab, fun h ↦
    mem_sobolevIntervalZero_of_toContinuousMap_eq_zero hab u h.1 h.2⟩

end Density

namespace ContDiffMapIcc

variable {a b : ℝ} {hab : a ≤ b} {k : ℕ}

/-- The `j`-th derivative of `u ∈ C^k[a, b]`, extended by its endpoint values off `[a, b]`, as an
element of `L²(a, b)`: `ContDiffMapIcc.derivLpOf` at `p = 2`. -/
def derivLp (u : ContDiffMapIcc hab k) (j : Fin (k + 1)) : Lp ℝ 2 (volume.restrict (Ioo a b)) :=
  derivLpOf 2 u j

/-- `ContDiffMapIcc.derivLp` is the extended derivative almost everywhere. -/
theorem coeFn_derivLp (u : ContDiffMapIcc hab k) (j : Fin (k + 1)) :
    u.derivLp j =ᵐ[volume.restrict (Ioo a b)] IccExtend hab (u.deriv j) :=
  coeFn_derivLpOf u j

/-- `ContDiffMapIcc.derivLp` is additive. -/
theorem derivLp_add (u v : ContDiffMapIcc hab k) (j : Fin (k + 1)) :
    (u + v).derivLp j = u.derivLp j + v.derivLp j :=
  derivLpOf_add u v j

/-- `ContDiffMapIcc.derivLp` is homogeneous. -/
theorem derivLp_smul (c : ℝ) (u : ContDiffMapIcc hab k) (j : Fin (k + 1)) :
    (c • u).derivLp j = c • u.derivLp j :=
  derivLpOf_smul c u j

/-- The extended derivatives of `u ∈ C^k[a, b]` are the weak derivatives of `u` on `(a, b)`
(`ContDiffMapIcc.hasWeakIteratedDerivOn_derivLpOf` at `p = 2`). -/
theorem hasWeakIteratedDerivOn_derivLp (hlt : a < b) (u : ContDiffMapIcc hab k)
    (j : Fin (k + 1)) :
    HasWeakIteratedDerivOn (j : ℕ) (u.derivLp 0) (u.derivLp j) (Opens.Ioo a b) :=
  hasWeakIteratedDerivOn_derivLpOf hlt u j

/-- The inclusion `C^k[a, b] → H^k(a, b)` as a linear map: `u` goes to the element whose `j`-th
component is the extended derivative `u^{(j)}` (`ContDiffMapIcc.toSobolevIntervalLpₗ` at
`p = 2`). -/
def toSobolevIntervalₗ (hab : a ≤ b) (hlt : a < b) (k : ℕ) :
    ContDiffMapIcc hab k →ₗ[ℝ] SobolevInterval k a b :=
  toSobolevIntervalLpₗ 2 hab hlt k

/-- The weak derivatives of the inclusion of `u ∈ C^k[a, b]` are its extended derivatives. -/
@[simp]
theorem deriv_toSobolevIntervalₗ (hab : a ≤ b) (hlt : a < b) (u : ContDiffMapIcc hab k)
    (j : Fin (k + 1)) : SobolevInterval.deriv (toSobolevIntervalₗ hab hlt k u) j = u.derivLp j :=
  rfl

/-- `‖u^{(j)}‖_{L²(a, b)} ≤ √(b - a) ‖u^{(j)}‖_∞` (`ContDiffMapIcc.norm_derivLpOf_le` at `p = 2`,
where `(b - a)^{1/p} = √(b - a)`). -/
theorem norm_derivLp_le (u : ContDiffMapIcc hab k) (j : Fin (k + 1)) :
    ‖u.derivLp j‖ ≤ Real.sqrt (b - a) * ‖u.deriv j‖ := by
  have h := norm_derivLpOf_le (p := 2) u j
  rw [ENNReal.toReal_ofNat] at h
  rw [Real.sqrt_eq_rpow, one_div]
  exact h

/-- The constant of the inclusion `C^k[a, b] → H^k(a, b)`, for the linear map:
`‖u‖_{H^k} ≤ √(b - a) ‖u‖_{C^k}` (`ContDiffMapIcc.norm_toSobolevIntervalLpₗ_le` at `p = 2`). -/
theorem norm_toSobolevIntervalₗ_le (hab : a ≤ b) (hlt : a < b) (u : ContDiffMapIcc hab k) :
    ‖toSobolevIntervalₗ hab hlt k u‖ ≤ Real.sqrt (b - a) * ‖u‖ := by
  have h := norm_toSobolevIntervalLpₗ_le (p := 2) hab hlt u
  rw [ENNReal.toReal_ofNat] at h
  rw [Real.sqrt_eq_rpow, one_div]
  exact h

/-- **The inclusion `C^k[a, b] → H^k(a, b)`**: the continuous linear map sending
`u ∈ C^k[a, b]` to the element of `H^k(a, b)` whose components are its derivatives
`u, u', …, u^{(k)}`, extended by their endpoint values off `[a, b]` —
`ContDiffMapIcc.toSobolevIntervalLp` at `p = 2`. It is injective
(`ContDiffMapIcc.toSobolevInterval_injective`) and has norm at most `√(b - a)`
(`ContDiffMapIcc.norm_toSobolevInterval_le`). Its completion is what Atkinson and Han,
*Theoretical Numerical Analysis*, 3rd edition, Examples 1.2.28(b) and 2.4.2 call `H^k(a, b)`;
its range is dense at every order (`ContDiffMapIcc.denseRange_toSobolevInterval`,
`ContDiffMapIcc.denseRange_toSobolevInterval_one`). -/
def toSobolevInterval (hab : a ≤ b) (hlt : a < b) (k : ℕ) :
    ContDiffMapIcc hab k →L[ℝ] SobolevInterval k a b :=
  toSobolevIntervalLp 2 hab hlt k

/-- The weak derivatives of the inclusion of `u ∈ C^k[a, b]` are its extended derivatives. -/
@[simp]
theorem deriv_toSobolevInterval (hab : a ≤ b) (hlt : a < b) (u : ContDiffMapIcc hab k)
    (j : Fin (k + 1)) : SobolevInterval.deriv (toSobolevInterval hab hlt k u) j = u.derivLp j :=
  rfl

/-- The function of the inclusion of `u ∈ C^k[a, b]` is `u` almost everywhere on `(a, b)`. -/
theorem fn_toSobolevInterval_ae_eq (hab : a ≤ b) (hlt : a < b) (u : ContDiffMapIcc hab k) :
    SobolevInterval.fn (toSobolevInterval hab hlt k u) =ᵐ[volume.restrict (Ioo a b)] u.extend :=
  coeFn_derivLp u 0

/-- **The constant of the inclusion `C^k[a, b] → H^k(a, b)`**: `‖u‖_{H^k} ≤ √(b - a) ‖u‖_{C^k}`,
each `‖u^{(j)}‖_{L²}` being at most `√(b - a) ‖u^{(j)}‖_∞`. -/
theorem norm_toSobolevInterval_le (hab : a ≤ b) (hlt : a < b) (u : ContDiffMapIcc hab k) :
    ‖toSobolevInterval hab hlt k u‖ ≤ Real.sqrt (b - a) * ‖u‖ :=
  norm_toSobolevIntervalₗ_le hab hlt u

/-- **The inclusion `C^k[a, b] → H^k(a, b)` is injective**: a continuous function vanishing
almost everywhere on `(a, b)` vanishes on `[a, b]` (`ContDiffMapIcc.toSobolevIntervalLp_injective`
at `p = 2`). -/
theorem toSobolevInterval_injective (hab : a ≤ b) (hlt : a < b) (k : ℕ) :
    Function.Injective (toSobolevInterval hab hlt k) :=
  toSobolevIntervalLp_injective (p := 2) hab hlt k

/-- **`C^k[a, b]` is dense in `H^k(a, b)`** at every order
(`ContDiffMapIcc.denseRange_toSobolevIntervalLp` at `p = 2`). -/
theorem denseRange_toSobolevInterval (hab : a ≤ b) (hlt : a < b) (k : ℕ) :
    DenseRange (toSobolevInterval hab hlt k) :=
  denseRange_toSobolevIntervalLp (p := 2) hab hlt (by norm_num) k

/-- **`C¹[a, b]` is dense in `H^1(a, b)`**: the case `k = 1` of
`ContDiffMapIcc.denseRange_toSobolevInterval` (Atkinson and Han, *Theoretical Numerical
Analysis*, 3rd edition, Examples 1.2.28(b) and 2.4.2). -/
theorem denseRange_toSobolevInterval_one (hlt : a < b) :
    DenseRange (toSobolevInterval hlt.le hlt 1) :=
  denseRange_toSobolevInterval hlt.le hlt 1

end ContDiffMapIcc

/-! ### Piecewise `C¹` functions -/

section Piecewise

variable {a b : ℝ}

/-- **Continuous piecewise-`C¹` functions lie in `H^1(a, b)`**: for a partition
`x 0 = a < x 1 < ⋯ < x (N + 1) = b` and `g` continuous on `[a, b]`, `C¹` on each open panel with
the panel derivatives bounded by a common constant, `g ∈ H^1(a, b)` with weak derivative
`deriv g` (whose values at the nodes are irrelevant). This is what puts the finite element spaces
`X_h^k` of [quarteroni2000numerical] §12.4.5 inside `H^1(0, 1)`; with
`mem_sobolevIntervalZero_of_toContinuousMap_eq_zero` the elements vanishing at the endpoints lie
in `H^1_0(0, 1)`. The case `p = 2` of `memSobolevIntervalLp_of_piecewise_contDiffOn`. -/
theorem memSobolevInterval_of_piecewise_contDiffOn {N : ℕ} {x : Fin (N + 2) → ℝ}
    (hx : StrictMono x) (hxa : x 0 = a) (hxb : x (Fin.last (N + 1)) = b) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ j : Fin (N + 1), ContDiffOn ℝ 1 g (Ioo (x j.castSucc) (x j.succ)))
    (hbdd : ∃ C, ∀ j : Fin (N + 1), ∀ t ∈ Ioo (x j.castSucc) (x j.succ), |deriv g t| ≤ C) :
    MemSobolevInterval g 1 a b ∧ HasWeakDerivOn g (deriv g) (Opens.Ioo a b) :=
  memSobolevIntervalLp_of_piecewise_contDiffOn hx hxa hxb hg hg' hbdd

end Piecewise
