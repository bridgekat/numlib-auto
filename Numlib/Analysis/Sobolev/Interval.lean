/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/MultiIndex.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Numlib.Analysis.Calculus.ContDiffMapIcc
import Numlib.Analysis.Sobolev.MultiIndex

/-!
# Sobolev spaces on an interval

`H^m(a, b) = W^{m,2}(a, b)` and `H^1_0(a, b)`, with the one-dimensional facts that have no
analogue in higher dimension: every function of `H^1(a, b)` has an absolutely continuous
representative, `H^1(a, b)` embeds in `C[a, b]`, and Poincaré's inequality on `H^1_0(a, b)` holds
with the explicit constant `(b - a)/√2`.

`SobolevInterval m a b` is *not* a new space: it is the multi-index Sobolev space
`SobolevMultiIndex ℝ (Module.Basis.singleton Unit ℝ) m 2 (Opens.Ioo a b) volume` of
`Numlib/Analysis/Sobolev/MultiIndex.lean`, read on `E = ℝ` with the one-element basis, so that
its components are the weak derivatives `u, u', …, u^{(m)}` in `L²(a, b)` and it is a Hilbert
space for the inner product `(u, v)_{H^m} = ∑_{j ≤ m} (u^{(j)}, v^{(j)})_{L²}` on the nose
(`SobolevMultiIndex.inner_eq`). `H^1_0(a, b)` is accordingly `SobolevMultiIndexZero`, the closure
of the test functions in the multi-index space.

## Main definitions

* `TopologicalSpace.Opens.Ioo a b`, the open interval as an element of `Opens ℝ`;
* `HasWeakDerivOn f w a b` and `HasWeakIteratedDerivOn k f w a b`, the first-order and the
  `k`-th weak derivative on `(a, b)`, as `HasWeakIteratedLineDerivOn` along the constant tuple of
  directions `1`;
* `TestFunction.primitive`, the antiderivative of a test function on `(a, b)` with zero mean,
  which is again a test function;
* `SobolevInterval m a b`, the space `H^m(a, b)`, with `MemSobolevInterval f m a b` the
  corresponding predicate on functions, `SobolevInterval.deriv u j` the `j`-th weak derivative in
  `L²(a, b)`, and `SobolevInterval.seminorm m a b` the seminorm `|u|_{H^m} = ‖u^{(m)}‖_{L²}`;
* `SobolevInterval.toContinuousMap hab`, the embedding `H^1(a, b) ↪ C[a, b]`, sending `u` to
  its continuous representative;
* `SobolevIntervalZero a b`, the space `H^1_0(a, b)`;
* `SobolevInterval.derivCLM m a b`, weak differentiation `H^{m+1}(a, b) → H^m(a, b)`, and
  `ContDiffMapIcc.toSobolevInterval`, the inclusion `C^k[a, b] → H^k(a, b)`.

## Main statements

* `hasWeakDerivOn_integral`: the antiderivative of an integrable function is weakly
  differentiable, and `ae_eq_const_of_hasWeakDerivOn_zero`, **du Bois-Reymond's lemma**: a
  function whose weak derivative vanishes is almost everywhere constant. Together they give
  `HasWeakDerivOn.exists_ae_eq_integral`, **the absolutely continuous representative**: a
  function with an integrable weak derivative `w` on `(a, b)` agrees almost everywhere with
  `c + ∫_a^x w`.
* `SobolevInterval.norm_toContinuousMap_le`: **`H^1(a, b) ↪ C[a, b]`** with the constant
  `(b - a)^{-1/2} + (b - a)^{1/2}`; `SobolevInterval.toContinuousMap_sub_eq_integral`, the
  fundamental theorem of calculus in `H^1(a, b)`;
  `SobolevInterval.integral_deriv_mul_add_mul_deriv`, integration by parts, and
  `SobolevInterval.memSobolevInterval_mul`, the product rule.
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
`H^1(a, b)` vanishing at both endpoints lies in the closure of the test functions — is proved
without any cut-off or mollification of the function itself: its derivative `u'` has zero mean
and is approximated in `L²(a, b)` by test functions of zero mean (Mathlib's density of smooth
compactly supported functions in `L²`, followed by a cut-off to the interior), whose primitives
are test functions converging to `u` in `H^1` by Poincaré's inequality.

Conventions: `a < b` is a hypothesis of every theorem that needs it, never of the definitions;
the measure is `volume.restrict (Ioo a b)`; the `L²(a, b)` type is
`Lp ℝ 2 (volume.restrict (Ioo a b))`.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace Topology

noncomputable section

/-! ### The open interval as an open set -/

namespace TopologicalSpace.Opens

/-- The open interval `(a, b)` as an open set of `ℝ`. -/
def Ioo (a b : ℝ) : Opens ℝ := ⟨Set.Ioo a b, isOpen_Ioo⟩

/-- The underlying set of `Opens.Ioo a b` is `Set.Ioo a b`. -/
@[simp]
theorem coe_Ioo (a b : ℝ) : (Opens.Ioo a b : Set ℝ) = Set.Ioo a b := rfl

end TopologicalSpace.Opens

/-! ### Weak derivatives on an interval -/

/-- The `k`-th weak derivative on the interval `(a, b)`: `HasWeakIteratedDerivOn k f w a b` says
that `w` is the weak derivative of order `k` of `f` on `(a, b)`, that is, `f` and `w` are locally
integrable on `(a, b)` and `∫_a^b φ^{(k)} f = (-1)^k ∫_a^b φ w` for every test function `φ` on
`(a, b)`. It is `HasWeakIteratedLineDerivOn` along the constant tuple of directions `1`. -/
abbrev HasWeakIteratedDerivOn (k : ℕ) (f w : ℝ → ℝ) (a b : ℝ) : Prop :=
  HasWeakIteratedLineDerivOn (fun _ : Fin k ↦ (1 : ℝ)) f w (Opens.Ioo a b) volume

/-- The first-order weak derivative on the interval `(a, b)`: `HasWeakDerivOn f w a b` says that
`f` and `w` are locally integrable on `(a, b)` and `∫_a^b φ' f = -∫_a^b φ w` for every test
function `φ` on `(a, b)`. This is `HasWeakIteratedDerivOn 1`. -/
abbrev HasWeakDerivOn (f w : ℝ → ℝ) (a b : ℝ) : Prop :=
  HasWeakIteratedLineDerivOn (fun _ : Fin 1 ↦ (1 : ℝ)) f w (Opens.Ioo a b) volume

section Chain

variable {a b : ℝ} {f v w : ℝ → ℝ} {k : ℕ}

/-- The weak derivative of order one is `HasWeakDerivOn`. -/
theorem hasWeakIteratedDerivOn_one : HasWeakIteratedDerivOn 1 f w a b ↔ HasWeakDerivOn f w a b :=
  Iff.rfl

/-- The `k`-th weak derivative on an interval unfolded: local integrability of both functions,
and the integration by parts formula `∫_a^b φ^{(k)} f = (-1)^k ∫_a^b φ w` against every test
function `φ` on `(a, b)`. -/
theorem hasWeakIteratedDerivOn_iff :
    HasWeakIteratedDerivOn k f w a b ↔ LocallyIntegrableOn f (Ioo a b) ∧
      LocallyIntegrableOn w (Ioo a b) ∧ ∀ φ : 𝓓(Opens.Ioo a b, ℝ),
        ∫ x in Ioo a b, iteratedDeriv k φ x * f x = (-1) ^ k * ∫ x in Ioo a b, φ x * w x := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun φ ↦ by
      simpa only [smul_eq_mul, iteratedDeriv_eq_iteratedFDeriv, Opens.coe_Ioo] using h3 φ⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun φ ↦ by
      simpa only [smul_eq_mul, iteratedDeriv_eq_iteratedFDeriv, Opens.coe_Ioo] using h3 φ⟩

/-- The first-order weak derivative on an interval unfolded: local integrability of both
functions, and the integration by parts formula `∫_a^b φ' f = -∫_a^b φ w` against every test
function `φ` on `(a, b)`. -/
theorem hasWeakDerivOn_iff :
    HasWeakDerivOn f w a b ↔ LocallyIntegrableOn f (Ioo a b) ∧ LocallyIntegrableOn w (Ioo a b) ∧
      ∀ φ : 𝓓(Opens.Ioo a b, ℝ),
        ∫ x in Ioo a b, deriv φ x * f x = -∫ x in Ioo a b, φ x * w x := by
  rw [← hasWeakIteratedDerivOn_one, hasWeakIteratedDerivOn_iff]
  simp only [iteratedDeriv_one, pow_one, neg_one_mul]

/-- The integration by parts formula of the `k`-th weak derivative on an interval. -/
theorem HasWeakIteratedDerivOn.integral_iteratedDeriv_mul (h : HasWeakIteratedDerivOn k f w a b)
    (φ : 𝓓(Opens.Ioo a b, ℝ)) :
    ∫ x in Ioo a b, iteratedDeriv k φ x * f x = (-1) ^ k * ∫ x in Ioo a b, φ x * w x :=
  (hasWeakIteratedDerivOn_iff.1 h).2.2 φ

/-- The integration by parts formula of the first-order weak derivative on an interval. -/
theorem HasWeakDerivOn.integral_deriv_mul (h : HasWeakDerivOn f w a b)
    (φ : 𝓓(Opens.Ioo a b, ℝ)) :
    ∫ x in Ioo a b, deriv φ x * f x = -∫ x in Ioo a b, φ x * w x :=
  (hasWeakDerivOn_iff.1 h).2.2 φ

/-- The `k`-th derivative of a test function on an interval is the test function
`TestFunction.iteratedFDerivApply` along the constant tuple `1`. -/
theorem TestFunction.iteratedDerivApply_coe (φ : 𝓓(Opens.Ioo a b, ℝ)) (k : ℕ) :
    (φ.iteratedFDerivApply k (fun _ ↦ (1 : ℝ)) : ℝ → ℝ) = iteratedDeriv k φ := rfl

/-- The derivative of a test function on an interval is the test function
`TestFunction.fderivApply` in the direction `1`. -/
theorem TestFunction.derivApply_coe (φ : 𝓓(Opens.Ioo a b, ℝ)) :
    (φ.fderivApply 1 : ℝ → ℝ) = deriv φ := rfl

/-- Chaining weak derivatives on an interval: if `v` is the weak derivative of `f` and `w` the
`k`-th weak derivative of `v`, then `w` is the `(k + 1)`-th weak derivative of `f`. The proof
tests the first identity against `φ^{(k)}`, which is again a test function. -/
theorem HasWeakDerivOn.hasWeakIteratedDerivOn_succ (h : HasWeakDerivOn f v a b)
    (h' : HasWeakIteratedDerivOn k v w a b) : HasWeakIteratedDerivOn (k + 1) f w a b := by
  refine hasWeakIteratedDerivOn_iff.2 ⟨h.locallyIntegrableOn, h'.locallyIntegrableOn_weakDeriv,
    fun φ ↦ ?_⟩
  have e1 := h.integral_deriv_mul (φ.iteratedFDerivApply k (fun _ ↦ 1))
  rw [TestFunction.iteratedDerivApply_coe] at e1
  rw [iteratedDeriv_succ, e1, h'.integral_iteratedDeriv_mul, pow_succ]
  ring

/-- Peeling the first weak derivative: if `v` is the weak derivative of `f` and `w` the
`(k + 1)`-th weak derivative of `f`, then `w` is the `k`-th weak derivative of `v`. -/
theorem HasWeakDerivOn.hasWeakIteratedDerivOn_of_succ (h : HasWeakDerivOn f v a b)
    (h' : HasWeakIteratedDerivOn (k + 1) f w a b) : HasWeakIteratedDerivOn k v w a b := by
  refine hasWeakIteratedDerivOn_iff.2 ⟨h.locallyIntegrableOn_weakDeriv,
    h'.locallyIntegrableOn_weakDeriv, fun φ ↦ ?_⟩
  have e1 := h.integral_deriv_mul (φ.iteratedFDerivApply k (fun _ ↦ 1))
  rw [TestFunction.iteratedDerivApply_coe, ← iteratedDeriv_succ,
    h'.integral_iteratedDeriv_mul] at e1
  rw [neg_eq_iff_eq_neg.1 e1.symm, pow_succ]
  ring

/-- Peeling the last weak derivative: if `v` is the `k`-th and `w` the `(k + 1)`-th weak
derivative of `f`, then `w` is the weak derivative of `v`. This is what makes the weak
derivatives of a function of `H^m(a, b)` a chain, each the weak derivative of the one before. -/
theorem HasWeakIteratedDerivOn.hasWeakDerivOn_of_succ (h : HasWeakIteratedDerivOn k f v a b)
    (h' : HasWeakIteratedDerivOn (k + 1) f w a b) : HasWeakDerivOn v w a b := by
  refine hasWeakDerivOn_iff.2 ⟨h.locallyIntegrableOn_weakDeriv,
    h'.locallyIntegrableOn_weakDeriv, fun φ ↦ ?_⟩
  have e1 := h.integral_iteratedDeriv_mul (φ.fderivApply 1)
  rw [TestFunction.derivApply_coe, ← iteratedDeriv_succ', h'.integral_iteratedDeriv_mul] at e1
  have hk : ((-1 : ℝ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  refine mul_left_cancel₀ hk ?_
  rw [← e1, pow_succ]
  ring

/-- The weak derivative along any tuple of `k` directions all equal to `1` is the `k`-th weak
derivative on the interval; stated for a tuple whose length is only propositionally `k`, as the
tuples `multiIndexTuple` naming a multi-index are. -/
theorem hasWeakIteratedLineDerivOn_iff_hasWeakIteratedDerivOn {n : ℕ} {y : Fin n → ℝ}
    (hy : ∀ j, y j = 1) (hn : n = k) :
    HasWeakIteratedLineDerivOn y f w (Opens.Ioo a b) volume ↔
      HasWeakIteratedDerivOn k f w a b := by
  subst hn
  rw [show y = fun _ ↦ (1 : ℝ) from funext hy]

end Chain

/-! ### Test functions on an interval -/

namespace TestFunction

variable {a b : ℝ}

/-- A test function on `(a, b)` vanishes to the left of `a`. -/
theorem eq_zero_of_le_left (ψ : 𝓓(Opens.Ioo a b, ℝ)) {x : ℝ} (hx : x ≤ a) : ψ x = 0 :=
  ψ.eq_zero_of_notMem fun h ↦ (lt_irrefl a) (lt_of_lt_of_le h.1 hx)

/-- A test function on `(a, b)` vanishes to the right of `b`. -/
theorem eq_zero_of_le_right (ψ : 𝓓(Opens.Ioo a b, ℝ)) {x : ℝ} (hx : b ≤ x) : ψ x = 0 :=
  ψ.eq_zero_of_notMem fun h ↦ (lt_irrefl b) (lt_of_le_of_lt hx h.2)

/-- Integrating a test function on `(a, b)` against a function over `(a, b)` is integrating it
over the whole line. -/
theorem integral_eq_setIntegral_Ioo (ψ : 𝓓(Opens.Ioo a b, ℝ)) (g : ℝ → ℝ) :
    ∫ x in Ioo a b, ψ x * g x = ∫ x, ψ x * g x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
    rw [ψ.eq_zero_of_notMem hx, zero_mul]

/-- A test function on `(a, b)` is integrable for Lebesgue measure. -/
theorem integrable_volume (φ : 𝓓(Opens.Ioo a b, ℝ)) : Integrable φ :=
  φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport

/-- The support of a test function on `(a, b)` lies in a compact subinterval `[lo, hi]` with
`a < lo` and `hi < b`. -/
theorem exists_tsupport_subset_Icc (hab : a < b) (ψ : 𝓓(Opens.Ioo a b, ℝ)) :
    ∃ lo hi : ℝ, a < lo ∧ hi < b ∧ tsupport ψ ⊆ Icc lo hi := by
  by_cases hne : (tsupport ψ).Nonempty
  · obtain ⟨lo, hlo⟩ := ψ.hasCompactSupport.exists_isLeast hne
    obtain ⟨hi, hhi⟩ := ψ.hasCompactSupport.exists_isGreatest hne
    have hlo' : lo ∈ Ioo a b := ψ.tsupport_subset hlo.1
    have hhi' : hi ∈ Ioo a b := ψ.tsupport_subset hhi.1
    exact ⟨lo, hi, hlo'.1, hhi'.2, fun t ht ↦ ⟨hlo.2 ht, hhi.2 ht⟩⟩
  · refine ⟨(a + b) / 2, (a + b) / 2, by linarith, by linarith, ?_⟩
    rw [Set.not_nonempty_iff_eq_empty.1 hne]
    exact empty_subset _

/-- The antiderivative `x ↦ ∫_a^x ψ` of a test function `ψ` with zero mean vanishes outside any
interval `[lo, hi]` containing the support of `ψ`: to the left because the integrand vanishes,
to the right because the total integral does. -/
theorem support_integral_subset (ψ : 𝓓(Opens.Ioo a b, ℝ)) (hψ : ∫ x, ψ x = 0)
    {lo hi : ℝ} (hsupp : tsupport ψ ⊆ Icc lo hi) :
    Function.support (fun x ↦ ∫ t in a..x, ψ t) ⊆ Icc lo hi := by
  have hzero : ∀ t, t ∉ Icc lo hi → ψ t = 0 := fun t ht ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ ht (hsupp h)
  intro x hx
  by_contra hxI
  apply hx
  rcases le_or_gt x a with hxa | hax
  · refine (intervalIntegral.integral_congr (g := fun _ ↦ 0) fun t ht ↦ ?_).trans
      intervalIntegral.integral_zero
    exact ψ.eq_zero_of_le_left (ht.2.trans (max_le le_rfl hxa))
  rcases not_and_or.1 (mem_Icc.not.1 hxI) with hxlo | hxhi
  · refine (intervalIntegral.integral_congr (g := fun _ ↦ 0) fun t ht ↦ ?_).trans
      intervalIntegral.integral_zero
    refine hzero t fun htI ↦ hxlo ?_
    exact htI.1.trans (ht.2.trans (max_le hax.le le_rfl))
  · change ∫ t in a..x, ψ t = 0
    rw [intervalIntegral.integral_of_le hax.le,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦ ?_]
    · exact hψ
    · rcases not_and_or.1 (mem_Ioc.not.1 ht) with hta | htx
      · exact ψ.eq_zero_of_le_left (not_lt.1 hta)
      · exact hzero t fun htI ↦ hxhi ((not_le.1 htx).le.trans htI.2)

/-- **The antiderivative of a test function with zero mean is a test function**: for `ψ` a test
function on `(a, b)` with `∫ ψ = 0`, the function `x ↦ ∫_a^x ψ` is smooth with derivative `ψ`, it
vanishes to the left of the support of `ψ`, and to the right of it as well because the total
integral vanishes. This is what makes the derivatives of the test functions exactly the test
functions of zero mean, the fact behind du Bois-Reymond's lemma. -/
def primitive (hab : a < b) (ψ : 𝓓(Opens.Ioo a b, ℝ)) (hψ : ∫ x, ψ x = 0) :
    𝓓(Opens.Ioo a b, ℝ) where
  toFun x := ∫ t in a..x, ψ t
  contDiff' := by
    have hd : deriv (fun x ↦ ∫ t in a..x, ψ t) = ψ :=
      funext fun x ↦ Continuous.deriv_integral _ ψ.continuous a x
    exact contDiff_infty_iff_deriv.2 ⟨fun x ↦ (ψ.continuous.integral_hasStrictDerivAt a x)
      |>.hasDerivAt.differentiableAt, by rw [hd]; exact ψ.contDiff⟩
  hasCompactSupport' := by
    obtain ⟨lo, hi, -, -, hsupp⟩ := ψ.exists_tsupport_subset_Icc hab
    exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (ψ.support_integral_subset hψ hsupp)
  tsupport_subset' := by
    obtain ⟨lo, hi, hlo, hhi, hsupp⟩ := ψ.exists_tsupport_subset_Icc hab
    exact (closure_minimal (ψ.support_integral_subset hψ hsupp) isClosed_Icc).trans
      (Icc_subset_Ioo hlo hhi)

/-- `TestFunction.primitive` as a function. -/
@[simp]
theorem primitive_coe (hab : a < b) (ψ : 𝓓(Opens.Ioo a b, ℝ)) (hψ : ∫ x, ψ x = 0) :
    (primitive hab ψ hψ : ℝ → ℝ) = fun x ↦ ∫ t in a..x, ψ t := rfl

/-- The derivative of `TestFunction.primitive ψ` is `ψ`. -/
theorem deriv_primitive (hab : a < b) (ψ : 𝓓(Opens.Ioo a b, ℝ)) (hψ : ∫ x, ψ x = 0) :
    deriv (primitive hab ψ hψ) = ψ :=
  funext fun x ↦ Continuous.deriv_integral _ ψ.continuous a x

end TestFunction

/-- A test function on `(a, b)` with integral one: a normalized bump around the midpoint. -/
theorem exists_testFunction_integral_eq_one {a b : ℝ} (hab : a < b) :
    ∃ ψ : 𝓓(Opens.Ioo a b, ℝ), ∫ x, ψ x = 1 := by
  let φ : ContDiffBump ((a + b) / 2) := ⟨(b - a) / 8, (b - a) / 4, by linarith, by linarith⟩
  refine ⟨⟨φ.normed volume, φ.contDiff_normed (n := ⊤), φ.hasCompactSupport_normed, ?_⟩,
    φ.integral_normed⟩
  rw [φ.tsupport_normed_eq]
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  have hrOut : φ.rOut = (b - a) / 4 := rfl
  rw [hrOut] at hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-! ### Antiderivatives, and the absolutely continuous representative -/

section Integral

variable {a b : ℝ} {f w : ℝ → ℝ}

/-- A function integrable on `(a, b)` is integrable on `[a, b]`. -/
theorem MeasureTheory.IntegrableOn.integrableOn_Icc_of_Ioo (hw : IntegrableOn w (Ioo a b)) :
    IntegrableOn w (Icc a b) :=
  (integrableOn_Icc_iff_integrableOn_Ioo (f := w) (μ := volume) (a := a) (b := b) enorm_ne_top
    enorm_ne_top).2 hw

/-- A function integrable on `(a, b)` is interval integrable between any two points of
`[a, b]`. -/
theorem MeasureTheory.IntegrableOn.intervalIntegrable_of_Ioo (hw : IntegrableOn w (Ioo a b))
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) : IntervalIntegrable w volume x y :=
  (hw.integrableOn_Icc_of_Ioo.mono_set (uIcc_subset_Icc hx hy)).intervalIntegrable

/-- The antiderivative of a function integrable on `(a, b)` is continuous on `[a, b]`. -/
theorem continuousOn_integral_of_integrableOn_Ioo (hab : a ≤ b) (hw : IntegrableOn w (Ioo a b))
    (c : ℝ) : ContinuousOn (fun x ↦ c + ∫ t in a..x, w t) (Icc a b) :=
  continuousOn_const.add (by
    simpa [uIcc_of_le hab] using intervalIntegral.continuousOn_primitive_interval
      (μ := volume) (f := w) (a := a) (b := b)
      (by simpa [uIcc_of_le hab] using hw.integrableOn_Icc_of_Ioo))

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
    HasWeakDerivOn (fun x ↦ c + ∫ t in a..x, w t) w a b := by
  set g : ℝ → ℝ := fun x ↦ c + ∫ t in a..x, w t with hg
  refine hasWeakDerivOn_iff.2 ⟨((continuousOn_integral_of_integrableOn_Ioo hab hw c).mono
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

/-- **du Bois-Reymond's lemma on an interval**: a function whose weak derivative on `(a, b)`
vanishes is almost everywhere constant on `(a, b)`. The constant is `∫ ψ₀ f` for a fixed test
function `ψ₀` of integral one: for any test function `φ`, the function `φ - (∫ φ) ψ₀` has zero
mean, so its antiderivative is a test function (`TestFunction.primitive`) whose derivative it
is, and testing the hypothesis against that antiderivative gives `∫ φ (f - c) = 0`; the
generalized variational lemma `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` finishes. -/
theorem ae_eq_const_of_hasWeakDerivOn_zero (hab : a < b) (h : HasWeakDerivOn f 0 a b) :
    ∃ c : ℝ, f =ᵐ[volume.restrict (Ioo a b)] fun _ ↦ c := by
  obtain ⟨ψ₀, hψ₀⟩ := exists_testFunction_integral_eq_one hab
  refine ⟨∫ x in Ioo a b, ψ₀ x * f x, ?_⟩
  set c := ∫ x in Ioo a b, ψ₀ x * f x with hc
  have key : ∀ᵐ x, x ∈ Ioo a b → f x - c = 0 := by
    refine isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (h.locallyIntegrableOn.sub (continuous_const.locallyIntegrable.locallyIntegrableOn _))
      fun g hg h'g hgs ↦ ?_
    set φ : 𝓓(Opens.Ioo a b, ℝ) := ⟨g, hg, h'g, hgs⟩ with hφ
    set m := ∫ x, φ x with hm
    have hmean : ∫ x, (φ - m • ψ₀) x = 0 := by
      simp only [FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_sub φ.integrable_volume (ψ₀.integrable_volume.const_mul m), integral_const_mul,
        hψ₀]
      simp [hm]
    have hχ := h.integral_deriv_mul (TestFunction.primitive hab (φ - m • ψ₀) hmean)
    rw [TestFunction.deriv_primitive] at hχ
    simp only [FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, mul_zero, integral_zero, neg_zero, sub_mul, mul_assoc] at hχ
    have i1 : IntegrableOn (fun x ↦ φ x * f x) (Ioo a b) := (h.integrable_smul φ).integrableOn
    have i2 : IntegrableOn (fun x ↦ ψ₀ x * f x) (Ioo a b) := (h.integrable_smul ψ₀).integrableOn
    rw [integral_sub i1 (i2.const_mul m), integral_const_mul, sub_eq_zero] at hχ
    have i3 : Integrable (fun x ↦ g x * f x) := h.integrable_smul φ
    have i4 : Integrable (fun x ↦ g x * c) := φ.integrable_volume.mul_const c
    simp only [smul_eq_mul, mul_sub]
    rw [integral_sub i3 i4, integral_mul_const]
    change (∫ x, φ x * f x) - (∫ x, φ x) * c = 0
    rw [← φ.integral_eq_setIntegral_Ioo, hχ, ← hm, sub_self]
  exact (ae_restrict_iff' measurableSet_Ioo).2 (key.mono fun x hx hxI ↦ sub_eq_zero.1 (hx hxI))

/-- **The absolutely continuous representative**: a function with an integrable weak derivative
`w` on `(a, b)` agrees almost everywhere on `(a, b)` with `c + ∫_a^x w` for some constant `c`.
The difference of `f` and the antiderivative has weak derivative `0`, so it is almost everywhere
constant by du Bois-Reymond's lemma. -/
theorem HasWeakDerivOn.exists_ae_eq_integral (hab : a < b) (h : HasWeakDerivOn f w a b)
    (hw : IntegrableOn w (Ioo a b)) :
    ∃ c : ℝ, f =ᵐ[volume.restrict (Ioo a b)] fun x ↦ c + ∫ t in a..x, w t := by
  have h1 := hasWeakDerivOn_integral hab.le hw 0
  have h2 : HasWeakDerivOn (fun x ↦ f x - (0 + ∫ t in a..x, w t)) 0 a b :=
    (h.sub h1).congr_ae (Eventually.of_forall fun x ↦ rfl)
      (Eventually.of_forall fun x ↦ sub_self _)
  obtain ⟨c, hc⟩ := ae_eq_const_of_hasWeakDerivOn_zero hab h2
  refine ⟨c, hc.mono fun x hx ↦ ?_⟩
  simp only [zero_add] at hx ⊢
  linarith

/-- The absolutely continuous representative, as a function continuous on `[a, b]` that is the
integral of the weak derivative between any two points of `[a, b]`. -/
theorem HasWeakDerivOn.exists_continuousOn_ae_eq (hab : a < b) (h : HasWeakDerivOn f w a b)
    (hw : IntegrableOn w (Ioo a b)) :
    ∃ g : ℝ → ℝ, ContinuousOn g (Icc a b) ∧ f =ᵐ[volume.restrict (Ioo a b)] g ∧
      ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, g y - g x = ∫ t in x..y, w t := by
  obtain ⟨c, hc⟩ := h.exists_ae_eq_integral hab hw
  refine ⟨_, continuousOn_integral_of_integrableOn_Ioo hab.le hw c, hc, fun x hx y hy ↦ ?_⟩
  rw [add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
    (hw.intervalIntegrable_of_Ioo (left_mem_Icc.2 hab.le) hy)
    (hw.intervalIntegrable_of_Ioo (left_mem_Icc.2 hab.le) hx)]

end Integral

/-! ### The space `H^m(a, b)` -/

section Space

/-- The tuple of directions naming a multi-index of the one-element basis of `ℝ` is constantly
`1`. -/
theorem multiIndexTuple_singleton (α : Unit → ℕ) (j : Fin (∑ i, α i)) :
    multiIndexTuple (Module.Basis.singleton Unit ℝ) α j = 1 := by
  simp [multiIndexTuple, multiIndexDirections, List.getElem_replicate]

/-- **The Sobolev space `H^m(a, b) = W^{m,2}(a, b)`**: the multi-index Sobolev space
`SobolevMultiIndex` of `Numlib/Analysis/Sobolev/MultiIndex.lean` on `E = ℝ` with the one-element
basis, whose multi-indices of order at most `m` are the derivative orders `0, …, m`. Being an
`abbrev`, it inherits the `InnerProductSpace ℝ` and `CompleteSpace` instances of the multi-index
space: it is a Hilbert space for the inner product
`(u, v)_{H^m} = ∑_{j ≤ m} (u^{(j)}, v^{(j)})_{L²(a, b)}` (`SobolevInterval.inner_eq`). -/
abbrev SobolevInterval (m : ℕ) (a b : ℝ) : Type :=
  SobolevMultiIndex ℝ (Module.Basis.singleton Unit ℝ) m 2 (Opens.Ioo a b) volume

/-- `MemSobolevInterval f m a b` says that the function `f` belongs to `H^m(a, b)`: it lies in
`L²(a, b)` together with its weak derivatives of orders `1, …, m`. -/
def MemSobolevInterval (f : ℝ → ℝ) (m : ℕ) (a b : ℝ) : Prop :=
  MemSobolevMultiIndex (Module.Basis.singleton Unit ℝ) f m 2 (Opens.Ioo a b) volume

variable {m : ℕ} {a b : ℝ} {f : ℝ → ℝ}

/-- Membership of `H^m(a, b)` unfolded: `f ∈ L²(a, b)`, and for every `j ≤ m` the `j`-th weak
derivative of `f` on `(a, b)` exists and lies in `L²(a, b)`. -/
theorem memSobolevInterval_iff :
    MemSobolevInterval f m a b ↔ MemLp f 2 (volume.restrict (Ioo a b)) ∧ ∀ j ≤ m,
      ∃ w : ℝ → ℝ, HasWeakIteratedDerivOn j f w a b ∧ MemLp w 2 (volume.restrict (Ioo a b)) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j hj ↦ ?_⟩
    obtain ⟨w, hw, hwp⟩ := h2 (fun _ ↦ j) (by simpa using hj)
    exact ⟨w, (hasWeakIteratedLineDerivOn_iff_hasWeakIteratedDerivOn
      (multiIndexTuple_singleton _) (by simp)).1 hw, hwp⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun α hα ↦ ?_⟩
    obtain ⟨w, hw, hwp⟩ := h2 (α ()) (by simpa using hα)
    exact ⟨w, (hasWeakIteratedLineDerivOn_iff_hasWeakIteratedDerivOn
      (multiIndexTuple_singleton _) (by simp)).2 hw, hwp⟩

/-- `H^0(a, b)` is `L²(a, b)`. -/
theorem memSobolevInterval_zero_iff :
    MemSobolevInterval f 0 a b ↔ MemLp f 2 (volume.restrict (Ioo a b)) := by
  rw [memSobolevInterval_iff]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun j hj ↦ ?_⟩⟩
  obtain rfl : j = 0 := Nat.le_zero.1 hj
  exact ⟨f, HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
    (h.locallyIntegrableOn one_le_two), h⟩

/-- **The recursive description of `H^{m+1}(a, b)`**: a function lies in `H^{m+1}(a, b)` exactly
when it lies in `L²(a, b)` and has a weak derivative lying in `H^m(a, b)`. Forwards, the weak
derivatives of `f'` of orders `≤ m` are those of `f` of orders `≤ m + 1`; backwards, the chain
rule `HasWeakDerivOn.hasWeakIteratedDerivOn_succ`. -/
theorem memSobolevInterval_succ_iff :
    MemSobolevInterval f (m + 1) a b ↔ MemLp f 2 (volume.restrict (Ioo a b)) ∧
      ∃ w : ℝ → ℝ, HasWeakDerivOn f w a b ∧ MemSobolevInterval w m a b := by
  simp only [memSobolevInterval_iff]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨w, hw, hwp⟩ := h2 1 (by omega)
    refine ⟨h1, w, hw, hwp, fun j hj ↦ ?_⟩
    obtain ⟨w', hw', hwp'⟩ := h2 (j + 1) (by omega)
    exact ⟨w', HasWeakDerivOn.hasWeakIteratedDerivOn_of_succ hw hw', hwp'⟩
  · rintro ⟨h1, w, hw, hwp, h2⟩
    refine ⟨h1, fun j hj ↦ ?_⟩
    cases j with
    | zero =>
      exact ⟨f, HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _ hw.locallyIntegrableOn, h1⟩
    | succ j =>
      obtain ⟨w', hw', hwp'⟩ := h2 j (by omega)
      exact ⟨w', HasWeakDerivOn.hasWeakIteratedDerivOn_succ hw hw', hwp'⟩

/-- `H^1(a, b)` is the space of `L²(a, b)` functions with a weak derivative in `L²(a, b)`:
[quarteroni2000numerical] (12.42), without the boundary condition. -/
theorem memSobolevInterval_one_iff :
    MemSobolevInterval f 1 a b ↔ MemLp f 2 (volume.restrict (Ioo a b)) ∧
      ∃ w : ℝ → ℝ, HasWeakDerivOn f w a b ∧ MemLp w 2 (volume.restrict (Ioo a b)) := by
  simp only [memSobolevInterval_succ_iff, memSobolevInterval_zero_iff]

namespace SobolevInterval

/-- The function of an element of `H^m(a, b)`. -/
abbrev fn (u : SobolevInterval m a b) : ℝ → ℝ := SobolevMultiIndex.fn u

/-- The multi-index of the `j`-th derivative in one variable. -/
def derivIndex (m : ℕ) (j : Fin (m + 1)) : MultiIndexLE Unit m :=
  ⟨fun _ ↦ j, by simpa using Fin.is_le j⟩

/-- The derivative orders `0, …, m` are the multi-indices of order at most `m` in one
variable. -/
def derivIndexEquiv (m : ℕ) : Fin (m + 1) ≃ MultiIndexLE Unit m where
  toFun := derivIndex m
  invFun α := ⟨α.1 (), by have := α.2; simpa using Nat.lt_succ_of_le this⟩
  left_inv j := rfl
  right_inv α := Subtype.ext (funext fun _ ↦ rfl)

/-- The `j`-th weak derivative `u^{(j)}` of `u ∈ H^m(a, b)`, as an element of `L²(a, b)`; `j = 0`
is the function itself. -/
def deriv (u : SobolevInterval m a b) (j : Fin (m + 1)) : Lp ℝ 2 (volume.restrict (Ioo a b)) :=
  SobolevMultiIndex.weakDeriv u (derivIndex m j)

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
  Subtype.ext (PiLp.ext fun α ↦ h ((derivIndexEquiv m).symm α))

/-- The `j`-th component of an element of `H^m(a, b)` is the `j`-th weak derivative of its
function. -/
theorem hasWeakIteratedDerivOn_deriv (u : SobolevInterval m a b) (j : Fin (m + 1)) :
    HasWeakIteratedDerivOn j (fn u) (deriv u j) a b :=
  (hasWeakIteratedLineDerivOn_iff_hasWeakIteratedDerivOn (multiIndexTuple_singleton _)
    (by simp [derivIndex])).1 (SobolevMultiIndex.hasWeakIteratedLineDerivOn u (derivIndex m j))

/-- The weak derivatives of an element of `H^m(a, b)` form a chain: `u^{(j+1)}` is the weak
derivative of `u^{(j)}`. -/
theorem hasWeakDerivOn_deriv_succ (u : SobolevInterval m a b) (j : Fin m) :
    HasWeakDerivOn (deriv u j.castSucc) (deriv u j.succ) a b :=
  (hasWeakIteratedDerivOn_deriv u j.castSucc).hasWeakDerivOn_of_succ
    (hasWeakIteratedDerivOn_deriv u j.succ)

/-- The function of an element of `H^m(a, b)` lies in `H^m(a, b)`. -/
theorem memSobolevInterval_fn (u : SobolevInterval m a b) : MemSobolevInterval (fn u) m a b :=
  SobolevMultiIndex.memSobolevMultiIndex u

/-- The weak derivatives of an element of `H^m(a, b)` are integrable on `(a, b)`. -/
theorem integrableOn_deriv (u : SobolevInterval m a b) (j : Fin (m + 1)) :
    IntegrableOn (deriv u j) (Ioo a b) :=
  (Lp.memLp (deriv u j)).integrable one_le_two

/-- **The norm of `H^m(a, b)`**: `‖u‖² = ∑_{j ≤ m} ‖u^{(j)}‖²_{L²(a, b)}`, the norm (10.35) of
[quarteroni2000numerical]. -/
theorem norm_sq_eq (u : SobolevInterval m a b) :
    ‖u‖ ^ 2 = ∑ j : Fin (m + 1), ‖deriv u j‖ ^ 2 := by
  rw [Submodule.coe_norm, PiLp.norm_sq_eq_of_L2, ← (derivIndexEquiv m).sum_comp]
  rfl

/-- **The inner product of `H^m(a, b)`**: `(u, v)_{H^m} = ∑_{j ≤ m} (u^{(j)}, v^{(j)})_{L²(a, b)}`,
the inner product (10.34) of [quarteroni2000numerical]. -/
theorem inner_eq (u v : SobolevInterval m a b) :
    ⟪u, v⟫_ℝ = ∑ j : Fin (m + 1), ⟪deriv u j, deriv v j⟫_ℝ := by
  rw [Submodule.coe_inner, PiLp.inner_apply, ← (derivIndexEquiv m).sum_comp]
  rfl

/-- Each weak derivative is bounded by the `H^m` norm. -/
theorem norm_deriv_le (u : SobolevInterval m a b) (j : Fin (m + 1)) : ‖deriv u j‖ ≤ ‖u‖ := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, norm_sq_eq]
  exact Finset.single_le_sum (f := fun j ↦ ‖deriv u j‖ ^ 2) (fun _ _ ↦ sq_nonneg _)
    (Finset.mem_univ j)

variable (m a b) in
/-- The `j`-th weak derivative as a continuous linear map `H^m(a, b) → L²(a, b)`, of norm at most
one. -/
def derivL (j : Fin (m + 1)) : SobolevInterval m a b →L[ℝ] Lp ℝ 2 (volume.restrict (Ioo a b)) :=
  LinearMap.mkContinuous
    { toFun := fun u ↦ deriv u j
      map_add' := fun u v ↦ deriv_add u v j
      map_smul' := fun c u ↦ deriv_smul c u j } 1 fun u ↦ by
    rw [one_mul]; exact norm_deriv_le u j

/-- `SobolevInterval.derivL` is the weak derivative. -/
@[simp]
theorem derivL_apply (j : Fin (m + 1)) (u : SobolevInterval m a b) : derivL m a b j u = deriv u j :=
  rfl

variable (m a b) in
/-- **The Sobolev seminorm** `|u|_{H^m(a, b)} = ‖u^{(m)}‖_{L²(a, b)}`, bundled as a `Seminorm` so
that the seminorm forms of Céa's and Strang's lemmas apply to it; it is the `|·|_{H¹(0,1)}` of
[quarteroni2000numerical] (12.49). -/
def seminorm : Seminorm ℝ (SobolevInterval m a b) :=
  (normSeminorm ℝ (Lp ℝ 2 (volume.restrict (Ioo a b)))).comp
    (derivL m a b (Fin.last m) : SobolevInterval m a b →ₗ[ℝ] _)

/-- The seminorm is the `L²` norm of the top derivative. -/
theorem seminorm_apply (u : SobolevInterval m a b) : seminorm m a b u = ‖deriv u (Fin.last m)‖ :=
  rfl

/-- The seminorm is bounded by the norm. -/
theorem seminorm_le_norm (u : SobolevInterval m a b) : seminorm m a b u ≤ ‖u‖ :=
  norm_deriv_le u _

/-- Building an element of `H^m(a, b)` from `L²(a, b)` functions `v 0, …, v m` of which `v j` is
the `j`-th weak derivative of `v 0`. -/
def mk (v : Fin (m + 1) → Lp ℝ 2 (volume.restrict (Ioo a b)))
    (hv : ∀ j : Fin (m + 1), HasWeakIteratedDerivOn (j : ℕ) (v 0) (v j) a b) :
    SobolevInterval m a b :=
  ⟨WithLp.toLp 2 fun α ↦ v ((derivIndexEquiv m).symm α), fun α ↦
    (hasWeakIteratedLineDerivOn_iff_hasWeakIteratedDerivOn (multiIndexTuple_singleton _)
      (Fintype.sum_unique _)).2 (hv ((derivIndexEquiv m).symm α))⟩

/-- The weak derivatives of `SobolevInterval.mk v hv` are the `v j`. -/
@[simp]
theorem deriv_mk (v : Fin (m + 1) → Lp ℝ 2 (volume.restrict (Ioo a b)))
    (hv : ∀ j : Fin (m + 1), HasWeakIteratedDerivOn (j : ℕ) (v 0) (v j) a b) (j : Fin (m + 1)) :
    deriv (mk v hv) j = v j := rfl

/-- The function of `SobolevInterval.mk v hv` is `v 0`. -/
theorem fn_mk (v : Fin (m + 1) → Lp ℝ 2 (volume.restrict (Ioo a b)))
    (hv : ∀ j : Fin (m + 1), HasWeakIteratedDerivOn (j : ℕ) (v 0) (v j) a b) :
    fn (mk v hv) = v 0 := rfl

variable (m a b) in
/-- Weak differentiation `H^{m+1}(a, b) → H^m(a, b)` as a linear map. -/
def derivₗ : SobolevInterval (m + 1) a b →ₗ[ℝ] SobolevInterval m a b where
  toFun u := mk (fun j ↦ deriv u j.succ) fun j ↦ by
    have h0 := hasWeakDerivOn_deriv_succ u 0
    have h1 := hasWeakIteratedDerivOn_deriv u j.succ
    rw [Fin.castSucc_zero] at h0
    rw [Fin.val_succ, ← deriv_zero] at h1
    exact h0.hasWeakIteratedDerivOn_of_succ h1
  map_add' u v := ext fun j ↦ by simp only [deriv_mk, deriv_add]
  map_smul' c u := ext fun j ↦ by simp only [deriv_mk, deriv_smul, RingHom.id_apply]

/-- The weak derivatives of `u'` are those of `u`, shifted by one. -/
@[simp]
theorem deriv_derivₗ (u : SobolevInterval (m + 1) a b) (j : Fin (m + 1)) :
    deriv (derivₗ m a b u) j = deriv u j.succ := rfl

/-- Weak differentiation does not increase the norm. -/
theorem norm_derivₗ_le (u : SobolevInterval (m + 1) a b) : ‖derivₗ m a b u‖ ≤ ‖u‖ := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, norm_sq_eq,
    norm_sq_eq, Fin.sum_univ_succ (f := fun j ↦ ‖deriv u j‖ ^ 2)]
  simp only [deriv_derivₗ]
  exact le_add_of_nonneg_left (sq_nonneg _)

variable (m a b) in
/-- **Weak differentiation `d/dx : H^{m+1}(a, b) → H^m(a, b)`** as a continuous linear map, of
norm at most one. -/
def derivCLM : SobolevInterval (m + 1) a b →L[ℝ] SobolevInterval m a b :=
  (derivₗ m a b).mkContinuous 1 fun u ↦ by rw [one_mul]; exact norm_derivₗ_le u

/-- The weak derivatives of `u'` are those of `u`, shifted by one. -/
@[simp]
theorem deriv_derivCLM (u : SobolevInterval (m + 1) a b) (j : Fin (m + 1)) :
    deriv (derivCLM m a b u) j = deriv u j.succ := rfl

/-- Weak differentiation has norm at most one. -/
theorem norm_derivCLM_le : ‖derivCLM m a b‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

variable (m a b) in
/-- Forgetting the top derivative: the inclusion `H^{m+1}(a, b) → H^m(a, b)` as a linear map. -/
def inclusionₗ : SobolevInterval (m + 1) a b →ₗ[ℝ] SobolevInterval m a b where
  toFun u := mk (fun j ↦ deriv u j.castSucc) fun j ↦ by
    have h1 := hasWeakIteratedDerivOn_deriv u j.castSucc
    rw [Fin.val_castSucc, ← deriv_zero] at h1
    rw [Fin.castSucc_zero]
    exact h1
  map_add' u v := ext fun j ↦ by simp only [deriv_mk, deriv_add]
  map_smul' c u := ext fun j ↦ by simp only [deriv_mk, deriv_smul, RingHom.id_apply]

/-- The weak derivatives of the inclusion of `u` are those of `u`. -/
@[simp]
theorem deriv_inclusionₗ (u : SobolevInterval (m + 1) a b) (j : Fin (m + 1)) :
    deriv (inclusionₗ m a b u) j = deriv u j.castSucc := rfl

/-- The inclusion does not increase the norm. -/
theorem norm_inclusionₗ_le (u : SobolevInterval (m + 1) a b) : ‖inclusionₗ m a b u‖ ≤ ‖u‖ := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, norm_sq_eq,
    norm_sq_eq, Fin.sum_univ_castSucc (f := fun j ↦ ‖deriv u j‖ ^ 2)]
  simp only [deriv_inclusionₗ]
  exact le_add_of_nonneg_right (sq_nonneg _)

variable (m a b) in
/-- **The inclusion `H^{m+1}(a, b) → H^m(a, b)`**, forgetting the top derivative, as a continuous
linear map of norm at most one. -/
def inclusionCLM : SobolevInterval (m + 1) a b →L[ℝ] SobolevInterval m a b :=
  (inclusionₗ m a b).mkContinuous 1 fun u ↦ by rw [one_mul]; exact norm_inclusionₗ_le u

/-- The weak derivatives of the inclusion of `u` are those of `u`. -/
@[simp]
theorem deriv_inclusionCLM (u : SobolevInterval (m + 1) a b) (j : Fin (m + 1)) :
    deriv (inclusionCLM m a b u) j = deriv u j.castSucc := rfl

/-- The inclusion does not change the function. -/
theorem fn_inclusionCLM (u : SobolevInterval (m + 1) a b) : fn (inclusionCLM m a b u) = fn u :=
  rfl

/-- The inclusion has norm at most one. -/
theorem norm_inclusionCLM_le : ‖inclusionCLM m a b‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

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

end CauchySchwarz

/-! ### The continuous representative, and `H^1(a, b) ↪ C[a, b]` -/

section Embedding

variable {a b : ℝ}

/-- Two functions continuous on `[a, b]` and almost everywhere equal on `(a, b)` agree on all of
`[a, b]`. -/
theorem eqOn_Icc_of_ae_eq (hab : a < b) {g₁ g₂ : ℝ → ℝ} (h₁ : ContinuousOn g₁ (Icc a b))
    (h₂ : ContinuousOn g₂ (Icc a b)) (h : g₁ =ᵐ[volume.restrict (Ioo a b)] g₂) :
    EqOn g₁ g₂ (Icc a b) :=
  Measure.eqOn_of_ae_eq (by rwa [← restrict_Ioo_eq_restrict_Icc (μ := volume)]) h₁ h₂
    (by rw [interior_Icc, closure_Ioo hab.ne])

/-- Absolute continuity on `[a, b]` only sees the values on `[a, b]`. -/
theorem AbsolutelyContinuousOnInterval.congr {f g : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (h : EqOn f g (uIcc a b)) :
    AbsolutelyContinuousOnInterval g a b := by
  unfold AbsolutelyContinuousOnInterval at hf ⊢
  refine (tendsto_congr' ?_).1 hf
  refine Filter.eventually_inf_principal.2 (Eventually.of_forall fun E hE ↦ ?_)
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [h (hE.1 i hi).1, h (hE.1 i hi).2]

/-- A function continuous on `[a, b]` is essentially bounded on `(a, b)`. -/
theorem ContinuousOn.memLp_top_restrict_Ioo {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b)) :
    MemLp g ⊤ (volume.restrict (Ioo a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  exact memLp_top_of_bound ((hg.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)
    C ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx ↦
      hC x (Ioo_subset_Icc_self hx)))

/-- A function continuous on `[a, b]` lies in `L²(a, b)`. -/
theorem ContinuousOn.memLp_two_restrict_Ioo {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b)) :
    MemLp g 2 (volume.restrict (Ioo a b)) :=
  hg.memLp_top_restrict_Ioo.mono_exponent le_top

namespace SobolevInterval

/-- The function of `u ∈ H^1(a, b)` has the weak derivative `u'`. -/
theorem hasWeakDerivOn_fn (u : SobolevInterval 1 a b) : HasWeakDerivOn (fn u) (deriv u 1) a b := by
  have := hasWeakDerivOn_deriv_succ u 0
  rwa [Fin.castSucc_zero, Fin.succ_zero_eq_one, deriv_zero] at this

/-- The constant of the continuous representative of `u ∈ H^1(a, b)`: the mean over `(a, b)` of
`u - ∫_a^x u'`, chosen so as to depend linearly on `u`. -/
def repConst (u : SobolevInterval 1 a b) : ℝ :=
  (b - a)⁻¹ * ∫ t in Ioo a b, (fn u t - ∫ s in a..t, deriv u 1 s)

/-- **The continuous representative** of `u ∈ H^1(a, b)`, as a function on all of `ℝ`:
`repConst u + ∫_a^x u'`. It agrees with `u` almost everywhere on `(a, b)`
(`SobolevInterval.fn_ae_eq_rep`), is continuous and absolutely continuous on `[a, b]`, and is the
integral of `u'` between any two points of `[a, b]` (`SobolevInterval.rep_sub_rep`). The bundled
embedding `SobolevInterval.toContinuousMap` is this function restricted to `[a, b]`. -/
def rep (u : SobolevInterval 1 a b) (x : ℝ) : ℝ :=
  repConst u + ∫ t in a..x, deriv u 1 t

/-- The continuous representative is `repConst u + ∫_a^x u'`. -/
theorem rep_apply (u : SobolevInterval 1 a b) (x : ℝ) :
    rep u x = repConst u + ∫ t in a..x, deriv u 1 t := rfl

/-- The continuous representative is continuous on `[a, b]`. -/
theorem continuousOn_rep (hab : a ≤ b) (u : SobolevInterval 1 a b) :
    ContinuousOn (rep u) (Icc a b) :=
  continuousOn_integral_of_integrableOn_Ioo hab (integrableOn_deriv u 1) _

/-- The continuous representative is absolutely continuous on `[a, b]`. -/
theorem absolutelyContinuousOnInterval_rep (hab : a ≤ b) (u : SobolevInterval 1 a b) :
    AbsolutelyContinuousOnInterval (rep u) a b :=
  absolutelyContinuousOnInterval_integral hab (integrableOn_deriv u 1) _

/-- The continuous representative has the weak derivative `u'`. -/
theorem hasWeakDerivOn_rep (hab : a ≤ b) (u : SobolevInterval 1 a b) :
    HasWeakDerivOn (rep u) (deriv u 1) a b :=
  hasWeakDerivOn_integral hab (integrableOn_deriv u 1) _

/-- The classical derivative of the continuous representative is `u'` almost everywhere. -/
theorem ae_deriv_rep_eq (hab : a ≤ b) (u : SobolevInterval 1 a b) :
    ∀ᵐ x, x ∈ Ioc a b → _root_.deriv (rep u) x = deriv u 1 x :=
  ae_deriv_integral_eq hab (integrableOn_deriv u 1) _

/-- **The fundamental theorem of calculus in `H^1(a, b)`**: the continuous representative is the
integral of `u'` between any two points of `[a, b]`. -/
theorem rep_sub_rep (hab : a ≤ b) (u : SobolevInterval 1 a b) {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc a b) : rep u y - rep u x = ∫ t in x..y, deriv u 1 t := by
  simp only [rep_apply]
  rw [add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
    ((integrableOn_deriv u 1).intervalIntegrable_of_Ioo (left_mem_Icc.2 hab) hy)
    ((integrableOn_deriv u 1).intervalIntegrable_of_Ioo (left_mem_Icc.2 hab) hx)]

/-- The function of `u ∈ H^1(a, b)` agrees almost everywhere on `(a, b)` with its continuous
representative: the constant of `HasWeakDerivOn.exists_ae_eq_integral` is `repConst u`, by
integrating the almost everywhere identity over `(a, b)`. -/
theorem fn_ae_eq_rep (hab : a < b) (u : SobolevInterval 1 a b) :
    fn u =ᵐ[volume.restrict (Ioo a b)] rep u := by
  obtain ⟨c, hc⟩ := (hasWeakDerivOn_fn u).exists_ae_eq_integral hab (integrableOn_deriv u 1)
  have hcc : repConst u = c := by
    have : ∫ t in Ioo a b, (fn u t - ∫ s in a..t, deriv u 1 s) = ∫ t in Ioo a b, c := by
      refine integral_congr_ae (hc.mono fun t ht ↦ ?_)
      dsimp only
      rw [ht]; ring
    rw [repConst, this, setIntegral_const, Real.volume_real_Ioo_of_le hab.le, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ (sub_pos.2 hab).ne', one_mul]
  exact hc.trans (Eventually.of_forall fun x ↦ by rw [rep_apply, hcc])

/-- The continuous representative is canonical: any function continuous on `[a, b]` that agrees
almost everywhere with `u` on `(a, b)` is the representative on all of `[a, b]`. -/
theorem rep_eq_of_continuousOn (hab : a < b) (u : SobolevInterval 1 a b) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) (hu : fn u =ᵐ[volume.restrict (Ioo a b)] g) :
    EqOn (rep u) g (Icc a b) :=
  eqOn_Icc_of_ae_eq hab (continuousOn_rep hab.le u) hg ((fn_ae_eq_rep hab u).symm.trans hu)

/-- The continuous representative of a sum. -/
theorem rep_add (hab : a < b) (u v : SobolevInterval 1 a b) :
    EqOn (rep (u + v)) (rep u + rep v) (Icc a b) :=
  rep_eq_of_continuousOn hab (u + v) ((continuousOn_rep hab.le u).add (continuousOn_rep hab.le v))
    ((SobolevMultiIndex.fn_add u v).trans ((fn_ae_eq_rep hab u).add (fn_ae_eq_rep hab v)))

/-- The continuous representative of a scalar multiple. -/
theorem rep_smul (hab : a < b) (c : ℝ) (u : SobolevInterval 1 a b) :
    EqOn (rep (c • u)) (c • rep u) (Icc a b) :=
  rep_eq_of_continuousOn hab (c • u) ((continuousOn_rep hab.le u).const_smul c)
    ((SobolevMultiIndex.fn_smul c u).trans ((fn_ae_eq_rep hab u).const_smul c))

/-- **The pointwise bound of the embedding `H^1(a, b) ↪ C[a, b]`**:
`|u(x)| ≤ ((b - a)^{-1/2} + (b - a)^{1/2}) ‖u‖_{H^1}` for `x ∈ [a, b]`. From
`u(x) = u(y) + ∫_y^x u'` and Cauchy–Schwarz, `|u(x)| ≤ |u(y)| + √(b - a) ‖u'‖_{L²}` for every
`y ∈ [a, b]`; averaging over `y ∈ (a, b)` and applying Cauchy–Schwarz to `∫ |u|` gives the
bound. -/
theorem abs_rep_le (hab : a < b) (u : SobolevInterval 1 a b) {x : ℝ} (hx : x ∈ Icc a b) :
    |rep u x| ≤ (1 / Real.sqrt (b - a) + Real.sqrt (b - a)) * ‖u‖ := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hsq : 0 < Real.sqrt (b - a) := Real.sqrt_pos.2 hba
  -- `|g x| ≤ |g y| + √(b - a) ‖u'‖` for every `y ∈ [a, b]`
  have key : ∀ y ∈ Icc a b, |rep u x| ≤ |rep u y| + Real.sqrt (b - a) * ‖deriv u 1‖ := by
    intro y hy
    have e : rep u x = rep u y + ∫ t in y..x, deriv u 1 t := by
      simp only [rep_apply]
      rw [add_assoc, intervalIntegral.integral_add_adjacent_intervals
        ((integrableOn_deriv u 1).intervalIntegrable_of_Ioo (left_mem_Icc.2 hab.le) hy)
        ((integrableOn_deriv u 1).intervalIntegrable_of_Ioo hy hx)]
    rw [e]
    refine (abs_add_le _ _).trans ?_
    gcongr
    rcases le_total y x with hyx | hxy
    · refine (abs_intervalIntegral_le_sqrt_mul_norm _ hy hx hyx).trans ?_
      gcongr <;> linarith [hx.1, hx.2, hy.1, hy.2]
    · rw [intervalIntegral.integral_symm, abs_neg]
      refine (abs_intervalIntegral_le_sqrt_mul_norm _ hx hy hxy).trans ?_
      gcongr <;> linarith [hx.1, hx.2, hy.1, hy.2]
  -- average over `y ∈ (a, b)`
  have hint : ∫ y in Ioo a b, |rep u x|
      ≤ ∫ y in Ioo a b, (|rep u y| + Real.sqrt (b - a) * ‖deriv u 1‖) := by
    refine setIntegral_mono_on (integrableOn_const (by simp)) ?_ measurableSet_Ioo fun y hy ↦
      key y (Ioo_subset_Icc_self hy)
    refine ((continuousOn_rep hab.le u).abs.integrableOn_Icc.mono_set Ioo_subset_Icc_self).add
      (integrableOn_const (by simp))
  rw [setIntegral_const, integral_add ((continuousOn_rep hab.le u).abs.integrableOn_Icc.mono_set
    Ioo_subset_Icc_self) (integrableOn_const (by simp)), setIntegral_const,
    Real.volume_real_Ioo_of_le hab.le, smul_eq_mul, smul_eq_mul] at hint
  have habs : ∫ y in Ioo a b, |rep u y| ≤ Real.sqrt (b - a) * ‖deriv u 0‖ := by
    have e : ∫ y in Ioo a b, |rep u y| = ∫ y in Ioo a b, |(deriv u 0 : ℝ → ℝ) y| :=
      integral_congr_ae ((fn_ae_eq_rep hab u).mono fun y hy ↦ by
        change |rep u y| = |fn u y|
        rw [hy])
    rw [e]
    exact integral_abs_le_sqrt_mul_norm hab.le _
  have h0 := norm_deriv_le u 0
  have h1 := norm_deriv_le u 1
  have hsqsq : Real.sqrt (b - a) * Real.sqrt (b - a) = b - a := Real.mul_self_sqrt hba.le
  have h1sq : (b - a)⁻¹ * Real.sqrt (b - a) = 1 / Real.sqrt (b - a) := by
    rw [eq_div_iff hsq.ne', mul_assoc, hsqsq, inv_mul_cancel₀ hba.ne']
  calc |rep u x| = (b - a)⁻¹ * ((b - a) * |rep u x|) := by
        rw [← mul_assoc, inv_mul_cancel₀ hba.ne', one_mul]
    _ ≤ (b - a)⁻¹ * (Real.sqrt (b - a) * ‖deriv u 0‖ +
          (b - a) * (Real.sqrt (b - a) * ‖deriv u 1‖)) := by
      gcongr
      linarith
    _ ≤ (b - a)⁻¹ * (Real.sqrt (b - a) * ‖u‖ + (b - a) * (Real.sqrt (b - a) * ‖u‖)) := by
      gcongr
    _ = ((b - a)⁻¹ * Real.sqrt (b - a) + (b - a)⁻¹ * (b - a) * Real.sqrt (b - a)) * ‖u‖ := by
      ring
    _ = (1 / Real.sqrt (b - a) + Real.sqrt (b - a)) * ‖u‖ := by
      rw [h1sq, inv_mul_cancel₀ hba.ne', one_mul]

/-- The embedding `H^1(a, b) → C[a, b]` as a linear map: `u ↦` its continuous representative,
restricted to `[a, b]`. Linearity is the canonicity of the representative. -/
def toContinuousMapₗ (hab : a < b) : SobolevInterval 1 a b →ₗ[ℝ] C(Icc a b, ℝ) where
  toFun u := ⟨fun x ↦ rep u x,
    (continuousOn_rep hab.le u).comp_continuous continuous_subtype_val fun x ↦ x.2⟩
  map_add' u v := ContinuousMap.ext fun x ↦ rep_add hab u v x.2
  map_smul' c u := ContinuousMap.ext fun x ↦ rep_smul hab c u x.2

/-- The embedding constant, for the linear map. -/
theorem norm_toContinuousMapₗ_le (hab : a < b) (u : SobolevInterval 1 a b) :
    ‖toContinuousMapₗ hab u‖ ≤ (1 / Real.sqrt (b - a) + Real.sqrt (b - a)) * ‖u‖ :=
  (ContinuousMap.norm_le _ (by positivity)).2 fun x ↦ by
    rw [Real.norm_eq_abs]; exact abs_rep_le hab u x.2

/-- **The embedding `H^1(a, b) ↪ C[a, b]`**: the continuous linear map sending `u ∈ H^1(a, b)` to
its continuous representative `x ↦ repConst u + ∫_a^x u'` on `[a, b]`, of norm at most
`(b - a)^{-1/2} + (b - a)^{1/2}` (`SobolevInterval.norm_toContinuousMap_le`). For `H^m(a, b)`
with `m ≥ 1`, compose with `SobolevInterval.inclusionCLM`. -/
def toContinuousMap (hab : a < b) : SobolevInterval 1 a b →L[ℝ] C(Icc a b, ℝ) :=
  (toContinuousMapₗ hab).mkContinuous _ (norm_toContinuousMapₗ_le hab)

/-- The embedding is the continuous representative on `[a, b]`. -/
theorem toContinuousMap_apply (hab : a < b) (u : SobolevInterval 1 a b) (x : Icc a b) :
    toContinuousMap hab u x = rep u x := rfl

/-- **The embedding constant of `H^1(a, b) ↪ C[a, b]`**:
`‖u‖_∞ ≤ ((b - a)^{-1/2} + (b - a)^{1/2}) ‖u‖_{H^1}`. -/
theorem norm_toContinuousMap_le (hab : a < b) (u : SobolevInterval 1 a b) :
    ‖toContinuousMap hab u‖ ≤ (1 / Real.sqrt (b - a) + Real.sqrt (b - a)) * ‖u‖ :=
  norm_toContinuousMapₗ_le hab u

/-- The operator norm of the embedding `H^1(a, b) ↪ C[a, b]` is at most
`(b - a)^{-1/2} + (b - a)^{1/2}`. -/
theorem norm_toContinuousMap_le' (hab : a < b) :
    ‖toContinuousMap hab‖ ≤ 1 / Real.sqrt (b - a) + Real.sqrt (b - a) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- The function of `u` agrees almost everywhere on `(a, b)` with its embedding into `C[a, b]`,
extended by the endpoint values outside `[a, b]`. -/
theorem coe_toContinuousMap_ae_eq (hab : a < b) (u : SobolevInterval 1 a b) :
    fn u =ᵐ[volume.restrict (Ioo a b)] IccExtend hab.le (toContinuousMap hab u) :=
  (fn_ae_eq_rep hab u).trans ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall
    fun x hx ↦ by rw [IccExtend_of_mem hab.le _ (Ioo_subset_Icc_self hx)]; rfl))

/-- The embedding is canonical: any function continuous on `[a, b]` that agrees almost everywhere
with `u` on `(a, b)` is the embedding of `u` on all of `[a, b]`. -/
theorem toContinuousMap_eq_of_continuousOn (hab : a < b) (u : SobolevInterval 1 a b) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) (hu : fn u =ᵐ[volume.restrict (Ioo a b)] g) (x : Icc a b) :
    toContinuousMap hab u x = g x :=
  rep_eq_of_continuousOn hab u hg hu x.2

/-- **The fundamental theorem of calculus in `H^1(a, b)`**: the embedding of `u` into `C[a, b]`
is the integral of `u'` between any two points of `[a, b]`. -/
theorem toContinuousMap_sub_eq_integral (hab : a < b) (u : SobolevInterval 1 a b)
    (x y : Icc a b) :
    toContinuousMap hab u y - toContinuousMap hab u x = ∫ t in (x : ℝ)..y, deriv u 1 t :=
  rep_sub_rep hab.le u x.2 y.2

/-- The embedding of `u` into `C[a, b]`, extended by the endpoint values outside `[a, b]`, is
absolutely continuous on `[a, b]`. -/
theorem absolutelyContinuousOnInterval_toContinuousMap (hab : a < b)
    (u : SobolevInterval 1 a b) :
    AbsolutelyContinuousOnInterval (IccExtend hab.le (toContinuousMap hab u)) a b :=
  (absolutelyContinuousOnInterval_rep hab.le u).congr fun x hx ↦ by
    rw [uIcc_of_le hab.le] at hx
    rw [IccExtend_of_mem hab.le _ hx]; rfl

end SobolevInterval

end Embedding

/-! ### Integration by parts and the product rule in `H^1(a, b)` -/

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

/-- **Integration by parts in `H^1(a, b)`**: for `u, v ∈ H^1(a, b)` with continuous
representatives `g_u, g_v`, `∫_a^b (u' g_v + g_u v') = g_u(b) g_v(b) - g_u(a) g_v(a)`. -/
theorem integral_deriv_mul_add_mul_deriv (hab : a < b) (u v : SobolevInterval 1 a b) :
    ∫ t in a..b, (deriv u 1 t * rep v t + rep u t * deriv v 1 t) =
      rep u b * rep v b - rep u a * rep v a := by
  have := integral_mul_add_mul_of_eq_integral hab.le (integrableOn_deriv u 1)
    (integrableOn_deriv v 1) (repConst u) (repConst v) (right_mem_Icc.2 hab.le)
  simp only [rep_apply, intervalIntegral.integral_same, add_zero]
  rw [← this]

/-- **Integration by parts in `H^1(a, b)` against an absolutely continuous factor** `ψ`:
`∫_a^b u' ψ = [g_u ψ]_a^b - ∫_a^b g_u ψ'`, where `ψ'` is the classical derivative, which exists
almost everywhere. -/
theorem integral_deriv_mul_eq_sub_integral_mul_deriv (hab : a < b) (u : SobolevInterval 1 a b)
    {ψ : ℝ → ℝ} (hψ : AbsolutelyContinuousOnInterval ψ a b) :
    ∫ t in a..b, deriv u 1 t * ψ t =
      rep u b * ψ b - rep u a * ψ a - ∫ t in a..b, rep u t * _root_.deriv ψ t := by
  have key := (absolutelyContinuousOnInterval_rep hab.le u).integral_deriv_mul_eq_sub hψ
  rw [← key, ← intervalIntegral.integral_sub]
  · refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_deriv_rep_eq hab.le u] with t h1 ht
    rw [uIoc_of_le hab.le] at ht
    rw [h1 ht]; ring
  · exact ((absolutelyContinuousOnInterval_rep hab.le u).intervalIntegrable_deriv.mul_continuousOn
      hψ.continuousOn).add (hψ.intervalIntegrable_deriv.continuousOn_mul
      (absolutelyContinuousOnInterval_rep hab.le u).continuousOn)
  · exact hψ.intervalIntegrable_deriv.continuousOn_mul
      (absolutelyContinuousOnInterval_rep hab.le u).continuousOn

/-- **Integration by parts in `H^1(a, b)` against a `C¹` factor** `ψ`, such as a coefficient of
a differential operator: `∫_a^b u' ψ = [g_u ψ]_a^b - ∫_a^b g_u ψ'`. -/
theorem integral_deriv_mul_contDiffOn (hab : a < b) (u : SobolevInterval 1 a b)
    {ψ : ℝ → ℝ} (hψ : ContDiffOn ℝ 1 ψ (Icc a b)) :
    ∫ t in a..b, deriv u 1 t * ψ t =
      rep u b * ψ b - rep u a * ψ a - ∫ t in a..b, rep u t * _root_.deriv ψ t :=
  integral_deriv_mul_eq_sub_integral_mul_deriv hab u
    (by rw [← uIcc_of_le hab.le] at hψ; exact hψ.absolutelyContinuousOnInterval)

/-- The product of two continuous representatives is the antiderivative of the Leibniz
expression `u' g_v + g_u v'`. -/
theorem rep_mul_rep_eq (hab : a < b) (u v : SobolevInterval 1 a b) {x : ℝ} (hx : x ∈ Icc a b) :
    rep u x * rep v x = repConst u * repConst v +
      ∫ t in a..x, (deriv u 1 t * rep v t + rep u t * deriv v 1 t) := by
  have := integral_mul_add_mul_of_eq_integral hab.le (integrableOn_deriv u 1)
    (integrableOn_deriv v 1) (repConst u) (repConst v) hx
  simp only [rep_apply]
  rw [← this]
  ring

/-- The Leibniz expression `u' g_v + g_u v'` is integrable on `(a, b)`. -/
theorem integrableOn_leibniz (hab : a < b) (u v : SobolevInterval 1 a b) :
    IntegrableOn (fun t ↦ deriv u 1 t * rep v t + rep u t * deriv v 1 t) (Ioo a b) :=
  ((integrableOn_deriv u 1).mul_continuousOn_of_subset (continuousOn_rep hab.le v)
    measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self).add
    ((integrableOn_deriv v 1).continuousOn_mul_of_subset (continuousOn_rep hab.le u)
    isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self)

/-- **The product rule in `H^1(a, b)`**, weak derivative form: the product `g_u g_v` of the
continuous representatives has the weak derivative `u' g_v + g_u v'` on `(a, b)`. -/
theorem hasWeakDerivOn_rep_mul (hab : a < b) (u v : SobolevInterval 1 a b) :
    HasWeakDerivOn (fun t ↦ rep u t * rep v t)
      (fun t ↦ deriv u 1 t * rep v t + rep u t * deriv v 1 t) a b :=
  (hasWeakDerivOn_integral hab.le (integrableOn_leibniz hab u v) (repConst u * repConst v)).congr_ae
    ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun _ hx ↦
      (rep_mul_rep_eq hab u v (Ioo_subset_Icc_self hx)).symm)) (Eventually.of_forall fun _ ↦ rfl)

/-- The Leibniz expression `u' g_v + g_u v'` lies in `L²(a, b)`: a product of an `L²` function
and a bounded one. -/
theorem memLp_leibniz (hab : a < b) (u v : SobolevInterval 1 a b) :
    MemLp (fun t ↦ deriv u 1 t * rep v t + rep u t * deriv v 1 t) 2
      (volume.restrict (Ioo a b)) := by
  have h1 : MemLp (fun t ↦ deriv u 1 t * rep v t) 2 (volume.restrict (Ioo a b)) :=
    MemLp.mul' (continuousOn_rep hab.le v).memLp_top_restrict_Ioo (Lp.memLp (deriv u 1))
  have h2 : MemLp (fun t ↦ rep u t * deriv v 1 t) 2 (volume.restrict (Ioo a b)) :=
    MemLp.mul' (Lp.memLp (deriv v 1)) (continuousOn_rep hab.le u).memLp_top_restrict_Ioo
  exact h1.add h2

/-- **The product rule in `H^1(a, b)`**: the product of the continuous representatives of two
elements of `H^1(a, b)` lies in `H^1(a, b)`, with weak derivative `u' g_v + g_u v'`
(`SobolevInterval.hasWeakDerivOn_rep_mul`). -/
theorem memSobolevInterval_mul (hab : a < b) (u v : SobolevInterval 1 a b) :
    MemSobolevInterval (fun t ↦ rep u t * rep v t) 1 a b :=
  memSobolevInterval_one_iff.2 ⟨((continuousOn_rep hab.le u).mul
    (continuousOn_rep hab.le v)).memLp_two_restrict_Ioo, _, hasWeakDerivOn_rep_mul hab u v,
    memLp_leibniz hab u v⟩

end SobolevInterval

end Leibniz

/-! ### Poincaré's inequality, and `H^1_0(a, b)` -/

section Poincare

variable {a b : ℝ}

/-- `‖f‖² = ∫_a^b |f|²` in `L²(a, b)`. -/
theorem norm_sq_eq_integral_sq (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    ‖f‖ ^ 2 = ∫ x in Ioo a b, |f x| ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs]

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
`H^1(a, b)`: `SobolevMultiIndexZero` of `Numlib/Analysis/Sobolev/MultiIndex.lean` on the
interval. A closed subspace of a Hilbert space, hence a Hilbert space. It is the space `V` of
[quarteroni2000numerical] §12.4.1, and by `mem_sobolevIntervalZero_iff` it is exactly the set
(12.42) of functions of `H^1(a, b)` vanishing at both endpoints. -/
abbrev SobolevIntervalZero (a b : ℝ) : Submodule ℝ (SobolevInterval 1 a b) :=
  SobolevMultiIndexZero ℝ (Module.Basis.singleton Unit ℝ) 1 2 (Opens.Ioo a b) volume

namespace SobolevIntervalZero

/-- An element of `H^1(a, b)` whose function is a test function lies in `H^1_0(a, b)`. -/
theorem mem_of_fn_ae_eq (φ : 𝓓(Opens.Ioo a b, ℝ)) {u : SobolevInterval 1 a b}
    (hu : SobolevInterval.fn u =ᵐ[volume.restrict (Ioo a b)] φ) : u ∈ SobolevIntervalZero a b :=
  SobolevMultiIndexZero.testFunctions_le ⟨φ, hu⟩

/-- Every test function on `(a, b)` is the function of an element of `H^1_0(a, b)`. -/
theorem exists_mem_fn_ae_eq (φ : 𝓓(Opens.Ioo a b, ℝ)) :
    ∃ u ∈ SobolevIntervalZero a b, SobolevInterval.fn u =ᵐ[volume.restrict (Ioo a b)] φ :=
  let ⟨u, hu, hφ⟩ := TestFunction.exists_mem_sobolevMultiIndex_testFunctions
    (b := Module.Basis.singleton Unit ℝ) (k := 1) (p := 2) φ
  ⟨u, SobolevMultiIndexZero.testFunctions_le hu, hφ⟩

open SobolevInterval in
/-- The continuous representative of an element of `H^1_0(a, b)` vanishes at `a`: evaluation
at `a` is a continuous linear functional on `H^1(a, b)` that vanishes on the test functions, hence
on their closure. -/
theorem rep_left_eq_zero (hab : a < b) {u : SobolevInterval 1 a b}
    (hu : u ∈ SobolevIntervalZero a b) : rep u a = 0 := by
  let e : SobolevInterval 1 a b →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM ℝ (⟨a, left_mem_Icc.2 hab.le⟩ : Icc a b)).comp (toContinuousMap hab)
  have hker : SobolevMultiIndex.testFunctions ℝ (Module.Basis.singleton Unit ℝ) 1 2
      (Opens.Ioo a b) volume ≤ LinearMap.ker (e : SobolevInterval 1 a b →ₗ[ℝ] ℝ) := by
    rintro v ⟨φ, hφ⟩
    change toContinuousMap hab v ⟨a, _⟩ = 0
    rw [toContinuousMap_eq_of_continuousOn hab v φ.continuous.continuousOn hφ]
    exact φ.eq_zero_of_le_left le_rfl
  exact Submodule.topologicalClosure_minimal _ hker e.isClosed_ker hu

open SobolevInterval in
/-- The continuous representative of an element of `H^1_0(a, b)` vanishes at `b`. -/
theorem rep_right_eq_zero (hab : a < b) {u : SobolevInterval 1 a b}
    (hu : u ∈ SobolevIntervalZero a b) : rep u b = 0 := by
  let e : SobolevInterval 1 a b →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM ℝ (⟨b, right_mem_Icc.2 hab.le⟩ : Icc a b)).comp (toContinuousMap hab)
  have hker : SobolevMultiIndex.testFunctions ℝ (Module.Basis.singleton Unit ℝ) 1 2
      (Opens.Ioo a b) volume ≤ LinearMap.ker (e : SobolevInterval 1 a b →ₗ[ℝ] ℝ) := by
    rintro v ⟨φ, hφ⟩
    change toContinuousMap hab v ⟨b, _⟩ = 0
    rw [toContinuousMap_eq_of_continuousOn hab v φ.continuous.continuousOn hφ]
    exact φ.eq_zero_of_le_right le_rfl
  exact Submodule.topologicalClosure_minimal _ hker e.isClosed_ker hu

open SobolevInterval in
/-- **An element of `H^1_0(a, b)` vanishes at both endpoints**: the trace of `H^1_0(a, b)` is
zero. -/
theorem toContinuousMap_eq_zero (hab : a < b) {u : SobolevInterval 1 a b}
    (hu : u ∈ SobolevIntervalZero a b) :
    toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩ = 0 ∧
      toContinuousMap hab u ⟨b, right_mem_Icc.2 hab.le⟩ = 0 :=
  ⟨rep_left_eq_zero hab hu, rep_right_eq_zero hab hu⟩

open SobolevInterval in
/-- The continuous representative of an element of `H^1_0(a, b)` is `∫_a^x u'`. -/
theorem rep_eq_integral (hab : a < b) {u : SobolevInterval 1 a b}
    (hu : u ∈ SobolevIntervalZero a b) (x : ℝ) : rep u x = ∫ t in a..x, deriv u 1 t := by
  have h := rep_left_eq_zero hab hu
  rw [rep_apply, intervalIntegral.integral_same, add_zero] at h
  rw [rep_apply, h, zero_add]

open SobolevInterval in
/-- **Poincaré's inequality on `H^1_0(a, b)`**, [quarteroni2000numerical] (12.16) with the
explicit constant `C_P = (b - a)/√2`: `‖u‖_{L²(a, b)} ≤ ((b - a)/√2) ‖u'‖_{L²(a, b)}`. An
element of `H^1_0(a, b)` is the antiderivative of its derivative, so this is the elementary form
`SobolevInterval.norm_le_of_eq_integral`. -/
theorem norm_deriv_zero_le (hab : a < b) {u : SobolevInterval 1 a b}
    (hu : u ∈ SobolevIntervalZero a b) :
    ‖deriv u 0‖ ≤ (b - a) / Real.sqrt 2 * ‖deriv u 1‖ :=
  norm_le_of_eq_integral hab.le ((fn_ae_eq_rep hab u).trans (Eventually.of_forall
    fun x ↦ rep_eq_integral hab hu x))

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
/-- The seminorm `|·|_{H^1}` is a norm on `H^1_0(a, b)`. -/
theorem seminorm_eq_zero_iff (hab : a < b) {u : SobolevInterval 1 a b}
    (hu : u ∈ SobolevIntervalZero a b) : seminorm 1 a b u = 0 ↔ u = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h, seminorm_apply, deriv_zero_elem]⟩
  have := norm_le_seminorm hab hu
  rw [h, mul_zero] at this
  exact norm_le_zero_iff.1 this

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
      ≤ eLpNorm (S.indicator fun _ ↦ C) 2 (volume.restrict (Ioo a b)) := eLpNorm_mono_ae hpt
    _ ≤ ‖C‖ₑ * (volume.restrict (Ioo a b)) S ^ (1 / (2 : ℝ≥0∞).toReal) :=
        eLpNorm_indicator_const_le C 2
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
        exact eLpNorm_add_le (hw.aestronglyMeasurable.sub hg.continuous.aestronglyMeasurable)
          (hg.continuous.aestronglyMeasurable.sub ψ.continuous.aestronglyMeasurable) one_le_two
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
in `H^1_0(a, b)`**, the converse of `SobolevIntervalZero.toContinuousMap_eq_zero`.

The derivative `u'` has zero mean on `(a, b)`, since `u(b) - u(a) = ∫_a^b u'`. Approximate `u'` in
`L²(a, b)` by a test function `ψ` (`exists_testFunction_norm_sub_toLp_le`), correct its mean by
a multiple of a fixed test function of integral one, and take the primitive `φ = ∫_a^x ψ` of the
corrected function, which is again a test function (`TestFunction.primitive`). Then
`u - φ = ∫_a^x (u' - ψ)` and Poincaré's inequality `SobolevInterval.norm_le_of_eq_integral`
bounds `‖u - φ‖_{H^1}` by a multiple of `‖u' - ψ‖_{L²}`. No cut-off or mollification of `u`
itself is needed. -/
theorem SobolevIntervalZero.mem_of_rep_eq_zero (hab : a < b) (u : SobolevInterval 1 a b)
    (ha : rep u a = 0) (hb : rep u b = 0) : u ∈ SobolevIntervalZero a b := by
  have hrep : ∀ x, rep u x = ∫ t in a..x, deriv u 1 t := fun x ↦ by
    have h := ha
    rw [rep_apply, intervalIntegral.integral_same, add_zero] at h
    rw [rep_apply, h, zero_add]
  have hwint : ∫ x in Ioo a b, deriv u 1 x = 0 := by
    have := rep_sub_rep hab.le u (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le)
    rw [ha, hb, sub_zero, intervalIntegral.integral_of_le hab.le,
      integral_Ioc_eq_integral_Ioo] at this
    exact this.symm
  have hwi : ∀ x ∈ Icc a b, IntervalIntegrable (deriv u 1) volume a x := fun x hx ↦
    (integrableOn_deriv u 1).intervalIntegrable_of_Ioo (left_mem_Icc.2 hab.le) hx
  obtain ⟨ψ₀, hψ₀⟩ := exists_testFunction_integral_eq_one hab
  set N := ‖ψ₀.toLp₂‖ with hN
  set CP := (b - a) / Real.sqrt 2 with hCP
  have hCP0 : 0 ≤ CP := by positivity
  set M := Real.sqrt (1 + CP ^ 2) * (1 + Real.sqrt (b - a) * N) with hM
  have hM0 : 0 < M := by positivity
  rw [← SetLike.mem_coe, SobolevIntervalZero, SobolevMultiIndexZero,
    Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  intro ε hε
  set η := ε / (2 * M) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ψ, hψ⟩ := exists_testFunction_norm_sub_toLp_le hab (deriv u 1) hη0
  -- correct the mean of `ψ`
  set m := ∫ x, ψ x with hm
  obtain ⟨ψ', hψ'c, hmean⟩ : ∃ ψ' : 𝓓(Opens.Ioo a b, ℝ),
      ((ψ' : ℝ → ℝ) = fun x ↦ ψ x - m * ψ₀ x) ∧ ∫ x, ψ' x = 0 := by
    refine ⟨ψ - m • ψ₀, ?_, ?_⟩
    · funext x; simp [smul_eq_mul]
    · simp only [FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_sub ψ.integrable_volume (ψ₀.integrable_volume.const_mul m), integral_const_mul,
        hψ₀]
      simp [hm]
  obtain ⟨φ, hφc⟩ : ∃ φ : 𝓓(Opens.Ioo a b, ℝ), (φ : ℝ → ℝ) = fun x ↦ ∫ t in a..x, ψ' t :=
    ⟨TestFunction.primitive hab ψ' hmean, rfl⟩
  have hφ' : HasWeakDerivOn φ ψ' a b := by
    have := hasWeakDerivOn_integral hab.le ψ'.integrable_volume.integrableOn 0
    refine this.congr_ae (Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun _ ↦ rfl)
    rw [hφc]; simp
  -- the element of `H^1(a, b)` carried by `φ`
  obtain ⟨v, hv0, hv1⟩ : ∃ v : SobolevInterval 1 a b, deriv v 0 = φ.toLp₂ ∧
      deriv v 1 = ψ'.toLp₂ := by
    have hloc : LocallyIntegrableOn (φ.toLp₂ : ℝ → ℝ) (Ioo a b) :=
      (Lp.memLp φ.toLp₂).locallyIntegrableOn (Ω := Opens.Ioo a b) one_le_two
    have h0 : HasWeakIteratedDerivOn 0 φ.toLp₂ φ.toLp₂ a b :=
      HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _ hloc
    have h1 : HasWeakIteratedDerivOn 1 φ.toLp₂ ψ'.toLp₂ a b :=
      hφ'.congr_ae φ.coeFn_toLp₂.symm ψ'.coeFn_toLp₂.symm
    have hv : ∀ j : Fin 2, HasWeakIteratedDerivOn (j : ℕ) (![φ.toLp₂, ψ'.toLp₂] 0)
        (![φ.toLp₂, ψ'.toLp₂] j) a b := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
    exact ⟨mk _ hv, rfl, rfl⟩
  refine ⟨v, ⟨φ, ?_⟩, ?_⟩
  · have e : (deriv v 0 : ℝ → ℝ) = SobolevMultiIndex.fn v := rfl
    rw [← e, hv0]
    exact φ.coeFn_toLp₂
  -- the bound on the derivative
  have hψ'Lp : ψ'.toLp₂ = ψ.toLp₂ - m • ψ₀.toLp₂ := by
    refine Lp.ext (ψ'.coeFn_toLp₂.trans ?_)
    filter_upwards [Lp.coeFn_sub ψ.toLp₂ (m • ψ₀.toLp₂), Lp.coeFn_smul m ψ₀.toLp₂,
      ψ.coeFn_toLp₂, ψ₀.coeFn_toLp₂] with x hx1 hx2 hx3 hx4
    rw [hx1, Pi.sub_apply, hx2, Pi.smul_apply, hx3, hx4, hψ'c, smul_eq_mul]
  have hm' : |m| ≤ Real.sqrt (b - a) * η := by
    have e1 : m = ∫ x in Ioo a b, ψ x :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ψ.eq_zero_of_notMem hx).symm
    have e2 : ∫ x in Ioo a b, (deriv u 1 - ψ.toLp₂) x
        = ∫ x in Ioo a b, (deriv u 1 x - ψ x) := by
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (deriv u 1) ψ.toLp₂, ψ.coeFn_toLp₂] with x hx1 hx2
      rw [hx1, Pi.sub_apply, hx2]
    have := abs_setIntegral_le_sqrt_mul_norm (deriv u 1 - ψ.toLp₂) measurableSet_Ioo subset_rfl
    rw [e2, integral_sub (integrableOn_deriv u 1) ψ.integrable_volume.integrableOn, hwint,
      zero_sub, abs_neg, Real.volume_real_Ioo_of_le hab.le, ← e1] at this
    exact this.trans (by gcongr)
  have hD : ‖deriv u 1 - ψ'.toLp₂‖ ≤ η * (1 + Real.sqrt (b - a) * N) := by
    rw [hψ'Lp, show deriv u 1 - (ψ.toLp₂ - m • ψ₀.toLp₂)
      = (deriv u 1 - ψ.toLp₂) + m • ψ₀.toLp₂ by abel]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    calc ‖deriv u 1 - ψ.toLp₂‖ + |m| * N ≤ η + Real.sqrt (b - a) * η * N := by
          gcongr
      _ = η * (1 + Real.sqrt (b - a) * N) := by ring
  -- the bound on the function, by Poincaré
  have hderiv1 : deriv (u - v) 1 = deriv u 1 - ψ'.toLp₂ := by
    rw [SobolevInterval.deriv_sub, hv1]
  have hderiv0 : (deriv (u - v) 0 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)]
      fun x ↦ ∫ t in a..x, (deriv (u - v) 1) t := by
    rw [hderiv1, SobolevInterval.deriv_sub, hv0]
    filter_upwards [Lp.coeFn_sub (deriv u 0) φ.toLp₂, fn_ae_eq_rep hab u, φ.coeFn_toLp₂,
      ae_restrict_mem measurableSet_Ioo] with x hx1 hx2 hx3 hx4
    rw [hx1, Pi.sub_apply, SobolevInterval.deriv_zero, hx2, hx3, hrep, hφc]
    dsimp only
    rw [← intervalIntegral.integral_sub (hwi x (Ioo_subset_Icc_self hx4))
      (ψ'.continuous.intervalIntegrable _ _)]
    refine intervalIntegral_congr_ae_Ioo ?_ (Ioo_subset_Icc_self hx4)
    exact ((Lp.coeFn_sub (deriv u 1) ψ'.toLp₂).trans (ψ'.coeFn_toLp₂.mono fun t ht ↦ by
      simp only [Pi.sub_apply, ht])).symm
  have h0 : ‖deriv (u - v) 0‖ ≤ CP * ‖deriv (u - v) 1‖ :=
    norm_le_of_eq_integral hab.le hderiv0
  -- assembling
  rw [dist_eq_norm]
  have hsq : ‖u - v‖ ^ 2 ≤ (1 + CP ^ 2) * ‖deriv (u - v) 1‖ ^ 2 := by
    rw [norm_sq_eq, Fin.sum_univ_two]
    have := norm_nonneg (deriv (u - v) 1)
    nlinarith [h0, norm_nonneg (deriv (u - v) 0)]
  have h1 : ‖u - v‖ ≤ Real.sqrt (1 + CP ^ 2) * ‖deriv (u - v) 1‖ := by
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow,
      Real.sq_sqrt (by positivity)]
    exact hsq
  calc ‖u - v‖ ≤ Real.sqrt (1 + CP ^ 2) * ‖deriv (u - v) 1‖ := h1
    _ ≤ Real.sqrt (1 + CP ^ 2) * (η * (1 + Real.sqrt (b - a) * N)) := by
        rw [hderiv1]; gcongr
    _ = M * η := by rw [hM]; ring
    _ = ε / 2 := by
        rw [hη, ← mul_div_assoc, mul_comm M ε, mul_div_mul_right _ _ hM0.ne']
    _ < ε := half_lt_self hε

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

/-! ### Classical derivatives are weak derivatives, and `C^k[a, b] → H^k(a, b)` -/

section Classical

variable {a b : ℝ} {f : ℝ → ℝ}

/-- **A classical derivative is a weak derivative on an interval**, iterated form: for `f` of
class `C^N` on `(a, b)` and `k ≤ N`, the `k`-th derivative `iteratedDeriv k f` is the `k`-th weak
derivative of `f` on `(a, b)`. This is `ContDiffOn.hasWeakIteratedFDerivOn` read in the direction
`1`; on the open interval `iteratedDeriv k f` agrees with `iteratedDerivWithin k f (Ioo a b)`. -/
theorem hasWeakIteratedDerivOn_of_contDiffOn {N : ℕ∞ω} {k : ℕ} (hf : ContDiffOn ℝ N f (Ioo a b))
    (hk : (k : ℕ∞ω) ≤ N) : HasWeakIteratedDerivOn k f (iteratedDeriv k f) a b :=
  (ContDiffOn.hasWeakIteratedFDerivOn (Ω := Opens.Ioo a b) (μ := volume) hf hk).lineDeriv _

/-- **A classical derivative is a weak derivative on an interval**: for `f` of class `C¹` on
`(a, b)`, `deriv f` is the weak derivative of `f` on `(a, b)`. -/
theorem hasWeakDerivOn_of_contDiffOn (hf : ContDiffOn ℝ 1 f (Ioo a b)) :
    HasWeakDerivOn f (deriv f) a b := by
  have := hasWeakIteratedDerivOn_of_contDiffOn (k := 1) hf le_rfl
  rwa [iteratedDeriv_one] at this

/-- An `L²(a, b)` function bounded by `C` has norm at most `√(b - a) C`. -/
theorem MeasureTheory.Lp.norm_le_sqrt_mul_of_ae_bound (hab : a ≤ b)
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᵐ x ∂(volume.restrict (Ioo a b)), |f x| ≤ C) : ‖f‖ ≤ Real.sqrt (b - a) * C := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, norm_sq_eq_integral_sq,
    mul_pow, Real.sq_sqrt (sub_nonneg.2 hab)]
  calc ∫ x in Ioo a b, |f x| ^ 2 ≤ ∫ _ in Ioo a b, C ^ 2 := by
        refine integral_mono_ae ?_ (integrableOn_const (by simp)) ?_
        · have := (Lp.memLp f).integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
          simpa [Real.norm_eq_abs] using this
        · filter_upwards [h] with x hx
          exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    _ = (b - a) * C ^ 2 := by
        rw [setIntegral_const, Real.volume_real_Ioo_of_le hab, smul_eq_mul]

end Classical

namespace ContDiffMapIcc

variable {a b : ℝ} {hab : a ≤ b} {k : ℕ}

/-- The `j`-th derivative of `u ∈ C^k[a, b]`, extended by its endpoint values off `[a, b]`, as an
element of `L²(a, b)`. -/
def derivLp (u : ContDiffMapIcc hab k) (j : Fin (k + 1)) : Lp ℝ 2 (volume.restrict (Ioo a b)) :=
  ((ContinuousMap.IccExtend hab (u.deriv j)).continuous.continuousOn.memLp_two_restrict_Ioo).toLp _

/-- `ContDiffMapIcc.derivLp` is the extended derivative almost everywhere. -/
theorem coeFn_derivLp (u : ContDiffMapIcc hab k) (j : Fin (k + 1)) :
    u.derivLp j =ᵐ[volume.restrict (Ioo a b)] IccExtend hab (u.deriv j) :=
  MemLp.coeFn_toLp _

/-- `ContDiffMapIcc.derivLp` is additive. -/
theorem derivLp_add (u v : ContDiffMapIcc hab k) (j : Fin (k + 1)) :
    (u + v).derivLp j = u.derivLp j + v.derivLp j := by
  refine Lp.ext ((coeFn_derivLp _ _).trans ?_)
  refine ((Lp.coeFn_add _ _).trans ((coeFn_derivLp u j).add (coeFn_derivLp v j))).symm.trans ?_
  exact Eventually.of_forall fun x ↦ rfl

/-- `ContDiffMapIcc.derivLp` is homogeneous. -/
theorem derivLp_smul (c : ℝ) (u : ContDiffMapIcc hab k) (j : Fin (k + 1)) :
    (c • u).derivLp j = c • u.derivLp j := by
  refine Lp.ext ((coeFn_derivLp _ _).trans ?_)
  refine ((Lp.coeFn_smul _ _).trans ((coeFn_derivLp u j).const_smul c)).symm.trans ?_
  exact Eventually.of_forall fun x ↦ rfl

/-- The extended derivatives of `u ∈ C^k[a, b]` are the weak derivatives of `u` on `(a, b)`: on
the open interval the `j`-th entry of the tuple is the `j`-th classical derivative
(`ContDiffMapIcc.deriv_eq_iteratedDerivWithin`), and a classical derivative is a weak one. -/
theorem hasWeakIteratedDerivOn_derivLp (hlt : a < b) (u : ContDiffMapIcc hab k)
    (j : Fin (k + 1)) : HasWeakIteratedDerivOn (j : ℕ) (u.derivLp 0) (u.derivLp j) a b := by
  have hcd : ContDiffOn ℝ k u.extend (Ioo a b) := (u.contDiffOn hlt).mono Ioo_subset_Icc_self
  have h := hasWeakIteratedDerivOn_of_contDiffOn hcd (k := j) (by exact_mod_cast Fin.is_le j)
  refine h.congr_ae ?_ ?_
  · exact (coeFn_derivLp u 0).symm
  · refine EventuallyEq.trans ?_ (coeFn_derivLp u j).symm
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx ↦ ?_)
    have hx' : x ∈ Icc a b := Ioo_subset_Icc_self hx
    have e1 := u.deriv_eq_iteratedDerivWithin hlt j.2 ⟨x, hx'⟩
    have e2 := iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hlt)
      ((hcd.contDiffAt (isOpen_Ioo.mem_nhds hx)).of_le (by exact_mod_cast Fin.is_le j)) hx'
    rw [← e2, ← e1, IccExtend_of_mem hab _ hx']

/-- The inclusion `C^k[a, b] → H^k(a, b)` as a linear map: `u` goes to the element whose `j`-th
component is the extended derivative `u^{(j)}`. -/
def toSobolevIntervalₗ (hab : a ≤ b) (hlt : a < b) (k : ℕ) :
    ContDiffMapIcc hab k →ₗ[ℝ] SobolevInterval k a b where
  toFun u := SobolevInterval.mk u.derivLp (hasWeakIteratedDerivOn_derivLp hlt u)
  map_add' u v := SobolevInterval.ext fun j ↦ by simp only [SobolevInterval.deriv_mk,
    SobolevInterval.deriv_add, derivLp_add]
  map_smul' c u := SobolevInterval.ext fun j ↦ by simp only [SobolevInterval.deriv_mk,
    SobolevInterval.deriv_smul, derivLp_smul, RingHom.id_apply]

/-- The weak derivatives of the inclusion of `u ∈ C^k[a, b]` are its extended derivatives. -/
@[simp]
theorem deriv_toSobolevIntervalₗ (hab : a ≤ b) (hlt : a < b) (u : ContDiffMapIcc hab k)
    (j : Fin (k + 1)) : SobolevInterval.deriv (toSobolevIntervalₗ hab hlt k u) j = u.derivLp j :=
  rfl

/-- `‖u^{(j)}‖_{L²(a, b)} ≤ √(b - a) ‖u^{(j)}‖_∞`. -/
theorem norm_derivLp_le (u : ContDiffMapIcc hab k) (j : Fin (k + 1)) :
    ‖u.derivLp j‖ ≤ Real.sqrt (b - a) * ‖u.deriv j‖ := by
  refine Lp.norm_le_sqrt_mul_of_ae_bound hab _ (norm_nonneg _) ?_
  filter_upwards [coeFn_derivLp u j] with x hx
  rw [hx, ← Real.norm_eq_abs, IccExtend_apply]
  exact ContinuousMap.norm_coe_le_norm _ _

/-- The constant of the inclusion `C^k[a, b] → H^k(a, b)`, for the linear map:
`‖u‖_{H^k} ≤ √(b - a) ‖u‖_{C^k}`. -/
theorem norm_toSobolevIntervalₗ_le (hab : a ≤ b) (hlt : a < b) (u : ContDiffMapIcc hab k) :
    ‖toSobolevIntervalₗ hab hlt k u‖ ≤ Real.sqrt (b - a) * ‖u‖ := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero,
    SobolevInterval.norm_sq_eq, mul_pow, Real.sq_sqrt (sub_nonneg.2 hab), norm_def]
  simp only [deriv_toSobolevIntervalₗ]
  calc ∑ j, ‖u.derivLp j‖ ^ 2 ≤ ∑ j, (Real.sqrt (b - a) * ‖u.deriv j‖) ^ 2 := by
        gcongr with j
        exact norm_derivLp_le u j
    _ = (b - a) * ∑ j, ‖u.deriv j‖ ^ 2 := by
        simp only [mul_pow, Real.sq_sqrt (sub_nonneg.2 hab), Finset.mul_sum]
    _ ≤ (b - a) * (∑ j, ‖u.deriv j‖) ^ 2 := by
        gcongr
        exact Finset.sum_sq_le_sq_sum_of_nonneg fun j _ ↦ norm_nonneg _

/-- **The inclusion `C^k[a, b] → H^k(a, b)`**: the continuous linear map sending
`u ∈ C^k[a, b]` to the element of `H^k(a, b)` whose components are its derivatives
`u, u', …, u^{(k)}`, extended by their endpoint values off `[a, b]`. It is injective
(`ContDiffMapIcc.toSobolevInterval_injective`) and has norm at most `√(b - a)`
(`ContDiffMapIcc.norm_toSobolevInterval_le`). Its completion is what Atkinson and Han,
*Theoretical Numerical Analysis*, 3rd edition, Examples 1.2.28(b) and 2.4.2 call `H^k(a, b)`;
that its range is dense is not proved here. -/
def toSobolevInterval (hab : a ≤ b) (hlt : a < b) (k : ℕ) :
    ContDiffMapIcc hab k →L[ℝ] SobolevInterval k a b :=
  (toSobolevIntervalₗ hab hlt k).mkContinuous _ (norm_toSobolevIntervalₗ_le hab hlt)

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
almost everywhere on `(a, b)` vanishes on `[a, b]`. -/
theorem toSobolevInterval_injective (hab : a ≤ b) (hlt : a < b) (k : ℕ) :
    Function.Injective (toSobolevInterval hab hlt k) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu ↦ ?_
  have h0 : u.derivLp 0 = 0 := by
    rw [← deriv_toSobolevInterval hab hlt u 0, hu, SobolevInterval.deriv_zero_elem]
  have hae : (IccExtend hab (u.deriv 0) : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun _ ↦ 0 :=
    (coeFn_derivLp u 0).symm.trans (by rw [h0]; exact Lp.coeFn_zero _ _ _)
  have heq := eqOn_Icc_of_ae_eq hlt
    (ContinuousMap.IccExtend hab (u.deriv 0)).continuous.continuousOn continuousOn_const hae
  refine coe_injective hlt ?_
  funext t
  have := heq t.2
  simp only [ContinuousMap.coe_IccExtend, IccExtend_of_mem hab _ t.2] at this
  exact this

end ContDiffMapIcc

/-! ### Piecewise `C¹` functions -/

section Piecewise

variable {a b : ℝ}

/-- **The fundamental theorem of calculus for a continuous piecewise-`C¹` function** on a
partition `x 0 = a < x 1 < ⋯ < x (N + 1)`: for every node index `j`, `g' = deriv g` is bounded by
`C` almost everywhere on `(a, x j)` and `g t = g a + ∫_a^t g'` on `[a, x j]`. By induction on
`j`, the step being the fundamental theorem of calculus on one panel, where `g` is continuous up
to the ends and differentiable inside; continuity of `g` at the nodes glues the panels. -/
theorem eq_add_integral_deriv_of_piecewise {N : ℕ} {x : Fin (N + 2) → ℝ} (hx : StrictMono x)
    (hxa : x 0 = a) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a (x (Fin.last (N + 1)))))
    (hg' : ∀ j : Fin (N + 1), ContDiffOn ℝ 1 g (Ioo (x j.castSucc) (x j.succ)))
    {C : ℝ} (hbdd : ∀ j : Fin (N + 1), ∀ t ∈ Ioo (x j.castSucc) (x j.succ), |deriv g t| ≤ C) :
    ∀ j : Fin (N + 2), (∀ᵐ t, t ∈ Ioo a (x j) → |deriv g t| ≤ C) ∧
      ∀ t ∈ Icc a (x j), g t = g a + ∫ s in a..t, deriv g s := by
  have hmono : Monotone x := hx.monotone
  have hxa' : ∀ j, a ≤ x j := fun j ↦ hxa ▸ hmono (Fin.zero_le j)
  have hxb' : ∀ j, x j ≤ x (Fin.last (N + 1)) := fun j ↦ hmono (Fin.le_last j)
  intro j
  induction j using Fin.induction with
  | zero =>
    refine ⟨?_, fun t ht ↦ ?_⟩
    · rw [hxa, Ioo_self]
      exact Eventually.of_forall fun t ht ↦ absurd ht (notMem_empty t)
    · rw [hxa, Icc_self, mem_singleton_iff] at ht
      rw [ht, intervalIntegral.integral_same, add_zero]
  | succ j ih =>
    obtain ⟨ihae, ihfun⟩ := ih
    have hlt : x j.castSucc < x j.succ := hx (Fin.castSucc_lt_succ (i := j))
    -- the bound on the new panel, almost everywhere
    have hae : ∀ᵐ t, t ∈ Ioo a (x j.succ) → |deriv g t| ≤ C := by
      have hne : ∀ᵐ t : ℝ, t ≠ x j.castSucc := by simp [ae_iff, measure_singleton]
      filter_upwards [ihae, hne] with t ht htne htI
      rcases lt_or_gt_of_ne htne with h | h
      · exact ht ⟨htI.1, h⟩
      · exact hbdd j t ⟨h, htI.2⟩
    refine ⟨hae, fun t ht ↦ ?_⟩
    rcases le_or_gt t (x j.castSucc) with htj | htj
    · exact ihfun t ⟨ht.1, htj⟩
    -- integrability of the derivative on `(a, x (j+1))`
    have hint : IntegrableOn (deriv g) (Ioo a (x j.succ)) :=
      Measure.integrableOn_of_bounded (M := C) (by simp) (measurable_deriv g).aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ioo).2 (hae.mono fun t ht htI ↦ by
          rw [Real.norm_eq_abs]; exact ht htI))
    have hint' : ∀ y z, y ∈ Icc a (x j.succ) → z ∈ Icc a (x j.succ) →
        IntervalIntegrable (deriv g) volume y z := fun y z hy hz ↦
      (hint.integrableOn_Icc_of_Ioo.mono_set (uIcc_subset_Icc hy hz)).intervalIntegrable
    -- the fundamental theorem of calculus on `[x j, t]`
    have hftc : ∫ s in (x j.castSucc)..t, deriv g s = g t - g (x j.castSucc) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le htj.le
        (hg.mono (Icc_subset_Icc (hxa' _) (ht.2.trans (hxb' _)))) (fun s hs ↦ ?_)
        (hint' _ _ ⟨hxa' _, hlt.le⟩ ht)
      have hs' : s ∈ Ioo (x j.castSucc) (x j.succ) := ⟨hs.1, hs.2.trans_le ht.2⟩
      exact (((hg' j).differentiableOn one_ne_zero).differentiableAt
        (isOpen_Ioo.mem_nhds hs')).hasDerivAt
    have hj := ihfun (x j.castSucc) ⟨hxa' _, le_rfl⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint' _ _ ⟨le_rfl, hxa' _⟩
      ⟨hxa' _, hlt.le⟩) (hint' _ _ ⟨hxa' _, hlt.le⟩ ht), hftc, ← add_assoc, ← hj]
    ring

/-- **Continuous piecewise-`C¹` functions lie in `H^1(a, b)`**: for a partition
`x 0 = a < x 1 < ⋯ < x (N + 1) = b` and `g` continuous on `[a, b]`, `C¹` on each open panel with
the panel derivatives bounded by a common constant, `g ∈ H^1(a, b)` with weak derivative
`deriv g` (whose values at the nodes are irrelevant). This is what puts the finite element spaces
`X_h^k` of [quarteroni2000numerical] §12.4.5 inside `H^1(0, 1)`; with
`mem_sobolevIntervalZero_of_toContinuousMap_eq_zero` the elements vanishing at the endpoints lie
in `H^1_0(0, 1)`. -/
theorem memSobolevInterval_of_piecewise_contDiffOn {N : ℕ} {x : Fin (N + 2) → ℝ}
    (hx : StrictMono x) (hxa : x 0 = a) (hxb : x (Fin.last (N + 1)) = b) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ j : Fin (N + 1), ContDiffOn ℝ 1 g (Ioo (x j.castSucc) (x j.succ)))
    (hbdd : ∃ C, ∀ j : Fin (N + 1), ∀ t ∈ Ioo (x j.castSucc) (x j.succ), |deriv g t| ≤ C) :
    MemSobolevInterval g 1 a b ∧ HasWeakDerivOn g (deriv g) a b := by
  obtain ⟨C, hC⟩ := hbdd
  have hab : a ≤ b := hxa ▸ hxb ▸ hx.monotone (Fin.zero_le _)
  obtain ⟨hae, hfun⟩ := eq_add_integral_deriv_of_piecewise hx hxa (hxb ▸ hg) hg' hC
    (Fin.last (N + 1))
  rw [hxb] at hae hfun
  have hmem : MemLp (deriv g) 2 (volume.restrict (Ioo a b)) :=
    MemLp.of_bound (measurable_deriv g).aestronglyMeasurable C
      ((ae_restrict_iff' measurableSet_Ioo).2 (hae.mono fun t ht htI ↦ by
        rw [Real.norm_eq_abs]; exact ht htI))
  have hweak : HasWeakDerivOn g (deriv g) a b :=
    (hasWeakDerivOn_integral hab (hmem.integrable one_le_two) (g a)).congr_ae
      ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun t ht ↦
        (hfun t (Ioo_subset_Icc_self ht)).symm)) (Eventually.of_forall fun _ ↦ rfl)
  exact ⟨memSobolevInterval_one_iff.2 ⟨hg.memLp_two_restrict_Ioo, _, hweak, hmem⟩, hweak⟩

end Piecewise
