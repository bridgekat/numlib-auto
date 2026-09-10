/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside Mathlib's Bessel potential spaces.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.Sobolev
import Numlib.Analysis.Sobolev.MultiIndex

/-!
# Weak derivatives and tempered distributions on the whole space

There are two ways to differentiate a locally integrable function on `ℝ^d` in the sense of
distributions, and they use different classes of test functions. Atkinson and Han, *Theoretical
Numerical Analysis: A Functional Analysis Framework*, 3rd edition, Springer, 2009
[han2009theoretical], Definition 7.1.3 tests against `C_0^∞`, the compactly supported smooth
functions, which is `HasWeakIteratedLineDerivOn` of `Numlib/Analysis/Sobolev/WeakDeriv.lean` and
makes sense on any open set. Mathlib's `TemperedDistribution` tests against the Schwartz class,
which needs the whole space but supports the Fourier transform. This file shows that on the whole
space the two agree for `L^p` functions, and draws the consequence that the Sobolev space of
integer order `k` cut out by the weak derivatives is Mathlib's Bessel potential space `H^k`.

## Main statements

* `MeasureTheory.Lp.iteratedLineDerivOp_eq_iff_hasWeakIteratedLineDerivOn`: **the bridge.** For
  `L^p` functions `u` and `v` on `E`, the distributional derivative `∂^{m} u` of the tempered
  distribution attached to `u` is `v` exactly when `v` is a weak derivative of `u` along the tuple
  `m` of directions in the sense of integration by parts against `C_0^∞(E)`.
  One direction is free, a test function being a Schwartz function; the other,
  `HasWeakIteratedLineDerivOn.integral_smul_eq_schwartz`, multiplies a Schwartz function `g` by the
  cut-offs `χ(·/(N+1))` — so that `χ(·/(N+1)) g` is a test function — and passes to the limit by
  dominated convergence. The derivatives of the cut-offs are bounded uniformly in `N` because
  rescaling by a factor at most `1` does not increase them, and the resulting bound is integrable
  against an `L^p` function because the derivatives of a Schwartz function are bounded and
  integrable, hence lie in every `L^q`.
* `TemperedDistribution.MemSobolev.of_iteratedLineDerivOp`: if every iterated directional
  derivative of a tempered distribution of order at most `k` is an `L²` function, the distribution
  lies in `H^k`. This is the converse of Mathlib's `TemperedDistribution.MemSobolev.lineDerivOp`,
  and rests on the multiplier identity
  `(1 + |ξ|²)^{1/2} = (1 + |ξ|²)^{-1/2} + |ξ|² (1 + |ξ|²)^{-1/2}`, the second summand being, up to
  the constant that Mathlib's convention for the Fourier transform contributes, the symbol of the
  Laplacian: `TemperedDistribution.besselPotential_one_eq`.
* `MemSobolevMultiIndex.memSobolev` and `TemperedDistribution.MemSobolev.memSobolevMultiIndex`:
  **the two descriptions of `H^k(ℝ^d)` agree.** An `L²` function lies in the Sobolev space
  `W^{k,2}(ℝ^d)` of `Numlib/Analysis/Sobolev/MultiIndex.lean`, cut out by the weak derivatives
  `∂^α` of order `|α| ≤ k`, exactly when it lies in Mathlib's Bessel potential space `H^k(ℝ^d)`.
* `memSobolevMultiIndex_ofReal_iff`: a real function lies in `W^{k,p}(Ω)` exactly when its
  complexification does.

## Implementation notes

### Why the derivatives have to be allowed to commute

The two descriptions are indexed differently: `MemSobolevMultiIndex` names a derivative by a
multi-index `α`, which `multiIndexDirections` reads as the list of basis vectors `b i` repeated
`α i` times *in increasing order of `i`*, while the induction that builds `H^k` out of `H^0` peels
one derivative off the front and so produces the basis vectors in an arbitrary order. Matching the
two needs the invariance of `∂_{m_1} ⋯ ∂_{m_n}` under permutations of the directions. That is
proved here from scratch: `SchwartzMap.lineDerivOp_comm` is the symmetry of the second derivative
of a smooth function, `Mathlib`'s `second_derivative_symmetric`, and
`LineDeriv.listLineDerivOp_congr_perm` propagates it along a `List.Perm` — whose `swap`
constructor is exactly a transposition of two adjacent directions. Mathlib has the symmetry of
`iteratedFDeriv` only at order two, or at every order for analytic functions, so the route through
lists is what makes the general order available for Schwartz functions and hence for tempered
distributions.

### Scope

Everything here is on the whole space and for the Lebesgue-like measures that support the Schwartz
theory (`Measure.HasTemperateGrowth`). Nothing is claimed on a proper open subset, where the
Schwartz class is not available and the comparison has no meaning.
-/

open Filter FourierTransform LineDeriv Metric MeasureTheory Set TemperedDistribution
  TopologicalSpace

open scoped ContDiff Distributions ENNReal Laplacian Real SchwartzMap Topology


/-! ### Preliminaries on `L^p` spaces -/

namespace MeasureTheory

variable {α G : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup G]

/-- An integrable function that is also bounded lies in every `L^q` with `1 ≤ q`: the pointwise
bound turns `‖f‖^q` into a constant multiple of `‖f‖`. -/
theorem Integrable.memLp_of_bound {f : α → G} (hf : Integrable f μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) {q : ℝ≥0∞} (hq : 1 ≤ q) : MemLp f q μ := by
  rcases eq_or_ne q ∞ with rfl | hq'
  · exact memLp_top_of_bound hf.1 C hC
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hr : (1 : ℝ) ≤ q.toReal := by
    rw [show (1 : ℝ) = (1 : ℝ≥0∞).toReal by simp]
    exact ENNReal.toReal_mono hq' hq
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hbd : ∀ᵐ x ∂μ, ‖f x‖ ≤ C' := hC.mono fun x hx ↦ hx.trans (le_max_left _ _)
  rw [← integrable_norm_rpow_iff hf.1 hq0 hq']
  have hmeas : AEStronglyMeasurable (fun x ↦ ‖f x‖ ^ q.toReal) μ :=
    (Real.continuous_rpow_const (by linarith)).comp_aestronglyMeasurable hf.1.norm
  refine Integrable.mono (hf.norm.const_mul (C' ^ (q.toReal - 1))) hmeas ?_
  filter_upwards [hbd] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  rcases eq_or_lt_of_le (norm_nonneg (f x)) with h0 | h0
  · rw [← h0, Real.zero_rpow (by linarith), mul_zero]
  · have key : ‖f x‖ ^ (q.toReal - 1) * ‖f x‖ = ‖f x‖ ^ q.toReal := by
      conv_rhs => rw [show q.toReal = q.toReal - 1 + 1 by ring]
      rw [Real.rpow_add h0, Real.rpow_one]
    rw [← key]
    gcongr

end MeasureTheory

/-! ### Commuting line derivatives -/

namespace LineDeriv

variable {V X : Type*} [LineDeriv V X X]

/-- The iterated line derivative along a *list* of directions: `∂_{v₁} ⋯ ∂_{vₙ} x` for
`l = [v₁, …, vₙ]`, the head of the list being the outermost derivative. This is the same operation
as `LineDeriv.iteratedLineDerivOp`, indexed by a list rather than by a tuple, which is what makes
`List.Perm` available as an induction principle. -/
def listLineDerivOp (l : List V) (x : X) : X := l.foldr (fun v y ↦ ∂_{v} y) x

/-- Differentiating along the empty list does nothing. -/
@[simp] theorem listLineDerivOp_nil (x : X) : listLineDerivOp ([] : List V) x = x := rfl

/-- The head of the list is the outermost derivative. -/
@[simp] theorem listLineDerivOp_cons (v : V) (l : List V) (x : X) :
    listLineDerivOp (v :: l) x = ∂_{v} (listLineDerivOp l x) := rfl

/-- Differentiating along a tuple of directions is differentiating along the list of its
entries. -/
theorem iteratedLineDerivOp_eq_listLineDerivOp {n : ℕ} (m : Fin n → V) (x : X) :
    ∂^{m} x = listLineDerivOp (List.ofFn m) x := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedLineDerivOp_succ_left, List.ofFn_succ, listLineDerivOp_cons, ih]; rfl

variable (hcomm : ∀ (a b : V) (x : X), ∂_{a} (∂_{b} x) = ∂_{b} (∂_{a} x))

include hcomm

/-- **Iterated line derivatives along a list only see the list up to a permutation**, as soon as
any two line derivatives commute. The induction is on `List.Perm`, whose `swap` constructor is
exactly the transposition of the two outermost derivatives. -/
theorem listLineDerivOp_congr_perm {l₁ l₂ : List V} (h : l₁.Perm l₂) (x : X) :
    listLineDerivOp l₁ x = listLineDerivOp l₂ x := by
  induction h with
  | nil => rfl
  | cons a _ ih => rw [listLineDerivOp_cons, listLineDerivOp_cons, ih]
  | swap a b l => rw [listLineDerivOp_cons, listLineDerivOp_cons, listLineDerivOp_cons,
      listLineDerivOp_cons, hcomm]
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- **Iterated line derivatives along a tuple only see the tuple up to a permutation**, as soon as
any two line derivatives commute. -/
theorem iteratedLineDerivOp_congr_perm {n₁ n₂ : ℕ} {m₁ : Fin n₁ → V} {m₂ : Fin n₂ → V}
    (h : (List.ofFn m₁).Perm (List.ofFn m₂)) (x : X) : ∂^{m₁} x = ∂^{m₂} x := by
  rw [iteratedLineDerivOp_eq_listLineDerivOp, iteratedLineDerivOp_eq_listLineDerivOp,
    listLineDerivOp_congr_perm hcomm h]

/-- One more line derivative may be taken before or after an iterated one, as soon as any two line
derivatives commute. -/
theorem lineDerivOp_iteratedLineDerivOp {n : ℕ} (m : Fin n → V) (a : V) (x : X) :
    ∂_{a} (∂^{m} x) = ∂^{m} (∂_{a} x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedLineDerivOp_succ_left, iteratedLineDerivOp_succ_left, hcomm, ih]

end LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SchwartzMap

/-- **Line derivatives of a Schwartz function commute**: this is the symmetry of the second
derivative of a smooth function, `second_derivative_symmetric`. -/
theorem lineDerivOp_comm (a b : E) (f : 𝓢(E, F)) : ∂_{a} (∂_{b} f) = ∂_{b} (∂_{a} f) := by
  ext x
  have hd : ∀ y : E, HasFDerivAt (f : E → F) (fderiv ℝ (f : E → F) y) y := fun y ↦ f.hasFDerivAt y
  have hdiff : Differentiable ℝ (fderiv ℝ (f : E → F)) :=
    ((f.smooth ⊤).fderiv_right (m := ∞) le_rfl).differentiable (by simp)
  have hd2 : HasFDerivAt (fderiv ℝ (f : E → F)) (fderiv ℝ (fderiv ℝ (f : E → F)) x) x :=
    (hdiff x).hasFDerivAt
  have e : ∀ u v : E, (∂_{u} (∂_{v} f)) x = fderiv ℝ (fderiv ℝ (f : E → F)) x u v := by
    intro u v
    rw [lineDerivOp_apply_eq_fderiv]
    have h : HasFDerivAt (fun y ↦ fderiv ℝ (f : E → F) y v)
        ((ContinuousLinearMap.apply ℝ F v).comp (fderiv ℝ (fderiv ℝ (f : E → F)) x)) x :=
      (ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp x hd2
    have h2 : ((∂_{v} f : 𝓢(E, F)) : E → F) = fun y ↦ fderiv ℝ (f : E → F) y v := rfl
    rw [h2, h.fderiv]
    rfl
  rw [e, e, second_derivative_symmetric hd hd2 a b]

/-- **The iterated line derivative of a Schwartz function is symmetric in its directions.** Through
`SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv` this says that `iteratedFDeriv ℝ n f x` is a
symmetric multilinear map for `f` a Schwartz function, which Mathlib has only at order two
(`ContDiffAt.isSymmSndFDerivAt`) or for analytic functions. -/
theorem iteratedLineDerivOp_congr_perm {n₁ n₂ : ℕ} {m₁ : Fin n₁ → E} {m₂ : Fin n₂ → E}
    (h : (List.ofFn m₁).Perm (List.ofFn m₂)) (f : 𝓢(E, F)) : ∂^{m₁} f = ∂^{m₂} f :=
  LineDeriv.iteratedLineDerivOp_congr_perm (fun a b x ↦ lineDerivOp_comm a b x) h f

end SchwartzMap

namespace TemperedDistribution

variable [NormedSpace ℂ F]

omit [NormedSpace ℝ F] in
/-- **Line derivatives of a tempered distribution commute**, because they are defined by
precomposition with the line derivatives of the Schwartz functions they are tested against, and
those commute. -/
theorem lineDerivOp_comm (a b : E) (T : 𝓢'(E, F)) : ∂_{a} (∂_{b} T) = ∂_{b} (∂_{a} T) := by
  ext g
  simp only [lineDerivOp_apply_apply, map_neg, neg_neg, SchwartzMap.lineDerivOp_comm]

omit [NormedSpace ℝ F] in
/-- **The iterated line derivative of a tempered distribution is symmetric in its directions.** -/
theorem iteratedLineDerivOp_congr_perm {n₁ n₂ : ℕ} {m₁ : Fin n₁ → E} {m₂ : Fin n₂ → E}
    (h : (List.ofFn m₁).Perm (List.ofFn m₂)) (T : 𝓢'(E, F)) : ∂^{m₁} T = ∂^{m₂} T :=
  LineDeriv.iteratedLineDerivOp_congr_perm (fun a b x ↦ lineDerivOp_comm a b x) h T

omit [NormedSpace ℝ F] in
/-- **Integration by parts for a tempered distribution**: the iterated line derivative of `T`
tested against `g` is `(-1)^n` times `T` tested against the iterated line derivative of `g`. -/
theorem iteratedLineDerivOp_apply {n : ℕ} (m : Fin n → E) (T : 𝓢'(E, F)) (g : 𝓢(E, ℂ)) :
    (∂^{m} T) g = (-1 : ℂ) ^ n • T (∂^{m} g) := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, lineDerivOp_apply_apply, ih,
      LineDeriv.iteratedLineDerivOp_neg, map_neg,
      ← LineDeriv.lineDerivOp_iteratedLineDerivOp
        (fun a b x ↦ SchwartzMap.lineDerivOp_comm a b x),
      ← LineDeriv.iteratedLineDerivOp_succ_left]
    rw [pow_succ]
    module

end TemperedDistribution

/-! ### A family of cut-offs -/

section Cutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A fixed smooth cut-off on `E`: it is `1` on the closed unit ball and vanishes outside the ball
of radius `2`. -/
private noncomputable def bump (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The rescaled cut-offs `x ↦ χ (x / (N + 1))`: they are `1` on the ball of radius `N + 1` and
vanish outside the ball of radius `2 (N + 1)`. -/
private noncomputable def bumpScaled (N : ℕ) (x : E) : ℝ := bump E (((N : ℝ) + 1)⁻¹ • x)

/-- The fixed cut-off as a Schwartz function, used only to name a bound for its derivatives. -/
private noncomputable def bumpSchwartz (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : 𝓢(E, ℝ) :=
  (bump E).hasCompactSupport.toSchwartzMap (bump E).contDiff

/-- The rescaled cut-offs are smooth. -/
private theorem contDiff_bumpScaled (N : ℕ) : ContDiff ℝ ∞ (bumpScaled (E := E) N) :=
  (bump E).contDiff.comp (contDiff_const_smul _)

/-- The rescaled cut-offs have compact support. -/
private theorem hasCompactSupport_bumpScaled (N : ℕ) :
    HasCompactSupport (bumpScaled (E := E) N) := by
  have hne : (((N : ℝ) + 1)⁻¹) ≠ 0 := by positivity
  exact (bump E).hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero _ hne)

/-- The rescaled cut-offs are at most `1`. -/
private theorem bumpScaled_le_one (N : ℕ) (x : E) : bumpScaled N x ≤ 1 := (bump E).le_one
/-- The rescaled cut-offs are nonnegative. -/
private theorem bumpScaled_nonneg (N : ℕ) (x : E) : 0 ≤ bumpScaled N x := (bump E).nonneg

/-- Near any fixed point, all but finitely many of the rescaled cut-offs are identically `1`. -/
private theorem bumpScaled_eventuallyEq_one (x : E) :
    ∀ᶠ N : ℕ in atTop, bumpScaled (E := E) N =ᶠ[𝓝 x] 1 := by
  filter_upwards [Filter.eventually_gt_atTop ⌈‖x‖⌉₊] with N hN
  have hx : ‖(((N : ℝ) + 1)⁻¹ • x)‖ < 1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity),
      inv_mul_lt_one₀ (by positivity)]
    calc ‖x‖ ≤ (⌈‖x‖⌉₊ : ℝ) := Nat.le_ceil _
      _ < (N : ℝ) := by exact_mod_cast hN
      _ < (N : ℝ) + 1 := by linarith
  have hcont : Continuous fun y : E ↦ ‖(((N : ℝ) + 1)⁻¹ • y)‖ := by fun_prop
  filter_upwards [hcont.continuousAt.eventually_lt continuousAt_const hx] with y hy
  simp only [bumpScaled, Pi.one_apply]
  exact (bump E).one_of_mem_closedBall
    (by simpa [mem_closedBall, dist_zero_right, bump] using hy.le)

/-- A bound, uniform in `N`, for the derivatives of the rescaled cut-offs: rescaling by a factor
at most `1` does not increase the norm of a derivative. -/
private theorem norm_iteratedFDeriv_bumpScaled_le (i N : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (bumpScaled (E := E) N) x‖
      ≤ SchwartzMap.seminorm ℝ 0 i (bumpSchwartz E) := by
  set c : ℝ := ((N : ℝ) + 1)⁻¹ with hc
  set L : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E with hL
  have hLnorm : ‖L‖ ≤ 1 := by
    rw [hL, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc c * ‖ContinuousLinearMap.id ℝ E‖ ≤ c * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (by positivity)
      _ ≤ 1 := by
          rw [mul_one, hc, inv_le_one₀ (by positivity)]
          linarith [Nat.cast_nonneg (α := ℝ) N]
  have heq : bumpScaled (E := E) N = (bump E : E → ℝ) ∘ L := rfl
  rw [heq, L.iteratedFDeriv_comp_right ((bump E).contDiff (n := (⊤ : ℕ∞))) x (by simp)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _j : Fin i, ‖L‖ ≤ 1 :=
    (Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ hLnorm)).trans (by simp)
  refine (mul_le_mul (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ (bumpSchwartz E) i (L x))
    hprod (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) (apply_nonneg _ _)).trans_eq (mul_one _)


end Cutoff

/-! ### Pairing Schwartz derivatives with `L^p` functions -/

section Pairing

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] {μ : Measure E} [μ.HasTemperateGrowth]
  {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]

/-- The derivatives of a Schwartz function pair with every `L^p` function: the norm of the `j`-th
derivative of a Schwartz function is bounded and integrable, hence in every `L^q`, and Hölder's
inequality applies. -/
theorem SchwartzMap.integrable_norm_iteratedFDeriv_mul_norm {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (g : 𝓢(E, V)) (j : ℕ) {f : E → F} (hf : MemLp f p μ) :
    Integrable (fun x ↦ ‖iteratedFDeriv ℝ j (g : E → V) x‖ * ‖f x‖) μ := by
  have := ENNReal.HolderConjugate.inv_one_sub_inv' hp.out
  have : Fact (1 ≤ (1 - p⁻¹)⁻¹) := by simp [fact_iff]
  have hint : Integrable (fun x ↦ ‖iteratedFDeriv ℝ j (g : E → V) x‖) μ := by
    simpa using g.integrable_pow_mul_iteratedFDeriv μ 0 j
  have hmem : MemLp (fun x ↦ ‖iteratedFDeriv ℝ j (g : E → V) x‖) (1 - p⁻¹)⁻¹ μ :=
    Integrable.memLp_of_bound hint (C := SchwartzMap.seminorm ℝ 0 j g)
      (Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact g.norm_iteratedFDeriv_le_seminorm ℝ j x)
      (by simp)
  exact hmem.integrable_mul hf.norm

end Pairing

/-! ### Complex test functions -/

section ComplexTest

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [T2Space E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {n : ℕ} {m : Fin n → E} {f w : E → F} {μ : Measure E}


omit [MeasurableSpace E] [T2Space E] in
/-- The `n`-th derivative of `c φ` for a real function `φ` and a complex constant `c`. -/
private theorem iteratedFDeriv_const_mul_ofReal {φ : E → ℝ} (hs : ContDiff ℝ ∞ φ) (c : ℂ)
    (x : E) (y : Fin n → E) :
    iteratedFDeriv ℝ n (fun z ↦ c * ((φ z : ℝ) : ℂ)) x y
      = c * ((iteratedFDeriv ℝ n φ x y : ℝ) : ℂ) := by
  have h1 : (fun z ↦ c * ((φ z : ℝ) : ℂ)) = c • (Complex.ofRealCLM ∘ φ) := by
    funext z; simp [smul_eq_mul]
  have hs' : ContDiff ℝ (n : ℕ∞ω) φ := hs.of_le (by simp)
  have h2 : ContDiffAt ℝ n (Complex.ofRealCLM ∘ φ) x :=
    (Complex.ofRealCLM.contDiff.comp hs').contDiffAt
  rw [h1, iteratedFDeriv_const_smul_apply h2,
    Complex.ofRealCLM.iteratedFDeriv_comp_left hs'.contDiffAt le_rfl]
  simp

omit [OpensMeasurableSpace E] [T2Space E] [CompleteSpace F] in
/-- **Complex test functions in the weak-derivative identity.** If `w` is the weak derivative of
`f` along `m` on the whole space and `φ` is a real test function, the integration by parts formula
holds after multiplying `φ` by a complex constant. -/
private theorem HasWeakIteratedLineDerivOn.integral_smul_eq_const_mul
    (h : HasWeakIteratedLineDerivOn m f w ⊤ μ) {φ : E → ℝ} (hs : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (c : ℂ) :
    ∫ x, iteratedFDeriv ℝ n (fun z ↦ c * ((φ z : ℝ) : ℂ)) x m • f x ∂μ
      = (-1 : ℝ) ^ n • ∫ x, (c * ((φ x : ℝ) : ℂ)) • w x ∂μ := by
  have key : ∫ x, iteratedFDeriv ℝ n φ x m • f x ∂μ
      = (-1 : ℝ) ^ n • ∫ x, φ x • w x ∂μ :=
    h.integral_smul_eq' ⟨φ, hs, hc, by simp⟩
  have e1 : ∀ (r : ℝ) (v : F), ((c * (r : ℂ)) • v) = c • (r • v) := by
    intro r v
    rw [mul_smul, ← Complex.coe_smul r v]
  calc ∫ x, iteratedFDeriv ℝ n (fun z ↦ c * ((φ z : ℝ) : ℂ)) x m • f x ∂μ
      = ∫ x, c • (iteratedFDeriv ℝ n φ x m • f x) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        change iteratedFDeriv ℝ n (fun z ↦ c * ((φ z : ℝ) : ℂ)) x m • f x
          = c • (iteratedFDeriv ℝ n φ x m • f x)
        rw [iteratedFDeriv_const_mul_ofReal hs c x m, e1]
    _ = c • ∫ x, iteratedFDeriv ℝ n (φ : E → ℝ) x m • f x ∂μ := integral_smul _ _
    _ = c • ((-1 : ℝ) ^ n • ∫ x, φ x • w x ∂μ) := by rw [key]
    _ = (-1 : ℝ) ^ n • (c • ∫ x, (φ : E → ℝ) x • w x ∂μ) := smul_comm _ _ _
    _ = (-1 : ℝ) ^ n • ∫ x, (c * ((φ x : ℝ) : ℂ)) • w x ∂μ := by
        rw [← integral_smul]
        exact congrArg _ (integral_congr_ae (Filter.Eventually.of_forall fun x ↦ (e1 _ _).symm))

omit [T2Space E] [CompleteSpace F] in
/-- **The integration by parts formula of the weak derivative, against complex test functions.**
If `w` is a weak derivative of `f` along the tuple `m` of directions on the whole space, the
identity `∫ (∂^m ψ) • f = (-1)^{|m|} ∫ ψ • w` holds for every smooth, compactly supported
complex-valued `ψ`, and not only for the real-valued test functions of the definition: split `ψ`
into its real and imaginary parts. -/
theorem HasWeakIteratedLineDerivOn.integral_smul_eq_complex
    (h : HasWeakIteratedLineDerivOn m f w ⊤ μ) {ψ : E → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) :
    ∫ x, iteratedFDeriv ℝ n ψ x m • f x ∂μ = (-1 : ℝ) ^ n • ∫ x, ψ x • w x ∂μ := by
  set u : E → ℝ := fun z ↦ (ψ z).re with hu
  set v : E → ℝ := fun z ↦ (ψ z).im with hv
  have hsu : ContDiff ℝ ∞ u := Complex.reCLM.contDiff.comp hs
  have hsv : ContDiff ℝ ∞ v := Complex.imCLM.contDiff.comp hs
  have hcu : HasCompactSupport u := hc.comp_left (g := Complex.re) (by simp)
  have hcv : HasCompactSupport v := hc.comp_left (g := Complex.im) (by simp)
  set ψ₁ : E → ℂ := fun z ↦ (1 : ℂ) * ((u z : ℝ) : ℂ) with hψ₁
  set ψ₂ : E → ℂ := fun z ↦ Complex.I * ((v z : ℝ) : ℂ) with hψ₂
  have hsplit : ψ = ψ₁ + ψ₂ := by
    funext z
    simp only [hψ₁, hψ₂, hu, hv, Pi.add_apply, one_mul]
    rw [mul_comm]
    exact (Complex.re_add_im (ψ z)).symm
  have hs₁ : ContDiff ℝ ∞ ψ₁ := by
    simpa [hψ₁] using (Complex.ofRealCLM.contDiff.comp hsu).const_smul (1 : ℂ)
  have hs₂ : ContDiff ℝ ∞ ψ₂ := by
    simpa [hψ₂, smul_eq_mul] using (Complex.ofRealCLM.contDiff.comp hsv).const_smul Complex.I
  -- integrability of the four pieces
  have iF : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Integrable (fun x ↦ iteratedFDeriv ℝ n φ x m • f x) μ := by
    intro φ hsφ hcφ
    have := h.integrable_smul
      ((⟨φ, hsφ, hcφ, by simp⟩ : 𝓓((⊤ : Opens E), ℝ)).iteratedFDerivApply n m)
    simpa [TestFunction.iteratedFDerivApply_apply] using this
  have iW : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Integrable (fun x ↦ φ x • w x) μ := fun φ hsφ hcφ ↦
    h.integrable_smul_weakDeriv ⟨φ, hsφ, hcφ, by simp⟩
  have e1 : ∀ (c : ℂ) (r : ℝ) (y : F), ((c * (r : ℂ)) • y) = c • (r • y) := by
    intro c r y; rw [mul_smul, ← Complex.coe_smul r y]
  have key₁ : ∀ x, iteratedFDeriv ℝ n ψ₁ x m • f x
      = (1 : ℂ) • (iteratedFDeriv ℝ n u x m • f x) := by
    intro x
    simp only [hψ₁]
    rw [iteratedFDeriv_const_mul_ofReal hsu 1 x m, e1]
  have key₂ : ∀ x, iteratedFDeriv ℝ n ψ₂ x m • f x
      = Complex.I • (iteratedFDeriv ℝ n v x m • f x) := by
    intro x
    simp only [hψ₂]
    rw [iteratedFDeriv_const_mul_ofReal hsv Complex.I x m, e1]
  have iF₁ : Integrable (fun x ↦ iteratedFDeriv ℝ n ψ₁ x m • f x) μ :=
    ((iF u hsu hcu).smul (1 : ℂ)).congr (Filter.Eventually.of_forall fun x ↦ (key₁ x).symm)
  have iF₂ : Integrable (fun x ↦ iteratedFDeriv ℝ n ψ₂ x m • f x) μ :=
    ((iF v hsv hcv).smul Complex.I).congr (Filter.Eventually.of_forall fun x ↦ (key₂ x).symm)
  have iW₁ : Integrable (fun x ↦ ψ₁ x • w x) μ :=
    ((iW u hsu hcu).smul (1 : ℂ)).congr (Filter.Eventually.of_forall fun x ↦ by
      simp only [hψ₁, Pi.smul_apply]; exact (e1 1 (u x) (w x)).symm)
  have iW₂ : Integrable (fun x ↦ ψ₂ x • w x) μ :=
    ((iW v hsv hcv).smul Complex.I).congr (Filter.Eventually.of_forall fun x ↦ by
      simp only [hψ₂, Pi.smul_apply]; exact (e1 Complex.I (v x) (w x)).symm)
  have hs₁' : ContDiff ℝ (n : ℕ∞ω) ψ₁ := hs₁.of_le (by simp)
  have hs₂' : ContDiff ℝ (n : ℕ∞ω) ψ₂ := hs₂.of_le (by simp)
  have hadd : ∀ x, iteratedFDeriv ℝ n ψ x m
      = iteratedFDeriv ℝ n ψ₁ x m + iteratedFDeriv ℝ n ψ₂ x m := fun x ↦ by
    rw [hsplit]
    exact congrFun (congrArg _ (iteratedFDeriv_add_apply (i := n)
      hs₁'.contDiffAt hs₂'.contDiffAt)) m
  calc ∫ x, iteratedFDeriv ℝ n ψ x m • f x ∂μ
      = ∫ x, (iteratedFDeriv ℝ n ψ₁ x m • f x + iteratedFDeriv ℝ n ψ₂ x m • f x) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        change iteratedFDeriv ℝ n ψ x m • f x
          = iteratedFDeriv ℝ n ψ₁ x m • f x + iteratedFDeriv ℝ n ψ₂ x m • f x
        rw [hadd x, add_smul]
    _ = (∫ x, iteratedFDeriv ℝ n ψ₁ x m • f x ∂μ) + ∫ x, iteratedFDeriv ℝ n ψ₂ x m • f x ∂μ :=
        integral_add iF₁ iF₂
    _ = ((-1 : ℝ) ^ n • ∫ x, ψ₁ x • w x ∂μ) + (-1 : ℝ) ^ n • ∫ x, ψ₂ x • w x ∂μ := by
        rw [h.integral_smul_eq_const_mul hsu hcu 1, h.integral_smul_eq_const_mul hsv hcv Complex.I]
    _ = (-1 : ℝ) ^ n • ∫ x, ψ x • w x ∂μ := by
        rw [← smul_add, ← integral_add iW₁ iW₂]
        exact congrArg _ (integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
          rw [hsplit]; exact (add_smul _ _ _).symm))

end ComplexTest

/-! ### The truncation argument -/

section Truncation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {μ : Measure E} [μ.HasTemperateGrowth] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {n : ℕ} {m : Fin n → E} {f w : E → F}

set_option maxHeartbeats 1000000 in
-- the proof carries a dominating function through two applications of dominated convergence, and
-- elaborating the bound needs more than the default budget
omit [CompleteSpace F] in
/-- **The integration by parts formula of the weak derivative holds against Schwartz functions.**
If `w` is a weak derivative of `f` along the tuple `m` of directions on the whole space and both
`f` and `w` lie in `L^p`, then `∫ (∂^m g) • f = (-1)^{|m|} ∫ g • w` for every Schwartz function
`g`, and not only for the compactly supported test functions of the definition.

The proof multiplies `g` by the cut-offs `χ(·/(N+1))`, so that `χ(·/(N+1)) g` is a test function,
and passes to the limit by dominated convergence; the derivatives of the cut-offs are bounded
uniformly in `N` because rescaling by a factor at most `1` does not increase them. -/
theorem HasWeakIteratedLineDerivOn.integral_smul_eq_schwartz
    (h : HasWeakIteratedLineDerivOn m f w ⊤ μ) (hf : MemLp f p μ) (hw : MemLp w p μ)
    (g : 𝓢(E, ℂ)) :
    ∫ x, iteratedFDeriv ℝ n (g : E → ℂ) x m • f x ∂μ = (-1 : ℝ) ^ n • ∫ x, g x • w x ∂μ := by
  set A : ℕ → ℝ := fun i ↦ SchwartzMap.seminorm ℝ 0 i (bumpSchwartz E) with hA
  set ψ : ℕ → E → ℂ := fun N x ↦ ((bumpScaled N x : ℝ) : ℂ) • (g x : ℂ) with hψ
  have hcofR : ∀ N, ContDiff ℝ ∞ fun x ↦ ((bumpScaled (E := E) N x : ℝ) : ℂ) := fun N ↦
    Complex.ofRealCLM.contDiff.comp (contDiff_bumpScaled N)
  have hgs : ContDiff ℝ ∞ (g : E → ℂ) := g.smooth'
  have hsψ : ∀ N, ContDiff ℝ ∞ (ψ N) := fun N ↦ (hcofR N).smul hgs
  have hcψ : ∀ N, HasCompactSupport (ψ N) := fun N ↦
    HasCompactSupport.smul_right
      ((hasCompactSupport_bumpScaled (E := E) N).comp_left (g := Complex.ofReal) (by simp))
  have key : ∀ N, ∫ x, iteratedFDeriv ℝ n (ψ N) x m • f x ∂μ
      = (-1 : ℝ) ^ n • ∫ x, ψ N x • w x ∂μ :=
    fun N ↦ h.integral_smul_eq_complex (hsψ N) (hcψ N)
  -- the dominating function
  set Φ : E → ℝ := fun x ↦ ∑ i ∈ Finset.range (n + 1),
      ((∏ j, ‖m j‖) * (n.choose i : ℝ) * A i) * ‖iteratedFDeriv ℝ (n - i) (g : E → ℂ) x‖ with hΦ
  have hbdd : ∀ N x, ‖iteratedFDeriv ℝ n (ψ N) x m • f x‖ ≤ Φ x * ‖f x‖ := by
    intro N x
    rw [norm_smul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have h1 : ‖iteratedFDeriv ℝ n (ψ N) x‖
        ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i *
            ‖iteratedFDeriv ℝ (n - i) (g : E → ℂ) x‖ := by
      refine (norm_iteratedFDeriv_smul_le (hcofR N) hgs x (by simp)).trans ?_
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have : ‖iteratedFDeriv ℝ i (fun y ↦ ((bumpScaled (E := E) N y : ℝ) : ℂ)) x‖ ≤ A i := by
        rw [show (fun y ↦ ((bumpScaled (E := E) N y : ℝ) : ℂ))
            = Complex.ofRealLI ∘ bumpScaled N from rfl,
          Complex.ofRealLI.norm_iteratedFDeriv_comp_left
            ((contDiff_bumpScaled (E := E) N).contDiffAt) (by simp)]
        exact norm_iteratedFDeriv_bumpScaled_le i N x
      gcongr
    calc ‖iteratedFDeriv ℝ n (ψ N) x m‖ ≤ ‖iteratedFDeriv ℝ n (ψ N) x‖ * ∏ j, ‖m j‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i *
            ‖iteratedFDeriv ℝ (n - i) (g : E → ℂ) x‖) * ∏ j, ‖m j‖ := by
          gcongr
      _ = Φ x := by
          rw [hΦ, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hΦint : Integrable (fun x ↦ Φ x * ‖f x‖) μ := by
    rw [hΦ]
    simp only [Finset.sum_mul]
    refine integrable_finsetSum _ fun i _ ↦ ?_
    simpa only [mul_assoc] using
      ((g.integrable_norm_iteratedFDeriv_mul_norm (n - i) hf).const_mul
        ((∏ j, ‖m j‖) * (n.choose i : ℝ) * A i))
  -- measurability of the truncated integrands
  have hmeasL : ∀ N, AEStronglyMeasurable (fun x ↦ iteratedFDeriv ℝ n (ψ N) x m • f x) μ :=
    fun N ↦ (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ E) ℂ m).continuous.comp
      ((hsψ N).continuous_iteratedFDeriv (by simp))).aestronglyMeasurable).smul hf.1
  have hmeasR : ∀ N, AEStronglyMeasurable (fun x ↦ ψ N x • w x) μ :=
    fun N ↦ ((hsψ N).continuous.aestronglyMeasurable).smul hw.1
  -- pointwise convergence: the cut-offs are eventually `1` near each point
  have hone : ∀ x : E, ∀ᶠ N in atTop, ψ N x = (g : E → ℂ) x := by
    intro x
    filter_upwards [bumpScaled_eventuallyEq_one (E := E) x] with N hN
    simp only [hψ, hN.eq_of_nhds, Pi.one_apply, Complex.ofReal_one, one_smul]
  have hlimL : ∀ x : E, ∀ᶠ N in atTop,
      iteratedFDeriv ℝ n (ψ N) x m • f x = iteratedFDeriv ℝ n (g : E → ℂ) x m • f x := by
    intro x
    filter_upwards [bumpScaled_eventuallyEq_one (E := E) x] with N hN
    have hEq : ψ N =ᶠ[𝓝 x] (g : E → ℂ) := by
      filter_upwards [hN] with y hy
      simp only [hψ, hy, Pi.one_apply, Complex.ofReal_one, one_smul]
    rw [(hEq.iteratedFDeriv ℝ n).eq_of_nhds]
  have hL : Tendsto (fun N ↦ ∫ x, iteratedFDeriv ℝ n (ψ N) x m • f x ∂μ) atTop
      (𝓝 (∫ x, iteratedFDeriv ℝ n (g : E → ℂ) x m • f x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x ↦ Φ x * ‖f x‖) hmeasL hΦint
      (fun N ↦ Filter.Eventually.of_forall (hbdd N))
      (Filter.Eventually.of_forall fun x ↦ by
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [hlimL x] with N hN
        exact hN.symm)
  have hRint : Integrable (fun x ↦ ‖(g : E → ℂ) x‖ * ‖w x‖) μ := by
    simpa using g.integrable_norm_iteratedFDeriv_mul_norm 0 hw
  have hR : Tendsto (fun N ↦ ∫ x, ψ N x • w x ∂μ) atTop (𝓝 (∫ x, (g : E → ℂ) x • w x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖(g : E → ℂ) x‖ * ‖w x‖) hmeasR
      hRint (fun N ↦ Filter.Eventually.of_forall fun x ↦ ?_)
      (Filter.Eventually.of_forall fun x ↦ by
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [hone x] with N hN
        rw [hN])
    rw [norm_smul, norm_smul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bumpScaled_nonneg N x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (bumpScaled_le_one N x)
  refine tendsto_nhds_unique hL ?_
  simp only [key]
  exact hR.const_smul ((-1 : ℝ) ^ n)

end Truncation

/-! ### The bridge -/

section Bridge

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {μ : Measure E} [μ.HasTemperateGrowth] [IsLocallyFiniteMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {n : ℕ} {m : Fin n → E}

/-- The two signs `(-1)^n`, one a complex scalar and one a real one, cancel. -/
private theorem neg_one_pow_smul_neg_one_pow_smul {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] (n : ℕ) (y : G) : ((-1 : ℂ) ^ n) • (((-1 : ℝ) ^ n) • y) = y := by
  rw [← Complex.coe_smul, smul_smul]
  push_cast
  rw [← mul_pow]
  norm_num

omit [FiniteDimensional ℝ E] in
/-- **A distributional derivative of an `L^p` function is a weak derivative.** This is the
direction of the bridge that is free: a test function is a Schwartz function. -/
theorem MeasureTheory.Lp.hasWeakIteratedLineDerivOn_of_iteratedLineDerivOp_eq
    {u v : Lp F p μ} (h : ∂^{m} (u : 𝓢'(E, F)) = (v : 𝓢'(E, F))) :
    HasWeakIteratedLineDerivOn m (u : E → F) (v : E → F) ⊤ μ where
  locallyIntegrableOn := ((Lp.memLp u).locallyIntegrable Fact.out).locallyIntegrableOn _
  locallyIntegrableOn_weakDeriv := ((Lp.memLp v).locallyIntegrable Fact.out).locallyIntegrableOn _
  integral_smul_eq φ := by
    have hcs : HasCompactSupport (fun x ↦ ((φ x : ℝ) : ℂ)) :=
      φ.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
    have hsm : ContDiff ℝ ∞ (fun x ↦ ((φ x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp φ.contDiff
    set g : 𝓢(E, ℂ) := hcs.toSchwartzMap hsm with hg
    have hgv : (g : E → ℂ) = fun x ↦ ((φ x : ℝ) : ℂ) := rfl
    have happ := congrArg (fun T : 𝓢'(E, F) ↦ T g) h
    simp only [TemperedDistribution.iteratedLineDerivOp_apply,
      Lp.toTemperedDistribution_apply] at happ
    have hder : ∀ x, (∂^{m} g : 𝓢(E, ℂ)) x = ((iteratedFDeriv ℝ n (φ : E → ℝ) x m : ℝ) : ℂ) := by
      intro x
      rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv, hgv,
        show (fun y ↦ ((φ y : ℝ) : ℂ)) = Complex.ofRealCLM ∘ (φ : E → ℝ) from rfl,
        Complex.ofRealCLM.iteratedFDeriv_comp_left (φ.contDiff.of_le (by simp)).contDiffAt le_rfl]
      simp
    have e1 : ∫ x, (∂^{m} g : 𝓢(E, ℂ)) x • (u : E → F) x ∂μ
        = ∫ x, iteratedFDeriv ℝ n (φ : E → ℝ) x m • (u : E → F) x ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
        change (∂^{m} g : 𝓢(E, ℂ)) x • (u : E → F) x
          = iteratedFDeriv ℝ n (φ : E → ℝ) x m • (u : E → F) x
        rw [hder x, Complex.coe_smul])
    have e2 : ∫ x, (g : E → ℂ) x • (v : E → F) x ∂μ = ∫ x, (φ : E → ℝ) x • (v : E → F) x ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
        change (g : E → ℂ) x • (v : E → F) x = (φ : E → ℝ) x • (v : E → F) x
        rw [hgv, Complex.coe_smul])
    rw [e1] at happ
    rw [e2] at happ
    have hres : ∀ (F' : E → F), ∫ x in ((⊤ : Opens E) : Set E), F' x ∂μ = ∫ x, F' x ∂μ := by
      intro F'
      rw [show ((⊤ : Opens E) : Set E) = Set.univ from rfl, Measure.restrict_univ]
    rw [hres, hres, ← happ, smul_comm, neg_one_pow_smul_neg_one_pow_smul]

omit [IsLocallyFiniteMeasure μ] in
/-- **A weak derivative of an `L^p` function is a distributional derivative.** This is the
truncation direction of the bridge. -/
theorem MeasureTheory.Lp.iteratedLineDerivOp_eq_of_hasWeakIteratedLineDerivOn
    {u v : Lp F p μ} (h : HasWeakIteratedLineDerivOn m (u : E → F) (v : E → F) ⊤ μ) :
    ∂^{m} (u : 𝓢'(E, F)) = (v : 𝓢'(E, F)) := by
  ext g
  rw [TemperedDistribution.iteratedLineDerivOp_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  have hsch := h.integral_smul_eq_schwartz (Lp.memLp u) (Lp.memLp v) g
  have e1 : ∫ x, (∂^{m} g : 𝓢(E, ℂ)) x • (u : E → F) x ∂μ
      = ∫ x, iteratedFDeriv ℝ n (g : E → ℂ) x m • (u : E → F) x ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
      change (∂^{m} g : 𝓢(E, ℂ)) x • (u : E → F) x
        = iteratedFDeriv ℝ n (g : E → ℂ) x m • (u : E → F) x
      rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv])
  rw [e1, hsch, neg_one_pow_smul_neg_one_pow_smul]

/-- **The bridge between the two readings of the derivative on the whole space.** For `L^p`
functions `u` and `v`, the distributional derivative `∂^{m} u` of the tempered distribution
attached to `u`, which is tested against Schwartz functions, equals `v` exactly when `v` is a weak
derivative of `u` along `m` in the sense of integration by parts against `C_0^∞` test functions. -/
theorem MeasureTheory.Lp.iteratedLineDerivOp_eq_iff_hasWeakIteratedLineDerivOn
    (u v : Lp F p μ) (m : Fin n → E) :
    ∂^{m} (u : 𝓢'(E, F)) = (v : 𝓢'(E, F)) ↔
      HasWeakIteratedLineDerivOn m (u : E → F) (v : E → F) ⊤ μ :=
  ⟨fun h ↦ Lp.hasWeakIteratedLineDerivOn_of_iteratedLineDerivOp_eq h,
   fun h ↦ Lp.iteratedLineDerivOp_eq_of_hasWeakIteratedLineDerivOn h⟩

end Bridge


/-! ### Bessel potential spaces of integer order -/

section Bessel

variable {ι E F : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace TemperedDistribution

section normed

variable [NormedSpace ℂ F]

/-- The scalar identity behind the splitting of the Bessel potential of order `1`, namely
`(1 + r) ^ (1 / 2) = (1 + r) ^ (-1 / 2) + r * (1 + r) ^ (-1 / 2)`, which after factoring out
`(1 + r) ^ (-1 / 2)` on the right is `(1 + r) ^ (1 / 2) = (1 + r) ^ (-1 / 2) * (1 + r)`. -/
theorem one_add_rpow_half_eq_add {r : ℝ} (hr : 0 ≤ r) :
    (1 + r) ^ (1 / 2 : ℝ) = (1 + r) ^ (-1 / 2 : ℝ) + r * (1 + r) ^ (-1 / 2 : ℝ) := by
  have hp : (0 : ℝ) < 1 + r := by linarith
  have h : (1 + r) ^ (-1 / 2 : ℝ) + r * (1 + r) ^ (-1 / 2 : ℝ)
      = (1 + r) ^ (1 : ℝ) * (1 + r) ^ (-1 / 2 : ℝ) := by
    rw [Real.rpow_one]; ring
  rw [h, ← Real.rpow_add hp]
  norm_num

/-- The Fourier multiplier operator is additive in its symbol. -/
theorem fourierMultiplierCLM_add {g₁ g₂ : E → ℂ} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢'(E, F)) :
    fourierMultiplierCLM F (g₁ + g₂) f =
      fourierMultiplierCLM F g₁ f + fourierMultiplierCLM F g₂ f := by
  simp [fourierMultiplierCLM_apply, smulLeftCLM_add hg₁ hg₂]

/-- The Bessel potential of order `-1` applied to the Laplacian is the Fourier multiplier with
symbol `-(2 * π) ^ 2 * (‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ (-1 / 2))`.

The factor `-(2 * π) ^ 2` is the one in
`TemperedDistribution.laplacian_eq_fourierMultiplierCLM`; it reflects the convention used in
Mathlib for the Fourier transform, for which the symbol of the Laplacian is
`-(2 * π) ^ 2 * ‖x‖ ^ 2` rather than `-‖x‖ ^ 2`. -/
theorem besselPotential_neg_one_laplacian_eq (f : 𝓢'(E, F)) :
    besselPotential E F (-1) (Δ f) = (-(2 * π) ^ 2 : ℂ) •
      fourierMultiplierCLM F
        (fun x ↦ Complex.ofReal (‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))) f := by
  rw [laplacian_eq_fourierMultiplierCLM, besselPotential,
    ContinuousLinearMap.map_smul_of_tower,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop),
    ← Complex.coe_smul (-(2 * π) ^ 2)]
  push_cast
  congr

/-- The Bessel potential of order `1` splits as the Bessel potential of order `-1` minus
`((2 * π) ^ 2)⁻¹` times the Bessel potential of order `-1` of the Laplacian. The minus sign is
there because the symbol of `Δ` is `-(2 * π) ^ 2 * ‖x‖ ^ 2`, so that subtracting it adds
`‖x‖ ^ 2`.

On the Fourier side this is the identity
`(1 + ‖x‖ ^ 2) ^ (1 / 2) = (1 + ‖x‖ ^ 2) ^ (-1 / 2) + ‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ (-1 / 2)`
of `TemperedDistribution.one_add_rpow_half_eq_add`. -/
theorem besselPotential_one_eq (f : 𝓢'(E, F)) :
    besselPotential E F 1 f =
      besselPotential E F (-1) f - (((2 * π) ^ 2 : ℝ)⁻¹ : ℂ) • besselPotential E F (-1) (Δ f) := by
  have hπ : ((2 * π) ^ 2 : ℝ) ≠ 0 := by positivity
  have h₁ : (fun x : E ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))).HasTemperateGrowth := by
    fun_prop
  have h₂ : (fun x : E ↦
      Complex.ofReal (‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))).HasTemperateGrowth := by
    fun_prop
  have hsym : (fun x : E ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2)))
      = (fun x : E ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)))
        + (fun x : E ↦ Complex.ofReal (‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))) := by
    funext x
    simp only [Pi.add_apply, ← Complex.ofReal_add, Complex.ofReal_inj]
    exact one_add_rpow_half_eq_add (r := ‖x‖ ^ 2) (by positivity)
  rw [besselPotential_neg_one_laplacian_eq, smul_smul,
    show ((((2 * π) ^ 2 : ℝ)⁻¹ : ℂ)) * (-(2 * π) ^ 2 : ℂ) = -1 by
      push_cast; field_simp,
    neg_one_smul, sub_neg_eq_add, besselPotential, besselPotential,
    ← fourierMultiplierCLM_add h₁ h₂, hsym]

variable [CompleteSpace F]

/-- A finite sum of Sobolev functions of order `s` and exponent `p` is again a Sobolev function
of order `s` and exponent `p`. -/
theorem MemSobolev.sum {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {t : Finset ι} {g : ι → 𝓢'(E, F)}
    (h : ∀ i ∈ t, MemSobolev s p (g i)) : MemSobolev s p (∑ i ∈ t, g i) := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (by simp)).add (ih fun i hi ↦ h i (by simp [hi]))

end normed

section inner

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- If all the directional derivatives of `f` along an orthonormal basis lie in `H ^ s`, then
`Δ f` lies in `H ^ {s - 1}`.

This refines `TemperedDistribution.MemSobolev.laplacian`, which concludes only
`Δ f ∈ H ^ {s - 2}` from `f ∈ H ^ s`; here the hypothesis is one derivative stronger. -/
theorem MemSobolev.laplacian_of_lineDerivOp [Fintype ι] (b : OrthonormalBasis ι ℝ E) {s : ℝ}
    {f : 𝓢'(E, F)} (hd : ∀ i, MemSobolev s 2 (∂_{b i} f)) : MemSobolev (s - 1) 2 (Δ f) := by
  rw [laplacian_eq_sum b]
  exact MemSobolev.sum fun i _ ↦ (hd i).lineDerivOp

/-- If `f` lies in `H ^ s` and all its directional derivatives along an orthonormal basis lie in
`H ^ s`, then `f` lies in `H ^ {s + 1}`.

This is the converse of `TemperedDistribution.MemSobolev.lineDerivOp`, and is the inductive step
in the identification of `H ^ k` with the space of tempered distributions whose derivatives of
order at most `k` are square integrable; see W. McLean, *Strongly Elliptic Systems and Boundary
Integral Equations*, Cambridge University Press, 2000, Chapter 3. -/
theorem MemSobolev.of_lineDerivOp [Fintype ι] (b : OrthonormalBasis ι ℝ E) {s : ℝ} {f : 𝓢'(E, F)}
    (hf : MemSobolev s 2 f) (hd : ∀ i, MemSobolev s 2 (∂_{b i} f)) : MemSobolev (s + 1) 2 f := by
  have h₁ : MemSobolev s 2 (besselPotential E F (-1) f) := by
    rw [memSobolev_besselPotential_iff]
    exact hf.mono (by linarith)
  have h₂ : MemSobolev s 2 (besselPotential E F (-1) (Δ f)) := by
    rw [memSobolev_besselPotential_iff, show (-1 : ℝ) + s = s - 1 by ring]
    exact MemSobolev.laplacian_of_lineDerivOp b hd
  have h : MemSobolev s 2 (besselPotential E F 1 f) := by
    rw [besselPotential_one_eq]
    exact h₁.sub (h₂.smul _)
  rwa [memSobolev_besselPotential_iff, add_comm] at h

/-- **The iterated directional derivative lowers the Sobolev order by the number of derivatives**:
if `f` lies in `H ^ s` then `∂_{m_1} ⋯ ∂_{m_n} f` lies in `H ^ {s - n}`. This is
`TemperedDistribution.MemSobolev.lineDerivOp`, iterated. -/
theorem MemSobolev.iteratedLineDerivOp {s : ℝ} {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) :
    ∀ (n : ℕ) (m : Fin n → E), MemSobolev (s - n) 2 (∂^{m} f) := by
  intro n
  induction n with
  | zero => intro m; simpa using hf
  | succ n ih =>
    intro m
    rw [LineDeriv.iteratedLineDerivOp_succ_left,
      show s - ((n + 1 : ℕ) : ℝ) = s - (n : ℝ) - 1 by push_cast; ring]
    exact (ih (Fin.tail m)).lineDerivOp

/-- If every iterated directional derivative of `f` of order at most `k`, taken in arbitrary
directions, can be represented by a square integrable function, then `f` lies in `H ^ k`.

Together with `TemperedDistribution.MemSobolev.lineDerivOp`, which gives the converse, this is
the identification of the Bessel potential space of integer order `k` with the Sobolev space
defined by square integrability of the weak derivatives of order at most `k`; see W. McLean,
*Strongly Elliptic Systems and Boundary Integral Equations*, Cambridge University Press, 2000,
Chapter 3. -/
theorem MemSobolev.of_iteratedLineDerivOp {k : ℕ} {f : 𝓢'(E, F)}
    (h : ∀ n ≤ k, ∀ m : Fin n → E, MemSobolev 0 2 (∂^{m} f)) :
    MemSobolev (k : ℝ) 2 f := by
  induction k generalizing f with
  | zero => simpa using h 0 le_rfl (fun i ↦ i.elim0)
  | succ k ih =>
    set b := stdOrthonormalBasis ℝ E with hb
    have hf : MemSobolev (k : ℝ) 2 f := ih fun n hn m ↦ h n (by omega) m
    have hd : ∀ i, MemSobolev (k : ℝ) 2 (∂_{b i} f) := by
      intro i
      refine ih fun n hn m ↦ ?_
      have hm := h (n + 1) (by omega) (Fin.snoc m (b i))
      rwa [LineDeriv.iteratedLineDerivOp_succ_right, Fin.init_snoc, Fin.snoc_last] at hm
    have hk := MemSobolev.of_lineDerivOp b hf hd
    rwa [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring] at hk

end inner

end TemperedDistribution

end Bessel

/-! ### Lemma 1: incrementing one entry of a multi-index -/

/-- Raising by one the exponent of a single index `i` in a `flatMap` of replicated blocks adds one
more copy of `b i`, up to a permutation: the block of `b i` grows by one entry, and moving that
entry to the front is a permutation. The list `l` of indices is required to be duplicate-free so
that `i` names exactly one block. This is the general statement behind
`multiIndexDirections_add_single_perm`. -/
theorem List.perm_flatMap_replicate_update {ι E : Type*} [DecidableEq ι] (b : ι → E) (α : ι → ℕ)
    (i : ι) (l : List ι) (hi : i ∈ l) (hnd : l.Nodup) :
    (l.flatMap fun j ↦ List.replicate (if j = i then α j + 1 else α j) (b j)).Perm
      (b i :: l.flatMap fun j ↦ List.replicate (α j) (b j)) := by
  induction l with
  | nil => simp at hi
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hat, hndt⟩ := hnd
    by_cases hai : a = i
    · -- The incremented block is the head block, and the two sides are equal.
      have hne : ∀ j ∈ t, ¬ j = i := fun j hj hji ↦ hat (by rw [hai, ← hji]; exact hj)
      have h1 : ∀ j ∈ t, List.replicate (if j = i then α j + 1 else α j) (b j)
          = List.replicate (α j) (b j) := fun j hj ↦ by rw [ite_eq_right (hne j hj)]
      have key : ((a :: t).flatMap fun j ↦ List.replicate (if j = i then α j + 1 else α j) (b j))
          = b i :: ((a :: t).flatMap fun j ↦ List.replicate (α j) (b j)) := by
        rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_congr h1, ite_eq_left hai, hai,
          List.replicate_succ, List.cons_append]
      rw [key]
    · -- The incremented block is inside the tail; `List.perm_middle` moves `b i` to the front.
      have hit : i ∈ t := (List.mem_cons.1 hi).resolve_left fun h ↦ hai h.symm
      rw [List.flatMap_cons, List.flatMap_cons, ite_eq_right hai]
      exact ((ih hit hndt).append_left _).trans List.perm_middle

/-- **Incrementing the `i`-th entry of a multi-index prepends one copy of `b i`**: the list of
directions naming `α + e_i` is a permutation of `b i` followed by the list naming `α`, where
`e_i = Pi.single i 1`. The two lists are not equal: the extra copy of `b i` sits in the block of the
index `i` and not at the head. -/
theorem multiIndexDirections_add_single_perm {ι E : Type*} [Fintype ι] [LinearOrder ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (b : ι → E) (α : ι → ℕ) (i : ι) :
    (multiIndexDirections b (α + Pi.single i 1)).Perm (b i :: multiIndexDirections b α) := by
  have hfun : (fun j ↦ List.replicate ((α + Pi.single i 1 : ι → ℕ) j) (b j))
      = fun j ↦ List.replicate (if j = i then α j + 1 else α j) (b j) := by
    funext j
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [multiIndexDirections, multiIndexDirections, hfun]
  exact List.perm_flatMap_replicate_update b α i _ ((Finset.mem_sort _).2 (Finset.mem_univ i))
    (Finset.sort_nodup _ _)

/-! ### Lemma 2: weak derivatives under a continuous linear map -/

/-- **A continuous linear map passes through the weak derivative**: if `w` is a weak derivative of
`f` along the tuple `y` of directions on `Ω`, then `L ∘ w` is one of `L ∘ f`. Both sides of the
integration by parts formula integrate integrable functions, so `L` commutes with the integrals,
and `L` is `ℝ`-linear, so it commutes with the scalars `∂^n φ x` and `(-1)^n` as well. Completeness
of `F` is what makes `MeasureTheory.integral` on `F` the Bochner integral rather than the junk
value `0`, so without it the hypothesis carries no information; no completeness is needed of `G`,
where the junk value makes the conclusion trivial. -/
theorem HasWeakIteratedLineDerivOn.comp_continuousLinearMap {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : ℕ} {y : Fin n → E} {f w : E → F} {Ω : Opens E} {μ : Measure E}
    (h : HasWeakIteratedLineDerivOn y f w Ω μ) (L : F →L[ℝ] G) :
    HasWeakIteratedLineDerivOn y (fun x ↦ L (f x)) (fun x ↦ L (w x)) Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn.comp_continuousLinearMap L
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.comp_continuousLinearMap L
  integral_smul_eq φ := by
    by_cases hG : CompleteSpace G
    · have i₁ : Integrable (fun x ↦ iteratedFDeriv ℝ n (φ : E → ℝ) x y • f x)
          (μ.restrict (Ω : Set E)) := by
        have h' := (h.integrable_smul (φ.iteratedFDerivApply n y)).integrableOn (s := (Ω : Set E))
        simp only [TestFunction.iteratedFDerivApply_apply] at h'
        exact h'
      have i₂ : Integrable (fun x ↦ (φ : E → ℝ) x • w x) (μ.restrict (Ω : Set E)) :=
        (h.integrable_smul_weakDeriv φ).integrableOn
      calc ∫ x in (Ω : Set E), iteratedFDeriv ℝ n (φ : E → ℝ) x y • L (f x) ∂μ
          = ∫ x in (Ω : Set E), L (iteratedFDeriv ℝ n (φ : E → ℝ) x y • f x) ∂μ := by
            simp only [map_smul]
        _ = L (∫ x in (Ω : Set E), iteratedFDeriv ℝ n (φ : E → ℝ) x y • f x ∂μ) :=
            L.integral_comp_comm i₁
        _ = L ((-1 : ℝ) ^ n • ∫ x in (Ω : Set E), (φ : E → ℝ) x • w x ∂μ) := by
            rw [h.integral_smul_eq φ]
        _ = (-1 : ℝ) ^ n • ∫ x in (Ω : Set E), (φ : E → ℝ) x • L (w x) ∂μ := by
            rw [map_smul, ← L.integral_comp_comm i₂]
            simp only [map_smul]
    · simp only [integral_of_not_completeSpace hG, smul_zero]

/-! ### Lemma 3: the real and the complex form of one weak derivative -/

/-- **A real function has a real weak derivative exactly when its complexification has the
complexified one**: composing with the embedding `ℝ → ℂ` and with the real part, both continuous
`ℝ`-linear maps, takes each statement to the other. -/
theorem HasWeakIteratedLineDerivOn.ofReal_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {n : ℕ} {y : Fin n → E} {f w : E → ℝ}
    {Ω : Opens E} {μ : Measure E} :
    HasWeakIteratedLineDerivOn y f w Ω μ ↔
      HasWeakIteratedLineDerivOn y (fun x ↦ (f x : ℂ)) (fun x ↦ (w x : ℂ)) Ω μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa using h.comp_continuousLinearMap Complex.ofRealCLM
  · simpa using h.comp_continuousLinearMap Complex.reCLM

/-- A real function lies in `L^p` exactly when its complexification does: the embedding `ℝ → ℂ` is
a continuous linear map, and so is the real part, which inverts it on real scalars. -/
theorem MeasureTheory.memLp_ofReal_iff {X : Type*} [MeasurableSpace X] {f : X → ℝ} {p : ℝ≥0∞}
    {μ : Measure X} : MemLp (fun x ↦ ((f x : ℝ) : ℂ)) p μ ↔ MemLp f p μ :=
  ⟨fun h ↦ by simpa [Function.comp_def] using Complex.reCLM.comp_memLp' h, fun h ↦ h.ofReal⟩

/-! ### From multi-index weak derivatives to the Bessel potential space -/

section Transfer

variable {ι E : Type*} [Fintype ι] [LinearOrder ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
/-- The list of directions naming a multi-index is the list of the entries of the tuple naming
it. -/
theorem ofFn_multiIndexTuple (b : ι → E) (α : ι → ℕ) :
    List.ofFn (multiIndexTuple b α) = multiIndexDirections b α := by
  refine List.ext_getElem (by simp [length_multiIndexDirections]) fun i h1 h2 ↦ ?_
  simp [multiIndexTuple]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Every tuple of basis vectors is a permutation of the tuple naming a multi-index.** Counting
how often each index occurs in the tuple gives the multi-index. -/
theorem exists_multiIndex_perm (b : ι → E) {n : ℕ} (m : Fin n → ι) :
    ∃ α : ι → ℕ, ∑ i, α i = n ∧
      (List.ofFn fun j ↦ b (m j)).Perm (multiIndexDirections b α) := by
  induction n with
  | zero => exact ⟨0, by simp, by simp [multiIndexDirections]⟩
  | succ n ih =>
    obtain ⟨α, hα, hperm⟩ := ih (Fin.tail m)
    refine ⟨α + Pi.single (m 0) 1, ?_, ?_⟩
    · simp [Finset.sum_add_distrib, hα]
    · rw [List.ofFn_succ]
      exact (hperm.cons _).trans (multiIndexDirections_add_single_perm b α (m 0)).symm

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

open TemperedDistribution in
omit [LinearOrder ι] in
/-- **A tempered distribution whose iterated directional derivatives along the vectors of an
orthonormal basis, in any order and of order at most `k`, are `L²` functions lies in `H^k`.**
This is the basis-indexed form of `TemperedDistribution.MemSobolev.of_iteratedLineDerivOp`. -/
theorem TemperedDistribution.MemSobolev.of_iteratedLineDerivOp_basis (b : OrthonormalBasis ι ℝ E)
    {k : ℕ} {f : 𝓢'(E, F)}
    (h : ∀ n ≤ k, ∀ m : Fin n → ι, MemSobolev 0 2 (∂^{fun j ↦ b (m j)} f)) :
    MemSobolev (k : ℝ) 2 f := by
  induction k generalizing f with
  | zero => simpa using h 0 le_rfl (fun i ↦ i.elim0)
  | succ k ih =>
    have hf : MemSobolev (k : ℝ) 2 f := ih fun n hn m ↦ h n (by omega) m
    have hd : ∀ i, MemSobolev (k : ℝ) 2 (∂_{b i} f) := by
      intro i
      refine ih fun n hn m ↦ ?_
      set m' : Fin (n + 1) → ι := Fin.snoc m i with hm'
      have hsn : (fun j ↦ b (m' j)) = Fin.snoc (fun j ↦ b (m j)) (b i) := by
        funext j
        refine Fin.lastCases ?_ ?_ j <;> simp [hm']
      have hm := h (n + 1) (by omega) m'
      rw [hsn, LineDeriv.iteratedLineDerivOp_succ_right, Fin.init_snoc, Fin.snoc_last] at hm
      exact hm
    have hk := MemSobolev.of_lineDerivOp b hf hd
    rwa [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring] at hk

end Transfer

/-! ### The two descriptions of `H^k(ℝ^d)` agree -/

section Agree

variable {ι E : Type*} [Fintype ι] [LinearOrder ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

open TemperedDistribution

/-- **An `L²` function whose weak derivatives up to order `k` are `L²` lies in the Bessel
potential space `H^k`.** -/
theorem MemSobolevMultiIndex.memSobolev (b : OrthonormalBasis ι ℝ E) {k : ℕ}
    {u : Lp ℂ 2 (volume : Measure E)}
    (h : MemSobolevMultiIndex b.toBasis (u : E → ℂ) k 2 ⊤ volume) :
    MemSobolev (k : ℝ) 2 (u : 𝓢'(E, ℂ)) := by
  refine MemSobolev.of_iteratedLineDerivOp_basis b fun n hn m ↦ ?_
  obtain ⟨α, hα, hperm⟩ := exists_multiIndex_perm (b : ι → E) m
  obtain ⟨w, hw, hwL⟩ := h.exists_hasWeakIteratedLineDerivOn (α := α) (by omega)
  simp only [OrthonormalBasis.coe_toBasis] at hw
  rw [show ((⊤ : Opens E) : Set E) = Set.univ from rfl, Measure.restrict_univ] at hwL
  have hw' : HasWeakIteratedLineDerivOn (multiIndexTuple (b : ι → E) α) (u : E → ℂ)
      ((hwL.toLp w : Lp ℂ 2 (volume : Measure E)) : E → ℂ) ⊤ volume :=
    hw.congr_ae (Filter.EventuallyEq.refl _ _) (by
      rw [show ((⊤ : Opens E) : Set E) = Set.univ from rfl, Measure.restrict_univ]
      exact hwL.coeFn_toLp.symm)
  have hperm' : (List.ofFn fun j ↦ (b : ι → E) (m j)).Perm
      (List.ofFn (multiIndexTuple (b : ι → E) α)) := by
    rw [ofFn_multiIndexTuple]; exact hperm
  rw [TemperedDistribution.iteratedLineDerivOp_congr_perm hperm',
    MeasureTheory.Lp.iteratedLineDerivOp_eq_of_hasWeakIteratedLineDerivOn hw']
  exact memSobolev_zero_iff.2 ⟨_, rfl⟩

/-- **An `L²` function in the Bessel potential space `H^k` has all its weak derivatives up to
order `k` in `L²`.** -/
theorem TemperedDistribution.MemSobolev.memSobolevMultiIndex (b : OrthonormalBasis ι ℝ E) {k : ℕ}
    {u : Lp ℂ 2 (volume : Measure E)} (h : MemSobolev (k : ℝ) 2 (u : 𝓢'(E, ℂ))) :
    MemSobolevMultiIndex b.toBasis (u : E → ℂ) k 2 ⊤ volume := by
  have huniv : ((⊤ : Opens E) : Set E) = Set.univ := rfl
  refine ⟨by rw [huniv, Measure.restrict_univ]; exact Lp.memLp u, fun α hα ↦ ?_⟩
  have hmem : MemSobolev 0 2 (∂^{multiIndexTuple (b : ι → E) α} (u : 𝓢'(E, ℂ))) := by
    refine (h.iteratedLineDerivOp _ (multiIndexTuple (b : ι → E) α)).mono ?_
    have : ((∑ i, α i : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hα
    linarith
  obtain ⟨wL, hwL⟩ := memSobolev_zero_iff.1 hmem
  refine ⟨(wL : E → ℂ), ?_, by rw [huniv, Measure.restrict_univ]; exact Lp.memLp wL⟩
  simpa only [OrthonormalBasis.coe_toBasis] using
    MeasureTheory.Lp.hasWeakIteratedLineDerivOn_of_iteratedLineDerivOp_eq hwL

/-- **The Sobolev space of integer order on the whole space, cut out by the weak derivatives, is
Mathlib's Bessel potential space.** An `L²` function has all its weak derivatives `∂^α` of order
`|α| ≤ k` in `L²(E)` exactly when it lies in `H^k(E)`. This is the statement Atkinson and Han,
*Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd edition, Springer, 2009,
Theorem 7.4.1 makes when its `H^k(ℝ^d)` is unfolded on both sides; the *norms* are not compared
here. -/
theorem memSobolevMultiIndex_iff_memSobolev (b : OrthonormalBasis ι ℝ E) {k : ℕ}
    {u : Lp ℂ 2 (volume : Measure E)} :
    MemSobolevMultiIndex b.toBasis (u : E → ℂ) k 2 ⊤ volume ↔
      MemSobolev (k : ℝ) 2 (u : 𝓢'(E, ℂ)) :=
  ⟨MemSobolevMultiIndex.memSobolev b, TemperedDistribution.MemSobolev.memSobolevMultiIndex b⟩

end Agree

/-! ### Complexification -/

section Complexify

variable {ι E : Type*} [Fintype ι] [LinearOrder ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]

/-- **A real function lies in `W^{k,p}(Ω)` exactly when its complexification does.** Composing
with the embedding `ℝ → ℂ` and with the real part, both continuous `ℝ`-linear maps, takes each
statement to the other. -/
theorem memSobolevMultiIndex_ofReal_iff {b : Module.Basis ι ℝ E} {f : E → ℝ} {k : ℕ} {p : ℝ≥0∞}
    {Ω : Opens E} {μ : Measure E} :
    MemSobolevMultiIndex b (fun x ↦ ((f x : ℝ) : ℂ)) k p Ω μ ↔
      MemSobolevMultiIndex b f k p Ω μ := by
  constructor
  · rintro ⟨hL, hd⟩
    refine ⟨by simpa [Function.comp_def] using (Complex.reCLM.comp_memLp' hL), fun α hα ↦ ?_⟩
    obtain ⟨w, hw, hwL⟩ := hd α hα
    refine ⟨fun x ↦ (w x).re, ?_,
      by simpa [Function.comp_def] using Complex.reCLM.comp_memLp' hwL⟩
    simpa using hw.comp_continuousLinearMap Complex.reCLM
  · rintro ⟨hL, hd⟩
    refine ⟨hL.ofReal, fun α hα ↦ ?_⟩
    obtain ⟨w, hw, hwL⟩ := hd α hα
    exact ⟨fun x ↦ ((w x : ℝ) : ℂ), hw.comp_continuousLinearMap Complex.ofRealCLM, hwL.ofReal⟩

end Complexify
