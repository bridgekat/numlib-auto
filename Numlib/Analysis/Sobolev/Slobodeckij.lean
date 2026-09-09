/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/MultiIndex.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.MultiIndex

/-!
# The Sobolev–Slobodeckij spaces `W^{s,p}(Ω)` of fractional order

`SobolevSlobodeckij F b k σ p Ω μ` is the Sobolev space `W^{s,p}(Ω)` of *real* order `s = k + σ`,
with `k ≥ 0` an integer and `σ ∈ (0,1)`: the functions of the integer-order space `W^{k,p}(Ω)`
whose weak derivatives of top order have finite Sobolev–Slobodeckij (or Gagliardo) seminorm,

`[v]_{σ,p,Ω} = [∑_{|α| = k} ∫_{Ω × Ω} |∂^α v(x) - ∂^α v(y)|^p / ‖x - y‖^{σp + d} dx dy]^{1/p}`,

carrying the norm `‖v‖_{s,p,Ω} = [‖v‖_{k,p,Ω}^p + [v]_{σ,p,Ω}^p]^{1/p}`. Here `d = dim E`. This is
Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*,
3rd edition, Springer, 2009, Definition 7.2.10, and `SobolevSlobodeckijZero` is the space
`W_0^{s,p}(Ω)` of Definition 7.2.11 there, the closure of the test functions in it.

`Numlib/Analysis/Sobolev/MultiIndex.lean` carries the integer-order space `SobolevMultiIndex`
with the norm `‖v‖_{k,p,Ω}`, indexed by multi-indices; this file is its fractional-order extension
and the norm above extends that one, the seminorm being adjoined to it in the `ℓ^p` combination.
Nothing here reduces to that file at `σ = 0`: the seminorm diverges there, and the integer-order
space is a separate object, as it is in the source.

## Implementation notes

Like `Numlib/Analysis/Sobolev/MultiIndex.lean`, this file moves *away* from the API of Mathlib
PR 32305 and its continuation `grunweg/SobolevSlobodeckij` (Michael Rothgang, Filippo Nuccio and
Floris van Doorn) rather than towards it: there the weak derivative is tensor-valued and carries no
basis, whereas the seminorm here is a sum over multi-indices of top order, which is the form the
source displays. Despite the name of that repository, what it carries is the integer-order space;
if a fractional one arrives there, this file is what should be compared with it.

The space is realised as a *submodule of a pair*: an element is a `W^{k,p}(Ω)` family
`(∂^α v)_{|α| ≤ k}` together with a family `(h_α)_{|α| = k}` of `L^p(Ω × Ω)` functions constrained
to be the difference quotients `slobodeckijQuotient` of its top-order members, the two combined in
the `ℓ^p` norm of `WithLp p (· × ·)`. The norm the pair then carries *is* the displayed norm, with
no rewriting: that is the reason for this shape, and `SobolevSlobodeckij.norm_eq_add` together with
`SobolevSlobodeckij.norm_snd_rpow` is the proof. It is the same device by which
`SobolevMultiIndex` is a submodule of a `PiLp p` of `L^p(Ω)` spaces.

Two things this file does *not* prove, both stated without proof in the source above:

* that `W^{s,p}(Ω)` is a Banach space (and reflexive exactly for `p ∈ (1,∞)`, and a Hilbert space
  for `p = 2`). Completeness would need this submodule to be closed in the ambient pair space,
  which is a further argument;
* that `C_0^∞(Ω) ⊆ W^{s,p}(Ω)`. `SobolevSlobodeckij.testFunctions` is therefore the image of
  `C_0^∞(Ω) ∩ W^{s,p}(Ω)`, which is what "`C_0^∞(Ω)` as a subset of `W^{s,p}(Ω)`" means in any
  case, so `SobolevSlobodeckijZero` is the space of Definition 7.2.11 as it stands; but nothing
  here produces a nonzero element of it, and there is no analogue of
  `TestFunction.exists_mem_testFunctions`. The missing statement is true whenever `0 < σ < 1` and
  `1 ≤ p < ∞`, and the route is: a test function `φ` has `|∂^α φ(x) - ∂^α φ(y)| ≤ L ‖x - y‖`, being
  smooth with compact support; so the integrand is at most `L^p ‖x - y‖^{p(1-σ) - d}`; bound that
  by `G(x - y)` with `G` the same power cut off outside a ball containing `Ω - Ω`, integrate by
  Tonelli, use the translation invariance of `μ` on the inner integral to replace
  `∫⁻ y, G (x - y)` by `∫⁻ z, G z`, and note that the latter is finite by
  `MeasureTheory.integrableOn_ball_of_norm_le_rpow`, the exponent `d - p(1-σ)` being `< d`. The
  friction in that route is a Lipschitz constant for `iteratedFDeriv` of a test function.

## Main definitions

* `slobodeckijQuotient σ p w`, the difference quotient
  `(x, y) ↦ (w(x) - w(y)) / ‖x - y‖^{σ + d/p}`, whose membership of `L^p(Ω × Ω)` is the condition
  the space imposes on `w = ∂^α v`;
* `prodRestrict Ω μ`, the measure `μ|_Ω × μ|_Ω` on `Ω × Ω` over which that membership is read;
* `SobolevSlobodeckijTuple F ι k p Ω μ`, the ambient pair space, and
  `SobolevSlobodeckij F b k σ p Ω μ`, the space itself, with `SobolevSlobodeckij.fn`,
  `SobolevSlobodeckij.toSobolevMultiIndex` and `SobolevSlobodeckij.testFunctions`;
* `SobolevSlobodeckijZero F b k σ p Ω μ`, the closure of the test functions in it.

## Main statements

* `slobodeckijQuotient_congr_ae`: the difference quotient only sees the function up to a null set
  of `Ω`, so the condition is well posed on weak derivatives, which are determined only almost
  everywhere;
* `SobolevSlobodeckij.norm_eq_add` and `SobolevSlobodeckij.norm_snd_rpow`: **the norm of the space
  is the displayed norm**, the second identifying the `L^p(Ω × Ω)` norm of the difference quotient
  with the seminorm integral.
-/

open Filter MeasureTheory Module Set TopologicalSpace

open scoped Distributions ENNReal Topology

/-! ### The difference quotient -/

section Quotient

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {σ : ℝ} {p : ℝ≥0∞} {w w' : E → F}

variable (Ω μ) in
/-- The measure `μ|_Ω × μ|_Ω` on `Ω × Ω`, over which the Sobolev–Slobodeckij seminorm of
`SobolevSlobodeckij` is taken. -/
noncomputable abbrev prodRestrict (Ω : Opens E) (μ : Measure E) : Measure (E × E) :=
  (μ.restrict (Ω : Set E)).prod (μ.restrict (Ω : Set E))

/-- The difference quotient `(x, y) ↦ (w(x) - w(y)) / ‖x - y‖^{σ + d/p}`, with `d = dim E`, whose
membership of `L^p(Ω × Ω)` is what the Sobolev–Slobodeckij space of order `s = k + σ` asks of the
weak derivatives `w = ∂^α v` of top order: Kendall Atkinson and Weimin Han, *Theoretical Numerical
Analysis: A Functional Analysis Framework*, 3rd edition, Springer, 2009, Definition 7.2.10. The
source writes the numerator in absolute value, which is immaterial, membership of `L^p` seeing a
function only through its norm. The `p`-th power of the quotient is the integrand
`|w(x) - w(y)|^p / ‖x - y‖^{σp + d}` of the norm displayed there. -/
noncomputable def slobodeckijQuotient (σ : ℝ) (p : ℝ≥0∞) (w : E → F) : E × E → F :=
  fun z ↦ (‖z.1 - z.2‖ ^ (σ + finrank ℝ E / p.toReal))⁻¹ • (w z.1 - w z.2)

omit [MeasurableSpace E] in
/-- The norm of the difference quotient, as a quotient of norms. -/
theorem norm_slobodeckijQuotient (σ : ℝ) (p : ℝ≥0∞) (w : E → F) (z : E × E) :
    ‖slobodeckijQuotient σ p w z‖ =
      ‖w z.1 - w z.2‖ / ‖z.1 - z.2‖ ^ (σ + finrank ℝ E / p.toReal) := by
  simp only [slobodeckijQuotient, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  rw [← div_eq_inv_mul]

omit [MeasurableSpace E] in
/-- The difference quotient is additive in the function. -/
theorem slobodeckijQuotient_add :
    slobodeckijQuotient σ p (w + w') = slobodeckijQuotient σ p w + slobodeckijQuotient σ p w' := by
  funext z
  simp only [slobodeckijQuotient, Pi.add_apply, smul_sub, smul_add]
  abel

omit [MeasurableSpace E] in
/-- The difference quotient is homogeneous in the function. -/
theorem slobodeckijQuotient_smul (c : ℝ) :
    slobodeckijQuotient σ p (c • w) = c • slobodeckijQuotient σ p w := by
  funext z
  simp only [slobodeckijQuotient, Pi.smul_apply]
  module

/-- The difference quotient only sees the function up to a null set of `Ω`: functions agreeing
almost everywhere on `Ω` have difference quotients agreeing almost everywhere on `Ω × Ω`, both
projections of the product measure being quasi measure preserving. This is what makes the condition
of `SobolevSlobodeckij` a condition on the weak derivatives `∂^α v`, which are themselves
determined only almost everywhere. -/
theorem slobodeckijQuotient_congr_ae {Ω : Opens E} {μ : Measure E} [SFinite μ]
    (h : w =ᵐ[μ.restrict (Ω : Set E)] w') :
    slobodeckijQuotient σ p w =ᵐ[prodRestrict Ω μ] slobodeckijQuotient σ p w' := by
  have h1 := h.comp_tendsto (Measure.quasiMeasurePreserving_fst
    (μ := μ.restrict (Ω : Set E)) (ν := μ.restrict (Ω : Set E))).tendsto_ae
  have h2 := h.comp_tendsto (Measure.quasiMeasurePreserving_snd
    (μ := μ.restrict (Ω : Set E)) (ν := μ.restrict (Ω : Set E))).tendsto_ae
  filter_upwards [h1, h2] with z hz1 hz2
  simp only [slobodeckijQuotient, Function.comp_apply] at *
  rw [hz1, hz2]

end Quotient

/-! ### The space `W^{s,p}(Ω)` -/

section Space

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι] [LinearOrder ι]
  {b : Basis ι ℝ E} {k : ℕ} {σ : ℝ} {p : ℝ≥0∞} {Ω : Opens E} {μ : Measure E}

variable (F ι k p Ω μ) in
/-- The ambient space of `W^{s,p}(Ω)` for `s = k + σ`: a `W^{k,p}(Ω)` family `(∂^α v)_{|α| ≤ k}`
paired with a family of `L^p(Ω × Ω)` functions indexed by the multi-indices of order exactly `k`,
the two combined in the `ℓ^p` norm. `SobolevSlobodeckij` is the subspace in which the second family
consists of the difference quotients of the top-order members of the first, and the norm the pair
then carries is the one displayed in Kendall Atkinson and Weimin Han, *Theoretical Numerical
Analysis: A Functional Analysis Framework*, 3rd edition, Springer, 2009, Definition 7.2.10. -/
abbrev SobolevSlobodeckijTuple : Type _ :=
  WithLp p (SobolevMultiIndexTuple F ι k p Ω μ ×
    PiLp p fun _ : MultiIndexEq ι k ↦ Lp F p (prodRestrict Ω μ))

variable [OpensMeasurableSpace E] [SFinite μ]

variable (F b k σ p Ω μ) in
/-- **The Sobolev–Slobodeckij space `W^{s,p}(Ω)` of real order `s = k + σ`**, as a subspace of
`SobolevSlobodeckijTuple F ι k p Ω μ`: the pairs `((∂^α v)_{|α| ≤ k}, (h_α)_{|α| = k})` in which
the first family lies in `W^{k,p}(Ω)` and `h_α` is, off a null set of `Ω × Ω`, the difference
quotient `(∂^α v(x) - ∂^α v(y)) / ‖x - y‖^{σ + d/p}` of its top-order member.

This is Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009, Definition 7.2.10, whose `σ` lies in `(0,1)`; that
restriction is what makes this the source's space rather than what makes it well formed, and it is
not imposed. The norm carried as a subspace of an `ℓ^p` combination is the norm displayed there, by
`SobolevSlobodeckij.norm_eq_add` and `SobolevSlobodeckij.norm_snd_rpow`. -/
def SobolevSlobodeckij (k : ℕ) (σ : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (Ω : Opens E) (μ : Measure E)
    [SFinite μ] : Submodule ℝ (SobolevSlobodeckijTuple F ι k p Ω μ) where
  carrier := {U | U.fst ∈ SobolevMultiIndex F b k p Ω μ ∧
    ∀ α : MultiIndexEq ι k,
      U.snd α =ᵐ[prodRestrict Ω μ] slobodeckijQuotient σ p (U.fst α.1)}
  zero_mem' := by
    refine ⟨Submodule.zero_mem _, fun α ↦ ?_⟩
    have h1 : slobodeckijQuotient σ p ((0 : SobolevSlobodeckijTuple F ι k p Ω μ).fst α.1 : E → F)
        =ᵐ[prodRestrict Ω μ] 0 := by
      refine (slobodeckijQuotient_congr_ae (Ω := Ω) (Lp.coeFn_zero F p _)).trans ?_
      filter_upwards with z
      simp [slobodeckijQuotient]
    exact (Lp.coeFn_zero F p _).trans h1.symm
  add_mem' := by
    rintro U V ⟨hU1, hU2⟩ ⟨hV1, hV2⟩
    refine ⟨Submodule.add_mem _ hU1 hV1, fun α ↦ ?_⟩
    refine (Lp.coeFn_add _ _).trans ((hU2 α).add (hV2 α)) |>.trans ?_
    exact ((slobodeckijQuotient_congr_ae (Ω := Ω) (Lp.coeFn_add (U.fst α.1) (V.fst α.1))).trans
      (by rw [slobodeckijQuotient_add])).symm
  smul_mem' := by
    rintro c U ⟨hU1, hU2⟩
    refine ⟨Submodule.smul_mem _ c hU1, fun α ↦ ?_⟩
    refine (Lp.coeFn_smul _ _).trans ((hU2 α).const_smul c) |>.trans ?_
    exact ((slobodeckijQuotient_congr_ae (Ω := Ω) (Lp.coeFn_smul c (U.fst α.1))).trans
      (by rw [slobodeckijQuotient_smul])).symm

namespace SobolevSlobodeckij

variable [Fact (1 ≤ p)]

/-- The `W^{k,p}(Ω)` part of an element of `W^{s,p}(Ω)`, as an element of the integer-order space
of `Numlib/Analysis/Sobolev/MultiIndex.lean`. -/
def toSobolevMultiIndex (U : SobolevSlobodeckij F b k σ p Ω μ) : SobolevMultiIndex F b k p Ω μ :=
  ⟨(U : SobolevSlobodeckijTuple F ι k p Ω μ).fst, U.2.1⟩

/-- The function underlying an element of `W^{s,p}(Ω)`. An element is a pair of families, hence a
term of a `Submodule`, so this is spelt `SobolevSlobodeckij.fn U` rather than `U.fn`. -/
noncomputable def fn (U : SobolevSlobodeckij F b k σ p Ω μ) : E → F :=
  SobolevMultiIndexTuple.fn (U : SobolevSlobodeckijTuple F ι k p Ω μ).fst

/-- The function of an element of `W^{s,p}(Ω)` is the function of its `W^{k,p}(Ω)` part. -/
theorem fn_toSobolevMultiIndex (U : SobolevSlobodeckij F b k σ p Ω μ) :
    SobolevMultiIndex.fn (toSobolevMultiIndex U) = fn U := rfl

/-- The second family of an element of `W^{s,p}(Ω)` consists of the difference quotients of its
weak derivatives of top order. -/
theorem snd_ae (U : SobolevSlobodeckij F b k σ p Ω μ) (α : MultiIndexEq ι k) :
    ((U : SobolevSlobodeckijTuple F ι k p Ω μ).snd α : E × E → F) =ᵐ[prodRestrict Ω μ]
      slobodeckijQuotient σ p ((U : SobolevSlobodeckijTuple F ι k p Ω μ).fst α.1) := U.2.2 α

/-- The function of the zero element of `W^{s,p}(Ω)` vanishes off a null set of `Ω`. -/
theorem fn_zero : fn (0 : SobolevSlobodeckij F b k σ p Ω μ) =ᵐ[μ.restrict (Ω : Set E)] 0 :=
  SobolevMultiIndexTuple.fn_zero

/-- The function of a sum is, off a null set of `Ω`, the sum of the functions. -/
theorem fn_add (U V : SobolevSlobodeckij F b k σ p Ω μ) :
    fn (U + V) =ᵐ[μ.restrict (Ω : Set E)] fn U + fn V :=
  SobolevMultiIndexTuple.fn_add _ _

/-- The function of a scalar multiple is, off a null set of `Ω`, the multiple of the function. -/
theorem fn_smul (c : ℝ) (U : SobolevSlobodeckij F b k σ p Ω μ) :
    fn (c • U) =ᵐ[μ.restrict (Ω : Set E)] c • fn U :=
  SobolevMultiIndexTuple.fn_smul _ _

private theorem toReal_pos (hp : p ≠ ⊤) : 0 < p.toReal :=
  ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp

/-- The norm of `W^{s,p}(Ω)` as the `ℓ^p` combination of the `L^p(Ω)` norms of the `∂^α v` with
`|α| ≤ k` and the `L^p(Ω × Ω)` norms of the difference quotients of those with `|α| = k`. The first
sum is `‖v‖_{k,p,Ω}^p`, by `SobolevMultiIndex.norm_eq_sum`, and the second the `p`-th power of the
Sobolev–Slobodeckij seminorm, by `SobolevSlobodeckij.norm_snd_rpow`; together they are the norm
displayed in Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, Definition 7.2.10. -/
theorem norm_eq_add (hp : p ≠ ⊤) (U : SobolevSlobodeckij F b k σ p Ω μ) :
    ‖U‖ = ((∑ α : MultiIndexLE ι k,
          ‖(U : SobolevSlobodeckijTuple F ι k p Ω μ).fst α‖ ^ p.toReal)
        + ∑ α : MultiIndexEq ι k,
          ‖(U : SobolevSlobodeckijTuple F ι k p Ω μ).snd α‖ ^ p.toReal) ^ (1 / p.toReal) := by
  have htp := toReal_pos (p := p) hp
  rw [Submodule.coe_norm, WithLp.prod_norm_eq_add htp, PiLp.norm_eq_sum htp,
    PiLp.norm_eq_sum htp, one_div, Real.rpow_inv_rpow (by positivity) htp.ne',
    Real.rpow_inv_rpow (by positivity) htp.ne']

/-- **The Sobolev–Slobodeckij seminorm**: the `p`-th power of the `L^p(Ω × Ω)` norm of the
difference quotient at `α` is the integral
`∫_{Ω × Ω} ‖∂^α v(x) - ∂^α v(y)‖^p / ‖x - y‖^{σp + d} dx dy` displayed in Kendall Atkinson and
Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd edition,
Springer, 2009, Definition 7.2.10. -/
theorem norm_snd_rpow (hp : p ≠ ⊤) (U : SobolevSlobodeckij F b k σ p Ω μ) (α : MultiIndexEq ι k) :
    ‖(U : SobolevSlobodeckijTuple F ι k p Ω μ).snd α‖ ^ p.toReal =
      ∫ z, ‖((U : SobolevSlobodeckijTuple F ι k p Ω μ).fst α.1 : E → F) z.1
            - ((U : SobolevSlobodeckijTuple F ι k p Ω μ).fst α.1 : E → F) z.2‖ ^ p.toReal
          / ‖z.1 - z.2‖ ^ (σ * p.toReal + finrank ℝ E) ∂(prodRestrict Ω μ) := by
  have htp := toReal_pos (p := p) hp
  have h0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  rw [Lp.norm_def, (Lp.memLp _).eLpNorm_eq_integral_rpow_norm h0 hp,
    ENNReal.toReal_ofReal (by positivity), Real.rpow_inv_rpow (by positivity) htp.ne']
  refine integral_congr_ae ?_
  filter_upwards [snd_ae U α] with z hz
  rw [hz, norm_slobodeckijQuotient,
    Real.div_rpow (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg _)]
  congr 2
  field_simp

variable (F b k σ p Ω μ) in
/-- The image of the test functions `C_0^∞(Ω)` in `W^{s,p}(Ω)`: the elements whose function agrees,
off a null set of `Ω`, with a test function on `Ω`.

Unlike its counterpart `Sobolev.testFunctions` for integer order, this is not accompanied by a
proof that every test function occurs; see the implementation notes of this file for what that
statement is and how it would be proved. This submodule is therefore the image of
`C_0^∞(Ω) ∩ W^{s,p}(Ω)`, which is what "`C_0^∞(Ω)` as a subset of `W^{s,p}(Ω)`" means in any
case. -/
def testFunctions : Submodule ℝ (SobolevSlobodeckij F b k σ p Ω μ) where
  carrier := {U | ∃ φ : 𝓓(Ω, F), fn U =ᵐ[μ.restrict (Ω : Set E)] φ}
  zero_mem' := ⟨0, fn_zero⟩
  add_mem' := fun {U V} ⟨φ, hφ⟩ ⟨ψ, hψ⟩ ↦ ⟨φ + ψ, (fn_add U V).trans (hφ.add hψ)⟩
  smul_mem' := fun c U ⟨φ, hφ⟩ ↦ ⟨c • φ, (fn_smul c U).trans (hφ.const_smul c)⟩

end SobolevSlobodeckij

variable (F b k σ p Ω μ) in
/-- **The Sobolev–Slobodeckij space `W_0^{s,p}(Ω)`**, the closure of `C_0^∞(Ω)` in `W^{s,p}(Ω)`:
Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*,
3rd edition, Springer, 2009, Definition 7.2.11. The closure is taken in the norm of `W^{s,p}(Ω)`,
which for a genuinely real order is strictly stronger than the norm of `W^{k,p}(Ω)`; that is the
point of the definition, `C_0^∞(Ω)` being dense in neither space in general. What the closure is
taken of is `SobolevSlobodeckij.testFunctions`; see the implementation notes of this file. -/
noncomputable def SobolevSlobodeckijZero [Fact (1 ≤ p)] :
    Submodule ℝ (SobolevSlobodeckij F b k σ p Ω μ) :=
  (SobolevSlobodeckij.testFunctions F b k σ p Ω μ).topologicalClosure

end Space
