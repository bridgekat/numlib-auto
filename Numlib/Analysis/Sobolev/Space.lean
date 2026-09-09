/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Domain.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.MeasureTheory.Function.Holder
import Numlib.Analysis.Sobolev.Domain

/-!
# The Sobolev space `W^{k,p}(Ω)` as a Banach space

`Sobolev F k p Ω μ` is the Sobolev space `W^{k,p}(Ω)` of Atkinson and Han, *Theoretical Numerical
Analysis: A Functional Analysis Framework*, 3rd edition, Definition 7.2.2, as a normed space rather
than as a predicate on functions. An element is a tuple `(w_0, …, w_k)` of `L^p(Ω)` functions in
which `w_n` is valued in the continuous `n`-linear maps `E [×n]→L[ℝ] F` and is a weak derivative of
order `n` of `w_0`; the function itself is `w_0`, read through the isometry
`E [×0]→L[ℝ] F ≃ₗᵢ[ℝ] F`. `Numlib/Analysis/Sobolev/Domain.lean` carries the same space as the
predicate `MemSobolev` on functions, and the two are matched here.

## Main definitions

* `SobolevTuple F k p Ω μ`, the ambient space: the `ℓ^p` product of the spaces `L^p(Ω)` of the
  derivative tensors of orders `0` to `k`, with `SobolevTuple.fn` the function a tuple carries;
* `Sobolev F k p Ω μ`, the Sobolev space `W^{k,p}(Ω)`, a submodule of that product, with
  `Sobolev.fn` and `Sobolev.weakDeriv`;
* `SobolevZero F k p Ω μ`, the subspace `W_0^{k,p}(Ω)`, the closure of the test functions in
  `W^{k,p}(Ω)` (Atkinson–Han, Definition 7.2.9);
* `MeasureTheory.MemLp.integralSmulCLM`, integration `u ↦ ∫ g • u` against a fixed function `g` of
  `L^q`, as a continuous linear map on `L^p`, `q` being the conjugate exponent of `p`.

## Main statements

* `Sobolev.isClosed`: `W^{k,p}(Ω)` is closed in the ambient product, because the integration by
  parts formula defining the weak derivative pairs the functions against a fixed test function, and
  that pairing is continuous on `L^p(Ω)` by Hölder's inequality;
* `Sobolev.instCompleteSpace`: **`W^{k,p}(Ω)` is a Banach space**, Atkinson–Han, Theorem 7.2.3;
* `Sobolev.memSobolev` and `MemSobolev.exists_sobolev`: the function underlying an element of
  `W^{k,p}(Ω)` satisfies `MemSobolev`, and every function satisfying `MemSobolev` underlies an
  element, uniquely by `Sobolev.ext_of_fn_ae_eq`; so the type is the space of Definition 7.2.2;
* `Sobolev.norm_eq`: the norm of the type is `sobolevNorm`, the norm of Definition 7.2.2 as
  `Numlib/Analysis/Sobolev/Domain.lean` reads it;
* `TestFunction.memSobolev` and `TestFunction.exists_mem_testFunctions`: every test function on `Ω`
  lies in `W^{k,p}(Ω)`, so `Sobolev.testFunctions` is the image of `C_0^∞(Ω)` there and
  `SobolevZero` is its closure.

## Implementation notes

This file, like `Numlib/Analysis/Sobolev/WeakDeriv.lean` and `Numlib/Analysis/Sobolev/Domain.lean`,
stands in for Mathlib PR 32305 and its continuation `grunweg/SobolevSlobodeckij` (Michael Rothgang,
Filippo Nuccio and Floris van Doorn); the names and the argument order follow that development
where possible, so that a later migration is a rename rather than a rewrite.

### Why a subspace of a product of `L^p` spaces

Three shapes were available for the type. A subtype of `L^p(Ω)` cut out by `MemSobolev` is closest
to the book, but it carries no derivatives, so `MemSobolev` would first have to be shown invariant
under modification on a null set, and then the norm, the normed space structure and completeness
would all have to be built by hand. A structure bundling a function with its weak derivatives is
the same work again over a new type. Carrying the derivatives as *data*, in a `PiLp p` of `Lp`
spaces, buys three of the four from Mathlib: the `ℓ^p` product norm of `PiLp` is exactly the `ℓ^p`
sum over the orders `n ≤ k` of the `L^p(Ω)` norms, which is the norm of Definition 7.2.2 in this
file's indexing (see below), and a closed subspace of a complete space is complete. What is left is
that the weak derivative relation is closed, which is the mathematical content of Theorem 7.2.3 and
is `Sobolev.isClosed`; the analytic ingredient there is `MeasureTheory.MemLp.integralSmulCLM`.

The price is that an element is a tuple and not a function: `Sobolev.fn` reads the function off it,
and `Sobolev.ext_of_fn_ae_eq` is what says the rest of the tuple is determined by it. Being a
`Submodule`, moreover, the type is a subtype, so the projections are written `Sobolev.fn u` rather
than `u.fn`.

### `H^k(Ω)` is not a Hilbert space for *this* norm

Atkinson–Han's Corollary 7.2.4, that `H^k(Ω) = W^{k,2}(Ω)` is a Hilbert space for the inner product
`(u,v)_k = ∫_Ω ∑_{|α| ≤ k} ∂^α u ∂^α v`, is *not* available in this formulation, and the reason is
the indexing rather than the completeness. Here all the derivatives of order `n` are one tensor of
`E [×n]→L[ℝ] F`, measured in its operator norm, where the book measures the derivatives `∂^α v`
with `|α| = n` separately; the two norms are equivalent — mathematically, the derivative tensors of
a Sobolev function being symmetric; the equivalence is not formalized here — but they are not
equal. At `p = 2` that matters: the operator norm on `E [×n]→L[ℝ] F` is not induced by an inner
product once `n ≥ 2` and `E` has dimension at least `2` — for `E = ℝ²` and `F = ℝ` it is the
spectral norm of a `2 × 2` matrix — so for `k ≥ 2` and `dim E ≥ 2` there is no inner product on
`W^{k,2}(Ω)` inducing its norm here. For `k ≤ 1`, or for `dim E ≤ 1`, there is one: every tensor in
sight is then a vector or a linear functional, whose operator norm is Euclidean.

`Numlib/Analysis/Sobolev/MultiIndex.lean` is the formulation that does carry the corollary: it
indexes the derivatives by the multi-indices of a basis, one `L^p(Ω)` function `∂^α v` for each `α`
with `|α| ≤ k`, so that the space is an `ℓ^p` product of `L^p(Ω)` spaces on the nose and, at
`p = 2`, an inner product space with the book's inner product. It repeats the argument of
`Sobolev.isClosed` rather than building on it, because the two ambient products are different
spaces; what it does reuse is `MeasureTheory.MemLp.integralSmulCLM` and the weak derivative theory.
A Hilbert–Schmidt norm on `E [×n]→L[ℝ] F` would be an inner-product norm too, but it is the `ℓ²`
sum over the *tuples* of directions, which weights the multi-index `α` by the multinomial
coefficient `n!/α!`, so it does not give the book's inner product either.
-/

open Filter MeasureTheory Set TopologicalSpace

open scoped Distributions ENNReal Topology

/-! ### Integration against a fixed `L^q` function -/

namespace MeasureTheory

variable {X G : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup G] [NormedSpace ℝ G] {p : ℝ≥0∞} {g : X → ℝ}

/-- Hölder's inequality: if `g` lies in `L^q` for the conjugate exponent `q` of `p` and `u` lies in
`L^p`, then `g • u` is integrable. -/
theorem MemLp.integrable_smul_of_conjExponent [Fact (1 ≤ p)]
    (hg : MemLp g (ENNReal.conjExponent p) μ) {u : X → G} (hu : MemLp u p μ) :
    Integrable (fun x ↦ g x • u x) μ :=
  memLp_one_iff_integrable.1 (hu.smul hg)

/-- Integration against a fixed function `g` of `L^q`, where `q` is the conjugate exponent of `p`,
as a continuous linear map `u ↦ ∫ g • u` on `L^p`. Its continuity is Hölder's inequality. -/
noncomputable def MemLp.integralSmulCLM (G : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] [Fact (1 ≤ p)] (hg : MemLp g (ENNReal.conjExponent p) μ) :
    Lp G p μ →L[ℝ] G :=
  letI : Fact (1 ≤ ENNReal.conjExponent p) := ⟨ENNReal.HolderConjugate.one_le _ p⟩
  (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing μ (ENNReal.conjExponent p) p (hg.toLp g)

/-- `MeasureTheory.MemLp.integralSmulCLM` is the integral it was built from. -/
theorem MemLp.integralSmulCLM_apply [CompleteSpace G] [Fact (1 ≤ p)]
    (hg : MemLp g (ENNReal.conjExponent p) μ) (u : Lp G p μ) :
    hg.integralSmulCLM G u = ∫ x, g x • u x ∂μ := by
  have : Fact (1 ≤ ENNReal.conjExponent p) := ⟨ENNReal.HolderConjugate.one_le _ p⟩
  rw [MemLp.integralSmulCLM, ContinuousLinearMap.lpPairing_eq_integral]
  exact integral_congr_ae (by filter_upwards [hg.coeFn_toLp] with x hx using by simp [hx])

end MeasureTheory

/-! ### Test functions are `p`-integrable -/

/-- A test function on `Ω` is continuous with compact support, hence lies in `L^q` for every
exponent `q` and every measure that is finite on compact sets. -/
protected theorem TestFunction.memLp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Opens E} {N : ℕ∞} (φ : 𝓓^{N}(Ω, F)) (q : ℝ≥0∞) (μ : Measure E)
    [IsFiniteMeasureOnCompacts μ] : MemLp φ q μ :=
  φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport

/-! ### The ambient space -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {k : ℕ} {p : ℝ≥0∞} {Ω : Opens E} {μ : Measure E}

variable (F k p Ω μ) in
/-- The ambient space of `W^{k,p}(Ω)`: tuples `(w_0, …, w_k)` in which `w_n` is an `L^p(Ω)`
function valued in the continuous `n`-linear maps `E [×n]→L[ℝ] F`, carrying the `ℓ^p` sum of the
`L^p(Ω)` norms of the components. `W^{k,p}(Ω)` is the subspace of those tuples for which `w_n` is
a weak derivative of order `n` of `w_0`. -/
abbrev SobolevTuple : Type _ :=
  PiLp p fun n : Fin (k + 1) ↦ Lp (E [×(n : ℕ)]→L[ℝ] F) p (μ.restrict (Ω : Set E))

namespace SobolevTuple

/-- The function underlying a tuple of `SobolevTuple F k p Ω μ`: its component of order `0`, which
is valued in the `0`-linear maps `E [×0]→L[ℝ] F` and is read as a function to `F` by evaluating at
the empty tuple. -/
noncomputable def fn (u : SobolevTuple F k p Ω μ) : E → F := fun x ↦ (u 0 x) 0

/-- The value of the function underlying a tuple. -/
theorem fn_apply (u : SobolevTuple F k p Ω μ) (x : E) : u.fn x = (u 0 x) 0 := rfl

/-- The function underlying a tuple lies in `L^p(Ω)`. -/
theorem memLp_fn [Fact (1 ≤ p)] (u : SobolevTuple F k p Ω μ) :
    MemLp u.fn p (μ.restrict (Ω : Set E)) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 ↦ E) F 0).comp_memLp' (Lp.memLp (u 0))

/-- The function underlying the zero tuple vanishes off a null set of `Ω`. -/
theorem fn_zero : (0 : SobolevTuple F k p Ω μ).fn =ᵐ[μ.restrict (Ω : Set E)] 0 := by
  filter_upwards [Lp.coeFn_zero (E [×(0 : ℕ)]→L[ℝ] F) p (μ.restrict (Ω : Set E))] with x hx
  exact congrArg (fun T : E [×(0 : ℕ)]→L[ℝ] F ↦ T 0) hx

/-- The function underlying a sum of tuples is, off a null set of `Ω`, the sum of the functions. -/
theorem fn_add (u v : SobolevTuple F k p Ω μ) :
    (u + v).fn =ᵐ[μ.restrict (Ω : Set E)] u.fn + v.fn := by
  filter_upwards [Lp.coeFn_add (u 0) (v 0)] with x hx
  exact congrArg (fun T : E [×(0 : ℕ)]→L[ℝ] F ↦ T 0) hx

/-- The function underlying a scalar multiple of a tuple is, off a null set of `Ω`, the multiple of
the function. -/
theorem fn_smul (c : ℝ) (u : SobolevTuple F k p Ω μ) :
    (c • u).fn =ᵐ[μ.restrict (Ω : Set E)] c • u.fn := by
  filter_upwards [Lp.coeFn_smul c (u 0)] with x hx
  exact congrArg (fun T : E [×(0 : ℕ)]→L[ℝ] F ↦ T 0) hx

end SobolevTuple

/-! ### The space `W^{k,p}(Ω)` -/

variable [OpensMeasurableSpace E]

variable (F k p Ω μ) in
/-- **The Sobolev space `W^{k,p}(Ω)`**, as the subspace of `SobolevTuple F k p Ω μ` consisting of
the tuples `(w_0, …, w_k)` in which `w_n` is a weak derivative of order `n` of `w_0` on `Ω`. This
is the space of Atkinson and Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Definition 7.2.2: an element is a function of `L^p(Ω)` together with its
weak derivatives up to order `k`, all in `L^p(Ω)`, and the induced norm is the `ℓ^p` sum of their
`L^p(Ω)` norms. -/
def Sobolev : Submodule ℝ (SobolevTuple F k p Ω μ) where
  carrier := {u | ∀ n : Fin (k + 1), HasWeakIteratedFDerivOn n u.fn (u n) Ω μ}
  zero_mem' _n :=
    HasWeakIteratedFDerivOn.zero.congr_ae SobolevTuple.fn_zero.symm (Lp.coeFn_zero _ _ _).symm
  add_mem' {u v} hu hv n :=
    ((hu n).add (hv n)).congr_ae (SobolevTuple.fn_add u v).symm (Lp.coeFn_add _ _).symm
  smul_mem' c u hu n :=
    ((hu n).const_smul c).congr_ae (SobolevTuple.fn_smul c u).symm (Lp.coeFn_smul _ _).symm

namespace Sobolev

/-- Membership of `W^{k,p}(Ω)` unfolded: a tuple lies in it exactly when each of its components is
a weak derivative of the corresponding order of the function it carries. -/
theorem mem_def {u : SobolevTuple F k p Ω μ} :
    u ∈ Sobolev F k p Ω μ ↔ ∀ n : Fin (k + 1), HasWeakIteratedFDerivOn n u.fn (u n) Ω μ :=
  Iff.rfl

/-- The function underlying an element of `W^{k,p}(Ω)`. Note that an element is a tuple, hence a
term of a `Submodule`, so this is spelt `Sobolev.fn u` rather than `u.fn`. -/
noncomputable def fn (u : Sobolev F k p Ω μ) : E → F :=
  SobolevTuple.fn (u : SobolevTuple F k p Ω μ)

/-- The weak derivative of order `n ≤ k` of an element of `W^{k,p}(Ω)`, as an element of
`L^p(Ω)`. -/
def weakDeriv (u : Sobolev F k p Ω μ) (n : Fin (k + 1)) :
    Lp (E [×(n : ℕ)]→L[ℝ] F) p (μ.restrict (Ω : Set E)) := (u : SobolevTuple F k p Ω μ) n

/-- The component of order `n` of an element of `W^{k,p}(Ω)` is a weak derivative of order `n` of
its underlying function. -/
theorem hasWeakIteratedFDerivOn (u : Sobolev F k p Ω μ) (n : Fin (k + 1)) :
    HasWeakIteratedFDerivOn n (fn u) (weakDeriv u n) Ω μ := u.2 n

/-- The function of the zero element of `W^{k,p}(Ω)` vanishes off a null set of `Ω`. -/
theorem fn_zero : fn (0 : Sobolev F k p Ω μ) =ᵐ[μ.restrict (Ω : Set E)] 0 :=
  SobolevTuple.fn_zero

/-- The function of a sum is, off a null set of `Ω`, the sum of the functions. -/
theorem fn_add (u v : Sobolev F k p Ω μ) :
    fn (u + v) =ᵐ[μ.restrict (Ω : Set E)] fn u + fn v :=
  SobolevTuple.fn_add _ _

/-- The function of a scalar multiple is, off a null set of `Ω`, the multiple of the function. -/
theorem fn_smul (c : ℝ) (u : Sobolev F k p Ω μ) :
    fn (c • u) =ᵐ[μ.restrict (Ω : Set E)] c • fn u :=
  SobolevTuple.fn_smul _ _

variable [Fact (1 ≤ p)]

/-- Membership of `W^{k,p}(Ω)` in terms of the integration by parts formula alone: the local
integrability that the weak derivative relation also asks for is automatic for `L^p(Ω)`
functions. -/
theorem mem_iff [IsLocallyFiniteMeasure μ] {u : SobolevTuple F k p Ω μ} :
    u ∈ Sobolev F k p Ω μ ↔ ∀ (n : Fin (k + 1)) (φ : 𝓓(Ω, ℝ)) (y : Fin n → E),
      ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • u.fn x ∂μ
        = (-1 : ℝ) ^ (n : ℕ) • ∫ x in (Ω : Set E), φ x • (u n x) y ∂μ :=
  ⟨fun h n φ y ↦ (h n).integral_smul_eq φ y, fun h n ↦
    { locallyIntegrableOn := u.memLp_fn.locallyIntegrableOn Fact.out
      locallyIntegrableOn_weakDeriv := (Lp.memLp (u n)).locallyIntegrableOn Fact.out
      integral_smul_eq := h n }⟩

/-- The function underlying an element of `W^{k,p}(Ω)` lies in `L^p(Ω)`. -/
theorem memLp (u : Sobolev F k p Ω μ) : MemLp (fn u) p (μ.restrict (Ω : Set E)) :=
  SobolevTuple.memLp_fn _

/-- The function underlying an element of `W^{k,p}(Ω)` belongs to `W^{k,p}(Ω)` in the sense of
`MemSobolev`, that is, of Atkinson and Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Definition 7.2.2. -/
theorem memSobolev (u : Sobolev F k p Ω μ) : MemSobolev (fn u) k p Ω μ := by
  refine ⟨memLp u, fun n hn ↦ ?_⟩
  have hn' : n < k + 1 := Nat.lt_succ_of_le (by exact_mod_cast hn)
  exact ⟨weakDeriv u ⟨n, hn'⟩, hasWeakIteratedFDerivOn u ⟨n, hn'⟩, Lp.memLp _⟩

/-! ### Completeness -/

section Complete

variable [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ]

variable (F k p Ω μ) in
/-- Pairing the component of order `n` of a tuple against a test function `φ` on `Ω` and a tuple
`y` of `n` directions, `u ↦ ∫_Ω φ (u_n)(y)`, as a continuous linear functional on the ambient space
of `W^{k,p}(Ω)`. Continuity is Hölder's inequality against `φ`, which lies in every `L^q(Ω)`; this
is what makes the weak derivative relation a closed condition. -/
noncomputable def pairingCLM (n : Fin (k + 1)) (φ : 𝓓(Ω, ℝ)) (y : Fin n → E) :
    SobolevTuple F k p Ω μ →L[ℝ] F :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (n : ℕ) ↦ E) F y) ∘L
    ((TestFunction.memLp φ (ENNReal.conjExponent p)
      (μ.restrict (Ω : Set E))).integralSmulCLM (E [×(n : ℕ)]→L[ℝ] F)) ∘L PiLp.proj p _ n

omit [IsLocallyFiniteMeasure μ] in
/-- `Sobolev.pairingCLM` is the integral it was built from. -/
theorem pairingCLM_apply (n : Fin (k + 1)) (φ : 𝓓(Ω, ℝ)) (y : Fin n → E)
    (u : SobolevTuple F k p Ω μ) :
    pairingCLM F k p Ω μ n φ y u = ∫ x in (Ω : Set E), φ x • (u n x) y ∂μ := by
  rw [pairingCLM]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousMultilinearMap.apply_apply, MemLp.integralSmulCLM_apply, PiLp.proj_apply]
  exact ContinuousMultilinearMap.integral_apply
    ((TestFunction.memLp φ _ _).integrable_smul_of_conjExponent (Lp.memLp _)) y

/-- **`W^{k,p}(Ω)` is a closed subspace of the `ℓ^p` product of the `L^p(Ω)` spaces**: an `L^p(Ω)`
limit of weak derivatives is a weak derivative, because the integration by parts formula pairs the
functions against a fixed test function and that pairing is continuous on `L^p(Ω)`. This is the
substance of Atkinson and Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*,
3rd edition, Theorem 7.2.3. -/
theorem isClosed : IsClosed (Sobolev F k p Ω μ : Set (SobolevTuple F k p Ω μ)) := by
  have key : (Sobolev F k p Ω μ : Set (SobolevTuple F k p Ω μ)) =
      ⋂ (n : Fin (k + 1)) (φ : 𝓓(Ω, ℝ)) (y : Fin n → E),
        {u | pairingCLM F k p Ω μ 0 (φ.iteratedFDerivApply n y) 0 u
          = (-1 : ℝ) ^ (n : ℕ) • pairingCLM F k p Ω μ n φ y u} := by
    ext u
    simp only [SetLike.mem_coe, mem_iff, mem_iInter, Set.mem_ofPred_eq, pairingCLM_apply,
      SobolevTuple.fn_apply, TestFunction.iteratedFDerivApply_apply]
  rw [key]
  exact isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦
    isClosed_eq (ContinuousLinearMap.continuous _)
      ((ContinuousLinearMap.continuous _).const_smul _)

/-- **The Sobolev space `W^{k,p}(Ω)` is a Banach space**: Atkinson and Han, *Theoretical Numerical
Analysis: A Functional Analysis Framework*, 3rd edition, Theorem 7.2.3. It is a closed subspace of
an `ℓ^p` product of `L^p(Ω)` spaces, so it inherits their completeness. -/
instance instCompleteSpace : CompleteSpace (Sobolev F k p Ω μ) :=
  Sobolev.isClosed.completeSpace_coe

end Complete

/-! ### Comparison with the predicate `MemSobolev` -/

/-- Every function that lies in `W^{k,p}(Ω)` in the sense of `MemSobolev` is, up to a null set of
`Ω`, the function underlying an element of `Sobolev F k p Ω μ`. Together with `Sobolev.memSobolev`
this identifies the type with the space of Atkinson and Han, *Theoretical Numerical Analysis: A
Functional Analysis Framework*, 3rd edition, Definition 7.2.2. -/
theorem _root_.MemSobolev.exists_sobolev [IsLocallyFiniteMeasure μ] {f : E → F}
    (h : MemSobolev f k p Ω μ) :
    ∃ u : Sobolev F k p Ω μ, fn u =ᵐ[μ.restrict (Ω : Set E)] f := by
  have hL : MemLp (fun x ↦ (continuousMultilinearCurryFin0 ℝ E F).symm (f x)) p
      (μ.restrict (Ω : Set E)) :=
    (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
      |>.comp_memLp' h.memLp
  choose w hw hwp using fun i : Fin k ↦
    h.exists_hasWeakIteratedFDerivOn (n := (i : ℕ) + 1)
      (by exact_mod_cast Nat.succ_le_of_lt i.2)
  set u : SobolevTuple F k p Ω μ :=
    WithLp.toLp p (Fin.cons (hL.toLp _) fun i : Fin k ↦ (hwp i).toLp (w i)) with hu
  have hfn : SobolevTuple.fn u =ᵐ[μ.restrict (Ω : Set E)] f := by
    filter_upwards [hL.coeFn_toLp] with x hx
    exact congrArg (fun T : E [×(0 : ℕ)]→L[ℝ] F ↦ T 0) hx
  refine ⟨⟨u, Fin.cases ?_ fun i ↦ ?_⟩, hfn⟩
  · exact (hasWeakIteratedFDerivOn_zero (h.memLp.locallyIntegrableOn Fact.out)).congr_ae
      hfn.symm hL.coeFn_toLp.symm
  · exact (hw i).congr_ae hfn.symm (hwp i).coeFn_toLp.symm

section Uniqueness

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]

omit [Fact (1 ≤ p)] in
/-- The whole tuple of an element of `W^{k,p}(Ω)` is determined by the function it carries: two
elements whose functions agree off a null set of `Ω` are equal. This is the almost everywhere
uniqueness of the weak derivative, `HasWeakIteratedFDerivOn.ae_eq`. -/
theorem ext_of_fn_ae_eq {u v : Sobolev F k p Ω μ}
    (h : fn u =ᵐ[μ.restrict (Ω : Set E)] fn v) : u = v :=
  Subtype.ext <| PiLp.ext fun n ↦ Lp.ext <|
    (ae_restrict_iff' Ω.isOpen.measurableSet).2
      (((hasWeakIteratedFDerivOn u n).congr_ae h (Filter.EventuallyEq.refl _ _)).ae_eq
        (hasWeakIteratedFDerivOn v n))

/-! ### The norm -/

omit [Fact (1 ≤ p)] in
/-- The `L^p(Ω)` norm of the chosen weak derivative of order `n` of the function of an element of
`W^{k,p}(Ω)` is the `L^p(Ω)` norm of the element's own component of order `n`. -/
theorem eLpNorm_weakIteratedFDeriv (u : Sobolev F k p Ω μ) (n : Fin (k + 1)) :
    eLpNorm (weakIteratedFDeriv n (fn u) Ω μ) p (μ.restrict (Ω : Set E))
      = eLpNorm (weakDeriv u n) p (μ.restrict (Ω : Set E)) :=
  eLpNorm_congr_ae <| (ae_restrict_iff' Ω.isOpen.measurableSet).2
    (hasWeakIteratedFDerivOn u n).weakIteratedFDeriv_ae_eq

/-- **The norm of the type `W^{k,p}(Ω)` is the norm of Atkinson and Han**, *Theoretical Numerical
Analysis: A Functional Analysis Framework*, 3rd edition, Definition 7.2.2, as `sobolevNorm` reads
it: the `ℓ^p` sum, over the orders `n ≤ k`, of the `L^p(Ω)` norms of the weak derivatives. -/
theorem norm_eq (u : Sobolev F k p Ω μ) : ‖u‖ = (sobolevNorm (fn u) k p Ω μ).toReal := by
  have hfin : ∀ n : Fin (k + 1),
      eLpNorm (weakIteratedFDeriv (n : ℕ) (fn u) Ω μ) p (μ.restrict (Ω : Set E)) ≠ ⊤ := by
    intro n
    rw [eLpNorm_weakIteratedFDeriv]
    exact (Lp.memLp (weakDeriv u n)).2.ne
  rw [Submodule.coe_norm, sobolevNorm]
  rcases eq_or_ne p ⊤ with rfl | hp
  · rw [ite_eq_left rfl, PiLp.norm_eq_ciSup, ENNReal.toReal_iSup hfin]
    exact iSup_congr fun n ↦ by rw [Lp.norm_def, eLpNorm_weakIteratedFDeriv]; rfl
  · have hp0 : 0 < p.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
    rw [ite_eq_right hp, PiLp.norm_eq_sum hp0, ← ENNReal.toReal_rpow]
    congr 1
    rw [ENNReal.toReal_sum fun n _ ↦ ENNReal.rpow_ne_top_of_nonneg hp0.le (hfin n)]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [← ENNReal.toReal_rpow, Lp.norm_def, eLpNorm_weakIteratedFDeriv]
    rfl

end Uniqueness

/-! ### The subspace `W_0^{k,p}(Ω)` -/

section Zero

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] [μ.IsAddHaarMeasure]

section

variable {K : ℕ∞}

omit [Fact (1 ≤ p)] [CompleteSpace F] in
/-- **A test function on `Ω` belongs to `W^{k,p}(Ω)`**: it is smooth with compact support in `Ω`,
so its classical derivatives are its weak ones (Atkinson and Han, *Theoretical Numerical Analysis:
A Functional Analysis Framework*, 3rd edition, Lemma 7.1.5), and every one of them is continuous
with compact support, hence in `L^p(Ω)`. -/
theorem _root_.TestFunction.memSobolev (φ : 𝓓(Ω, F)) : MemSobolev (φ : E → F) K p Ω μ := by
  refine ⟨(TestFunction.memLp φ p μ).restrict _, fun n _ ↦
    ⟨iteratedFDeriv ℝ n φ, φ.contDiff.contDiffOn.hasWeakIteratedFDerivOn (by simp), ?_⟩⟩
  exact ((φ.contDiff.continuous_iteratedFDeriv (m := n) (by simp)).memLp_of_hasCompactSupport
    (φ.hasCompactSupport.iteratedFDeriv n)).restrict _

end

variable (F k p Ω μ) in
/-- The image of the test functions `C_0^∞(Ω)` in `W^{k,p}(Ω)`: the elements whose function agrees,
off a null set of `Ω`, with a test function on `Ω`. Every test function does occur, by
`TestFunction.exists_mem_testFunctions`. -/
def testFunctions : Submodule ℝ (Sobolev F k p Ω μ) where
  carrier := {u | ∃ φ : 𝓓(Ω, F), fn u =ᵐ[μ.restrict (Ω : Set E)] φ}
  zero_mem' := ⟨0, fn_zero⟩
  add_mem' := fun {u v} ⟨φ, hφ⟩ ⟨ψ, hψ⟩ ↦ ⟨φ + ψ, (fn_add u v).trans (hφ.add hψ)⟩
  smul_mem' := fun c u ⟨φ, hφ⟩ ↦ ⟨c • φ, (fn_smul c u).trans (hφ.const_smul c)⟩

omit [CompleteSpace F] in
/-- Every test function on `Ω` is the function of an element of `Sobolev.testFunctions`, so that
submodule really is the image of `C_0^∞(Ω)` in `W^{k,p}(Ω)`. -/
theorem _root_.TestFunction.exists_mem_testFunctions (φ : 𝓓(Ω, F)) :
    ∃ u ∈ testFunctions F k p Ω μ, fn u =ᵐ[μ.restrict (Ω : Set E)] φ :=
  let ⟨u, hu⟩ := (TestFunction.memSobolev φ).exists_sobolev
  ⟨u, ⟨φ, hu⟩, hu⟩

end Zero

end Sobolev

variable [Fact (1 ≤ p)] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]

variable (F k p Ω μ) in
/-- **The Sobolev space `W_0^{k,p}(Ω)`**, the closure of `C_0^∞(Ω)` in `W^{k,p}(Ω)`: Atkinson and
Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd edition,
Definition 7.2.9. Its elements are informally the functions whose derivatives of order at most
`k - 1` vanish on the boundary of `Ω`, a reading that only the trace theorems make precise. -/
noncomputable def SobolevZero : Submodule ℝ (Sobolev F k p Ω μ) :=
  (Sobolev.testFunctions F k p Ω μ).topologicalClosure
