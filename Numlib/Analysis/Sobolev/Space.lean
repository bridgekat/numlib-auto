/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
# The Sobolev space $W^{k,p}(\Omega)$ as a Banach space

Let $\Omega$ be an open subset of a real normed space $E$, let $F$ be a real normed space, and let
$\mu$ be a measure on $E$. This module builds the Sobolev space $W^{k,p}(\Omega)$ of Definition
7.2.2 of [han2009theoretical] as a normed space, not as a predicate on functions. An element is a
tuple $(w_0, \dots, w_k)$ of $L^p(\Omega)$ functions in which $w_n$ takes values in the continuous
$n$-linear maps $E^n \to F$ and is a weak derivative of order $n$ of $w_0$. The function itself is
$w_0$, read through the isometry between the $0$-linear maps and $F$. The norm is the $\ell^p$ sum
of the $L^p(\Omega)$ norms of $w_0, \dots, w_k$.

The module proves that $W^{k,p}(\Omega)$ is a Banach space, which is Theorem 7.2.3 of
[han2009theoretical]. It matches the type with the predicate `MemSobolev` of
`Numlib.Analysis.Sobolev.Domain` and the norm with `sobolevNorm`. It also defines the closure
$W_0^{k,p}(\Omega)$ of the test functions, which is Definition 7.2.9 of [han2009theoretical].

## Main definitions

* `SobolevTuple`, with `SobolevTuple.fn`: the ambient space, the $\ell^p$ product of the spaces
  $L^p(\Omega)$ of the derivative tensors of orders $0$ to $k$, and the function that a tuple
  carries.
* `Sobolev`, with `Sobolev.fn` and `Sobolev.weakDeriv`: the Sobolev space $W^{k,p}(\Omega)$, a
  submodule of that product, the function of an element, and its weak derivatives.
* `SobolevZero`: the subspace $W_0^{k,p}(\Omega)$, the closure of the test functions in
  $W^{k,p}(\Omega)$.
* `MeasureTheory.MemLp.integralSmulCLM`: integration $u \mapsto \int g u$ against a fixed function
  $g \in L^{p'}$, as a continuous linear map on $L^p$, where $p'$ is the conjugate exponent of $p$.

## Main results

* `Sobolev.isClosed`: $W^{k,p}(\Omega)$ is closed in the ambient product.
* `Sobolev.instCompleteSpace`: $W^{k,p}(\Omega)$ is a Banach space (Theorem 7.2.3 of
  [han2009theoretical]).
* `Sobolev.memSobolev` and `MemSobolev.exists_sobolev`: the function of an element of
  $W^{k,p}(\Omega)$ satisfies `MemSobolev`, and every function that satisfies `MemSobolev` is the
  function of an element, which is unique by `Sobolev.ext_of_fn_ae_eq`. So the type is the space of
  Definition 7.2.2.
* `Sobolev.norm_eq`: the norm of the type is `sobolevNorm`, the norm of Definition 7.2.2 as
  `Numlib.Analysis.Sobolev.Domain` reads it.
* `TestFunction.memSobolev` and `TestFunction.exists_mem_testFunctions`: every test function on
  $\Omega$ lies in $W^{k,p}(\Omega)$, so `Sobolev.testFunctions` is the image of
  $C_0^\infty(\Omega)$ there and `SobolevZero` is its closure.

## Proof outline

The weak derivative relation is closed because the integration by parts formula pairs the functions
against a fixed test function, and this pairing is continuous on $L^p(\Omega)$ by Hölder's
inequality. A closed subspace of the complete $\ell^p$ product of $L^p(\Omega)$ spaces is complete.

## Implementation notes

* This module, with `Numlib.Analysis.Sobolev.WeakDeriv` and `Numlib.Analysis.Sobolev.Domain`, stands
  in for Mathlib PR 32305 and its continuation `grunweg/SobolevSlobodeckij` (Michael Rothgang,
  Filippo Nuccio and Floris van Doorn). The names and the argument order follow that development
  where possible, so that a later migration is a rename and not a rewrite.
* There were three possible shapes for the type. A subtype of $L^p(\Omega)$ cut out by `MemSobolev`
  is closest to the source, but it carries no derivatives: `MemSobolev` would first have to be shown
  invariant under modification on a null set, and then the norm, the normed space structure and
  completeness would all have to be built by hand. A structure that bundles a function with its weak
  derivatives is the same work again over a new type. Carrying the derivatives as data, in a
  `PiLp p` of `Lp` spaces, gets three of the four from Mathlib. The product norm of `PiLp` is
  exactly the $\ell^p$ sum over the orders $n \le k$ of the $L^p(\Omega)$ norms, which is the
  norm of Definition 7.2.2 in this indexing, and a closed subspace of a complete space is complete.
  What remains is that the weak derivative relation is closed. This is the mathematical content of
  Theorem 7.2.3 and is `Sobolev.isClosed`, whose analytic ingredient is
  `MeasureTheory.MemLp.integralSmulCLM`.
* The price is that an element is a tuple and not a function. `Sobolev.fn` reads the function off
  the tuple, and `Sobolev.ext_of_fn_ae_eq` says that the rest of the tuple is determined by it.
  Because the type is a `Submodule`, it is a subtype, so the projections are written `Sobolev.fn u`
  and not `u.fn`.
* Corollary 7.2.4 of [han2009theoretical], that $H^k(\Omega) = W^{k,2}(\Omega)$ is a Hilbert space
  for the inner product $(u, v)_k = \int_\Omega \sum_{|\alpha| \le k} \partial^\alpha u \,
  \partial^\alpha v$, is not available for this norm. The reason is the indexing, not the
  completeness. Here all the derivatives of order $n$ form one tensor in the continuous $n$-linear
  maps $E^n \to F$, measured in its operator norm, where the source measures the derivatives
  $\partial^\alpha v$ with $|\alpha| = n$ separately. The two norms are equivalent, because the
  derivative tensors of a Sobolev function are symmetric, but they are not equal, and the
  equivalence is not formalized here. At $p = 2$ this matters: the operator norm on the $n$-linear
  maps is not induced by an inner product once $n \ge 2$ and $\dim E \ge 2$ (for $E = \mathbb{R}^2$
  and $F = \mathbb{R}$ it is the spectral norm of a $2 \times 2$ matrix). So for $k \ge 2$ and
  $\dim E \ge 2$ no inner product on $W^{k,2}(\Omega)$ induces its norm here. For $k \le 1$, or for
  $\dim E \le 1$, there is one, because every tensor that occurs is then a vector or a linear
  functional, whose operator norm is Euclidean.
* `Numlib.Analysis.Sobolev.MultiIndex` is the formulation that does carry Corollary 7.2.4. It
  indexes the derivatives by the multi-indices of a basis, with one $L^p(\Omega)$ function
  $\partial^\alpha v$ for each $\alpha$ with $|\alpha| \le k$. So that space is exactly an $\ell^p$
  product of $L^p(\Omega)$ spaces and, at $p = 2$, an inner product space with the inner product of
  the source. It repeats the argument of `Sobolev.isClosed` rather than building on it, because the
  two ambient products are different spaces; it reuses `MeasureTheory.MemLp.integralSmulCLM` and the
  weak derivative theory.
* A Hilbert–Schmidt norm on the $n$-linear maps is also an inner-product norm. But it is the
  $\ell^2$ sum over the tuples of directions, which weights the multi-index $\alpha$ by the
  multinomial coefficient $n!/\alpha!$, so it does not give the inner product of the source either.
-/

open Filter MeasureTheory Set TopologicalSpace

open scoped Distributions ENNReal Topology

/-! ### Integration against a fixed $L^q$ function -/

namespace MeasureTheory

variable {X G : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup G] [NormedSpace ℝ G] {p : ℝ≥0∞} {g : X → ℝ}

/-- **Hölder's inequality**, in integrability form. Let $p \ge 1$ and let $p'$ be its conjugate
exponent. If $g \in L^{p'}(\mu)$ is a real function and $u \in L^p(\mu)$ takes values in a real
normed space $G$, then $x \mapsto g(x) u(x)$ is integrable.

The conjugate exponent is `ENNReal.conjExponent p`. -/
theorem MemLp.integrable_smul_of_conjExponent [Fact (1 ≤ p)]
    (hg : MemLp g (ENNReal.conjExponent p) μ) {u : X → G} (hu : MemLp u p μ) :
    Integrable (fun x ↦ g x • u x) μ :=
  memLp_one_iff_integrable.1 (hg.smul hu)

/-- Let $p \ge 1$, let $p'$ be its conjugate exponent, let $G$ be a real Banach space, and let
$g \in L^{p'}(\mu)$ be a real function. Integration against $g$ is the continuous linear map
$$L^p(\mu; G) \to G, \qquad u \mapsto \int g(x) u(x) \, d\mu(x).$$
Its continuity is Hölder's inequality.

The map is `ContinuousLinearMap.lpPairing` for scalar multiplication, applied to the class of
$g$ in $L^{p'}$. -/
noncomputable def MemLp.integralSmulCLM (G : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] [Fact (1 ≤ p)] (hg : MemLp g (ENNReal.conjExponent p) μ) :
    Lp G p μ →L[ℝ] G :=
  letI : Fact (1 ≤ ENNReal.conjExponent p) := ⟨ENNReal.HolderConjugate.one_le _ p⟩
  (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing μ (ENNReal.conjExponent p) p (hg.toLp g)

/-- The map `MeasureTheory.MemLp.integralSmulCLM` sends $u \in L^p(\mu; G)$ to
$\int g(x) u(x) \, d\mu(x)$. -/
theorem MemLp.integralSmulCLM_apply [CompleteSpace G] [Fact (1 ≤ p)]
    (hg : MemLp g (ENNReal.conjExponent p) μ) (u : Lp G p μ) :
    hg.integralSmulCLM G u = ∫ x, g x • u x ∂μ := by
  have : Fact (1 ≤ ENNReal.conjExponent p) := ⟨ENNReal.HolderConjugate.one_le _ p⟩
  rw [MemLp.integralSmulCLM, ContinuousLinearMap.lpPairing_eq_integral]
  exact integral_congr_ae (by filter_upwards [hg.coeFn_toLp] with x hx using by simp [hx])

end MeasureTheory

/-! ### Test functions are $p$-integrable -/

/-- Let $E$ be a real normed space whose open sets are measurable, let $\mu$ be a measure on $E$
that is finite on compact sets, and let $q \in [0, \infty]$. Every test function $\varphi$ on
$\Omega$, of any order of smoothness, lies in $L^q(\mu)$, because it is continuous with compact
support. -/
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
/-- The ambient space of $W^{k,p}(\Omega)$: the tuples $(w_0, \dots, w_k)$ in which $w_n$ is an
$L^p(\Omega)$ function with values in the continuous $n$-linear maps $E^n \to F$. The norm is
the $\ell^p$ sum of the $L^p(\Omega)$ norms of the components. $W^{k,p}(\Omega)$ is the subspace
of the tuples in which $w_n$ is a weak derivative of order $n$ of $w_0$.

The space is a `PiLp p` indexed by `Fin (k + 1)`, and $L^p(\Omega)$ is $L^p$ for the restriction
of $\mu$ to $\Omega$. -/
abbrev SobolevTuple : Type _ :=
  PiLp p fun n : Fin (k + 1) ↦ Lp (E [×(n : ℕ)]→L[ℝ] F) p (μ.restrict (Ω : Set E))

namespace SobolevTuple

/-- The function underlying a tuple $(w_0, \dots, w_k)$ of `SobolevTuple F k p Ω μ`: its component
$w_0$ of order $0$, whose values are $0$-linear maps, read as a function $E \to F$ by evaluation
at the empty tuple. -/
noncomputable def fn (u : SobolevTuple F k p Ω μ) : E → F := fun x ↦ (u 0 x) 0

/-- At each point $x$, the function underlying a tuple takes the value $w_0(x)$ evaluated at the
empty tuple. -/
theorem fn_apply (u : SobolevTuple F k p Ω μ) (x : E) : u.fn x = (u 0 x) 0 := rfl

/-- The function underlying a tuple lies in $L^p(\Omega)$. -/
theorem memLp_fn (u : SobolevTuple F k p Ω μ) :
    MemLp u.fn p (μ.restrict (Ω : Set E)) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 ↦ E) F 0).comp_memLp' (Lp.memLp (u 0))

/-- The function underlying the zero tuple is $0$ almost everywhere on $\Omega$. -/
theorem fn_zero : (0 : SobolevTuple F k p Ω μ).fn =ᵐ[μ.restrict (Ω : Set E)] 0 := by
  filter_upwards [Lp.coeFn_zero (E [×(0 : ℕ)]→L[ℝ] F) p (μ.restrict (Ω : Set E))] with x hx
  exact congrArg (fun T : E [×(0 : ℕ)]→L[ℝ] F ↦ T 0) hx

/-- The function underlying a sum of two tuples is, almost everywhere on $\Omega$, the sum of their
functions. -/
theorem fn_add (u v : SobolevTuple F k p Ω μ) :
    (u + v).fn =ᵐ[μ.restrict (Ω : Set E)] u.fn + v.fn := by
  filter_upwards [Lp.coeFn_add (u 0) (v 0)] with x hx
  exact congrArg (fun T : E [×(0 : ℕ)]→L[ℝ] F ↦ T 0) hx

/-- The function underlying $c u$, for $c \in \mathbb{R}$ and a tuple $u$, is, almost everywhere on
$\Omega$, $c$ times the function of $u$. -/
theorem fn_smul (c : ℝ) (u : SobolevTuple F k p Ω μ) :
    (c • u).fn =ᵐ[μ.restrict (Ω : Set E)] c • u.fn := by
  filter_upwards [Lp.coeFn_smul c (u 0)] with x hx
  exact congrArg (fun T : E [×(0 : ℕ)]→L[ℝ] F ↦ T 0) hx

end SobolevTuple

/-! ### The space $W^{k,p}(\Omega)$ -/

variable [OpensMeasurableSpace E]

variable (F k p Ω μ) in
/-- Let $E$ be a real normed space whose open sets are measurable, let $F$ be a real normed space,
let $\Omega \subseteq E$ be open, let $\mu$ be a measure on $E$, and let $k \in \mathbb{N}$ and
$p \in [0, \infty]$. The **Sobolev space** $W^{k,p}(\Omega)$ is the subspace of
`SobolevTuple F k p Ω μ` of the tuples $(w_0, \dots, w_k)$ in which, for each $n \le k$, the
component $w_n$ is a weak derivative of order $n$ on $\Omega$ of the function $v$ that the tuple
carries: $v$ and $w_n$ are locally integrable on $\Omega$, and
$$\int_\Omega D^n \varphi(x)(y) \, v(x) \, d\mu(x) = (-1)^n \int_\Omega \varphi(x) \, w_n(x)(y)
  \, d\mu(x)$$
for every real test function $\varphi \in C_0^\infty(\Omega)$ and every $y \in E^n$. This is the
space of Definition 7.2.2 of [han2009theoretical]: a function of $L^p(\Omega)$ together with its
weak derivatives up to order $k$, all in $L^p(\Omega)$. The induced norm is the $\ell^p$ sum of
their $L^p(\Omega)$ norms.

The weak derivative relation is `HasWeakIteratedFDerivOn`, and $v$ is `SobolevTuple.fn`. All the
derivatives of order $n$ form one tensor $w_n$, measured in its operator norm, where the source
measures the derivatives $\partial^\alpha v$ with $|\alpha| = n$ separately; see the
implementation notes of the module. The type is identified with the predicate `MemSobolev` by
`Sobolev.memSobolev` and `MemSobolev.exists_sobolev`. -/
def Sobolev : Submodule ℝ (SobolevTuple F k p Ω μ) where
  carrier := {u | ∀ n : Fin (k + 1), HasWeakIteratedFDerivOn n u.fn (u n) Ω μ}
  zero_mem' _n :=
    HasWeakIteratedFDerivOn.zero.congr_ae SobolevTuple.fn_zero.symm (Lp.coeFn_zero _ _ _).symm
  add_mem' {u v} hu hv n :=
    ((hu n).add (hv n)).congr_ae (SobolevTuple.fn_add u v).symm (Lp.coeFn_add _ _).symm
  smul_mem' c u hu n :=
    ((hu n).const_smul c).congr_ae (SobolevTuple.fn_smul c u).symm (Lp.coeFn_smul _ _).symm

namespace Sobolev

/-- A tuple lies in $W^{k,p}(\Omega)$ if and only if, for each $n \le k$, its component of order $n$
is a weak derivative of order $n$ on $\Omega$ of the function that the tuple carries. -/
theorem mem_def {u : SobolevTuple F k p Ω μ} :
    u ∈ Sobolev F k p Ω μ ↔ ∀ n : Fin (k + 1), HasWeakIteratedFDerivOn n u.fn (u n) Ω μ :=
  Iff.rfl

/-- The function underlying an element of $W^{k,p}(\Omega)$: the function `SobolevTuple.fn` of its
tuple. An element is a term of a `Submodule`, so this is written `Sobolev.fn u` rather than
`u.fn`. -/
noncomputable def fn (u : Sobolev F k p Ω μ) : E → F :=
  SobolevTuple.fn (u : SobolevTuple F k p Ω μ)

/-- The weak derivative of order $n \le k$ of an element of $W^{k,p}(\Omega)$: the component $w_n$
of its tuple, an element of $L^p(\Omega)$ with values in the continuous $n$-linear maps
$E^n \to F$. -/
def weakDeriv (u : Sobolev F k p Ω μ) (n : Fin (k + 1)) :
    Lp (E [×(n : ℕ)]→L[ℝ] F) p (μ.restrict (Ω : Set E)) := (u : SobolevTuple F k p Ω μ) n

/-- For an element $u$ of $W^{k,p}(\Omega)$ and $n \le k$, the component `Sobolev.weakDeriv u n` is
a weak derivative of order $n$ on $\Omega$ of the function `Sobolev.fn u`. -/
theorem hasWeakIteratedFDerivOn (u : Sobolev F k p Ω μ) (n : Fin (k + 1)) :
    HasWeakIteratedFDerivOn n (fn u) (weakDeriv u n) Ω μ := u.2 n

/-- The function of the zero element of $W^{k,p}(\Omega)$ is $0$ almost everywhere on $\Omega$. -/
theorem fn_zero : fn (0 : Sobolev F k p Ω μ) =ᵐ[μ.restrict (Ω : Set E)] 0 :=
  SobolevTuple.fn_zero

/-- The function of a sum $u + v$ in $W^{k,p}(\Omega)$ is, almost everywhere on $\Omega$, the sum of
the functions of $u$ and $v$. -/
theorem fn_add (u v : Sobolev F k p Ω μ) :
    fn (u + v) =ᵐ[μ.restrict (Ω : Set E)] fn u + fn v :=
  SobolevTuple.fn_add _ _

/-- The function of a scalar multiple $c u$ in $W^{k,p}(\Omega)$ is, almost everywhere on $\Omega$,
$c$ times the function of $u$. -/
theorem fn_smul (c : ℝ) (u : Sobolev F k p Ω μ) :
    fn (c • u) =ᵐ[μ.restrict (Ω : Set E)] c • fn u :=
  SobolevTuple.fn_smul _ _

variable [Fact (1 ≤ p)]

/-- Let $p \ge 1$ and let $\mu$ be locally finite. A tuple $(w_0, \dots, w_k)$ of
`SobolevTuple F k p Ω μ` with function $v$ lies in $W^{k,p}(\Omega)$ if and only if
$$\int_\Omega D^n \varphi(x)(y) \, v(x) \, d\mu(x) = (-1)^n \int_\Omega \varphi(x) \, w_n(x)(y)
  \, d\mu(x)$$
for every $n \le k$, every real test function $\varphi \in C_0^\infty(\Omega)$ and every
$y \in E^n$. The local integrability that the weak derivative relation also asks for is
automatic for $L^p(\Omega)$ functions. -/
theorem mem_iff [IsLocallyFiniteMeasure μ] {u : SobolevTuple F k p Ω μ} :
    u ∈ Sobolev F k p Ω μ ↔ ∀ (n : Fin (k + 1)) (φ : 𝓓(Ω, ℝ)) (y : Fin n → E),
      ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • u.fn x ∂μ
        = (-1 : ℝ) ^ (n : ℕ) • ∫ x in (Ω : Set E), φ x • (u n x) y ∂μ :=
  ⟨fun h n φ y ↦ (h n).integral_smul_eq φ y, fun h n ↦
    { locallyIntegrableOn := u.memLp_fn.locallyIntegrableOn Fact.out
      locallyIntegrableOn_weakDeriv := (Lp.memLp (u n)).locallyIntegrableOn Fact.out
      integral_smul_eq := h n }⟩

omit [Fact (1 ≤ p)] in
/-- The function underlying an element of $W^{k,p}(\Omega)$ lies in $L^p(\Omega)$. -/
theorem memLp (u : Sobolev F k p Ω μ) : MemLp (fn u) p (μ.restrict (Ω : Set E)) :=
  SobolevTuple.memLp_fn _

omit [Fact (1 ≤ p)] in
/-- The function underlying an element of $W^{k,p}(\Omega)$ belongs to $W^{k,p}(\Omega)$ in the
sense of the predicate `MemSobolev`, which is Definition 7.2.2 of [han2009theoretical]. -/
theorem memSobolev (u : Sobolev F k p Ω μ) : MemSobolev (fn u) k p Ω μ := by
  refine ⟨memLp u, fun n hn ↦ ?_⟩
  have hn' : n < k + 1 := Nat.lt_succ_of_le (by exact_mod_cast hn)
  exact ⟨weakDeriv u ⟨n, hn'⟩, hasWeakIteratedFDerivOn u ⟨n, hn'⟩, Lp.memLp _⟩

/-! ### Completeness -/

section Complete

variable [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ]

variable (F k p Ω μ) in
/-- Let $p \ge 1$, let $F$ be complete, and let $\mu$ be finite on compact sets. For $n \le k$, a
real test function $\varphi$ on $\Omega$ and $y \in E^n$, the pairing
$$(w_0, \dots, w_k) \mapsto \int_\Omega \varphi(x) \, w_n(x)(y) \, d\mu(x)$$
is a continuous linear map from the ambient space `SobolevTuple F k p Ω μ` of $W^{k,p}(\Omega)$
to $F$. Its continuity is Hölder's inequality against $\varphi$, which lies in every
$L^q(\Omega)$. This is what makes the weak derivative relation a closed condition. -/
noncomputable def pairingCLM (n : Fin (k + 1)) (φ : 𝓓(Ω, ℝ)) (y : Fin n → E) :
    SobolevTuple F k p Ω μ →L[ℝ] F :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (n : ℕ) ↦ E) F y) ∘L
    ((TestFunction.memLp φ (ENNReal.conjExponent p)
      (μ.restrict (Ω : Set E))).integralSmulCLM (E [×(n : ℕ)]→L[ℝ] F)) ∘L PiLp.proj p _ n

omit [IsLocallyFiniteMeasure μ] in
/-- The map `Sobolev.pairingCLM F k p Ω μ n φ y` sends a tuple $(w_0, \dots, w_k)$ to
$\int_\Omega \varphi(x) \, w_n(x)(y) \, d\mu(x)$. -/
theorem pairingCLM_apply (n : Fin (k + 1)) (φ : 𝓓(Ω, ℝ)) (y : Fin n → E)
    (u : SobolevTuple F k p Ω μ) :
    pairingCLM F k p Ω μ n φ y u = ∫ x in (Ω : Set E), φ x • (u n x) y ∂μ := by
  rw [pairingCLM]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousMultilinearMap.apply_apply, MemLp.integralSmulCLM_apply, PiLp.proj_apply]
  exact ContinuousMultilinearMap.integral_apply
    ((TestFunction.memLp φ _ _).integrable_smul_of_conjExponent (Lp.memLp _)) y

/-- Let $p \ge 1$, let $F$ be complete, and let $\mu$ be locally finite and finite on compact sets.
Then $W^{k,p}(\Omega)$ is a closed subset of the $\ell^p$ product `SobolevTuple F k p Ω μ` of
$L^p(\Omega)$ spaces. This is the substance of Theorem 7.2.3 of [han2009theoretical].

An $L^p(\Omega)$ limit of weak derivatives is a weak derivative, because the integration by
parts formula pairs the functions against a fixed test function, and this pairing
(`Sobolev.pairingCLM`) is continuous on $L^p(\Omega)$. -/
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

/-- Let $p \ge 1$, let $F$ be complete, and let $\mu$ be locally finite and finite on compact sets.
Then the Sobolev space $W^{k,p}(\Omega)$ is a Banach space. This is Theorem 7.2.3 of
[han2009theoretical].

The space is a closed subspace of an $\ell^p$ product of $L^p(\Omega)$ spaces, by
`Sobolev.isClosed`, so it inherits their completeness. -/
instance instCompleteSpace : CompleteSpace (Sobolev F k p Ω μ) :=
  Sobolev.isClosed.completeSpace_coe

end Complete

/-! ### Comparison with the predicate `MemSobolev` -/

/-- Let $p \ge 1$ and let $\mu$ be locally finite. If $f$ belongs to $W^{k,p}(\Omega)$ in the sense
of `MemSobolev`, then there is an element $u$ of `Sobolev F k p Ω μ` whose function equals $f$
almost everywhere on $\Omega$. Together with `Sobolev.memSobolev`, this identifies the type with
the space of Definition 7.2.2 of [han2009theoretical]. -/
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
/-- Let $E$ be finite-dimensional with its Borel σ-algebra, and let $F$ be complete. If the
functions of two elements $u$ and $v$ of $W^{k,p}(\Omega)$ agree almost everywhere on $\Omega$,
then $u = v$. So the whole tuple of an element is determined by its function.

This is the almost everywhere uniqueness of the weak derivative,
`HasWeakIteratedFDerivOn.ae_eq`. -/
theorem ext_of_fn_ae_eq {u v : Sobolev F k p Ω μ}
    (h : fn u =ᵐ[μ.restrict (Ω : Set E)] fn v) : u = v :=
  Subtype.ext <| PiLp.ext fun n ↦ Lp.ext <|
    (ae_restrict_iff' Ω.isOpen.measurableSet).2
      (((hasWeakIteratedFDerivOn u n).congr_ae h (Filter.EventuallyEq.refl _ _)).ae_eq
        (hasWeakIteratedFDerivOn v n))

/-! ### The norm -/

omit [Fact (1 ≤ p)] in
/-- Let $E$ be finite-dimensional with its Borel σ-algebra, and let $F$ be complete. For an element
$u$ of $W^{k,p}(\Omega)$ and $n \le k$, the $L^p(\Omega)$ norm of the chosen weak derivative
`weakIteratedFDeriv n (Sobolev.fn u) Ω μ` equals the $L^p(\Omega)$ norm of the component
`Sobolev.weakDeriv u n`. -/
theorem eLpNorm_weakIteratedFDeriv (u : Sobolev F k p Ω μ) (n : Fin (k + 1)) :
    eLpNorm (weakIteratedFDeriv n (fn u) Ω μ) p (μ.restrict (Ω : Set E))
      = eLpNorm (weakDeriv u n) p (μ.restrict (Ω : Set E)) :=
  eLpNorm_congr_ae <| (ae_restrict_iff' Ω.isOpen.measurableSet).2
    (hasWeakIteratedFDerivOn u n).weakIteratedFDeriv_ae_eq

/-- Let $p \ge 1$, let $E$ be finite-dimensional with its Borel σ-algebra, and let $F$ be complete.
The norm of an element $u$ of $W^{k,p}(\Omega)$ with function $v$ is
$$\|u\| = \Big(\sum_{n = 0}^{k} \|D^n v\|_{L^p(\Omega)}^p\Big)^{1/p}$$
for $p < \infty$, and $\max_{n \le k} \|D^n v\|_{L^\infty(\Omega)}$ for $p = \infty$, where
$D^n v$ is the weak derivative of order $n$. This is the norm of Definition 7.2.2 of
[han2009theoretical] as `sobolevNorm` reads it.

The right side is `ENNReal.toReal (sobolevNorm (Sobolev.fn u) k p Ω μ)`, in which $D^n v$ is
`weakIteratedFDeriv`, with the derivatives of each order collected into one tensor. -/
theorem norm_eq (u : Sobolev F k p Ω μ) : ‖u‖ = (sobolevNorm (fn u) k p Ω μ).toReal := by
  have hfin : ∀ n : Fin (k + 1),
      eLpNorm (weakIteratedFDeriv (n : ℕ) (fn u) Ω μ) p (μ.restrict (Ω : Set E)) ≠ ⊤ := by
    intro n
    rw [eLpNorm_weakIteratedFDeriv]
    exact (Lp.memLp (weakDeriv u n)).eLpNorm_lt_top.ne
  rw [← Submodule.norm_coe, sobolevNorm]
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

/-! ### The subspace $W_0^{k,p}(\Omega)$ -/

section Zero

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] [μ.IsAddHaarMeasure]

section

variable {K : ℕ∞}

omit [Fact (1 ≤ p)] [CompleteSpace F] in
/-- Let $E$ be finite-dimensional with its Borel σ-algebra, let $\mu$ be an additive Haar measure,
let $K \in \mathbb{N} \cup \{\infty\}$ and let $p \in [0, \infty]$. Every test function
$\varphi \in C_0^\infty(\Omega, F)$ belongs to $W^{K,p}(\Omega)$ in the sense of `MemSobolev`.

The classical derivatives of $\varphi$ are its weak derivatives (Lemma 7.1.5 of
[han2009theoretical]), and each of them is continuous with compact support in $\Omega$, hence in
$L^p(\Omega)$. -/
theorem _root_.TestFunction.memSobolev (φ : 𝓓(Ω, F)) : MemSobolev (φ : E → F) K p Ω μ := by
  refine ⟨(TestFunction.memLp φ p μ).restrict _, fun n _ ↦
    ⟨iteratedFDeriv ℝ n φ, φ.contDiff.contDiffOn.hasWeakIteratedFDerivOn (by simp), ?_⟩⟩
  exact ((φ.contDiff.continuous_iteratedFDeriv (m := n) (by simp)).memLp_of_hasCompactSupport
    (φ.hasCompactSupport.iteratedFDeriv n)).restrict _

end

variable (F k p Ω μ) in
/-- The image of the test functions $C_0^\infty(\Omega)$ in $W^{k,p}(\Omega)$: the submodule of the
elements whose function agrees almost everywhere on $\Omega$ with a test function on $\Omega$.
Every test function occurs, by `TestFunction.exists_mem_testFunctions`. -/
def testFunctions : Submodule ℝ (Sobolev F k p Ω μ) where
  carrier := {u | ∃ φ : 𝓓(Ω, F), fn u =ᵐ[μ.restrict (Ω : Set E)] φ}
  zero_mem' := ⟨0, fn_zero⟩
  add_mem' := fun {u v} ⟨φ, hφ⟩ ⟨ψ, hψ⟩ ↦ ⟨φ + ψ, (fn_add u v).trans (hφ.add hψ)⟩
  smul_mem' := fun c u ⟨φ, hφ⟩ ↦ ⟨c • φ, (fn_smul c u).trans (hφ.const_smul c)⟩

omit [CompleteSpace F] in
/-- Let $p \ge 1$, let $E$ be finite-dimensional with its Borel σ-algebra, and let $\mu$ be an
additive Haar measure. For every test function $\varphi$ on $\Omega$ there is an element of
`Sobolev.testFunctions` whose function equals $\varphi$ almost everywhere on $\Omega$. So that
submodule is the image of $C_0^\infty(\Omega)$ in $W^{k,p}(\Omega)$. -/
theorem _root_.TestFunction.exists_mem_testFunctions (φ : 𝓓(Ω, F)) :
    ∃ u ∈ testFunctions F k p Ω μ, fn u =ᵐ[μ.restrict (Ω : Set E)] φ :=
  let ⟨u, hu⟩ := (TestFunction.memSobolev φ).exists_sobolev
  ⟨u, ⟨φ, hu⟩, hu⟩

end Zero

end Sobolev

variable [Fact (1 ≤ p)] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]

variable (F k p Ω μ) in
/-- Let $p \ge 1$. The **Sobolev space** $W_0^{k,p}(\Omega)$ is the closure of $C_0^\infty(\Omega)$,
that is, of `Sobolev.testFunctions`, in $W^{k,p}(\Omega)$. This is Definition 7.2.9 of
[han2009theoretical].

Informally, its elements are the functions whose derivatives of order at most $k - 1$ vanish on
the boundary of $\Omega$, a reading that only the trace theorems make precise. -/
noncomputable def SobolevZero : Submodule ℝ (Sobolev F k p Ω μ) :=
  (Sobolev.testFunctions F k p Ω μ).topologicalClosure
