/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the Bessel potential spaces on the
whole space that already live there.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.WeakDeriv

/-!
# Sobolev spaces of integer order on an open set, and the regularity of the boundary

Let $\Omega$ be an open set in a real normed space $E$ with a measure $\mu$, let
$k \in \mathbb{N} \cup \{\infty\}$ and $p \in [0, \infty]$; most results assume $p \ge 1$. A
function $f : E \to F$ belongs to the **Sobolev space** $W^{k,p}(\Omega)$ if $f \in L^p(\Omega)$
and, for every order $n \le k$, $f$ has a weak derivative $D^n f$ of order $n$ on $\Omega$ that
lies in $L^p(\Omega)$. This is Definition 7.2.2 of [han2009theoretical]. The file defines this
membership, the norm
$$\|f\|_{k,p,\Omega} = \Bigl(\sum_{n=0}^{k} \|D^n f\|_{L^p(\Omega)}^p\Bigr)^{1/p}$$
and the seminorm $|f|_{k,p,\Omega} = \|D^k f\|_{L^p(\Omega)}$, and it proves that $W^{k,p}(\Omega)$
is a linear subspace of $L^p(\Omega)$ that decreases in $k$. The module
`Numlib.Analysis.Sobolev.Space` carries the same space as a type, `Sobolev F k p Ω μ`, whose norm is
`sobolevNorm` and which is a Banach space.

The last section is about the domain. The boundary of a set $\Omega \subseteq \mathbb{R}^{d+1}$ is
**of class $V$** if, near each boundary point and after a rigid motion of the coordinates, $\Omega$
is the region above the graph of a function of $d$ variables in the class $V$. This is Definition
7.2.1 of [han2009theoretical]. It is the hypothesis under which the structure theory of Sobolev
spaces on a domain (extension, density up to the boundary, the trace) is stated. Lipschitz domains
and $C^n$ domains are the two named cases.

## Main definitions

* `MemSobolev`: membership of $W^{k,p}(\Omega)$.
* `weakIteratedFDeriv`: a choice of weak derivative of order $n$, or $0$ when there is none.
* `sobolevNorm` and `sobolevSeminorm`: the norm and the seminorm of $W^{k,p}(\Omega)$.
* `IsBoundaryOfClass`: the boundary of $\Omega \subseteq \mathbb{R}^{d+1}$ is locally the graph of a
  function in a class $V$ of functions of $d$ variables.
* `IsLipschitzDomain` and `IsContDiffDomain`: Lipschitz domains and $C^n$ domains.

## Main results

* `MemSobolev.congr_ae`: membership of $W^{k,p}(\Omega)$ depends on the function only up to a null
  set of $\Omega$.
* `MemSobolev.mono_order`, `MemSobolev.mono_set` and `MemSobolev.mono_exponent`: $W^{k,p}(\Omega)$
  decreases as $k$ increases, is inherited by open subsets, and increases as $p$ decreases on a set
  of finite measure.
* `memSobolev_zero_order`: $W^{0,p}(\Omega) = L^p(\Omega)$.
* `MemSobolev.add`, `MemSobolev.const_smul`, `MemSobolev.neg`, `MemSobolev.sub` and
  `memSobolev_zero`: $W^{k,p}(\Omega)$ is a linear subspace of $L^p(\Omega)$.
* `IsBoundaryOfClass.exists_finite_cover`: the boundary of a bounded set of class $V$ is covered by
  finitely many balls in each of which it is a graph.

## Implementation notes

* This file, like `Numlib.Analysis.Sobolev.WeakDeriv`, stands in for Mathlib pull request 32305 and
  its continuation (by Michael Rothgang, Filippo Nuccio and Floris van Doorn). `MemSobolev` and
  `sobolevNorm` follow that work in name and in the order of the arguments, so that a migration is a
  rename.
* The module `Mathlib.Analysis.Distribution.Sobolev` is about a different subject: the Bessel
  potential spaces $H^{s,p}$ of tempered distributions on the whole space, with no domain.
* The boundary regularity of the last section is not part of that pull request, which works over an
  arbitrary open set with no condition on $\partial\Omega$. Mathlib has no `IsLipschitzDomain`,
  `IsBoundaryOfClass` or `EuclideanSpace.init` under these or similar names. Nothing in the first
  part of this file depends on the boundary section.
* The derivatives of order $n$ are one function with values in the continuous $n$-linear maps
  (`ContinuousMultilinearMap`), not a family indexed by multi-indices. So `sobolevNorm` sums the
  $L^p$ norms of the derivative tensors, each measured in the operator norm, over the orders
  $n \le k$. Atkinson and Han sum over the multi-indices $\alpha$ with $|\alpha| \le k$ instead. The
  two norms are equivalent, because on $\mathbb{R}^d$ the operator norm of a symmetric $n$-tensor is
  comparable to any norm on its finitely many entries. They are not equal, so `sobolevNorm` is not
  literally the formula of Definition 7.2.2.
* As a consequence, for $k \ge 2$ and $\dim E \ge 2$ the norm `sobolevNorm f k 2 Ω μ` is not an
  inner-product norm, because the operator norm on $n$-linear maps with $n \ge 2$ on a space of
  dimension at least $2$ is not one. For $k \le 1$ or $\dim E \le 1$ it is an inner-product norm.
* The module `Numlib.Analysis.Sobolev.MultiIndex` indexes the derivatives by multi-indices, and so
  has the book's own norm and, at $p = 2$, its inner product. The comparison is
  `MemSobolev.memSobolevMultiIndex`. The space, the norm and the completeness do not need it; it is
  needed for $H^k(\Omega)$ to be a Hilbert space, Corollary 7.2.4 of [han2009theoretical].
-/

open Filter MeasureTheory Set TopologicalSpace

open scoped Distributions ENNReal Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {μ : Measure E} {n : ℕ} {k : ℕ∞} {p : ℝ≥0∞} {f : E → F}

/-! ### Preliminaries -/

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Let $1 \le p$ and let $\mu$ be locally finite. A function of $L^p(\Omega)$ is locally integrable
on $\Omega$. -/
theorem MeasureTheory.MemLp.locallyIntegrableOn [OpensMeasurableSpace E] [IsLocallyFiniteMeasure μ]
    (hf : MemLp f p (μ.restrict Ω)) (hp : 1 ≤ p) : LocallyIntegrableOn f (Ω : Set E) μ :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable hp)

/-- Every function $f$ that is locally integrable on $\Omega$ has a weak derivative of order $0$ on
$\Omega$, namely $f$ itself, read as a $0$-linear map. -/
theorem hasWeakIteratedFDerivOn_zero (hf : LocallyIntegrableOn f (Ω : Set E) μ) :
    HasWeakIteratedFDerivOn 0 f
      (fun x ↦ (continuousMultilinearCurryFin0 ℝ E F).symm (f x)) Ω μ where
  locallyIntegrableOn := hf
  locallyIntegrableOn_weakDeriv := hf.comp_continuousLinearMap
    (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
  integral_smul_eq φ y := by simp

/-! ### Membership of $W^{k,p}(\Omega)$ -/

/-- A function $f : E \to F$ belongs to the **Sobolev space** $W^{k,p}(\Omega)$, for
$k \in \mathbb{N} \cup \{\infty\}$, if $f \in L^p(\Omega)$ and, for every $n \in \mathbb{N}$
with $n \le k$, there is a weak derivative $w$ of order $n$ of $f$ on $\Omega$ with
$w \in L^p(\Omega)$. This is Definition 7.2.2 of [han2009theoretical].

The weak derivative of order $n$ is a function with values in the continuous $n$-linear maps
from $E$ to $F$ (`HasWeakIteratedFDerivOn`). A tuple of $n$ directions plays the role of a
multi-index $\alpha$ with $|\alpha| = n$. For $k = \infty$ the condition holds for all orders. -/
def MemSobolev (f : E → F) (k : ℕ∞) (p : ℝ≥0∞) (Ω : Opens E) (μ : Measure E) : Prop :=
  MemLp f p (μ.restrict Ω) ∧ ∀ n : ℕ, (n : ℕ∞) ≤ k →
    ∃ w : E → E [×n]→L[ℝ] F, HasWeakIteratedFDerivOn n f w Ω μ ∧ MemLp w p (μ.restrict Ω)

namespace MemSobolev

/-- A function of $W^{k,p}(\Omega)$ lies in $L^p(\Omega)$. -/
theorem memLp (h : MemSobolev f k p Ω μ) : MemLp f p (μ.restrict Ω) := h.1

/-- A function of $W^{k,p}(\Omega)$ has, for every order $n \le k$, a weak derivative of order $n$
on $\Omega$ that lies in $L^p(\Omega)$. -/
theorem exists_hasWeakIteratedFDerivOn (h : MemSobolev f k p Ω μ) (hn : (n : ℕ∞) ≤ k) :
    ∃ w : E → E [×n]→L[ℝ] F, HasWeakIteratedFDerivOn n f w Ω μ ∧ MemLp w p (μ.restrict Ω) :=
  h.2 n hn

/-- Membership of $W^{k,p}(\Omega)$ depends on the function only up to a null set of $\Omega$: if
$f \in W^{k,p}(\Omega)$ and $f = f'$ almost everywhere on $\Omega$, then
$f' \in W^{k,p}(\Omega)$. -/
theorem congr_ae {f' : E → F} (h : MemSobolev f k p Ω μ)
    (hf : f =ᵐ[μ.restrict (Ω : Set E)] f') : MemSobolev f' k p Ω μ := by
  refine ⟨h.1.ae_eq hf, fun n hn ↦ ?_⟩
  obtain ⟨w, hw, hwp⟩ := h.2 n hn
  exact ⟨w, hw.congr_ae hf (Filter.EventuallyEq.refl _ _), hwp⟩

/-- The space $W^{k,p}(\Omega)$ decreases as the order increases: if $f \in W^{k,p}(\Omega)$ and
$k' \le k$, then $f \in W^{k',p}(\Omega)$. -/
theorem mono_order {k' : ℕ∞} (h : MemSobolev f k p Ω μ) (hk : k' ≤ k) : MemSobolev f k' p Ω μ :=
  ⟨h.1, fun n hn ↦ h.2 n (hn.trans hk)⟩

/-- Membership of $W^{k,p}$ is inherited by open subsets: if $f \in W^{k,p}(\Omega)$ and
$\Omega' \subseteq \Omega$ is open, then $f \in W^{k,p}(\Omega')$. -/
theorem mono_set {Ω' : Opens E} (h : MemSobolev f k p Ω μ)
    (hΩ : Ω' ≤ Ω) : MemSobolev f k p Ω' μ := by
  refine ⟨h.1.mono_measure (Measure.restrict_mono hΩ le_rfl), fun n hn ↦ ?_⟩
  obtain ⟨w, hw, hwp⟩ := h.2 n hn
  exact ⟨w, hw.mono hΩ, hwp.mono_measure (Measure.restrict_mono hΩ le_rfl)⟩

/-- On a set of finite measure, $W^{k,p}(\Omega)$ increases as the exponent decreases: if
$\mu(\Omega) < \infty$, $q \le p$ and $f \in W^{k,p}(\Omega)$, then $f \in W^{k,q}(\Omega)$. -/
theorem mono_exponent {q : ℝ≥0∞} (h : MemSobolev f k p Ω μ) (hpq : q ≤ p)
    (hΩ : μ (Ω : Set E) ≠ ⊤) : MemSobolev f k q Ω μ := by
  have : IsFiniteMeasure (μ.restrict (Ω : Set E)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hΩ⟩
  refine ⟨h.1.mono_exponent hpq, fun n hn ↦ ?_⟩
  obtain ⟨w, hw, hwp⟩ := h.2 n hn
  exact ⟨w, hw, hwp.mono_exponent hpq⟩

end MemSobolev

/-- Let $1 \le p$ and let $\mu$ be locally finite. Then $W^{0,p}(\Omega) = L^p(\Omega)$: a function
belongs to $W^{0,p}(\Omega)$ if and only if it belongs to $L^p(\Omega)$. This is Definition
7.2.2 of [han2009theoretical] with $k = 0$. -/
theorem memSobolev_zero_order [OpensMeasurableSpace E] [IsLocallyFiniteMeasure μ] (hp : 1 ≤ p) :
    MemSobolev f 0 p Ω μ ↔ MemLp f p (μ.restrict Ω) := by
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun n hn ↦ ?_⟩⟩
  obtain rfl : n = 0 := by exact_mod_cast le_antisymm hn (Nat.cast_le.2 n.zero_le)
  refine ⟨_, hasWeakIteratedFDerivOn_zero (h.locallyIntegrableOn hp), ?_⟩
  exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
    |>.comp_memLp' h

/-! ### The linear structure -/

section Linear

variable [OpensMeasurableSpace E]

omit [OpensMeasurableSpace E] in
/-- The zero function lies in every $W^{k,p}(\Omega)$. -/
theorem memSobolev_zero : MemSobolev (0 : E → F) k p Ω μ :=
  ⟨MemLp.zero, fun n _ ↦ ⟨(0 : E → E [×n]→L[ℝ] F), HasWeakIteratedFDerivOn.zero, MemLp.zero⟩⟩

namespace MemSobolev

/-- The space $W^{k,p}(\Omega)$ is closed under addition: if $f_1, f_2 \in W^{k,p}(\Omega)$, then
$f_1 + f_2 \in W^{k,p}(\Omega)$. -/
protected theorem add {f₁ f₂ : E → F} (h₁ : MemSobolev f₁ k p Ω μ) (h₂ : MemSobolev f₂ k p Ω μ) :
    MemSobolev (f₁ + f₂) k p Ω μ := by
  refine ⟨h₁.1.add h₂.1, fun n hn ↦ ?_⟩
  obtain ⟨w₁, hw₁, hw₁p⟩ := h₁.2 n hn
  obtain ⟨w₂, hw₂, hw₂p⟩ := h₂.2 n hn
  exact ⟨w₁ + w₂, hw₁.add hw₂, hw₁p.add hw₂p⟩

omit [OpensMeasurableSpace E] in
/-- The space $W^{k,p}(\Omega)$ is closed under scalar multiplication: if $f \in W^{k,p}(\Omega)$
and $c \in \mathbb{R}$, then $cf \in W^{k,p}(\Omega)$. -/
protected theorem const_smul (h : MemSobolev f k p Ω μ) (c : ℝ) :
    MemSobolev (c • f) k p Ω μ := by
  refine ⟨h.1.const_smul c, fun n hn ↦ ?_⟩
  obtain ⟨w, hw, hwp⟩ := h.2 n hn
  exact ⟨c • w, hw.const_smul c, hwp.const_smul c⟩

omit [OpensMeasurableSpace E] in
/-- The space $W^{k,p}(\Omega)$ is closed under negation: if $f \in W^{k,p}(\Omega)$, then
$-f \in W^{k,p}(\Omega)$. -/
protected theorem neg (h : MemSobolev f k p Ω μ) : MemSobolev (-f) k p Ω μ := by
  refine ⟨h.1.neg, fun n hn ↦ ?_⟩
  obtain ⟨w, hw, hwp⟩ := h.2 n hn
  exact ⟨-w, hw.neg, hwp.neg⟩

/-- The space $W^{k,p}(\Omega)$ is closed under subtraction: if $f_1, f_2 \in W^{k,p}(\Omega)$, then
$f_1 - f_2 \in W^{k,p}(\Omega)$. -/
protected theorem sub {f₁ f₂ : E → F} (h₁ : MemSobolev f₁ k p Ω μ) (h₂ : MemSobolev f₂ k p Ω μ) :
    MemSobolev (f₁ - f₂) k p Ω μ := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

end MemSobolev

end Linear

/-! ### The Sobolev norm -/

open Classical in
/-- A choice of **weak derivative of order $n$** of $f$ on $\Omega$: a function $D^n f$ with values
in the continuous $n$-linear maps from $E$ to $F$ that is a weak derivative of order $n$ of $f$
on $\Omega$, and the function $0$ when $f$ has no weak derivative of order $n$.

The choice is determined almost everywhere on $\Omega$
(`HasWeakIteratedFDerivOn.weakIteratedFDeriv_ae_eq`). -/
noncomputable def weakIteratedFDeriv (n : ℕ) (f : E → F) (Ω : Opens E) (μ : Measure E) :
    E → E [×n]→L[ℝ] F :=
  if h : ∃ w, HasWeakIteratedFDerivOn n f w Ω μ then h.choose else 0

/-- If $f$ has a weak derivative of order $n$ on $\Omega$, then the chosen function
`weakIteratedFDeriv n f Ω μ` is a weak derivative of order $n$ of $f$ on $\Omega$. -/
theorem HasWeakIteratedFDerivOn.hasWeakIteratedFDerivOn_weakIteratedFDeriv
    {w : E → E [×n]→L[ℝ] F} (h : HasWeakIteratedFDerivOn n f w Ω μ) :
    HasWeakIteratedFDerivOn n f (weakIteratedFDeriv n f Ω μ) Ω μ := by
  rw [weakIteratedFDeriv]
  split
  · exact Exists.choose_spec ‹_›
  · exact absurd (⟨w, h⟩ : ∃ w, HasWeakIteratedFDerivOn n f w Ω μ) ‹_›

/-- Let $E$ be finite-dimensional and $F$ complete. If $w$ is a weak derivative of order $n$ of $f$
on $\Omega$, then the chosen weak derivative `weakIteratedFDeriv n f Ω μ` agrees with $w$ at
almost every point of $\Omega$. -/
theorem HasWeakIteratedFDerivOn.weakIteratedFDeriv_ae_eq [FiniteDimensional ℝ E] [BorelSpace E]
    [CompleteSpace F] {w : E → E [×n]→L[ℝ] F} (h : HasWeakIteratedFDerivOn n f w Ω μ) :
    ∀ᵐ x ∂μ, x ∈ (Ω : Set E) → weakIteratedFDeriv n f Ω μ x = w x :=
  h.hasWeakIteratedFDerivOn_weakIteratedFDeriv.ae_eq h

/-- The **Sobolev norm** of $f$ on $\Omega$, with values in $[0, \infty]$, is
$$\|f\|_{k,p,\Omega} = \Bigl(\sum_{n=0}^{k} \|D^n f\|_{L^p(\Omega)}^p\Bigr)^{1/p}$$
for $p < \infty$, and $\|f\|_{k,\infty,\Omega} = \max_{0 \le n \le k} \|D^n
f\|_{L^\infty(\Omega)}$ for $p = \infty$. This is the norm of Definition 7.2.2 of
[han2009theoretical]. Here $D^n f$ is the chosen weak derivative `weakIteratedFDeriv n f Ω μ`,
and the $L^p$ norm uses the operator norm of $n$-linear maps at each point.

The book sums over the multi-indices $\alpha$ with $|\alpha| \le k$; here the derivatives of
each order form one tensor. The two norms are equivalent but not equal (see the implementation
notes of the module). If $f$ has no weak derivative of some order $n$, the term of order $n$ is
$0$. At $p = 0$ the formula gives the value $1$. -/
noncomputable def sobolevNorm (f : E → F) (k : ℕ) (p : ℝ≥0∞) (Ω : Opens E) (μ : Measure E) :
    ℝ≥0∞ :=
  if p = ⊤ then ⨆ n : Fin (k + 1), eLpNorm (weakIteratedFDeriv n f Ω μ) ⊤ (μ.restrict Ω)
  else (∑ n : Fin (k + 1), eLpNorm (weakIteratedFDeriv n f Ω μ) p (μ.restrict Ω) ^ p.toReal)
    ^ (1 / p.toReal)

/-- The **Sobolev seminorm** of $f$ on $\Omega$, with values in $[0, \infty]$, is the $L^p(\Omega)$
norm of the weak derivative of top order:
$$|f|_{k,p,\Omega} = \|D^k f\|_{L^p(\Omega)}.$$
This is the seminorm of Definition 7.2.2 of [han2009theoretical].

The book sums over the multi-indices $\alpha$ with $|\alpha| = k$; here $D^k f$ is one tensor
(`weakIteratedFDeriv k f Ω μ`), measured in the operator norm at each point. -/
noncomputable def sobolevSeminorm (f : E → F) (k : ℕ) (p : ℝ≥0∞) (Ω : Opens E) (μ : Measure E) :
    ℝ≥0∞ :=
  eLpNorm (weakIteratedFDeriv k f Ω μ) p (μ.restrict Ω)

/-! ### Regularity of the boundary -/

section Boundary

variable {d : ℕ} {V : Set (EuclideanSpace ℝ (Fin d) → ℝ)}
  {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))}

/-- The first $d$ coordinates $(x_1, \dots, x_d)$ of a point $x \in \mathbb{R}^{d+1}$, as a point of
$\mathbb{R}^d$.

This is `Fin.init` read between Euclidean spaces. It is the projection along which
`IsBoundaryGraphAt` writes the boundary of a domain as a graph. -/
def EuclideanSpace.init (x : EuclideanSpace ℝ (Fin (d + 1))) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i ↦ x i.castSucc

/-- The coordinate $i$ of `EuclideanSpace.init x` is the coordinate $i$ of $x$, for $i < d$. -/
@[simp]
theorem EuclideanSpace.init_apply (x : EuclideanSpace ℝ (Fin (d + 1))) (i : Fin d) :
    EuclideanSpace.init x i = x i.castSucc :=
  rfl

/-- Let $V$ be a class of functions $\mathbb{R}^d \to \mathbb{R}$, let
$\Omega \subseteq \mathbb{R}^{d+1}$, $x_0 \in \mathbb{R}^{d+1}$ and $r \in \mathbb{R}$. The set
$\Omega$ is **a graph of class $V$ near $x_0$ at radius $r$** if there are an affine isometry
$T$ of $\mathbb{R}^{d+1}$ and a function $g \in V$ with
$$\Omega \cap B(x_0, r)
  = \{x \in B(x_0, r) : g\bigl((Tx)_1, \dots, (Tx)_d\bigr) < (Tx)_{d+1}\}.$$
So in the ball, after the change of coordinates $T$, the set $\Omega$ is the region strictly
above the graph of $g$. This is the local condition of Definition 7.2.1 of [han2009theoretical].

The isometry $T$ is the rigid motion of the coordinate system; it may include a reflection. The
radius is named so that a covering of the boundary by such balls can be stated.
`IsBoundaryOfClass` quantifies the condition over the boundary. -/
def IsBoundaryGraphAt (V : Set (EuclideanSpace ℝ (Fin d) → ℝ))
    (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) (x₀ : EuclideanSpace ℝ (Fin (d + 1))) (r : ℝ) :
    Prop :=
  ∃ T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)), ∃ g ∈ V,
    Ω ∩ Metric.ball x₀ r =
      {x ∈ Metric.ball x₀ r | g (EuclideanSpace.init (T x)) < T x (Fin.last d)}

/-- Let $V$ be a class of functions $\mathbb{R}^d \to \mathbb{R}$. The boundary of a set
$\Omega \subseteq \mathbb{R}^{d+1}$ is **of class $V$** if every point $x_0 \in \partial\Omega$
has a radius $r > 0$ such that $\Omega$ is a graph of class $V$ near $x_0$ at radius $r$
(`IsBoundaryGraphAt`): in the ball $B(x_0, r)$, after a rigid motion of the coordinate system,
$\Omega$ is the region strictly above the graph of some $g \in V$. This is Definition 7.2.1 of
[han2009theoretical].

The book takes $\Omega$ open and bounded. Neither hypothesis is part of this definition; the
results that need them state them (`IsBoundaryOfClass.exists_finite_cover` assumes boundedness).
The class $V$ of Lipschitz functions gives a Lipschitz domain (`IsLipschitzDomain`), the class
of $C^n$ functions gives a $C^n$ domain (`IsContDiffDomain`), and the class of $C^{k,\alpha}$
functions gives a Hölder boundary of class $C^{k,\alpha}$. -/
def IsBoundaryOfClass (V : Set (EuclideanSpace ℝ (Fin d) → ℝ))
    (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) : Prop :=
  ∀ x₀ ∈ frontier Ω, ∃ r > 0, IsBoundaryGraphAt V Ω x₀ r

/-- A set $\Omega \subseteq \mathbb{R}^{d+1}$ is a **Lipschitz domain** if $\Omega$ is open and its
boundary is of class $V$ for the class $V$ of Lipschitz continuous functions
$\mathbb{R}^d \to \mathbb{R}$: locally and after a rigid motion of the coordinate system,
$\Omega$ lies above the graph of a Lipschitz function of $d$ variables. This is Definition 7.2.1
of [han2009theoretical] for Lipschitz functions.

The book assumes $\Omega$ bounded throughout. Boundedness is not part of this definition: a
hypothesis `Bornology.IsBounded Ω` is stated beside it where it is needed, as in the phrase
"bounded Lipschitz domain". -/
def IsLipschitzDomain (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) : Prop :=
  IsOpen Ω ∧ IsBoundaryOfClass {g | ∃ K, LipschitzWith K g} Ω

/-- A set $\Omega \subseteq \mathbb{R}^{d+1}$ is a **$C^n$ domain** if $\Omega$ is open and its
boundary is of class $V$ for the class $V$ of $C^n$ functions $\mathbb{R}^d \to \mathbb{R}$:
locally and after a rigid motion of the coordinate system, $\Omega$ lies above the graph of a
$C^n$ function of $d$ variables. This is Definition 7.2.1 of [han2009theoretical] for $C^n$
functions.

The order $n$ is in `WithTop ℕ∞`, so it can be a natural number, $\infty$ (smooth) or $\omega$
(analytic). As for `IsLipschitzDomain`, boundedness is not part of the definition. -/
def IsContDiffDomain (n : WithTop ℕ∞) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) : Prop :=
  IsOpen Ω ∧ IsBoundaryOfClass {g | ContDiff ℝ n g} Ω

/-- A Lipschitz domain is open. -/
theorem IsLipschitzDomain.isOpen (h : IsLipschitzDomain Ω) : IsOpen Ω := h.1

/-- The boundary of a Lipschitz domain is of class $V$ for the class $V$ of Lipschitz functions: it
is locally the graph of a Lipschitz function. -/
theorem IsLipschitzDomain.isBoundaryOfClass (h : IsLipschitzDomain Ω) :
    IsBoundaryOfClass {g | ∃ K, LipschitzWith K g} Ω := h.2

/-- A $C^n$ domain is open. -/
theorem IsContDiffDomain.isOpen {n : WithTop ℕ∞} (h : IsContDiffDomain n Ω) : IsOpen Ω := h.1

/-- The boundary of a $C^n$ domain is of class $V$ for the class $V$ of $C^n$ functions: it is
locally the graph of a $C^n$ function. -/
theorem IsContDiffDomain.isBoundaryOfClass {n : WithTop ℕ∞} (h : IsContDiffDomain n Ω) :
    IsBoundaryOfClass {g | ContDiff ℝ n g} Ω := h.2

/-- The local graph condition is monotone in the class of graph functions: if $V \subseteq V'$ and
$\Omega$ is a graph of class $V$ near $x_0$ at radius $r$, then $\Omega$ is a graph of class
$V'$ near $x_0$ at radius $r$. -/
theorem IsBoundaryGraphAt.mono {V' : Set (EuclideanSpace ℝ (Fin d) → ℝ)} (hV : V ⊆ V')
    {x₀ : EuclideanSpace ℝ (Fin (d + 1))} {r : ℝ} (h : IsBoundaryGraphAt V Ω x₀ r) :
    IsBoundaryGraphAt V' Ω x₀ r :=
  let ⟨T, g, hg, hgraph⟩ := h
  ⟨T, g, hV hg, hgraph⟩

/-- The boundary condition is monotone in the class of graph functions: if $V \subseteq V'$ and the
boundary of $\Omega$ is of class $V$, then it is of class $V'$. -/
theorem IsBoundaryOfClass.mono {V' : Set (EuclideanSpace ℝ (Fin d) → ℝ)} (hV : V ⊆ V')
    (h : IsBoundaryOfClass V Ω) : IsBoundaryOfClass V' Ω :=
  fun x₀ hx₀ ↦ let ⟨r, hr, hgraph⟩ := h x₀ hx₀; ⟨r, hr, hgraph.mono hV⟩

/-- A $C^n$ domain is a $C^m$ domain for every $m \le n$.

This is how a result that has a $C^2$ domain obtains the $C^1$ structure on which the surface
measure is stated. -/
theorem IsContDiffDomain.of_le {m n : WithTop ℕ∞} (hmn : m ≤ n) (h : IsContDiffDomain n Ω) :
    IsContDiffDomain m Ω :=
  ⟨h.isOpen, h.isBoundaryOfClass.mono fun _ hg ↦ ContDiff.of_le hg hmn⟩

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be bounded with boundary of class $V$. Then there are
finitely many points $x_i \in \partial\Omega$ and radii $r_i > 0$ such that $\Omega$ is a graph
of class $V$ near $x_i$ at radius $r_i$ for each $i$, and
$$\partial\Omega \subseteq \bigcup_i B(x_i, r_i).$$
This is the remark after Definition 7.2.1 of [han2009theoretical], and it is the form in which
that definition is used.

The boundary $\partial\Omega$ is compact because $\Omega$ is bounded. The points and the radii
form a finite set of pairs $(x_i, r_i)$. -/
theorem IsBoundaryOfClass.exists_finite_cover (hΩ : Bornology.IsBounded Ω)
    (h : IsBoundaryOfClass V Ω) :
    ∃ s : Finset (EuclideanSpace ℝ (Fin (d + 1)) × ℝ),
      (∀ q ∈ s, q.1 ∈ frontier Ω ∧ 0 < q.2 ∧ IsBoundaryGraphAt V Ω q.1 q.2) ∧
        frontier Ω ⊆ ⋃ q ∈ s, Metric.ball q.1 q.2 := by
  have hc : IsCompact (frontier Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier
      (hΩ.closure.subset frontier_subset_closure)
  set S : Set (EuclideanSpace ℝ (Fin (d + 1)) × ℝ) :=
    {q | q.1 ∈ frontier Ω ∧ 0 < q.2 ∧ IsBoundaryGraphAt V Ω q.1 q.2} with hS
  have hcov : frontier Ω ⊆ ⋃ q ∈ S, Metric.ball q.1 q.2 := fun x hx ↦
    let ⟨r, hr, hgraph⟩ := h x hx
    Set.mem_biUnion (show (x, r) ∈ S from ⟨hx, hr, hgraph⟩) (Metric.mem_ball_self hr)
  obtain ⟨s, hsS, hsfin, hs⟩ := hc.elim_finite_subcover_image (fun q _ ↦ Metric.isOpen_ball) hcov
  exact ⟨hsfin.toFinset, fun q hq ↦ hsS (hsfin.mem_toFinset.1 hq), by
    simpa only [Set.Finite.mem_toFinset] using hs⟩

/-- Let $V$ be a class of functions $\mathbb{R}^d \to \mathbb{R}$ that contains the zero function.
Then the upper half-space $\{x \in \mathbb{R}^{d+1} : x_{d+1} > 0\}$ has boundary of class $V$:
it is the region above the graph of $0$ in the given coordinates.

This fixes the orientation convention of `IsBoundaryGraphAt`: the set lies above the graph. -/
theorem isBoundaryOfClass_upperHalfSpace (hV : (0 : EuclideanSpace ℝ (Fin d) → ℝ) ∈ V) :
    IsBoundaryOfClass V {x : EuclideanSpace ℝ (Fin (d + 1)) | 0 < x (Fin.last d)} := by
  refine fun x₀ _ ↦ ⟨1, one_pos, AffineIsometryEquiv.refl ℝ _, 0, hV, ?_⟩
  ext x
  simp [and_comm]

end Boundary
