/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.Instances.AddCircle.Defs
import Numlib.Analysis.Calculus.Periodic

/-!
# The space $C^k[a, b]$ of continuously differentiable functions on a compact interval

Let $a \le b$ and $k \in \mathbb{N}$. The space $C^k[a, b]$ consists of the $k$ times continuously
differentiable real functions on the compact interval $[a, b]$, with the norm
$$\|u\| = \sum_{j=0}^{k} \|u^{(j)}\|_\infty.$$
It is a Banach space. This module also defines its closed subspace $C^k_0[a, b]$ of the functions
that vanish at both endpoints, and its closed subspace of the functions whose derivatives up to
order $k$ take equal values at the two endpoints, which are the periodic $C^k$ functions read on one
period. The space is defined in [han2009theoretical], §1.4. The norm used here is the one written
(2.1.2) in §2.1 of [han2009theoretical]; §1.4 uses the equivalent norm
$\max_{j \le k} \|u^{(j)}\|_\infty$ instead.

The derivatives at the endpoints are one-sided: $g$ is the derivative of $f$ on $[a, b]$ if $f$ has
the derivative $g(t)$ within $[a, b]$ at every $t \in [a, b]$, the endpoints included. By the
fundamental theorem of calculus this holds if and only if $f(t) = f(a) + \int_a^t g$ for all
$t \in [a, b]$, and this form shows that the condition is closed for the supremum norm.

## Main definitions

* `ContinuousMap.HasDerivIcc`: the continuous function $g$ on $[a, b]$ is the derivative of the
  continuous function $f$ on $[a, b]$, at the two endpoints as well.
* `ContinuousMap.antideriv`: the antiderivative $t \mapsto c + \int_a^t g$ of $g$ on $[a, b]$.
* `ContDiffMapIcc`: the space $C^k[a, b]$. For an element $u$, `ContDiffMapIcc.deriv u j` is the
  $j$-th derivative $u^{(j)}$, `⇑u` is the function $u$ on $[a, b]$, and `ContDiffMapIcc.extend u`
  is $u$ extended to $\mathbb{R}$ by constants.
* `ContDiffMapIcc.shift`, `ContDiffMapIcc.cons`: the differentiation
  $d/dx : C^{k+1}[a, b] \to C^k[a, b]$, and its right inverse that adds the antiderivative with a
  given value at $a$.
* `ContDiffMapIcc.derivCLM`, `ContDiffMapIcc.shiftCLM`: the maps $u \mapsto u^{(j)}$ from
  $C^k[a, b]$ to $C([a, b])$ and $d/dx$ from $C^{k+1}[a, b]$ to $C^k[a, b]$, as bounded linear maps
  of norm at most $1$.
* `ContDiffMapIcc.ofContDiff`, `ContDiffMapIcc.ofContDiffOn`: the element of $C^k[a, b]$ given by a
  function that is $C^k$ on $\mathbb{R}$, or $C^k$ on $[a, b]$.
* `ContDiffMapIcc.zeroBoundary`: the closed subspace $C^k_0[a, b] = \{v \in C^k[a, b] : v(a) =
  v(b) = 0\}$.
* `ContDiffMapIcc.periodicBoundary`: the closed subspace of the $u$ with $u^{(j)}(a) = u^{(j)}(b)$
  for all $j \le k$.

## Main results

* `ContDiffMapIcc.isClosed_submodule` and the instance `CompleteSpace (ContDiffMapIcc hab k)`:
  $C^k[a, b]$ is a Banach space.
* `ContDiffMapIcc.deriv_eq_iteratedDerivWithin`, `ContDiffMapIcc.coe_injective`: for $a < b$, the
  $j$-th derivative of an element is its $j$-th iterated derivative within $[a, b]$, so that an
  element is determined by the function $u$.
* `ContDiffMapIcc.contDiffOn`, `ContDiffMapIcc.ofContDiffOn`: for $a < b$, every element is $C^k$ on
  $[a, b]$, and every function that is $C^k$ on $[a, b]$ gives an element. Thus the space is the
  space of [han2009theoretical], §1.4.
* `ContDiffMapIcc.exists_periodic_contDiff`, `ContDiffMapIcc.ofContDiff_mem_periodicBoundary`: the
  elements of the periodic subspace are exactly the restrictions to $[a, b]$ of the
  $(b - a)$-periodic $C^k$ functions on $\mathbb{R}$.
* `ContinuousMap.hasDerivIcc_iff`: the fundamental theorem of calculus on $[a, b]$, which makes the
  defining condition of $C^k[a, b]$ a closed condition.

## Implementation notes

* An element $u$ is represented by the tuple $(u, u', \dots, u^{(k)})$ of its derivatives, each a
  continuous function on $[a, b]$, with the condition that each entry is the derivative of the entry
  before it on $[a, b]$. The norm $\sum_j \|p_j\|_\infty$ of a tuple $p$ is the norm of
  `PiLp 1 (Fin (k + 1) → C(Icc a b, ℝ))`, which is a Banach space, and $C^k[a, b]$ is a closed
  subspace of it.
* Two other representations do not work. On `{u : ℝ → ℝ // ContDiffOn ℝ k u (Icc a b)}` the
  expression $\sum_{j \le k} \|u^{(j)}\|_\infty$ is only a seminorm, because it does not see the
  values of $u$ outside $[a, b]$; this type would need a quotient. A single function on the subtype
  `Icc a b` would need a differential calculus on that subtype, which Mathlib does not have.
* The closedness does not follow from `hasDerivAt_of_tendstoUniformlyOn` or
  `hasFDerivAt_of_tendstoUniformlyOn`. These need an open set, and so say nothing at the endpoints
  of $[a, b]$. The fundamental theorem of calculus is used instead: $g$ is the derivative of $f$ on
  $[a, b]$ if and only if $f(t) = f(a) + \int_a^t g$, an identity between two continuous functions
  of $(f, g)$ for the supremum norm.
* Mathlib has the case $k = 0$ as `C(X, ℝ)` for compact `X`, and nothing for $k \ge 1$ on a compact
  interval. `ContDiffMapSupportedIn` is a different space: it asks for `ContDiff ℝ n f` on all of
  $\mathbb{R}$ together with `EqOn f 0 Kᶜ`, so that every derivative of a member vanishes at the
  endpoints, and it carries a family of seminorms rather than a norm.
* A continuous function on $[a, b]$ is extended to $\mathbb{R}$ by `ContinuousMap.IccExtend`, which
  is constant outside $[a, b]$. A derivative within $[a, b]$ at a point of $[a, b]$ sees only the
  values on $[a, b]$, so the choice of extension does not matter.
-/
open Set MeasureTheory intervalIntegral

namespace ContinuousMap

variable {a b : ℝ}

/-- Let $a \le b$ and let $f, g$ be continuous real functions on $[a, b]$. The function $g$ is the
**derivative of $f$ on $[a, b]$** if, at every $t \in [a, b]$ including the two endpoints, $f$
has the derivative $g(t)$ within $[a, b]$.

The function $f$ is extended to $\mathbb{R}$ by `ContinuousMap.IccExtend`, which is constant
outside $[a, b]$. A derivative within $[a, b]$ at a point of $[a, b]$ sees only the values on
$[a, b]$, so the choice of extension does not matter. -/
def HasDerivIcc (hab : a ≤ b) (f g : C(Icc a b, ℝ)) : Prop :=
  ∀ t : Icc a b, HasDerivWithinAt (IccExtend hab f) (g t) (Icc a b) t

/-- Let $a \le b$ and $t \in \mathbb{R}$. The map $f \mapsto \int_a^t f(s)\, ds$ on the continuous
functions on $[a, b]$, extended by constants outside $[a, b]$, is a bounded linear functional of
norm at most $|t - a|$.

The extension outside $[a, b]$ is `ContinuousMap.IccExtend`. For $t$ outside $[a, b]$ the
integral uses the constant values $f(a)$ or $f(b)$ there. -/
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

/-- The value of `ContinuousMap.integralIccCLM hab t` at $f$ is $\int_a^t f(s)\, ds$, with $f$
extended by constants outside $[a, b]$. -/
@[simp]
theorem integralIccCLM_apply (hab : a ≤ b) (t : ℝ) (f : C(Icc a b, ℝ)) :
    integralIccCLM hab t f = ∫ s in a..t, IccExtend hab f s :=
  rfl

variable {f g : C(Icc a b, ℝ)}

/-- If $g$ is the derivative of $f$ on $[a, b]$, then $\int_a^t g(s)\, ds = f(t) - f(a)$ for every
$t \in [a, b]$. This is one direction of `ContinuousMap.hasDerivIcc_iff`. -/
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

/-- The **fundamental theorem of calculus on $[a, b]$**. Let $a \le b$ and let $f, g$ be continuous
real functions on $[a, b]$. Then $g$ is the derivative of $f$ on $[a, b]$, endpoints included,
if and only if
$$f(t) = f(a) + \int_a^t g(s)\, ds \qquad \text{for all } t \in [a, b].$$

This is the form used to prove that $C^k[a, b]$ is complete: the right-hand side is a closed
condition on $(f, g)$ for the supremum norm. The integral is `ContinuousMap.integralIccCLM`. -/
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

/-- If $g_1$ is the derivative of $f_1$ and $g_2$ is the derivative of $f_2$ on $[a, b]$, then
$g_1 + g_2$ is the derivative of $f_1 + f_2$ on $[a, b]$. -/
theorem HasDerivIcc.add (hf : HasDerivIcc hab f₁ g₁) (hg : HasDerivIcc hab f₂ g₂) :
    HasDerivIcc hab (f₁ + f₂) (g₁ + g₂) := fun t => by
  have h := (hf t).add (hg t)
  rw [show ((g₁ + g₂) t : ℝ) = g₁ t + g₂ t from rfl]
  exact h

/-- If $g$ is the derivative of $f$ on $[a, b]$ and $c \in \mathbb{R}$, then $c g$ is the derivative
of $c f$ on $[a, b]$. -/
theorem HasDerivIcc.smul (c : ℝ) (hf : HasDerivIcc hab f₁ g₁) :
    HasDerivIcc hab (c • f₁) (c • g₁) := fun t => by
  have h := (hf t).const_smul c
  rw [show ((c • g₁) t : ℝ) = c • g₁ t from rfl]
  exact h

/-- The zero function is the derivative of the zero function on $[a, b]$. -/
theorem hasDerivIcc_zero (hab : a ≤ b) : HasDerivIcc hab (0 : C(Icc a b, ℝ)) 0 := fun t => by
  rw [show ((0 : C(Icc a b, ℝ)) t : ℝ) = 0 from rfl]
  exact (hasDerivWithinAt_const _ _ (0 : ℝ))

/-- Let $a \le b$, let $g$ be a continuous real function on $[a, b]$, and let $c \in \mathbb{R}$.
The **antiderivative** of $g$ with value $c$ at $a$ is the continuous function
$t \mapsto c + \int_a^t g(s)\, ds$ on $[a, b]$.

It is the unique continuous function on $[a, b]$ with value $c$ at $a$ whose derivative on
$[a, b]$ is $g$, by `ContinuousMap.hasDerivIcc_antideriv` and
`ContinuousMap.HasDerivIcc.eq_antideriv`. -/
noncomputable def antideriv (hab : a ≤ b) (g : C(Icc a b, ℝ)) (c : ℝ) : C(Icc a b, ℝ) where
  toFun t := c + ∫ s in a..(t : ℝ), IccExtend hab g s
  continuous_toFun := by
    have h : Continuous fun t : ℝ => c + ∫ s in a..t, IccExtend hab g s :=
      continuous_const.add (continuous_iff_continuousAt.2 fun t =>
        (((IccExtend hab g).continuous.integral_hasStrictDerivAt a t).hasDerivAt).continuousAt)
    exact h.comp continuous_subtype_val

/-- The value of the antiderivative at $t \in [a, b]$ is $c + \int_a^t g(s)\, ds$. -/
@[simp]
theorem antideriv_apply (hab : a ≤ b) (g : C(Icc a b, ℝ)) (c : ℝ) (t : Icc a b) :
    antideriv hab g c t = c + ∫ s in a..(t : ℝ), IccExtend hab g s := rfl

/-- The antiderivative with value $c$ at $a$ has the value $c$ at $a$. -/
@[simp]
theorem antideriv_left (hab : a ≤ b) (g : C(Icc a b, ℝ)) (c : ℝ) :
    antideriv hab g c ⟨a, left_mem_Icc.2 hab⟩ = c := by
  simp

/-- The **fundamental theorem of calculus on $[a, b]$**, existence. Let $a \le b$, let $g$ be a
continuous real function on $[a, b]$, and let $c \in \mathbb{R}$. Then $g$ is the derivative on
$[a, b]$, endpoints included, of its antiderivative $t \mapsto c + \int_a^t g(s)\, ds$. -/
theorem hasDerivIcc_antideriv (hab : a ≤ b) (g : C(Icc a b, ℝ)) (c : ℝ) :
    HasDerivIcc hab (antideriv hab g c) g := by
  rw [hasDerivIcc_iff]
  intro t
  simp

/-- Let $a \le b$, and let $g$ be the derivative of $f$ on $[a, b]$. Then $f$ is the antiderivative
of $g$ with value $f(a)$ at $a$:
$$f(t) = f(a) + \int_a^t g(s)\, ds \qquad \text{for all } t \in [a, b].$$
In particular, a function on $[a, b]$ is determined by its derivative and its value at $a$. -/
theorem HasDerivIcc.eq_antideriv {hab : a ≤ b} {f g : C(Icc a b, ℝ)} (h : HasDerivIcc hab f g) :
    f = antideriv hab g (f ⟨a, left_mem_Icc.2 hab⟩) := by
  ext t
  rw [antideriv_apply, ← integralIccCLM_apply]
  exact (hasDerivIcc_iff hab).1 h t

/-- For every $c \in \mathbb{R}$, the zero function is the derivative of the constant function $c$
on $[a, b]$. -/
theorem hasDerivIcc_const (hab : a ≤ b) (c : ℝ) :
    HasDerivIcc hab (ContinuousMap.const (Icc a b) c) 0 := fun t => by
  rw [show ((0 : C(Icc a b, ℝ)) t : ℝ) = 0 from rfl]
  exact hasDerivWithinAt_const _ _ _

/-- Let $a < b$. If $g_1$ and $g_2$ are both derivatives of $f$ on $[a, b]$, then $g_1 = g_2$. -/
theorem HasDerivIcc.unique {hab : a ≤ b} (hlt : a < b) {f g₁ g₂ : C(Icc a b, ℝ)}
    (h₁ : HasDerivIcc hab f g₁) (h₂ : HasDerivIcc hab f g₂) : g₁ = g₂ := by
  ext t
  exact (uniqueDiffOn_Icc hlt t t.2).eq_deriv _ (h₁ t) (h₂ t)

end ContinuousMap

open ContinuousMap

variable {a b : ℝ}

/-- The submodule of `PiLp 1 (Fin (k + 1) → C(Icc a b, ℝ))` of the tuples $(p_0, \dots, p_k)$ of
continuous functions on $[a, b]$ in which $p_{j+1}$ is the derivative of $p_j$ on $[a, b]$ for
each $j < k$. The ambient space carries the norm $\sum_j \|p_j\|_\infty$. This submodule is the
carrier of `ContDiffMapIcc`. -/
def ContDiffMapIcc.submodule (hab : a ≤ b) (k : ℕ) :
    Submodule ℝ (PiLp 1 fun _ : Fin (k + 1) => C(Icc a b, ℝ)) where
  carrier := {p | ∀ j : Fin k, HasDerivIcc hab (p j.castSucc) (p j.succ)}
  add_mem' hp hq j := (hp j).add (hq j)
  zero_mem' _ := hasDerivIcc_zero hab
  smul_mem' c _ hp j := (hp j).smul c

/-- Let $a \le b$ and $k \in \mathbb{N}$. The space **$C^k[a, b]$** consists of the $k$ times
continuously differentiable real functions on the compact interval $[a, b]$, with the norm
$$\|u\| = \sum_{j=0}^{k} \|u^{(j)}\|_\infty.$$
It is a Banach space. This is the space of [han2009theoretical], §1.4.

An element is represented by the tuple $(u, u', \dots, u^{(k)})$ of its derivatives, each a
continuous function on $[a, b]$, with the condition that each entry is the derivative of the
entry before it on $[a, b]$, endpoints included (`ContinuousMap.HasDerivIcc`). On
`{u : ℝ → ℝ // ContDiffOn ℝ k u (Icc a b)}` the expression $\sum_{j \le k} \|u^{(j)}\|_\infty$
would be only a seminorm, because it does not see the values of $u$ outside $[a, b]$. With the
tuple, the norm is a norm, and the space is a closed subspace of a finite product of copies of
$C([a, b])$, hence complete. `ContDiffMapIcc.deriv u j` is the $j$-th entry, and `⇑u` is the
function $u$ itself. For $a < b$, `ContDiffMapIcc.deriv_eq_iteratedDerivWithin` identifies the
$j$-th entry with `iteratedDerivWithin j u (Icc a b)`. -/
def ContDiffMapIcc (hab : a ≤ b) (k : ℕ) : Type := ContDiffMapIcc.submodule hab k

namespace ContDiffMapIcc

variable {hab : a ≤ b} {k : ℕ}

noncomputable instance : NormedAddCommGroup (ContDiffMapIcc hab k) :=
  inferInstanceAs (NormedAddCommGroup (submodule hab k))

noncomputable instance : NormedSpace ℝ (ContDiffMapIcc hab k) :=
  inferInstanceAs (NormedSpace ℝ (submodule hab k))

/-- The $j$-th derivative $u^{(j)}$ of $u \in C^k[a, b]$, for $j \le k$, as a continuous function on
$[a, b]$. For $j = 0$ it is $u$ itself. -/
def deriv (u : ContDiffMapIcc hab k) (j : Fin (k + 1)) : C(Icc a b, ℝ) := u.1 j

/-- Every $u \in C^k[a, b]$ is a function on $[a, b]$, namely its zeroth derivative $u^{(0)}$. -/
instance : CoeFun (ContDiffMapIcc hab k) fun _ => Icc a b → ℝ := ⟨fun u => u.deriv 0⟩

/-- The function $u$ on $[a, b]$ of $u \in C^k[a, b]$ is its zeroth derivative $u^{(0)}$. -/
theorem coe_def (u : ContDiffMapIcc hab k) : ⇑u = ⇑(u.deriv 0) := rfl

/-- The element $u \in C^k[a, b]$ as a continuous function on all of $\mathbb{R}$, constant outside
$[a, b]$.

Statements about the calculus of $u$ use this extension. A derivative within $[a, b]$ at a point
of $[a, b]$ does not see the values outside $[a, b]$, so no statement depends on the choice of
extension. -/
noncomputable def extend (u : ContDiffMapIcc hab k) : C(ℝ, ℝ) :=
  ContinuousMap.IccExtend hab (u.deriv 0)

/-- On $[a, b]$, the extension of $u \in C^k[a, b]$ to $\mathbb{R}$ agrees with $u$. -/
@[simp]
theorem extend_val (u : ContDiffMapIcc hab k) (t : Icc a b) : u.extend t = u t :=
  Set.IccExtend_val hab _ t

/-- For $t \in [a, b]$, the extension of $u \in C^k[a, b]$ to $\mathbb{R}$ takes the value $u(t)$ at
$t$. -/
theorem extend_of_mem (u : ContDiffMapIcc hab k) {t : ℝ} (ht : t ∈ Icc a b) :
    u.extend t = u ⟨t, ht⟩ :=
  Set.IccExtend_of_mem hab _ ht

/-- For $u \in C^k[a, b]$ and $j < k$, the derivative $u^{(j+1)}$ is the derivative of $u^{(j)}$ on
$[a, b]$, endpoints included. -/
theorem hasDerivIcc (u : ContDiffMapIcc hab k) (j : Fin k) :
    HasDerivIcc hab (u.deriv j.castSucc) (u.deriv j.succ) := u.2 j

/-- Two elements of $C^k[a, b]$ are equal if their $j$-th derivatives are equal for every $j \le k$.
-/
@[ext]
theorem ext {u v : ContDiffMapIcc hab k} (h : ∀ j, u.deriv j = v.deriv j) : u = v :=
  Subtype.ext ((WithLp.ext_iff 1).2 (funext h))

/-- The $j$-th derivative of $u + v$ is $u^{(j)} + v^{(j)}$. -/
@[simp]
theorem deriv_add (u v : ContDiffMapIcc hab k) (j : Fin (k + 1)) :
    (u + v).deriv j = u.deriv j + v.deriv j := rfl

/-- The $j$-th derivative of $c u$ is $c u^{(j)}$. -/
@[simp]
theorem deriv_smul (c : ℝ) (u : ContDiffMapIcc hab k) (j : Fin (k + 1)) :
    (c • u).deriv j = c • u.deriv j := rfl

/-- Every derivative of the zero element of $C^k[a, b]$ is zero. -/
@[simp]
theorem deriv_zero (j : Fin (k + 1)) : (0 : ContDiffMapIcc hab k).deriv j = 0 := rfl

/-- The $j$-th derivative of $u - v$ is $u^{(j)} - v^{(j)}$. -/
@[simp]
theorem deriv_sub (u v : ContDiffMapIcc hab k) (j : Fin (k + 1)) :
    (u - v).deriv j = u.deriv j - v.deriv j := rfl

/-- The norm of $u \in C^k[a, b]$ is $\|u\| = \sum_{j=0}^{k} \|u^{(j)}\|_\infty$, where
$\|\cdot\|_\infty$ is the supremum norm on $[a, b]$. -/
theorem norm_def (u : ContDiffMapIcc hab k) : ‖u‖ = ∑ j, ‖u.deriv j‖ := by
  have h : ‖u‖ = ‖(u.1 : PiLp 1 fun _ : Fin (k + 1) => C(Icc a b, ℝ))‖ := rfl
  rw [h, PiLp.norm_eq_of_L1]
  rfl

/-- For $u \in C^k[a, b]$ and $j \le k$, $\|u^{(j)}\|_\infty \le \|u\|$. -/
theorem norm_deriv_le (u : ContDiffMapIcc hab k) (j : Fin (k + 1)) : ‖u.deriv j‖ ≤ ‖u‖ := by
  rw [norm_def]
  exact Finset.single_le_sum (f := fun i => ‖u.deriv i‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ j)

/-- For $a \le b$ and $k \in \mathbb{N}$, the set of tuples $(p_0, \dots, p_k)$ of continuous
functions on $[a, b]$ in which each $p_{j+1}$ is the derivative of $p_j$ on $[a, b]$ is closed
in the product space with the norm $\sum_j \|p_j\|_\infty$.

By the fundamental theorem of calculus (`ContinuousMap.hasDerivIcc_iff`), the condition says
that each entry is the integral of the next, and both sides of this identity are continuous for
the supremum norm. Mathlib's `hasDerivAt_of_tendstoUniformlyOn` is not used, because it needs an
open set and so says nothing at the endpoints of $[a, b]$. This closedness gives the
completeness of $C^k[a, b]$. -/
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

/-- The space $C^k[a, b]$ is a Banach space ([han2009theoretical], §1.4). It is a closed subspace of
a finite product of copies of the Banach space $C([a, b])$. -/
instance : CompleteSpace (ContDiffMapIcc hab k) := by
  have : IsClosed (submodule hab k : Set (PiLp 1 fun _ : Fin (k + 1) => C(Icc a b, ℝ))) :=
    isClosed_submodule hab k
  exact inferInstanceAs (CompleteSpace (submodule hab k))

/-- The element of $C^k[a, b]$ given by the tuple of its derivatives: continuous functions
$p_0, \dots, p_k$ on $[a, b]$ such that $p_{j+1}$ is the derivative of $p_j$ on $[a, b]$ for
each $j < k$. -/
def mk (hab : a ≤ b) {k : ℕ} (p : Fin (k + 1) → C(Icc a b, ℝ))
    (hp : ∀ j : Fin k, HasDerivIcc hab (p j.castSucc) (p j.succ)) : ContDiffMapIcc hab k :=
  ⟨WithLp.toLp 1 p, hp⟩

/-- The $j$-th derivative of the element built from the tuple $(p_0, \dots, p_k)$ is $p_j$. -/
@[simp]
theorem deriv_mk (hab : a ≤ b) {k : ℕ} (p : Fin (k + 1) → C(Icc a b, ℝ))
    (hp : ∀ j : Fin k, HasDerivIcc hab (p j.castSucc) (p j.succ)) (j : Fin (k + 1)) :
    (mk hab p hp).deriv j = p j := rfl

/-- For $j \le k$, the map $u \mapsto u^{(j)}$ from $C^k[a, b]$ to $C([a, b])$, as a bounded linear
map of norm at most $1$. -/
noncomputable def derivCLM (hab : a ≤ b) (k : ℕ) (j : Fin (k + 1)) :
    ContDiffMapIcc hab k →L[ℝ] C(Icc a b, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun u => u.deriv j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    1 fun u => (norm_deriv_le u j).trans_eq (one_mul _).symm

/-- The map `ContDiffMapIcc.derivCLM hab k j` sends $u$ to $u^{(j)}$. -/
@[simp]
theorem derivCLM_apply (hab : a ≤ b) (k : ℕ) (j : Fin (k + 1)) (u : ContDiffMapIcc hab k) :
    derivCLM hab k j u = u.deriv j := rfl

/-- **Differentiation** $d/dx : C^{k+1}[a, b] \to C^k[a, b]$, which sends $u$ to $u'$. On the tuple
of derivatives it drops the zeroth entry. -/
def shift (u : ContDiffMapIcc hab (k + 1)) : ContDiffMapIcc hab k :=
  mk hab (fun j => u.deriv j.succ) fun j => by
    have h := u.hasDerivIcc j.succ
    rwa [← Fin.succ_castSucc] at h

/-- For $u \in C^{k+1}[a, b]$ and $j \le k$, the $j$-th derivative of $u'$ is $u^{(j+1)}$. -/
@[simp]
theorem deriv_shift (u : ContDiffMapIcc hab (k + 1)) (j : Fin (k + 1)) :
    (shift u).deriv j = u.deriv j.succ := rfl

/-- Differentiation $d/dx : C^{k+1}[a, b] \to C^k[a, b]$ as a bounded linear map of norm at most
$1$. -/
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

/-- The map `ContDiffMapIcc.shiftCLM hab k` is `ContDiffMapIcc.shift`. -/
@[simp]
theorem shiftCLM_apply (hab : a ≤ b) (k : ℕ) (u : ContDiffMapIcc hab (k + 1)) :
    shiftCLM hab k u = shift u := rfl

/-- Let $a < b$ and $u \in C^k[a, b]$. Then for every $j \le k$ and $t \in [a, b]$, the $j$-th
derivative $u^{(j)}(t)$ is the $j$-th iterated derivative within $[a, b]$ at $t$ of the
extension of $u$ to $\mathbb{R}$.

This makes the representation faithful: the higher entries of the tuple are determined by the
zeroth, so $C^k[a, b]$ is a space of functions. The hypothesis $a < b$ is needed, because a
derivative within a one-point set is not determined. The iterated derivative is
`iteratedDerivWithin j u.extend (Icc a b)`. -/
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

/-- For $u \in C^{k+1}[a, b]$ and $t \in [a, b]$, the extension of $u$ to $\mathbb{R}$ has the
derivative $u'(t)$ within $[a, b]$ at $t$, endpoints included. -/
theorem hasDerivWithinAt_extend (u : ContDiffMapIcc hab (k + 1)) (t : Icc a b) :
    HasDerivWithinAt u.extend (u.deriv 1 t) (Icc a b) t := by
  have h := u.hasDerivIcc 0 t
  rwa [show (0 : Fin (k + 1)).castSucc = 0 from rfl,
    show (0 : Fin (k + 1)).succ = 1 from rfl] at h

/-- Let $a < b$. Every $u \in C^k[a, b]$ is $k$ times continuously differentiable on $[a, b]$, which
is the definition of the space in [han2009theoretical], §1.4.

The statement is `ContDiffOn ℝ k` on `Icc a b` for the extension of $u$ to $\mathbb{R}$. -/
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

/-- For $t \in [a, b]$, $(u + v)(t) = u(t) + v(t)$. -/
@[simp]
theorem coe_add (u v : ContDiffMapIcc hab k) (t : Icc a b) : (u + v) t = u t + v t := rfl

/-- For $t \in [a, b]$, $(c u)(t) = c\, u(t)$. -/
@[simp]
theorem coe_smul (c : ℝ) (u : ContDiffMapIcc hab k) (t : Icc a b) : (c • u) t = c * u t := rfl

/-- The zero element of $C^k[a, b]$ is the zero function. -/
@[simp]
theorem coe_zero (t : Icc a b) : (0 : ContDiffMapIcc hab k) t = 0 := rfl

/-- For $u \in C^k[a, b]$, $\max_{j \le k} \|u^{(j)}\|_\infty \le \|u\|$. This is one half of the
equivalence between the norm $\sum_{j \le k} \|u^{(j)}\|_\infty$ used here and the norm
$\max_{j \le k} \|u^{(j)}\|_\infty$ of [han2009theoretical], §1.4. -/
theorem iSup_norm_deriv_le_norm (u : ContDiffMapIcc hab k) : ⨆ j, ‖u.deriv j‖ ≤ ‖u‖ :=
  ciSup_le fun j => norm_deriv_le u j

/-- For $u \in C^k[a, b]$, $\|u\| \le (k + 1) \max_{j \le k} \|u^{(j)}\|_\infty$. This is the other
half of the equivalence with the norm $\max_{j \le k} \|u^{(j)}\|_\infty$ of
[han2009theoretical], §1.4: a sum of $k + 1$ terms is at most $k + 1$ times the largest. -/
theorem norm_le_iSup_norm_deriv (u : ContDiffMapIcc hab k) :
    ‖u‖ ≤ (k + 1) * ⨆ j, ‖u.deriv j‖ := by
  rw [norm_def]
  calc ∑ j, ‖u.deriv j‖ ≤ ∑ _j : Fin (k + 1), ⨆ i, ‖u.deriv i‖ :=
        Finset.sum_le_sum fun j _ =>
          le_ciSup (f := fun i => ‖u.deriv i‖) (Finite.bddAbove_range _) j
    _ = (k + 1) * ⨆ j, ‖u.deriv j‖ := by simp [Finset.sum_const]

/-- A continuous function $f$ on $[a, b]$ as an element of $C^0[a, b]$. A tuple of length one
carries no condition, so $C^0[a, b]$ is $C([a, b])$. -/
def ofContinuousMap (hab : a ≤ b) (f : C(Icc a b, ℝ)) : ContDiffMapIcc hab 0 :=
  mk hab (fun _ => f) fun j => j.elim0

/-- The zeroth derivative of the element of $C^0[a, b]$ given by $f$ is $f$. -/
@[simp]
theorem deriv_ofContinuousMap (hab : a ≤ b) (f : C(Icc a b, ℝ)) (j : Fin 1) :
    (ofContinuousMap hab f).deriv j = f := rfl

/-- Every $u \in C^0[a, b]$ is the element given by the continuous function $u^{(0)}$. -/
theorem ofContinuousMap_deriv (u : ContDiffMapIcc hab 0) : ofContinuousMap hab (u.deriv 0) = u :=
  ext fun j => by rw [Fin.fin_one_eq_zero j]; rfl

/-- Let $a < b$. An element $u \in C^k[a, b]$ is determined by the function $u$ on $[a, b]$: the map
$u \mapsto u$ from $C^k[a, b]$ to the functions on $[a, b]$ is injective. The higher entries of
the tuple are the iterated derivatives of $u$. -/
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

/-- Let $a < b$, and let $f : \mathbb{R} \to \mathbb{R}$ be $k$ times continuously differentiable on
$[a, b]$. Then $f$ gives an element of $C^k[a, b]$, whose $j$-th derivative is the $j$-th
iterated derivative of $f$ within $[a, b]$.

With `ContDiffMapIcc.contDiffOn`, this shows that $C^k[a, b]$ is exactly the space of
[han2009theoretical], §1.4. The hypothesis "$C^k$ on $[a, b]$" is `ContDiffOn ℝ k f (Icc a b)`,
and the derivatives are `iteratedDerivWithin j f (Icc a b)`. -/
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

/-- For the element of $C^k[a, b]$ given by a function $f$ that is $C^k$ on $[a, b]$, the $j$-th
derivative at $t$ is the $j$-th iterated derivative of $f$ within $[a, b]$ at $t$. -/
@[simp]
theorem deriv_ofContDiffOn (hab : a ≤ b) (hlt : a < b) {k : ℕ} {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ k f (Icc a b)) (j : Fin (k + 1)) (t : Icc a b) :
    (ofContDiffOn hab hlt hf).deriv j t = iteratedDerivWithin j f (Icc a b) t := rfl

/-- The element of $C^k[a, b]$ given by a function $f$ that is $C^k$ on $[a, b]$ takes the value
$f(t)$ at $t \in [a, b]$. -/
@[simp]
theorem coe_ofContDiffOn (hab : a ≤ b) (hlt : a < b) {k : ℕ} {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ k f (Icc a b)) (t : Icc a b) : ofContDiffOn hab hlt hf t = f t := rfl

/-- For $u \in C^k[a, b]$ and $c \in \mathbb{R}$, the element of $C^{k+1}[a, b]$ whose derivative is
$u$ and whose value at $a$ is $c$: its zeroth entry is $t \mapsto c + \int_a^t u(s)\, ds$.

With `ContDiffMapIcc.shift`, it identifies $C^{k+1}[a, b]$ with $C^k[a, b] \times \mathbb{R}$
(`ContDiffMapIcc.shift_cons`, `ContDiffMapIcc.cons_shift`). -/
noncomputable def cons (u : ContDiffMapIcc hab k) (c : ℝ) : ContDiffMapIcc hab (k + 1) :=
  mk hab (Fin.cons (antideriv hab (u.deriv 0) c) u.deriv) fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hasDerivIcc_antideriv hab (u.deriv 0) c
    · simpa [← Fin.succ_castSucc] using u.hasDerivIcc j

/-- The zeroth derivative of `ContDiffMapIcc.cons u c` is the antiderivative of $u$ with value $c$
at $a$. -/
@[simp]
theorem deriv_cons_zero (u : ContDiffMapIcc hab k) (c : ℝ) :
    (cons u c).deriv 0 = antideriv hab (u.deriv 0) c := rfl

/-- The $(j+1)$-th derivative of `ContDiffMapIcc.cons u c` is $u^{(j)}$. -/
@[simp]
theorem deriv_cons_succ (u : ContDiffMapIcc hab k) (c : ℝ) (j : Fin (k + 1)) :
    (cons u c).deriv j.succ = u.deriv j := rfl

/-- The derivative of `ContDiffMapIcc.cons u c` is $u$. -/
@[simp]
theorem shift_cons (u : ContDiffMapIcc hab k) (c : ℝ) : shift (cons u c) = u := by
  ext j; rfl

/-- The value of `ContDiffMapIcc.cons u c` at $a$ is $c$. -/
@[simp]
theorem cons_left (u : ContDiffMapIcc hab k) (c : ℝ) :
    cons u c ⟨a, left_mem_Icc.2 hab⟩ = c := antideriv_left hab _ c

/-- For $v \in C^{k+1}[a, b]$, the element built from the derivative $v'$ and the value $v(a)$ is
$v$. With `ContDiffMapIcc.shift_cons`, this identifies $C^{k+1}[a, b]$ with
$C^k[a, b] \times \mathbb{R}$. -/
theorem cons_shift (v : ContDiffMapIcc hab (k + 1)) :
    cons (shift v) (v ⟨a, left_mem_Icc.2 hab⟩) = v := by
  refine ext fun j => ?_
  refine Fin.cases ?_ (fun _ => rfl) j
  have h := (v.hasDerivIcc 0).eq_antideriv
  rw [show (0 : Fin (k + 1)).castSucc = 0 from rfl,
    show (0 : Fin (k + 1)).succ = 1 from rfl] at h
  exact h.symm

/-- For $j \le k$ and $t \in [a, b]$, the map $u \mapsto u^{(j)}(t)$ is continuous on $C^k[a, b]$.

The closedness of `ContDiffMapIcc.zeroBoundary` and of `ContDiffMapIcc.periodicBoundary` both
rest on this: both subspaces are defined by equations between such evaluations. -/
theorem continuous_deriv_eval (hab : a ≤ b) (k : ℕ) (j : Fin (k + 1)) (t : Icc a b) :
    Continuous fun u : ContDiffMapIcc hab k => u.deriv j t :=
  (continuous_eval_const t).comp (derivCLM hab k j).continuous

/-- For $t \in [a, b]$, the evaluation $u \mapsto u(t)$ is continuous on $C^k[a, b]$. -/
theorem continuous_eval (hab : a ≤ b) (k : ℕ) (t : Icc a b) :
    Continuous fun u : ContDiffMapIcc hab k => u t :=
  continuous_deriv_eval hab k 0 t

/-- The subspace $C^k_0[a, b] = \{v \in C^k[a, b] : v(a) = v(b) = 0\}$ of the elements that vanish
at both endpoints.

For $k = 2$ on $[0, 1]$, this is the space $C^2_0[0, 1]$ in which [han2009theoretical], §5.4.2,
poses the two-point boundary value problem $u'' = f(t, u)$, $u(0) = u(1) = 0$. -/
def zeroBoundary (hab : a ≤ b) (k : ℕ) : Submodule ℝ (ContDiffMapIcc hab k) where
  carrier := {u | u ⟨a, left_mem_Icc.2 hab⟩ = 0 ∧ u ⟨b, right_mem_Icc.2 hab⟩ = 0}
  add_mem' hu hv := ⟨by simp [hu.1, hv.1], by simp [hu.2, hv.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' c _ hu := ⟨by simp [hu.1], by simp [hu.2]⟩

/-- An element $u \in C^k[a, b]$ is in $C^k_0[a, b]$ if and only if $u(a) = 0$ and $u(b) = 0$. -/
@[simp]
theorem mem_zeroBoundary {u : ContDiffMapIcc hab k} :
    u ∈ zeroBoundary hab k ↔
      u ⟨a, left_mem_Icc.2 hab⟩ = 0 ∧ u ⟨b, right_mem_Icc.2 hab⟩ = 0 := Iff.rfl

/-- The subspace $C^k_0[a, b]$ is closed in $C^k[a, b]$, since it is defined by two continuous
conditions. -/
theorem isClosed_zeroBoundary (hab : a ≤ b) (k : ℕ) :
    IsClosed (zeroBoundary hab k : Set (ContDiffMapIcc hab k)) := by
  have hset : (zeroBoundary hab k : Set (ContDiffMapIcc hab k)) =
      {u : ContDiffMapIcc hab k | u ⟨a, left_mem_Icc.2 hab⟩ = 0} ∩
        {u : ContDiffMapIcc hab k | u ⟨b, right_mem_Icc.2 hab⟩ = 0} := rfl
  rw [hset]
  exact (isClosed_eq (continuous_eval hab k _) continuous_const).inter
    (isClosed_eq (continuous_eval hab k _) continuous_const)

/-- The space $C^k_0[a, b]$ is a Banach space, as a closed subspace of a Banach space. -/
instance : CompleteSpace (zeroBoundary hab k) := by
  have : IsClosed (zeroBoundary hab k : Set (ContDiffMapIcc hab k)) := isClosed_zeroBoundary hab k
  infer_instance

/-! ### Periodic boundary conditions -/

/-- The subspace of $C^k[a, b]$ of the elements $u$ whose derivatives up to order $k$ take equal
values at the two endpoints: $u^{(j)}(a) = u^{(j)}(b)$ for all $j \le k$.

Its elements are exactly the restrictions to one period of the $(b - a)$-periodic functions of
class $C^k$ on $\mathbb{R}$, the space that [han2009theoretical], §1.2, writes $C_p^k(T)$. One
direction is `ContDiffMapIcc.exists_periodic_contDiff` and the other is
`ContDiffMapIcc.ofContDiff_mem_periodicBoundary`. The periodic extension is $C^k$, and not only
continuous, because all derivatives up to order $k$ match, not only the values.

For $k = 0$ this agrees with the reading of $C_p(T)$ as `C(AddCircle T, ℝ)`: a continuous
function on the circle is the same as a continuous function on $[a, b]$ with equal values at the
two ends. There is no circle version for higher orders here, because Mathlib has no differential
calculus on `AddCircle`. -/
def periodicBoundary (hab : a ≤ b) (k : ℕ) : Submodule ℝ (ContDiffMapIcc hab k) where
  carrier := {u | ∀ j, u.deriv j ⟨a, left_mem_Icc.2 hab⟩ = u.deriv j ⟨b, right_mem_Icc.2 hab⟩}
  add_mem' hu hv j := by simp [hu j, hv j]
  zero_mem' _ := rfl
  smul_mem' c _ hu j := by simp [hu j]

/-- An element $u \in C^k[a, b]$ satisfies the periodic boundary conditions if and only if
$u^{(j)}(a) = u^{(j)}(b)$ for all $j \le k$. -/
@[simp]
theorem mem_periodicBoundary {u : ContDiffMapIcc hab k} :
    u ∈ periodicBoundary hab k ↔
      ∀ j, u.deriv j ⟨a, left_mem_Icc.2 hab⟩ = u.deriv j ⟨b, right_mem_Icc.2 hab⟩ := Iff.rfl

/-- The subspace of $C^k[a, b]$ defined by the periodic boundary conditions is closed. As for
`ContDiffMapIcc.zeroBoundary`, it is defined by equations between evaluations of derivatives,
and each evaluation is continuous by `ContDiffMapIcc.continuous_deriv_eval`. -/
theorem isClosed_periodicBoundary (hab : a ≤ b) (k : ℕ) :
    IsClosed (periodicBoundary hab k : Set (ContDiffMapIcc hab k)) := by
  have hset : (periodicBoundary hab k : Set (ContDiffMapIcc hab k)) =
      ⋂ j : Fin (k + 1), {u : ContDiffMapIcc hab k |
        u.deriv j ⟨a, left_mem_Icc.2 hab⟩ = u.deriv j ⟨b, right_mem_Icc.2 hab⟩} := by
    ext u; simp [Set.mem_iInter]
  rw [hset]
  exact isClosed_iInter fun j =>
    isClosed_eq (continuous_deriv_eval hab k j _) (continuous_deriv_eval hab k j _)

/-- The periodic $C^k$ functions on $[a, b]$ form a Banach space, as a closed subspace of the Banach
space $C^k[a, b]$. -/
instance : CompleteSpace (periodicBoundary hab k) := by
  have : IsClosed (periodicBoundary hab k : Set (ContDiffMapIcc hab k)) :=
    isClosed_periodicBoundary hab k
  infer_instance

/-- Let $a \le b$, and let $f : \mathbb{R} \to \mathbb{R}$ be $k$ times continuously differentiable
on $\mathbb{R}$. The restriction of $f$ to $[a, b]$ as an element of $C^k[a, b]$, whose $j$-th
derivative is the restriction of $f^{(j)}$.

Unlike `ContDiffMapIcc.ofContDiffOn`, this needs no hypothesis $a < b$, because the derivatives
are the global derivatives `iteratedDeriv j f` and not derivatives within $[a, b]$. -/
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

/-- The $j$-th derivative at $t \in [a, b]$ of the restriction of a $C^k$ function $f$ on
$\mathbb{R}$ is $f^{(j)}(t)$. -/
@[simp]
theorem deriv_ofContDiff (hab : a ≤ b) {k : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ k f)
    (j : Fin (k + 1)) (t : Icc a b) :
    (ofContDiff hab hf).deriv j t = iteratedDeriv j f t := rfl

/-- The restriction of a $C^k$ function $f$ on $\mathbb{R}$ to $[a, b]$ takes the value $f(t)$ at
$t \in [a, b]$. -/
@[simp]
theorem coe_ofContDiff (hab : a ≤ b) {k : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ k f) (t : Icc a b) :
    ofContDiff hab hf t = f t := rfl

/-- Let $a \le b$, and let $f : \mathbb{R} \to \mathbb{R}$ be $C^k$ and $(b - a)$-periodic. Then the
restriction of $f$ to $[a, b]$ satisfies the periodic boundary conditions
$f^{(j)}(a) = f^{(j)}(b)$ for $j \le k$.

With `ContDiffMapIcc.exists_periodic_contDiff`, this identifies
`ContDiffMapIcc.periodicBoundary` with the periodic $C^k$ functions. -/
theorem ofContDiff_mem_periodicBoundary (hab : a ≤ b) {k : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ k f)
    (hper : Function.Periodic f (b - a)) : ofContDiff hab hf ∈ periodicBoundary hab k := by
  intro j
  have h := hper.iteratedDeriv j a
  simp only [deriv_ofContDiff]
  rw [show a + (b - a) = b by ring] at h
  exact h.symm

/-- Let $a < b$ and let $u \in C^k[a, b]$ satisfy the periodic boundary conditions
$u^{(j)}(a) = u^{(j)}(b)$ for $j \le k$. Then there is a $(b - a)$-periodic function
$f : \mathbb{R} \to \mathbb{R}$ of class $C^k$ with $f(t) = u(t)$ for all $t \in [a, b]$. This
is the converse of `ContDiffMapIcc.ofContDiff_mem_periodicBoundary`; together they say that the
periodic boundary conditions describe exactly the periodic $C^k$ functions read on one period.

The extension is built by integration from the top derivative down, and not by gluing
translates, so no theorem about $C^k$ functions glued at a point is needed. The top derivative
$u^{(k)}$ is extended periodically as a continuous function, which needs only that its two
endpoint values agree. Each lower derivative is then recovered as
$x \mapsto u^{(j)}(a) + \int_a^x \tilde u_{j+1}$, where $\tilde u_{j+1}$ is the extension of
$u^{(j+1)}$. This function is one degree smoother, and it is periodic because the integral of
$\tilde u_{j+1}$ over one period is $u^{(j)}(b) - u^{(j)}(a) = 0$. Thus the matching at order
$j$ makes the extension of $u^{(j)}$ periodic, and each matching condition up to order $k$ is
used once. -/
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
