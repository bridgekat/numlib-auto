/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas`, beside the one-variable iterated
derivative.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Iterated partial derivatives of a function of two real variables

A function $v$ of two real variables, written in curried form $v \colon \mathbb{R} \to \mathbb{R}
\to \mathbb{R}$, has a partial derivative in each argument. The predicate `HasPartialDerivFst v vx`
says that for every $(x, t)$ the function $y \mapsto v(y, t)$ has the derivative $v_x(x, t)$ at $x$.
The predicate `HasPartialDerivSnd v vt` says the same for $s \mapsto v(x, s)$ and $v_t(x, t)$.
Neither predicate asks for differentiability of $v$ as a function on $\mathbb{R}^2$. Only the
restrictions of $v$ to the coordinate lines enter, and the results below use nothing more.

The predicate `HasPartialDerivs v D` names a whole doubly indexed family of partial derivatives:
$D_{ij}$ stands for $\partial_x^i \partial_t^j v$, with $D_{00} = v$, the partial derivative of
$D_{ij}$ in the first variable equal to $D_{i+1,j}$, and the partial derivative of $D_{ij}$ in the
second variable equal to $D_{i,j+1}$. It expresses that $v$ is smooth along the coordinate lines,
and it gives names to all its partial derivatives. The symmetry of the mixed partial derivatives is
part of the definition, since $D_{i+1,j+1}$ is reached from $D_{ij}$ in both orders.

Two consequences are the purpose of this interface. First, every coordinate slice
$y \mapsto D_{ij}(y, t)$ and $s \mapsto D_{ij}(x, s)$ is of class $C^n$ for every $n$, and its
one-variable iterated derivatives are members of the family: $\frac{d^k}{dy^k} D_{ij}(y, t) =
D_{i+k,j}(y, t)$. So any one-variable theorem, such as Taylor's theorem with the Lagrange remainder
or a bound on a difference quotient, applies to a slice directly. Second, a pointwise identity
between two such functions can be differentiated: two functions with named partial derivatives that
agree everywhere have partial derivatives that agree everywhere. This is how a partial differential
equation satisfied by $v$ is differentiated into identities between the members of $D$.

## Main definitions

* `HasPartialDerivFst`: $v_x$ is the partial derivative of $v$ in the first variable.
* `HasPartialDerivSnd`: $v_t$ is the partial derivative of $v$ in the second variable.
* `HasPartialDerivs`: $D$ is a family of all iterated partial derivatives of $v$.

## Main results

* `HasPartialDerivs.contDiff_fst`, `HasPartialDerivs.contDiff_snd`: every coordinate slice of a
  member of the family is $C^n$ for every $n$.
* `HasPartialDerivs.iteratedDeriv_fst`, `HasPartialDerivs.iteratedDeriv_snd`: the iterated
  derivatives of a slice are members of the family.
* `HasPartialDerivFst.congr`, `HasPartialDerivSnd.congr`: two functions that agree everywhere have
  equal partial derivatives.
* `HasPartialDerivFst.add`, `HasPartialDerivFst.const_mul`, `HasPartialDerivSnd.add`,
  `HasPartialDerivSnd.const_mul`: the partial derivatives of sums and constant multiples.
* `HasPartialDerivs.swap`: exchanging the two variables transposes the family.

## Implementation notes

* The results are proved once for the first variable and transferred to the second by
  `HasPartialDerivs.swap`, which exchanges the arguments of $v$ and transposes the family.
-/

open Set

variable {v w vx wx vt wt : ℝ → ℝ → ℝ} {D : ℕ → ℕ → ℝ → ℝ → ℝ}

/-! ### Partial derivatives in one of the two variables -/

/-- **The partial derivative in the first variable.** For $v, v_x \colon \mathbb{R} \to \mathbb{R}
\to \mathbb{R}$, the function $v_x$ is the partial derivative of $v$ in the first variable if
for all $x, t \in \mathbb{R}$ the function $y \mapsto v(y, t)$ has the derivative $v_x(x, t)$ at
$x$. -/
def HasPartialDerivFst (v vx : ℝ → ℝ → ℝ) : Prop :=
  ∀ x t : ℝ, HasDerivAt (fun y => v y t) (vx x t) x

/-- **The partial derivative in the second variable.** For $v, v_t \colon \mathbb{R} \to \mathbb{R}
\to \mathbb{R}$, the function $v_t$ is the partial derivative of $v$ in the second variable if
for all $x, t \in \mathbb{R}$ the function $s \mapsto v(x, s)$ has the derivative $v_t(x, t)$ at
$t$. -/
def HasPartialDerivSnd (v vt : ℝ → ℝ → ℝ) : Prop :=
  ∀ x t : ℝ, HasDerivAt (fun s => v x s) (vt x t) t

/-- Exchange of the two arguments: $(t, x) \mapsto v_t(x, t)$ is the partial derivative in the first
variable of $(t, x) \mapsto v(x, t)$ if and only if $v_t$ is the partial derivative of $v$ in
the second variable. -/
theorem hasPartialDerivFst_swap_iff :
    HasPartialDerivFst (fun t x => v x t) (fun t x => vt x t) ↔ HasPartialDerivSnd v vt :=
  ⟨fun h x t => h t x, fun h t x => h x t⟩

/-- Exchange of the two arguments: $(t, x) \mapsto v_x(x, t)$ is the partial derivative in the
second variable of $(t, x) \mapsto v(x, t)$ if and only if $v_x$ is the partial derivative of
$v$ in the first variable. -/
theorem hasPartialDerivSnd_swap_iff :
    HasPartialDerivSnd (fun t x => v x t) (fun t x => vx x t) ↔ HasPartialDerivFst v vx :=
  ⟨fun h x t => h t x, fun h t x => h x t⟩

/-- If $v_x$ and $w_x$ are the partial derivatives in the first variable of $v$ and $w$, then
$v_x + w_x$ is the partial derivative in the first variable of $v + w$. -/
theorem HasPartialDerivFst.add (hv : HasPartialDerivFst v vx) (hw : HasPartialDerivFst w wx) :
    HasPartialDerivFst (fun x t => v x t + w x t) fun x t => vx x t + wx x t :=
  fun x t => (hv x t).add (hw x t)

/-- If $v_x$ is the partial derivative in the first variable of $v$ and $c \in \mathbb{R}$, then
$c v_x$ is the partial derivative in the first variable of $c v$. -/
theorem HasPartialDerivFst.const_mul (hv : HasPartialDerivFst v vx) (c : ℝ) :
    HasPartialDerivFst (fun x t => c * v x t) fun x t => c * vx x t :=
  fun x t => (hv x t).const_mul c

/-- If $v_t$ and $w_t$ are the partial derivatives in the second variable of $v$ and $w$, then
$v_t + w_t$ is the partial derivative in the second variable of $v + w$. -/
theorem HasPartialDerivSnd.add (hv : HasPartialDerivSnd v vt) (hw : HasPartialDerivSnd w wt) :
    HasPartialDerivSnd (fun x t => v x t + w x t) fun x t => vt x t + wt x t :=
  fun x t => (hv x t).add (hw x t)

/-- If $v_t$ is the partial derivative in the second variable of $v$ and $c \in \mathbb{R}$, then
$c v_t$ is the partial derivative in the second variable of $c v$. -/
theorem HasPartialDerivSnd.const_mul (hv : HasPartialDerivSnd v vt) (c : ℝ) :
    HasPartialDerivSnd (fun x t => c * v x t) fun x t => c * vt x t :=
  fun x t => (hv x t).const_mul c

/-- **A pointwise identity can be differentiated in the first variable.** Let $v_x$ and $w_x$ be the
partial derivatives in the first variable of $v$ and $w$. If $v(x, t) = w(x, t)$ for all $x, t$,
then $v_x(x, t) = w_x(x, t)$ for all $x, t$. -/
theorem HasPartialDerivFst.congr (hv : HasPartialDerivFst v vx) (hw : HasPartialDerivFst w wx)
    (h : ∀ x t, v x t = w x t) (x t : ℝ) : vx x t = wx x t := by
  have hfun : (fun y => v y t) = fun y => w y t := funext fun y => h y t
  exact (hv x t).unique (hfun ▸ hw x t)

/-- **A pointwise identity can be differentiated in the second variable.** Let $v_t$ and $w_t$ be
the partial derivatives in the second variable of $v$ and $w$. If $v(x, t) = w(x, t)$ for all
$x, t$, then $v_t(x, t) = w_t(x, t)$ for all $x, t$. -/
theorem HasPartialDerivSnd.congr (hv : HasPartialDerivSnd v vt) (hw : HasPartialDerivSnd w wt)
    (h : ∀ x t, v x t = w x t) (x t : ℝ) : vt x t = wt x t := by
  have hfun : (fun s => v x s) = fun s => w x s := funext fun s => h x s
  exact (hv x t).unique (hfun ▸ hw x t)

/-! ### The whole family of iterated partial derivatives -/

/-- **A family of all iterated partial derivatives.** Let $v \colon \mathbb{R} \to \mathbb{R} \to
\mathbb{R}$, and let $D_{ij} \colon \mathbb{R} \to \mathbb{R} \to \mathbb{R}$ for
$i, j \in \mathbb{N}$. The family $D$ is a family of iterated partial derivatives of $v$ if
$D_{00} = v$ and, for all $i, j$, the partial derivative of $D_{ij}$ in the first variable is
$D_{i+1,j}$ and its partial derivative in the second variable is $D_{i,j+1}$.

Then $D_{ij}$ is $\partial_x^i \partial_t^j v$, and every $D_{ij}$ is smooth along both
coordinate directions. The mixed partial derivatives are symmetric by construction:
$D_{i+1,j+1}$ is the partial derivative of $D_{i+1,j}$ in the second variable and also the
partial derivative of $D_{i,j+1}$ in the first variable. The definition asks nothing about $v$
as a function on $\mathbb{R}^2$. -/
def HasPartialDerivs (v : ℝ → ℝ → ℝ) (D : ℕ → ℕ → ℝ → ℝ → ℝ) : Prop :=
  D 0 0 = v ∧ (∀ i j, HasPartialDerivFst (D i j) (D (i + 1) j)) ∧
    ∀ i j, HasPartialDerivSnd (D i j) (D i (j + 1))

namespace HasPartialDerivs

variable (h : HasPartialDerivs v D)
include h

/-- If $D$ is a family of iterated partial derivatives of $v$, then $D_{00} = v$. -/
theorem eq_zero_zero : D 0 0 = v := h.1

/-- If $D$ is a family of iterated partial derivatives of $v$, then $D_{i+1,j}$ is the partial
derivative of $D_{ij}$ in the first variable. -/
theorem hasPartialDerivFst (i j : ℕ) : HasPartialDerivFst (D i j) (D (i + 1) j) := h.2.1 i j

/-- If $D$ is a family of iterated partial derivatives of $v$, then $D_{i,j+1}$ is the partial
derivative of $D_{ij}$ in the second variable. -/
theorem hasPartialDerivSnd (i j : ℕ) : HasPartialDerivSnd (D i j) (D i (j + 1)) := h.2.2 i j

/-- **Exchange of the two variables.** If $D$ is a family of iterated partial derivatives of $v$,
then the transposed family $(i, j, t, x) \mapsto D_{ji}(x, t)$ is a family of iterated partial
derivatives of $(t, x) \mapsto v(x, t)$. -/
theorem swap : HasPartialDerivs (fun t x => v x t) fun i j t x => D j i x t :=
  ⟨by rw [← h.eq_zero_zero], fun i j t x => h.hasPartialDerivSnd j i x t,
    fun i j t x => h.hasPartialDerivFst j i x t⟩

/-- If $D$ is a family of iterated partial derivatives of $v$, then for all $i, j$ and $t$ the slice
$y \mapsto D_{ij}(y, t)$ is differentiable on $\mathbb{R}$. -/
theorem differentiable_fst (i j : ℕ) (t : ℝ) : Differentiable ℝ fun y => D i j y t :=
  fun y => (h.hasPartialDerivFst i j y t).differentiableAt

/-- If $D$ is a family of iterated partial derivatives of $v$, then the derivative of the slice
$y \mapsto D_{ij}(y, t)$ is the slice $y \mapsto D_{i+1,j}(y, t)$. -/
theorem deriv_fst (i j : ℕ) (t : ℝ) : (deriv fun y => D i j y t) = fun y => D (i + 1) j y t :=
  funext fun y => (h.hasPartialDerivFst i j y t).deriv

/-- If $D$ is a family of iterated partial derivatives of $v$, then for all $i, j$ and $x$ the slice
$s \mapsto D_{ij}(x, s)$ is differentiable on $\mathbb{R}$. -/
theorem differentiable_snd (i j : ℕ) (x : ℝ) : Differentiable ℝ fun s => D i j x s :=
  fun s => (h.hasPartialDerivSnd i j x s).differentiableAt

/-- If $D$ is a family of iterated partial derivatives of $v$, then the derivative of the slice
$s \mapsto D_{ij}(x, s)$ is the slice $s \mapsto D_{i,j+1}(x, s)$. -/
theorem deriv_snd (i j : ℕ) (x : ℝ) : (deriv fun s => D i j x s) = fun s => D i (j + 1) x s :=
  funext fun s => (h.hasPartialDerivSnd i j x s).deriv

/-- **Every slice in the first variable is smooth.** If $D$ is a family of iterated partial
derivatives of $v$, then for all $n, i, j \in \mathbb{N}$ and $t \in \mathbb{R}$ the slice
$y \mapsto D_{ij}(y, t)$ is of class $C^n$. -/
theorem contDiff_fst (n i j : ℕ) (t : ℝ) : ContDiff ℝ n fun y => D i j y t := by
  induction n generalizing i with
  | zero => exact contDiff_zero.2 (h.differentiable_fst i j t).continuous
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; ring]
    refine contDiff_succ_iff_deriv.2 ⟨h.differentiable_fst i j t, fun hn => ?_, ?_⟩
    · exact absurd hn (by simp)
    · rw [h.deriv_fst]
      exact ih (i + 1)

/-- **Every slice in the second variable is smooth.** If $D$ is a family of iterated partial
derivatives of $v$, then for all $n, i, j \in \mathbb{N}$ and $x \in \mathbb{R}$ the slice
$s \mapsto D_{ij}(x, s)$ is of class $C^n$. -/
theorem contDiff_snd (n i j : ℕ) (x : ℝ) : ContDiff ℝ n fun s => D i j x s :=
  h.swap.contDiff_fst n j i x

/-- **The iterated derivatives of a slice in the first variable.** If $D$ is a family of iterated
partial derivatives of $v$, then for all $k, i, j$ and $t$,
$$\frac{d^k}{dy^k} D_{ij}(y, t) = D_{i+k,j}(y, t) \quad \text{for all } y.$$
-/
theorem iteratedDeriv_fst (k i j : ℕ) (t : ℝ) :
    (iteratedDeriv k fun y => D i j y t) = fun y => D (i + k) j y t := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ', h.deriv_fst, ih (i + 1), show i + 1 + k = i + (k + 1) by omega]

/-- **The iterated derivatives of a slice in the second variable.** If $D$ is a family of iterated
partial derivatives of $v$, then for all $k, i, j$ and $x$,
$$\frac{d^k}{ds^k} D_{ij}(x, s) = D_{i,j+k}(x, s) \quad \text{for all } s.$$
-/
theorem iteratedDeriv_snd (k i j : ℕ) (x : ℝ) :
    (iteratedDeriv k fun s => D i j x s) = fun s => D i (j + k) x s :=
  h.swap.iteratedDeriv_fst k j i x

end HasPartialDerivs
