/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Field
import Numlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Numlib.RingTheory.Polynomial.HermiteInterpolation

/-!
# Jets and divided differences of functions

This module gives the analytic side of Hermite interpolation on a multiset of nodes, for functions
$f : \mathbb{K} \to \mathbb{K}$ on a nontrivially normed field $\mathbb{K}$. The jet of $f$ at $x$
is the sequence of its Taylor coefficients $f^{(j)}(x)/j!$. The divided difference $f[s]$ at a
multiset $s$ of nodes is the leading coefficient, in degree $|s| - 1$, of the Hermite interpolant of
the jets of $f$ on $s$. A node of multiplicity $m$ prescribes the first $m$ Taylor coefficients
there. At distinct nodes this is the classical divided difference $f[\lambda_0, \dots, \lambda_k]$
of [golub2013matrix], §9.1.4; at repeated nodes it is the confluent divided difference. The
field-level theory of jet interpolation is in `Numlib.RingTheory.Polynomial.HermiteInterpolation`.

## Main definitions

* `Hermite.taylorJet`: the Taylor coefficients $f^{(j)}(x)/j!$ of $f$ at $x$.
* `Hermite.divDiff`: the divided difference $f[s]$ at a multiset $s$ of possibly repeated nodes.

## Main results

* `Hermite.isJetInterpolant_taylorJet_iff`: in characteristic $0$, a polynomial $p$ interpolates the
  jets of $f$ on $s$ if and only if $p^{(j)}(x) = f^{(j)}(x)$ for each node $x$ and each $j$ less
  than the multiplicity of $x$.
* `Hermite.taylorJet_polynomial`: the jet of a polynomial function is its Taylor expansion.
* `Hermite.taylorJet_add`, `Hermite.taylorJet_mul`: jets of sums and products (Leibniz's rule) for
  smooth functions.
* `Hermite.divDiff_congr`: the divided difference depends only on the jets that it uses.
* `Hermite.IsJetInterpolant.divDiff_eq`: the divided difference can be computed from any polynomial
  that interpolates on more nodes.
* `Hermite.divDiff_replicate`: at $k + 1$ copies of one node, $f[x, \dots, x] = f^{(k)}(x)/k!$.
* `Hermite.divDiff_cons_cons`: the recursion $f[x, x', s] = (f[x, s] - f[x', s]) / (x - x')$ for
  $x \neq x'$.
* `Hermite.divDiff_cons_eq_of_eventuallyEq`: if $f(z) = f(a) + (z - a) g(z)$ near the nodes, then
  $f[a, s] = g[s]$.
* `Hermite.divDiff_X_pow`: the divided differences of monomials satisfy
  $z^{m+1}[x, s] = x \cdot z^m[x, s] + z^m[s]$, so they are complete homogeneous symmetric
  polynomials of the nodes.

## Implementation notes

* `Hermite.taylorJet` is total. Where $f$ is not differentiable, the value $0$ that Mathlib gives to
  `iteratedDeriv` enters. Each result that uses a jet has the smoothness that it needs as a
  hypothesis.
* The module is in `Numlib.Analysis.Calculus` and not beside the numerical Hermite interpolation of
  `Numlib.Approximation.Hermite`. The reason is that `Hermite.taylorJet` needs `iteratedDeriv`, and
  the primary functional calculus, which uses it, must not import the numerical
  `Numlib.Approximation` layer.
* The real, `Fin`-indexed Hermite interpolation of `Numlib.Approximation.Hermite` is a special case
  of `Hermite.interpolateJet`, by `Hermite.interpolate_eq_interpolateJet`. Its classical divided
  difference is a special case of `Hermite.divDiff`, by `DividedDifference.newtonOn_eq_divDiff`.
-/

open Polynomial

namespace Hermite

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-! ### Jets of functions -/

/-- The **Taylor coefficients** of $f : \mathbb{K} \to \mathbb{K}$ at $x$: the $j$-th coefficient is
$f^{(j)}(x)/j!$.

The definition is total: where $f$ is not $j$ times differentiable, `iteratedDeriv j f x` has
the value that Mathlib gives it, and results that use the jet carry the smoothness that they
need as a hypothesis. -/
noncomputable def taylorJet (f : 𝕜 → 𝕜) (x : 𝕜) (j : ℕ) : 𝕜 :=
  iteratedDeriv j f x / j.factorial

/-- The zeroth Taylor coefficient of $f$ at $x$ is $f(x)$. -/
@[simp]
theorem taylorJet_zero (f : 𝕜 → 𝕜) (x : 𝕜) : taylorJet f x 0 = f x := by
  simp [taylorJet]

/-- In characteristic $0$, the $j$-th coefficient of the Taylor expansion of a polynomial $p$ at $x$
is $p^{(j)}(x)/j!$. -/
theorem coeff_taylor_eq_eval_iterate_derivative_div [CharZero 𝕜] (p : 𝕜[X]) (x : 𝕜) (j : ℕ) :
    (taylor x p).coeff j = (derivative^[j] p).eval x / j.factorial := by
  have hj : (j.factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  rw [eq_div_iff hj, taylor_coeff, ← factorial_smul_hasseDeriv, LinearMap.smul_apply, eval_smul,
    nsmul_eq_mul, mul_comm]

/-- The **jet of a polynomial function is its Taylor expansion**. Let $\mathbb{K}$ have
characteristic $0$ and let $p \in \mathbb{K}[X]$. Then the $j$-th Taylor coefficient of the
function $z \mapsto p(z)$ at $x$ is the $j$-th coefficient of the Taylor expansion of $p$ at
$x$, that is, of $p(X + x)$.

The Taylor expansion is Mathlib's `Polynomial.taylor`. -/
theorem taylorJet_polynomial [CharZero 𝕜] (p : 𝕜[X]) (x : 𝕜) (j : ℕ) :
    taylorJet (fun z => p.eval z) x j = (taylor x p).coeff j := by
  rw [taylorJet, Polynomial.iteratedDeriv_eval, coeff_taylor_eq_eval_iterate_derivative_div]

/-- If $f$ and $g$ are $C^j$ at $x$, then the $j$-th Taylor coefficient of $f + g$ at $x$ is the sum
of those of $f$ and $g$. -/
theorem taylorJet_add {f g : 𝕜 → 𝕜} {x : 𝕜} {j : ℕ} (hf : ContDiffAt 𝕜 j f x)
    (hg : ContDiffAt 𝕜 j g x) : taylorJet (f + g) x j = taylorJet f x j + taylorJet g x j := by
  rw [taylorJet, iteratedDeriv_add hf hg, add_div, taylorJet, taylorJet]

/-- If $f$ and $g$ are $C^j$ at $x$, then the $j$-th Taylor coefficient of $f - g$ at $x$ is the
difference of those of $f$ and $g$. -/
theorem taylorJet_sub {f g : 𝕜 → 𝕜} {x : 𝕜} {j : ℕ} (hf : ContDiffAt 𝕜 j f x)
    (hg : ContDiffAt 𝕜 j g x) : taylorJet (f - g) x j = taylorJet f x j - taylorJet g x j := by
  rw [taylorJet, iteratedDeriv_sub hf hg, sub_div, taylorJet, taylorJet]

/-- The $j$-th Taylor coefficient of $c f$ at $x$ is $c$ times that of $f$, for every function $f$
and every constant $c$. -/
theorem taylorJet_const_smul (c : 𝕜) (f : 𝕜 → 𝕜) (x : 𝕜) (j : ℕ) :
    taylorJet (c • f) x j = c * taylorJet f x j := by
  rw [taylorJet, iteratedDeriv_const_smul_field, smul_eq_mul, mul_div_assoc, taylorJet]

/-- **Leibniz's rule for jets**. Let $\mathbb{K}$ have characteristic $0$, and let $f$ and $g$ be
$C^n$ at $x$. Then the jet of the product is the Cauchy product of the jets:
$$\frac{(fg)^{(n)}(x)}{n!} = \sum_{i=0}^{n} \frac{f^{(i)}(x)}{i!} \cdot
  \frac{g^{(n-i)}(x)}{(n-i)!}.$$
-/
theorem taylorJet_mul [CharZero 𝕜] {f g : 𝕜 → 𝕜} {x : 𝕜} {n : ℕ} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) :
    taylorJet (f * g) x n =
      ∑ i ∈ Finset.range (n + 1), taylorJet f x i * taylorJet g x (n - i) := by
  rw [taylorJet, iteratedDeriv_mul hf hg, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h := Nat.choose_mul_factorial_mul_factorial hin
  have h1 : (i.factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr i.factorial_ne_zero
  have h2 : ((n - i).factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (n - i).factorial_ne_zero
  have h3 : (n.choose i : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hin).ne'
  rw [taylorJet, taylorJet, ← h]
  push_cast
  field_simp

variable [DecidableEq 𝕜]

/-- **Interpolating the jets of a function is agreement of derivatives.** Let $\mathbb{K}$ have
characteristic $0$, let $s$ be a multiset of nodes, let $f : \mathbb{K} \to \mathbb{K}$, and let
$p \in \mathbb{K}[X]$. Then $p$ interpolates the jets of $f$ on $s$ if and only if
$$p^{(j)}(x) = f^{(j)}(x) \quad \text{for every node } x \in s \text{ and every } j < m(x),$$
where $m(x)$ is the multiplicity of $x$ in $s$.

Jet interpolation is `Hermite.IsJetInterpolant`: for each node $x$, $(X - x)^{m(x)}$ divides $p$
minus the Taylor polynomial of order $m(x)$ of the jet of $f$ at $x$. The derivative $f^{(j)}$
is `iteratedDeriv j f`. -/
theorem isJetInterpolant_taylorJet_iff [CharZero 𝕜] {s : Multiset 𝕜} {f : 𝕜 → 𝕜} {p : 𝕜[X]} :
    IsJetInterpolant s (taylorJet f) p ↔
      ∀ x ∈ s, ∀ j < s.count x, (derivative^[j] p).eval x = iteratedDeriv j f x := by
  rw [isJetInterpolant_iff_coeff_taylor]
  refine forall₂_congr fun x _ => forall₂_congr fun j _ => ?_
  have hj : (j.factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  rw [coeff_taylor_eq_eval_iterate_derivative_div, taylorJet, div_left_inj' hj]

/-- In characteristic $0$, a polynomial $p$ interpolates the jets of the function $z \mapsto p(z)$
on every multiset of nodes. -/
theorem isJetInterpolant_taylorJet_polynomial [CharZero 𝕜] (s : Multiset 𝕜) (p : 𝕜[X]) :
    IsJetInterpolant s (taylorJet fun z => p.eval z) p := by
  have h : (taylorJet fun z => p.eval z) = fun x j => (taylor x p).coeff j := by
    ext x j
    exact taylorJet_polynomial p x j
  rw [h]
  exact isJetInterpolant_coeff_taylor s p

/-- The Hermite interpolant of the jets of $f$ on $s$ takes the value $f(x)$ at every node
$x \in s$. -/
theorem eval_interpolateJet_taylorJet {f : 𝕜 → 𝕜} {s : Multiset 𝕜} {x : 𝕜} (hx : x ∈ s) :
    (interpolateJet s (taylorJet f)).eval x = f x := by
  have := isJetInterpolant_iff_coeff_taylor.mp (isJetInterpolant_interpolateJet s (taylorJet f))
    x hx 0 (Multiset.count_pos.mpr hx)
  rwa [taylor_coeff_zero, taylorJet_zero] at this

/-! ### Divided differences at repeated nodes -/

/-- The **divided difference** $f[s]$ of $f : \mathbb{K} \to \mathbb{K}$ at a multiset $s$ of
possibly repeated nodes: the coefficient of $X^{|s| - 1}$ in the Hermite interpolant of the jets
of $f$ on $s$.

At distinct nodes $x_0, \dots, x_k$ this is the classical divided difference
$f[x_0, \dots, x_k]$. At $k + 1$ copies of one node $x$ it is $f^{(k)}(x)/k!$
(`Hermite.divDiff_replicate`). At the empty multiset the value is $0$, because the interpolant
is $0$. The interpolant is `Hermite.interpolateJet s (Hermite.taylorJet f)`. -/
noncomputable def divDiff (f : 𝕜 → 𝕜) (s : Multiset 𝕜) : 𝕜 :=
  (interpolateJet s (taylorJet f)).coeff (Multiset.card s - 1)

/-- The divided difference at the empty multiset is $0$. -/
@[simp]
theorem divDiff_zero (f : 𝕜 → 𝕜) : divDiff f 0 = 0 := by
  simp [divDiff]

/-- The **divided difference depends only on the jets that it uses**. Let $s$ be a multiset of
nodes, and let $f, g : \mathbb{K} \to \mathbb{K}$ satisfy $f^{(j)}(x)/j! = g^{(j)}(x)/j!$ for
every node $x \in s$ and every $j$ less than the multiplicity of $x$ in $s$. Then $f[s] = g[s]$. -/
theorem divDiff_congr {f g : 𝕜 → 𝕜} {s : Multiset 𝕜}
    (h : ∀ x ∈ s, ∀ j < s.count x, taylorJet f x j = taylorJet g x j) :
    divDiff f s = divDiff g s := by
  rw [divDiff, divDiff, interpolateJet_congr h]

/-- If $p$ interpolates the jets of $f$ on $s$, then $f[s]$ is the coefficient of $X^{|s| - 1}$ in
the remainder of $p$ modulo the nodal polynomial $\prod_{x \in s} (X - x)$. -/
theorem IsJetInterpolant.divDiff_eq_coeff {f : 𝕜 → 𝕜} {s : Multiset 𝕜} {p : 𝕜[X]}
    (hp : IsJetInterpolant s (taylorJet f) p) :
    divDiff f s = (p %ₘ nodalMultiset s).coeff (Multiset.card s - 1) := by
  rw [divDiff, hp.modByMonic_eq_interpolateJet]

/-- In characteristic $0$, the divided difference of a polynomial function $z \mapsto p(z)$ at $s$
is the coefficient of $X^{|s| - 1}$ in the remainder of $p$ modulo the nodal polynomial
$\prod_{x \in s} (X - x)$. -/
theorem divDiff_polynomial [CharZero 𝕜] (p : 𝕜[X]) (s : Multiset 𝕜) :
    divDiff (fun z => p.eval z) s = (p %ₘ nodalMultiset s).coeff (Multiset.card s - 1) :=
  (isJetInterpolant_taylorJet_polynomial s p).divDiff_eq_coeff

/-- **Divided differences through an interpolant on more nodes.** Let $\mathbb{K}$ have
characteristic $0$, let $s \le t$ be multisets of nodes, and let $p \in \mathbb{K}[X]$
interpolate the jets of $f$ on $t$. Then $f[s] = p[s]$, where $p[s]$ is the divided difference
of the function $z \mapsto p(z)$. -/
theorem IsJetInterpolant.divDiff_eq [CharZero 𝕜] {f : 𝕜 → 𝕜} {s t : Multiset 𝕜} {p : 𝕜[X]}
    (hp : IsJetInterpolant t (taylorJet f) p) (hst : s ≤ t) :
    divDiff f s = divDiff (fun z => p.eval z) s := by
  rw [(hp.of_le hst).divDiff_eq_coeff, divDiff_polynomial]

/-- In characteristic $0$, if $p \in \mathbb{K}[X]$ has degree less than $|s|$, then the divided
difference of $z \mapsto p(z)$ at $s$ is the coefficient of $X^{|s| - 1}$ in $p$. -/
theorem divDiff_polynomial_of_degree_lt [CharZero 𝕜] {p : 𝕜[X]} {s : Multiset 𝕜}
    (hp : p.degree < Multiset.card s) :
    divDiff (fun z => p.eval z) s = p.coeff (Multiset.card s - 1) := by
  rw [divDiff_polynomial, (modByMonic_eq_self_iff (monic_nodalMultiset s)).mpr
    (by rwa [degree_nodalMultiset])]

/-- Divided differences are additive in the function: if $f$ and $g$ are $C^{m(x) - 1}$ at each node
$x \in s$, where $m(x)$ is the multiplicity of $x$ in $s$, then $(f + g)[s] = f[s] + g[s]$. -/
theorem divDiff_add {f g : 𝕜 → 𝕜} {s : Multiset 𝕜}
    (hf : ∀ x ∈ s, ContDiffAt 𝕜 (s.count x - 1 : ℕ) f x)
    (hg : ∀ x ∈ s, ContDiffAt 𝕜 (s.count x - 1 : ℕ) g x) :
    divDiff (f + g) s = divDiff f s + divDiff g s := by
  have h : ∀ x ∈ s, ∀ j < s.count x,
      taylorJet (f + g) x j = (taylorJet f + taylorJet g) x j := fun x hx j hj => by
    have hj : (j : WithTop ℕ∞) ≤ (s.count x - 1 : ℕ) := by exact_mod_cast (by omega : j ≤ _)
    rw [Pi.add_apply, Pi.add_apply, taylorJet_add ((hf x hx).of_le hj) ((hg x hx).of_le hj)]
  rw [divDiff, interpolateJet_congr h, interpolateJet_add, coeff_add, divDiff, divDiff]

/-- Divided differences are homogeneous in the function: $(c f)[s] = c \cdot f[s]$ for every
function $f$, constant $c$ and multiset $s$. -/
theorem divDiff_const_smul (c : 𝕜) (f : 𝕜 → 𝕜) (s : Multiset 𝕜) :
    divDiff (c • f) s = c * divDiff f s := by
  have h : taylorJet (c • f) = c • taylorJet f := by
    ext x j
    rw [taylorJet_const_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [divDiff, h, interpolateJet_smul, coeff_smul, smul_eq_mul, divDiff]

/-- At $k + 1$ copies of one node $x$, the divided difference is the Taylor coefficient:
$$f[\underbrace{x, \dots, x}_{k+1}] = \frac{f^{(k)}(x)}{k!}.$$

No smoothness of $f$ is assumed. Where $f$ is not $k$ times differentiable at $x$, both sides
use the value that Mathlib gives to `iteratedDeriv`. -/
theorem divDiff_replicate (f : 𝕜 → 𝕜) (x : 𝕜) (k : ℕ) :
    divDiff f (Multiset.replicate (k + 1) x) = taylorJet f x k := by
  have hP : IsJetInterpolant (Multiset.replicate (k + 1) x) (taylorJet f)
      (jetPoly (taylorJet f x) x (k + 1)) := by
    intro z hz
    rw [Multiset.eq_of_mem_replicate hz, Multiset.count_replicate_self, sub_self]
    exact dvd_zero _
  rw [divDiff, ← eq_interpolateJet (by simpa using degree_jetPoly_lt _ x (k + 1)) hP,
    Multiset.card_replicate, Nat.add_sub_cancel, coeff_jetPoly_succ_self]

/-- The divided difference at a single node $x$ is $f(x)$. -/
@[simp]
theorem divDiff_singleton (f : 𝕜 → 𝕜) (x : 𝕜) : divDiff f {x} = f x := by
  simpa using divDiff_replicate f x 0

/-- The **recursion of divided differences**. Let $x \neq x'$ be nodes and let $s$ be a multiset of
nodes, possibly with repetitions and possibly containing $x$ or $x'$. Then
$$f[x, x', s] = \frac{f[x, s] - f[x', s]}{x - x'}.$$

No smoothness of $f$ is assumed. -/
theorem divDiff_cons_cons (f : 𝕜 → 𝕜) {x x' : 𝕜} (h : x ≠ x') (s : Multiset 𝕜) :
    divDiff f (x ::ₘ x' ::ₘ s) = (divDiff f (x ::ₘ s) - divDiff f (x' ::ₘ s)) / (x - x') := by
  rw [eq_div_iff (sub_ne_zero.mpr h)]
  set Q := interpolateJet (x ::ₘ x' ::ₘ s) (taylorJet f)
  have h1 := interpolateJet_cons_sub x' (x ::ₘ s) (taylorJet f)
  have h2 := interpolateJet_cons_sub x (x' ::ₘ s) (taylorJet f)
  rw [Multiset.cons_swap] at h1
  simp only [Multiset.card_cons, nodalMultiset_cons] at h1 h2
  have key : interpolateJet (x ::ₘ s) (taylorJet f) - interpolateJet (x' ::ₘ s) (taylorJet f)
      = C (Q.coeff (Multiset.card s + 1) * (x - x')) * nodalMultiset s := by
    rw [map_mul, map_sub]
    linear_combination h2 - h1
  have hc := congrArg (coeff · (Multiset.card s)) key
  simp only [coeff_sub, coeff_C_mul] at hc
  rw [← natDegree_nodalMultiset s, (monic_nodalMultiset s).coeff_natDegree, mul_one,
    natDegree_nodalMultiset] at hc
  simp only [divDiff, Multiset.card_cons, Nat.add_sub_cancel]
  rw [hc]

/-- **Multiplication by the identity** adds one node to the divided difference of a polynomial
function. In characteristic $0$, for $p \in \mathbb{K}[X]$,
$$(z \, p)[x, s] = x \cdot p[x, s] + p[s],$$
where $p[s]$ is the divided difference of $z \mapsto p(z)$ and $(z \, p)[s]$ that of
$z \mapsto z \, p(z)$. -/
theorem divDiff_X_mul [CharZero 𝕜] (p : 𝕜[X]) (x : 𝕜) (s : Multiset 𝕜) :
    divDiff (fun z => z * p.eval z) (x ::ₘ s)
      = x * divDiff (fun z => p.eval z) (x ::ₘ s) + divDiff (fun z => p.eval z) s := by
  have hXp : (fun z => z * p.eval z) = fun z => (X * p).eval z := by
    ext z
    simp
  set k := Multiset.card s
  set N := nodalMultiset s
  set q := p %ₘ nodalMultiset (x ::ₘ s)
  set q' := p %ₘ N
  set c := q.coeff k
  have hq : q - q' = C c * N := by
    have := interpolateJet_cons_sub x s fun z j => (taylor z p).coeff j
    rwa [interpolateJet_coeff_taylor, interpolateJet_coeff_taylor] at this
  have hq'deg : q'.degree < k := by
    rw [← degree_nodalMultiset s]
    exact degree_modByMonic_lt _ (monic_nodalMultiset s)
  -- the remainder of `X * p`
  have hrem : (X * p) %ₘ nodalMultiset (x ::ₘ s) = X * q' + C (c * x) * N := by
    have hdvd : nodalMultiset (x ::ₘ s) ∣ X * p - (X * q' + C (c * x) * N) := by
      have hpq : nodalMultiset (x ::ₘ s) ∣ p - q := by
        rw [← dvd_neg, neg_sub]
        exact dvd_modByMonic_sub p _
      have e : X * p - (X * q' + C (c * x) * N) = X * (p - q) + C c * nodalMultiset (x ::ₘ s) := by
        rw [nodalMultiset_cons, map_mul]
        linear_combination X * hq
      rw [e]
      exact dvd_add (hpq.mul_left X) (dvd_mul_left _ _)
    rw [modByMonic_eq_of_dvd_sub (monic_nodalMultiset _) hdvd,
      (modByMonic_eq_self_iff (monic_nodalMultiset _)).mpr]
    rw [degree_nodalMultiset, Multiset.card_cons]
    refine (degree_lt_iff_coeff_zero _ _).mpr fun m hm => ?_
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [coeff_add, coeff_X_mul, coeff_C_mul, coeff_eq_zero_of_degree_lt
      (hq'deg.trans_le (by exact_mod_cast (by omega : k ≤ m))),
      coeff_eq_zero_of_natDegree_lt (by rw [natDegree_nodalMultiset]; omega), mul_zero, add_zero]
  rw [hXp, divDiff_polynomial, divDiff_polynomial, divDiff_polynomial, hrem, Multiset.card_cons,
    Nat.add_sub_cancel, coeff_add, coeff_C_mul, ← natDegree_nodalMultiset s,
    (monic_nodalMultiset s).coeff_natDegree, natDegree_nodalMultiset]
  change (X * q').coeff k + c * x * 1 = x * c + q'.coeff (k - 1)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk, coeff_X_mul_zero, coeff_eq_zero_of_degree_lt (hq'deg.trans_le (by rw [hk]))]
    ring
  · obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk', coeff_X_mul, Nat.add_sub_cancel]
    ring

/-- The **divided differences of monomials**. In characteristic $0$, for every $m \in \mathbb{N}$,
node $x$ and multiset $s$,
$$z^{m+1}[x, s] = x \cdot z^m[x, s] + z^m[s],$$
where $z^m[s]$ is the divided difference of $z \mapsto z^m$ at $s$.

With $z^m[s] = 0$ for $|s| > m + 1$ and $z^m[s] = 1$ for $|s| = m + 1$, this recursion makes
$z^m[s]$ the complete homogeneous symmetric polynomial of degree $m + 1 - |s|$ in the nodes. -/
theorem divDiff_X_pow [CharZero 𝕜] (m : ℕ) (x : 𝕜) (s : Multiset 𝕜) :
    divDiff (fun z => z ^ (m + 1)) (x ::ₘ s)
      = x * divDiff (fun z => z ^ m) (x ::ₘ s) + divDiff (fun z => z ^ m) s := by
  have h := divDiff_X_mul (X ^ m) x s
  simp only [eval_pow, eval_X] at h
  rw [← h]
  congr 1
  ext z
  ring

/-! ### Removing a node -/

omit [DecidableEq 𝕜] in
/-- Let $c, a \in \mathbb{K}$, let $p \in \mathbb{K}[X]$, and let $s$ be a nonempty multiset of
nodes, with nodal polynomial $\omega_s = \prod_{x \in s} (X - x)$. Then the coefficient of
$X^{|s|}$ in the remainder of $c + (X - a) p$ modulo $\omega_{a :: s}$ equals the coefficient of
$X^{|s| - 1}$ in the remainder of $p$ modulo $\omega_s$.

Here $a :: s$ is the multiset $s$ with one more copy of $a$. This is the polynomial form of
`Hermite.divDiff_cons_eq_of_eventuallyEq`. -/
theorem coeff_C_add_X_sub_C_mul_modByMonic (c a : 𝕜) (p : 𝕜[X]) {s : Multiset 𝕜} (hs : s ≠ 0) :
    ((C c + (X - C a) * p) %ₘ nodalMultiset (a ::ₘ s)).coeff (Multiset.card s)
      = (p %ₘ nodalMultiset s).coeff (Multiset.card s - 1) := by
  set N := nodalMultiset s
  set k := Multiset.card s
  set p₀ := p %ₘ N
  obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by
    have := Multiset.card_pos.mpr hs
    omega⟩
  have hp₀ : p₀.degree < k := by
    rw [← degree_nodalMultiset s]
    exact degree_modByMonic_lt _ (monic_nodalMultiset s)
  have hcoeff : ∀ m, k ≤ m → p₀.coeff m = 0 := fun m hm =>
    coeff_eq_zero_of_degree_lt (hp₀.trans_le (by exact_mod_cast hm))
  have hq : ∀ m, (C c + (X - C a) * p₀).coeff (m + 1) = p₀.coeff m - a * p₀.coeff (m + 1) := by
    intro m
    rw [sub_mul, coeff_add, coeff_sub, coeff_X_mul, coeff_C_mul, coeff_C, ite_eq_right (by omega),
      zero_add]
  have hrem : (C c + (X - C a) * p) %ₘ nodalMultiset (a ::ₘ s) = C c + (X - C a) * p₀ := by
    have hdvd : nodalMultiset (a ::ₘ s) ∣ C c + (X - C a) * p - (C c + (X - C a) * p₀) := by
      refine ⟨p /ₘ N, ?_⟩
      have h := modByMonic_add_div p N
      rw [nodalMultiset_cons]
      linear_combination -(X - C a) * h
    rw [modByMonic_eq_of_dvd_sub (monic_nodalMultiset _) hdvd,
      (modByMonic_eq_self_iff (monic_nodalMultiset _)).mpr]
    rw [degree_nodalMultiset, Multiset.card_cons]
    refine (degree_lt_iff_coeff_zero _ _).mpr fun m hm => ?_
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [hq, hcoeff m (by omega), hcoeff (m + 1) (by omega), mul_zero, sub_zero]
  rw [hrem, hk', hq, hcoeff (k' + 1) hk'.le, mul_zero, sub_zero, Nat.add_sub_cancel]

/-- **Removing a node divides by $z - a$.** Let $\mathbb{K}$ have characteristic $0$, let
$a \in \mathbb{K}$, and let $s$ be a nonempty multiset of nodes. Let
$f, g : \mathbb{K} \to \mathbb{K}$ be such that, at each node $x$ of $a :: s$, the function $g$
is $C^{|s|}$ at $x$ and
$$f(z) = f(a) + (z - a) \, g(z) \quad \text{for all } z \text{ near } x.$$
Then $f[a, s] = g[s]$.

Here $a :: s$ is the multiset $s$ with one more copy of $a$. -/
theorem divDiff_cons_eq_of_eventuallyEq [CharZero 𝕜] {f g : 𝕜 → 𝕜} {a : 𝕜} {s : Multiset 𝕜}
    (hs : s ≠ 0) (hg : ∀ x ∈ a ::ₘ s, ContDiffAt 𝕜 (Multiset.card s) g x)
    (hfg : ∀ x ∈ a ::ₘ s, f =ᶠ[nhds x] fun z => f a + (z - a) * g z) :
    divDiff f (a ::ₘ s) = divDiff g s := by
  set p := interpolateJet (a ::ₘ s) (taylorJet g)
  have hp : IsJetInterpolant (a ::ₘ s) (taylorJet g) p := isJetInterpolant_interpolateJet _ _
  have hq : IsJetInterpolant (a ::ₘ s) (taylorJet f) (C (f a) + (X - C a) * p) := by
    refine (isJetInterpolant_congr fun x hx j hj => ?_).mp
      ((isJetInterpolant_taylorJet_polynomial (a ::ₘ s) (C (f a))).add
        ((isJetInterpolant_taylorJet_polynomial (a ::ₘ s) (X - C a)).mul hp))
    have hjs : j ≤ Multiset.card s := by
      have := (Multiset.count_le_card x (a ::ₘ s)).trans_lt' hj
      rw [Multiset.card_cons] at this
      omega
    have hgx : ContDiffAt 𝕜 j g x := (hg x hx).of_le (by exact_mod_cast hjs)
    have hlin : ContDiffAt 𝕜 j (fun z => z - a) x := contDiffAt_id.sub contDiffAt_const
    have hf : taylorJet f x j = taylorJet ((fun _ => f a) + (fun z => z - a) * g) x j := by
      rw [taylorJet, taylorJet, (hfg x hx).iteratedDeriv_eq]
      rfl
    simp only [Pi.add_apply, eval_C, eval_sub, eval_X]
    rw [hf, taylorJet_add (f := fun _ => f a) (g := (fun z => z - a) * g) contDiffAt_const
      (hlin.mul hgx), taylorJet_mul hlin hgx]
  rw [hq.divDiff_eq_coeff, (hp.of_le (Multiset.le_cons_self s a)).divDiff_eq_coeff,
    Multiset.card_cons, Nat.add_sub_cancel, coeff_C_add_X_sub_C_mul_modByMonic _ _ _ hs]

end Hermite
