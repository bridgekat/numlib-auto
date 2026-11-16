/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas`, whose name this module mirrors.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Iterated derivatives: polynomials, conjugation, open sets and compositions

This module proves facts about the iterated derivative $f^{(j)}$ (`iteratedDeriv`) of a function of
one variable on a nontrivially normed field $\mathbb{K}$ that are not in Mathlib. They concern
polynomial functions, conjugation, functions of class $C^N$ on an open set, and compositions.

## Main results

* `Polynomial.iteratedDeriv_eval`: the iterated derivative of a polynomial function is the function
  of the iterated formal derivative.
* `iteratedDeriv_conj_conj`: the iterated derivatives of $\bar{f}(z) = \overline{f(\bar z)}$ are
  $\overline{f^{(j)}(\bar z)}$.
* `ContDiffOn.hasDerivAt_iteratedDeriv_of_isOpen`,
  `ContDiffOn.continuousOn_iteratedDeriv_of_isOpen`: on an open set where $f$ is $C^N$, the iterated
  derivatives are the successive derivatives, and the last one is continuous.
* `contDiffOn_of_hasDerivAt_chain`: conversely, a chain of functions on an open set, each the
  derivative of the one before and the last continuous, is the chain of iterated derivatives of a
  $C^n$ function.
* `iteratedDeriv_comp_congr`: the derivatives up to order $n$ of a composition at a point depend
  only on the derivatives up to order $n$ of the factors. This is the formal content of Faà di
  Bruno's formula.
* `FormalMultilinearSeries.taylorComp_congr`: the Taylor composition of two series at order $n$
  reads only the terms of order at most $n$.
-/

open Polynomial

section Polynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The iterated derivative of a polynomial function is the function of the iterated formal
derivative: for $p \in \mathbb{K}[X]$ and $n \in \mathbb{N}$, the $n$-th derivative of
$x \mapsto p(x)$ is $x \mapsto p^{(n)}(x)$, with $p^{(n)}$ the $n$-th formal derivative
`Polynomial.derivative^[n] p`. -/
theorem Polynomial.iteratedDeriv_eval (p : 𝕜[X]) (n : ℕ) :
    iteratedDeriv n (fun x => p.eval x) = fun x => (derivative^[n] p).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    ext x
    exact Polynomial.deriv _

end Polynomial

section Conj

open ComplexConjugate

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [NormedStarGroup 𝕜]

/-- Let $\mathbb{K}$ carry a star operation $z \mapsto \bar z$ that preserves the norm. For every
$f : \mathbb{K} \to \mathbb{K}$ and $j \in \mathbb{N}$, the $j$-th derivative of
$z \mapsto \overline{f(\bar z)}$ is $z \mapsto \overline{f^{(j)}(\bar z)}$.

No differentiability of $f$ is assumed: where $f$ is not differentiable, both sides use the
value that Mathlib gives to `iteratedDeriv`. -/
theorem iteratedDeriv_conj_conj (f : 𝕜 → 𝕜) (j : ℕ) :
    iteratedDeriv j (conj ∘ f ∘ conj) = conj ∘ iteratedDeriv j f ∘ conj := by
  induction j with
  | zero => simp
  | succ j ih => rw [iteratedDeriv_succ, ih, deriv_conj_conj, iteratedDeriv_succ]

end Conj

section OpenSet

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {f : 𝕜 → F} {U : Set 𝕜}

/-- Let $U \subseteq \mathbb{K}$ be open and let $f : \mathbb{K} \to F$ be $C^N$ on $U$, with
$N \in \mathbb{N}$. For $j < N$ and $b \in U$, the function $f^{(j)}$ has the derivative
$f^{(j+1)}(b)$ at $b$. -/
theorem ContDiffOn.hasDerivAt_iteratedDeriv_of_isOpen (hU : IsOpen U) {N : ℕ}
    (hf : ContDiffOn 𝕜 N f U) {j : ℕ} (hj : j < N) {b : 𝕜} (hb : b ∈ U) :
    HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f b) b := by
  have hd : DifferentiableOn 𝕜 (iteratedDerivWithin j f U) U :=
    hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hj) hU.uniqueDiffOn
  have hd' : DifferentiableOn 𝕜 (iteratedDeriv j f) U :=
    hd.congr (iteratedDerivWithin_of_isOpen hU).symm
  rw [iteratedDeriv_succ]
  exact (hd'.differentiableAt (hU.mem_nhds hb)).hasDerivAt

/-- Let $U \subseteq \mathbb{K}$ be open and let $f : \mathbb{K} \to F$ be $C^N$ on $U$, with
$N \in \mathbb{N}$. For $j \le N$, the function $f^{(j)}$ is continuous on $U$. -/
theorem ContDiffOn.continuousOn_iteratedDeriv_of_isOpen (hU : IsOpen U) {N : ℕ}
    (hf : ContDiffOn 𝕜 N f U) {j : ℕ} (hj : j ≤ N) : ContinuousOn (iteratedDeriv j f) U :=
  (hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) hU.uniqueDiffOn).congr
    (iteratedDerivWithin_of_isOpen hU).symm

/-- Let $U \subseteq \mathbb{K}$ be open, let $n \in \mathbb{N}$, and let
$G_0, G_1, \dots : \mathbb{K} \to F$ be functions such that for each $k < n$ and $b \in U$ the
function $G_k$ has the derivative $G_{k+1}(b)$ at $b$, and $G_n$ is continuous on $U$. Then
$G_0$ is $C^n$ on $U$, and $G_0^{(k)} = G_k$ on $U$ for every $k \le n$. -/
theorem contDiffOn_of_hasDerivAt_chain {G : ℕ → 𝕜 → F} (hU : IsOpen U) {n : ℕ}
    (hd : ∀ k < n, ∀ b ∈ U, HasDerivAt (G k) (G (k + 1) b) b) (hc : ContinuousOn (G n) U) :
    ContDiffOn 𝕜 n (G 0) U ∧ ∀ k ≤ n, Set.EqOn (iteratedDeriv k (G 0)) (G k) U := by
  induction n generalizing G with
  | zero =>
    refine ⟨contDiffOn_zero.2 hc, fun k hk => ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    simp [Set.EqOn]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (G := fun k => G (k + 1))
      (fun k hk b hb => hd (k + 1) (by omega) b hb) hc
    have hderiv : Set.EqOn (deriv (G 0)) (G 1) U := fun b hb => (hd 0 (by omega) b hb).deriv
    refine ⟨?_, fun k hk => ?_⟩
    · rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen hU]
      refine ⟨fun b hb => (hd 0 (by omega) b hb).differentiableAt.differentiableWithinAt, ?_,
        h1.congr hderiv⟩
      simp
    · cases k with
      | zero => simp [Set.EqOn]
      | succ k =>
        intro b hb
        rw [iteratedDeriv_succ', ← iteratedDerivWithin_of_isOpen hU hb,
          iteratedDerivWithin_congr hderiv hb, iteratedDerivWithin_of_isOpen hU hb]
        exact h2 k (by omega) hb

end OpenSet

section Composition

/-- Let $p, p'$ be formal multilinear series from $E$ to $F$ and $q, q'$ from $F$ to $G$, with
$q_k = q'_k$ and $p_k = p'_k$ for all $k \le n$. Then the Taylor compositions
(`FormalMultilinearSeries.taylorComp`) of $q$ with $p$ and of $q'$ with $p'$ agree at order $n$. -/
theorem FormalMultilinearSeries.taylorComp_congr {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {q q' : FormalMultilinearSeries 𝕜 F G}
    {p p' : FormalMultilinearSeries 𝕜 E F} {n : ℕ} (hq : ∀ k ≤ n, q k = q' k)
    (hp : ∀ k ≤ n, p k = p' k) : q.taylorComp p n = q'.taylorComp p' n := by
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition]
  rw [hq _ c.length_le]
  congr 1
  funext m
  exact hp _ (c.partSize_le m)

/-- The **derivatives of a composition depend only on the derivatives of the factors.** Let
$f, f', g, g' : \mathbb{K} \to \mathbb{K}$, let $f$ and $f'$ be $C^n$ at $x$, and let $g$ and
$g'$ be $C^n$ at $f(x)$. Suppose that $f^{(k)}(x) = f'^{(k)}(x)$ and
$g^{(k)}(f(x)) = g'^{(k)}(f(x))$ for every $k \le n$. Then
$$(g \circ f)^{(n)}(x) = (g' \circ f')^{(n)}(x).$$

This is the formal content of Faà di Bruno's formula, Mathlib's `iteratedFDeriv_comp`. Note that
$f(x) = f'(x)$ is the case $k = 0$ of the hypothesis on $f$. -/
theorem iteratedDeriv_comp_congr {𝕜 : Type*} [NontriviallyNormedField 𝕜] {f f' g g' : 𝕜 → 𝕜}
    {x : 𝕜} {n : ℕ} (hf : ContDiffAt 𝕜 n f x) (hf' : ContDiffAt 𝕜 n f' x)
    (hg : ContDiffAt 𝕜 n g (f x)) (hg' : ContDiffAt 𝕜 n g' (f x))
    (hff : ∀ k ≤ n, iteratedDeriv k f x = iteratedDeriv k f' x)
    (hgg : ∀ k ≤ n, iteratedDeriv k g (f x) = iteratedDeriv k g' (f x)) :
    iteratedDeriv n (g ∘ f) x = iteratedDeriv n (g' ∘ f') x := by
  have hx : f x = f' x := by simpa using hff 0 (Nat.zero_le n)
  rw [hx] at hg'
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    iteratedFDeriv_comp hg hf le_rfl, iteratedFDeriv_comp hg' hf' le_rfl]
  congr 1
  refine FormalMultilinearSeries.taylorComp_congr (fun k hk => ?_) (fun k hk => ?_)
  · ext
    simp only [ftaylorSeries, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    rw [hgg k hk, hx]
  · ext
    simp only [ftaylorSeries, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    rw [hff k hk]

end Composition
