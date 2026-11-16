/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Basic.Real.ENatENNReal
import Numlib.Optimization.Complexity.CarmonChain
import NumlibSurface.CartisGouldToint.Chapter04.Section01

/-!
# Cartis, Gould and Toint, Section 4.2: A lower complexity bound for finding first-order stationary points

This module formalizes §4.2 of [cartis2022evaluation], which follows Carmon, Duchi, Hinder and
Sidford. Let $\mathcal{F}(\Delta, p)$ be the class of smooth functions
$f : \mathbb{R}^n \to \mathbb{R}$, of any dimension $n$, whose $p$-th derivative is Lipschitz
continuous and with $f(0) - \inf f \le \Delta$. For a class $\mathcal{M}$ of methods, the complexity
$$\#_\varepsilon(\mathcal{M}, \mathcal{F}) = \inf_{M \in \mathcal{M}} \sup_{f \in \mathcal{F}}
  k_\varepsilon(M, f)$$
of (4.2.2) is the worst-case index of the first iterate with $\|\nabla f(x_k)\| \le \varepsilon$.
The main result, Theorem 4.2.6, is that every deterministic method of order $p$ that starts at
$x_0 = 0$ needs a number of iterations of the order of $\varepsilon^{-(p+1)/p}$ on
$\mathcal{F}(\Delta, p)$. Together with Theorem 4.1.5, this shows that ARp has the optimal order of
evaluation complexity among these methods.

The proofs are in the backbone modules `Numlib.Optimization.Complexity.ZeroChain`,
`Numlib.Optimization.Complexity.ResistingOracle` and `Numlib.Optimization.Complexity.CarmonChain`.

## Main definitions

* Section 4.2.1.1, `CartisGouldToint.Chapter04.functionClass`: the class $\mathcal{F}(\Delta, p)$,
  with the Lipschitz constant $L$ of $\nabla^p f$ explicit.
* Section 4.2.1.2, `CartisGouldToint.Chapter04.methodClassM`: the class $\mathcal{M}(p)$ of
  deterministic methods of order $p$ that start at $x_0 = 0$.
* Section 4.2.1.2, (4.2.1), `CartisGouldToint.Chapter04.methodClassZR`: the class
  $\mathcal{M}_{ZR}(p)$ of zero-respecting methods.
* (4.2.2), `CartisGouldToint.Chapter04.complexity`: the complexity
  $\#_\varepsilon(\mathcal{M}, \mathcal{F})$.
* (4.2.3), `CartisGouldToint.Chapter04.arpOracleMethod`: ARp, in the first-order case, as a method
  of $\mathcal{M}(p)$.
* (4.2.4), `Optimization.IsZeroChain`: the zero-chain property.
* (4.2.6), `CartisGouldToint.Chapter04.hardFunction`: the difficult function $f^D$.

## Main results

* Section 4.2.1.1, footnote 30, `CartisGouldToint.Chapter04.comp_adjoint_mem_functionClass`:
  $\mathcal{F}(\Delta, p)$ is invariant under orthogonal embeddings.
* (4.2.3), `CartisGouldToint.Chapter04.complexity_le_arpComplexityBound`: ARp gives the upper bound
  $\#_\varepsilon(\mathcal{M}(p), \mathcal{F}(\Delta, p)) \le \lfloor \kappa^A \Delta
  \varepsilon^{-(p+1)/p} + \kappa^C \rfloor$.
* Lemma 4.2.1, `CartisGouldToint.Chapter04.lemma_4_2_1`: zero chains are invariant under scaling.
* Lemma 4.2.2, `CartisGouldToint.Chapter04.lemma_4_2_2`: on a zero chain, the $k$-th iterate of a
  zero-respecting method vanishes in the coordinates after the $k$-th.
* Lemma 4.2.3, `CartisGouldToint.Chapter04.lemma_4_2_3`: zero-respecting methods need at least $n$
  iterations on a zero chain with large gradients.
* Theorem 4.2.4, `CartisGouldToint.Chapter04.theorem_4_2_4_i`,
  `CartisGouldToint.Chapter04.theorem_4_2_4_ii`: lower bounds for zero-respecting methods give lower
  bounds for all methods of $\mathcal{M}(p)$.
* Lemma 4.2.5 (i)–(iv), `CartisGouldToint.Chapter04.lemma_4_2_5_i`,
  `CartisGouldToint.Chapter04.lemma_4_2_5_ii`, `CartisGouldToint.Chapter04.lemma_4_2_5_iii`,
  `CartisGouldToint.Chapter04.lemma_4_2_5_iv`, `CartisGouldToint.Chapter04.lemma_4_2_5_iv_growth`:
  $f^D$ is a zero chain with large gradients, bounded below, with a Lipschitz $p$-th derivative.
* Theorem 4.2.6, `CartisGouldToint.Chapter04.theorem_4_2_6_i`: the lower bound (4.2.7).
* Theorem 4.2.6, `CartisGouldToint.Chapter04.theorem_4_2_6_ii`: $\#_\varepsilon(\mathcal{M}(p),
  \mathcal{F}(\Delta, p))$ is of exact order $\varepsilon^{-(p+1)/p}$ as $\varepsilon \to 0$, and
  ARp attains it.

## Proof outline

A zero chain is a function whose derivatives at a point with vanishing trailing coordinates do not
involve the next coordinates. A zero-respecting method applied to a zero chain therefore discovers
at most one new coordinate per iteration, and a rotation of the function reduces a general method to
a zero-respecting one (Theorem 4.2.4). The difficult function $f^D$ in $\bar k$ variables is a zero
chain whose gradient is large until all $\bar k$ coordinates are discovered. Scaling $f^D$ to the
class $\mathcal{F}(\Delta, p)$ gives the lower bound.

## Conventions

* Functions are on $\mathbb{R}^n$ = `EuclideanSpace ℝ (Fin n)`, with $n$ arbitrary. A function of
  variable dimension is a pair `⟨n, f⟩ : Σ n, EuclideanSpace ℝ (Fin n) → ℝ`.
* Coordinates are $0$-based in Lean: the coordinate $[x]_j$, $j \in \{1, \dots, n\}$, of the source
  is `x ⟨j - 1, _⟩`, and the Lean coordinate vector with index `j` is `EuclideanSpace.single j 1`.
* The index $k_\varepsilon(M, f)$ and the complexities are in `ℕ∞`. The index is `⊤` when no iterate
  is $\varepsilon$-stationary. Complexities are compared with real numbers in `ℝ≥0∞`.

## Deviations from the source

* **(4.2.6)** (typo). The first term of $f^D$ is $-\Psi(1) \Phi([x]_1)$, as in Carmon et al., not
  the printed $-\Psi([x]_1) \Phi([x]_1)$, with which Lemma 4.2.5 (ii) fails at $x = 0$. See
  `CartisGouldToint.Chapter04.hardFunction`.
* **Theorem 4.2.6** (correction). The proof gives $\#_\varepsilon \ge \bar k$ for both classes, not
  $\#_\varepsilon(\mathcal{M}(p), \mathcal{F}(\Delta, p)) \ge 2 \bar k$, and the form (4.2.7) with
  $c_0$ needs $\varepsilon$ small. See `CartisGouldToint.Chapter04.theorem_4_2_6_i`.
* **Theorem 4.2.6, tightness of (4.2.3)** (reading). Only the order in $\varepsilon$ is tight, and
  the upper bound uses $L_{f,p} = \max(1, L)$ and an integer part. See
  `CartisGouldToint.Chapter04.theorem_4_2_6_ii`.
* **Lemma 4.2.5 (i)** (generalization). The lemma is stated for every $p$, not only for $p \ge 1$.
  See `CartisGouldToint.Chapter04.lemma_4_2_5_i`.
* **Lemma 4.2.5 (iv)** (reading). The absolute constant of the growth bound is $c_1 = 20$. See
  `CartisGouldToint.Chapter04.lemma_4_2_5_iv_growth`.
* **$\mathcal{F}(\Delta, p)$** (reading). The members are $C^\infty$, as in footnote 29, and the
  Lipschitz constant is explicit. See `CartisGouldToint.Chapter04.functionClass`.
* **(4.2.1), zero-respecting methods** (reading). Zero respect is defined through null directions of
  the derivative tensors. See `CartisGouldToint.Chapter04.methodClassZR`.
* **Footnote 30 and Theorem 4.2.4** (reading). They assume $L \ge 0$. See
  `CartisGouldToint.Chapter04.comp_adjoint_mem_functionClass` and
  `CartisGouldToint.Chapter04.theorem_4_2_4_i`.
* **Lemmas 4.2.2, 4.2.3 and Theorem 4.2.4** (generalization). The unused hypotheses
  $\varepsilon > 0$, $p \ge 1$ and, for Lemma 4.2.2, $f \in \mathcal{F}(\Delta, p)$ are dropped. See
  `CartisGouldToint.Chapter04.lemma_4_2_2`.
* **Lemma 4.2.3** (typo). The source cites (4.2.3) for $\#_\varepsilon$; the definition is (4.2.2).
  See `CartisGouldToint.Chapter04.lemma_4_2_3`.
-/

open Set Optimization
open scoped ContDiff

namespace CartisGouldToint.Chapter04

variable {n p : ℕ}

/-! ### §4.2.1 Problems and methods of interest -/

/-- **Section 4.2.1.1** of [cartis2022evaluation], the function class $\mathcal{F}(\Delta, p)$. Let
$\Delta, L \in \mathbb{R}$ and $p \in \mathbb{N}$. The class consists of the functions
$f : \mathbb{R}^n \to \mathbb{R}$, of any dimension $n$, that are infinitely differentiable,
whose $p$-th derivative is Lipschitz continuous on $\mathbb{R}^n$ with constant $L$ (f.DpL),
that are bounded below (f.Bb), and that satisfy $f(0) - \inf_x f(x) \le \Delta$.

**Reading.** The members are $C^\infty$, as in footnote 29 of the source, and the Lipschitz
constant $L$ of $\nabla^p f$ is an explicit parameter of the class.

An element of the class is a pair `⟨n, f⟩ : Σ n, EuclideanSpace ℝ (Fin n) → ℝ`. The class is the
backbone class `Optimization.smoothClass Δ L p`. Unlike
`CartisGouldToint.Chapter04.AssumptionDpL`, it does not require $L \ge 1$. -/
def functionClass (Δ L : ℝ) (p : ℕ) : Set (Σ n, EuclideanSpace ℝ (Fin n) → ℝ) :=
  smoothClass Δ L p

/-- The class $\mathcal{F}(\Delta, p)$ is the backbone class `Optimization.smoothClass Δ L p`. -/
theorem functionClass_eq (Δ L : ℝ) (p : ℕ) : functionClass Δ L p = smoothClass Δ L p := rfl

/-- A function $f : \mathbb{R}^n \to \mathbb{R}$ is in $\mathcal{F}(\Delta, p)$ if and only if it is
$C^\infty$, its $p$-th derivative is $L$-Lipschitz on $\mathbb{R}^n$, it is bounded below, and
$f(0) - \inf_x f(x) \le \Delta$. -/
theorem mem_functionClass {Δ L : ℝ} {F : Σ n, EuclideanSpace ℝ (Fin n) → ℝ} :
    F ∈ functionClass Δ L p ↔ ContDiff ℝ ∞ F.2 ∧ IteratedFDerivLipschitzOn F.2 p L univ ∧
      BddBelow (range F.2) ∧ F.2 0 - ⨅ x, F.2 x ≤ Δ :=
  Iff.rfl

/-- **Section 4.2.1.1** of [cartis2022evaluation], footnote 30: the class $\mathcal{F}(\Delta, p)$
is invariant under orthogonal embeddings. Let $L \ge 0$, let $f : \mathbb{R}^n \to \mathbb{R}$
be in $\mathcal{F}(\Delta, p)$, and let $U \in O(m, n)$, that is, a linear isometry
$U : \mathbb{R}^n \to \mathbb{R}^m$. Then $f_U = f \circ U^T : \mathbb{R}^m \to \mathbb{R}$ is
in $\mathcal{F}(\Delta, p)$.

**Reading.** The source does not state the condition $L \ge 0$ on the Lipschitz constant.

The adjoint $U^T$ is `Optimization.isometryAdjoint U`. -/
theorem comp_adjoint_mem_functionClass {Δ L : ℝ} (hL : 0 ≤ L) {m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ⟨n, f⟩ ∈ functionClass Δ L p)
    (U : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) :
    ⟨m, f ∘ isometryAdjoint U⟩ ∈ functionClass Δ L p :=
  comp_adjoint_mem_smoothClass hL hf U

/-- **Section 4.2.1.2** of [cartis2022evaluation], the class $\mathcal{M}(p)$ of deterministic
methods of order $p$. A method of the class consists of one method in every dimension $n$. It
starts at $x_0 = 0$, and its iterate $x_{k+1}$ is a function of the values
$f(x_i), \nabla f(x_i), \dots, \nabla^p f(x_i)$ at the previous iterates $x_i$, $i \le k$.

A method is an element of `Optimization.JetMethod p`, and the class is
`Optimization.methodClass p`. The iterates of a method $M$ on $f : \mathbb{R}^n \to \mathbb{R}$
are `M.iter n f`. -/
abbrev methodClassM (p : ℕ) : Set (JetMethod p) := methodClass p

/-- **Section 4.2.1.2** of [cartis2022evaluation], (4.2.1): the class $\mathcal{M}_{ZR}(p)$ of
zero-respecting methods. A method of $\mathcal{M}(p)$ is zero-respecting if, for every function
$f$ in every dimension and every $k$, the coordinate $[x_{k+1}]_j$ is $0$ whenever $e_j$ is a
null direction of $\nabla^q f(x_i)$ for all $q \in \{1, \dots, p\}$ and all $i \le k$.

**Reading.** A vector $e_j$ is a null direction of a multilinear map if the map vanishes
whenever one of its arguments is $e_j$. For the symmetric derivatives of a $C^p$ function this
is the condition $\nabla^q f(x_i) e_j = 0$ of the source.

The class is `Optimization.zeroRespectingClass p`, and null directions are
`Optimization.IsNullDirection`. -/
abbrev methodClassZR (p : ℕ) : Set (JetMethod p) := zeroRespectingClass p

/-- Every zero-respecting method is in $\mathcal{M}(p)$:
$\mathcal{M}_{ZR}(p) \subseteq \mathcal{M}(p)$. -/
theorem methodClassZR_subset : methodClassZR p ⊆ methodClassM p :=
  zeroRespectingClass_subset_methodClass

/-- **(4.2.2)** of [cartis2022evaluation], the complexity of a class of methods on a class of
functions. For a method $M$ and a function $f$, let $k_\varepsilon(M, f) \in \mathbb{N} \cup
\{\infty\}$ be the index of the first iterate $x_k$ of $M$ on $f$ with
$\|\nabla f(x_k)\| \le \varepsilon$, and $k_\varepsilon(M, f) = \infty$ if there is none. Then
$$\#_\varepsilon(\mathcal{M}, \mathcal{F}) = \inf_{M \in \mathcal{M}} \sup_{f \in \mathcal{F}}
  k_\varepsilon(M, f).$$

The definition is `Optimization.classComplexity`, with values in `ℕ∞`, and the index
$k_\varepsilon(M, f)$ is `Optimization.firstStationaryIndex`. At a point where $f$ is not
differentiable the derivative is taken to be $0$, so such a point counts as stationary; the
members of $\mathcal{F}(\Delta, p)$ are differentiable. -/
noncomputable abbrev complexity (𝓜 : Set (JetMethod p))
    (𝓕 : Set (Σ n, EuclideanSpace ℝ (Fin n) → ℝ)) (ε : ℝ) : ℕ∞ :=
  classComplexity 𝓜 𝓕 ε

/-! ### §4.2.2 Zero chains -/

/-- **Lemma 4.2.1** of [cartis2022evaluation] (scale invariance of zero chains). Let
$f : \mathbb{R}^n \to \mathbb{R}$ be a zero chain of order $p$ (4.2.4), let
$\mu_1 \in \mathbb{R}$ and let $\mu_2 \neq 0$. Then $x \mapsto \mu_1 f(x/\mu_2)$ is a zero chain
of order $p$.

A zero chain is `Optimization.IsZeroChain`. With $0$-based indices, it means: if $[x]_i = 0$ for
all $i \ge j$, then the coordinate vectors $e_i$, $i > j$, are null directions of
$\nabla^q f(x)$ for every $q \in \{1, \dots, p\}$. -/
theorem lemma_4_2_1 {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsZeroChain f p) (μ₁ : ℝ) {μ₂ : ℝ}
    (hμ₂ : μ₂ ≠ 0) : IsZeroChain (fun x => μ₁ * f (μ₂⁻¹ • x)) p :=
  hf.comp_smul μ₁ hμ₂

/-- **Lemma 4.2.2** of [cartis2022evaluation] (zero-respecting methods applied to zero chains). Let
$M \in \mathcal{M}_{ZR}(p)$ and let $f : \mathbb{R}^n \to \mathbb{R}$ be a zero chain of order
$p$. Then the iterates of $M$ on $f$ satisfy $[x_k]_j = 0$ for all $j \in \{k + 1, \dots, n\}$.

**Generalization.** The hypotheses $\varepsilon > 0$, $p \ge 1$ and
$f \in \mathcal{F}(\Delta, p)$ of the source are not used and are dropped.

With $0$-based indices the conclusion is `M.iter n f k j = 0` for every `j : Fin n` with
$k \le j$. -/
theorem lemma_4_2_2 {M : JetMethod p} (hM : M ∈ methodClassZR p)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsZeroChain f p) (k : ℕ) (j : Fin n) (hkj : k ≤ j) :
    M.iter n f k j = 0 :=
  (hM n f).iterate_apply_eq_zero hf k j hkj

/-- **Lemma 4.2.3** of [cartis2022evaluation] (zero-respecting methods are slow on zero chains). Let
$f : \mathbb{R}^n \to \mathbb{R}$ be in $\mathcal{F}(\Delta, p)$ and be a zero chain of order
$p$, and suppose that $\|\nabla f(x)\| > \varepsilon$ for every $x$ with $[x]_n = 0$ (4.2.5).
Then
$$\#_\varepsilon(\mathcal{M}_{ZR}(p), \mathcal{F}(\Delta, p)) \ge
  \#_\varepsilon(\mathcal{M}_{ZR}(p), \{f\}) \ge n.$$

**Generalization.** The hypotheses $\varepsilon > 0$ and $p \ge 1$ of the source are not used
and are dropped.

**Typo.** The source cites (4.2.3) for $\#_\varepsilon$; the definition is (4.2.2).

The condition $[x]_n = 0$ is `x ⟨n - 1, _⟩ = 0` with $0$-based indices, and the hypothesis on
the gradient is required only for $n \ge 1$. -/
theorem lemma_4_2_3 {Δ L ε : ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : ⟨n, f⟩ ∈ functionClass Δ L p) (hf : IsZeroChain f p)
    (hgrad : ∀ (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)), x ⟨n - 1, by omega⟩ = 0 →
      ε < ‖fderiv ℝ f x‖) :
    complexity (methodClassZR p) {⟨n, f⟩} ε ≤ complexity (methodClassZR p) (functionClass Δ L p) ε ∧
      (n : ℕ∞) ≤ complexity (methodClassZR p) {⟨n, f⟩} ε :=
  ⟨classComplexity_mono_right (singleton_subset_iff.2 hF),
    (le_classComplexity_of_isZeroChain hf hgrad hF).1⟩

/-- Every member of $\mathcal{F}(\Delta, p)$ is $C^p$ and differentiable. -/
theorem contDiff_differentiable_of_mem_functionClass {Δ L : ℝ}
    {F : Σ n, EuclideanSpace ℝ (Fin n) → ℝ} (hF : F ∈ functionClass Δ L p) :
    ContDiff ℝ p F.2 ∧ Differentiable ℝ F.2 :=
  ⟨hF.1.of_le (by exact_mod_cast le_top), hF.1.differentiable (by simp)⟩

/-- **Theorem 4.2.4** of [cartis2022evaluation], first part. Let $L \ge 0$. For every $\varepsilon$,
$$\#_\varepsilon(\mathcal{M}(p), \mathcal{F}(\Delta, p)) \ge \#_\varepsilon(\mathcal{M}_{ZR}(p),
  \mathcal{F}(\Delta, p)).$$

**Reading.** The source does not state the condition $L \ge 0$ on the Lipschitz constant.

**Generalization.** The hypotheses $\varepsilon > 0$ and $p \ge 1$ of the source are not used
and are dropped.

The source cites Carmon et al. for the proof. The backbone proves the theorem with a resisting
oracle (`Numlib.Optimization.Complexity.ResistingOracle`). -/
theorem theorem_4_2_4_i {Δ L : ℝ} (hL : 0 ≤ L) (ε : ℝ) :
    complexity (methodClassZR p) (functionClass Δ L p) ε ≤
      complexity (methodClassM p) (functionClass Δ L p) ε :=
  classComplexity_zeroRespecting_le _ (fun _ hF _ U => comp_adjoint_mem_functionClass hL hF U)
    (fun _ hF => contDiff_differentiable_of_mem_functionClass hF) ε

/-- **Theorem 4.2.4** of [cartis2022evaluation], second part. Let $L \ge 0$, let
$f : \mathbb{R}^n \to \mathbb{R}$ be in $\mathcal{F}(\Delta, p)$, let $\bar k \in \mathbb{N}$,
and suppose that $\#_\varepsilon(\mathcal{M}_{ZR}(p), \{f\}) \ge \bar k$. Let $\{f_U\}$ be the
set of all functions $f_U = f \circ U^T : \mathbb{R}^{n + \bar k} \to \mathbb{R}$ with
$U \in O(n + \bar k, n)$. Then
$$\#_\varepsilon(\mathcal{M}(p), \mathcal{F}(\Delta, p)) \ge \#_\varepsilon(\mathcal{M}(p),
  \{f_U\}) \ge \bar k.$$

**Reading.** The source does not state the condition $L \ge 0$ on the Lipschitz constant.

**Generalization.** The hypotheses $\varepsilon > 0$ and $p \ge 1$ of the source are not used
and are dropped.

The matrices $U \in O(n + \bar k, n)$ are the linear isometries
$\mathbb{R}^n \to \mathbb{R}^{n + \bar k}$, and $U^T$ is `Optimization.isometryAdjoint U`. -/
theorem theorem_4_2_4_ii {Δ L ε : ℝ} (hL : 0 ≤ L) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : ⟨n, f⟩ ∈ functionClass Δ L p) {k : ℕ}
    (hk : (k : ℕ∞) ≤ complexity (methodClassZR p) {⟨n, f⟩} ε) :
    complexity (methodClassM p) {F | ∃ U : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin (n + k)), F = ⟨n + k, f ∘ isometryAdjoint U⟩} ε ≤
        complexity (methodClassM p) (functionClass Δ L p) ε ∧
      (k : ℕ∞) ≤ complexity (methodClassM p) {F | ∃ U : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin (n + k)), F = ⟨n + k, f ∘ isometryAdjoint U⟩} ε := by
  obtain ⟨hc, hd⟩ := contDiff_differentiable_of_mem_functionClass hF
  refine ⟨classComplexity_mono_right ?_, le_classComplexity_comp_adjoint _ hc hd hk⟩
  rintro _ ⟨U, rfl⟩
  exact comp_adjoint_mem_functionClass hL hF U

/-! ### The difficult function -/

/-- **(4.2.6)** of [cartis2022evaluation], the difficult function
$f^D : \mathbb{R}^{\bar k} \to \mathbb{R}$:
$$f^D(x) = -\Psi(1) \Phi([x]_1) + \sum_{i=2}^{\bar k} \left[\Psi(-[x]_{i-1}) \Phi(-[x]_i) -
  \Psi([x]_{i-1}) \Phi([x]_i)\right],$$
where $\Psi(y) = 0$ for $y \le 1/2$, $\Psi(y) = \exp(1 - (2y - 1)^{-2})$ for $y > 1/2$, and
$\Phi(y) = e^{1/2} \int_{-\infty}^y e^{-t^2/2}\, dt$.

**Typo.** The source prints the first term as $-\Psi([x]_1) \Phi([x]_1)$. With that term
$\nabla f^D(0) = 0$, and Lemma 4.2.5 (ii) fails at $x = 0$. The first term here is
$-\Psi(1) \Phi([x]_1)$, as in Carmon et al.

The function is `Optimization.CarmonChain.chain`. The function $\Psi$ is
`Optimization.CarmonChain.psi`, and the function
$\Phi$ is `Optimization.CarmonChain.phi`. -/
noncomputable def hardFunction (k : ℕ) : EuclideanSpace ℝ (Fin k) → ℝ :=
  CarmonChain.chain k

/-- The difficult function $f^D$ is the backbone function `Optimization.CarmonChain.chain`. -/
theorem hardFunction_eq (k : ℕ) : hardFunction k = CarmonChain.chain k := rfl

/-- **Lemma 4.2.5 (i)** of [cartis2022evaluation]. For every $\bar k$ and every $p$, the difficult
function $f^D$ is a zero chain of order $p$.

**Generalization.** The source states the lemma for $p \ge 1$. The statement holds for every
$p$, and it is vacuous for $p = 0$. -/
theorem lemma_4_2_5_i (k p : ℕ) : IsZeroChain (hardFunction k) p :=
  CarmonChain.isZeroChain_chain p

/-- **Lemma 4.2.5 (ii)** of [cartis2022evaluation]. Let $x \in \mathbb{R}^{\bar k}$ and suppose that
$|[x]_i| < 1$ for some $i$. Then there is $j \le i$ with $|[x]_j| < 1$ and
$$\|\nabla f^D(x)\| \ge \left|\frac{\partial f^D}{\partial [x]_j}(x)\right| > 1.$$

This part needs the corrected first term of (4.2.6) (`CartisGouldToint.Chapter04.hardFunction`).
The partial derivative is `fderiv ℝ (hardFunction k) x (EuclideanSpace.single j 1)`, and the
indices are $0$-based. -/
theorem lemma_4_2_5_ii {k : ℕ} {x : EuclideanSpace ℝ (Fin k)} {i : Fin k} (hi : |x i| < 1) :
    ∃ j : Fin k, j ≤ i ∧ |x j| < 1 ∧
      |fderiv ℝ (hardFunction k) x (EuclideanSpace.single j 1)| ≤
        ‖fderiv ℝ (hardFunction k) x‖ ∧
      1 < |fderiv ℝ (hardFunction k) x (EuclideanSpace.single j 1)| := by
  obtain ⟨j, hji, hxj, hj, -⟩ := CarmonChain.exists_abs_partial_chain_gt_one hi
  refine ⟨j, hji, hxj, ?_, hj⟩
  rw [← Real.norm_eq_abs]
  refine ((fderiv ℝ (hardFunction k) x).le_opNorm _).trans_eq ?_
  simp

/-- **Lemma 4.2.5 (iii)** of [cartis2022evaluation]. For every $\bar k$, the difficult function
$f^D$ is bounded below on $\mathbb{R}^{\bar k}$, and
$$f^D(0) - f^D_{\text{low}} \le 12 \bar k, \qquad f^D_{\text{low}} = \inf_x f^D(x).$$
-/
theorem lemma_4_2_5_iii (k : ℕ) :
    BddBelow (range (hardFunction k)) ∧ hardFunction k 0 - ⨅ x, hardFunction k x ≤ 12 * k :=
  CarmonChain.chain_zero_sub_iInf_le

/-- **Lemma 4.2.5 (iv)** of [cartis2022evaluation], without the growth estimate. Let $p \ge 1$.
There is a constant $L^D_p > 0$, independent of $\bar k$, such that for every $\bar k$ the
$p$-th derivative of $f^D$ is Lipschitz continuous on $\mathbb{R}^{\bar k}$ with constant
$L^D_p$ (f.DpL).

The constant is explicit: $L^D_p$ is `Optimization.CarmonChain.lipschitzConst p`, a bound on
$\|\nabla^{p+1} f^D\|$ that does not depend on $\bar k$. -/
theorem lemma_4_2_5_iv {p : ℕ} (hp : 1 ≤ p) :
    0 < CarmonChain.lipschitzConst p ∧ ∀ k : ℕ,
      IteratedFDerivLipschitzOn (hardFunction k) p (CarmonChain.lipschitzConst p) univ :=
  ⟨CarmonChain.lipschitzConst_pos p, fun _ => CarmonChain.lipschitzOn_iteratedFDeriv_chain hp⟩

/-- **Lemma 4.2.5 (iv)** of [cartis2022evaluation], with the growth estimate. There is an absolute
constant $c_1 > 0$ such that for every $p \ge 1$ the following holds: for every $\bar k$ the
$p$-th derivative of $f^D$ is Lipschitz continuous on $\mathbb{R}^{\bar k}$ with the constant
$L^D_p$, which does not depend on $\bar k$, and
$$L^D_p \le \exp\left(\tfrac{5}{2} p \log p + c_1 p\right).$$

**Reading.** The source leaves the absolute constant $c_1$ unspecified. One may take $c_1 = 20$
(`Optimization.CarmonChain.lipschitzConst_le_exp_twenty`).

The constant $L^D_p$ is `Optimization.CarmonChain.lipschitzConst p`. -/
theorem lemma_4_2_5_iv_growth :
    ∃ c₁ > 0, ∀ p : ℕ, 1 ≤ p →
      (∀ k : ℕ, IteratedFDerivLipschitzOn (hardFunction k) p (CarmonChain.lipschitzConst p) univ) ∧
        CarmonChain.lipschitzConst p ≤ Real.exp (5 / 2 * p * Real.log p + c₁ * p) := by
  obtain ⟨c₁, hc₁, h⟩ := CarmonChain.lipschitzConst_le_exp
  exact ⟨c₁, hc₁, fun p hp => ⟨(lemma_4_2_5_iv hp).2, h p hp⟩⟩

/-! ### The lower bound -/

/-- $\lfloor x \rfloor \ge x/2$ for $x \ge 1$. -/
private theorem div_two_le_floor {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ ⌊x⌋₊ := by
  have h := Nat.lt_floor_add_one x
  have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.le_floor (by simpa using hx)
  linarith

/-- **Theorem 4.2.6** of [cartis2022evaluation] (lower complexity bound). Let $p \ge 1$ and
$\Delta, L, \varepsilon > 0$, let $L^D_p$ be the constant of Lemma 4.2.5 (iv), and let
$$Y = \Delta \left(\frac{L}{L^D_p}\right)^{1/p} \varepsilon^{-(p+1)/p}.$$
Then $\#_\varepsilon(\mathcal{M}(p), \mathcal{F}(\Delta, p)) \ge
\#_\varepsilon(\mathcal{M}_{ZR}(p), \mathcal{F}(\Delta, p))$, and both complexities are at least
$\lfloor Y/12 \rfloor$. Consequently, if $Y \ge 12$, then both complexities are at least $c_0 Y$
with $c_0 = 1/24$; this is (4.2.7).

**Correction.** With $\bar k = \lfloor Y/12 \rfloor$, the source states
$\#_\varepsilon(\mathcal{M}(p), \mathcal{F}(\Delta, p)) \ge 2 \bar k$. This does not follow from
Theorem 4.2.4, and the proof gives only $\#_\varepsilon \ge \bar k$ for both classes. The form
(4.2.7) with $c_0$ needs $Y \ge 12$, that is, $\varepsilon$ small enough: for large
$\varepsilon$ the complexity is $0$.

The comparison with the real number $c_0 Y$ is made in `ℝ≥0∞`. The constant $L^D_p$ is
`Optimization.CarmonChain.lipschitzConst p`. -/
theorem theorem_4_2_6_i (hp : 1 ≤ p) {Δ L ε : ℝ} (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) :
    let Y := Δ * (L / CarmonChain.lipschitzConst p) ^ (1 / p : ℝ) * ε ^ (-((p + 1 : ℝ) / p))
    complexity (methodClassZR p) (functionClass Δ L p) ε ≤
        complexity (methodClassM p) (functionClass Δ L p) ε ∧
      ((⌊Y / 12⌋₊ : ℕ) : ℕ∞) ≤ complexity (methodClassZR p) (functionClass Δ L p) ε ∧
      ((⌊Y / 12⌋₊ : ℕ) : ℕ∞) ≤ complexity (methodClassM p) (functionClass Δ L p) ε ∧
      (12 ≤ Y → ENNReal.ofReal (1 / 24 * Y) ≤
        (complexity (methodClassZR p) (functionClass Δ L p) ε : ENNReal) ∧
        ENNReal.ofReal (1 / 24 * Y) ≤
          (complexity (methodClassM p) (functionClass Δ L p) ε : ENNReal)) := by
  intro Y
  have hY : Y / 12 = Δ / 12 * (L / CarmonChain.lipschitzConst p) ^ (1 / p : ℝ) *
      ε ^ (-((p + 1 : ℝ) / p)) := by simp only [Y]; ring
  obtain ⟨h1, h2⟩ := CarmonChain.le_classComplexity_smoothClass_methodClass hp hΔ hL hε
  rw [← hY] at h1 h2
  have hc : ∀ c : ℕ∞, ((⌊Y / 12⌋₊ : ℕ) : ℕ∞) ≤ c → 12 ≤ Y →
      ENNReal.ofReal (1 / 24 * Y) ≤ (c : ENNReal) := by
    intro c hc hY12
    refine le_trans ?_ (ENat.toENNReal_le.2 hc)
    rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    have := div_two_le_floor (x := Y / 12) (by linarith)
    linarith
  exact ⟨theorem_4_2_4_i hL.le ε, h1, h2, fun hY12 => ⟨hc _ h1 hY12, hc _ h2 hY12⟩⟩

/-! ### ARp as a method of $\mathcal{M}(p)$ and the tightness of the lower bound -/

namespace ARpOracle

/-- The Taylor polynomial of degree $p$ built from the oracle answer at $x$ is the Taylor polynomial
of $f$ at $x$. -/
theorem taylorSum_jetSeries_jetOracle (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (jetSeries (jetOracle f p x)).taylorSum p = (ftaylorSeries ℝ f x).taylorSum p :=
  FormalMultilinearSeries.taylorSum_congr fun _ hi => jetSeries_jetOracle f x hi

/-- The model (4.1.2) built from the oracle answer at $x$ is the model built from the Taylor series
of $f$ at $x$. -/
theorem regularizedModel_jetSeries_jetOracle (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (σ : ℝ) :
    regularizedModel (jetSeries (jetOracle f p x)) p σ =
      regularizedModel (ftaylorSeries ℝ f x) p σ := by
  funext s
  rw [regularizedModel_def, regularizedModel_def, taylorSum_jetSeries_jetOracle]

/-- The decrease $T_{f,p}(x, 0) - T_{f,p}(x, s)$ built from the oracle answer at $x$ is the one
built from the Taylor series of $f$ at $x$. -/
theorem taylorDecrement_jetSeries_jetOracle (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) :
    (jetSeries (jetOracle f p x)).taylorDecrement p s =
      (ftaylorSeries ℝ f x).taylorDecrement p s := by
  simp only [FormalMultilinearSeries.taylorDecrement_def, taylorSum_jetSeries_jetOracle]

/-- The first-order termination test (4.1.5) on an oracle answer $J = (J_0, \dots, J_p)$:
$\|J_1\| \le \varepsilon$. -/
def jetTest (ε : ℝ) (J : Jet (EuclideanSpace ℝ (Fin n)) p) : Prop :=
  ‖jetSeries J 1‖ ≤ ε

/-- For $p \ge 1$, the test on the oracle answer at $x$ holds if and only if
$\|\nabla f(x)\| \le \varepsilon$. -/
theorem jetTest_jetOracle (hp : 1 ≤ p) {ε : ℝ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    jetTest ε (jetOracle f p x) ↔ ‖gradient f x‖ ≤ ε := by
  rw [jetTest, jetSeries_jetOracle f x hp, norm_gradient_eq]
  simp [ftaylorSeries]

/-- The state of ARp: the iterate, the regularization weight, and the oracle answer at the iterate.
-/
abbrev State (n p : ℕ) :=
  EuclideanSpace ℝ (Fin n) × ℝ × Jet (EuclideanSpace ℝ (Fin n)) p

/-- The step of ARp at a state: a global minimizer of the model (4.1.2), chosen with the axiom of
choice, which exists in finite dimension for $\sigma > 0$ and $p \ge 1$. In the other cases the
step is $0$. -/
noncomputable def step (st : State n p) : EuclideanSpace ℝ (Fin n) :=
  if h : 0 < st.2.1 ∧ 1 ≤ p then
    Classical.choose (exists_isMinOn_regularizedModel (D := jetSeries st.2.2) h.1 h.2)
  else 0

/-- For $\sigma > 0$ and $p \ge 1$, the step of ARp is a global minimizer of the model (4.1.2). -/
theorem isMinOn_step {st : State n p} (hσ : 0 < st.2.1) (hp : 1 ≤ p) :
    IsMinOn (regularizedModel (jetSeries st.2.2) p st.2.1) univ (step st) := by
  rw [step, dite_eq_left ⟨hσ, hp⟩]
  exact (Classical.choose_spec
    (exists_isMinOn_regularizedModel (D := jetSeries st.2.2) hσ hp)).1

/-- The ratio (4.1.15) of ARp, computed from the oracle answer at the iterate $x$ and the answer $a$
at the trial point $x + s$: $(f(x) - f(x + s))/(T_{f,p}(x, 0) - T_{f,p}(x, s))$. -/
noncomputable def ratio (st : State n p) (a : Jet (EuclideanSpace ℝ (Fin n)) p) : ℝ :=
  (jetValue st.2.2 - jetValue a) / (jetSeries st.2.2).taylorDecrement p (step st)

open Classical in
/-- One iteration of ARp, given the answer $a$ of the oracle at the trial point. After termination
the state does not change. Otherwise, if $\rho \ge \eta_1$, the trial point and its answer are
accepted with the same weight, and if $\rho < \eta_1$, the iterate is kept and the weight is
multiplied by $\gamma_2$. -/
noncomputable def update (P : ARpParams) (ε : ℝ) (st : State n p)
    (a : Jet (EuclideanSpace ℝ (Fin n)) p) : State n p :=
  if jetTest ε st.2.2 then st
  else if P.η₁ ≤ ratio st a then (st.1 + step st, st.2.1, a) else (st.1, P.γ₂ * st.2.1, st.2.2)

open Classical in
/-- The next query of ARp at a state: the trial point $x_k + s_k$, or $x_k$ after termination. -/
noncomputable def query (ε : ℝ) (st : State n p) : EuclideanSpace ℝ (Fin n) :=
  if jetTest ε st.2.2 then st.1 else st.1 + step st

/-- The states of ARp reconstructed from a sequence $a$ of oracle answers: the state
$(0, \sigma_0, a_0)$, followed by the iterations `CartisGouldToint.Chapter04.ARpOracle.update`. -/
noncomputable def states (P : ARpParams) (ε : ℝ) (a : ℕ → Jet (EuclideanSpace ℝ (Fin n)) p) :
    ℕ → State n p
  | 0 => (0, P.σ₀, a 0)
  | k + 1 => update P ε (states P ε a k) (a (k + 1))

/-- The $k$-th reconstructed state depends only on the answers $a_0, \dots, a_k$. -/
theorem states_congr (P : ARpParams) (ε : ℝ) {a a' : ℕ → Jet (EuclideanSpace ℝ (Fin n)) p} :
    ∀ k, (∀ i ≤ k, a i = a' i) → states P ε a k = states P ε a' k
  | 0, h => by simp [states, h 0 le_rfl]
  | k + 1, h => by
    simp only [states]
    rw [states_congr P ε k fun i hi => h i (hi.trans k.le_succ), h (k + 1) le_rfl]

end ARpOracle

open ARpOracle in
/-- **(4.2.3)** of [cartis2022evaluation]: ARp as a deterministic method of order $p$, in the
first-order case with tolerance $\varepsilon$. In every dimension the method starts at
$x_0 = 0$. The state $(x_k, \sigma_k, J_k)$, with $J_k$ the oracle answer at $x_k$, is
reconstructed from the oracle answers. The next query is the trial point $x_k + s_k$, where
$s_k$ is a global minimizer of the model (4.1.2), and the trial point is accepted if and only if
$\rho_k \ge \eta_1$ (4.1.15). Of the updates that (4.1.16) admits, the method takes
$\sigma_{k+1} = \sigma_k$ after a successful iteration and $\sigma_{k+1} = \gamma_2 \sigma_k$
after an unsuccessful one. Once $\|\nabla f(x_k)\| \le \varepsilon$, the method repeats $x_k$.

In the oracle model of §4.2 every query returns the full answer $f, \nabla f, \dots, \nabla^p f$
at the trial point, although ARp itself needs the derivatives only after successful iterations.
So $k$ iterations of the method correspond to $k + 1$ evaluations of $f$. The global minimizer
is chosen with the axiom of choice (`CartisGouldToint.Chapter04.ARpOracle.step`). -/
noncomputable def arpOracleMethod (P : ARpParams) (ε : ℝ) : JetMethod p := fun _ =>
  { x₀ := 0
    next := fun k b => query ε (states P ε (fun i => if h : i < k + 1 then b ⟨i, h⟩ else 0) k) }

/-- ARp is a method of the class $\mathcal{M}(p)$. -/
theorem arpOracleMethod_mem (P : ARpParams) (ε : ℝ) :
    arpOracleMethod (p := p) P ε ∈ methodClassM p :=
  fun _ => rfl

namespace ARpOracle

variable (P : ARpParams) (ε : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)

/-- The oracle answers at the queries of ARp on $f$. -/
noncomputable def answers (p : ℕ) (k : ℕ) : Jet (EuclideanSpace ℝ (Fin n)) p :=
  jetOracle f p ((arpOracleMethod (p := p) P ε).iter n f k)

/-- The query $k + 1$ of ARp on $f$ is the query of the $k$-th reconstructed state. -/
theorem iter_succ (k : ℕ) :
    (arpOracleMethod (p := p) P ε).iter n f (k + 1) = query ε (states P ε (answers P ε f p) k) := by
  rw [JetMethod.iter_eq, OracleMethod.iterate_succ]
  exact congrArg (query ε) (states_congr P ε k fun i hi => by
    rw [dite_eq_left (Nat.lt_succ_of_le hi)]; rfl)

/-- The first query of ARp is $x_0 = 0$. -/
theorem iter_zero : (arpOracleMethod (p := p) P ε).iter n f 0 = 0 := rfl

variable {P ε f}

/-- The invariant of the reconstruction: the answer in the $k$-th state is the oracle answer at its
iterate, the iterate is one of the queries $0, \dots, k$, and the weight is at least
$\sigma_{\min}$. -/
theorem states_spec (k : ℕ) :
    (states P ε (answers P ε f p) k).2.2 = jetOracle f p (states P ε (answers P ε f p) k).1 ∧
      (∃ j ≤ k, (states P ε (answers P ε f p) k).1 = (arpOracleMethod (p := p) P ε).iter n f j) ∧
      P.σmin ≤ (states P ε (answers P ε f p) k).2.1 := by
  induction k with
  | zero => exact ⟨rfl, ⟨0, le_rfl, rfl⟩, P.σmin_le_σ₀⟩
  | succ k ih =>
    obtain ⟨hJ, ⟨j, hj, hx⟩, hσ⟩ := ih
    have hσ0 : 0 ≤ (states P ε (answers P ε f p) k).2.1 := P.σmin_nonneg.trans hσ
    have hq := iter_succ (p := p) P ε f k
    simp only [states, update]
    split_ifs with ht hs
    · exact ⟨hJ, ⟨j, hj.trans k.le_succ, hx⟩, hσ⟩
    · rw [query, ite_eq_right ht] at hq
      exact ⟨by rw [answers, hq], ⟨k + 1, le_rfl, hq.symm⟩, hσ⟩
    · exact ⟨hJ, ⟨j, hj.trans k.le_succ, hx⟩,
        hσ.trans (le_mul_of_one_le_left hσ0 P.toARParams.one_le_γ₂)⟩

/-- The reconstructed sequences form an ARp run ([cartis2022evaluation], (4.2.3)). Let $f$ be $C^p$
with $p \ge 1$, and let $\varepsilon > 0$. Then there is a run $(x_k, s_k, \sigma_k)$ of
Algorithm 4.1.1 in the first-order case ($\varepsilon_2 = \varepsilon_3 = +\infty$) with
tolerance $\varepsilon$ from $x_0 = 0$, such that the query $k + 1$ of ARp is $x_k + s_k$ at
every iteration $k$ at which the test fails, and every iterate $x_k$ is one of the queries
$0, \dots, k$. -/
theorem exists_run (hp : 1 ≤ p) (hε : 0 < ε) (hf : ContDiff ℝ p f) :
    ∃ x s σ, x 0 = 0 ∧ algorithm_4_1_1 f p P ε none none x s σ ∧
      (∀ k, ¬ arpTest f p P ε none none x s σ k →
        (arpOracleMethod (p := p) P ε).iter n f (k + 1) = x k + s k) ∧
      ∀ k, ∃ j ≤ k, x k = (arpOracleMethod (p := p) P ε).iter n f j := by
  set st := states P ε (answers P ε f p)
  set x : ℕ → EuclideanSpace ℝ (Fin n) := fun k => (st k).1
  set s : ℕ → EuclideanSpace ℝ (Fin n) := fun k => step (st k)
  set σ : ℕ → ℝ := fun k => (st k).2.1
  have hspec := states_spec (P := P) (ε := ε) (f := f) (p := p)
  have hσpos : ∀ k, 0 < σ k := fun k => P.σmin_pos.trans_le (hspec k).2.2
  have htest : ∀ k, arpTest f p P ε none none x s σ k ↔ jetTest ε (st k).2.2 := fun k => by
    rw [arpTest, arpStopTest_none, (hspec k).1, jetTest_jetOracle hp]
  have hmin : ∀ k, IsMinOn (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) univ (s k) :=
    fun k => by
      have := isMinOn_step (st := st k) (hσpos k) hp
      rwa [(hspec k).1, regularizedModel_jetSeries_jetOracle] at this
  have hquery : ∀ k, ¬ arpTest f p P ε none none x s σ k →
      (arpOracleMethod (p := p) P ε).iter n f (k + 1) = x k + s k := fun k hk => by
    rw [iter_succ, query, ite_eq_right ((htest k).not.1 hk)]
  have hratio : ∀ k, ¬ arpTest f p P ε none none x s σ k →
      ratio (st k) (answers P ε f p (k + 1)) = taylorRatio f p x s k := fun k hk => by
    rw [ratio, taylorRatio_def, reductionRatio, (hspec k).1, jetValue_jetOracle, answers,
      jetValue_jetOracle, hquery k hk, taylorDecrement_jetSeries_jetOracle]
  refine ⟨x, s, σ, rfl, ⟨hp, by simpa using hp, hε, by simp, by simp, fun _ => rfl, ?_⟩,
    hquery, fun k => (hspec k).2.1⟩
  refine ⟨rfl, fun k _ hk => ?_, fun k hk => ?_⟩
  · -- Step 2: the global model minimizer
    have hg : ε < ‖fderiv ℝ f (x k)‖ := by
      rw [← norm_gradient_eq]; simpa using hk
    have hdec := regularizedModel_lt_of_isMinOn_of_fderiv_ne_zero (hmin k) (by
      rw [fderiv_regularizedModel_ftaylorSeries_zero hf.contDiffAt hp]
      intro h0; rw [h0, norm_zero] at hg; linarith)
    exact isARpStep_of_isMinOn P.toARpParams (fun h => absurd h (by simp)) (hmin k) hdec
      (fun h => absurd h (by simp))
  · -- Steps 3–4
    have hk' : ¬ arpTest f p P ε none none x s σ k := fun h => hk k le_rfl (Or.inl h)
    have hst : st (k + 1) = update P ε (st k) (answers P ε f p (k + 1)) := rfl
    have hσ0 := (hσpos k).le
    have hσm := (hspec k).2.2
    change ARAcceptance P.toARParams (taylorRatio f p x s k) (x k) (s k) (st (k + 1)).1 (σ k)
      (st (k + 1)).2.1
    rw [hst, update, ite_eq_right ((htest k).not.1 hk'), hratio k hk']
    by_cases hs : P.η₁ ≤ taylorRatio f p x s k
    · rw [ite_eq_left hs]
      refine ⟨by rw [ite_eq_left hs], ⟨fun _ => ⟨max_le hσm (mul_le_of_le_one_left hσ0
        P.toARParams.γ₁_le_one), le_rfl⟩, fun _ _ => ⟨le_rfl, le_mul_of_one_le_left hσ0
        P.toARParams.one_le_γ₂⟩, fun h => absurd hs (not_le.2 h)⟩⟩
    · rw [ite_eq_right hs]
      refine ⟨by rw [ite_eq_right hs], ⟨fun h => absurd (P.η₁_le_η₂.trans h) hs,
        fun h => absurd h hs, fun _ => ⟨le_rfl, mul_le_mul_of_nonneg_right P.γ₂_le_γ₃ hσ0⟩⟩⟩

end ARpOracle

/-- Let $p \ge 1$ and $\varepsilon > 0$, and let $f$ satisfy f.Bb with lower bound $f_{\text{low}}$
and f.DpL with constant $L_{f,p}$. Then the index of the first query of ARp on $f$ with
$\|\nabla f\| \le \varepsilon$ is at most some $k$ with
$$k + 1 \le \kappa^A \frac{f(0) - f_{\text{low}}}{\varepsilon^{(p+1)/p}} + \kappa^C,$$
where $\kappa^A$ and $\kappa^C$ are the constants of Theorem 4.1.5 in the first-order case. The
index $k$ is the termination index of the reconstructed ARp run. -/
theorem firstStationaryIndex_arpOracleMethod_le {p : ℕ} (hp : 1 ≤ p) (P : ARpParams) {ε L flow : ℝ}
    (hε : 0 < ε) {f : EuclideanSpace ℝ (Fin n) → ℝ} (hb : Chapter02.AssumptionBb f flow)
    (hf : AssumptionDpL f p L) :
    ∃ k : ℕ, firstStationaryIndex ((arpOracleMethod (p := p) P ε).iter n f) f ε ≤ k ∧
      (k + 1 : ℝ) ≤ kappaSARp P p L 1 * (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
        (f 0 - flow) / ε ^ (((p : ℝ) + 1) / p) + kappaCARp P L := by
  obtain ⟨x, s, σ, hx0, hrun, -, hmem⟩ := ARpOracle.exists_run (P := P) hp hε hf.contDiff
  obtain ⟨kε, hk, hF, -⟩ := theorem_4_1_5_i hb hf hrun
  obtain ⟨j, hj, hxj⟩ := hmem kε
  refine ⟨kε, (firstStationaryIndex_le (k := j) ?_).trans (by exact_mod_cast hj), ?_⟩
  · rw [← hxj, ← norm_gradient_eq]; exact hk.test
  · rw [funEvalCount_eq, hx0] at hF; exact_mod_cast hF

/-- The bound $\kappa^A \Delta \varepsilon^{-(p+1)/p} + \kappa^C$ of (4.2.3), with the constants
$\kappa^A$ and $\kappa^C$ of Theorem 4.1.5 in the first-order case for $L_{f,p} = \max(1, L)$. -/
noncomputable def arpComplexityBound (P : ARpParams) (p : ℕ) (Δ L ε : ℝ) : ℝ :=
  kappaSARp P p (max 1 L) 1 * (1 + |Real.log P.γ₁| / Real.log P.γ₂) * Δ /
    ε ^ (((p : ℝ) + 1) / p) + kappaCARp P (max 1 L)

/-- The worst case $\sup_{f \in \mathcal{F}(\Delta, p)} k_\varepsilon(\mathrm{ARp}, f)$ of ARp on
the class $\mathcal{F}(\Delta, p)$, in `ℕ∞`. -/
noncomputable def arpWorstCase (P : ARpParams) (p : ℕ) (Δ L ε : ℝ) : ℕ∞ :=
  ⨆ F ∈ functionClass Δ L p,
    firstStationaryIndex ((arpOracleMethod (p := p) P ε).iter F.1 F.2) F.2 ε

/-- ARp attains the upper bound (4.2.3) ([cartis2022evaluation], §4.2.3). For $p \ge 1$ and
$\varepsilon > 0$ and for every $f \in \mathcal{F}(\Delta, p)$, the index of the first query of
ARp on $f$ with $\|\nabla f\| \le \varepsilon$ is at most $\lfloor \kappa^A \Delta
\varepsilon^{-(p+1)/p} + \kappa^C \rfloor$, uniformly in the dimension. The constants are those
of `CartisGouldToint.Chapter04.arpComplexityBound`. -/
theorem arpWorstCase_le_arpComplexityBound {p : ℕ} (hp : 1 ≤ p) (P : ARpParams) {Δ L ε : ℝ}
    (hε : 0 < ε) : arpWorstCase P p Δ L ε ≤ ((⌊arpComplexityBound P p Δ L ε⌋₊ : ℕ) : ℕ∞) := by
  refine iSup₂_le fun F hF => ?_
  obtain ⟨hc, hlip, hbdd, hΔ⟩ := mem_functionClass.1 hF
  have hb : Chapter02.AssumptionBb F.2 (⨅ y, F.2 y) := fun y => ciInf_le hbdd y
  have hf : AssumptionDpL F.2 p (max 1 L) :=
    .of_iteratedFDerivLipschitzOn (hc.of_le (by exact_mod_cast le_top)) (le_max_left _ _)
      (iteratedFDerivLipschitzOn_iff.2 fun x hx y hy =>
        (iteratedFDerivLipschitzOn_iff.1 hlip x hx y hy).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))
  obtain ⟨k, hk, hkB⟩ := firstStationaryIndex_arpOracleMethod_le hp P hε hb hf
  refine hk.trans (Nat.cast_le.2 (Nat.le_floor ?_))
  have hκ := kappaSARp_pos (P := P) (p := p) (L := max 1 L) (by positivity) 1
  have hlog : 0 ≤ 1 + |Real.log P.γ₁| / Real.log P.γ₂ := by
    have := P.toARParams.log_γ₂_pos; positivity
  have hE : 0 < ε ^ (((p : ℝ) + 1) / p) := Real.rpow_pos_of_pos hε _
  have : kappaSARp P p (max 1 L) 1 * (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
      (F.2 0 - ⨅ y, F.2 y) /
      ε ^ (((p : ℝ) + 1) / p) ≤ kappaSARp P p (max 1 L) 1 *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) * Δ / ε ^ (((p : ℝ) + 1) / p) := by
    gcongr
  rw [arpComplexityBound]
  linarith

/-- The complexity $\#_\varepsilon(\mathcal{M}(p), \mathcal{F}(\Delta, p))$ is at most the worst
case of ARp on $\mathcal{F}(\Delta, p)$, because ARp is a method of $\mathcal{M}(p)$. -/
theorem complexity_le_arpWorstCase (P : ARpParams) {p : ℕ} (Δ L ε : ℝ) :
    complexity (methodClassM p) (functionClass Δ L p) ε ≤ arpWorstCase P p Δ L ε :=
  iInf₂_le (f := fun M (_ : M ∈ methodClassM p) =>
    ⨆ F ∈ functionClass Δ L p, firstStationaryIndex (M.iter F.1 F.2) F.2 ε)
    (arpOracleMethod P ε) (arpOracleMethod_mem P ε)

/-- **(4.2.3)** of [cartis2022evaluation], the upper bound. For $p \ge 1$ and $\varepsilon > 0$,
$$\#_\varepsilon(\mathcal{M}(p), \mathcal{F}(\Delta, p)) \le \lfloor \kappa^A \Delta
  \varepsilon^{-(p+1)/p} + \kappa^C \rfloor,$$
and ARp attains this bound. The constants are those of Theorem 4.1.5 in the first-order case for
$L_{f,p} = \max(1, L)$ (`CartisGouldToint.Chapter04.arpComplexityBound`). -/
theorem complexity_le_arpComplexityBound {p : ℕ} (hp : 1 ≤ p) (P : ARpParams) {Δ L ε : ℝ}
    (hε : 0 < ε) :
    complexity (methodClassM p) (functionClass Δ L p) ε ≤
      ((⌊arpComplexityBound P p Δ L ε⌋₊ : ℕ) : ℕ∞) :=
  (complexity_le_arpWorstCase P Δ L ε).trans (arpWorstCase_le_arpComplexityBound hp P hε)

/-- **Theorem 4.2.6** of [cartis2022evaluation], tightness: the bound (4.2.3) is tight, and ARp has
the optimal order of evaluation complexity for methods in $\mathcal{M}(p)$. Let $p \ge 1$, let
the constants of ARp be given, and let $\Delta, L > 0$. Then the following holds.

* For every $\varepsilon > 0$, the worst case of ARp on $\mathcal{F}(\Delta, p)$, and also
  $\#_\varepsilon(\mathcal{M}(p), \mathcal{F}(\Delta, p))$, is at most $\lfloor \kappa^A \Delta
  \varepsilon^{-(p+1)/p} + \kappa^C \rfloor$ (4.2.3).
* There are $c, C, \varepsilon_0 > 0$ such that for all $\varepsilon \in (0, \varepsilon_0]$
  $$c\, \varepsilon^{-(p+1)/p} \le \#_\varepsilon(\mathcal{M}(p), \mathcal{F}(\Delta, p)) \le
  \sup_{f \in \mathcal{F}(\Delta, p)} k_\varepsilon(\mathrm{ARp}, f) \le C
  \varepsilon^{-(p+1)/p}.$$

**Reading.** The source states that the bound (4.2.3) is tight. The upper bound grows like
$\Delta L^{(p+1)/p}$ and the lower bound (4.2.7) like $\Delta L^{1/p}$, so only the order in
$\varepsilon$ is tight, and this is what the theorem states. The upper bound uses the constants
of Theorem 4.1.5 in the first-order case with $L_{f,p} = \max(1, L)$, because f.DpL requires
$L_{f,p} \ge 1$, and it is stated with an integer part.

The comparisons with real numbers are made in `ℝ≥0∞`. The worst case of ARp is
`CartisGouldToint.Chapter04.arpWorstCase`, and the bound is
`CartisGouldToint.Chapter04.arpComplexityBound`. -/
theorem theorem_4_2_6_ii {p : ℕ} (hp : 1 ≤ p) (P : ARpParams) {Δ L : ℝ} (hΔ : 0 < Δ)
    (hL : 0 < L) :
    (∀ ε, 0 < ε → arpWorstCase P p Δ L ε ≤ ((⌊arpComplexityBound P p Δ L ε⌋₊ : ℕ) : ℕ∞) ∧
      complexity (methodClassM p) (functionClass Δ L p) ε ≤
        ((⌊arpComplexityBound P p Δ L ε⌋₊ : ℕ) : ℕ∞)) ∧
    ∃ c C ε₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      ENNReal.ofReal (c * ε ^ (-((p + 1 : ℝ) / p))) ≤
          (complexity (methodClassM p) (functionClass Δ L p) ε : ENNReal) ∧
        complexity (methodClassM p) (functionClass Δ L p) ε ≤ arpWorstCase P p Δ L ε ∧
        (arpWorstCase P p Δ L ε : ENNReal) ≤ ENNReal.ofReal (C * ε ^ (-((p + 1 : ℝ) / p))) := by
  refine ⟨fun ε hε => ⟨arpWorstCase_le_arpComplexityBound hp P hε,
    complexity_le_arpComplexityBound hp P hε⟩, ?_⟩
  set a : ℝ := (p + 1 : ℝ) / p
  have ha : 0 < a := by positivity
  set K := Δ * (L / CarmonChain.lipschitzConst p) ^ (1 / p : ℝ)
  have hK : 0 < K := by
    have := CarmonChain.lipschitzConst_pos p
    positivity
  have hκA : 0 ≤ kappaSARp P p (max 1 L) 1 * (1 + |Real.log P.γ₁| / Real.log P.γ₂) := by
    have := kappaSARp_pos (P := P) (p := p) (L := max 1 L) (by positivity) 1
    have := P.toARParams.log_γ₂_pos
    positivity
  have hκC := two_le_kappaCARp (P := P) (max 1 L)
  set ε₀ := min 1 ((K / 12) ^ (1 / a))
  have hε₀ : 0 < ε₀ := lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨1 / 24 * K, kappaSARp P p (max 1 L) 1 * (1 + |Real.log P.γ₁| / Real.log P.γ₂) * Δ +
    kappaCARp P (max 1 L), ε₀, by positivity, by positivity, hε₀,
    fun ε hε hεε₀ => ⟨?_, complexity_le_arpWorstCase P Δ L ε, ?_⟩⟩
  · -- the lower bound of Theorem 4.2.6 (i)
    have hY : 12 ≤ K * ε ^ (-a) := by
      have h1 : ((K / 12) ^ (1 / a)) ^ (-a) ≤ ε ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos hε (hεε₀.trans (min_le_right _ _)) (by linarith)
      rw [← Real.rpow_mul (by positivity), show 1 / a * -a = -1 by field_simp, Real.rpow_neg_one,
        inv_div] at h1
      have := mul_le_mul_of_nonneg_left h1 hK.le
      rwa [mul_div_cancel₀ _ hK.ne'] at this
    have := (theorem_4_2_6_i hp hΔ hL hε).2.2.2 (by simpa only [K, mul_assoc] using hY)
    simpa only [K, mul_assoc] using this.2
  · -- the upper bound (4.2.3)
    refine (ENat.toENNReal_le.2 (arpWorstCase_le_arpComplexityBound hp P hε)).trans ?_
    rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ((Nat.floor_le (by
      rw [arpComplexityBound]; have := Real.rpow_pos_of_pos hε a; positivity)).trans ?_)
    have hε1 : 1 ≤ ε ^ (-a) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε (hεε₀.trans (min_le_left _ _))
        (by linarith)
    rw [arpComplexityBound, div_eq_mul_inv, ← Real.rpow_neg hε.le]
    nlinarith [mul_nonneg hκA hΔ.le]

end CartisGouldToint.Chapter04
