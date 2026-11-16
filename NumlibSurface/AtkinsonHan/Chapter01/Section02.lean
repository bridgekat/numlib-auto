/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Instances.AddCircle.Real
import Numlib.Analysis.Calculus.ContDiffMapIcc
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Analysis.Sobolev.Interval.Higher

/-!
# Atkinson and Han, Section 1.2: Normed spaces

This module formalizes §1.2 of [han2009theoretical]: norms and semi-norms, convergence and
continuity, equivalence of norms, series, density and separability, Cauchy sequences, Banach spaces,
the completion of a normed space, and the two facts from measure theory (§1.2.3) that the book
records for later use, the dominated convergence theorem and Fubini's theorem. The examples treat
the $p$-norms on $\mathbb{R}^d$, the sequence spaces $\ell^p$, the spaces $C[a, b]$ and $C_p(2\pi)$
with the maximum norm, the failure of completeness of $C[0, 1]$ for the norm
$\|v\|_p = (\int_0^1 |v|^p)^{1/p}$, and the space $C^m[a, b]$ with two norms. For the norm
$\sum_{j \le m} \|v^{(j)}\|_\infty$ the space $C^m[a, b]$ is complete. For the norm
$[\sum_{j \le m} \|v^{(j)}\|_{L^p}^p]^{1/p}$ it is not complete, and its completion is the Sobolev
space $W^{m,p}(a, b)$.

The definitions of the section are Mathlib's `Norm`, `Seminorm`, `Metric.ball`, `IsOpen`,
`IsClosed`, `Filter.Tendsto`, `SeqContinuous`, `Dense`, `TopologicalSpace.SeparableSpace`,
`SchauderBasis`, `CauchySeq` and `CompleteSpace`, and each is restated here under the number of the
book. The spaces $C^m[a, b]$ and $W^{m,p}(a, b)$ come from the backbone modules
`Numlib.Analysis.Calculus.ContDiffMapIcc` and `Numlib.Analysis.Sobolev.Interval.Basic`.

## Main definitions

* Definition 1.2.2, `AtkinsonHan.Chapter01.definition_1_2_2`: a semi-norm is a norm without the
  requirement that $|v| = 0$ imply $v = 0$.
* Definition 1.2.8, `AtkinsonHan.Chapter01.definition_1_2_8`: $u_n \to u$ means $\|u_n - u\| \to 0$.
* Definition 1.2.9, `AtkinsonHan.Chapter01.definition_1_2_9`: continuity at a point, in sequential
  form.
* Definition 1.2.17, `AtkinsonHan.Chapter01.definition_1_2_17`: convergence of the series
  $\sum v_i$, through its partial sums.
* Definition 1.2.18, `AtkinsonHan.Chapter01.definition_1_2_18`: $V_1$ is dense in $V_2$.
* Definition 1.2.20, `AtkinsonHan.Chapter01.definition_1_2_20` and
  `AtkinsonHan.Chapter01.definition_1_2_20_schauder`: a countably-infinite basis, which makes the
  space separable, and a Schauder basis.
* Definition 1.2.21, `AtkinsonHan.Chapter01.definition_1_2_21`: a Cauchy sequence.
* Example 1.2.28(b), `AtkinsonHan.Chapter01.ContDiffMapIccSobolevNorm`: the space $C^m[a, b]$ with
  the norm of $W^{m,p}(a, b)$.

## Main results

* Definition 1.2.1, `AtkinsonHan.Chapter01.definition_1_2_1`: a Mathlib norm satisfies the three
  axioms of a norm.
* Definitions 1.2.2, 1.2.8, 1.2.9, 1.2.17, 1.2.18 and 1.2.21,
  `AtkinsonHan.Chapter01.definition_1_2_2_iff`, `AtkinsonHan.Chapter01.definition_1_2_8_iff`,
  `AtkinsonHan.Chapter01.definition_1_2_9_iff`, `AtkinsonHan.Chapter01.definition_1_2_17_iff`,
  `AtkinsonHan.Chapter01.definition_1_2_18_iff` and `AtkinsonHan.Chapter01.definition_1_2_21_iff`:
  each restated definition is the corresponding Mathlib notion.
* Example 1.2.3, `AtkinsonHan.Chapter01.example_1_2_3`: the $p$-norms and the maximum norm on
  $\mathbb{R}^d$.
* Example 1.2.4, `AtkinsonHan.Chapter01.example_1_2_4`: the norms of the sequence spaces $\ell^p$.
* Example 1.2.5(a), `AtkinsonHan.Chapter01.example_1_2_5`: the maximum norm of $C[a, b]$ and of
  $C_p(2\pi)$.
* Definitions 1.2.6 and 1.2.7, `AtkinsonHan.Chapter01.definition_1_2_6` and
  `AtkinsonHan.Chapter01.definition_1_2_7`: open and closed balls, and open and closed sets.
* Definition 1.2.8, `AtkinsonHan.Chapter01.definition_1_2_8_unique`: a sequence has at most one
  limit.
* Proposition 1.2.10, `AtkinsonHan.Chapter01.proposition_1_2_10`: the norm is continuous.
* Example 1.2.11, `AtkinsonHan.Chapter01.example_1_2_11`: point evaluation is continuous on
  $C[0, 1]$.
* Example 1.2.13, `AtkinsonHan.Chapter01.example_1_2_13`: the inequality (1.2.6), $\|x\|_\infty \le
  \|x\|_p \le d^{1/p} \|x\|_\infty$ on $\mathbb{R}^d$.
* Theorem 1.2.14, `AtkinsonHan.Chapter01.theorem_1_2_14`: any two norms on a finite-dimensional
  space are equivalent in the sense of Definition 1.2.12.
* Example 1.2.15, `AtkinsonHan.Chapter01.example_1_2_15`: on $C[0, 1]$ the norms $\|\cdot\|_p$ and
  $\|\cdot\|_\infty$ are not equivalent.
* Example 1.2.16, `AtkinsonHan.Chapter01.example_1_2_16`: on $C[0, 1]$, $\|v\|_p \le \|v\|_\infty$.
* Definition 1.2.20, `AtkinsonHan.Chapter01.definition_1_2_20_of_schauder`: a Schauder basis is a
  countably-infinite basis.
* Example 1.2.22, `AtkinsonHan.Chapter01.example_1_2_22` and
  `AtkinsonHan.Chapter01.example_1_2_22_incomplete`: $C(\bar\Omega)$ is complete for the maximum
  norm, and $C[0, 1]$ is not complete for $\|\cdot\|_p$, $1 \le p < \infty$.
* Proposition 1.2.23, `AtkinsonHan.Chapter01.proposition_1_2_23`: a Cauchy sequence with a
  convergent subsequence converges.
* Definition 1.2.24, `AtkinsonHan.Chapter01.definition_1_2_24`: a normed space is complete if and
  only if every Cauchy sequence converges.
* Theorem 1.2.25, `AtkinsonHan.Chapter01.theorem_1_2_25` and
  `AtkinsonHan.Chapter01.theorem_1_2_25_uniqueness`: every normed space has a completion, unique up
  to a linear isometric isomorphism that fixes the embedded copy of the space.
* Theorem 1.2.26, `AtkinsonHan.Chapter01.theorem_1_2_26`: the Lebesgue dominated convergence
  theorem.
* Theorem 1.2.27, `AtkinsonHan.Chapter01.theorem_1_2_27`: Fubini's theorem.
* Example 1.2.28(a), `AtkinsonHan.Chapter01.example_1_2_28_a` and
  `AtkinsonHan.Chapter01.example_1_2_28_a_periodic`: $C^m[a, b]$ and $C_p^k(2\pi)$ are Banach
  spaces.
* Example 1.2.28(b), `AtkinsonHan.Chapter01.example_1_2_28_b_norm` and
  `AtkinsonHan.Chapter01.example_1_2_28_b`: the formula for the Sobolev norm on $C^m[a, b]$, and the
  statement that $C^m[a, b]$ with this norm is not complete and has the completion $W^{m,p}(a, b)$.

## Conventions

* The space $\mathbb{R}^d$ with the norm $\|\cdot\|_p$ is `PiLp p (fun _ : Fin d => ℝ)`, whose case
  $p = \infty$ carries the maximum norm. The space $\ell^p$ is `lp (fun _ : ℕ => ℝ) p`.
* The space $C[a, b]$ is `C(Set.Icc a b, ℝ)`, and the space of continuous $2\pi$-periodic
  functions is `C(AddCircle (2 * π), ℝ)`. Both carry the supremum norm, because their domains are
  compact.
* The space $C^m[a, b]$ is the backbone's `ContDiffMapIcc hab m`, with the norm
  $\sum_{j \le m} \|v^{(j)}\|_\infty$.
* The norm $\|v\|_p$ on $C[0, 1]$ has no normed-space structure in Mathlib. Where the section uses
  it (Examples 1.2.15 and 1.2.16, and the second half of Example 1.2.22), it is written out as the
  interval integral $(\int_0^1 |v(x)|^p \, dx)^{1/p}$, for functions $v : \mathbb{R} \to \mathbb{R}$
  that are continuous on $[0, 1]$.

## Implementation notes

* As in §1.1, a definition that names a property of data is a `def … : Prop` in the words of the
  book with a companion theorem `…_iff` that identifies it with the Mathlib notion. A definition
  that names a structure carried by a type, here the norm and completeness, is a theorem that the
  Mathlib class satisfies the axioms of the book.
* Theorem 1.2.14 quantifies over two norms on one linear space. A Lean type carries one norm, so the
  statement is about two normed types $V$ and $W$ and a linear equivalence $e : V \to W$, and the
  two norms are $\|v\|$ and $\|e v\|$.
* The space $C_p^k(2\pi)$ of Example 1.2.28(a) is read on one period, as the subspace
  `ContDiffMapIcc.periodicBoundary` of $C^k[0, 2\pi]$ on which every derivative of order at most $k$
  takes the same value at the two ends. The statement identifies it with the $2\pi$-periodic $C^k$
  functions on $\mathbb{R}$, and at $k = 0$ it agrees with the space `C(AddCircle (2 * π), ℝ)` of
  Example 1.2.5.
* In Example 1.2.28(b), $W^{m,p}(a, b)$ is the backbone's `SobolevIntervalLp m p (Opens.Ioo a b)`,
  and the norm of $C^m[a, b]$ is the norm of $W^{m,p}(a, b)$ pulled back along the injective
  inclusion `ContDiffMapIcc.toSobolevIntervalLp`. The book's "completion" is read as a dense linear
  isometry into a Banach space, in the sense of `AtkinsonHan.Chapter01.theorem_1_2_25_uniqueness`.

## Deviations from the source

* **Theorem 1.2.26** (generalization). The book states the dominated convergence theorem for
  Lebesgue measure on an open set of $\mathbb{R}^d$. The statement holds on an arbitrary measure
  space. See `AtkinsonHan.Chapter01.theorem_1_2_26`.
* **Theorem 1.2.27** (generalization). The book states Fubini's theorem for Lebesgue measure on open
  sets of Euclidean spaces. The statement holds for two s-finite measure spaces. See
  `AtkinsonHan.Chapter01.theorem_1_2_27`.

## Not formalized

* **Example 1.2.5(b)**, the norm $\|f\|_{k,\infty} = \max_{j \le k} \|f^{(j)}\|_\infty$ of
  $C^k[a, b]$. The backbone's $C^k[a, b]$ carries the equivalent norm
  $\sum_{j \le k} \|f^{(j)}\|_\infty$, and the two-sided bound between the two norms is part of
  `AtkinsonHan.Chapter01.example_1_2_28_a`.
* **Example 1.2.19.** It is Theorem 1.5.6 for a bounded open set $\Omega$, and it is covered by
  `AtkinsonHan.Chapter01.theorem_1_5_6_open`.
* **The closing remark of Example 1.2.28(b)**, that for $f \in W^{m,p}(a, b)$ the derivatives
  $f, \dots, f^{(m-1)}$ are continuous and $f^{(m)} \in L^p(a, b)$. It is the backbone's embedding
  `SobolevIntervalLp.toContDiffMapIcc` and is not restated.
-/

open ENNReal Filter MeasureTheory Topology

open scoped NNReal Real

namespace AtkinsonHan.Chapter01

section Normed

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Definition 1.2.1** of [han2009theoretical]. A **norm** on a linear space $V$ over $\mathbb{K}$
is a function $\|\cdot\| : V \to \mathbb{R}$ with three properties: $\|v\| \ge 0$, and
$\|v\| = 0$ if and only if $v = 0$; $\|\alpha v\| = |\alpha| \, \|v\|$ (positive homogeneity);
and $\|u + v\| \le \|u\| + \|v\|$ (the triangle inequality). The pair $(V, \|\cdot\|)$ is a
**normed space**. The theorem states that every normed space over $\mathbb{K}$ in the sense of
Mathlib has these three properties.

A normed space is `NormedAddCommGroup V` with `NormedSpace 𝕜 V`. The scalar field is `𝕜` with
`RCLike 𝕜`, which is $\mathbb{R}$ or $\mathbb{C}$. -/
theorem definition_1_2_1 (𝕜 V : Type*) [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    (∀ v : V, 0 ≤ ‖v‖ ∧ (‖v‖ = 0 ↔ v = 0)) ∧
      (∀ (α : 𝕜) (v : V), ‖α • v‖ = ‖α‖ * ‖v‖) ∧
      (∀ u v : V, ‖u + v‖ ≤ ‖u‖ + ‖v‖) :=
  ⟨fun v => ⟨norm_nonneg v, norm_eq_zero⟩, norm_smul, norm_add_le⟩

/-- **Definition 1.2.2** of [han2009theoretical]. A **semi-norm** on a linear space $V$ over
$\mathbb{K}$ is a function $p : V \to \mathbb{R}$ with the properties of a norm (Definition
1.2.1) except that $p(v) = 0$ need not imply $v = 0$: $p(v) \ge 0$,
$p(\alpha v) = |\alpha| \, p(v)$ and $p(u + v) \le p(u) + p(v)$.

The predicate is stated on a normed space, whose own norm it does not use. It is `Seminorm` by
`AtkinsonHan.Chapter01.definition_1_2_2_iff`. The book uses semi-norms for the error of
polynomial interpolation in Chapter 3. -/
def definition_1_2_2 (𝕜 : Type*) {V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    (p : V → ℝ) : Prop :=
  (∀ v : V, 0 ≤ p v) ∧ (∀ (α : 𝕜) (v : V), p (α • v) = ‖α‖ * p v) ∧
    ∀ u v : V, p (u + v) ≤ p u + p v

/-- A function $p : V \to \mathbb{R}$ is a semi-norm in the sense of Definition 1.2.2 of
[han2009theoretical] if and only if it is the function of a Mathlib `Seminorm 𝕜 V`. -/
theorem definition_1_2_2_iff (p : V → ℝ) :
    definition_1_2_2 𝕜 p ↔ ∃ q : Seminorm 𝕜 V, ⇑q = p := by
  constructor
  · rintro ⟨-, hsmul, hadd⟩
    refine ⟨⟨⟨p, ?_, hadd, fun v => ?_⟩, hsmul⟩, rfl⟩
    · simpa using hsmul 0 0
    · simpa using hsmul (-1) v
  · rintro ⟨q, rfl⟩
    exact ⟨fun v => apply_nonneg q v, fun α v => map_smul_eq_mul q α v,
      fun u v => map_add_le_add q u v⟩

/-- **Example 1.2.3** of [han2009theoretical]. Let $d \in \mathbb{N}$. On $\mathbb{R}^d$, the
$p$-norm (1.2.2) for $1 \le p < \infty$ is $$\|x\|_p = \Big(\sum_{i=1}^d |x_i|^p\Big)^{1/p},$$
and the maximum norm (1.2.3) is $\|x\|_\infty = \max_{1 \le i \le d} |x_i|$.

The space is `PiLp p (fun _ : Fin d => ℝ)`, of which `EuclideanSpace ℝ (Fin d)` is the case
$p = 2$. The maximum is the supremum `⨆ i`, which is $0$ for $d = 0$. -/
theorem example_1_2_3 (d : ℕ) :
    (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → ∀ x : PiLp p fun _ : Fin d => ℝ,
        ‖x‖ = (∑ i, |x i| ^ p.toReal) ^ (1 / p.toReal)) ∧
      (∀ x : PiLp ∞ fun _ : Fin d => ℝ, ‖x‖ = ⨆ i, |x i|) := by
  refine ⟨fun p _ hp x => ?_, fun x => ?_⟩
  · rw [PiLp.norm_eq_sum (p.toReal_pos_iff_ne_top.mpr hp)]
    simp [Real.norm_eq_abs]
  · rw [PiLp.norm_eq_ciSup]
    simp [Real.norm_eq_abs]

/-- **Example 1.2.4** of [han2009theoretical]. Let $1 \le p \le \infty$. The space $\ell^p$ consists
of the real sequences $v = (v_n)$ of finite norm, where $$\|v\|_{\ell^p} = \Big(\sum_n
|v_n|^p\Big)^{1/p} \quad (p < \infty), \qquad \|v\|_{\ell^\infty} = \sup_n |v_n|.$$ The
statement gives these formulas for the norm of $\ell^p$.

The space is `lp (fun _ : ℕ => ℝ) p`, the subtype of the sequences that satisfy `Memℓp`, and
sequences are indexed from $0$. Its norm instance carries the triangle inequality, which the
book leaves to Exercise 1.5.11. -/
theorem example_1_2_4 :
    (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → ∀ v : lp (fun _ : ℕ => ℝ) p,
        ‖v‖ = (∑' n, |v n| ^ p.toReal) ^ (1 / p.toReal)) ∧
      (∀ v : lp (fun _ : ℕ => ℝ) ∞, ‖v‖ = ⨆ n, |v n|) := by
  refine ⟨fun p _ hp v => ?_, fun v => ?_⟩
  · rw [lp.norm_eq_tsum_rpow (p.toReal_pos_iff_ne_top.mpr hp)]
    simp [Real.norm_eq_abs]
  · rw [lp.norm_eq_ciSup]
    simp [Real.norm_eq_abs]

section Periodic

/-- **Example 1.2.5(a)** of [han2009theoretical]. Let $a, b \in \mathbb{R}$. The standard norm of
$C[a, b]$ is the maximum norm $\|f\|_\infty = \max_{a \le x \le b} |f(x)|$, and the same formula
gives the standard norm of the space $C_p(2\pi)$ of continuous $2\pi$-periodic functions.

Both norms are the supremum norm of Mathlib on `C(X, ℝ)` for a compact `X`, and the maximum is
written as the supremum `⨆ x`. If $a > b$, then $[a, b]$ is empty and both sides are $0$. -/
theorem example_1_2_5 {a b : ℝ} :
    (∀ f : C(Set.Icc a b, ℝ), ‖f‖ = ⨆ x, |f x|) ∧
      (∀ f : C(AddCircle (2 * π), ℝ), ‖f‖ = ⨆ x, |f x|) :=
  ⟨fun f => by simpa [Real.norm_eq_abs] using f.norm_eq_iSup_norm,
    fun f => by simpa [Real.norm_eq_abs] using f.norm_eq_iSup_norm⟩

end Periodic

/-- **Definition 1.2.6** of [han2009theoretical]. Let $V$ be a normed space, $v_0 \in V$ and
$r > 0$. The **open ball** is $B(v_0, r) = \{v \in V : \|v - v_0\| < r\}$, and the **closed
ball** is $\bar B(v_0, r) = \{v \in V : \|v - v_0\| \le r\}$. For $v_0 = 0$ and $r = 1$ they are
the unit balls. The theorem states that `Metric.ball v₀ r` and `Metric.closedBall v₀ r` are
these sets, for every real $r$. -/
theorem definition_1_2_6 (v₀ : V) (r : ℝ) :
    Metric.ball v₀ r = {v | ‖v - v₀‖ < r} ∧ Metric.closedBall v₀ r = {v | ‖v - v₀‖ ≤ r} :=
  ⟨by ext v; simp [Metric.mem_ball, dist_eq_norm],
    by ext v; simp [Metric.mem_closedBall, dist_eq_norm]⟩

/-- **Definition 1.2.7** of [han2009theoretical]. A set $A$ in a normed space $V$ is **open** if
every $v \in A$ has a ball $B(v, r) \subseteq A$ with $r > 0$. It is **closed** if its
complement $V \setminus A$ is open. The theorem states that `IsOpen` and `IsClosed`, for the
topology of the norm, have these characterizations. -/
theorem definition_1_2_7 (A : Set V) :
    (IsOpen A ↔ ∀ v ∈ A, ∃ r > 0, Metric.ball v r ⊆ A) ∧ (IsClosed A ↔ IsOpen Aᶜ) :=
  ⟨Metric.isOpen_iff, isOpen_compl_iff.symm⟩

/-- **Definition 1.2.8** of [han2009theoretical]. A sequence $\{u_n\}$ in a normed space $V$
**converges** to $u \in V$ if $\|u_n - u\| \to 0$ as $n \to \infty$. Then $u$ is the **limit**
of the sequence.

A sequence has at most one limit by `AtkinsonHan.Chapter01.definition_1_2_8_unique`. The
predicate is `Filter.Tendsto u atTop (𝓝 v)` by `AtkinsonHan.Chapter01.definition_1_2_8_iff`. -/
def definition_1_2_8 {V : Type*} [NormedAddCommGroup V] (u : ℕ → V) (v : V) : Prop :=
  Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0)

/-- A sequence $\{u_n\}$ in a normed space converges to $v$ in the sense of Definition 1.2.8 of
[han2009theoretical] if and only if $u_n \to v$ in the topology of the norm, which is
`Filter.Tendsto u atTop (𝓝 v)`. -/
theorem definition_1_2_8_iff (u : ℕ → V) (v : V) :
    definition_1_2_8 u v ↔ Tendsto u atTop (𝓝 v) :=
  tendsto_iff_norm_sub_tendsto_zero.symm

/-- A sequence in a normed space has at most one limit: if $u_n \to v$ and $u_n \to w$ in the sense
of Definition 1.2.8 of [han2009theoretical], then $v = w$. The book records this after
Definition 1.2.8. -/
theorem definition_1_2_8_unique {u : ℕ → V} {v w : V} (hv : definition_1_2_8 u v)
    (hw : definition_1_2_8 u w) : v = w :=
  tendsto_nhds_unique ((definition_1_2_8_iff u v).mp hv) ((definition_1_2_8_iff u w).mp hw)

/-- **Definition 1.2.9** of [han2009theoretical]. Let $V$ be a normed space. A function
$f : V \to \mathbb{R}$ is **continuous at** $u \in V$ if $f(u_n) \to f(u)$ for every sequence
$u_n \to u$. It is **continuous on** $V$ if it is continuous at every $u \in V$.

The predicate is continuity at one point. The sequential form of the book is `SeqContinuous`,
which agrees with `Continuous` on a metric space, and
`AtkinsonHan.Chapter01.definition_1_2_9_iff` is the correspondence. -/
def definition_1_2_9 {V : Type*} [NormedAddCommGroup V] (f : V → ℝ) (u : V) : Prop :=
  ∀ v : ℕ → V, definition_1_2_8 v u → definition_1_2_8 (fun n => f (v n)) (f u)

/-- A function $f : V \to \mathbb{R}$ on a normed space is continuous at every point in the sense of
Definition 1.2.9 of [han2009theoretical] if and only if it is `Continuous`. -/
theorem definition_1_2_9_iff (f : V → ℝ) : (∀ u, definition_1_2_9 f u) ↔ Continuous f := by
  rw [continuous_iff_seqContinuous]
  constructor
  · intro h x y hxy
    exact (definition_1_2_8_iff _ _).mp (h y x ((definition_1_2_8_iff _ _).mpr hxy))
  · intro h u v hv
    exact (definition_1_2_8_iff _ _).mpr (h ((definition_1_2_8_iff _ _).mp hv))

/-- **Proposition 1.2.10** of [han2009theoretical]. The norm is a continuous function: if
$u_n \to v$ in a normed space $V$, then $\|u_n\| \to \|v\|$.

The book's proof is the inequality (1.2.5), $\big|\|u\| - \|v\|\big| \le \|u - v\|$, which is
`abs_norm_sub_norm_le`. -/
theorem proposition_1_2_10 {u : ℕ → V} {v : V} (h : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖v‖) :=
  h.norm

/-- **Example 1.2.11** of [han2009theoretical]. Let $x_0 \in [0, 1]$. On $V = C[0, 1]$, the point
evaluation $\ell_{x_0}(v) = v(x_0)$ is continuous at every $u \in V$ in the sense of Definition
1.2.9.

The proof is the bound $|\ell_{x_0}(v_n) - \ell_{x_0}(v)| \le \|v_n - v\|_\infty$. The book
returns to $\ell_{x_0}$ as a linear functional in Chapter 2. -/
theorem example_1_2_11 (x₀ : Set.Icc (0 : ℝ) 1) (u : C(Set.Icc (0 : ℝ) 1, ℝ)) :
    definition_1_2_9 (fun v : C(Set.Icc (0 : ℝ) 1, ℝ) => v x₀) u :=
  (definition_1_2_9_iff _).mpr (continuous_eval_const x₀) u

/-- **Example 1.2.13** of [han2009theoretical], the inequality (1.2.6). Let $d \in \mathbb{N}$ and
$1 \le p \le \infty$. Every $x \in \mathbb{R}^d$ satisfies $$\|x\|_\infty \le \|x\|_p \le
d^{1/p} \|x\|_\infty,$$ with $1/\infty = 0$. Hence all the $p$-norms on $\mathbb{R}^d$ are
equivalent, a special case of Theorem 1.2.14.

The book states the inequality for $1 \le p < \infty$. The case $p = \infty$ is trivial, because
the exponent $1/p$ is `1 / p.toReal`, which is $0$ for $p = \infty$. -/
theorem example_1_2_13 {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : Fin d → ℝ) :
    ‖(WithLp.toLp ∞ x : PiLp ∞ fun _ : Fin d => ℝ)‖ ≤
        ‖(WithLp.toLp p x : PiLp p fun _ : Fin d => ℝ)‖ ∧
      ‖(WithLp.toLp p x : PiLp p fun _ : Fin d => ℝ)‖ ≤
        (d : ℝ) ^ (1 / p.toReal) * ‖(WithLp.toLp ∞ x : PiLp ∞ fun _ : Fin d => ℝ)‖ := by
  have hK : (((Fintype.card (Fin d) : ℝ≥0) ^ (1 / p).toReal : ℝ≥0) : ℝ)
      = (d : ℝ) ^ (1 / p.toReal) := by
    rw [Fintype.card_fin, NNReal.coe_rpow, NNReal.coe_natCast, ENNReal.toReal_div,
      ENNReal.toReal_one]
  refine ⟨?_, ?_⟩
  · rw [PiLp.norm_eq_ciSup]
    refine Real.iSup_le (fun i => ?_) (norm_nonneg _)
    simpa using PiLp.norm_apply_le (WithLp.toLp p x) i
  · have h := (PiLp.lipschitzWith_toLp p fun _ : Fin d => ℝ).dist_le_mul x 0
    simp only [WithLp.toLp_zero, dist_zero_right] at h
    rw [PiLp.norm_toLp, ← hK]
    exact h

/-- **Example 1.2.15** of [han2009theoretical]. On $C[0, 1]$ the norms $\|\cdot\|_p$,
$1 \le p < \infty$, and $\|\cdot\|_\infty$ are not equivalent: no constant $c$ satisfies
$\|v\|_\infty \le c \|v\|_p$ for all $v$. Precisely, let $1 \le p < \infty$ and
$c \in \mathbb{R}$. Then there is a continuous $v : \mathbb{R} \to \mathbb{R}$ with
$|v(x)| \le 1$ for $x \in [0, 1]$ and $v(0) = 1$, so that $\|v\|_\infty = 1$, and with $$c
\Big(\int_0^1 |v(x)|^p \, dx\Big)^{1/p} < 1.$$

The book's witnesses are the functions $u_n(x) = \max\{1 - nx, 0\}$, with
$\|u_n\|_p = [n(p + 1)]^{-1/p}$. The proof uses the functions $v_n(x) = (1 - x)^n$ instead, with
$\|v_n\|_p = (np + 1)^{-1/p}$, because they need no case distinction. -/
theorem example_1_2_15 {p : ℝ} (hp : 1 ≤ p) (c : ℝ) :
    ∃ v : ℝ → ℝ, Continuous v ∧ (∀ x ∈ Set.Icc (0 : ℝ) 1, |v x| ≤ 1) ∧ v 0 = 1 ∧
      c * (∫ x in (0 : ℝ)..1, |v x| ^ p) ^ (1 / p) < 1 := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  -- the witness `vₙ x = (1 - x)ⁿ`, for an `n` chosen below
  set n : ℕ := ⌈max c 0 ^ p⌉₊ with hn
  refine ⟨fun x => (1 - x) ^ n, by fun_prop, fun x hx => ?_, by simp, ?_⟩
  · rw [abs_pow]
    refine pow_le_one₀ (abs_nonneg _) ?_
    rw [abs_le]
    constructor <;> [linarith [hx.2]; linarith [hx.1]]
  -- the integral is `1 / (n p + 1)`
  have hr : (0 : ℝ) ≤ (n : ℝ) * p := by positivity
  have hint : (∫ x in (0 : ℝ)..1, |(1 - x) ^ n| ^ p) = 1 / ((n : ℝ) * p + 1) := by
    have hcongr : ∀ x ∈ Set.uIcc (0 : ℝ) 1, |(1 - x) ^ n| ^ p = (1 - x) ^ ((n : ℝ) * p) := by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      have h1x : (0 : ℝ) ≤ 1 - x := by linarith [hx.2]
      rw [abs_of_nonneg (pow_nonneg h1x n), ← Real.rpow_natCast (1 - x) n,
        ← Real.rpow_mul h1x]
    rw [intervalIntegral.integral_congr hcongr,
      intervalIntegral.integral_comp_sub_left (fun x => x ^ ((n : ℝ) * p)) 1]
    norm_num
    rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < (n : ℝ) * p)), Real.one_rpow,
      Real.zero_rpow (by linarith), sub_zero, one_div]
  rw [hint]
  rcases le_or_gt c 0 with hc | hc
  · have : (0 : ℝ) ≤ (1 / ((n : ℝ) * p + 1)) ^ (1 / p) :=
      Real.rpow_nonneg (by positivity) _
    nlinarith
  -- for `c > 0`, `n` was chosen so that `n p + 1 > c ^ p`
  · have hcp : max c 0 ^ p ≤ (n : ℝ) := Nat.le_ceil _
    have hcp' : c ^ p < (n : ℝ) * p + 1 := by
      have hmax : max c 0 = c := max_eq_left hc.le
      rw [hmax] at hcp
      nlinarith [Real.rpow_nonneg hc.le p]
    have hcppos : (0 : ℝ) < c ^ p := Real.rpow_pos_of_pos hc p
    have hlt : (1 / ((n : ℝ) * p + 1)) ^ (1 / p) < (1 / c ^ p) ^ (1 / p) := by
      refine Real.rpow_lt_rpow (by positivity) ?_ (by positivity)
      exact one_div_lt_one_div_of_lt hcppos hcp'
    have heq : (1 / c ^ p) ^ (1 / p) = 1 / c := by
      rw [one_div, one_div, Real.inv_rpow (le_of_lt hcppos), ← Real.rpow_mul hc.le,
        mul_inv_cancel₀ hp0.ne', Real.rpow_one, one_div]
    rw [heq] at hlt
    calc c * (1 / ((n : ℝ) * p + 1)) ^ (1 / p) < c * (1 / c) := by
          exact mul_lt_mul_of_pos_left hlt hc
      _ = 1 := by field_simp

/-- **Example 1.2.16** of [han2009theoretical]. Let $1 \le p < \infty$, let $v$ be continuous on
$[0, 1]$, and let $M \in \mathbb{R}$ satisfy $|v(x)| \le M$ for all $x \in [0, 1]$. Then
$$\Big(\int_0^1 |v(x)|^p \, dx\Big)^{1/p} \le M.$$ With $M = \|v\|_\infty$ this is
$\|v\|_p \le \|v\|_\infty$, so uniform convergence implies convergence in $\|\cdot\|_p$. The
converse fails by Example 1.2.15.

The general form of the inequality, the inclusion $L^q(\Omega) \subseteq L^p(\Omega)$ with the
constant $\operatorname{meas}(\Omega)^{1/p - 1/q}$, is `AtkinsonHan.Chapter01.theorem_1_5_5_c`. -/
theorem example_1_2_16 {p : ℝ} (hp : 1 ≤ p) {v : ℝ → ℝ} (hv : ContinuousOn v (Set.Icc 0 1))
    {M : ℝ} (hM : ∀ x ∈ Set.Icc (0 : ℝ) 1, |v x| ≤ M) :
    (∫ x in (0 : ℝ)..1, |v x| ^ p) ^ (1 / p) ≤ M := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 (by norm_num))
  have hcont : ContinuousOn (fun x => |v x| ^ p) (Set.Icc 0 1) :=
    hv.abs.rpow_const fun _ _ => Or.inr hp0.le
  have hint : IntervalIntegrable (fun x => |v x| ^ p) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hle : (∫ x in (0 : ℝ)..1, |v x| ^ p) ≤ M ^ p := by
    have hmono : (∫ x in (0 : ℝ)..1, |v x| ^ p) ≤ ∫ _ in (0 : ℝ)..1, M ^ p := by
      refine intervalIntegral.integral_mono_on (by norm_num) hint intervalIntegrable_const ?_
      intro x hx
      exact Real.rpow_le_rpow (abs_nonneg _) (hM x hx) hp0.le
    simpa using hmono
  have hnn : 0 ≤ ∫ x in (0 : ℝ)..1, |v x| ^ p :=
    intervalIntegral.integral_nonneg (by norm_num) fun x _ => Real.rpow_nonneg (abs_nonneg _) p
  calc (∫ x in (0 : ℝ)..1, |v x| ^ p) ^ (1 / p)
      ≤ (M ^ p) ^ (1 / p) := Real.rpow_le_rpow hnn hle (by positivity)
    _ = M := by
        rw [← Real.rpow_mul hM0, mul_one_div_cancel hp0.ne', Real.rpow_one]

/-- **Definition 1.2.17** of [han2009theoretical]. Let $\{v_i\}$ be a sequence in a normed space
$V$, with partial sums $s_n = \sum_{i < n} v_i$. The series $\sum_i v_i$ **converges** to
$s \in V$ if $s_n \to s$ in $V$.

Sequences are indexed from $0$, so $s_n$ is the sum over `Finset.range n`. This is the ordered
form of summation. Mathlib's `HasSum` is the unordered form, and the two agree for the
unconditionally convergent series that the book uses. -/
def definition_1_2_17 {V : Type*} [NormedAddCommGroup V] (v : ℕ → V) (s : V) : Prop :=
  definition_1_2_8 (fun n => ∑ i ∈ Finset.range n, v i) s

/-- A series $\sum_i v_i$ in a normed space converges to $s$ in the sense of Definition 1.2.17 of
[han2009theoretical] if and only if its partial sums $\sum_{i < n} v_i$ tend to $s$ in the
topology of the norm. -/
theorem definition_1_2_17_iff (v : ℕ → V) (s : V) :
    definition_1_2_17 v s ↔ Tendsto (fun n => ∑ i ∈ Finset.range n, v i) atTop (𝓝 s) :=
  definition_1_2_8_iff _ _

/-- **Definition 1.2.18** of [han2009theoretical]. Let $V_1 \subseteq V_2$ be subsets of a normed
space $V$. Then $V_1$ is **dense** in $V_2$ if for every $u \in V_2$ and every $\varepsilon > 0$
there is a $v \in V_1$ with $\|v - u\| < \varepsilon$.

The predicate does not require $V_1 \subseteq V_2$. It says that $V_2$ lies in the closure of
$V_1$, by `AtkinsonHan.Chapter01.definition_1_2_18_iff`, and for $V_2 = V$ it is `Dense V₁`, by
`AtkinsonHan.Chapter01.definition_1_2_18_iff_dense`. -/
def definition_1_2_18 {V : Type*} [NormedAddCommGroup V] (V₁ V₂ : Set V) : Prop :=
  ∀ u ∈ V₂, ∀ ε > 0, ∃ v ∈ V₁, ‖v - u‖ < ε

/-- For subsets $V_1, V_2$ of a normed space, $V_1$ is dense in $V_2$ in the sense of Definition
1.2.18 of [han2009theoretical] if and only if $V_2$ is contained in the closure of $V_1$. -/
theorem definition_1_2_18_iff (V₁ V₂ : Set V) :
    definition_1_2_18 V₁ V₂ ↔ V₂ ⊆ closure V₁ := by
  constructor
  · intro h u hu
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨v, hv, hvu⟩ := h u hu ε hε
    exact ⟨v, hv, by rwa [dist_eq_norm, norm_sub_rev]⟩
  · intro h u hu ε hε
    obtain ⟨v, hv, hvu⟩ := Metric.mem_closure_iff.mp (h hu) ε hε
    exact ⟨v, hv, by rwa [dist_eq_norm, norm_sub_rev] at hvu⟩

/-- A subset $V_1$ of a normed space $V$ is dense in $V$ in the sense of Definition 1.2.18 of
[han2009theoretical] if and only if it is `Dense`. -/
theorem definition_1_2_18_iff_dense (V₁ : Set V) :
    definition_1_2_18 V₁ Set.univ ↔ Dense V₁ := by
  rw [definition_1_2_18_iff, dense_iff_closure_eq, Set.univ_subset_iff, eq_comm]

/-- **Definition 1.2.20(a)** of [han2009theoretical]. Let $V$ be an infinite-dimensional normed
space over $\mathbb{K}$, and let $\{v_i\}_{i \ge 0}$ be a sequence in $V$. Then $\{v_i\}$ is a
**countably-infinite basis** of $V$ if for every $u \in V$ there are scalars $\alpha_{n,i}$ with
$$\Big\|u - \sum_{i < n} \alpha_{n,i} v_i\Big\| \to 0 \quad \text{as } n \to \infty.$$ The space
$V$ is then called **separable**. The book calls $\{v_i\}$ a basis if, in addition, each finite
subfamily of $\{v_i\}$ is linearly independent.

The predicate is the approximation property alone, which is what makes $V$ separable in the
sense of `TopologicalSpace.SeparableSpace`. It does not assume that $V$ is infinite dimensional.
The linear independence of the finite subfamilies is Definition 1.1.5. -/
def definition_1_2_20 (𝕜 : Type*) {V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    (v : ℕ → V) : Prop :=
  ∀ u : V, ∃ α : ℕ → ℕ → 𝕜, definition_1_2_8 (fun n => ∑ i ∈ Finset.range n, α n i • v i) u

/-- **Definition 1.2.20(b)** of [han2009theoretical]. A sequence $\{v_n\}$ in a normed space $V$
over $\mathbb{K}$ is a **Schauder basis** of $V$ if every $u \in V$ is the sum
$u = \sum_n \alpha_n v_n$ of a convergent series (Definition 1.2.17) for a unique sequence of
scalars $\{\alpha_n\}$.

Mathlib's counterpart is `SchauderBasis 𝕜 V`, an abbreviation for `GeneralSchauderBasis ℕ 𝕜 V
(SummationFilter.conditional ℕ)`. A Schauder basis is a countably-infinite basis in the sense of
clause (a), by `AtkinsonHan.Chapter01.definition_1_2_20_of_schauder`. -/
def definition_1_2_20_schauder (𝕜 : Type*) {V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] (v : ℕ → V) : Prop :=
  ∀ u : V, ∃! α : ℕ → 𝕜, definition_1_2_17 (fun n => α n • v n) u

/-- A Schauder basis in the sense of Definition 1.2.20(b) of [han2009theoretical] is a
countably-infinite basis in the sense of Definition 1.2.20(a): take $\alpha_{n,i} = \alpha_i$
for all $n$. -/
theorem definition_1_2_20_of_schauder {v : ℕ → V} (h : definition_1_2_20_schauder 𝕜 v) :
    definition_1_2_20 𝕜 v := by
  intro u
  obtain ⟨α, hα, -⟩ := h u
  exact ⟨fun _ i => α i, hα⟩

/-- **Definition 1.2.21** of [han2009theoretical]. A sequence $\{u_n\}$ in a normed space is a
**Cauchy sequence** if $\|u_m - u_n\| \to 0$ as $m, n \to \infty$, that is, if for every
$\varepsilon > 0$ there is an $N$ with $\|u_m - u_n\| < \varepsilon$ for all $m, n \ge N$.

The predicate is `CauchySeq` by `AtkinsonHan.Chapter01.definition_1_2_21_iff`. -/
def definition_1_2_21 {V : Type*} [NormedAddCommGroup V] (u : ℕ → V) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖u m - u n‖ < ε

/-- A sequence in a normed space is a Cauchy sequence in the sense of Definition 1.2.21 of
[han2009theoretical] if and only if it is `CauchySeq`. -/
theorem definition_1_2_21_iff (u : ℕ → V) : definition_1_2_21 u ↔ CauchySeq u := by
  rw [Metric.cauchySeq_iff]
  simp [definition_1_2_21, dist_eq_norm]

/-- **Example 1.2.22** of [han2009theoretical], first half. Let $D \subseteq \mathbb{R}^d$ be
compact. Then $C(D)$ with the maximum norm is a Banach space, because a uniform limit of
continuous functions is continuous.

The compact set $D$ stands for the book's $\bar\Omega$. The second half of the example is
`AtkinsonHan.Chapter01.example_1_2_22_incomplete`. -/
theorem example_1_2_22 {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} (hD : IsCompact D) :
    CompleteSpace C(D, ℝ) :=
  have : CompactSpace D := isCompact_iff_compactSpace.mp hD
  inferInstance

/-! ### Example 1.2.22, second half: $C[0, 1]$ with $\|\cdot\|_p$ is not complete -/

section Incomplete

/-- The ramp $u_n$ of Example 1.2.22: $u_n(x) = 0$ for $x \le 1/2$, $u_n$ rises linearly to $1$ at
$x = 1/2 + 1/(n + 1)$, and $u_n(x) = 1$ from there on. -/
private noncomputable def ramp (n : ℕ) (x : ℝ) : ℝ :=
  min 1 (max 0 (((n : ℝ) + 1) * (x - 1 / 2)))

private theorem continuous_ramp (n : ℕ) : Continuous (ramp n) := by
  unfold ramp
  fun_prop

private theorem ramp_nonneg (n : ℕ) (x : ℝ) : 0 ≤ ramp n x :=
  le_min zero_le_one (le_max_left _ _)

private theorem ramp_le_one (n : ℕ) (x : ℝ) : ramp n x ≤ 1 := min_le_left _ _

private theorem ramp_eq_zero {n : ℕ} {x : ℝ} (hx : x ≤ 1 / 2) : ramp n x = 0 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have h : ((n : ℝ) + 1) * (x - 1 / 2) ≤ 0 := by nlinarith
  rw [ramp, max_eq_left h, min_eq_right zero_le_one]

private theorem ramp_eq_one {n : ℕ} {x : ℝ} (hx : 1 / 2 + 1 / ((n : ℝ) + 1) ≤ x) :
    ramp n x = 1 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : 1 / ((n : ℝ) + 1) ≤ x - 1 / 2 := by linarith
  have h : (1 : ℝ) ≤ ((n : ℝ) + 1) * (x - 1 / 2) := by
    calc (1 : ℝ) = ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) := by field_simp
      _ ≤ ((n : ℝ) + 1) * (x - 1 / 2) := by exact mul_le_mul_of_nonneg_left h1 hn.le
  rw [ramp, max_eq_right (by linarith), min_eq_left h]

/-- If $p > 0$, $a < b$, $w$ is continuous on $[a, b]$ and $\int_a^b |w(x)|^p \, dx = 0$, then
$w = 0$ on $(a, b)$. -/
private theorem eqOn_zero_of_integral_rpow_eq_zero {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {w : ℝ → ℝ} (hw : ContinuousOn w (Set.Icc a b)) (h : (∫ x in a..b, |w x| ^ p) = 0)
    (x : ℝ) (hx : x ∈ Set.Ioo a b) : w x = 0 := by
  by_contra hne
  set F : ℝ → ℝ := fun y => |w y| ^ p with hF
  have hFcont : ContinuousOn F (Set.Ioo a b) :=
    ((hw.mono Set.Ioo_subset_Icc_self).abs).rpow_const fun _ _ => Or.inr hp.le
  have hFint : IntervalIntegrable F volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab.le]
    exact hw.abs.rpow_const fun _ _ => Or.inr hp.le
  set U : Set ℝ := Set.Ioo a b ∩ F ⁻¹' {y : ℝ | y ≠ 0} with hU
  have hUopen : IsOpen U := hFcont.isOpen_inter_preimage isOpen_Ioo isOpen_ne
  have hUne : U.Nonempty := by
    refine ⟨x, hx, ?_⟩
    simp only [hF]
    exact fun hc => hne (abs_eq_zero.mp ((Real.rpow_eq_zero_iff_of_nonneg (abs_nonneg _)).mp hc).1)
  rw [intervalIntegral.integral_of_le hab.le] at h
  have hae : F =ᵐ[volume.restrict (Set.Ioc a b)] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg
      (fun y => Real.rpow_nonneg (abs_nonneg _) p)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp hFint)).mp h
  have hnull : volume.restrict (Set.Ioc a b) {y | F y ≠ 0} = 0 := by
    have := MeasureTheory.ae_iff.mp hae
    simpa using this
  have hsub : U ⊆ {y | F y ≠ 0} := fun y hy => hy.2
  have hUnull : volume U = 0 := by
    have h1 : volume.restrict (Set.Ioc a b) U = 0 :=
      MeasureTheory.measure_mono_null hsub hnull
    rwa [MeasureTheory.Measure.restrict_apply hUopen.measurableSet,
      Set.inter_eq_self_of_subset_left
        (fun y (hy : y ∈ U) => Set.Ioo_subset_Ioc_self hy.1)] at h1
  exact absurd hUnull (ne_of_gt (hUopen.measure_pos volume hUne))

/-- If $v$ is continuous on $[0, 1]$ and $s_k \to z$ with $s_k, z \in [0, 1]$, then
$v(s_k) \to v(z)$. -/
private theorem tendsto_val_of_continuousOn {v : ℝ → ℝ} (hv : ContinuousOn v (Set.Icc 0 1))
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) {s : ℕ → ℝ} (hs : ∀ k, s k ∈ Set.Icc (0 : ℝ) 1)
    (hlim : Tendsto s atTop (𝓝 z)) : Tendsto (fun k => v (s k)) atTop (𝓝 (v z)) :=
  Filter.Tendsto.comp (hv z hz) (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hs⟩)

/-- The sequence $1/(k + 3)$ tends to $0$. -/
private theorem tendsto_one_div_add_three :
    Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 3)) atTop (𝓝 0) := by
  have h : Tendsto (fun k : ℕ => (k : ℝ) + 3) atTop atTop :=
    tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop
  refine h.inv_tendsto_atTop.congr fun k => ?_
  simp [one_div]

/-- If $p > 0$, $N \ge 1$ and $m, n \ge N$, then $\int_0^1 |u_m(x) - u_n(x)|^p \, dx \le 1/(N + 1)$
for the ramps $u_m, u_n$. -/
private theorem integral_ramp_sub_le {p : ℝ} (hp : 0 < p) {N m n : ℕ} (hN : 1 ≤ N) (hm : N ≤ m)
    (hn : N ≤ n) : (∫ x in (0 : ℝ)..1, |ramp m x - ramp n x| ^ p) ≤ 1 / ((N : ℝ) + 1) := by
  have hdc : Continuous fun x => |ramp m x - ramp n x| ^ p :=
    (((continuous_ramp m).sub (continuous_ramp n)).abs).rpow_const fun _ => Or.inr hp.le
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNle : 1 / ((N : ℝ) + 1) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  set c : ℝ := 1 / 2 + 1 / ((N : ℝ) + 1) with hc
  have hpos : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  have hc2 : (1 : ℝ) / 2 < c := by rw [hc]; linarith
  have hc1 : c ≤ 1 := by rw [hc]; linarith
  have hmono : ∀ k : ℕ, N ≤ k → 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
    intro k hk
    have hk' : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    exact one_div_le_one_div_of_le hNpos (by linarith)
  have hzeroL : Set.EqOn (fun x => |ramp m x - ramp n x| ^ p) (fun _ => (0 : ℝ))
      (Set.uIcc (0 : ℝ) (1 / 2)) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1 / 2)] at hx
    have hrm : ramp m x = 0 := ramp_eq_zero hx.2
    have hrn : ramp n x = 0 := ramp_eq_zero hx.2
    simp [hrm, hrn, Real.zero_rpow hp.ne']
  have hzeroR : Set.EqOn (fun x => |ramp m x - ramp n x| ^ p) (fun _ => (0 : ℝ))
      (Set.uIcc c 1) := by
    intro x hx
    rw [Set.uIcc_of_le hc1] at hx
    have hcx : 1 / 2 + 1 / ((N : ℝ) + 1) ≤ x := by
      have h := hx.1
      rw [hc] at h
      exact h
    have hrm : ramp m x = 1 := ramp_eq_one (by linarith [hmono m hm])
    have hrn : ramp n x = 1 := ramp_eq_one (by linarith [hmono n hn])
    simp [hrm, hrn, Real.zero_rpow hp.ne']
  have hmid : (∫ x in (1 / 2 : ℝ)..c, |ramp m x - ramp n x| ^ p) ≤ 1 / ((N : ℝ) + 1) := by
    have hle : ∀ x ∈ Set.Icc (1 / 2 : ℝ) c, |ramp m x - ramp n x| ^ p ≤ 1 := by
      intro x _
      refine Real.rpow_le_one (abs_nonneg _) ?_ hp.le
      rw [abs_le]
      exact ⟨by linarith [ramp_nonneg m x, ramp_le_one n x],
        by linarith [ramp_nonneg n x, ramp_le_one m x]⟩
    calc (∫ x in (1 / 2 : ℝ)..c, |ramp m x - ramp n x| ^ p)
        ≤ ∫ _ in (1 / 2 : ℝ)..c, (1 : ℝ) :=
          intervalIntegral.integral_mono_on hc2.le (hdc.intervalIntegrable _ _)
            intervalIntegrable_const hle
      _ = 1 / ((N : ℝ) + 1) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, hc]; ring
  have hsplit : (∫ x in (0 : ℝ)..1, |ramp m x - ramp n x| ^ p)
      = (∫ x in (0 : ℝ)..(1 / 2), |ramp m x - ramp n x| ^ p)
        + (∫ x in (1 / 2 : ℝ)..c, |ramp m x - ramp n x| ^ p)
        + ∫ x in c..(1 : ℝ), |ramp m x - ramp n x| ^ p := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hdc.intervalIntegrable _ _)
        (hdc.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hdc.intervalIntegrable _ _)
        (hdc.intervalIntegrable _ _)]
  rw [hsplit, intervalIntegral.integral_congr hzeroL, intervalIntegral.integral_congr hzeroR,
    intervalIntegral.integral_zero, intervalIntegral.integral_zero, zero_add, add_zero]
  exact hmid

/-- **Example 1.2.22** of [han2009theoretical], second half. Let $1 \le p < \infty$. The space
$C[0, 1]$ with the norm $\|v\|_p = (\int_0^1 |v(x)|^p \, dx)^{1/p}$ is not complete: there are
continuous functions $u_n : \mathbb{R} \to \mathbb{R}$ that form a Cauchy sequence for
$\|\cdot\|_p$, that is, for every $\varepsilon > 0$ there is an $N$ with
$\|u_m - u_n\|_p < \varepsilon$ for all $m, n \ge N$, while no function $v$ continuous on
$[0, 1]$ satisfies $\|u_n - v\|_p \to 0$.

This is the case $\Omega = (0, 1)$ of the book's statement that $C(\bar\Omega)$ with the norm
(1.2.9) is not complete. The witnesses are the book's ramps, which rise linearly from $0$ to $1$
on an interval of width $1/(n + 1)$ to the right of $x = 1/2$. They are Cauchy, because two of
them with index at least $N$ differ only on an interval of width $1/(N + 1)$, where the
difference is at most $1$. A continuous limit would vanish on $(0, 1/2)$ and equal $1$ on
$(1/2, 1)$, which is impossible. An element of $C[0, 1]$ is represented by a function
$v : \mathbb{R} \to \mathbb{R}$ continuous on $[0, 1]$, which is all that the integral uses. -/
theorem example_1_2_22_incomplete {p : ℝ} (hp : 1 ≤ p) :
    ∃ u : ℕ → ℝ → ℝ, (∀ n, Continuous (u n)) ∧
      (∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
        (∫ x in (0 : ℝ)..1, |u m x - u n x| ^ p) ^ (1 / p) < ε) ∧
      ∀ v : ℝ → ℝ, ContinuousOn v (Set.Icc 0 1) →
        ¬ Tendsto (fun n => (∫ x in (0 : ℝ)..1, |u n x - v x| ^ p) ^ (1 / p)) atTop (𝓝 0) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  refine ⟨ramp, continuous_ramp, fun ε hε => ?_, ?_⟩
  · -- the ramps are `‖·‖_p` Cauchy
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε ^ p)
    refine ⟨max 1 K, fun m hm n hn => ?_⟩
    set N := max 1 K with hNdef
    have hN1 : 1 ≤ N := le_max_left _ _
    have hNK : (K : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_max_right 1 K
    have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hεp : (0 : ℝ) < ε ^ p := Real.rpow_pos_of_pos hε p
    have hlt : 1 / ((N : ℝ) + 1) < ε ^ p := by
      have h1 : 1 / ε ^ p < (N : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ hεp] at h1
      rw [div_lt_iff₀ hNpos]
      linarith [mul_comm ((N : ℝ) + 1) (ε ^ p)]
    have hnn : (0 : ℝ) ≤ ∫ x in (0 : ℝ)..1, |ramp m x - ramp n x| ^ p :=
      intervalIntegral.integral_nonneg (by norm_num) fun x _ => Real.rpow_nonneg (abs_nonneg _) p
    calc (∫ x in (0 : ℝ)..1, |ramp m x - ramp n x| ^ p) ^ (1 / p)
        ≤ (1 / ((N : ℝ) + 1)) ^ (1 / p) :=
          Real.rpow_le_rpow hnn (integral_ramp_sub_le hp0 hN1 hm hn) (by positivity)
      _ < (ε ^ p) ^ (1 / p) := Real.rpow_lt_rpow (by positivity) hlt (by positivity)
      _ = ε := by rw [← Real.rpow_mul hε.le, mul_one_div_cancel hp0.ne', Real.rpow_one]
  · -- and they have no continuous limit
    intro v hv hlim
    set A : ℕ → ℝ := fun n => ∫ x in (0 : ℝ)..1, |ramp n x - v x| ^ p with hAdef
    have hcontn : ∀ n : ℕ, ContinuousOn (fun x => |ramp n x - v x| ^ p) (Set.Icc 0 1) :=
      fun n => (((continuous_ramp n).continuousOn.sub hv).abs).rpow_const
        fun _ _ => Or.inr hp0.le
    have hint : ∀ (n : ℕ) (a b : ℝ), Set.uIcc a b ⊆ Set.Icc (0 : ℝ) 1 →
        IntervalIntegrable (fun x => |ramp n x - v x| ^ p) volume a b :=
      fun n _ _ hsub => ContinuousOn.intervalIntegrable ((hcontn n).mono hsub)
    have hnonneg : ∀ a b : ℝ, a ≤ b → ∀ n : ℕ,
        0 ≤ ∫ x in a..b, |ramp n x - v x| ^ p :=
      fun a b hab n => intervalIntegral.integral_nonneg hab fun x _ =>
        Real.rpow_nonneg (abs_nonneg _) p
    have hA0 : ∀ n, 0 ≤ A n := fun n => hnonneg 0 1 (by norm_num) n
    have hAlim : Tendsto A atTop (𝓝 0) := by
      have hc : ContinuousAt (fun t : ℝ => t ^ p) 0 :=
        Real.continuousAt_rpow_const 0 p (Or.inr hp0.le)
      have h := hc.tendsto.comp hlim
      rw [Real.zero_rpow hp0.ne'] at h
      refine h.congr fun n => ?_
      simp only [Function.comp_apply]
      rw [← Real.rpow_mul (hA0 n), one_div, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
    -- the limit vanishes on `(0, 1/2)`
    have hsub1 : Set.uIcc (0 : ℝ) (1 / 2) ⊆ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1 / 2)]
      exact Set.Icc_subset_Icc le_rfl (by norm_num)
    have hsub2 : Set.uIcc (1 / 2 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)]
      exact Set.Icc_subset_Icc (by norm_num) le_rfl
    have hleft : (∫ x in (0 : ℝ)..(1 / 2), |v x| ^ p) = 0 := by
      refine le_antisymm ?_ (intervalIntegral.integral_nonneg (by norm_num) fun x _ =>
        Real.rpow_nonneg (abs_nonneg _) p)
      refine ge_of_tendsto hAlim (Eventually.of_forall fun n => ?_)
      have hEq : Set.EqOn (fun x => |v x| ^ p) (fun x => |ramp n x - v x| ^ p)
          (Set.uIcc (0 : ℝ) (1 / 2)) := by
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1 / 2)] at hx
        have hr : ramp n x = 0 := ramp_eq_zero hx.2
        simp [hr]
      rw [intervalIntegral.integral_congr hEq, hAdef]
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hint n 0 (1 / 2) hsub1) (hint n (1 / 2) 1 hsub2)
      linarith [hnonneg (1 / 2) 1 (by norm_num) n]
    have hv0 : ∀ x ∈ Set.Ioo (0 : ℝ) (1 / 2), v x = 0 :=
      eqOn_zero_of_integral_rpow_eq_zero hp0 (by norm_num)
        (hv.mono (Set.Icc_subset_Icc le_rfl (by norm_num))) hleft
    -- and equals `1` on `(1/2, 1)`
    have hright : ∀ a : ℝ, 1 / 2 < a → a < 1 → (∫ x in a..(1 : ℝ), |1 - v x| ^ p) = 0 := by
      intro a ha1 ha2
      have hsubA : Set.uIcc (0 : ℝ) a ⊆ Set.Icc (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ a)]
        exact Set.Icc_subset_Icc le_rfl ha2.le
      have hsubB : Set.uIcc a (1 : ℝ) ⊆ Set.Icc (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le ha2.le]
        exact Set.Icc_subset_Icc (by linarith) le_rfl
      refine le_antisymm ?_ (intervalIntegral.integral_nonneg ha2.le fun x _ =>
        Real.rpow_nonneg (abs_nonneg _) p)
      obtain ⟨K, hK⟩ := exists_nat_gt (1 / (a - 1 / 2))
      refine ge_of_tendsto hAlim (Filter.eventually_atTop.2 ⟨K, fun n hn => ?_⟩)
      have hapos : (0 : ℝ) < a - 1 / 2 := by linarith
      have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hKn : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hna : 1 / ((n : ℝ) + 1) ≤ a - 1 / 2 := by
        have h1 : 1 / (a - 1 / 2) < (n : ℝ) + 1 := by linarith
        rw [div_lt_iff₀ hapos] at h1
        rw [div_le_iff₀ hnpos]
        nlinarith
      have hEq : Set.EqOn (fun x => |1 - v x| ^ p) (fun x => |ramp n x - v x| ^ p)
          (Set.uIcc a 1) := by
        intro x hx
        rw [Set.uIcc_of_le ha2.le] at hx
        have hr : ramp n x = 1 := ramp_eq_one (by linarith [hx.1])
        simp [hr]
      rw [intervalIntegral.integral_congr hEq, hAdef]
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hint n 0 a hsubA) (hint n a 1 hsubB)
      linarith [hnonneg 0 a (by linarith) n]
    have hv1 : ∀ a : ℝ, 1 / 2 < a → a < 1 → ∀ x ∈ Set.Ioo a 1, v x = 1 := by
      intro a ha1 ha2 x hx
      have h := eqOn_zero_of_integral_rpow_eq_zero hp0 ha2
        (continuousOn_const.sub (hv.mono (Set.Icc_subset_Icc (by linarith) le_rfl)))
        (hright a ha1 ha2) x hx
      simp only [Pi.sub_apply] at h
      linarith
    -- the two descriptions clash at `1/2`
    have hhalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    have hk3 : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 3 := fun k => by positivity
    have hk3' : ∀ k : ℕ, 1 / ((k : ℝ) + 3) ≤ 1 / 3 := fun k =>
      one_div_le_one_div_of_le (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
    have hvzero : v (1 / 2) = 0 := by
      have hs : ∀ k : ℕ, (1 : ℝ) / 2 - 1 / ((k : ℝ) + 3) ∈ Set.Icc (0 : ℝ) 1 := fun k =>
        ⟨by linarith [hk3' k, one_div_pos.2 (hk3 k)], by linarith [one_div_pos.2 (hk3 k)]⟩
      have hstend : Tendsto (fun k : ℕ => (1 : ℝ) / 2 - 1 / ((k : ℝ) + 3)) atTop (𝓝 (1 / 2)) := by
        simpa using tendsto_const_nhds.sub tendsto_one_div_add_three
      have h1 := tendsto_val_of_continuousOn hv hhalf hs hstend
      have h2 : ∀ k : ℕ, v ((1 : ℝ) / 2 - 1 / ((k : ℝ) + 3)) = 0 := fun k =>
        hv0 _ ⟨by linarith [hk3' k], by linarith [one_div_pos.2 (hk3 k)]⟩
      exact tendsto_nhds_unique (h1.congr h2) tendsto_const_nhds
    have hvone : v (1 / 2) = 1 := by
      have ht : ∀ k : ℕ, (1 : ℝ) / 2 + 1 / ((k : ℝ) + 3) ∈ Set.Icc (0 : ℝ) 1 := fun k =>
        ⟨by linarith [one_div_pos.2 (hk3 k)], by linarith [hk3' k]⟩
      have httend : Tendsto (fun k : ℕ => (1 : ℝ) / 2 + 1 / ((k : ℝ) + 3)) atTop (𝓝 (1 / 2)) := by
        simpa using tendsto_const_nhds.add tendsto_one_div_add_three
      have h2 : ∀ k : ℕ, v ((1 : ℝ) / 2 + 1 / ((k : ℝ) + 3)) = 1 := by
        intro k
        have hhalfk : 1 / (2 * ((k : ℝ) + 3)) < 1 / ((k : ℝ) + 3) :=
          one_div_lt_one_div_of_lt (hk3 k) (by linarith [hk3 k])
        have hposk : (0 : ℝ) < 1 / (2 * ((k : ℝ) + 3)) := by positivity
        exact hv1 (1 / 2 + 1 / (2 * ((k : ℝ) + 3))) (by linarith)
          (by linarith [hk3' k, hhalfk]) _ ⟨by linarith, by linarith [hk3' k]⟩
      have h1 := tendsto_val_of_continuousOn hv hhalf ht httend
      exact tendsto_nhds_unique (h1.congr h2) tendsto_const_nhds
    exact absurd (hvzero.symm.trans hvone) (by norm_num)

end Incomplete

/-- **Proposition 1.2.23** of [han2009theoretical]. Let $\{u_n\}$ be a Cauchy sequence in a normed
space $V$, and let $\varphi : \mathbb{N} \to \mathbb{N}$ be strictly increasing. If the
subsequence $\{u_{\varphi(n)}\}$ converges to $v$, then $u_n \to v$. -/
theorem proposition_1_2_23 {u : ℕ → V} (hu : CauchySeq u) {φ : ℕ → ℕ} (hφ : StrictMono φ) {v : V}
    (h : Tendsto (u ∘ φ) atTop (𝓝 v)) : Tendsto u atTop (𝓝 v) :=
  tendsto_nhds_of_cauchySeq_of_subseq hu hφ.tendsto_atTop h

/-- **Definition 1.2.24** of [han2009theoretical]. A normed space $V$ is **complete** if every
Cauchy sequence in $V$ converges to an element of $V$. A complete normed space is a **Banach
space**. The theorem states that `CompleteSpace V` holds if and only if every Cauchy sequence in
the sense of Definition 1.2.21 converges in the sense of Definition 1.2.8.

Mathlib has no bundled Banach space. This library assumes `NormedAddCommGroup`, `NormedSpace`
and `CompleteSpace` instead. -/
theorem definition_1_2_24 (V : Type*) [NormedAddCommGroup V] :
    CompleteSpace V ↔ ∀ u : ℕ → V, definition_1_2_21 u → ∃ v : V, definition_1_2_8 u v := by
  simp only [definition_1_2_21_iff, definition_1_2_8_iff]
  exact ⟨fun _ _ hu => cauchySeq_tendsto_of_complete hu, Metric.complete_of_cauchySeq_tendsto⟩

/-- **Theorem 1.2.14** of [han2009theoretical]. On a finite-dimensional linear space any two norms
are equivalent. Precisely, let $V$ and $W$ be normed spaces over $\mathbb{K}$ with $V$ finite
dimensional, and let $e : V \to W$ be a linear bijection. Then there are constants
$c_1, c_2 > 0$ with $$c_1 \|v\| \le \|e v\| \le c_2 \|v\| \qquad \text{for all } v \in V.$$

A Lean type carries one norm, so the two norms of the book are $\|v\|$ and $\|e v\|$. The
conclusion is the equivalence of norms of Definition 1.2.12, which is not stated separately.
Both bounds come from the continuity of a linear map on a finite-dimensional space, applied to
$e$ and to $e^{-1}$. -/
theorem theorem_1_2_14 {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [FiniteDimensional 𝕜 V] (e : V ≃ₗ[𝕜] W) :
    ∃ c₁ > 0, ∃ c₂ > 0, ∀ v : V, c₁ * ‖v‖ ≤ ‖e v‖ ∧ ‖e v‖ ≤ c₂ * ‖v‖ := by
  have _ : FiniteDimensional 𝕜 W := e.finiteDimensional
  set E : V ≃L[𝕜] W := e.toContinuousLinearEquiv
  have hcoe : ∀ v : V, E v = e v := fun _ => rfl
  refine ⟨(‖(E.symm : W →L[𝕜] V)‖ + 1)⁻¹, by positivity, ‖(E : V →L[𝕜] W)‖ + 1, by positivity,
    fun v => ⟨?_, ?_⟩⟩
  · rw [inv_mul_le_iff₀ (by positivity), ← hcoe]
    calc ‖v‖ = ‖E.symm (E v)‖ := by simp
      _ ≤ ‖(E.symm : W →L[𝕜] V)‖ * ‖E v‖ := (E.symm : W →L[𝕜] V).le_opNorm _
      _ ≤ (‖(E.symm : W →L[𝕜] V)‖ + 1) * ‖E v‖ := by nlinarith [norm_nonneg (E v)]
  · rw [← hcoe]
    calc ‖E v‖ ≤ ‖(E : V →L[𝕜] W)‖ * ‖v‖ := (E : V →L[𝕜] W).le_opNorm _
      _ ≤ (‖(E : V →L[𝕜] W)‖ + 1) * ‖v‖ := by nlinarith [norm_nonneg v]

/-- **Theorem 1.2.25** of [han2009theoretical], existence. Every normed space $V$ has a completion:
a Banach space $\hat V$ with a linear isometry $V \to \hat V$ whose range is dense in $\hat V$.

The completion is `UniformSpace.Completion V`, and the isometry is
`UniformSpace.Completion.toComplₗᵢ`. -/
theorem theorem_1_2_25 :
    CompleteSpace (UniformSpace.Completion V) ∧
      DenseRange (UniformSpace.Completion.toComplₗᵢ : V →ₗᵢ[𝕜] UniformSpace.Completion V) :=
  ⟨inferInstance, UniformSpace.Completion.denseRange_coe⟩

/-- **Theorem 1.2.25** of [han2009theoretical], uniqueness. Let $V$ be a normed space, let $W$ be a
Banach space, and let $I : V \to W$ be a linear isometry with dense range. Then there is a
linear isometric isomorphism $e$ from the completion $\hat V$ of $V$ onto $W$ with $e(v) = I(v)$
for all $v \in V$. Hence any two completions of $V$ are isometrically isomorphic, by an
isomorphism that fixes the embedded copy of $V$.

The completion is `UniformSpace.Completion V`. -/
theorem theorem_1_2_25_uniqueness {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [CompleteSpace W] (I : V →ₗᵢ[𝕜] W) (hI : DenseRange I) :
    ∃ e : UniformSpace.Completion V ≃ₗᵢ[𝕜] W, ∀ v : V, e v = I v := by
  set f : UniformSpace.Completion V →L[𝕜] W := I.toContinuousLinearMap.fromCompletion with hf
  have hcoe : ∀ v : V, f v = I v := by simp [hf]
  have hnorm : ∀ x : UniformSpace.Completion V, ‖f x‖ = ‖x‖ := by
    intro x
    refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop))
      fun v => ?_
    rw [hcoe, I.norm_map, UniformSpace.Completion.norm_coe]
  let g : UniformSpace.Completion V →ₗᵢ[𝕜] W := ⟨f.toLinearMap, hnorm⟩
  have hsub : Set.range I ⊆ Set.range g := by
    rintro w ⟨v, rfl⟩
    exact ⟨(v : UniformSpace.Completion V), hcoe v⟩
  have hsurj : Function.Surjective g :=
    Set.range_eq_univ.mp <| by
      rw [← g.isometry.isClosedEmbedding.isClosed_range.closure_eq, (hI.mono hsub).closure_eq]
  exact ⟨LinearIsometryEquiv.ofSurjective g hsurj, hcoe⟩

/-- **Example 1.2.28(a)** of [han2009theoretical], the space $C^m[a, b]$. Let $a \le b$ and
$m \in \mathbb{N}$. The space $C^m[a, b]$ with the norm
$\|v\| = \sum_{j=0}^m \|v^{(j)}\|_\infty$ is a Banach space. This norm is equivalent to the norm
of Example 1.2.5(b): $$\max_{0 \le j \le m} \|v^{(j)}\|_\infty \le \|v\| \le (m + 1) \max_{0 \le
j \le m} \|v^{(j)}\|_\infty.$$ So $C^m[a, b]$ is complete for either norm.

The space is the backbone's `ContDiffMapIcc hab m`, whose norm is the sum, the norm (2.1.2) that
the book uses in §2.1. The maximum is the supremum `⨆ j`. The clause about $C_p^k(2\pi)$ is
`AtkinsonHan.Chapter01.example_1_2_28_a_periodic`, and clause (b) is
`AtkinsonHan.Chapter01.example_1_2_28_b`. -/
theorem example_1_2_28_a {a b : ℝ} (hab : a ≤ b) (m : ℕ) :
    (∀ v : ContDiffMapIcc hab m, ⨆ j, ‖v.deriv j‖ ≤ ‖v‖) ∧
      (∀ v : ContDiffMapIcc hab m, ‖v‖ ≤ (m + 1) * ⨆ j, ‖v.deriv j‖) ∧
      CompleteSpace (ContDiffMapIcc hab m) :=
  ⟨ContDiffMapIcc.iSup_norm_deriv_le_norm, ContDiffMapIcc.norm_le_iSup_norm_deriv, inferInstance⟩

/-- **Example 1.2.28(a)** of [han2009theoretical], the space $C_p^k(2\pi)$. Let $k \in \mathbb{N}$,
and read $C_p^k(2\pi)$ on one period, as the subspace of $C^k[0, 2\pi]$ of the functions $v$
with $v^{(j)}(0) = v^{(j)}(2\pi)$ for $0 \le j \le k$. With the norm
$\|v\| = \sum_{j=0}^k \|v^{(j)}\|_\infty$ this space is a Banach space, and $$\max_{0 \le j \le
k} \|v^{(j)}\|_\infty \le \|v\| \le (k + 1) \max_{0 \le j \le k} \|v^{(j)}\|_\infty.$$ Moreover,
every element is the restriction to $[0, 2\pi]$ of a $2\pi$-periodic function on $\mathbb{R}$ of
class $C^k$, and every $2\pi$-periodic function of class $C^k$ on $\mathbb{R}$ restricts to an
element.

The space is the backbone's `ContDiffMapIcc.periodicBoundary (Real.two_pi_pos.le : (0 : ℝ) ≤ 2 *
π) k`. The last two conjuncts identify it with the book's space, so nothing is lost by working
on one period. At $k = 0$ the space agrees with the space `C(AddCircle (2 * π), ℝ)` of
`AtkinsonHan.Chapter01.example_1_2_5`, because a continuous function on the circle is a
continuous function on $[0, 2\pi]$ with equal values at the two ends. The circle has no
higher-order analogue here, because Mathlib has no differential calculus on `AddCircle`. -/
theorem example_1_2_28_a_periodic (k : ℕ) :
    (∀ v : ContDiffMapIcc.periodicBoundary (Real.two_pi_pos.le : (0 : ℝ) ≤ 2 * π) k,
        ⨆ j, ‖(v : ContDiffMapIcc (Real.two_pi_pos.le : (0 : ℝ) ≤ 2 * π) k).deriv j‖ ≤ ‖v‖) ∧
      (∀ v : ContDiffMapIcc.periodicBoundary (Real.two_pi_pos.le : (0 : ℝ) ≤ 2 * π) k,
        ‖v‖ ≤ (k + 1) * ⨆ j,
          ‖(v : ContDiffMapIcc (Real.two_pi_pos.le : (0 : ℝ) ≤ 2 * π) k).deriv j‖) ∧
      CompleteSpace (ContDiffMapIcc.periodicBoundary (Real.two_pi_pos.le : (0 : ℝ) ≤ 2 * π) k) ∧
      (∀ v : ContDiffMapIcc.periodicBoundary (Real.two_pi_pos.le : (0 : ℝ) ≤ 2 * π) k,
        ∃ f : ℝ → ℝ, Function.Periodic f (2 * π) ∧ ContDiff ℝ k f ∧
          ∀ t : Set.Icc (0 : ℝ) (2 * π),
            f t = (v : ContDiffMapIcc (Real.two_pi_pos.le : (0 : ℝ) ≤ 2 * π) k) t) ∧
      (∀ f : ℝ → ℝ, ContDiff ℝ k f → Function.Periodic f (2 * π) →
        ∃ v : ContDiffMapIcc.periodicBoundary (Real.two_pi_pos.le : (0 : ℝ) ≤ 2 * π) k,
          ∀ t : Set.Icc (0 : ℝ) (2 * π),
            (v : ContDiffMapIcc (Real.two_pi_pos.le : (0 : ℝ) ≤ 2 * π) k) t = f t) := by
  have hab : (0 : ℝ) ≤ 2 * π := Real.two_pi_pos.le
  have hT : 2 * π - 0 = 2 * π := sub_zero _
  refine ⟨fun v => ContDiffMapIcc.iSup_norm_deriv_le_norm _,
    fun v => ContDiffMapIcc.norm_le_iSup_norm_deriv _, inferInstance, fun v => ?_,
    fun f hf hper => ?_⟩
  · obtain ⟨g, hgper, hgC, hgeq⟩ :=
      ContDiffMapIcc.exists_periodic_contDiff Real.two_pi_pos v.1 v.2
    exact ⟨g, hT ▸ hgper, hgC, hgeq⟩
  · exact ⟨⟨ContDiffMapIcc.ofContDiff hab hf,
      ContDiffMapIcc.ofContDiff_mem_periodicBoundary hab hf (by rw [hT]; exact hper)⟩,
      fun t => rfl⟩

end Normed

/-! ### Example 1.2.28(b): $C^m[a, b]$ with a Sobolev norm, and its completion $W^{m,p}(a, b)$ -/

section Example1228b

noncomputable section

open Set TopologicalSpace

variable {a b : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {m : ℕ}

/-! ### The space $C^m[a, b]$ with the Sobolev norm -/

/-- **Example 1.2.28(b)** of [han2009theoretical], the space. Let $a < b$, $m \in \mathbb{N}$ and
$1 \le p \le \infty$. This is the space $C^m[a, b]$ with the norm of $f$ as an element of the
Sobolev space $W^{m,p}(a, b)$, which for $p < \infty$ is $$\|f\| = \Big[\sum_{j=0}^m
\|f^{(j)}\|_{L^p(a, b)}^p\Big]^{1/p}.$$

The type is a synonym of `ContDiffMapIcc hlt.le m`. Its norm is pulled back from
$W^{m,p}(a, b)$, the backbone's `SobolevIntervalLp m p (Opens.Ioo a b)`, along the injective
inclusion `ContDiffMapIcc.toSobolevIntervalLp`, whose components are the derivatives
$f, f', \dots, f^{(m)}$ in $L^p(a, b)$. The formula for the norm is
`AtkinsonHan.Chapter01.example_1_2_28_b_norm`. -/
def ContDiffMapIccSobolevNorm (hlt : a < b) (m : ℕ) (_p : ℝ≥0∞) : Type :=
  ContDiffMapIcc hlt.le m

namespace ContDiffMapIccSobolevNorm

variable (hlt : a < b) (m : ℕ) (p : ℝ≥0∞)

instance : AddCommGroup (ContDiffMapIccSobolevNorm hlt m p) :=
  inferInstanceAs (AddCommGroup (ContDiffMapIcc hlt.le m))

instance : Module ℝ (ContDiffMapIccSobolevNorm hlt m p) :=
  inferInstanceAs (Module ℝ (ContDiffMapIcc hlt.le m))

/-- The identity map, as a linear equivalence from $C^m[a, b]$ with the Sobolev norm to $C^m[a, b]$
with the norm $\sum_{j \le m} \|f^{(j)}\|_\infty$. It is not an isometry. -/
def equiv : ContDiffMapIccSobolevNorm hlt m p ≃ₗ[ℝ] ContDiffMapIcc hlt.le m :=
  LinearEquiv.refl ℝ _

variable [Fact (1 ≤ p)]

/-- The inclusion of $C^m[a, b]$ into $W^{m,p}(a, b)$, as a linear map. The norm of $C^m[a, b]$ is
induced along it. -/
def toSobolevₗ : ContDiffMapIccSobolevNorm hlt m p →ₗ[ℝ] SobolevIntervalLp m p (Opens.Ioo a b) :=
  (ContDiffMapIcc.toSobolevIntervalLp p hlt.le hlt m : ContDiffMapIcc hlt.le m →ₗ[ℝ] _).comp
    (equiv hlt m p).toLinearMap

variable {hlt m p} in
/-- The inclusion `AtkinsonHan.Chapter01.ContDiffMapIccSobolevNorm.toSobolevₗ` sends $f$ to its
image under `ContDiffMapIcc.toSobolevIntervalLp`. -/
@[simp]
theorem toSobolevₗ_apply (f : ContDiffMapIccSobolevNorm hlt m p) :
    toSobolevₗ hlt m p f = ContDiffMapIcc.toSobolevIntervalLp p hlt.le hlt m (equiv hlt m p f) :=
  rfl

/-- The inclusion of $C^m[a, b]$ into $W^{m,p}(a, b)$ is injective, by
`ContDiffMapIcc.toSobolevIntervalLp_injective`. -/
theorem toSobolevₗ_injective : Function.Injective (toSobolevₗ hlt m p) :=
  (ContDiffMapIcc.toSobolevIntervalLp_injective (p := p) hlt.le hlt m).comp
    (equiv hlt m p).injective

/-- The norm $\|f\| = \|f\|_{W^{m,p}(a, b)}$, induced from $W^{m,p}(a, b)$ along the injective
inclusion. -/
instance : NormedAddCommGroup (ContDiffMapIccSobolevNorm hlt m p) :=
  NormedAddCommGroup.induced (ContDiffMapIccSobolevNorm hlt m p)
    (SobolevIntervalLp m p (Opens.Ioo a b)) (toSobolevₗ hlt m p).toAddMonoidHom
    (toSobolevₗ_injective hlt m p)

variable {hlt m p} in
/-- The norm of $f$ is the $W^{m,p}(a, b)$ norm of its inclusion. -/
theorem norm_eq (f : ContDiffMapIccSobolevNorm hlt m p) : ‖f‖ = ‖toSobolevₗ hlt m p f‖ := rfl

instance : NormedSpace ℝ (ContDiffMapIccSobolevNorm hlt m p) where
  norm_smul_le c f := le_of_eq (by rw [norm_eq, norm_eq, map_smul, norm_smul])

/-- The inclusion $C^m[a, b] \to W^{m,p}(a, b)$, as a linear isometry. -/
def toSobolevₗᵢ : ContDiffMapIccSobolevNorm hlt m p →ₗᵢ[ℝ] SobolevIntervalLp m p (Opens.Ioo a b) :=
  ⟨toSobolevₗ hlt m p, fun _ ↦ rfl⟩

variable {hlt m p} in
/-- The isometry `AtkinsonHan.Chapter01.ContDiffMapIccSobolevNorm.toSobolevₗᵢ` sends $f$ to its
image under `ContDiffMapIcc.toSobolevIntervalLp`. -/
@[simp]
theorem toSobolevₗᵢ_apply (f : ContDiffMapIccSobolevNorm hlt m p) :
    toSobolevₗᵢ hlt m p f = ContDiffMapIcc.toSobolevIntervalLp p hlt.le hlt m (equiv hlt m p f) :=
  rfl

/-- For $p < \infty$ the inclusion of $C^m[a, b]$ into $W^{m,p}(a, b)$ has dense range, by
`ContDiffMapIcc.denseRange_toSobolevIntervalLp`. -/
theorem denseRange_toSobolevₗᵢ (hp : p ≠ ⊤) : DenseRange (toSobolevₗᵢ hlt m p) :=
  (ContDiffMapIcc.denseRange_toSobolevIntervalLp hlt.le hlt hp m).comp
    (equiv hlt m p).surjective.denseRange (ContDiffMapIcc.toSobolevIntervalLp p _ hlt m).continuous

/-- For every $p$ the inclusion of $C^m[a, b]$ into $W^{m,p}(a, b)$ is not surjective, by
`ContDiffMapIcc.not_surjective_toSobolevIntervalLp`. -/
theorem not_surjective_toSobolevₗᵢ : ¬ Function.Surjective (toSobolevₗᵢ hlt m p) := fun h ↦
  ContDiffMapIcc.not_surjective_toSobolevIntervalLp (p := p) hlt m fun u ↦ by
    obtain ⟨f, hf⟩ := h u
    exact ⟨equiv hlt m p f, hf⟩

/-- For $p < \infty$, the space $C^m[a, b]$ with the Sobolev norm is not complete: it is isometric
to a dense proper subspace of the Banach space $W^{m,p}(a, b)$, and a complete subspace is
closed. -/
theorem not_completeSpace (hp : p ≠ ⊤) : ¬ CompleteSpace (ContDiffMapIccSobolevNorm hlt m p) := by
  intro h
  refine not_surjective_toSobolevₗᵢ hlt m p (Set.range_eq_univ.1 ?_)
  rw [← (toSobolevₗᵢ hlt m p).isometry.isClosedEmbedding.isClosed_range.closure_eq]
  exact (denseRange_toSobolevₗᵢ hlt m p hp).closure_eq

end ContDiffMapIccSobolevNorm

/-- **Example 1.2.28(b)** of [han2009theoretical], the norm. Let $a < b$, $m \in \mathbb{N}$ and
$1 \le p < \infty$. Every $f \in C^m[a, b]$ has the Sobolev norm $$\|f\| = \Big[\sum_{j=0}^m
\|f^{(j)}\|_{L^p(a, b)}^p\Big]^{1/p}.$$

The derivative $f^{(j)}$, read in $L^p(a, b)$, is `ContDiffMapIcc.derivLpOf p f j`, applied to
the image of $f$ under `AtkinsonHan.Chapter01.ContDiffMapIccSobolevNorm.equiv`. -/
theorem example_1_2_28_b_norm (hlt : a < b) (m : ℕ) (hp : p ≠ ⊤)
    (f : ContDiffMapIccSobolevNorm hlt m p) :
    ‖f‖ = (∑ j : Fin (m + 1),
      ‖ContDiffMapIcc.derivLpOf p (ContDiffMapIccSobolevNorm.equiv hlt m p f) j‖ ^ p.toReal)
        ^ (1 / p.toReal) := by
  rw [ContDiffMapIccSobolevNorm.norm_eq, SobolevIntervalLp.norm_eq_sum hp]
  rfl

/-- **Example 1.2.28(b)** of [han2009theoretical]. Let $a < b$, $m \in \mathbb{N}$ and
$1 \le p < \infty$. The space $C^m[a, b]$ with the norm $\|f\| = [\sum_{j=0}^m
\|f^{(j)}\|_{L^p(a, b)}^p]^{1/p}$ is not complete, and its completion is the Sobolev space
$W^{m,p}(a, b)$. Precisely: $C^m[a, b]$ is not complete for this norm; $W^{m,p}(a, b)$ is
complete; the inclusion of $C^m[a, b]$ into $W^{m,p}(a, b)$ is a linear isometry with dense
range; and there is a linear isometric isomorphism from the completion of $C^m[a, b]$ onto
$W^{m,p}(a, b)$ that extends the inclusion.

The space is `AtkinsonHan.Chapter01.ContDiffMapIccSobolevNorm hlt m p`, and the inclusion is
`AtkinsonHan.Chapter01.ContDiffMapIccSobolevNorm.toSobolevₗᵢ`. The isomorphism comes from the
uniqueness of the completion, `AtkinsonHan.Chapter01.theorem_1_2_25_uniqueness`. The book's
closing remark, that for $f \in W^{m,p}(a, b)$ the derivatives $f, f', \dots, f^{(m-1)}$ are
continuous and $f^{(m)}$ exists almost everywhere and lies in $L^p(a, b)$, is the backbone's
embedding `SobolevIntervalLp.toContDiffMapIcc` of $W^{m,p}(a, b)$ into $C^{m-1}[a, b]$, and is
not restated here. -/
theorem example_1_2_28_b (hlt : a < b) (m : ℕ) (hp : p ≠ ⊤) :
    ¬ CompleteSpace (ContDiffMapIccSobolevNorm hlt m p) ∧
      CompleteSpace (SobolevIntervalLp m p (Opens.Ioo a b)) ∧
      DenseRange (ContDiffMapIccSobolevNorm.toSobolevₗᵢ hlt m p) ∧
      ∃ e : UniformSpace.Completion (ContDiffMapIccSobolevNorm hlt m p) ≃ₗᵢ[ℝ]
          SobolevIntervalLp m p (Opens.Ioo a b),
        ∀ f : ContDiffMapIccSobolevNorm hlt m p,
          e f = ContDiffMapIccSobolevNorm.toSobolevₗᵢ hlt m p f :=
  ⟨ContDiffMapIccSobolevNorm.not_completeSpace hlt m p hp, inferInstance,
    ContDiffMapIccSobolevNorm.denseRange_toSobolevₗᵢ hlt m p hp,
    theorem_1_2_25_uniqueness _ (ContDiffMapIccSobolevNorm.denseRange_toSobolevₗᵢ hlt m p hp)⟩

end

end Example1228b

section Measure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Theorem 1.2.26** of [han2009theoretical] (Lebesgue dominated convergence theorem). Let
$(\alpha, \mu)$ be a measure space, and let $f_n, g, F : \alpha \to \mathbb{R}$ with each $f_n$
almost everywhere strongly measurable and $F$ integrable. Suppose that, for each $n$,
$|f_n(x)| \le F(x)$ for almost every $x$, and that $f_n(x) \to g(x)$ for almost every $x$. Then
$g$ is integrable and $$\int f_n \, d\mu \to \int g \, d\mu.$$

**Generalization.** The book states the theorem for Lebesgue measure on an open set of
$\mathbb{R}^d$. The statement holds on an arbitrary measure space, which is how Mathlib has it.

The dominating function $F$ is `bound`. -/
theorem theorem_1_2_26 {f : ℕ → α → ℝ} {g : α → ℝ} {bound : α → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hbound : Integrable bound μ)
    (hle : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Integrable g μ ∧ Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  have hgmeas : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae atTop hf hlim
  have hgle : ∀ᵐ x ∂μ, ‖g x‖ ≤ bound x := by
    filter_upwards [ae_all_iff.2 hle, hlim] with x hx hxlim
    exact le_of_tendsto' hxlim.norm hx
  exact ⟨hbound.mono' hgmeas hgle,
    tendsto_integral_of_dominated_convergence bound hf hbound hle hlim⟩

/-- **Theorem 1.2.27** of [han2009theoretical] (Fubini's theorem). Let $(\alpha, \mu)$ and
$(\beta, \nu)$ be s-finite measure spaces, and let $f : \alpha \times \beta \to \mathbb{R}$ be
integrable for the product measure $\mu \times \nu$. Then $f(x, \cdot)$ is $\nu$-integrable for
$\mu$-almost every $x$, $f(\cdot, y)$ is $\mu$-integrable for $\nu$-almost every $y$, and $$\int
\Big(\int f(x, y) \, d\nu(y)\Big) d\mu(x) = \int \Big(\int f(x, y) \, d\mu(x)\Big) d\nu(y).$$

**Generalization.** The book states the theorem for Lebesgue measure on open sets of Euclidean
spaces. The statement holds for two s-finite measure spaces, which is how Mathlib has it. -/
theorem theorem_1_2_27 {β : Type*} [MeasurableSpace β] {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α → β → ℝ} (hf : Integrable (Function.uncurry f) (μ.prod ν)) :
    (∀ᵐ x ∂μ, Integrable (f x) ν) ∧ (∀ᵐ y ∂ν, Integrable (fun x => f x y) μ) ∧
      ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫ x, f x y ∂μ ∂ν :=
  ⟨hf.prod_right_ae, hf.prod_left_ae, integral_integral_swap hf⟩

end Measure

end AtkinsonHan.Chapter01
