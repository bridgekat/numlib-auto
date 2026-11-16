/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Numlib.Analysis.Normed.Lp.Sequence
import NumlibSurface.Brezis.Chapter04.Section05

/-!
# Brezis, Section 11.3: Some classical spaces of sequences

This module formalizes Section 11.3 of [brezis2011functional] over $\mathbb{R}$. For
$1 \le p < \infty$, the space $\ell^p$ consists of the real sequences $x = (x_k)$ with
$\sum_k |x_k|^p < \infty$, with the norm $\|x\|_p = (\sum_k |x_k|^p)^{1/p}$. The space $\ell^\infty$
consists of the bounded sequences, with the norm $\|x\|_\infty = \sup_k |x_k|$. Inside $\ell^\infty$
lie the closed subspaces $c$ of convergent sequences and $c_0$ of sequences that tend to $0$. The
section shows that $\ell^p$ is reflexive and uniformly convex for $1 < p < \infty$ (Proposition
11.15), that $c$, $c_0$ and $\ell^p$ for $p < \infty$ are separable but $\ell^\infty$ is not
(Propositions 11.16 and 11.17), it identifies the duals $(\ell^p)^* = \ell^{p'}$, $(c_0)^* = \ell^1$
and $c^* = \ell^1 \times \mathbb{R}$ (Propositions 11.18–11.20), and it shows that $\ell^1$,
$\ell^\infty$, $c$ and $c_0$ are not reflexive (Proposition 11.21).

The space $\ell^p$ is Mathlib's `lp (fun _ : ℕ => ℝ) p`, with its norm, its completeness
`lp.completeSpace`, Hölder's inequality and the Hilbert structure of $\ell^2$. The spaces $c$ and
$c_0$ are the backbone subspaces `lp.convergent ℝ ℝ` and `lp.zeroAtInfty ℝ ℝ` of $\ell^\infty$.
Propositions 11.15–11.21 specialize the theorems of the backbone module
`Numlib.Analysis.Normed.Lp.Sequence` for real sequences indexed by $\mathbb{N}$.

## Main definitions

* Section 11.3, definition of $\ell^p$ and $\ell^\infty$, `Brezis.Chapter11.lpNorm_eq`: the norms
  $\|x\|_p$ and $\|x\|_\infty$, and the membership conditions $\sum_k |x_k|^p < \infty$ and
  $\sup_k |x_k| < \infty$.
* Section 11.3, definition of $c$ and $c_0$, `Brezis.Chapter11.mem_c_iff`: $x \in c$ if and only if
  $\lim_k x_k$ exists, and $x \in c_0$ if and only if $\lim_k x_k = 0$.

## Main results

* Section 11.3, completeness, `Brezis.Chapter11.lp_completeSpace`: $\ell^p$ is a Banach space for
  $1 \le p \le \infty$.
* Section 11.3, `Brezis.Chapter11.c₀_le_c_isClosed`: $c_0 \subseteq c \subseteq \ell^\infty$, and
  $c$ and $c_0$ are closed in $\ell^\infty$.
* Section 11.3, Hölder's inequality, `Brezis.Chapter11.holder_lp`:
  $|\sum_k x_k y_k| \le \|x\|_p \|y\|_{p'}$.
* Section 11.3, `Brezis.Chapter11.l2_inner`: $\ell^2$ is a Hilbert space with the scalar product
  $(x, y) = \sum_k x_k y_k$.
* Section 11.3, `Brezis.Chapter11.lp_subset_c₀`: $\ell^p \subseteq c_0$ with
  $\|x\|_\infty \le \|x\|_p$ for $1 \le p < \infty$.
* Section 11.3, `Brezis.Chapter11.lp_subset_lq`: $\ell^p \subseteq \ell^q$ with
  $\|x\|_q \le \|x\|_p$ for $1 \le p \le q \le \infty$.
* Proposition 11.15, `Brezis.Chapter11.proposition_11_15`: $\ell^p$ is reflexive and uniformly
  convex for $1 < p < \infty$; the two clauses are `Brezis.Chapter11.proposition_11_15_reflexive`
  and `Brezis.Chapter11.proposition_11_15_uniformConvex`.
* Proposition 11.16, `Brezis.Chapter11.proposition_11_16`: $c$, $c_0$ and $\ell^p$ for
  $1 \le p < \infty$ are separable.
* Proposition 11.17, `Brezis.Chapter11.proposition_11_17`: $\ell^\infty$ is not separable.
* Proposition 11.18, `Brezis.Chapter11.proposition_11_18`: every $\varphi \in (\ell^p)^*$,
  $1 \le p < \infty$, is $x \mapsto \sum_k u_k x_k$ for a unique $u \in \ell^{p'}$, and
  $\|u\|_{p'} = \|\varphi\|$.
* Proposition 11.19, `Brezis.Chapter11.proposition_11_19`: every $\varphi \in (c_0)^*$ is
  $x \mapsto \sum_k u_k x_k$ for a unique $u \in \ell^1$, and $\|u\|_1 = \|\varphi\|$.
* Proposition 11.20, `Brezis.Chapter11.proposition_11_20`: every $\varphi \in c^*$ is
  $x \mapsto \sum_k u_k x_k + \lambda \lim_k x_k$ for a unique
  $(u, \lambda) \in \ell^1 \times \mathbb{R}$, and $\|u\|_1 + |\lambda| = \|\varphi\|$.
* Proposition 11.21, `Brezis.Chapter11.proposition_11_21`: $\ell^1$, $\ell^\infty$, $c$ and $c_0$
  are not reflexive; the four clauses are `Brezis.Chapter11.proposition_11_21_one`,
  `Brezis.Chapter11.proposition_11_21_top`, `Brezis.Chapter11.proposition_11_21_c` and
  `Brezis.Chapter11.proposition_11_21_c₀`.

## Proof outline

The reflexivity of $\ell^p$ follows directly from the duality of Proposition 11.18; the source
instead applies Theorem 4.10 to the counting measure. The uniform convexity follows the source: the
$L^p$ result of Chapter 4 is transported to $\ell^p$ along the isometry `lp.lpLIELpCount` between
$\ell^p$ and $L^p$ of the counting measure.

## Notation

* `ℓ^p`: the space $\ell^p$ of real sequences indexed by $\mathbb{N}$, a local notation for
  `lp (fun _ : ℕ => ℝ) p`.

## Conventions

* Sequences are indexed by $\mathbb{N}$ and start at $0$; the source starts at $1$. This
  relabelling changes nothing.
* The exponent $p \in [1, \infty]$ is an extended nonnegative real `p : ℝ≥0∞` with `[Fact (1 ≤ p)]`.
  Conjugate exponents $p$ and $p'$ are `p` and `q` with `[p.HolderConjugate q]`.

## Not formalized

* **Final table of Section 11.3, last entry.** The claim that $(\ell^\infty)^*$ is strictly bigger
  than $\ell^1$ is not a numbered claim. The other entries of the table are the content of
  Propositions 11.15–11.21.
-/

open Filter Topology
open scoped ENNReal InnerProductSpace

namespace Brezis.Chapter11

/-- The space $\ell^p$ of real sequences indexed by $\mathbb{N}$, which is
`lp (fun _ : ℕ => ℝ) p`. -/
local notation "ℓ^" p => lp (fun _ : ℕ => ℝ) p

/-! ### The definitions -/

/-- **Section 11.3** of [brezis2011functional], definition of $\ell^p$ and $\ell^\infty$. Let
$1 \le p < \infty$. For $x \in \ell^p$, $$\|x\|_p = \Bigl(\sum_k |x_k|^p\Bigr)^{1/p},$$ and a
real sequence $x$ belongs to $\ell^p$ if and only if $\sum_k |x_k|^p < \infty$. For
$x \in \ell^\infty$, $\|x\|_\infty = \sup_k |x_k|$, and a real sequence belongs to $\ell^\infty$
if and only if it is bounded.

The condition $\sum_k |x_k|^p < \infty$ is `Summable`, and the exponent $p$ is `p.toReal`. -/
theorem lpNorm_eq {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    (∀ x : ℓ^p, ‖x‖ = (∑' k, |x k| ^ p.toReal) ^ (1 / p.toReal)) ∧
    (∀ x : ℕ → ℝ, Memℓp x p ↔ Summable fun k => |x k| ^ p.toReal) ∧
    (∀ x : ℓ^∞, ‖x‖ = ⨆ k, |x k|) ∧
    ∀ x : ℕ → ℝ, Memℓp x ∞ ↔ BddAbove (Set.range fun k => |x k|) := by
  have hP : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
  exact ⟨fun x => by simpa only [Real.norm_eq_abs] using lp.norm_eq_tsum_rpow hP x,
    fun x => by simpa only [Real.norm_eq_abs] using memℓp_gen_iff (f := x) hP,
    fun x => by simpa only [Real.norm_eq_abs] using lp.norm_eq_ciSup x,
    fun x => by simpa only [Real.norm_eq_abs] using memℓp_infty_iff (f := x)⟩

/-- **Section 11.3** of [brezis2011functional], completeness of $\ell^p$. For $1 \le p \le \infty$,
the space $\ell^p$ is a Banach space for the $\ell^p$ norm (resp. the $\ell^\infty$ norm).

The proof is Mathlib's `lp.completeSpace`, the "direct and quite easy" proof of the source. The
other route of the source, through Theorem 4.8 on the counting measure, is available through the
backbone isometry `lp.lpLIELpCount`. -/
theorem lp_completeSpace {p : ℝ≥0∞} [Fact (1 ≤ p)] : CompleteSpace (ℓ^p) := inferInstance

/-- **Section 11.3** of [brezis2011functional], definition of $c$ and $c_0$. The spaces $$c = \{x
\in \ell^\infty ; \lim_k x_k \text{ exists}\}, \qquad c_0 = \{x \in \ell^\infty ; \lim_k x_k =
0\}$$ are subspaces of $\ell^\infty$ with the $\ell^\infty$ norm: $x \in c$ if and only if
$x_k \to l$ for some $l \in \mathbb{R}$, and $x \in c_0$ if and only if $x_k \to 0$.

The spaces $c$ and $c_0$ are `lp.convergent ℝ ℝ` and `lp.zeroAtInfty ℝ ℝ`. -/
theorem mem_c_iff (x : ℓ^∞) :
    (x ∈ lp.convergent ℝ ℝ ↔ ∃ l : ℝ, Tendsto (fun k => x k) atTop (𝓝 l)) ∧
    (x ∈ lp.zeroAtInfty ℝ ℝ ↔ Tendsto (fun k => x k) atTop (𝓝 0)) :=
  ⟨lp.mem_convergent, lp.mem_zeroAtInfty⟩

/-- **Section 11.3** of [brezis2011functional]. "Clearly $c_0 \subset c \subset \ell^\infty$ with
$c_0$ closed in $c$, and $c$ closed in $\ell^\infty$." Here $c_0 \subseteq c$, and both $c$ and
$c_0$ are closed in $\ell^\infty$. -/
theorem c₀_le_c_isClosed :
    lp.zeroAtInfty ℝ ℝ ≤ lp.convergent ℝ ℝ ∧ IsClosed (lp.convergent ℝ ℝ : Set (ℓ^∞)) ∧
      IsClosed (lp.zeroAtInfty ℝ ℝ : Set (ℓ^∞)) :=
  ⟨lp.zeroAtInfty_le_convergent ℝ ℝ, lp.isClosed_convergent ℝ ℝ, lp.isClosed_zeroAtInfty ℝ ℝ⟩

/-- **Section 11.3** of [brezis2011functional], Hölder's inequality in $\ell^p$. Let
$1 \le p \le \infty$ and let $p'$ be the conjugate exponent, $1/p + 1/p' = 1$. For
$x \in \ell^p$ and $y \in \ell^{p'}$, the series $\sum_k x_k y_k$ converges absolutely, and
$$\Bigl|\sum_k x_k y_k\Bigr| \le \|x\|_p \|y\|_{p'}.$$

The convergence is `Summable`, which for real series is absolute convergence. -/
theorem holder_lp {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] (x : ℓ^p)
    (y : ℓ^q) : (Summable fun k => x k * y k) ∧ |∑' k, x k * y k| ≤ ‖x‖ * ‖y‖ := by
  refine ⟨?_, ?_⟩
  · have h : Memℓp (fun k => ContinuousLinearMap.mul ℝ ℝ (x k) (y k)) 1 :=
      (lp.memℓp x).holder 1 (lp.memℓp y) (fun _ => ContinuousLinearMap.mul ℝ ℝ) (K := 1)
        fun _ => ContinuousLinearMap.opNorm_mul_le ℝ ℝ
    exact h.summable_of_one
  · have h := (lp.toDualCLM ℝ ℕ p q y).le_opNorm x
    rw [lp.toDualCLM_apply, lp.norm_toDualCLM_apply, Real.norm_eq_abs] at h
    rw [mul_comm ‖x‖]
    refine le_trans (le_of_eq ?_) h
    congr 1
    exact tsum_congr fun k => mul_comm _ _

/-- **Section 11.3** of [brezis2011functional]. "The space $\ell^2$ is a Hilbert space equipped with
the scalar product $(x, y) = \sum_k x_k y_k$": the scalar product of $\ell^2$ is
$\sum_k x_k y_k$, and $\ell^2$ is complete.

The scalar product is Mathlib's `lp.instInnerProductSpace`. -/
theorem l2_inner :
    (∀ x y : ℓ^2, ⟪x, y⟫_ℝ = ∑' k, x k * y k) ∧ CompleteSpace (ℓ^2) :=
  ⟨fun x y => by
    rw [lp.inner_eq_tsum]
    exact tsum_congr fun k => by simp [mul_comm], inferInstance⟩

/-- **Section 11.3** of [brezis2011functional]. "It is clear that $\ell^p \subset c_0$ with
$\|x\|_\infty \le \|x\|_p$, $1 \le p < \infty$." For $1 \le p < \infty$ and $x \in \ell^p$, the
sequence $x$, viewed in $\ell^\infty$, lies in $c_0$, and $\|x\|_\infty \le \|x\|_p$; in
particular $|x_k| \le \|x\|_p$ for every $k$.

The inclusion $\ell^p \subseteq \ell^\infty$ is Mathlib's `lp.linearMapOfLE`. -/
theorem lp_subset_c₀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) (x : ℓ^p) :
    lp.linearMapOfLE ℝ (fun _ : ℕ => ℝ) le_top x ∈ lp.zeroAtInfty ℝ ℝ ∧
      ‖lp.linearMapOfLE ℝ (fun _ : ℕ => ℝ) le_top x‖ ≤ ‖x‖ ∧ ∀ k, |x k| ≤ ‖x‖ :=
  ⟨lp.linearMapOfLE_mem_zeroAtInfty ℝ hp x,
    lp.norm_linearMapOfLE_le ℝ (zero_lt_one.trans_le Fact.out).ne' le_top x,
    fun k => by simpa only [Real.norm_eq_abs] using
      lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' x k⟩

/-- **Section 11.3** of [brezis2011functional]. "$\ell^p \subset \ell^q$ when
$1 \le p \le q \le \infty$, with $\|x\|_q \le \|x\|_p$." For $1 \le p \le q \le \infty$ and
$x \in \ell^p$, the sequence $x$ belongs to $\ell^q$, and $\|x\|_q \le \|x\|_p$.

The inclusion $\ell^p \subseteq \ell^q$ is Mathlib's `lp.linearMapOfLE`. -/
theorem lp_subset_lq {p q : ℝ≥0∞} [Fact (1 ≤ p)] (h : p ≤ q) (x : ℓ^p) :
    Memℓp (⇑x) q ∧ ‖lp.linearMapOfLE ℝ (fun _ : ℕ => ℝ) h x‖ ≤ ‖x‖ :=
  ⟨(lp.memℓp x).of_exponent_ge h,
    lp.norm_linearMapOfLE_le ℝ (zero_lt_one.trans_le Fact.out).ne' h x⟩

/-! ### Propositions 11.15–11.17 -/

/-- **Proposition 11.15** of [brezis2011functional], reflexivity. For $1 < p < \infty$, the space
$\ell^p$ is reflexive.

The backbone proof derives this from the duality of Proposition 11.18, not from Theorem 4.10 on
the counting measure as the source does. -/
theorem proposition_11_15_reflexive {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ∞) :
    NormedSpace.IsReflexive ℝ (ℓ^p) :=
  lp.isReflexive ℝ ℕ hp hp'

/-- **Proposition 11.15** of [brezis2011functional], uniform convexity. For $1 < p < \infty$, the
space $\ell^p$ is uniformly convex.

The proof transports the uniform convexity of $L^p$ of Chapter 4 along the isometry
`lp.lpLIELpCount` onto $L^p$ of the counting measure, as the source does. -/
theorem proposition_11_15_uniformConvex {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ∞) :
    UniformConvexSpace (ℓ^p) := by
  have := Fact.mk hp
  have := Fact.mk hp'
  exact lp.uniformConvexSpace

/-- **Proposition 11.15** of [brezis2011functional]. For $1 < p < \infty$, the space $\ell^p$ is
reflexive, and even uniformly convex.

The two clauses are `Brezis.Chapter11.proposition_11_15_reflexive` and
`Brezis.Chapter11.proposition_11_15_uniformConvex`. -/
theorem proposition_11_15 {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ∞) :
    NormedSpace.IsReflexive ℝ (ℓ^p) ∧ UniformConvexSpace (ℓ^p) :=
  ⟨proposition_11_15_reflexive hp hp', proposition_11_15_uniformConvex hp hp'⟩

/-- **Proposition 11.16** of [brezis2011functional]. The spaces $c$ and $c_0$, and the spaces
$\ell^p$ for $1 \le p < \infty$, are separable. -/
theorem proposition_11_16 :
    TopologicalSpace.SeparableSpace (lp.convergent ℝ ℝ) ∧
    TopologicalSpace.SeparableSpace (lp.zeroAtInfty ℝ ℝ) ∧
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → TopologicalSpace.SeparableSpace (ℓ^p) :=
  ⟨inferInstance, inferInstance, fun _ _ hp => lp.separableSpace (𝕜 := ℝ) hp⟩

/-- **Proposition 11.17** of [brezis2011functional]. The space $\ell^\infty$ is not separable. -/
theorem proposition_11_17 : ¬ TopologicalSpace.SeparableSpace (ℓ^∞) :=
  lp.not_separableSpace_top

/-! ### Propositions 11.18–11.20: the duals -/

/-- **Proposition 11.18** of [brezis2011functional]. Let $1 \le p < \infty$, and let $p'$ be the
conjugate exponent, $1/p + 1/p' = 1$. For every $\varphi \in (\ell^p)^*$ there is a unique
$u \in \ell^{p'}$ such that $$\varphi(x) = \sum_k u_k x_k \quad \text{for all } x \in \ell^p
\qquad \text{and} \qquad \|u\|_{p'} = \|\varphi\|.$$

The uniqueness is stated for the conjunction of the two conditions. -/
theorem proposition_11_18 {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (hp : p ≠ ∞) (φ : StrongDual ℝ (ℓ^p)) :
    ∃! u : ℓ^q, (∀ x : ℓ^p, φ x = ∑' k, u k * x k) ∧ ‖u‖ = ‖φ‖ := by
  obtain ⟨u, hu⟩ := lp.toDual_surjective (𝕜 := ℝ) (α := ℕ) (p := p) (q := q) hp φ
  refine ⟨u, ⟨fun x => by rw [← hu, lp.toDual_apply], by rw [← hu, LinearIsometry.norm_map]⟩,
    fun v ⟨hv, _⟩ => (lp.toDual ℝ ℕ p q).injective ?_⟩
  rw [hu]
  ext x
  rw [lp.toDual_apply, hv x]

/-- **Proposition 11.19** of [brezis2011functional]. For every $\varphi \in (c_0)^*$ there is a
unique $u \in \ell^1$ such that $$\varphi(x) = \sum_k u_k x_k \quad \text{for all } x \in c_0
\qquad \text{and} \qquad \|u\|_1 = \|\varphi\|.$$

The uniqueness is stated for the conjunction of the two conditions. -/
theorem proposition_11_19 (φ : StrongDual ℝ (lp.zeroAtInfty ℝ ℝ)) :
    ∃! u : ℓ^1, (∀ x : lp.zeroAtInfty ℝ ℝ, φ x = ∑' k, u k * (x : ℓ^∞) k) ∧ ‖u‖ = ‖φ‖ := by
  obtain ⟨u, hu⟩ := lp.zeroAtInfty.toDual_surjective (𝕜 := ℝ) φ
  refine ⟨u, ⟨fun x => by rw [← hu, lp.zeroAtInfty.toDual_apply],
    by rw [← hu, LinearIsometry.norm_map]⟩, fun v ⟨hv, _⟩ => (lp.zeroAtInfty.toDual ℝ).injective ?_⟩
  rw [hu]
  ext x
  rw [lp.zeroAtInfty.toDual_apply, hv x]

/-- **Proposition 11.20** of [brezis2011functional]. For every $\varphi \in c^*$ there is a unique
pair $(u, \lambda) \in \ell^1 \times \mathbb{R}$ such that $$\varphi(x) = \sum_k u_k x_k +
\lambda \lim_{k \to \infty} x_k \quad \text{for all } x \in c \qquad \text{and} \qquad \|u\|_1 +
|\lambda| = \|\varphi\|.$$

The limit map $c \to \mathbb{R}$ is the backbone's `lp.convergent.limCLM`. The uniqueness is
stated for the conjunction of the two conditions. -/
theorem proposition_11_20 (φ : StrongDual ℝ (lp.convergent ℝ ℝ)) :
    ∃! ul : (ℓ^1) × ℝ, (∀ x : lp.convergent ℝ ℝ,
      φ x = ∑' k, ul.1 k * (x : ℓ^∞) k + ul.2 * lp.convergent.limCLM ℝ ℝ x) ∧
      ‖ul.1‖ + |ul.2| = ‖φ‖ := by
  obtain ⟨w, hw⟩ := lp.convergent.toDual_surjective (𝕜 := ℝ) φ
  obtain ⟨⟨u, l⟩⟩ := w
  refine ⟨(u, l), ⟨fun x => by rw [← hw, lp.convergent.toDual_apply],
    by rw [← hw, LinearIsometry.norm_map, lp.norm_toLp_one_prod, Real.norm_eq_abs]⟩,
    fun ⟨v, m⟩ ⟨hv, _⟩ => ?_⟩
  have : WithLp.toLp 1 (v, m) = WithLp.toLp 1 (u, l) := by
    refine (lp.convergent.toDual ℝ).injective ?_
    rw [hw]
    ext x
    rw [lp.convergent.toDual_apply, hv x]
  exact congrArg WithLp.ofLp this

/-! ### Proposition 11.21 -/

/-- **Proposition 11.21** of [brezis2011functional], the space $c_0$. The space $c_0$ is not
reflexive. -/
theorem proposition_11_21_c₀ : ¬ NormedSpace.IsReflexive ℝ (lp.zeroAtInfty ℝ ℝ) :=
  lp.zeroAtInfty.not_isReflexive ℝ

/-- **Proposition 11.21** of [brezis2011functional], the space $\ell^1$. The space $\ell^1$ is not
reflexive. -/
theorem proposition_11_21_one : ¬ NormedSpace.IsReflexive ℝ (ℓ^1) :=
  lp.not_isReflexive_one ℝ

/-- **Proposition 11.21** of [brezis2011functional], the space $\ell^\infty$. The space
$\ell^\infty$ is not reflexive. -/
theorem proposition_11_21_top : ¬ NormedSpace.IsReflexive ℝ (ℓ^∞) :=
  lp.not_isReflexive_top ℝ

/-- **Proposition 11.21** of [brezis2011functional], the space $c$. The space $c$ is not reflexive.
-/
theorem proposition_11_21_c : ¬ NormedSpace.IsReflexive ℝ (lp.convergent ℝ ℝ) :=
  lp.convergent.not_isReflexive ℝ

/-- **Proposition 11.21** of [brezis2011functional]. The spaces $\ell^1$, $\ell^\infty$, $c$ and
$c_0$ are not reflexive.

Reflexivity is the backbone class `NormedSpace.IsReflexive`. -/
theorem proposition_11_21 :
    ¬ NormedSpace.IsReflexive ℝ (ℓ^1) ∧ ¬ NormedSpace.IsReflexive ℝ (ℓ^∞) ∧
      ¬ NormedSpace.IsReflexive ℝ (lp.convergent ℝ ℝ) ∧
      ¬ NormedSpace.IsReflexive ℝ (lp.zeroAtInfty ℝ ℝ) :=
  ⟨proposition_11_21_one, proposition_11_21_top, proposition_11_21_c, proposition_11_21_c₀⟩

end Brezis.Chapter11
