/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.HarmonicPolynomial
import NumlibSurface.AtkinsonHan.Chapter14.Section02

/-!
# Atkinson and Han, Section 14.4: A Galerkin method for an elliptic equation on the disk

This module formalizes the polynomial part of Section 14.4 of [han2009theoretical]. The section
poses $-\Delta u = f$ on $\mathbb{B}_2$ with $u = 0$ on the boundary, takes its weak formulation in
$H^1_0(\mathbb{B}_2)$, and applies the Galerkin method with the trial space
$\mathcal{X}_n = (1 - |x|^2) \Pi_n^2$, whose elements vanish on the unit circle. The module
formalizes (14.4.8) and Lemma 14.4.1, which mention no Sobolev space: the Laplacian is a linear
bijection of $\mathcal{X}_n$ onto $\Pi_n^d$, which makes the Galerkin equations uniquely solvable.
The book leaves the proof of the lemma as a problem. The module also states the basis (14.4.14) of
$\mathcal{X}_n$ that Example 14.4.2 uses.

## Main definitions

* (14.4.8), `AtkinsonHan.Chapter14.trialSpace`: the trial space
  $\mathcal{X}_n = (1 - |x|^2) \Pi_n^d$.
* Lemma 14.4.1, `AtkinsonHan.Chapter14.laplacianOn`: the Laplacian as a linear map
  $\mathcal{X}_n \to \Pi_n^d$.

## Main results

* `AtkinsonHan.Chapter14.finrank_trialSpace`: $\dim \mathcal{X}_n = \dim \Pi_n^d = \binom{n +
  d}{d}$.
* Lemma 14.4.1, `AtkinsonHan.Chapter14.lemma_14_4_1`: for $d \ge 1$,
  $\Delta : \mathcal{X}_n \to \Pi_n^d$ is a linear bijection.
* (14.4.14), `AtkinsonHan.Chapter14.span_ridgePoly_polySpace`: the ridge polynomials of Example
  14.2.2 span $\Pi_n^2$ as polynomials.
* (14.4.14) and Example 14.4.2, `AtkinsonHan.Chapter14.example_14_4_2`: the products of
  $1 - x^2 - y^2$ with the ridge polynomials span $\mathcal{X}_n$.

## Proof outline

The Laplacian maps $\mathcal{X}_n$ into $\Pi_n^d$ by a degree count: $(1 - |x|^2) p$ has degree at
most $n + 2$, and the Laplacian lowers the degree by two. The two spaces have equal dimension,
because multiplication by the nonzero polynomial $1 - |x|^2$ is injective. So bijectivity follows
from injectivity, which is the backbone
`MvPolynomial.eq_zero_of_laplacian_one_sub_sumSq_mul_eq_zero` of
`Numlib.Analysis.HarmonicPolynomial`.

## Not formalized

* **(14.4.1)–(14.4.7)**, the boundary value problem, its weak formulation, and the boundedness and
  coercivity of the bilinear form.
* **(14.4.10)–(14.4.11)**, the Galerkin method on $\mathcal{X}_n$ and its Céa estimate.
* **(14.4.12)–(14.4.13)**, the Green's function of the disk and the regularity bound that it gives.
* **Exercises 14.4.2–14.4.3**, the transfer of the problem from an ellipse or a smooth simply
  connected region to the disk.
* **The numerical part of Example 14.4.2**: the transformation of $-\Delta u + e^{s - t} u = g$ from
  the region $D$ to the disk by $s = x - y + a x^2$, $t = x + y$, with the coefficients $A$,
  $\gamma$, $f$ that it gives, the test solution (14.4.18), and the errors read off Figure 14.3. The
  transformation is a change of variables in the weak formulation, and the errors are read off a
  figure.

All these items quantify over $H^1_0(\mathbb{B}_2)$. The abstract parts of the argument are
formalized elsewhere in this library: the Lax–Milgram lemma in
`NumlibSurface.AtkinsonHan.Chapter08.Section03` and Céa's inequality in
`NumlibSurface.AtkinsonHan.Chapter09.Section01`.
-/

open Module MvPolynomial

namespace AtkinsonHan.Chapter14

variable {d : ℕ}

/-- The polynomial $1 - |x|^2 = 1 - x_1^2 - \cdots - x_d^2$ in $d$ variables, which vanishes exactly
on the unit sphere. -/
noncomputable abbrev oneSubSumSq (d : ℕ) : MvPolynomial (Fin d) ℝ := 1 - sumSq (Fin d) ℝ

/-- The polynomial $1 - |x|^2$ is not zero. -/
theorem oneSubSumSq_ne_zero : oneSubSumSq d ≠ 0 := fun hz => by
  have := congrArg (eval (fun _ => (0 : ℝ))) hz
  simp [oneSubSumSq, sumSq] at this

/-- **Equation (14.4.8)** of [han2009theoretical]. For $d, n \in \mathbb{N}$, the **trial space** of
the Galerkin method is $$\mathcal{X}_n = \{(1 - x_1^2 - \cdots - x_d^2) \, p : p \in
\Pi_n^d\}.$$ Its elements vanish on the unit sphere, so their restrictions to the unit ball lie
in $H^1_0(\mathbb{B}_d)$.

The space is a subspace of the polynomials in $d$ variables, the image of $\Pi_n^d$ under
multiplication by `AtkinsonHan.Chapter14.oneSubSumSq d`. -/
noncomputable def trialSpace (d n : ℕ) : Submodule ℝ (MvPolynomial (Fin d) ℝ) :=
  (polySpace d n).map (LinearMap.mulLeft ℝ (oneSubSumSq d))

/-- A polynomial $q$ is in $\mathcal{X}_n$ if and only if $q = (1 - |x|^2) p$ for a polynomial $p$
of total degree at most $n$. -/
theorem mem_trialSpace_iff {n : ℕ} {q : MvPolynomial (Fin d) ℝ} :
    q ∈ trialSpace d n ↔ ∃ p, p.totalDegree ≤ n ∧ oneSubSumSq d * p = q := by
  simp only [trialSpace, Submodule.mem_map, mem_polySpace_iff, LinearMap.mulLeft_apply]

/-- Multiplication by $1 - |x|^2$ is an injective linear map on the polynomials in $d$ variables. -/
theorem mulLeft_oneSubSumSq_injective :
    Function.Injective (LinearMap.mulLeft ℝ (oneSubSumSq d)) :=
  mul_right_injective₀ oneSubSumSq_ne_zero

instance finiteDimensional_trialSpace (n : ℕ) : FiniteDimensional ℝ (trialSpace d n) := by
  have : Module.Finite ℝ (polySpace d n) := inferInstance
  exact Module.Finite.map (polySpace d n) (LinearMap.mulLeft ℝ (oneSubSumSq d))

/-- For all $d, n \in \mathbb{N}$, $$\dim \mathcal{X}_n = \dim \Pi_n^d = \binom{n + d}{d},$$ because
multiplication by $1 - |x|^2$ is injective, so it maps $\Pi_n^d$ isomorphically onto
$\mathcal{X}_n$. For $d = 2$ this is $(n + 1)(n + 2)/2$, the count of Section 14.1. -/
theorem finrank_trialSpace (n : ℕ) :
    finrank ℝ (trialSpace d n) = (n + d).choose d := by
  rw [← finrank_polySpace d n]
  exact (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective _ mulLeft_oneSubSumSq_injective _)).symm

/-- Every element of $\mathcal{X}_n$ has total degree at most $n + 2$. -/
theorem totalDegree_le_of_mem_trialSpace {n : ℕ} {q : MvPolynomial (Fin d) ℝ}
    (hq : q ∈ trialSpace d n) : q.totalDegree ≤ n + 2 := by
  obtain ⟨p, hp, rfl⟩ := mem_trialSpace_iff.1 hq
  refine (totalDegree_mul _ _).trans ?_
  have h1 : (oneSubSumSq d).totalDegree ≤ 2 :=
    (totalDegree_sub _ _).trans (by simp [totalDegree_sumSq_le])
  omega

/-- The Laplacian maps $\mathcal{X}_n$ into $\Pi_n^d$: if $q \in \mathcal{X}_n$, then
$\Delta q \in \Pi_n^d$. An element of $\mathcal{X}_n$ has degree at most $n + 2$, and the
Laplacian lowers the degree by two. -/
theorem laplacian_mem_polySpace {n : ℕ} {q : MvPolynomial (Fin d) ℝ} (hq : q ∈ trialSpace d n) :
    laplacian q ∈ polySpace d n := by
  have h1 := totalDegree_laplacian_le q
  have h2 := totalDegree_le_of_mem_trialSpace hq
  exact mem_polySpace_iff.2 (by omega)

/-- **Lemma 14.4.1** of [han2009theoretical], the map. For $d, n \in \mathbb{N}$, the Laplacian
$\Delta$ as a linear map from the trial space $\mathcal{X}_n$ to $\Pi_n^d$.

The Laplacian of polynomials is `MvPolynomial.laplacian`, and the map is well defined by
`AtkinsonHan.Chapter14.laplacian_mem_polySpace`. -/
noncomputable def laplacianOn (d n : ℕ) : trialSpace d n →ₗ[ℝ] polySpace d n :=
  laplacian.restrict fun _ hq => laplacian_mem_polySpace hq

/-- The value of the Laplacian $\mathcal{X}_n \to \Pi_n^d$ at $q$, read as a polynomial, is
$\Delta q$. -/
@[simp]
theorem laplacianOn_coe {n : ℕ} (q : trialSpace d n) :
    (laplacianOn d n q : MvPolynomial (Fin d) ℝ) = laplacian (q : MvPolynomial (Fin d) ℝ) := rfl

/-- **Lemma 14.4.1** of [han2009theoretical], injectivity. Let $d \ge 1$ and $n \in \mathbb{N}$. The
Laplacian $\Delta : \mathcal{X}_n \to \Pi_n^d$ is injective: a harmonic element of
$\mathcal{X}_n$ is zero.

For $q = (1 - |x|^2) p$, the backbone
`MvPolynomial.eq_zero_of_laplacian_one_sub_sumSq_mul_eq_zero` gives $p = 0$. In analysis this is
the uniqueness for the Dirichlet problem, that a harmonic function on the ball that vanishes on
the sphere is zero, but the proof is algebraic. -/
theorem lemma_14_4_1_injective (hd : 0 < d) (n : ℕ) : Function.Injective (laplacianOn d n) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨q, hq⟩ hker
  obtain ⟨p, hp, rfl⟩ := mem_trialSpace_iff.1 hq
  have hlap : laplacian (oneSubSumSq d * p) = 0 :=
    congrArg Subtype.val (LinearMap.mem_ker.1 hker)
  have hp0 : p = 0 := MvPolynomial.eq_zero_of_laplacian_one_sub_sumSq_mul_eq_zero
    (Fin.pos_iff_nonempty.1 hd) hp hlap
  exact Subtype.ext (by simp [hp0])

/-- **Lemma 14.4.1** of [han2009theoretical]. Let $d \ge 1$ and $n \in \mathbb{N}$. The Laplacian is
a linear bijection $$\Delta : \mathcal{X}_n = (1 - |x|^2) \Pi_n^d \to \Pi_n^d.$$

The surjectivity follows from the injectivity, because the two spaces have the same dimension.
The lemma makes the Galerkin equations of Section 14.4 uniquely solvable. -/
theorem lemma_14_4_1 (hd : 0 < d) (n : ℕ) : Function.Bijective (laplacianOn d n) := by
  refine ⟨lemma_14_4_1_injective hd n, ?_⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1
    (lemma_14_4_1_injective hd n)
  rw [finrank_trialSpace n, finrank_polySpace]


/-! ### Example 14.4.2: the basis (14.4.14) of the trial space -/

section Basis

open Approximation

open scoped Real

/-- For every $n \in \mathbb{N}$, the ridge polynomials $\varphi_{m,k}$ of Example 14.2.2 with
$0 \le k \le m \le n$ span $\Pi_n^2$ as a space of polynomials, and not only as classes in
$L^2(\mathbb{B}_2)$. It supports (14.4.14).

This is `AtkinsonHan.Chapter14.example_14_2_2_polyLE` carried back along
`Approximation.IsMvWeight.toL2`, which is injective on polynomials, because no nonzero
polynomial vanishes almost everywhere on the disk. The polynomial $\varphi_{m,k}$ is
`Approximation.ridgePoly m (k * (π / (m + 1)))`. -/
theorem span_ridgePoly_polySpace (n : ℕ) :
    Submodule.span ℝ {p : MvPolynomial (Fin 2) ℝ |
        ∃ m ≤ n, ∃ k ≤ m, p = ridgePoly m (k * (π / (m + 1)))} = polySpace 2 n := by
  refine Submodule.map_injective_of_injective
    (f := (isMvWeight_ballVolume 2).toL2) (IsMvWeight.toL2_injective _) ?_
  rw [Submodule.map_span]
  have himg : (isMvWeight_ballVolume 2).toL2 ''
      {p : MvPolynomial (Fin 2) ℝ | ∃ m ≤ n, ∃ k ≤ m, p = ridgePoly m (k * (π / (m + 1)))}
      = {f | ∃ m ≤ n, ∃ k ≤ m, f = ridgeL2 m k} := by
    ext f
    constructor
    · rintro ⟨p, ⟨m, hm, k, hk, rfl⟩, rfl⟩
      exact ⟨m, hm, k, hk, rfl⟩
    · rintro ⟨m, hm, k, hk, rfl⟩
      exact ⟨ridgePoly m (k * (π / (m + 1))), ⟨m, hm, k, hk, rfl⟩, rfl⟩
  rw [himg, example_14_2_2_polyLE n]
  rfl

/-- **Equation (14.4.14)** of [han2009theoretical], the basis of the trial space in Example 14.4.2.
For every $n \in \mathbb{N}$, with the ridge polynomials $\varphi_{m,k}$ of Example 14.2.2, the
functions $$\psi_{m,k}(x, y) = (1 - x^2 - y^2) \, \varphi_{m,k}(x, y), \qquad 0 \le k \le m \le
n,$$ span the trial space $\mathcal{X}_n$ of (14.4.8).

There are $\dim \Pi_n^2 = (n + 1)(n + 2)/2$ of them, and $\dim \mathcal{X}_n$ is the same
(`AtkinsonHan.Chapter14.finrank_trialSpace`), so they are a basis of $\mathcal{X}_n$. This makes
the Galerkin equations of Section 14.4 a square system, uniquely solvable by Lemma 14.4.1. The
rest of Example 14.4.2 is numerical and is not formalized. -/
theorem example_14_4_2 (n : ℕ) :
    Submodule.span ℝ {q : MvPolynomial (Fin 2) ℝ |
        ∃ m ≤ n, ∃ k ≤ m, q = oneSubSumSq 2 * ridgePoly m (k * (π / (m + 1)))}
      = trialSpace 2 n := by
  rw [trialSpace, ← span_ridgePoly_polySpace n, Submodule.map_span]
  congr 1
  ext q
  constructor
  · rintro ⟨m, hm, k, hk, rfl⟩
    exact ⟨_, ⟨m, hm, k, hk, rfl⟩, rfl⟩
  · rintro ⟨p, ⟨m, hm, k, hk, rfl⟩, rfl⟩
    exact ⟨m, hm, k, hk, rfl⟩

end Basis

end AtkinsonHan.Chapter14
