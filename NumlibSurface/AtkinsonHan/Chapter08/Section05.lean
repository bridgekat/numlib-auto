/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Sobolev.Korn
import NumlibSurface.AtkinsonHan.Chapter08.Section03

/-!
# Atkinson and Han, Section 8.5: A boundary value problem of linearized elasticity

This module formalizes part of Section 8.5 of [han2009theoretical]. The section sets up the problem
of linearized elasticity (8.5.1)–(8.5.5),
$$-\operatorname{div} \sigma = f \text{ in } \Omega, \qquad \sigma = C \varepsilon(u), \qquad
  \varepsilon(u) = \tfrac12 \left( \nabla u + (\nabla u)^T \right),$$
with the displacement $u = 0$ on $\Gamma_D$ and the traction $\sigma \nu = g$ on $\Gamma_N$. Theorem
8.5.1, whose proof the source leaves to Exercise 8.5.3, states that the weak formulation (8.5.15) on
$V = \{ v \in [H^1(\Omega)]^d : v = 0 \text{ on } \Gamma_D \}$ has a unique solution, and that the
solution is the minimizer of the energy (8.5.17). The $V$-ellipticity of the bilinear form comes
from Korn's inequality.

Here the theorem is formalized in the pure displacement case $\Gamma_D = \Gamma$, without traction,
on a bounded open set $\Omega \subseteq B(0, R) \subseteq \mathbb{R}^{d+1}$. Then
$V = [H^1_0(\Omega)]^{d+1}$, and the inequality needed is Korn's first inequality $\int_\Omega
|\nabla v|^2 \le 2 \int_\Omega |\varepsilon(v)|^2$, which needs no regularity of $\Omega$. Korn's
first inequality and the strain come from the backbone module `Numlib.Analysis.Sobolev.Korn`, and
the proof of the theorem is the Lax–Milgram lemma of Section 8.3 with the energy characterization of
Theorem 8.3.3.

## Main definitions

* Section 8.5, `AtkinsonHan.Chapter08.elasticityForm`: the bilinear form $a(u, v) = \int_\Omega [C
  \varepsilon(u)] : \varepsilon(v) \, dx$ on $[H^1_0(\Omega)]^N$.
* Equations (8.5.6)–(8.5.8), `AtkinsonHan.Chapter08.IsElasticityTensor`: the components
  $C_{ijkl} \in L^\infty(\Omega)$ have the symmetries (8.5.7) and satisfy the stability condition
  (8.5.8).
* Equation (8.5.14), `AtkinsonHan.Chapter08.elasticityLoad`: the load
  $\ell(v) = \int_\Omega f \cdot v \, dx$ for $f \in [L^2(\Omega)]^{d+1}$.

## Main results

* Section 8.5, `AtkinsonHan.Chapter08.elasticityForm_isBoundedWith`,
  `AtkinsonHan.Chapter08.elasticityForm_isHermitian` and
  `AtkinsonHan.Chapter08.elasticityForm_isCoerciveWith`: the elasticity form is bounded, symmetric
  and $V$-elliptic on $[H^1_0(\Omega)]^{d+1}$.
* Theorem 8.5.1, `AtkinsonHan.Chapter08.theorem_8_5_1_dirichlet`: in the pure displacement case the
  weak problem (8.5.15) has exactly one solution, and a displacement solves it if and only if it
  minimizes the energy (8.5.17).

## Conventions

* The source works in $\mathbb{R}^d$. The dimension here is $d + 1$, because the backbone's Poincaré
  inequality is stated in that form. The general constructions of the elasticity form are in
  dimension $N$.
* $[H^1_0(\Omega)]^{d+1}$ is the backbone's `SobolevEuclideanZeroVec (d + 1) Ω`, with
  $\|v\|^2 = \sum_i \|v_i\|_{H^1(\Omega)}^2$. The strain component $\varepsilon(v)_{ij} = \frac12
  (\partial_j v_i + \partial_i v_j) \in L^2(\Omega)$ is `SobolevEuclideanZeroVec.strainL i j v`.

## Implementation notes

* The components $C_{ijkl}$ are elements of $L^\infty(\Omega)$. They act on $L^2(\Omega)$ through
  the multiplication operator `Elliptic.mulL`.
* The Lax–Milgram lemma with the energy characterization is proved once on an abstract Hilbert
  space, `AtkinsonHan.Chapter08.existsUnique_and_isMinOn_iff`, so that Theorem 8.5.1 is one
  application of it.
* The mixed case of Theorem 8.5.1 needs only one more fact. The surface measure, the outward normal
  and the trace on a $C^1$ domain exist in `Numlib.Analysis.Sobolev.Boundary.ContDiffDomain`, so $V$
  is a closed subspace of $[H^1(\Omega)]^{d+1}$, the form is the elasticity form restricted to $V$,
  and the load is $\ell$ plus the traction functional $v \mapsto \int_{\Gamma_N} g \cdot \gamma v \,
  d\sigma$, bounded by $\|g\|_{L^2(\sigma)} \|\gamma\| \|v\|$. The missing fact is the
  $V$-ellipticity of the form on $V$, that is the inequality
  $\|v\|_{H^1}^2 \le c \|\varepsilon(v)\|_{L^2}^2$ on $V$. It rests on Korn's second inequality
  $\|v\|_{H^1}^2 \le c (\|v\|_{L^2}^2 + \|\varepsilon(v)\|_{L^2}^2)$ on $[H^1(\Omega)]^{d+1}$,
  followed by a compactness argument (Rellich's theorem, then the kernel of $\varepsilon$ on a
  connected domain). In that argument, a nonzero infinitesimal rigid motion $a + Wx$ with $W$ skew
  cannot vanish on a part of the boundary of positive surface measure: its zero set is an affine
  subspace of even codimension at least $2$, so it is a null set on a $C^1$ hypersurface, even one
  with a flat face.

## Deviations from the source

* **Equations (8.5.6)–(8.5.8)** (reading). The coefficient fields are $L^\infty$
  classes. Their symmetries and uniform positivity are read almost everywhere.
* **Theorem 8.5.1** (generalization). The source assumes a Lipschitz domain. In the pure
  displacement case the theorem here holds on every bounded open set. See
  `AtkinsonHan.Chapter08.theorem_8_5_1_dirichlet`.

## Not formalized

* **Theorem 8.5.1 in the mixed displacement–traction case**, with
  $\operatorname{meas}(\Gamma_D) > 0$ and a traction $g \in [L^2(\Gamma_N)]^{d+1}$ on
  $\Gamma_N = \Gamma \setminus \Gamma_D$. The weak problem is to find $u \in V = \{ v \in
  [H^1(\Omega)]^{d+1} : \gamma v = 0 \text{ on } \Gamma_D \}$ (8.5.13) with $\int_\Omega [C
  \varepsilon(u)] : \varepsilon(v) \, dx = \int_\Omega f \cdot v \, dx + \int_{\Gamma_N} g \cdot
  \gamma v \, d\sigma$ for all $v \in V$. The $V$-ellipticity of the form on $V$ needs Korn's second
  inequality, which is not formalized.
* **Korn's second inequality** on $[H^1(\Omega)]^{d+1}$. Its proof (Duvaut–Lions, Nečas) writes
  $\partial_j \partial_k v_i = \partial_j \varepsilon_{ik} + \partial_k \varepsilon_{ij} -
  \partial_i \varepsilon_{jk}$ in $H^{-1}(\Omega)$ and uses Lions's lemma: on a bounded Lipschitz
  domain, a distribution $f$ with $f \in H^{-1}(\Omega)$ and $\nabla f \in H^{-1}(\Omega)^N$ is in
  $L^2(\Omega)$, with $\|f\|_{L^2} \le c (\|f\|_{H^{-1}} + \|\nabla f\|_{H^{-1}})$. Lions's lemma
  needs Bogovskiĭ's right inverse of the divergence or the Nečas inequality in $H^{-1}$, and neither
  is in Mathlib or in the backbone.
-/

open Filter MeasureTheory Metric Set TopologicalSpace Topology
open scoped ENNReal InnerProductSpace

namespace AtkinsonHan.Chapter08

/-! ### Finite sums and integrals -/

/-- Four nested finite sums can be reordered in pairs: for $f : \iota^4 \to M$ with values in a
commutative additive monoid,
$$\sum_{i, j, k, l} f(i, j, k, l) = \sum_{k, l, i, j} f(i, j, k, l),$$
where the outer two sums on the right run over $k$ and $l$. -/
theorem Finset.sum_sum_sum_sum_comm {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (f : ι → ι → ι → ι → M) :
    ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l :=
  calc ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ i, ∑ k, ∑ j, ∑ l, f i j k l :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, ∑ l, f i j k l := Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, f i j k l :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm

/-- Let $F_{ijkl}$, for $i, j, k, l$ in a finite type, be integrable real functions on a measure
space. Then the four nested sums of the integrals of $F_{ijkl}$ are the integral of the four
nested sums of $F_{ijkl}$. -/
theorem sum_sum_sum_sum_integral_eq {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    [Fintype ι] {F : ι → ι → ι → ι → X → ℝ} (hF : ∀ i j k l, Integrable (F i j k l) μ) :
    ∑ i, ∑ j, ∑ k, ∑ l, ∫ x, F i j k l x ∂μ = ∫ x, ∑ i, ∑ j, ∑ k, ∑ l, F i j k l x ∂μ := by
  symm
  rw [integral_finsetSum (f := fun i x ↦ ∑ j, ∑ k, ∑ l, F i j k l x) _ fun i _ ↦
    integrable_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun k _ ↦
      integrable_finsetSum _ fun l _ ↦ hF i j k l]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum (f := fun j x ↦ ∑ k, ∑ l, F i j k l x) _ fun j _ ↦
    integrable_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hF i j k l]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_finsetSum (f := fun k x ↦ ∑ l, F i j k l x) _ fun k _ ↦
    integrable_finsetSum _ fun l _ ↦ hF i j k l]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_finsetSum (f := fun l x ↦ F i j k l x) _ fun l _ ↦ hF i j k l]

/-- For real numbers $f(i, j, k, l)$ indexed by a finite type, the absolute value of the four nested
sums is at most the four nested sums of the absolute values:
$$\Big| \sum_{i, j, k, l} f(i, j, k, l) \Big| \le \sum_{i, j, k, l} |f(i, j, k, l)|.$$
-/
theorem abs_sum_sum_sum_sum_le {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → ℝ) :
    |∑ i, ∑ j, ∑ k, ∑ l, f i j k l| ≤ ∑ i, ∑ j, ∑ k, ∑ l, |f i j k l| :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ ↦
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ ↦
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ ↦
        Finset.abs_sum_le_sum_abs _ _)))

/-- Let $V$ be a real Hilbert space, let $a$ be a bilinear form on $V$ that is bounded with constant
$M$, symmetric, and $V$-elliptic with a constant $\alpha > 0$, and let $\ell \in V'$. Then
$u \in V$ minimizes the energy $E(v) = \frac12 a(v, v) - \ell(v)$ over $V$ if and only if
$a(u, v) = \ell(v)$ for all $v \in V$.

This is `AtkinsonHan.Chapter08.theorem_8_3_3_subspace` with $K = V$. -/
theorem isMinOn_energy_univ_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {a : BilinForm V} {M α : ℝ} (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V) (u : V) :
    IsMinOn (a.energy ℓ) univ u ↔ ∀ v, a u v = ℓ v := by
  have h := theorem_8_3_3_subspace hM hα ha hs ℓ ⊤ (Submodule.mem_top (x := u))
  rw [Submodule.top_coe] at h
  simpa using h

/-- The Lax–Milgram lemma with the energy characterization. Let $V$ be a real Hilbert space, let $a$
be a bounded sesquilinear form on $V$ (here a real bilinear form) that is bounded with constant
$M$, Hermitian, and coercive with a constant $c > 0$, and let $\ell \in V'$. Then the problem
$a(u, v) = \ell(v)$ for all $v \in V$ has exactly one solution, and $u \in V$ solves it if and
only if $u$ minimizes $\frac12 a(v, v) - \ell(v)$ over $V$.

The proof is `AtkinsonHan.Chapter08.theorem_8_3_4` together with Theorem 8.3.3, on an abstract
space, so that a concrete problem is one application. -/
theorem existsUnique_and_isMinOn_iff {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] {a : SesqForm ℝ V} {M c : ℝ}
    (hM : a.IsBoundedWith M) (hc : 0 < c) (hcoer : a.IsCoerciveWith c) (hherm : a.IsHermitian)
    (ℓ : StrongDual ℝ V) :
    (∃! u : V, ∀ v, a u v = ℓ v)
      ∧ ∀ u : V, (∀ v, a u v = ℓ v)
        ↔ IsMinOn (fun v ↦ (1 / 2 : ℝ) * a v v - ℓ v) univ u := by
  have hM' : (BilinForm.ofCLM a).IsBoundedWith M := fun u v ↦ by
    rw [BilinForm.ofCLM_apply, ← Real.norm_eq_abs]
    exact hM u v
  have hα : (BilinForm.ofCLM a).IsEllipticWith c := fun v ↦ by
    rw [BilinForm.ofCLM_apply]
    exact hcoer v
  have hs : LinearMap.BilinForm.IsSymm (BilinForm.ofCLM a) :=
    (BilinForm.isSymm_ofCLM_iff _).2 fun u v ↦ by
      have h := hherm u v
      rwa [conj_trivial] at h
  exact ⟨theorem_8_3_4 hM' hc hα ℓ, fun u ↦ (isMinOn_energy_univ_iff hM' hc hα hs ℓ u).symm⟩

/-! ### The elasticity form $a(u, v) = \int_\Omega [C \varepsilon(u)] : \varepsilon(v) \, dx$ -/

section Elasticity

variable {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N)))

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open, let $T$ be a bounded linear operator on
$L^2(\Omega)$, and let $i, j, k, l$ be indices. The **strain pairing** is the bounded bilinear
form on $[H^1_0(\Omega)]^N$
$$(u, v) \mapsto \left( T \varepsilon(u)_{kl}, \varepsilon(v)_{ij} \right)_{L^2(\Omega)}.$$

The elasticity form is a finite sum of such pairings. Compare `Elliptic.pairing`. -/
noncomputable def strainPairing
    (T : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (k l i j : Fin N) : SesqForm ℝ (SobolevEuclideanZeroVec N Ω) :=
  (((innerSL ℝ).comp (T.comp (SobolevEuclideanZeroVec.strainL k l))).flip.comp
    (SobolevEuclideanZeroVec.strainL i j)).flip

/-- The strain pairing of $T$ and $i, j, k, l$ at $u, v$ is $(T \varepsilon(u)_{kl},
\varepsilon(v)_{ij})_{L^2(\Omega)}$. -/
theorem strainPairing_apply
    (T : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (k l i j : Fin N) (u v : SobolevEuclideanZeroVec N Ω) :
    strainPairing Ω T k l i j u v
      = ⟪T (SobolevEuclideanZeroVec.strainL k l u), SobolevEuclideanZeroVec.strainL i j v⟫_ℝ :=
  rfl

/-- **Section 8.5** of [han2009theoretical], the elasticity form. Let
$\Omega \subseteq \mathbb{R}^N$ be open, and let $C_{ijkl} \in L^\infty(\Omega)$ for
$i, j, k, l = 1, \dots, N$ (8.5.6). The **elasticity form** on $[H^1_0(\Omega)]^N$ is
$$a(u, v) = \int_\Omega [C \varepsilon(u)] : \varepsilon(v) \, dx = \sum_{i, j, k, l}
  \int_\Omega C_{ijkl} \, \varepsilon_{kl}(u) \, \varepsilon_{ij}(v) \, dx.$$

It is defined as the sum of the strain pairings of the multiplication operators by $C_{ijkl}$.
The integral form is `AtkinsonHan.Chapter08.elasticityForm_apply`.

**Reading.** Bilinear form is restricted to zero trace on the whole boundary.
-/
noncomputable def elasticityForm
    (C : Fin N → Fin N → Fin N → Fin N →
      Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    SesqForm ℝ (SobolevEuclideanZeroVec N Ω) :=
  ∑ i, ∑ j, ∑ k, ∑ l, strainPairing Ω (Elliptic.mulL Ω (C i j k l)) k l i j

/-- **Equations (8.5.6)–(8.5.8)** of [han2009theoretical], the hypotheses on the elasticity tensor.
Let $\Omega \subseteq \mathbb{R}^N$ be open, let $C_{ijkl} \in L^\infty(\Omega)$ (8.5.6), and
let $\alpha \in \mathbb{R}$. Then $C$ is an **elasticity tensor with stability constant**
$\alpha$ if it has the symmetries $C_{ijkl} = C_{jikl} = C_{klij}$ (8.5.7), and $\alpha > 0$
with the stability condition (8.5.8): for almost every $x \in \Omega$ and every symmetric matrix
$\varepsilon \in \mathbb{S}^N$,
$$\sum_{i, j, k, l} C_{ijkl}(x) \, \varepsilon_{kl} \, \varepsilon_{ij} \ge \alpha \sum_{i, j}
  \varepsilon_{ij}^2.$$

The condition (8.5.6) is the type of the components. The symmetry $C_{ijkl} = C_{ijlk}$ follows
from the two symmetries that are fields.

**Reading.** Same symmetries and symmetric strain coercivity in essentially bounded coefficient
classes.
-/
structure IsElasticityTensor
    (C : Fin N → Fin N → Fin N → Fin N →
      Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (α : ℝ) : Prop where
  /-- The symmetry $C_{ijkl} = C_{jikl}$ of (8.5.7). -/
  symm_left : ∀ i j k l, C i j k l = C j i k l
  /-- The symmetry $C_{ijkl} = C_{klij}$ of (8.5.7). -/
  symm_pair : ∀ i j k l, C i j k l = C k l i j
  /-- The stability constant $\alpha$ is positive. -/
  pos : 0 < α
  /-- The stability condition (8.5.8): for almost every $x \in \Omega$ and every symmetric
  $\varepsilon$, $\sum_{i,j,k,l} C_{ijkl}(x) \varepsilon_{kl} \varepsilon_{ij} \ge \alpha
  \sum_{i,j} \varepsilon_{ij}^2$. -/
  stable : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
    ∀ ε : Fin N → Fin N → ℝ, (∀ i j, ε i j = ε j i) →
      α * ∑ i, ∑ j, ε i j ^ 2 ≤ ∑ i, ∑ j, ∑ k, ∑ l, C i j k l x * ε k l * ε i j

variable (C : Fin N → Fin N → Fin N → Fin N →
  Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))

/-- The elasticity form is a sum of $L^2(\Omega)$ inner products of strain components:
$$a(u, v) = \sum_{i, j, k, l} \left( C_{ijkl} \, \varepsilon(u)_{kl}, \varepsilon(v)_{ij}
  \right)_{L^2(\Omega)}.$$
-/
theorem elasticityForm_apply_inner (u v : SobolevEuclideanZeroVec N Ω) :
    elasticityForm Ω C u v = ∑ i, ∑ j, ∑ k, ∑ l,
      ⟪Elliptic.mulL Ω (C i j k l) (SobolevEuclideanZeroVec.strainL k l u),
        SobolevEuclideanZeroVec.strainL i j v⟫_ℝ := by
  simp only [elasticityForm, sum_apply, strainPairing_apply]

/-- The elasticity form is the integral of the contracted product of stress and strain: for
$u, v \in [H^1_0(\Omega)]^N$,
$$a(u, v) = \int_\Omega \sum_{i, j, k, l} C_{ijkl}(x) \, \varepsilon_{kl}(u)(x) \,
  \varepsilon_{ij}(v)(x) \, dx.$$
-/
theorem elasticityForm_apply (u v : SobolevEuclideanZeroVec N Ω) :
    elasticityForm Ω C u v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ∑ i, ∑ j, ∑ k, ∑ l, C i j k l x * SobolevEuclideanZeroVec.strainL k l u x
        * SobolevEuclideanZeroVec.strainL i j v x := by
  rw [elasticityForm_apply_inner]
  simp only [Elliptic.inner_mulL_eq_integral]
  exact sum_sum_sum_sum_integral_eq fun i j k l ↦ Elliptic.integrable_mul_mul Ω _ _ _

/-- The elasticity form is bounded with constant $\sum_{i, j, k, l}
\|C_{ijkl}\|_{L^\infty(\Omega)}$:
$$|a(u, v)| \le \Big( \sum_{i, j, k, l} \|C_{ijkl}\|_{L^\infty(\Omega)} \Big) \|u\| \|v\|.$$

Each term is at most $\|C_{ijkl}\|_\infty \|\varepsilon_{kl}(u)\|_{L^2}
\|\varepsilon_{ij}(v)\|_{L^2}$, and $\|\varepsilon_{ij}(v)\|_{L^2} \le \|v\|$
(`SobolevEuclideanZeroVec.norm_strainL_apply_le`). No hypothesis on $C$ is needed. -/
theorem elasticityForm_isBoundedWith :
    (elasticityForm Ω C).IsBoundedWith (∑ i, ∑ j, ∑ k, ∑ l, ‖C i j k l‖) := by
  intro u v
  rw [Real.norm_eq_abs, elasticityForm_apply_inner]
  have key : ∀ i j k l, |⟪Elliptic.mulL Ω (C i j k l) (SobolevEuclideanZeroVec.strainL k l u),
      SobolevEuclideanZeroVec.strainL i j v⟫_ℝ| ≤ ‖C i j k l‖ * ‖u‖ * ‖v‖ := fun i j k l ↦ by
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖Elliptic.mulL Ω (C i j k l) (SobolevEuclideanZeroVec.strainL k l u)‖
          * ‖SobolevEuclideanZeroVec.strainL i j v‖
        ≤ ‖C i j k l‖ * ‖SobolevEuclideanZeroVec.strainL k l u‖
          * ‖SobolevEuclideanZeroVec.strainL i j v‖ := by
          gcongr
          exact Elliptic.norm_mulL_apply_le Ω _ _
      _ ≤ ‖C i j k l‖ * ‖u‖ * ‖v‖ := by
          gcongr
          · exact SobolevEuclideanZeroVec.norm_strainL_apply_le k l u
          · exact SobolevEuclideanZeroVec.norm_strainL_apply_le i j v
  refine (abs_sum_sum_sum_sum_le _).trans ?_
  calc ∑ i, ∑ j, ∑ k, ∑ l, |⟪Elliptic.mulL Ω (C i j k l)
          (SobolevEuclideanZeroVec.strainL k l u), SobolevEuclideanZeroVec.strainL i j v⟫_ℝ|
      ≤ ∑ i, ∑ j, ∑ k, ∑ l, ‖C i j k l‖ * ‖u‖ * ‖v‖ :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun k _ ↦
          Finset.sum_le_sum fun l _ ↦ key i j k l
    _ = (∑ i, ∑ j, ∑ k, ∑ l, ‖C i j k l‖) * ‖u‖ * ‖v‖ := by
        simp only [Finset.sum_mul]

/-- Let $C$ be an elasticity tensor with stability constant $\alpha$, and let
$S_{ij}, S'_{ij} \in L^2(\Omega)$. Then
$$\sum_{i, j, k, l} (C_{ijkl} S_{kl}, S'_{ij})_{L^2} = \sum_{i, j, k, l} (C_{ijkl} S'_{kl},
  S_{ij})_{L^2}.$$

The proof exchanges the index pairs $(i, j)$ and $(k, l)$ and uses $C_{ijkl} = C_{klij}$. -/
theorem sum_inner_mulL_comm {α : ℝ} (hC : IsElasticityTensor Ω C α)
    (S S' : Fin N → Fin N → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ∑ i, ∑ j, ∑ k, ∑ l, ⟪Elliptic.mulL Ω (C i j k l) (S k l), S' i j⟫_ℝ
      = ∑ i, ∑ j, ∑ k, ∑ l, ⟪Elliptic.mulL Ω (C i j k l) (S' k l), S i j⟫_ℝ := by
  simp only [Elliptic.inner_mulL_eq_integral]
  rw [Finset.sum_sum_sum_sum_comm (fun i j k l ↦ ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
    C i j k l x * S k l x * S' i j x)]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  rw [hC.symm_pair k l i j]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)

/-- Let $C$ be an elasticity tensor with stability constant $\alpha$. Then the elasticity form is
symmetric: $a(u, v) = a(v, u)$ for all $u, v \in [H^1_0(\Omega)]^N$.

The proof exchanges the index pairs $(i, j)$ and $(k, l)$ in the sum and uses
$C_{ijkl} = C_{klij}$. -/
theorem elasticityForm_comm {α : ℝ} (hC : IsElasticityTensor Ω C α)
    (u v : SobolevEuclideanZeroVec N Ω) :
    elasticityForm Ω C u v = elasticityForm Ω C v u := by
  rw [elasticityForm_apply_inner, elasticityForm_apply_inner]
  exact sum_inner_mulL_comm Ω C hC (fun i j ↦ SobolevEuclideanZeroVec.strainL i j u)
    (fun i j ↦ SobolevEuclideanZeroVec.strainL i j v)

/-- Let $C$ be an elasticity tensor with stability constant $\alpha$. Then the elasticity form is
Hermitian in the sense of `SesqForm.IsHermitian`, which over $\mathbb{R}$ is symmetry. -/
theorem elasticityForm_isHermitian {α : ℝ} (hC : IsElasticityTensor Ω C α) :
    (elasticityForm Ω C).IsHermitian := fun u v ↦ by
  rw [conj_trivial]
  exact elasticityForm_comm Ω C hC u v

/-- Let $C$ be an elasticity tensor with stability constant $\alpha$. Then for every
$v \in [H^1_0(\Omega)]^N$,
$$a(v, v) \ge \alpha \sum_{i, j} \|\varepsilon_{ij}(v)\|_{L^2(\Omega)}^2.$$

The proof applies the stability condition (8.5.8) to the symmetric matrix $\varepsilon(v)(x)$
under the integral. -/
theorem elasticityForm_self_ge {α : ℝ} (hC : IsElasticityTensor Ω C α)
    (v : SobolevEuclideanZeroVec N Ω) :
    α * ∑ i, ∑ j, ‖SobolevEuclideanZeroVec.strainL i j v‖ ^ 2 ≤ elasticityForm Ω C v v := by
  rw [elasticityForm_apply_inner]
  obtain ⟨S, hS⟩ : ∃ S : Fin N → Fin N →
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      S = fun i j ↦ SobolevEuclideanZeroVec.strainL i j v := ⟨_, rfl⟩
  have hSsymm : ∀ i j, S i j = S j i := fun i j ↦ by
    rw [hS]
    exact congrFun (congrArg DFunLike.coe (SobolevEuclideanZeroVec.strainL_symm i j)) v
  have hsum : ∑ i, ∑ j, ‖SobolevEuclideanZeroVec.strainL i j v‖ ^ 2 = ∑ i, ∑ j, ‖S i j‖ ^ 2 := by
    rw [hS]
  have hinner : ∀ i j k l, ⟪Elliptic.mulL Ω (C i j k l) (SobolevEuclideanZeroVec.strainL k l v),
      SobolevEuclideanZeroVec.strainL i j v⟫_ℝ = ⟪Elliptic.mulL Ω (C i j k l) (S k l), S i j⟫_ℝ :=
    fun i j k l ↦ by rw [hS]
  simp only [hsum, hinner, Elliptic.inner_mulL_eq_integral]
  have hint : ∀ i j k l, Integrable (fun x ↦ C i j k l x * S k l x * S i j x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i j k l ↦
    Elliptic.integrable_mul_mul Ω _ _ _
  have hsq : ∀ i j, Integrable (fun x ↦ S i j x * S i j x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i j ↦
    (L2.integrable_inner (𝕜 := ℝ) (S i j) (S i j)).congr
      (Eventually.of_forall fun x ↦ by simp [sq])
  have e : ∑ i, ∑ j, ‖S i j‖ ^ 2 = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ∑ i, ∑ j, S i j x * S i j x := by
    rw [integral_finsetSum (f := fun i x ↦ ∑ j, S i j x * S i j x) _ fun i _ ↦
      integrable_finsetSum _ fun j _ ↦ hsq i j]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finsetSum (f := fun j x ↦ S i j x * S i j x) _ fun j _ ↦ hsq i j]
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [← real_inner_self_eq_norm_sq, L2.inner_eq_integral_mul]
  rw [e, ← integral_const_mul, sum_sum_sum_sum_integral_eq hint]
  refine integral_mono_ae ((integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    hsq i j).const_mul α) (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      integrable_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hint i j k l) ?_
  filter_upwards [hC.stable] with x hx
  have h := hx (fun i j ↦ S i j x) fun i j ↦ by rw [hSsymm]
  simpa [sq] using h

end Elasticity

/-! ### $V$-ellipticity on a bounded domain, the load, and Theorem 8.5.1 -/

section Dirichlet

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))
  (C : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) →
    Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))

/-- **Section 8.5** of [han2009theoretical], $V$-ellipticity of the elasticity form. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be open and contained in the ball $B(0, R)$ with $R \ge 0$,
and let $C$ be an elasticity tensor with stability constant $\alpha$. Then the elasticity form
is $V$-elliptic on $[H^1_0(\Omega)]^{d+1}$:
$$a(v, v) \ge \frac{\alpha}{2 (1 + (2R)^2)} \|v\|^2 \quad \text{for all } v \in
  [H^1_0(\Omega)]^{d+1}.$$

This is the step of Exercise 8.5.3 that needs Korn's inequality. On $[H^1_0(\Omega)]^{d+1}$,
Korn's first inequality is enough, and no regularity of the boundary enters. The proof combines
`AtkinsonHan.Chapter08.elasticityForm_self_ge` with Korn's first inequality and the Poincaré
inequality (`SobolevEuclideanZeroVec.norm_sq_le_sum_norm_strainL_sq`). Korn's first inequality
`SobolevEuclideanZeroVec.korn_first` comes from the identity $\int_\Omega |\varepsilon(v)|^2 =
\frac12 \int_\Omega |\nabla v|^2 + \frac12 \int_\Omega (\operatorname{div} v)^2$ on
$[H^1_0(\Omega)]^{d+1}$, which follows by two integrations by parts and density.

**Reading.** Korn and Poincaré bound gives explicit coercivity for zero trace on the whole boundary.
-/
theorem elasticityForm_isCoerciveWith {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R) {α : ℝ}
    (hC : IsElasticityTensor Ω C α) :
    (elasticityForm Ω C).IsCoerciveWith (α / (2 * (1 + (2 * R) ^ 2))) := by
  intro v
  rw [RCLike.re_to_real]
  have h1 := elasticityForm_self_ge Ω C hC v
  have h2 := SobolevEuclideanZeroVec.norm_sq_le_sum_norm_strainL_sq hR hΩ v
  have hpos : 0 < 2 * (1 + (2 * R) ^ 2) := by positivity
  have hα : 0 < α := hC.pos
  calc α / (2 * (1 + (2 * R) ^ 2)) * ‖v‖ ^ 2
      ≤ α / (2 * (1 + (2 * R) ^ 2))
        * (2 * (1 + (2 * R) ^ 2) * ∑ i, ∑ j, ‖SobolevEuclideanZeroVec.strainL i j v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = α * ∑ i, ∑ j, ‖SobolevEuclideanZeroVec.strainL i j v‖ ^ 2 := by
        field_simp
    _ ≤ elasticityForm Ω C v v := h1

/-- **Equation (8.5.14)** of [han2009theoretical], the load. Let $\Omega \subseteq \mathbb{R}^{d+1}$
be open, and let $f \in [L^2(\Omega)]^{d+1}$ be a body force. The **load** is the bounded linear
functional on $[H^1_0(\Omega)]^{d+1}$
$$\ell(v) = \int_\Omega f \cdot v \, dx = \sum_i \int_\Omega f_i v_i \, dx.$$

The traction term $\int_{\Gamma_N} g \cdot v \, ds$ of (8.5.14) is absent in the pure
displacement case.

**Reading.** Pure displacement case keeps only the interior load.
-/
noncomputable def elasticityLoad
    (f : Fin (d + 1) → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    StrongDual ℝ (SobolevEuclideanZeroVec (d + 1) Ω) :=
  ∑ i, (Elliptic.load Ω (f i)).comp ((SobolevEuclideanZero (d + 1) 1 2 Ω).subtypeL.comp
    (PiLp.proj 2 (fun _ : Fin (d + 1) ↦ SobolevEuclideanZero (d + 1) 1 2 Ω) i))

/-- The load satisfies $\ell(v) = \sum_i \int_\Omega f_i v_i \, dx$ for every
$v \in [H^1_0(\Omega)]^{d+1}$.

**Reading.** Evaluates only the body-force term because all boundary displacements are prescribed.
-/
theorem elasticityLoad_apply
    (f : Fin (d + 1) → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (v : SobolevEuclideanZeroVec (d + 1) Ω) :
    elasticityLoad Ω f v = ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      f i x * SobolevMultiIndex.fn (v i : SobolevEuclidean (d + 1) 1 2 Ω) x := by
  simp only [elasticityLoad, sum_apply, ContinuousLinearMap.comp_apply, Elliptic.load_apply]
  rfl

variable {Ω C}

/-- **Theorem 8.5.1** of [han2009theoretical], the pure displacement case $\Gamma_D = \Gamma$. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be open and contained in the ball $B(0, R)$ with $R \ge 0$,
let $C$ be an elasticity tensor that satisfies (8.5.6)–(8.5.8), and let
$f \in [L^2(\Omega)]^{d+1}$. Then the weak problem (8.5.15) without traction term, to find
$u \in [H^1_0(\Omega)]^{d+1}$ with
$$\int_\Omega [C \varepsilon(u)] : \varepsilon(v) \, dx = \int_\Omega f \cdot v \, dx \quad
  \text{for all } v \in [H^1_0(\Omega)]^{d+1},$$
has exactly one solution. Moreover, $u$ solves it if and only if $u$ minimizes the energy
(8.5.17)
$$E(v) = \frac12 \int_\Omega [C \varepsilon(v)] : \varepsilon(v) \, dx - \int_\Omega f \cdot v
  \, dx$$
over $[H^1_0(\Omega)]^{d+1}$, as in (8.5.16).

**Generalization.** The source assumes a Lipschitz domain. In the pure displacement case no
regularity of the boundary is needed, and the theorem here holds on every bounded open set.

The source also allows mixed boundary conditions, with $\operatorname{meas}(\Gamma_D) > 0$ and a
traction $g$ on $\Gamma_N$. That case is not formalized; the module doc comment says what it
needs. The form is `AtkinsonHan.Chapter08.elasticityForm` (see
`AtkinsonHan.Chapter08.elasticityForm_apply`) and the load is
`AtkinsonHan.Chapter08.elasticityLoad` (see `AtkinsonHan.Chapter08.elasticityLoad_apply`). The
proof is the Lax–Milgram lemma `AtkinsonHan.Chapter08.theorem_8_3_4` and Theorem 8.3.3, with the
$V$-ellipticity of `AtkinsonHan.Chapter08.elasticityForm_isCoerciveWith`. -/
theorem theorem_8_5_1_dirichlet {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R) {α : ℝ}
    (hC : IsElasticityTensor Ω C α)
    (f : Fin (d + 1) → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (∃! u : SobolevEuclideanZeroVec (d + 1) Ω,
        ∀ v, elasticityForm Ω C u v = elasticityLoad Ω f v)
      ∧ ∀ u : SobolevEuclideanZeroVec (d + 1) Ω,
        (∀ v, elasticityForm Ω C u v = elasticityLoad Ω f v)
          ↔ IsMinOn (fun v ↦ (1 / 2 : ℝ) * elasticityForm Ω C v v - elasticityLoad Ω f v)
              univ u := by
  have hcoer := elasticityForm_isCoerciveWith Ω C hR hΩ hC
  have hpos : 0 < α / (2 * (1 + (2 * R) ^ 2)) := div_pos hC.pos (by positivity)
  exact existsUnique_and_isMinOn_iff (elasticityForm_isBoundedWith Ω C) hpos hcoer
    (elasticityForm_isHermitian Ω C hC) (elasticityLoad Ω f)

end Dirichlet

end AtkinsonHan.Chapter08
