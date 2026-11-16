/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Normed.Operator.Scaling
import Numlib.Analysis.Sobolev.Affine
import Numlib.Analysis.Sobolev.SeminormCompare
import Numlib.Analysis.Sobolev.Simplex
import Numlib.Analysis.Sobolev.Triangulation
import Numlib.FiniteElement.LagrangeElement

/-!
# Finite element interpolation error on affine families and triangulations

This module proves the interpolation error estimates of the finite element method by the reference
element technique of [han2009theoretical], §10.3. Let $\hat K \subseteq \mathbb{R}^d$ be a reference
element with nodes $\hat x_i \in \overline{\hat K}$ and shape functions $\hat\varphi_i$, and let
$\hat\Pi \hat v = \sum_i \hat v(\hat x_i) \hat\varphi_i$ be its nodal interpolation operator. If
$\hat\Pi$ reproduces the polynomials of degree at most $k$ and $k + 1 > d/2$, then $|\hat v -
\hat\Pi \hat v|_{m, \hat K} \le c |\hat v|_{k+1, \hat K}$ by the Bramble–Hilbert lemma. An element
$K = F_K(\hat K)$ with $F_K(\hat x) = T_K \hat x + b_K$ carries the interpolation operator $\Pi_K$
with the nodes $F_K(\hat x_i)$ and the shape functions $\hat\varphi_i \circ F_K^{-1}$, and the
transport to $K$ gives
$$|v - \Pi_K v|_{m, K} \le c \, h_K^{k+1} \rho_K^{-m} |v|_{k+1, K},$$
where $h_K$ is the diameter of $K$ and $\rho_K$ is the diameter of a ball in $K$. On a regular
family of elements the ratio $h_K / \rho_K$ is bounded, and the estimate becomes $\|v - \Pi_K
v\|_{m, K} \le c \, h_K^{k+1-m} |v|_{k+1, K}$. A sum over the elements of a triangulation of a plane
domain gives the global estimate $\|v - \Pi_h v\|_{m, \Omega} \le c \, h^{k+1-m} |v|_{k+1, \Omega}$
for $m = 0, 1$.

All Sobolev spaces have the exponent $2$, so $H^m = W^{m, 2}$. The one-dimensional counterpart of
these estimates is `Numlib.Approximation.SobolevInterpolation`.

## Main definitions

* `FiniteElement.IsRegularFamily`: a family of collections of elements is regular if $h_K / \rho_K$
  is bounded uniformly and the mesh parameter tends to $0$ (Definition 10.3.6 of
  [han2009theoretical]).

## Main results

* `FiniteElement.sobolevSeminorm_sub_nodalInterp_le`: on the reference element, $|\hat v - \hat\Pi
  \hat v|_{m, \hat K} \le c |\hat v|_{k+1, \hat K}$ when $\hat\Pi$ reproduces the polynomials of
  degree at most $k$ (Theorem 10.3.3).
* `FiniteElement.opNorm_le_diam_div_of_image`: $\|T_K\| \le h_K / \hat\rho$ and
  $\|T_K^{-1}\| \le \hat h / \rho_K$ (Lemma 10.2.2).
* `FiniteElement.sobolevSeminorm_sub_nodalInterp_comp_affine_le`: $|v - \Pi_K v|_{m, K} \le c \,
  h_K^{k+1} \rho_K^{-m} |v|_{k+1, K}$ on every affine image of the reference element (Theorem
  10.3.5).
* `FiniteElement.sobolevNorm_sub_nodalInterp_comp_affine_le`: $\|v - \Pi_K v\|_{m, K} \le c \,
  h_K^{k+1-m} |v|_{k+1, K}$ on a regular family (Corollary 10.3.7).
* `FiniteElement.isRegularFamily_range_K_iff`: regularity of a family of triangulations, in terms of
  the elements and the mesh sizes.
* `Triangulation.sobolevNorm_sub_globalInterp_le`: $\|v - \Pi_h v\|_{m, \Omega} \le c \, h^{k+1-m}
  |v|_{k+1, \Omega}$ for $m = 0, 1$ and a conforming element on a regular family of triangulations
  (Theorem 10.3.9).
* `LagrangeElement.sobolevNorm_sub_globalInterp_le`: the global estimate for the $\mathbb{P}_k$
  Lagrange element.
* `LagrangeElement.exists_mem_polySpaceZero_globalInterp`: the $\mathbb{P}_k$ interpolant of a
  function that vanishes on $\partial\Omega$ lies in the finite element space $V_h$ (Example
  10.4.2).
* `LagrangeElement.finiteDimensional_polySpaceZero`: $V_h$ is finite-dimensional.

## Proof outline

On the reference element, $\hat\Pi$ is bounded from $H^{k+1}(\hat K)$ to $H^m(\hat K)$ through the
embedding $H^{k+1}(\hat K) \hookrightarrow C(\overline{\hat K})$, and it fixes the polynomials of
degree at most $k$. So $|\hat v - \hat\Pi \hat v|_{m, \hat K} \le c \inf_{q \in \mathbb{P}_k} \|\hat
v + q\|_{k+1, \hat K}$, and the Bramble–Hilbert estimate bounds the infimum by
$|\hat v|_{k+1, \hat K}$. Nodal interpolation commutes with $F_K$, so $(v - \Pi_K v) \circ F_K =
\hat v - \hat\Pi \hat v$ with $\hat v = v \circ F_K$. The affine change of variables moves the
seminorms between $K$ and $\hat K$ with the factors $\|T_K\|^{k+1}$ and $\|T_K^{-1}\|^m$, the
factors $|\det T_K|^{\pm 1/2}$ cancel, and Lemma 10.2.2 bounds the operator norms. On a regular
family, $\rho_K \ge h_K / \sigma$. The norm of order $m$ is at most the sum of the seminorms of the
orders $j \le m$, and each of them is bounded by the local estimate at order $j$. The global
estimate adds the squares of the local estimates over the elements.

## Implementation notes

* The reference element is assumed to be a $W^{1, q}$-extension domain for every exponent $q$
  (`IsSobolevExtensionDomainAll`). The embedding $H^{k+1}(\hat K) \hookrightarrow C(\overline{\hat
  K})$ and the Bramble–Hilbert estimate in `Numlib.Analysis.Sobolev.Compactness` and
  `Numlib.Analysis.Sobolev.DenyLions` need this. The reference triangle satisfies it
  (`isSobolevExtensionDomainAll_referenceTriangle`), and so does the unit square.
* A function is read on a representative that is continuous up to the boundary
  (`ContinuousOn v (closure K)`), so that the nodal values are meaningful at nodes on $\partial K$.
  Every element of $H^{k+1}(K)$ with $k + 1 > d/2$ has such a representative.
* Regularity (`FiniteElement.IsRegularFamily`) asks for some inscribed ball of radius $r$ with
  $h_K \le \sigma (2r)$, not for the largest inscribed ball, which Mathlib does not define. The mesh
  parameter is the supremum of the diameters, written inline so that it does not clash with
  `FiniteElement.meshSize` of `Numlib.FiniteElement.Interval`.
* Membership in $H^m(K)$ is `MemSobolev v m 2 K volume`, and the norm and the seminorm are
  `sobolevNorm` and `sobolevSeminorm`. They are built from the tensor of all derivatives of one
  order, not from multi-indices, and take values in $[0, \infty]$. The comparison with the
  multi-index seminorm of the Bramble–Hilbert estimate is `SobolevMultiIndex.sobolevSeminorm_fn_le`
  and `SobolevMultiIndex.topSeminorm_le_mul_toReal_sobolevSeminorm`.
* The nodal interpolation operator is `Approximation.nodalInterp`, and it commutes with the affine
  pullback (`Approximation.nodalInterp_comp`).
* The local estimate on an affine image is proved directly from the affine change of variables in
  $H^m$ (`sobolevSeminorm_comp_affine_le`) and the bound of the operator norm by inscribed balls
  (`ContinuousLinearMap.opNorm_le_diam_div`).
* An element is an open set, its diameter is `Metric.diam`, and a ball of diameter $\rho$ is
  `Metric.closedBall c (ρ / 2)`. In each estimate the constant $c$ is chosen before the elements and
  the functions, so it does not depend on them.
-/

open Filter Metric Topology MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace FiniteElement

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- For a polynomial $q$ in $d$ variables, the function $x \mapsto q(x)$ on $\mathbb{R}^d$ is
continuous. -/
private theorem continuous_eval_coords (q : MvPolynomial (Fin d) ℝ) :
    Continuous fun x : 𝔼 ↦ MvPolynomial.eval (fun i ↦ x i) q :=
  (MvPolynomial.continuous_eval q).comp (PiLp.continuous_ofLp 2 _)

/-! ### Nodal interpolation in Sobolev spaces -/

variable {Ω : Opens (EuclideanSpace ℝ (Fin d))}

/-- Let $\Omega \subseteq \mathbb{R}^d$ be open, let $x_1, \dots, x_I \in \mathbb{R}^d$ be nodes,
and let the shape functions $\varphi_1, \dots, \varphi_I$ lie in $W^{m, p}(\Omega)$. Then for
every function $v : \mathbb{R}^d \to \mathbb{R}$ the nodal interpolant $\sum_i v(x_i) \varphi_i$
lies in $W^{m, p}(\Omega)$. -/
theorem memSobolev_nodalInterp {I : ℕ} {x : Fin I → EuclideanSpace ℝ (Fin d)}
    {φ : Fin I → EuclideanSpace ℝ (Fin d) → ℝ} {m : ℕ} {p : ℝ≥0∞}
    (hφ : ∀ i, MemSobolev (φ i) m p Ω volume) (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    MemSobolev (Approximation.nodalInterp x φ v) m p Ω volume := by
  rw [Approximation.nodalInterp_eq_sum_smul]
  exact MemSobolev.finsetSum fun i _ ↦ (hφ i).const_smul _

/-- Let $\Omega \subseteq \mathbb{R}^d$ be open, let $p \ge 1$, and let the shape functions
$\varphi_i$ lie in $W^{m, p}(\Omega)$. Then for every function $v$ the nodal interpolant at the
nodes $x_i$ satisfies
$$\Big| \sum_i v(x_i) \varphi_i \Big|_{m, p, \Omega} \le \sum_i |v(x_i)| \, |\varphi_i|_{m, p,
  \Omega}.$$
-/
theorem sobolevSeminorm_nodalInterp_le {I : ℕ} {x : Fin I → EuclideanSpace ℝ (Fin d)}
    {φ : Fin I → EuclideanSpace ℝ (Fin d) → ℝ} {m : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hφ : ∀ i, MemSobolev (φ i) m p Ω volume) (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    sobolevSeminorm (Approximation.nodalInterp x φ v) m p Ω volume
      ≤ ∑ i, ‖v (x i)‖ₑ * sobolevSeminorm (φ i) m p Ω volume := by
  rw [Approximation.nodalInterp_eq_sum_smul]
  exact sobolevSeminorm_sum_smul_le hp (fun i _ ↦ hφ i) _

/-- Let $V$ be a real normed space, let $K \subseteq \mathbb{R}^d$ be compact, let
$\iota : V \to C(K)$ be a bounded linear map, and let $y_1, \dots, y_I \in K$. Let
$\Omega \subseteq \mathbb{R}^d$ be open, let $p \ge 1$, and let the functions $\varphi_i$ lie in
$W^{m, p}(\Omega)$. Then for every $w \in V$
$$\Big| \sum_i (\iota w)(y_i) \, \varphi_i \Big|_{m, p, \Omega} \le \|\iota\| \, \|w\| \sum_i
  |\varphi_i|_{m, p, \Omega}.$$
This is the boundedness of the interpolation operator in the first display of the proof of
Theorem 10.3.3 of [han2009theoretical]. -/
theorem sobolevSeminorm_sum_apply_smul_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K] (ι : V →L[ℝ] C(K, ℝ)) {I : ℕ}
    (y : Fin I → K) {φ : Fin I → EuclideanSpace ℝ (Fin d) → ℝ} {m : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hφ : ∀ i, MemSobolev (φ i) m p Ω volume) (w : V) :
    sobolevSeminorm (∑ i, (ι w (y i)) • φ i) m p Ω volume
      ≤ ENNReal.ofReal (‖ι‖ * ‖w‖ * ∑ i, (sobolevSeminorm (φ i) m p Ω volume).toReal) := by
  refine (sobolevSeminorm_sum_smul_le hp (fun i _ ↦ hφ i) _).trans ?_
  calc ∑ i, ‖ι w (y i)‖ₑ * sobolevSeminorm (φ i) m p Ω volume
      ≤ ∑ i, ENNReal.ofReal (‖ι‖ * ‖w‖) * sobolevSeminorm (φ i) m p Ω volume := by
        gcongr with i
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal
          ((ContinuousMap.norm_coe_le_norm _ _).trans (ι.le_opNorm w))
    _ = ENNReal.ofReal (‖ι‖ * ‖w‖) * ∑ i, sobolevSeminorm (φ i) m p Ω volume := by
        rw [Finset.mul_sum]
    _ = _ := by
        rw [ENNReal.ofReal_mul (p := ‖ι‖ * ‖w‖) (by positivity),
          ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ ENNReal.toReal_nonneg]
        congr 1
        exact Finset.sum_congr rfl fun i _ ↦
          (ENNReal.ofReal_toReal (hφ i).sobolevSeminorm_ne_top).symm

local notation "𝟚" => ((2 : ℝ≥0) : ℝ≥0∞)

/-! ### The estimate on the reference element -/

/-- Let $\hat K \subseteq \mathbb{R}^d$ be a bounded open set, and let $K \subseteq \mathbb{R}^d$.
Let $\iota : H^{k+1}(\hat K) \to C(K)$ be a bounded linear map such that for every $u$ there is
a continuous function $\tilde u$ on $\mathbb{R}^d$ that equals $u$ almost everywhere on $\hat K$
and equals $\iota u$ on $K$. Let the nodes $\hat x_i$ lie in $K$ and in $\overline{\hat K}$, and
assume that the nodal interpolation with the shape functions $\hat\varphi_i$ reproduces, at
every point of $\hat K$, every polynomial of total degree at most $k$. Then for every $q$ in the
subspace $\mathbb{P}_k(\hat K)$ of $H^{k+1}(\hat K)$, the interpolant
$\sum_i (\iota q)(\hat x_i) \, \hat\varphi_i$ equals $q$ almost everywhere on $\hat K$. This is
the polynomial invariance (10.3.4) of [han2009theoretical].

The nodes may lie on the boundary of $\hat K$, which is why $\iota$ reads a continuous
representative on a set $K$ that contains the nodes. The space $H^{k+1}(\hat K)$ is
`SobolevEuclidean d (k + 1) 2 Khat`, and $\mathbb{P}_k(\hat K)$ is
`SobolevEuclidean.polynomialSubmodule`. -/
theorem sum_apply_smul_ae_eq_fn_of_mem_polynomialSubmodule
    {Khat : Opens (EuclideanSpace ℝ (Fin d))}
    (hb : Bornology.IsBounded (Khat : Set (EuclideanSpace ℝ (Fin d)))) {k : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (ι : SobolevEuclidean d (k + 1) 𝟚 Khat →L[ℝ] C(K, ℝ))
    (hι : ∀ u, ∃ ut : EuclideanSpace ℝ (Fin d) → ℝ, Continuous ut ∧
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (Khat : Set (EuclideanSpace ℝ (Fin d)))] ut ∧
      ∀ x : K, ι u x = ut x)
    {I : ℕ} (xhat : Fin I → EuclideanSpace ℝ (Fin d))
    (φhat : Fin I → EuclideanSpace ℝ (Fin d) → ℝ) (hx : ∀ i, xhat i ∈ K)
    (hxc : ∀ i, xhat i ∈ closure (Khat : Set (EuclideanSpace ℝ (Fin d))))
    (hP : ∀ q : MvPolynomial (Fin d) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ Khat, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q)
    {q : SobolevEuclidean d (k + 1) 𝟚 Khat}
    (hq : q ∈ SobolevEuclidean.polynomialSubmodule (k := k) (p := 𝟚) hb) :
    (∑ i, (ι q ⟨xhat i, hx i⟩) • φhat i)
      =ᵐ[volume.restrict (Khat : Set (EuclideanSpace ℝ (Fin d)))] SobolevMultiIndex.fn q := by
  obtain ⟨r, hr, hqr⟩ := (SobolevEuclidean.mem_polynomialSubmodule_iff hb).1 hq
  have hrep := hι q
  obtain ⟨qt, hqtc, hqtae, hqtι⟩ := hrep
  have hpq : EqOn (fun x : EuclideanSpace ℝ (Fin d) ↦ MvPolynomial.eval (fun i ↦ x i) r) qt
      (closure (Khat : Set (EuclideanSpace ℝ (Fin d)))) :=
    (continuous_eval_coords r).continuousOn.eqOn_closure_of_ae_eq Khat.isOpen hqtc.continuousOn
      (hqr.symm.trans hqtae)
  have hIq : (∑ i, (ι q ⟨xhat i, hx i⟩) • φhat i) = Approximation.nodalInterp xhat φhat
      (fun x : EuclideanSpace ℝ (Fin d) ↦ MvPolynomial.eval (fun i ↦ x i) r) := by
    rw [Approximation.nodalInterp_eq_sum_smul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hqtι, ← hpq (hxc i)]
  rw [hIq]
  refine Filter.EventuallyEq.trans ?_ hqr.symm
  exact ae_restrict_of_forall_mem Khat.isOpen.measurableSet fun x hx' ↦
    hP r ((MvPolynomial.mem_restrictTotalDegree _ _ _).1 hr) x hx'

/-- Let $\hat K \subseteq \mathbb{R}^d$ be a bounded, preconnected open set that is a
$W^{1, q}$-extension domain for every exponent $q$. Let $k$ and $m$ be natural numbers with
$m \le k + 1$ and $d/2 < k + 1$. Let $\hat x_1, \dots, \hat x_I \in \overline{\hat K}$ be nodes
and $\hat\varphi_1, \dots, \hat\varphi_I \in H^m(\hat K)$ shape functions, and let $\hat\Pi \hat
v = \sum_i \hat v(\hat x_i) \hat\varphi_i$. Assume that $\hat\Pi q = q$ at every point of
$\hat K$ for every polynomial $q$ of total degree at most $k$. Then there is a constant
$c \ge 0$ such that
$$|\hat v - \hat\Pi \hat v|_{m, \hat K} \le c \, |\hat v|_{k+1, \hat K}$$
for every $\hat v \in H^{k+1}(\hat K)$ that is continuous on $\overline{\hat K}$. This is
Theorem 10.3.3 of [han2009theoretical].

The function $\hat v$ is read on its representative that is continuous up to the boundary, so
that the nodal values are meaningful at nodes on the boundary. Every element of
$H^{k+1}(\hat K)$ has such a representative by the embedding $H^{k+1}(\hat K) \hookrightarrow
C(\overline{\hat K})$ (`SobolevEuclidean.exists_isCompactEmbedding_toContinuousMap_of_order`).
The extension hypothesis is `IsSobolevExtensionDomainAll`, and the seminorms are
`sobolevSeminorm` with $p = 2$. The proof bounds the left side by $c \inf_{q \in \mathbb{P}_k}
\|\hat v + q\|_{k+1, \hat K}$ (`FiniteElement.sobolevSeminorm_sum_apply_smul_le`,
`FiniteElement.sum_apply_smul_ae_eq_fn_of_mem_polynomialSubmodule`) and then applies the
Bramble–Hilbert estimate `SobolevEuclidean.exists_ciInf_norm_add_le_mul_topSeminorm`. -/
theorem sobolevSeminorm_sub_nodalInterp_le {Khat : Opens (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsSobolevExtensionDomainAll d Khat)
    (hb : Bornology.IsBounded (Khat : Set (EuclideanSpace ℝ (Fin d))))
    (hc : IsPreconnected (Khat : Set (EuclideanSpace ℝ (Fin d))))
    {k m : ℕ} (hm : m ≤ k + 1) (hkd : (d : ℝ) / 2 < k + 1)
    {I : ℕ} (xhat : Fin I → EuclideanSpace ℝ (Fin d))
    (φhat : Fin I → EuclideanSpace ℝ (Fin d) → ℝ)
    (hx : ∀ i, xhat i ∈ closure (Khat : Set (EuclideanSpace ℝ (Fin d))))
    (hφ : ∀ i, MemSobolev (φhat i) m 2 Khat volume)
    (hP : ∀ q : MvPolynomial (Fin d) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ Khat, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ v : EuclideanSpace ℝ (Fin d) → ℝ, MemSobolev v (k + 1) 2 Khat volume →
      ContinuousOn v (closure (Khat : Set (EuclideanSpace ℝ (Fin d)))) →
      sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 2 Khat volume
        ≤ ENNReal.ofReal c * sobolevSeminorm v (k + 1) 2 Khat volume := by
  classical
  -- the exponent in the backbone's form, `2 = ((2 : ℝ≥0) : ℝ≥0∞)` definitionally
  replace hφ : ∀ i, MemSobolev (φhat i) m 𝟚 Khat volume := hφ
  have : CompactSpace (closure (Khat : Set (EuclideanSpace ℝ (Fin d)))) :=
    isCompact_iff_compactSpace.1 hb.isCompact_closure
  -- the embedding `H^{k+1}(K̂) ↪ C(K̂̄)`
  have hkd' : (d : ℝ) / ((2 : ℝ≥0) : ℝ) < ((k + 1 : ℕ) : ℝ) := by
    rw [NNReal.coe_ofNat]
    push_cast
    exact hkd
  have hemb := SobolevEuclidean.exists_isCompactEmbedding_toContinuousMap_of_order (N := d) k hΩ
    (Or.inr (by norm_num)) hkd' (K := closure (Khat : Set (EuclideanSpace ℝ (Fin d))))
    subset_closure
  obtain ⟨ι, hι, -⟩ := hemb
  -- Bramble–Hilbert: the quotient norm is bounded by the top seminorm
  have hBH := SobolevEuclidean.exists_ciInf_norm_add_le_mul_topSeminorm (N := d) (k := k)
    (p := 2) (hΩ _) hb hc
  obtain ⟨C₁, hC₁, hBH⟩ := hBH
  -- the constants
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = ∑ m' : Fin m → Fin d,
      ‖basisCoordProd (EuclideanSpace.basisFun (Fin d) ℝ).toBasis m'‖ := ⟨_, rfl⟩
  obtain ⟨Ck, hCk⟩ : ∃ Ck : ℝ, Ck = ∑ α : MultiIndexEq (Fin d) (k + 1), ∏ j,
      ‖multiIndexTuple ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis :
        Fin d → EuclideanSpace ℝ (Fin d)) α.1.1 j‖ := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ i, (sobolevSeminorm (φhat i) m 𝟚 Khat volume).toReal :=
    ⟨_, rfl⟩
  have hCm0 : 0 ≤ Cm := by rw [hCm]; positivity
  have hCk0 : 0 ≤ Ck := by rw [hCk]; positivity
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hA0 : 0 ≤ Cm + ‖ι‖ * S := add_nonneg hCm0 (mul_nonneg (norm_nonneg _) hS0)
  have hc0 : 0 ≤ (Cm + ‖ι‖ * S) * C₁ * Ck := mul_nonneg (mul_nonneg hA0 hC₁.le) hCk0
  refine ⟨(Cm + ‖ι‖ * S) * C₁ * Ck, hc0, fun v hv hvc ↦ ?_⟩
  replace hv : MemSobolev v (k + 1) 𝟚 Khat volume := hv
  suffices key : sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat volume
      ≤ ENNReal.ofReal ((Cm + ‖ι‖ * S) * C₁ * Ck) * sobolevSeminorm v (k + 1) 𝟚 Khat volume from
    key
  -- the typed element of `H^{k+1}(K̂)` carrying `v`
  have hv' : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin d) ℝ).toBasis v (k + 1) 𝟚 Khat
      volume := hv.memSobolevMultiIndex
  have hu := hv'.exists_sobolevMultiIndex
  obtain ⟨u, hu⟩ := hu
  -- its continuous representative is `v` on the closure
  have hrep := hι u
  obtain ⟨ut, hutc, hutae, hutι⟩ := hrep
  have hvut : EqOn v ut (closure (Khat : Set (EuclideanSpace ℝ (Fin d)))) :=
    hvc.eqOn_closure_of_ae_eq Khat.isOpen hutc.continuousOn (hu.symm.trans hutae)
  have hnode : ∀ i, v (xhat i) = ι u ⟨xhat i, hx i⟩ := fun i ↦ by rw [hvut (hx i), hutι]
  -- the interpolation operator on the typed space
  obtain ⟨Ip, hIp⟩ : ∃ Ip : SobolevEuclidean d (k + 1) 𝟚 Khat → EuclideanSpace ℝ (Fin d) → ℝ,
      ∀ w, Ip w = ∑ i, (ι w ⟨xhat i, hx i⟩) • φhat i := ⟨_, fun _ ↦ rfl⟩
  have hIpu : Approximation.nodalInterp xhat φhat v = Ip u := by
    rw [Approximation.nodalInterp_eq_sum_smul, hIp]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hnode i]
  have hIpadd : ∀ w₁ w₂, Ip (w₁ + w₂) = Ip w₁ + Ip w₂ := fun w₁ w₂ ↦ by
    rw [hIp, hIp, hIp, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [map_add, ContinuousMap.add_apply, add_smul]
  have hIpmem : ∀ w, MemSobolev (Ip w) m 𝟚 Khat volume := fun w ↦ by
    rw [hIp]
    exact MemSobolev.finsetSum fun i _ ↦ (hφ i).const_smul _
  have hIpbound : ∀ w, sobolevSeminorm (Ip w) m 𝟚 Khat volume
      ≤ ENNReal.ofReal (‖ι‖ * ‖w‖ * S) := fun w ↦ by
    rw [hIp, hS]
    exact sobolevSeminorm_sum_apply_smul_le ι (fun i ↦ ⟨xhat i, hx i⟩) (by norm_num) hφ w
  -- the estimate against `‖u + q‖` for every `q ∈ ℙ_k(K̂)`
  have hvm : MemSobolev v m 𝟚 Khat volume := hv.mono_order (by exact_mod_cast hm)
  have hmain : ∀ q : SobolevEuclidean.polynomialSubmodule (k := k) (p := 𝟚) hb,
      (sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat volume).toReal
        ≤ (Cm + ‖ι‖ * S) * ‖u + q.1‖ := by
    intro q
    have hfnq : MemSobolev (SobolevMultiIndex.fn q.1) (k + 1) 𝟚 Khat volume :=
      SobolevMultiIndex.memSobolev_fn q.1
    have hpoly := sum_apply_smul_ae_eq_fn_of_mem_polynomialSubmodule hb ι hι xhat φhat hx hx hP
      q.2
    rw [← hIp] at hpoly
    have hae : v - Approximation.nodalInterp xhat φhat v
        =ᵐ[volume.restrict (Khat : Set (EuclideanSpace ℝ (Fin d)))]
          (v + SobolevMultiIndex.fn q.1) - Ip (u + q.1) := by
      rw [hIpu, hIpadd]
      filter_upwards [hpoly] with x hx'
      simp only [Pi.sub_apply, Pi.add_apply, hx']
      ring
    rw [sobolevSeminorm_congr_ae hae]
    have h1 : sobolevSeminorm ((v + SobolevMultiIndex.fn q.1) - Ip (u + q.1)) m 𝟚 Khat volume
        ≤ sobolevSeminorm (v + SobolevMultiIndex.fn q.1) m 𝟚 Khat volume
          + sobolevSeminorm (Ip (u + q.1)) m 𝟚 Khat volume :=
      sobolevSeminorm_sub_le (by norm_num) (hvm.add (hfnq.mono_order (by exact_mod_cast hm)))
        (hIpmem _)
    have h2 : sobolevSeminorm (v + SobolevMultiIndex.fn q.1) m 𝟚 Khat volume
        ≤ ENNReal.ofReal (Cm * ‖u + q.1‖) := by
      have hae2 : v + SobolevMultiIndex.fn q.1
          =ᵐ[volume.restrict (Khat : Set (EuclideanSpace ℝ (Fin d)))]
            SobolevMultiIndex.fn (u + q.1) := by
        filter_upwards [hu, SobolevMultiIndex.fn_add u q.1] with x h1 h2
        rw [h2]
        change v x + _ = SobolevMultiIndex.fn u x + _
        rw [h1]
      rw [sobolevSeminorm_congr_ae hae2, ENNReal.ofReal_mul hCm0, hCm]
      exact SobolevMultiIndex.sobolevSeminorm_fn_le (u + q.1) hm
    have h3 := hIpbound (u + q.1)
    have htot : sobolevSeminorm ((v + SobolevMultiIndex.fn q.1) - Ip (u + q.1)) m 𝟚 Khat volume
        ≤ ENNReal.ofReal ((Cm + ‖ι‖ * S) * ‖u + q.1‖) := by
      refine h1.trans ((add_le_add h2 h3).trans (le_of_eq ?_))
      rw [← ENNReal.ofReal_add (mul_nonneg hCm0 (norm_nonneg _))
        (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hS0)]
      congr 1
      ring
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hA0 (norm_nonneg _)) htot
  -- pass to the infimum, apply Bramble–Hilbert and compare the seminorms
  have hinf : (sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat volume).toReal
      ≤ (Cm + ‖ι‖ * S) * ⨅ q : SobolevEuclidean.polynomialSubmodule (k := k) (p := 𝟚) hb,
        ‖u + q‖ := by
    rw [Real.mul_iInf_of_nonneg hA0]
    exact le_ciInf hmain
  have hBHu := hBH u
  have hcmp := SobolevMultiIndex.topSeminorm_le_mul_toReal_sobolevSeminorm u
  rw [← hCk] at hcmp
  have hsv : sobolevSeminorm v (k + 1) 𝟚 Khat volume
      = sobolevSeminorm (SobolevMultiIndex.fn u) (k + 1) 𝟚 Khat volume :=
    sobolevSeminorm_congr_ae hu.symm
  have hfinal : (sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat
      volume).toReal
        ≤ (Cm + ‖ι‖ * S) * C₁ * Ck * (sobolevSeminorm v (k + 1) 𝟚 Khat volume).toReal := by
    rw [hsv]
    refine hinf.trans ?_
    refine (mul_le_mul_of_nonneg_left hBHu hA0).trans ?_
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcmp hC₁.le) hA0).trans
      (le_of_eq ?_)
    ring
  have hlhs : sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat volume ≠ ⊤ :=
    (hvm.sub (memSobolev_nodalInterp hφ v)).sobolevSeminorm_ne_top
  calc sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat volume
      = ENNReal.ofReal (sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat
          volume).toReal := (ENNReal.ofReal_toReal hlhs).symm
    _ ≤ ENNReal.ofReal ((Cm + ‖ι‖ * S) * C₁ * Ck
          * (sobolevSeminorm v (k + 1) 𝟚 Khat volume).toReal) := ENNReal.ofReal_le_ofReal hfinal
    _ = ENNReal.ofReal ((Cm + ‖ι‖ * S) * C₁ * Ck) * sobolevSeminorm v (k + 1) 𝟚 Khat volume := by
          rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_toReal hv.sobolevSeminorm_ne_top]

/-! ### Affine maps between elements -/

/-- Let $\hat K, K \subseteq \mathbb{R}^d$ be bounded, let $T$ be an invertible linear map of
$\mathbb{R}^d$ and $b \in \mathbb{R}^d$, and suppose that $F(\hat x) = T \hat x + b$ maps
$\hat K$ onto $K$. Suppose that $\hat K$ contains a closed ball of diameter $\hat\rho > 0$ and
$K$ contains a closed ball of diameter $\rho_K > 0$. Then
$$\|T\| \le \frac{h_K}{\hat\rho}, \qquad \|T^{-1}\| \le \frac{\hat h}{\rho_K},$$
where $h_K$ and $\hat h$ are the diameters of $K$ and $\hat K$. This is Lemma 10.2.2 of
[han2009theoretical].

A ball of diameter $\rho$ is `Metric.closedBall c (ρ / 2)`. The proof applies
`ContinuousLinearMap.opNorm_le_diam_div` to $F$ and to $F^{-1}(y) = T^{-1} y - T^{-1} b$. -/
theorem opNorm_le_diam_div_of_image {Khat K : Set 𝔼} {T : 𝔼 ≃L[ℝ] 𝔼} {b chat c : 𝔼}
    {ρhat ρK : ℝ} (hρhat : 0 < ρhat) (hρK : 0 < ρK) (hKhatb : Bornology.IsBounded Khat)
    (hKb : Bornology.IsBounded K) (hballhat : closedBall chat (ρhat / 2) ⊆ Khat)
    (hballK : closedBall c (ρK / 2) ⊆ K) (hF : (fun x ↦ T x + b) '' Khat = K) :
    ‖(T : 𝔼 →L[ℝ] 𝔼)‖ ≤ diam K / ρhat ∧ ‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ≤ diam Khat / ρK := by
  constructor
  · have h := ContinuousLinearMap.opNorm_le_diam_div (T : 𝔼 →L[ℝ] 𝔼) (b := b) (S := Khat)
      (D := K) (by positivity) hKb hballhat (fun x hx ↦ hF ▸ Set.mem_image_of_mem _ hx)
    rwa [show 2 * (ρhat / 2) = ρhat by ring] at h
  · have hmaps : ∀ y ∈ K, (T.symm : 𝔼 →L[ℝ] 𝔼) y + (-T.symm b) ∈ Khat := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ : ∃ x ∈ Khat, T x + b = y := by
        rw [← hF] at hy
        obtain ⟨x, hx, hxy⟩ := hy
        exact ⟨x, hx, hxy⟩
      have : (T.symm : 𝔼 →L[ℝ] 𝔼) (T x + b) + (-T.symm b) = x := by
        simp [ContinuousLinearEquiv.coe_coe, map_add]
      rw [this]
      exact hx
    have h := ContinuousLinearMap.opNorm_le_diam_div (T.symm : 𝔼 →L[ℝ] 𝔼) (b := -T.symm b)
      (S := K) (D := Khat) (by positivity) hKhatb hballK hmaps
    rwa [show 2 * (ρK / 2) = ρK by ring] at h


/-- For an invertible linear map $T$ of $\mathbb{R}^d$ and $b \in \mathbb{R}^d$, the map
$y \mapsto T^{-1}(y - b)$ is a left inverse of the affine map $x \mapsto T x + b$. -/
theorem affine_leftInverse (T : 𝔼 ≃L[ℝ] 𝔼) (b : 𝔼) :
    Function.LeftInverse (fun y ↦ T.symm (y - b)) (fun x ↦ T x + b) := fun x ↦ by simp

/-! ### The local estimate on an affine image -/

/-- Let $\hat K \subseteq \mathbb{R}^d$ be a bounded, preconnected open set that is a
$W^{1, q}$-extension domain for every exponent $q$ and contains a closed ball of diameter
$\hat\rho > 0$. Let $m \le k + 1$ and $d/2 < k + 1$, let $\hat x_i \in \overline{\hat K}$ be
nodes and $\hat\varphi_i \in H^m(\hat K)$ shape functions, and assume that the nodal
interpolation $\hat\Pi$ reproduces, at every point of $\hat K$, every polynomial of total degree
at most $k$. Then there is a constant $c \ge 0$ with the following property. Let $T$ be an
invertible linear map of $\mathbb{R}^d$ and $b \in \mathbb{R}^d$, let $K$ be an open set with
$K = F_K(\hat K)$ for $F_K(\hat x) = T \hat x + b$, and let $K$ contain a closed ball of
diameter $\rho_K > 0$. Let $\Pi_K$ be the nodal interpolation operator with the nodes
$F_K(\hat x_i)$ and the shape functions $\hat\varphi_i \circ F_K^{-1}$. Then
$$|v - \Pi_K v|_{m, K} \le c \, \frac{h_K^{k+1}}{\rho_K^m} \, |v|_{k+1, K}$$
for every $v \in H^{k+1}(K)$ that is continuous on $\overline K$, where $h_K$ is the diameter of
$K$. This is Theorem 10.3.5 of [han2009theoretical], estimate (10.3.7).

The constant depends only on $\hat K$ and $\hat\Pi$: it is $c = c_0 \hat h^m / \hat\rho^{k+1}$,
where $c_0$ is the constant of `FiniteElement.sobolevSeminorm_sub_nodalInterp_le` and $\hat h$
is the diameter of $\hat K$. Nodal interpolation commutes with $F_K$
(`Approximation.nodalInterp_comp`), so $(v - \Pi_K v) \circ F_K = \hat v - \hat\Pi \hat v$ with
$\hat v = v \circ F_K$. The proof moves the seminorms between $K$ and $\hat K$ by the affine
change of variables of Theorem 10.3.4 of [han2009theoretical]
(`sobolevSeminorm_le_comp_affine_of_image`, `sobolevSeminorm_comp_affine_le_of_image`) and
bounds $\|T\| \le h_K / \hat\rho$ and $\|T^{-1}\| \le \hat h / \rho_K$ by
`FiniteElement.opNorm_le_diam_div_of_image`. -/
theorem sobolevSeminorm_sub_nodalInterp_comp_affine_le {Khat : Opens 𝔼}
    (hΩ : IsSobolevExtensionDomainAll d Khat)
    (hb : Bornology.IsBounded (Khat : Set 𝔼)) (hc : IsPreconnected (Khat : Set 𝔼))
    {chat : 𝔼} {ρhat : ℝ} (hρhat : 0 < ρhat)
    (hballhat : Metric.closedBall chat (ρhat / 2) ⊆ Khat)
    {k m : ℕ} (hm : m ≤ k + 1) (hkd : (d : ℝ) / 2 < k + 1)
    {I : ℕ} (xhat : Fin I → 𝔼) (φhat : Fin I → 𝔼 → ℝ)
    (hx : ∀ i, xhat i ∈ closure (Khat : Set 𝔼))
    (hφ : ∀ i, MemSobolev (φhat i) m 2 Khat volume)
    (hP : ∀ q : MvPolynomial (Fin d) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ Khat, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (T : 𝔼 ≃L[ℝ] 𝔼) (b : 𝔼) (K : Opens 𝔼),
      (fun x ↦ T x + b) '' Khat = K →
      ∀ {cK : 𝔼} {ρK : ℝ}, 0 < ρK → Metric.closedBall cK (ρK / 2) ⊆ K →
      ∀ v : 𝔼 → ℝ, MemSobolev v (k + 1) 2 K volume → ContinuousOn v (closure (K : Set 𝔼)) →
      sobolevSeminorm (v - Approximation.nodalInterp ((fun x ↦ T x + b) ∘ xhat)
          (fun i ↦ φhat i ∘ fun y ↦ T.symm (y - b)) v) m 2 K volume
        ≤ ENNReal.ofReal (c * Metric.diam (K : Set 𝔼) ^ (k + 1) / ρK ^ m)
          * sobolevSeminorm v (k + 1) 2 K volume := by
  obtain ⟨c₀, hc₀0, hc₀⟩ := sobolevSeminorm_sub_nodalInterp_le hΩ hb hc hm hkd xhat φhat hx hφ hP
  refine ⟨c₀ * Metric.diam (Khat : Set 𝔼) ^ m / ρhat ^ (k + 1), by positivity, ?_⟩
  intro T b K hK cK ρK hρK hballK v hv hvc
  have hKb : Bornology.IsBounded (K : Set 𝔼) := hK ▸ isBounded_image_affine T b hb
  -- the operator norms of `T` and `T⁻¹`
  obtain ⟨hT, hT'⟩ := opNorm_le_diam_div_of_image hρhat hρK hb hKb hballhat hballK hK
  -- the change of variables `F_K`
  have hKhat : Khat = affinePreimage T b K := (affinePreimage_eq_of_image_eq T b hK).symm
  have hG : Function.LeftInverse (fun y ↦ T.symm (y - b)) (fun x ↦ T x + b) :=
    affine_leftInverse T b
  -- the transported shape functions lie in `H^m(K)`
  have hφK : ∀ i, MemSobolev (φhat i ∘ fun y ↦ T.symm (y - b)) m 2 K volume := fun i ↦
    memSobolev_comp_affine_inv T b hK (hφ i)
  -- `w = v − Π_K v` and its transport `w ∘ F_K = v̂ − Π̂ v̂`
  obtain ⟨w, hw⟩ : ∃ w : 𝔼 → ℝ, w = v - Approximation.nodalInterp ((fun x ↦ T x + b) ∘ xhat)
      (fun i ↦ φhat i ∘ fun y ↦ T.symm (y - b)) v := ⟨_, rfl⟩
  have hwmem : MemSobolev w m 2 K volume := by
    rw [hw]
    exact (hv.mono_order (by exact_mod_cast hm)).sub (memSobolev_nodalInterp hφK v)
  have hwF : (fun x ↦ w (T x + b))
      = (fun x ↦ v (T x + b)) - Approximation.nodalInterp xhat φhat (fun x ↦ v (T x + b)) := by
    funext x
    have h := congrFun (Approximation.nodalInterp_comp xhat φhat v hG) x
    change w (T x + b)
      = v (T x + b) - Approximation.nodalInterp xhat φhat (v ∘ fun x ↦ T x + b) x
    rw [← h, hw]
    rfl
  rw [← hw]
  -- back to `K̂`, the estimate there, and forth to `K` at order `k + 1`
  have h6 := sobolevSeminorm_le_comp_affine_of_image T b hK hwmem
  have hvF : MemSobolev (fun x ↦ v (T x + b)) (k + 1) 2 Khat volume := by
    rw [hKhat]
    exact memSobolev_comp_affine T b hv
  have hvFc : ContinuousOn (fun x ↦ v (T x + b)) (closure (Khat : Set 𝔼)) := by
    rw [hKhat]
    exact hvc.comp_affine_closure T b
  have h3 := hc₀ _ hvF hvFc
  rw [← hwF] at h3
  have h5 := sobolevSeminorm_comp_affine_le_of_image T b hK hv
  -- assemble the constants
  have hdet : |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ)
      * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ)) = 1 :=
    abs_det_rpow_half_mul_rpow_neg_half T
  have hA0 : 0 ≤ ‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ) := by
    positivity
  have hreal : ‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ)
      * (c₀ * (‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1) * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ))))
      ≤ c₀ * Metric.diam (Khat : Set 𝔼) ^ m / ρhat ^ (k + 1) * Metric.diam (K : Set 𝔼) ^ (k + 1)
        / ρK ^ m := by
    have e : ‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ)
        * (c₀ * (‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1) * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ))))
        = c₀ * ‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * ‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1)
          * (|LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ)
            * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ))) := by ring
    rw [e, hdet, mul_one]
    have h1 : ‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m ≤ (Metric.diam (Khat : Set 𝔼) / ρK) ^ m :=
      pow_le_pow_left₀ (norm_nonneg _) hT' m
    have h2 : ‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1) ≤ (Metric.diam (K : Set 𝔼) / ρhat) ^ (k + 1) :=
      pow_le_pow_left₀ (norm_nonneg _) hT (k + 1)
    calc c₀ * ‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * ‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1)
        ≤ c₀ * (Metric.diam (Khat : Set 𝔼) / ρK) ^ m
            * (Metric.diam (K : Set 𝔼) / ρhat) ^ (k + 1) := by
          gcongr
      _ = c₀ * Metric.diam (Khat : Set 𝔼) ^ m / ρhat ^ (k + 1) * Metric.diam (K : Set 𝔼) ^ (k + 1)
            / ρK ^ m := by
          rw [div_pow, div_pow]
          field_simp
  calc sobolevSeminorm w m 2 K volume
      ≤ ENNReal.ofReal (‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ))
          * (ENNReal.ofReal c₀ * (ENNReal.ofReal (‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1)
            * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ)))
            * sobolevSeminorm v (k + 1) 2 K volume)) := by
        refine h6.trans ?_
        gcongr
        exact h3.trans (by gcongr)
    _ = ENNReal.ofReal (‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ)
          * (c₀ * (‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1) * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ)))))
          * sobolevSeminorm v (k + 1) 2 K volume := by
        rw [ENNReal.ofReal_mul hA0, ENNReal.ofReal_mul hc₀0, mul_assoc, mul_assoc]
    _ ≤ _ := by gcongr

/-- Let $h, \rho, \sigma, H$ be real numbers with $0 \le h \le \sigma \rho$, $\rho > 0$,
$\sigma \ge 0$ and $h \le H$, and let $j \le m \le k + 1$ be natural numbers. Then $h^{k+1} /
\rho^j \le \sigma^j H^{m-j} h^{k+1-m}$. This is the arithmetic of the estimate on a regular
family. -/
theorem pow_div_pow_le_of_le_mul {h ρ σ H : ℝ} (hh : 0 ≤ h) (hρ : 0 < ρ) (hσ : 0 ≤ σ)
    (hhσ : h ≤ σ * ρ) (hhH : h ≤ H) {j m k : ℕ} (hjm : j ≤ m) (hmk : m ≤ k + 1) :
    h ^ (k + 1) / ρ ^ j ≤ σ ^ j * H ^ (m - j) * h ^ (k + 1 - m) := by
  obtain ⟨a, rfl⟩ : ∃ a, m = j + a := ⟨m - j, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, k + 1 = j + a + e := ⟨k + 1 - (j + a), by omega⟩
  rw [he, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, pow_add, pow_add,
    div_le_iff₀ (by positivity)]
  have h1 : h ^ j ≤ (σ * ρ) ^ j := pow_le_pow_left₀ hh hhσ j
  have h2 : h ^ a ≤ H ^ a := pow_le_pow_left₀ hh hhH a
  calc h ^ j * h ^ a * h ^ e ≤ (σ * ρ) ^ j * H ^ a * h ^ e := by gcongr
    _ = σ ^ j * H ^ a * h ^ e * ρ ^ j := by ring

/-! ### Regular families -/

/-- Let $E$ be a pseudometric space, and let $(\mathcal{T}_i)_{i \in \iota}$ be a family of
collections of subsets of $E$, called elements, indexed along a filter $l$ on $\iota$. Write
$h_K$ for the diameter of an element $K$. The family is **regular** if

* (a) there is a $\sigma$ such that every element $K$ of every $\mathcal{T}_i$ contains a closed
  ball of some radius $r > 0$ with $h_K \le \sigma (2r)$, and
* (b) the mesh parameter $h_i = \sup_{K \in \mathcal{T}_i} h_K$ tends to $0$ along $l$.

This is Definition 10.3.6 of [han2009theoretical].

Condition (a) is the inequality $h_K \le \sigma \rho_K$, with $\rho_K$ the diameter of the
largest inscribed ball, whenever that ball exists. Regularity turns the element-wise estimate
`FiniteElement.sobolevSeminorm_sub_nodalInterp_comp_affine_le`, whose right side contains both
$h_K$ and $\rho_K$, into a bound in $h_K$ alone
(`FiniteElement.sobolevNorm_sub_nodalInterp_comp_affine_le`). The diameter is `Metric.diam`,
which is $0$ for an unbounded set, and the supremum is the real supremum `sSup`, which is $0$
for an empty or unbounded set of diameters. -/
def IsRegularFamily {E ι : Type*} [PseudoMetricSpace E] (l : Filter ι) (T : ι → Set (Set E)) :
    Prop :=
  (∃ σ : ℝ, ∀ i, ∀ K ∈ T i, ∃ (c : E) (r : ℝ),
      0 < r ∧ closedBall c r ⊆ K ∧ diam K ≤ σ * (2 * r)) ∧
    Tendsto (fun i ↦ sSup (diam '' T i)) l (𝓝 0)

/-- Let $\hat K \subseteq \mathbb{R}^d$ be a bounded, preconnected open set that is a
$W^{1, q}$-extension domain for every exponent $q$ and contains a closed ball of diameter
$\hat\rho > 0$. Let $m \le k + 1$ and $d/2 < k + 1$, let $\hat x_i \in \overline{\hat K}$ be
nodes and $\hat\varphi_i \in H^m(\hat K)$ shape functions, and assume that the nodal
interpolation $\hat\Pi$ reproduces, at every point of $\hat K$, every polynomial of total degree
at most $k$. Let $(\mathcal{T}_i)_{i \in \iota}$ be a regular family of collections of subsets
of $\mathbb{R}^d$ (`FiniteElement.IsRegularFamily`) whose elements all have diameter at most
$H$. Then there is a constant $c \ge 0$ with the following property. Let $K$ be an element of
some $\mathcal{T}_i$ that is open and equal to $F_K(\hat K)$ for $F_K(\hat x) = T \hat x + b$,
with $T$ an invertible linear map of $\mathbb{R}^d$ and $b \in \mathbb{R}^d$. Let $\Pi_K$ be the
nodal interpolation operator with the nodes $F_K(\hat x_i)$ and the shape functions
$\hat\varphi_i \circ F_K^{-1}$. Then
$$\|v - \Pi_K v\|_{m, K} \le c \, h_K^{k+1-m} \, |v|_{k+1, K}$$
for every $v \in H^{k+1}(K)$ that is continuous on $\overline K$, where $h_K$ is the diameter of
$K$. This is Corollary 10.3.7 of [han2009theoretical], estimate (10.3.10).

The source leaves the bound $h_K \le H$ implicit. It enters the constant through the seminorms
of lower order. Regularity gives $\rho_K \ge h_K / \sigma$, which turns the factor
$h_K^{k+1} \rho_K^{-m}$ of the local estimate into $\sigma^m h_K^{k+1-m}$. The norm
$\|\cdot\|_{m, K}$ is at most the sum of the seminorms of the orders $j \le m$
(`MemSobolev.sobolevNorm_le_sum_sobolevSeminorm`), and each of them is bounded by the local
estimate at order $j$ with $h_K^{k+1-j} = h_K^{m-j} h_K^{k+1-m} \le H^{m-j} h_K^{k+1-m}$. In the
Lean statement the element $K$ is a set, and an open set `Kop` with the same points carries the
Sobolev norms. -/
theorem sobolevNorm_sub_nodalInterp_comp_affine_le {Khat : Opens 𝔼}
    (hΩ : IsSobolevExtensionDomainAll d Khat)
    (hb : Bornology.IsBounded (Khat : Set 𝔼)) (hc : IsPreconnected (Khat : Set 𝔼))
    {chat : 𝔼} {ρhat : ℝ} (hρhat : 0 < ρhat)
    (hballhat : Metric.closedBall chat (ρhat / 2) ⊆ Khat)
    {k m : ℕ} (hm : m ≤ k + 1) (hkd : (d : ℝ) / 2 < k + 1)
    {I : ℕ} (xhat : Fin I → 𝔼) (φhat : Fin I → 𝔼 → ℝ)
    (hx : ∀ i, xhat i ∈ closure (Khat : Set 𝔼))
    (hφ : ∀ i, MemSobolev (φhat i) m 2 Khat volume)
    (hP : ∀ q : MvPolynomial (Fin d) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ Khat, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q)
    {ι : Type*} {l : Filter ι} {𝒯 : ι → Set (Set 𝔼)} (hreg : IsRegularFamily l 𝒯)
    {H : ℝ} (hH : ∀ i, ∀ K ∈ 𝒯 i, Metric.diam K ≤ H) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ∀ K ∈ 𝒯 i, ∀ Kop : Opens 𝔼, (Kop : Set 𝔼) = K →
      ∀ (T : 𝔼 ≃L[ℝ] 𝔼) (b : 𝔼), (fun x ↦ T x + b) '' Khat = Kop →
      ∀ v : 𝔼 → ℝ, MemSobolev v (k + 1) 2 Kop volume → ContinuousOn v (closure (Kop : Set 𝔼)) →
      sobolevNorm (v - Approximation.nodalInterp ((fun x ↦ T x + b) ∘ xhat)
          (fun i ↦ φhat i ∘ fun y ↦ T.symm (y - b)) v) m 2 Kop volume
        ≤ ENNReal.ofReal (c * Metric.diam K ^ (k + 1 - m))
          * sobolevSeminorm v (k + 1) 2 Kop volume := by
  obtain ⟨σ, hσ⟩ := hreg.1
  -- the local estimate at every order `j ≤ m`
  have h5 : ∀ j : Fin (m + 1), ∃ c : ℝ, 0 ≤ c ∧ ∀ (T : 𝔼 ≃L[ℝ] 𝔼) (b : 𝔼) (K : Opens 𝔼),
      (fun x ↦ T x + b) '' Khat = K →
      ∀ {cK : 𝔼} {ρK : ℝ}, 0 < ρK → Metric.closedBall cK (ρK / 2) ⊆ K →
      ∀ v : 𝔼 → ℝ, MemSobolev v (k + 1) 2 K volume → ContinuousOn v (closure (K : Set 𝔼)) →
      sobolevSeminorm (v - Approximation.nodalInterp ((fun x ↦ T x + b) ∘ xhat)
          (fun i ↦ φhat i ∘ fun y ↦ T.symm (y - b)) v) j 2 K volume
        ≤ ENNReal.ofReal (c * Metric.diam (K : Set 𝔼) ^ (k + 1) / ρK ^ (j : ℕ))
          * sobolevSeminorm v (k + 1) 2 K volume := fun j ↦
    sobolevSeminorm_sub_nodalInterp_comp_affine_le hΩ hb hc hρhat hballhat
      ((Nat.lt_succ_iff.1 j.2).trans hm) hkd xhat φhat hx
      (fun i ↦ (hφ i).mono_order (by exact_mod_cast Nat.lt_succ_iff.1 j.2)) hP
  choose cj hcj0 hcj using h5
  obtain ⟨σ', hσ'⟩ : ∃ σ' : ℝ, σ' = max σ 0 := ⟨_, rfl⟩
  obtain ⟨H', hH'⟩ : ∃ H' : ℝ, H' = max H 0 := ⟨_, rfl⟩
  have hσ'0 : 0 ≤ σ' := hσ' ▸ le_max_right _ _
  have hH'0 : 0 ≤ H' := hH' ▸ le_max_right _ _
  refine ⟨∑ j : Fin (m + 1), cj j * σ' ^ (j : ℕ) * H' ^ (m - j),
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (mul_nonneg (hcj0 j) (by positivity)) (by positivity),
    ?_⟩
  intro i K hK Kop hKop T b hF v hv hvc
  obtain ⟨cK, r, hr, hball, hdiam⟩ := hσ i K hK
  have hball' : Metric.closedBall cK (2 * r / 2) ⊆ Kop := by
    rw [hKop, mul_div_cancel_left₀ _ (two_ne_zero' ℝ)]
    exact hball
  have hdiamK : Metric.diam (Kop : Set 𝔼) = Metric.diam K := by rw [hKop]
  have hw : MemSobolev (v - Approximation.nodalInterp ((fun x ↦ T x + b) ∘ xhat)
      (fun i ↦ φhat i ∘ fun y ↦ T.symm (y - b)) v) m 2 Kop volume :=
    (hv.mono_order (by exact_mod_cast hm)).sub
      (memSobolev_nodalInterp (fun i ↦ memSobolev_comp_affine_inv T b hF (hφ i)) v)
  refine (hw.sobolevNorm_le_sum_sobolevSeminorm (by norm_num)).trans ?_
  -- the real inequality of each order
  have hreal : ∀ j : Fin (m + 1), cj j * Metric.diam (Kop : Set 𝔼) ^ (k + 1) / (2 * r) ^ (j : ℕ)
      ≤ cj j * σ' ^ (j : ℕ) * H' ^ (m - j) * Metric.diam K ^ (k + 1 - m) := by
    intro j
    rw [hdiamK, mul_div_assoc, mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hcj0 j)
    rw [← mul_assoc]
    refine pow_div_pow_le_of_le_mul Metric.diam_nonneg (by positivity) hσ'0 ?_ ?_
      (Nat.lt_succ_iff.1 j.2) hm
    · exact hdiam.trans (mul_le_mul_of_nonneg_right (hσ' ▸ le_max_left _ _) (by positivity))
    · exact (hH i K hK).trans (hH' ▸ le_max_left _ _)
  calc ∑ j : Fin (m + 1), sobolevSeminorm (v - Approximation.nodalInterp ((fun x ↦ T x + b) ∘ xhat)
        (fun i ↦ φhat i ∘ fun y ↦ T.symm (y - b)) v) j 2 Kop volume
      ≤ ∑ j : Fin (m + 1), ENNReal.ofReal (cj j * σ' ^ (j : ℕ) * H' ^ (m - j)
          * Metric.diam K ^ (k + 1 - m)) * sobolevSeminorm v (k + 1) 2 Kop volume := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        refine (hcj j T b Kop hF (by positivity) hball' v hv hvc).trans ?_
        gcongr
        exact hreal j
    _ = ENNReal.ofReal (∑ j : Fin (m + 1), cj j * σ' ^ (j : ℕ) * H' ^ (m - j)
          * Metric.diam K ^ (k + 1 - m)) * sobolevSeminorm v (k + 1) 2 Kop volume := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun j _ ↦
          mul_nonneg (mul_nonneg (mul_nonneg (hcj0 j) (by positivity)) (by positivity))
            (by positivity)]
    _ = _ := by rw [Finset.sum_mul]

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- Let $(\mathcal{T}_i)_{i \in \iota}$ be a family of triangulations of an open set
$\Omega \subseteq \mathbb{R}^2$, indexed along a filter $l$. The family of the collections of
open elements of the $\mathcal{T}_i$ is regular in the sense of `FiniteElement.IsRegularFamily`
if and only if (a) there is a $\sigma$ such that every element $K$ of every $\mathcal{T}_i$
contains a closed ball of some radius $r > 0$ with $h_K \le \sigma (2r)$, and (b) the mesh sizes
of the $\mathcal{T}_i$ tend to $0$ along $l$. This is Definition 10.3.6 of [han2009theoretical]
for triangulations.

The open element of a vertex triple is `Triangulation.K`, and the mesh size is
`Triangulation.meshSize`. -/
theorem isRegularFamily_range_K_iff {Ω : Opens 𝔼₂} {ι : Type*} (l : Filter ι)
    (𝒯 : ι → Triangulation Ω) :
    IsRegularFamily l (fun i ↦ Set.range (𝒯 i).K) ↔
      (∃ σ : ℝ, ∀ i, ∀ T : (𝒯 i).elems, ∃ (c : 𝔼₂) (r : ℝ), 0 < r ∧
        closedBall c r ⊆ (𝒯 i).K T ∧ diam ((𝒯 i).K T) ≤ σ * (2 * r)) ∧
      Tendsto (fun i ↦ (𝒯 i).meshSize) l (𝓝 0) := by
  simp only [IsRegularFamily, ← Triangulation.meshSize_eq_sSup_image, Set.forall_mem_range]

end FiniteElement

/-! ### The global estimate on a triangulation -/

namespace Triangulation

open EuclideanSpace

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- Let $(\mathcal{T}_i)_{i \in \iota}$ be a family of triangulations of an open set
$\Omega \subseteq \mathbb{R}^2$, indexed along a filter $l$, which is regular
(`FiniteElement.IsRegularFamily` for the collections of open elements) and whose mesh sizes
$h_i$ are all at most $H$. Let $k \ge 1$ and $m \in \{0, 1\}$. On the reference triangle
$\hat K$, let the nodes $\hat x_i$ lie in $\overline{\hat K}$, let the shape functions
$\hat\varphi_i$ be continuously differentiable on $\mathbb{R}^2$, and assume that the nodal
interpolation $\hat\Pi$ reproduces, at every point of $\hat K$, every polynomial of total degree
at most $k$. Assume that this element is conforming on every $\mathcal{T}_i$. Then there is a
constant $c \ge 0$, independent of $i$, such that the global interpolant $\Pi_h$ on
$\mathcal{T}_i$ satisfies
$$\|v - \Pi_h v\|_{m, \Omega} \le c \, h_i^{k+1-m} \, |v|_{k+1, \Omega}$$
for every $i$ and every $v \in H^{k+1}(\Omega)$ that is continuous on $\overline\Omega$. This is
Theorem 10.3.9 of [han2009theoretical], estimate (10.3.13).

The reference triangle is `EuclideanSpace.referenceTriangle`, the global interpolant is
`Triangulation.globalInterp`, and conformity is `Triangulation.IsConformingElement`. The proof
writes $\|v - \Pi_h v\|_{m, \Omega}^2 = \sum_K \|v - \Pi_K v\|_{m, K}^2$
(`Triangulation.sobolevNorm_rpow_eq_sum`), which needs $v - \Pi_h v \in H^m(\Omega)$, given for
$m = 1$ by conformity. It bounds each term by
`FiniteElement.sobolevNorm_sub_nodalInterp_comp_affine_le` with $h_K \le h_i$, and it uses
$\sum_K |v|_{k+1, K}^2 = |v|_{k+1, \Omega}^2$. -/
theorem sobolevNorm_sub_globalInterp_le {k m : ℕ} (hm : m ≤ 1) (hk : 1 ≤ k)
    {I : ℕ} (xhat : Fin I → 𝔼₂) (φhat : Fin I → 𝔼₂ → ℝ)
    (hx : ∀ i, xhat i ∈ closure (referenceTriangle : Set 𝔼₂))
    (hφ : ∀ i, ContDiff ℝ 1 (φhat i))
    (hP : ∀ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ referenceTriangle, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q)
    {Ω : Opens 𝔼₂} {ι : Type*} {l : Filter ι} {𝒯 : ι → Triangulation Ω}
    (hreg : FiniteElement.IsRegularFamily l fun i ↦ Set.range (𝒯 i).K)
    {H : ℝ} (hH : ∀ i, (𝒯 i).meshSize ≤ H)
    (hconf : ∀ i, (𝒯 i).IsConformingElement xhat φhat) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ∀ v : 𝔼₂ → ℝ, MemSobolev v (k + 1) 2 Ω volume →
      ContinuousOn v (closure (Ω : Set 𝔼₂)) →
      sobolevNorm (v - (𝒯 i).globalInterp xhat φhat v) m 2 Ω volume
        ≤ ENNReal.ofReal (c * (𝒯 i).meshSize ^ (k + 1 - m))
          * sobolevSeminorm v (k + 1) 2 Ω volume := by
  -- the elementwise estimate on the reference triangle
  have hφ1 : ∀ i, MemSobolev (φhat i) m 2 referenceTriangle volume := fun i ↦
    ((hφ i).memSobolev_of_isBounded isBounded_referenceTriangle 2).mono_order
      (by exact_mod_cast hm)
  have hkd : (2 : ℝ) / 2 < k + 1 := by
    norm_num
    exact_mod_cast hk
  have hH' : ∀ i, ∀ K ∈ Set.range (𝒯 i).K, Metric.diam K ≤ H := by
    rintro i _ ⟨T, rfl⟩
    exact ((𝒯 i).diam_le_meshSize T).trans (hH i)
  obtain ⟨c, hc0, hc⟩ := FiniteElement.sobolevNorm_sub_nodalInterp_comp_affine_le (k := k) (m := m)
    isSobolevExtensionDomainAll_referenceTriangle isBounded_referenceTriangle
    convex_referenceTriangle.isPreconnected (by norm_num : (0 : ℝ) < 1 / 4)
    closedBall_subset_referenceTriangle (hm.trans (by omega)) hkd xhat φhat hx hφ1 hP hreg hH'
  refine ⟨c, hc0, fun i v hv hvc ↦ ?_⟩
  -- `v − Π_h v ∈ H^m(Ω)`: the conformity of the element
  have hw : MemSobolev (v - (𝒯 i).globalInterp xhat φhat v) m 2 Ω volume :=
    (hv.mono_order (by exact_mod_cast (show m ≤ k + 1 by omega))).sub
      (((𝒯 i).memSobolev_globalInterp xhat φhat (hconf i) hφ v 2).mono_order
        (by exact_mod_cast hm))
  -- the bound on each element, with `h_K ≤ h`
  have helem : ∀ T : (𝒯 i).elems,
      sobolevNorm (v - (𝒯 i).globalInterp xhat φhat v) m 2 ((𝒯 i).Kopens T) volume
        ≤ ENNReal.ofReal (c * (𝒯 i).meshSize ^ (k + 1 - m))
          * sobolevSeminorm v (k + 1) 2 ((𝒯 i).Kopens T) volume := by
    intro T
    rw [(𝒯 i).sobolevNorm_sub_globalInterp xhat φhat (hconf i) T v m]
    refine (hc i _ ⟨T, rfl⟩ ((𝒯 i).Kopens T) rfl ((𝒯 i).linearPart T) (T.1 0)
      ((𝒯 i).image_referenceTriangle T) v (hv.mono_set ((𝒯 i).Kopens_le T))
      (hvc.mono (closure_mono ((𝒯 i).K_subset T)))).trans ?_
    gcongr
    exact (𝒯 i).diam_le_meshSize T
  -- sum the squares over the elements
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  have hsum := (𝒯 i).sobolevNorm_rpow_eq_sum (p := 2) (by simp) hw
  have hsum' := (𝒯 i).sobolevSeminorm_rpow_eq_sum (p := 2) (by simp) hv
  rw [h2] at hsum hsum'
  have key : sobolevNorm (v - (𝒯 i).globalInterp xhat φhat v) m 2 Ω volume ^ (2 : ℝ)
      ≤ (ENNReal.ofReal (c * (𝒯 i).meshSize ^ (k + 1 - m))
          * sobolevSeminorm v (k + 1) 2 Ω volume) ^ (2 : ℝ) := by
    rw [hsum, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hsum', Finset.mul_sum]
    refine Finset.sum_le_sum fun T _ ↦ ?_
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    exact ENNReal.rpow_le_rpow (helem T) (by norm_num)
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).1 key

end Triangulation

/-! ### The $\mathbb{P}_k$ Lagrange element -/

namespace LagrangeElement

open EuclideanSpace

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- Let $(\mathcal{T}_i)_{i \in \iota}$ be a family of triangulations of an open set
$\Omega \subseteq \mathbb{R}^2$, indexed along a filter $l$, which is regular
(`FiniteElement.IsRegularFamily` for the collections of open elements) and whose mesh sizes
$h_i$ are all at most $H$. Let $k \ge 1$ and $m \in \{0, 1\}$. Then there is a constant
$c \ge 0$ such that the continuous piecewise $\mathbb{P}_k$ interpolant $\Pi_h v$ at the lattice
nodes of $\mathcal{T}_i$ satisfies
$$\|v - \Pi_h v\|_{m, \Omega} \le c \, h_i^{k+1-m} \, |v|_{k+1, \Omega}$$
for every $i$ and every $v \in H^{k+1}(\Omega)$ that is continuous on $\overline\Omega$. This is
Theorem 10.3.9 of [han2009theoretical] for the affine-equivalent spaces of piecewise polynomials
of degree at most $k$.

The nodes and the shape functions are `LagrangeElement.node` and `LagrangeElement.shape`. The
proof applies `Triangulation.sobolevNorm_sub_globalInterp_le`: the element is conforming
(`LagrangeElement.isConformingElement`) and reproduces the polynomials of degree at most $k$
(`LagrangeElement.nodalInterp_eval`). -/
theorem sobolevNorm_sub_globalInterp_le {k m : ℕ} (hm : m ≤ 1) (hk : 1 ≤ k) {Ω : Opens 𝔼₂}
    {ι : Type*} {l : Filter ι} {𝒯 : ι → Triangulation Ω}
    (hreg : FiniteElement.IsRegularFamily l fun i ↦ Set.range (𝒯 i).K)
    {H : ℝ} (hH : ∀ i, (𝒯 i).meshSize ≤ H) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ∀ v : 𝔼₂ → ℝ, MemSobolev v (k + 1) 2 Ω volume →
      ContinuousOn v (closure (Ω : Set 𝔼₂)) →
      sobolevNorm (v - (𝒯 i).globalInterp (node k) (shape k) v) m 2 Ω volume
        ≤ ENNReal.ofReal (c * (𝒯 i).meshSize ^ (k + 1 - m))
          * sobolevSeminorm v (k + 1) 2 Ω volume :=
  Triangulation.sobolevNorm_sub_globalInterp_le hm hk (node k) (shape k) (node_mem_closure hk)
    (fun i ↦ (contDiff_shape k i).of_le (by simp))
    (fun q hq x _ ↦ nodalInterp_eval hk q hq x) hreg hH
    fun i ↦ isConformingElement hk (𝒯 i)

/-- Let $\mathcal{T}$ be a triangulation of an open set $\Omega \subseteq \mathbb{R}^2$ whose
boundary is a union of element edges, and let $k \ge 1$ and $1 \le p < \infty$. If
$v : \mathbb{R}^2 \to \mathbb{R}$ vanishes on $\partial\Omega$, then its $\mathbb{P}_k$ Lagrange
interpolant $\Pi_h v$ is, almost everywhere on $\Omega$, the function of an element of $V_h$.
Here $V_h$ is the space of continuous piecewise $\mathbb{P}_k$ functions that vanish on
$\partial\Omega$, as a subspace of $W^{1, p}_0(\Omega)$. This is the step $v_h = \Pi_h u$ of
Example 10.4.2 of [han2009theoretical].

The space $V_h$ is `Triangulation.polySpaceZero`, and the hypothesis on the boundary is
`Triangulation.FrontierSubsetEdges`. The function $v$ need not be continuous, because $\Pi_h v$
depends only on the nodal values. The proof applies
`Triangulation.exists_mem_polySpaceZero_globalInterp`: the element is conforming, edge
unisolvent and polynomial. -/
theorem exists_mem_polySpaceZero_globalInterp {k : ℕ} (hk : 0 < k) {Ω : Opens 𝔼₂}
    (𝒯 : Triangulation Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hedge : 𝒯.FrontierSubsetEdges)
    {v : 𝔼₂ → ℝ} (hv0 : EqOn v 0 (frontier (Ω : Set 𝔼₂))) :
    ∃ w ∈ 𝒯.polySpaceZero p k, SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 p Ω)
      =ᵐ[volume.restrict (Ω : Set 𝔼₂)] 𝒯.globalInterp (node k) (shape k) v :=
  𝒯.exists_mem_polySpaceZero_globalInterp p hp (isConformingElement hk 𝒯)
    (fun i ↦ (contDiff_shape k i).continuous) (isEdgeUnisolvent hk) (shape_eq_eval k) hedge hv0

/-- Let $\mathcal{T}$ be a triangulation of an open set $\Omega \subseteq \mathbb{R}^2$, and let
$k \ge 1$ and $p \ge 1$. Then the space $V_h$ of continuous piecewise $\mathbb{P}_k$ functions
that vanish on $\partial\Omega$, as a subspace of $W^{1, p}_0(\Omega)$, is finite-dimensional.
Its elements are determined by their values at the nodes of the $\mathbb{P}_k$ Lagrange element.
$V_h$ is the finite element space of Example 10.4.2 of [han2009theoretical].

The space is `Triangulation.polySpaceZero`, and the proof applies
`Triangulation.finiteDimensional_polySpaceZero`. -/
theorem finiteDimensional_polySpaceZero {k : ℕ} (hk : 0 < k) {Ω : Opens 𝔼₂}
    (𝒯 : Triangulation Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    FiniteDimensional ℝ (𝒯.polySpaceZero p k) :=
  𝒯.finiteDimensional_polySpaceZero p (isConformingElement hk 𝒯) (node_mem_closure hk)
    (nodalInterp_eval hk)

end LagrangeElement
