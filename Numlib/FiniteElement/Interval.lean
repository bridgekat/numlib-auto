/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Sobolev.Interval
import Numlib.Approximation.SobolevInterpolation
import Numlib.Approximation.Spline
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz
import Numlib.Variational.EllipticInterval

/-!
# Lagrange finite elements on an interval

This file studies the finite element spaces of continuous piecewise polynomials on an interval,
which are the trial and test spaces of the finite element method for a two-point boundary value
problem ((8.22) and (12.57) of [quarteroni2000numerical]). Let $a = x_0 < x_1 < \dots < x_n = b$ be
a partition of $[a, b]$ into $n \ge 1$ panels $[x_k, x_{k+1}]$ of lengths $h_k = x_{k+1} - x_k$. The
space $X_h^k$ consists of the elements of $H^1(a, b)$ whose continuous representative is a
polynomial of degree at most $k$ on each panel, and $X_h^{k,0}$ consists of the elements of $X_h^k$
that vanish at $a$ and $b$. The file constructs the hat functions $\varphi_i$, which form the nodal
basis of $X_h^1$, computes the stiffness and mass matrices that they produce, and shows that on a
uniform mesh the Galerkin method is the centred difference scheme. It also constructs the nodal
basis of $X_h^2$ from the shape functions (12.63)–(12.64), and proves the interpolation estimates
$|u - \Pi_h^k u|_{H^1} \le h^k |u|_{H^{k+1}}$ for $k = 1, 2$ (Theorem 8.3 of
[quarteroni2000numerical]).

There is one space, not three. `Spline.splineSpace a b n x k 0` in `Numlib.Approximation.Spline` is
the space of continuous piecewise polynomials, as a subspace of $C([a, b])$.
`FiniteElement.lagrangeSpace` is its preimage under the embedding
$H^1(a, b) \hookrightarrow C([a, b])$ (`SobolevInterval.toContinuousMap`), and the embedding
restricts to a linear isomorphism between the two (`FiniteElement.lagrangeSpaceEquiv`). The
embedding is injective because a continuous function determines its $L^2$ class and the weak
derivative is determined by the function. Its image is all of `Spline.splineSpace`, because a
continuous piecewise polynomial is piecewise $C^1$ with bounded derivative, hence in $H^1(a, b)$
(`memSobolevInterval_of_piecewise_contDiffOn`). So every fact about one space transfers to the
other, and $\dim X_h^k = nk + 1$ follows from `Spline.finrank_splineSpace`.

## Main definitions

* `FiniteElement.meshSize`: the mesh size $h = \max_k (x_{k+1} - x_k)$.
* `FiniteElement.lagrangeSpace`, `FiniteElement.lagrangeSpaceZero`: the spaces $X_h^k$ and
  $X_h^{k,0}$ inside $H^1(a, b)$.
* `FiniteElement.lagrangeSpaceEquiv`: the isomorphism of $X_h^k$ with `Spline.splineSpace`.
* `FiniteElement.hatFun`, `FiniteElement.hatDerivFun`: the hat function (12.61) and its weak
  derivative, as functions $\mathbb{R} \to \mathbb{R}$.
* `FiniteElement.hatFunction`: the hat function as an element of $H^1(a, b)$.
  `FiniteElement.hatBasis` and `FiniteElement.hatBasisZero` are the bases of $X_h^1$ and $X_h^{1,0}$
  that the hat functions form.
* `FiniteElement.affineMap`, `FiniteElement.referenceHat`, `FiniteElement.referenceQuadratic`,
  `FiniteElement.referenceHierarchical`: the reference element (12.62), (12.65), (12.66).
* `FiniteElement.evenNodes`, `FiniteElement.quadShapeFun`, `FiniteElement.quadraticShape`: the
  element partition of a quadratic mesh $x_0 < x_1 < \dots < x_{2n}$, and the shape functions
  (12.63)–(12.64) as functions and as elements of $H^1(a, b)$. `FiniteElement.quadraticBasis` is the
  nodal basis of $X_h^2$ that they form.
* `FiniteElement.stiffnessMatrix`, `FiniteElement.massMatrix`: the matrix $A_{fe}$ of (12.48) and
  the matrix $M$ of (13.14) of a family of trial functions.
* `FiniteElement.lagrangeInterp`, `FiniteElement.quadraticInterp`: the nodal interpolation operators
  $\Pi_h^1$ and $\Pi_h^2$ as maps $H^1(a, b) \to H^1(a, b)$. `FiniteElement.quadElemPoly` is the
  local Lagrange polynomial of one quadratic element.

## Main results

* `FiniteElement.exists_mem_lagrangeSpace`: every continuous piecewise polynomial is the continuous
  representative of an element of $H^1(a, b)$.
* `FiniteElement.lagrangeSpace_eq_map_splineSpace`: an element of $H^1(a, b)$ lies in $X_h^k$ if and
  only if its continuous representative lies in the spline space.
* `FiniteElement.finrank_lagrangeSpace`: $\dim X_h^k = nk + 1$.
  `FiniteElement.finrank_lagrangeSpaceZero_one`: $\dim X_h^{1,0} = n - 1$.
* `FiniteElement.rep_hatFunction_node`: $\varphi_i(x_j) = \delta_{ij}$.
* `FiniteElement.hasWeakDerivOn_hatFun`: the weak derivative of $\varphi_i$ is $1/h_{i-1}$ and
  $-1/h_i$ on the two adjacent panels.
* `FiniteElement.eq_sum_hatFunction`: $v_h = \sum_i v_h(x_i)\, \varphi_i$ for $v_h \in X_h^1$.
* `FiniteElement.stiffnessMatrix_eq_zero_of_lt`, `FiniteElement.isTridiagonal_stiffnessMatrix`: the
  stiffness matrix of the hat functions is tridiagonal.
* `FiniteElement.stiffnessMatrix_uniform_eq`, `FiniteElement.massMatrix_uniform_eq`: on a uniform
  mesh with constant coefficients, $A_{fe} = (\varepsilon/h) \operatorname{tridiag}(-1, 2, -1) +
  (\beta/2) \operatorname{tridiag}(-1, 0, 1) + (\gamma h/6) \operatorname{tridiag}(1, 4, 1)$ and
  $M = (h/6) \operatorname{tridiag}(1, 4, 1)$.
* `FiniteElement.stiffnessMatrix_posDef`: the stiffness matrix of a symmetric coercive form is
  positive definite.
* `FiniteElement.condNumber_stiffnessMatrix_model`: for the model problem $-u'' = f$ on a uniform
  mesh, $K_2(A_{fe}) = \cot^2(\pi/(2n))$.
* `FiniteElement.galerkin_iff_centredScheme`: the Galerkin system for $X_h^1$ on a uniform mesh is
  the centred difference scheme (12.75).
* `FiniteElement.rep_quadraticShape_node`, `FiniteElement.rep_quadraticShape_eq_zero_of_panel`: the
  quadratic shape functions satisfy $\varphi_i(x_j) = \delta_{ij}$ and have local support.
* `FiniteElement.rep_quadraticShape_eq_referenceQuadratic`: when the interior nodes are the
  midpoints, the quadratic shape functions are the images of (12.65) under the affine map (12.62).
* `FiniteElement.seminorm_sub_lagrangeInterp_le`, `FiniteElement.seminorm_sub_quadraticInterp_le`:
  $|u - \Pi_h^k u|_{H^1} \le h^k |u|_{H^{k+1}}$ for $k = 1$ and $k = 2$.

## Implementation notes

* A partition is a sequence `x : ℕ → ℝ` with `IsIntervalPartition a b n x`. A quadratic mesh is a
  partition into $2n$ panels, `IsIntervalPartition a b (2 * n) x`, whose even-indexed nodes are the
  element endpoints.
* The hat functions and the quadratic shape functions are first built as functions
  $\mathbb{R} \to \mathbb{R}$ and only then made elements of $H^1(a, b)$. The sectioning comments
  below describe the two constructions.
* `FiniteElement.hatFunction` is assembled with `SobolevInterval.mk` from the $L^2$ classes of the
  function and of its weak derivative, not through an existence statement, so that both components
  are available definitionally for the stiffness and mass integrals.
* The bilinear form is `EllipticInterval.form`, $a(u, v) = \int_a^b (\alpha u' v' + \beta u' v +
  \gamma u v)$ with coefficients in $L^\infty(a, b)$. Constant coefficients are
  `EllipticInterval.constLinf`.
-/

open Set MeasureTheory intervalIntegral

namespace FiniteElement

variable {a b : ℝ}

/-! ### The mesh -/

/-- **The mesh size** of a partition $x_0, \dots, x_n$: $$h = \max_{0 \le j < n} (x_{j+1} - x_j),$$
the $h$ of the finite element spaces $X_h^k$ (§12.4.5 of [quarteroni2000numerical]).

The maximum is taken together with $0$, so the mesh size of the empty partition $n = 0$ is $0$. -/
noncomputable def meshSize (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  (Finset.range n).fold max 0 fun j ↦ x (j + 1) - x j

/-- The mesh size is nonnegative. -/
theorem meshSize_nonneg (n : ℕ) (x : ℕ → ℝ) : 0 ≤ meshSize n x :=
  (Finset.le_fold_max _).2 (Or.inl le_rfl)

/-- Every panel length $x_{j+1} - x_j$, $j < n$, is at most the mesh size. -/
theorem sub_le_meshSize {n : ℕ} (x : ℕ → ℝ) {j : ℕ} (hj : j < n) :
    x (j + 1) - x j ≤ meshSize n x :=
  (Finset.le_fold_max _).2 (Or.inr ⟨j, Finset.mem_range.2 hj, le_rfl⟩)

/-! ### The finite element spaces -/

/-- **The finite element space $X_h^k$** of (8.22) of [quarteroni2000numerical], inside $H^1(a, b)$.
Let $a < b$, and let $x_0, \dots, x_n$ be nodes. Then $X_h^k$ consists of the $u \in H^1(a, b)$
whose continuous representative is a continuous piecewise polynomial of degree at most $k$ on
the panels $[x_j, x_{j+1}]$.

It is the preimage of `Spline.splineSpace a b n x k 0` under `SobolevInterval.toContinuousMap`. -/
noncomputable def lagrangeSpace (hab : a < b) (n : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    Submodule ℝ (SobolevInterval 1 a b) :=
  Submodule.comap (SobolevInterval.toContinuousMap hab).toLinearMap
    (Spline.splineSpace a b n x k 0)

/-- An element $u \in H^1(a, b)$ lies in $X_h^k$ if and only if its continuous representative lies
in `Spline.splineSpace a b n x k 0`. -/
theorem mem_lagrangeSpace_iff {hab : a < b} {n k : ℕ} {x : ℕ → ℝ}
    {u : SobolevInterval 1 a b} :
    u ∈ lagrangeSpace hab n x k ↔
      SobolevInterval.toContinuousMap hab u ∈ Spline.splineSpace a b n x k 0 := Iff.rfl

/-- **The finite element space $X_h^{k,0}$** of (12.57) of [quarteroni2000numerical]: the
intersection of $X_h^k$ with $H^1_0(a, b)$, that is, the $v_h \in X_h^k$ with
$v_h(a) = v_h(b) = 0$. -/
noncomputable def lagrangeSpaceZero (hab : a < b) (n : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    Submodule ℝ (SobolevInterval 1 a b) :=
  lagrangeSpace hab n x k ⊓ SobolevIntervalZero a b

/-- The space $X_h^{k,0}$ is contained in $H^1_0(a, b)$. -/
theorem lagrangeSpaceZero_le_sobolevIntervalZero (hab : a < b) (n : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    lagrangeSpaceZero hab n x k ≤ SobolevIntervalZero a b := inf_le_right

/-- The space $X_h^{k,0}$ is contained in $X_h^k$. -/
theorem lagrangeSpaceZero_le_lagrangeSpace (hab : a < b) (n : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    lagrangeSpaceZero hab n x k ≤ lagrangeSpace hab n x k := inf_le_left

/-- An element $u \in H^1(a, b)$ lies in $X_h^{k,0}$ if and only if $u \in X_h^k$ and its continuous
representative vanishes at $a$ and at $b$. This is (12.57) of [quarteroni2000numerical]
unfolded. -/
theorem mem_lagrangeSpaceZero_iff (hab : a < b) (n : ℕ) (x : ℕ → ℝ) (k : ℕ)
    (u : SobolevInterval 1 a b) :
    u ∈ lagrangeSpaceZero hab n x k ↔ u ∈ lagrangeSpace hab n x k ∧
      SobolevInterval.toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩ = 0 ∧
      SobolevInterval.toContinuousMap hab u ⟨b, right_mem_Icc.2 hab.le⟩ = 0 :=
  Submodule.mem_inf.trans (and_congr_right' (mem_sobolevIntervalZero_iff hab u))

/-! ### The bridge to the spline space -/

/-- **Every continuous piecewise polynomial lies in $H^1(a, b)$.** Let $a = x_0 < \dots < x_n = b$
be a partition with $n \ge 1$, and let $f \in C([a, b])$ be a polynomial of degree at most $k$
on each panel. Then there is $u \in H^1(a, b)$ whose continuous representative is $f$. In
particular $u \in X_h^k$.

The proof applies `memSobolevInterval_of_piecewise_contDiffOn` panel by panel, with the
derivatives of the panel polynomials as panel derivatives. -/
theorem exists_mem_lagrangeSpace {n k : ℕ} {x : ℕ → ℝ} (hab : a < b)
    (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    {f : C(Icc a b, ℝ)} (hf : f ∈ Spline.splineSpace a b n x k 0) :
    ∃ u : SobolevInterval 1 a b, SobolevInterval.toContinuousMap hab u = f := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  obtain ⟨g, hg0, hfg, hp⟩ := hf
  have hgcont : ContinuousOn g (Icc a b) := hg0.continuousOn
  set P : Fin (N + 1) → Polynomial ℝ := fun j ↦ (hp (j : ℕ) j.isLt).choose with hP
  have hPe : ∀ j : Fin (N + 1),
      EqOn g (P j).eval (Icc (x (j : ℕ)) (x ((j : ℕ) + 1))) :=
    fun j ↦ (hp (j : ℕ) j.isLt).choose_spec.2
  set y : Fin (N + 2) → ℝ := fun j ↦ x (j : ℕ) with hy
  have hsub : ∀ j : Fin (N + 1), Ioo (y j.castSucc) (y j.succ)
      ⊆ Icc (x (j : ℕ)) (x ((j : ℕ) + 1)) := fun j ↦ by
    simp only [hy, Fin.val_castSucc, Fin.val_succ]
    exact Ioo_subset_Icc_self
  have hsubI : ∀ j : Fin (N + 1), Icc (x (j : ℕ)) (x ((j : ℕ) + 1)) ⊆ Icc a b :=
    fun j ↦ hx.Icc_subset j.isLt
  have hymono : StrictMono y := fun i j hij ↦
    hx.lt (Fin.lt_def.1 hij) (by omega)
  have hy0 : y 0 = a := by simpa [hy] using hx.first
  have hylast : y (Fin.last (N + 1)) = b := by simpa [hy] using hx.last
  have hg' : ∀ j : Fin (N + 1), ContDiffOn ℝ 1 g (Ioo (y j.castSucc) (y j.succ)) := fun j ↦
    ((P j).contDiff_eval 1).contDiffOn.congr fun t ht ↦ hPe j (hsub j ht)
  have hCbdd : ∀ j : Fin (N + 1),
      BddAbove ((fun s ↦ |(P j).derivative.eval s|) '' Icc a b) := fun j ↦
    (isCompact_Icc.image_of_continuousOn
      (((P j).derivative.contDiff_eval 0).continuous.continuousOn.abs)).bddAbove
  set C : Fin (N + 1) → ℝ := fun j ↦ sSup ((fun s ↦ |(P j).derivative.eval s|) '' Icc a b) with hC
  have hbdd : ∃ D, ∀ j : Fin (N + 1), ∀ t ∈ Ioo (y j.castSucc) (y j.succ), |deriv g t| ≤ D := by
    refine ⟨Finset.univ.sup' Finset.univ_nonempty C, fun j t ht ↦ ?_⟩
    have hev : g =ᶠ[nhds t] fun s ↦ (P j).eval s :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs ↦ hPe j (hsub j hs)
    rw [hev.deriv_eq, Polynomial.deriv]
    exact (le_csSup (hCbdd j) (mem_image_of_mem _ (hsubI j (hsub j ht)))).trans
      (Finset.le_sup' C (Finset.mem_univ j))
  obtain ⟨hmem, -⟩ :=
    memSobolevInterval_of_piecewise_contDiffOn hymono hy0 hylast hgcont hg' hbdd
  obtain ⟨u, hu⟩ := SobolevInterval.exists_toContinuousMap_eq hab hgcont hmem
  exact ⟨u, ContinuousMap.ext fun t ↦ (hu t).trans (hfg t).symm⟩

/-- **$X_h^k$ is the spline space read inside $H^1(a, b)$.** Let $a < b$. An element
$u \in H^1(a, b)$ lies in $X_h^k$ if and only if its continuous representative is a continuous
piecewise polynomial of degree at most $k$, that is, an element of
`Spline.splineSpace a b n x k 0`.

`Spline.splineSpace` is the definition of the continuous piecewise polynomials, and
`FiniteElement.lagrangeSpace` is its copy inside $H^1(a, b)$ that the Galerkin theory needs. The
two are identified by `FiniteElement.lagrangeSpaceEquiv`. -/
theorem lagrangeSpace_eq_map_splineSpace (hab : a < b) {n k : ℕ} {x : ℕ → ℝ}
    {u : SobolevInterval 1 a b} :
    u ∈ lagrangeSpace hab n x k ↔
      ∃ f ∈ Spline.splineSpace a b n x k 0, SobolevInterval.toContinuousMap hab u = f :=
  ⟨fun h ↦ ⟨_, h, rfl⟩, fun ⟨_, hf, hu⟩ ↦ by rw [mem_lagrangeSpace_iff, hu]; exact hf⟩

/-- The embedding $H^1(a, b) \hookrightarrow C([a, b])$, restricted to $X_h^k$, as a linear map into
the spline space. -/
noncomputable def toSplineSpace (hab : a < b) (n : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    lagrangeSpace hab n x k →ₗ[ℝ] Spline.splineSpace a b n x k 0 :=
  (SobolevInterval.toContinuousMap hab).toLinearMap.restrict fun _ hu ↦ hu

/-- The linear map `FiniteElement.toSplineSpace` sends $u \in X_h^k$ to its continuous
representative. -/
@[simp]
theorem coe_toSplineSpace (hab : a < b) {n k : ℕ} {x : ℕ → ℝ} (u : lagrangeSpace hab n x k) :
    (toSplineSpace hab n x k u : C(Icc a b, ℝ))
      = SobolevInterval.toContinuousMap hab (u : SobolevInterval 1 a b) := rfl

/-- **$X_h^k$ and the spline space are isomorphic.** Let $a = x_0 < \dots < x_n = b$ be a partition
with $n \ge 1$. The embedding $H^1(a, b) \hookrightarrow C([a, b])$, restricted to $X_h^k$, is a
linear isomorphism onto `Spline.splineSpace a b n x k 0`.

Injectivity is `SobolevInterval.toContinuousMap_injective`, and surjectivity is
`FiniteElement.exists_mem_lagrangeSpace`. -/
noncomputable def lagrangeSpaceEquiv {n : ℕ} {x : ℕ → ℝ} (hab : a < b)
    (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) (k : ℕ) :
    lagrangeSpace hab n x k ≃ₗ[ℝ] Spline.splineSpace a b n x k 0 :=
  LinearEquiv.ofBijective (toSplineSpace hab n x k)
    ⟨fun u v huv ↦
        Subtype.ext (SobolevInterval.toContinuousMap_injective hab (congrArg Subtype.val huv)),
      fun f ↦ by
        obtain ⟨u, hu⟩ := exists_mem_lagrangeSpace hab hx hn f.2
        exact ⟨⟨u, by rw [mem_lagrangeSpace_iff, hu]; exact f.2⟩, Subtype.ext hu⟩⟩

/-- **The dimension of $X_h^k$.** Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$.
Then $$\dim X_h^k = nk + 1,$$ the number of nodal values of a continuous piecewise polynomial of
degree $k$ on $n$ panels (§12.4.5 of [quarteroni2000numerical]).

The proof transports `Spline.finrank_splineSpace` at smoothness $r = 0$ by
`FiniteElement.lagrangeSpaceEquiv`. -/
theorem finrank_lagrangeSpace {n : ℕ} {x : ℕ → ℝ} (hab : a < b)
    (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) (k : ℕ) :
    Module.finrank ℝ (lagrangeSpace hab n x k) = n * k + 1 := by
  rw [(lagrangeSpaceEquiv hab hx hn k).finrank_eq, Spline.finrank_splineSpace hx hn (Nat.zero_le k)]
  simp

/-- For a partition with $n \ge 1$, the space $X_h^k$ is finite-dimensional. -/
theorem finiteDimensional_lagrangeSpace {n : ℕ} {x : ℕ → ℝ} (hab : a < b)
    (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) (k : ℕ) :
    FiniteDimensional ℝ (lagrangeSpace hab n x k) := by
  have h : FiniteDimensional ℝ (Spline.splineSpace a b n x k 0) :=
    Spline.finiteDimensional_splineSpace hx hn
  exact (lagrangeSpaceEquiv hab hx hn k).symm.finiteDimensional

/-!
### The hat functions of $X_h^1$

The shape functions of (12.61) of [quarteroni2000numerical] are first built as functions
$\mathbb{R} \to \mathbb{R}$ and only then made elements of $H^1(a, b)$. Let $R_j$ be the normalized
ramp of the panel $[x_j, x_{j+1}]$: zero to the left of $x_j$, rising linearly to $1$ at $x_{j+1}$,
and constant afterwards. With $R_{-1} = 1$ and $R_j = 0$ for $j \ge n$, the hat function at the node
$i$ is the difference $R_{i-1} - R_i$, for every $i$ at once, endpoints included; this is
`FiniteElement.hatStep` and `FiniteElement.hatFun`. Its derivative is the difference of the two
panel indicators, `FiniteElement.hatDerivFun`. The two are related by
`FiniteElement.hasWeakDerivOn_hatFun`, which is `memSobolevInterval_of_piecewise_contDiffOn` (a
continuous piecewise $C^1$ function lies in $H^1$) followed by the identification of the classical
derivative off the nodes.
-/

/-- The **normalized ramp** of the panel $[x_j, x_{j+1}]$: $$R_j(t) = \frac{\min(\max(t - x_j, 0),\
x_{j+1} - x_j)}{x_{j+1} - x_j}.$$ For $x_j < x_{j+1}$ it is $0$ to the left of $x_j$, affine on
the panel, and $1$ to the right of $x_{j+1}$. The hat functions of (12.61) of
[quarteroni2000numerical] are the differences of consecutive ramps. -/
noncomputable def rampFun (x : ℕ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun t ↦ min (max (t - x j) 0) (x (j + 1) - x j) / (x (j + 1) - x j)

/-- The normalized ramp is continuous, for any sequence of nodes. -/
theorem continuous_rampFun (x : ℕ → ℝ) (j : ℕ) : Continuous (rampFun x j) :=
  (((continuous_id.sub continuous_const).max continuous_const).min continuous_const).div_const _

/-- If $x_j \le x_{j+1}$, the normalized ramp $R_j$ vanishes at every $t \le x_j$. -/
theorem rampFun_of_le_left {x : ℕ → ℝ} {j : ℕ} {t : ℝ} (hx : x j ≤ x (j + 1)) (ht : t ≤ x j) :
    rampFun x j t = 0 := by
  rw [rampFun, max_eq_right (by linarith), min_eq_left (by linarith), zero_div]

/-- On its panel the normalized ramp is affine: $R_j(t) = (t - x_j)/(x_{j+1} - x_j)$ for
$x_j \le t \le x_{j+1}$. -/
theorem rampFun_of_mem {x : ℕ → ℝ} {j : ℕ} {t : ℝ} (h1 : x j ≤ t) (h2 : t ≤ x (j + 1)) :
    rampFun x j t = (t - x j) / (x (j + 1) - x j) := by
  rw [rampFun, max_eq_left (by linarith), min_eq_left (by linarith)]

/-- If $x_j < x_{j+1}$, the normalized ramp $R_j$ equals $1$ at every $t \ge x_{j+1}$. -/
theorem rampFun_of_right_le {x : ℕ → ℝ} {j : ℕ} {t : ℝ} (hx : x j < x (j + 1))
    (ht : x (j + 1) ≤ t) : rampFun x j t = 1 := by
  rw [rampFun, max_eq_left (by linarith), min_eq_right (by linarith), div_self (by linarith)]

/-- The **staircase** $R_{i-1}$ of the partition: the constant $1$ for $i = 0$, the normalized ramp
of the panel $[x_{i-1}, x_i]$ for $1 \le i \le n$, and the constant $0$ for $i > n$. The hat
function at the node $i$ is the difference of the staircases at $i$ and $i + 1$. -/
noncomputable def hatStep (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : ℝ → ℝ :=
  if i = 0 then fun _ ↦ 1 else if i ≤ n then rampFun x (i - 1) else fun _ ↦ 0

/-- **The hat function** $\varphi_i$ of (12.61) of [quarteroni2000numerical], as a function
$\mathbb{R} \to \mathbb{R}$. On a partition $x_0 < \dots < x_n$ it is the continuous piecewise
linear function with $\varphi_i(x_i) = 1$ and $\varphi_i(x_j) = 0$ for $j \ne i$:
$$\varphi_i(t) = \begin{cases}
  (t - x_{i-1})/(x_i - x_{i-1}) & \text{on } [x_{i-1}, x_i], \\
  (x_{i+1} - t)/(x_{i+1} - x_i) & \text{on } [x_i, x_{i+1}], \\
  0 & \text{elsewhere in } [x_0, x_n].
\end{cases}$$

It is defined as the difference of the staircases `FiniteElement.hatStep` at $i$ and $i + 1$.
This formula also gives the end functions $\varphi_0$ and $\varphi_n$, which have one branch
only, and gives $\varphi_i = 0$ for $i > n$. Outside $[x_0, x_n]$ the function $\varphi_0$ is
$1$ to the left and $\varphi_n$ is $1$ to the right. -/
noncomputable def hatFun (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : ℝ → ℝ :=
  fun t ↦ hatStep n x i t - hatStep n x (i + 1) t

/-- The staircase at $i = 0$ is the constant $1$. -/
@[simp]
theorem hatStep_zero (n : ℕ) (x : ℕ → ℝ) : hatStep n x 0 = fun _ ↦ 1 := by
  rw [hatStep]; simp

/-- For $1 \le i \le n$, the staircase at $i$ is the normalized ramp of the panel $[x_{i-1}, x_i]$.
-/
theorem hatStep_of_mem {n : ℕ} (x : ℕ → ℝ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ n) :
    hatStep n x i = rampFun x (i - 1) := by
  rw [hatStep]; split_ifs <;> first | rfl | omega

/-- For $i > n$, the staircase at $i$ is the constant $0$. -/
theorem hatStep_of_lt {n : ℕ} (x : ℕ → ℝ) {i : ℕ} (h : n < i) : hatStep n x i = fun _ ↦ 0 := by
  rw [hatStep]; split_ifs <;> first | rfl | omega

/-- The staircase is continuous. -/
theorem continuous_hatStep (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : Continuous (hatStep n x i) := by
  rw [hatStep]
  split_ifs
  · exact continuous_const
  · exact continuous_rampFun x _
  · exact continuous_const

/-- The hat function is continuous. -/
theorem continuous_hatFun (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : Continuous (hatFun n x i) :=
  (continuous_hatStep n x i).sub (continuous_hatStep n x (i + 1))

section Partition

variable {n : ℕ} {x : ℕ → ℝ}

/-- Let $x_0 < \dots < x_n$ be a partition of $[a, b]$, let $k < n$ and $i \le k$. Then the
staircase at $i$ equals $1$ at every $t \ge x_k$. -/
theorem hatStep_eq_one (hx : IsIntervalPartition a b n x) {k i : ℕ} (hk : k < n) (hi : i ≤ k)
    {t : ℝ} (ht : x k ≤ t) : hatStep n x i t = 1 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  · simp
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [hatStep_of_mem x (by omega) (by omega)]
    simp only [Nat.add_sub_cancel]
    exact rampFun_of_right_le (hx.lt (by omega) (by omega))
      ((hx.mono (by omega) (by omega)).trans ht)

/-- Let $x_0 < \dots < x_n$ be a partition of $[a, b]$ and let $i \ge k + 2$. Then the staircase at
$i$ vanishes at every $t \le x_{k+1}$. -/
theorem hatStep_eq_zero (hx : IsIntervalPartition a b n x) {k i : ℕ} (hi : k + 2 ≤ i)
    {t : ℝ} (ht : t ≤ x (k + 1)) : hatStep n x i t = 0 := by
  rcases lt_or_ge n i with h | h
  · rw [hatStep_of_lt x h]
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [hatStep_of_mem x (by omega) (by omega)]
    simp only [Nat.add_sub_cancel]
    exact rampFun_of_le_left (hx.mono (by omega) (by omega))
      (ht.trans (hx.mono (by omega) (by omega)))

/-- **The descending branch of the hat function.** For a partition of $[a, b]$ and $k < n$,
$$\varphi_k(t) = \frac{x_{k+1} - t}{x_{k+1} - x_k} \quad \text{for } x_k \le t \le x_{k+1}.$$
-/
theorem hatFun_eq_of_left (hx : IsIntervalPartition a b n x) {k : ℕ} (hk : k < n) {t : ℝ}
    (h1 : x k ≤ t) (h2 : t ≤ x (k + 1)) :
    hatFun n x k t = (x (k + 1) - t) / (x (k + 1) - x k) := by
  have hlt := hx.step k hk
  rw [hatFun, hatStep_eq_one hx hk le_rfl h1, hatStep_of_mem x (by omega) (by omega)]
  simp only [Nat.add_sub_cancel]
  rw [rampFun_of_mem h1 h2]
  have hne : x (k + 1) - x k ≠ 0 := by linarith
  field_simp
  ring

/-- **The ascending branch of the hat function.** For a partition of $[a, b]$ and $k < n$,
$$\varphi_{k+1}(t) = \frac{t - x_k}{x_{k+1} - x_k} \quad \text{for } x_k \le t \le x_{k+1}.$$
-/
theorem hatFun_eq_of_right (hx : IsIntervalPartition a b n x) {k : ℕ} (hk : k < n) {t : ℝ}
    (h1 : x k ≤ t) (h2 : t ≤ x (k + 1)) :
    hatFun n x (k + 1) t = (t - x k) / (x (k + 1) - x k) := by
  have hkn : k + 1 ≤ n := hk
  rw [hatFun, hatStep_of_mem x (by omega) hkn, hatStep_eq_zero hx (by omega) h2]
  simp only [Nat.add_sub_cancel]
  rw [rampFun_of_mem h1 h2, sub_zero]

/-- **The local support of the hat functions** (§12.4.5 of [quarteroni2000numerical]). For a
partition of $[a, b]$, $k < n$ and $i \notin \{k, k + 1\}$, the hat function $\varphi_i$
vanishes on the panel $[x_k, x_{k+1}]$. -/
theorem hatFun_eq_zero_of_panel (hx : IsIntervalPartition a b n x) {k i : ℕ} (hk : k < n)
    (h1 : i ≠ k) (h2 : i ≠ k + 1) {t : ℝ} (ht1 : x k ≤ t) (ht2 : t ≤ x (k + 1)) :
    hatFun n x i t = 0 := by
  rcases lt_or_gt_of_ne h1 with h | h
  · rw [hatFun, hatStep_eq_one hx hk (by omega) ht1, hatStep_eq_one hx hk (by omega) ht1, sub_self]
  · rw [hatFun, hatStep_eq_zero hx (by omega) ht2, hatStep_eq_zero hx (by omega) ht2, sub_self]

/-- **The Lagrange interpolation property** of (12.61) of [quarteroni2000numerical]. For a partition
of $[a, b]$ with $n \ge 1$, every index $i$ and every $j \le n$, $$\varphi_i(x_j) =
\delta_{ij}.$$
-/
theorem hatFun_apply_node (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) {i j : ℕ} (hj : j ≤ n) :
    hatFun n x i (x j) = if i = j then 1 else 0 := by
  rcases lt_or_ge j n with hjn | hjn
  · have hlt := hx.step j hjn
    by_cases hij : i = j
    · subst hij
      rw [hatFun_eq_of_left hx hjn le_rfl hlt.le, div_self (by linarith)]
      simp
    · rcases eq_or_ne i (j + 1) with rfl | hij'
      · rw [hatFun_eq_of_right hx hjn le_rfl hlt.le, sub_self, zero_div]
        simp
      · rw [hatFun_eq_zero_of_panel hx hjn hij hij' le_rfl hlt.le]
        simp [hij]
  · obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    subst hm
    obtain rfl : j = m + 1 := le_antisymm hj hjn
    have hlt := hx.step m (by omega)
    by_cases hij : i = m + 1
    · subst hij
      rw [hatFun_eq_of_right hx (by omega) hlt.le le_rfl, div_self (by linarith)]
      simp
    · rcases eq_or_ne i m with rfl | hij'
      · rw [hatFun_eq_of_left hx (by omega) hlt.le le_rfl, sub_self, zero_div]
        simp
      · rw [hatFun_eq_zero_of_panel hx (by omega) hij' hij hlt.le le_rfl]
        simp [hij]

end Partition

/-! ### The derivative of a hat function -/

/-- The derivative of the normalized ramp $R_j$: the function equal to $1/(x_{j+1} - x_j)$ on the
open panel $(x_j, x_{j+1})$ and $0$ elsewhere. -/
noncomputable def rampDerivFun (x : ℕ → ℝ) (j : ℕ) : ℝ → ℝ :=
  (Ioo (x j) (x (j + 1))).indicator fun _ ↦ (x (j + 1) - x j)⁻¹

/-- The derivative of the staircase `FiniteElement.hatStep`: $0$ for $i = 0$, the derivative of the
normalized ramp of the panel $[x_{i-1}, x_i]$ for $1 \le i \le n$, and $0$ for $i > n$. -/
noncomputable def hatStepDeriv (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : ℝ → ℝ :=
  if i = 0 then fun _ ↦ 0 else if i ≤ n then rampDerivFun x (i - 1) else fun _ ↦ 0

/-- **The weak derivative of the hat function** $\varphi_i$, as a function
$\mathbb{R} \to \mathbb{R}$: $1/h_{i-1}$ on the panel $(x_{i-1}, x_i)$, $-1/h_i$ on the panel
$(x_i, x_{i+1})$, and $0$ elsewhere, where $h_j = x_{j+1} - x_j$. Panels with index outside
$0, \dots, n - 1$ contribute nothing.

It is the difference of the staircase derivatives at $i$ and $i + 1$.
`FiniteElement.hasWeakDerivOn_hatFun` proves that it is the weak derivative of
`FiniteElement.hatFun`. -/
noncomputable def hatDerivFun (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : ℝ → ℝ :=
  fun t ↦ hatStepDeriv n x i t - hatStepDeriv n x (i + 1) t

/-- The derivative of the normalized ramp is measurable. -/
theorem measurable_rampDerivFun (x : ℕ → ℝ) (j : ℕ) : Measurable (rampDerivFun x j) :=
  measurable_const.indicator measurableSet_Ioo

/-- The derivative of the staircase is measurable. -/
theorem measurable_hatStepDeriv (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : Measurable (hatStepDeriv n x i) := by
  rw [hatStepDeriv]
  split_ifs
  · exact measurable_const
  · exact measurable_rampDerivFun x _
  · exact measurable_const

/-- The derivative of the hat function is measurable. -/
theorem measurable_hatDerivFun (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : Measurable (hatDerivFun n x i) :=
  (measurable_hatStepDeriv n x i).sub (measurable_hatStepDeriv n x (i + 1))

/-- On the open panel $(x_j, x_{j+1})$ the derivative of the normalized ramp is $1/(x_{j+1} - x_j)$.
-/
theorem rampDerivFun_of_mem {x : ℕ → ℝ} {j : ℕ} {t : ℝ} (ht : t ∈ Ioo (x j) (x (j + 1))) :
    rampDerivFun x j t = (x (j + 1) - x j)⁻¹ := indicator_of_mem ht _

/-- Outside the open panel $(x_j, x_{j+1})$ the derivative of the normalized ramp vanishes. -/
theorem rampDerivFun_of_notMem {x : ℕ → ℝ} {j : ℕ} {t : ℝ} (ht : t ∉ Ioo (x j) (x (j + 1))) :
    rampDerivFun x j t = 0 := indicator_of_notMem ht _

/-- For $1 \le i \le n$, the derivative of the staircase at $i$ is the derivative of the normalized
ramp of the panel $[x_{i-1}, x_i]$. -/
theorem hatStepDeriv_of_mem {n : ℕ} (x : ℕ → ℝ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ n) :
    hatStepDeriv n x i = rampDerivFun x (i - 1) := by
  rw [hatStepDeriv]; split_ifs <;> first | rfl | omega

/-- The derivative of the staircase at $i$ is bounded in absolute value by $|1/(x_i - x_{i-1})|$.
For $i = 0$ the bound is $0$, because the division by zero gives $0$. -/
theorem abs_hatStepDeriv_le (n : ℕ) (x : ℕ → ℝ) (i : ℕ) (t : ℝ) :
    |hatStepDeriv n x i t| ≤ |(x i - x (i - 1))⁻¹| := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [hatStepDeriv]
  rcases lt_or_ge n i with h | h
  · rw [hatStepDeriv]
    split_ifs with h1 h2
    · simp
    · omega
    · simp
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [hatStepDeriv_of_mem x (by omega) h]
    simp only [Nat.add_sub_cancel, rampDerivFun]
    by_cases ht : t ∈ Ioo (x i') (x (i' + 1))
    · rw [indicator_of_mem ht]
    · rw [indicator_of_notMem ht, abs_zero]
      exact abs_nonneg _

/-- The bound $|1/(x_i - x_{i-1})| + |1/(x_{i+1} - x_i)|$ on the derivative of the hat function
$\varphi_i$. -/
noncomputable def hatBound (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  |(x i - x (i - 1))⁻¹| + |(x (i + 1) - x i)⁻¹|

/-- The derivative of the hat function $\varphi_i$ is bounded in absolute value by
`FiniteElement.hatBound`, that is, by $|1/(x_i - x_{i-1})| + |1/(x_{i+1} - x_i)|$. -/
theorem abs_hatDerivFun_le (n : ℕ) (x : ℕ → ℝ) (i : ℕ) (t : ℝ) :
    |hatDerivFun n x i t| ≤ hatBound x i := by
  refine (abs_sub _ _).trans ?_
  have h1 := abs_hatStepDeriv_le n x i t
  have h2 := abs_hatStepDeriv_le n x (i + 1) t
  simp only [Nat.add_sub_cancel] at h2
  exact add_le_add h1 h2

/-- The hat function lies in $L^2(a, b)$, because it is continuous and bounded on the bounded
interval. -/
theorem memLp_hatFun (n : ℕ) (x : ℕ → ℝ) (i : ℕ) :
    MemLp (hatFun n x i) 2 (volume.restrict (Ioo a b)) :=
  ContinuousOn.memLp_two_restrict_Ioo (a := a) (b := b) (continuous_hatFun n x i).continuousOn

/-- The derivative of the hat function lies in $L^2(a, b)$, because it is measurable and bounded. -/
theorem memLp_hatDerivFun (n : ℕ) (x : ℕ → ℝ) (i : ℕ) :
    MemLp (hatDerivFun n x i) 2 (volume.restrict (Ioo a b)) :=
  MemLp.of_bound (measurable_hatDerivFun n x i).aestronglyMeasurable (hatBound x i)
    (Filter.Eventually.of_forall fun t ↦ by
      rw [Real.norm_eq_abs]; exact abs_hatDerivFun_le n x i t)

section Partition

variable {n : ℕ} {x : ℕ → ℝ}

/-- Let $x_0 < \dots < x_n$ be a partition of $[a, b]$, let $k < n$, $j \le n$ and $j \ne k$. Then
the derivative of the normalized ramp $R_j$ vanishes on the open panel $(x_k, x_{k+1})$, because
the panels are disjoint. -/
theorem rampDerivFun_eq_zero_of_ne (hx : IsIntervalPartition a b n x) {k j : ℕ} (hk : k < n)
    (hj : j ≤ n) (hjk : j ≠ k) {t : ℝ} (ht : t ∈ Ioo (x k) (x (k + 1))) :
    rampDerivFun x j t = 0 := by
  refine rampDerivFun_of_notMem fun htj ↦ ?_
  rcases lt_or_gt_of_ne hjk with h | h
  · exact absurd ((hx.mono (by omega) (by omega) : x (j + 1) ≤ x k).trans_lt ht.1)
      (not_lt.2 htj.2.le)
  · exact absurd (ht.2.trans_le (hx.mono (by omega) hj : x (k + 1) ≤ x j)) (not_lt.2 htj.1.le)

/-- Let $x_0 < \dots < x_n$ be a partition of $[a, b]$, let $k < n$ and $i \ne k + 1$. Then the
derivative of the staircase at $i$ vanishes on the open panel $(x_k, x_{k+1})$. -/
theorem hatStepDeriv_eq_zero_of_ne (hx : IsIntervalPartition a b n x) {k i : ℕ} (hk : k < n)
    (hik : i ≠ k + 1) {t : ℝ} (ht : t ∈ Ioo (x k) (x (k + 1))) : hatStepDeriv n x i t = 0 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [hatStepDeriv]
  rcases lt_or_ge n i with h | h
  · rw [hatStepDeriv]; split_ifs with h1 h2
    · rfl
    · omega
    · rfl
  · rw [hatStepDeriv_of_mem x hi h]
    exact rampDerivFun_eq_zero_of_ne hx hk (by omega) (by omega) ht

/-- For $k < n$, the derivative of the staircase at $k + 1$ equals $1/(x_{k+1} - x_k)$ on the open
panel $(x_k, x_{k+1})$. -/
theorem hatStepDeriv_eq {n : ℕ} {x : ℕ → ℝ} {k : ℕ} (hk : k < n) {t : ℝ}
    (ht : t ∈ Ioo (x k) (x (k + 1))) :
    hatStepDeriv n x (k + 1) t = (x (k + 1) - x k)⁻¹ := by
  have hkn : k + 1 ≤ n := hk
  rw [hatStepDeriv_of_mem x (by omega) hkn]
  exact rampDerivFun_of_mem ht

/-- **The descending slope.** For a partition of $[a, b]$ and $k < n$, the derivative of $\varphi_k$
equals $-1/(x_{k+1} - x_k)$ on the open panel $(x_k, x_{k+1})$. -/
theorem hatDerivFun_eq_of_left (hx : IsIntervalPartition a b n x) {k : ℕ} (hk : k < n) {t : ℝ}
    (ht : t ∈ Ioo (x k) (x (k + 1))) :
    hatDerivFun n x k t = -(x (k + 1) - x k)⁻¹ := by
  rw [hatDerivFun, hatStepDeriv_eq_zero_of_ne hx hk (by omega) ht, hatStepDeriv_eq hk ht, zero_sub]

/-- **The ascending slope.** For a partition of $[a, b]$ and $k < n$, the derivative of
$\varphi_{k+1}$ equals $1/(x_{k+1} - x_k)$ on the open panel $(x_k, x_{k+1})$. -/
theorem hatDerivFun_eq_of_right (hx : IsIntervalPartition a b n x) {k : ℕ} (hk : k < n) {t : ℝ}
    (ht : t ∈ Ioo (x k) (x (k + 1))) :
    hatDerivFun n x (k + 1) t = (x (k + 1) - x k)⁻¹ := by
  rw [hatDerivFun, hatStepDeriv_eq hk ht, hatStepDeriv_eq_zero_of_ne hx hk (by omega) ht, sub_zero]

/-- For a partition of $[a, b]$, $k < n$ and $i \notin \{k, k + 1\}$, the derivative of $\varphi_i$
vanishes on the open panel $(x_k, x_{k+1})$. -/
theorem hatDerivFun_eq_zero_of_panel (hx : IsIntervalPartition a b n x) {k i : ℕ} (hk : k < n)
    (h1 : i ≠ k) (h2 : i ≠ k + 1) {t : ℝ} (ht : t ∈ Ioo (x k) (x (k + 1))) :
    hatDerivFun n x i t = 0 := by
  rw [hatDerivFun, hatStepDeriv_eq_zero_of_ne hx hk h2 ht,
    hatStepDeriv_eq_zero_of_ne hx hk (by omega) ht, sub_zero]

/-- For a partition of $[a, b]$ and $k < n$, every hat function $\varphi_i$ is affine on the panel
$[x_k, x_{k+1}]$: there are $c$ and $d$ with $\varphi_i(t) = ct + d$ on the closed panel, and
`FiniteElement.hatDerivFun` equals the slope $c$ on the open panel.

This one fact gives the membership in the spline space, the smoothness on the open panels, and
the identification of the classical derivative. -/
theorem exists_affine_hatFun (hx : IsIntervalPartition a b n x) {k : ℕ} (hk : k < n) (i : ℕ) :
    ∃ c d : ℝ, (∀ t ∈ Icc (x k) (x (k + 1)), hatFun n x i t = c * t + d) ∧
      ∀ t ∈ Ioo (x k) (x (k + 1)), hatDerivFun n x i t = c := by
  have hlt := hx.step k hk
  have hne : x (k + 1) - x k ≠ 0 := by linarith
  rcases eq_or_ne i k with rfl | hik
  · refine ⟨-(x (i + 1) - x i)⁻¹, x (i + 1) * (x (i + 1) - x i)⁻¹, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
    · rw [hatFun_eq_of_left hx hk ht.1 ht.2]
      field_simp
      ring
    · exact hatDerivFun_eq_of_left hx hk ht
  rcases eq_or_ne i (k + 1) with rfl | hik'
  · refine ⟨(x (k + 1) - x k)⁻¹, -(x k * (x (k + 1) - x k)⁻¹), fun t ht ↦ ?_, fun t ht ↦ ?_⟩
    · rw [hatFun_eq_of_right hx hk ht.1 ht.2]
      field_simp
      ring
    · exact hatDerivFun_eq_of_right hx hk ht
  · exact ⟨0, 0, fun t ht ↦ by
      rw [hatFun_eq_zero_of_panel hx hk hik hik' ht.1 ht.2]; ring,
      fun t ht ↦ hatDerivFun_eq_zero_of_panel hx hk hik hik' ht⟩

/-- For a partition of $[a, b]$ and $k < n$, the classical derivative of $\varphi_i$ on the open
panel $(x_k, x_{k+1})$ is `FiniteElement.hatDerivFun`. -/
theorem deriv_hatFun_eq (hx : IsIntervalPartition a b n x) {k i : ℕ} (hk : k < n) {t : ℝ}
    (ht : t ∈ Ioo (x k) (x (k + 1))) : deriv (hatFun n x i) t = hatDerivFun n x i t := by
  obtain ⟨c, d, hcd, hc⟩ := exists_affine_hatFun hx hk i
  have hev : hatFun n x i =ᶠ[nhds t] fun s ↦ c * s + d :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs ↦ hcd s (Ioo_subset_Icc_self hs)
  rw [hev.deriv_eq, hc t ht]
  simp

/-- For a partition of $[a, b]$ and $k < n$, every hat function is $C^1$ on the open panel
$(x_k, x_{k+1})$. -/
theorem contDiffOn_hatFun_panel (hx : IsIntervalPartition a b n x) {k i : ℕ} (hk : k < n) :
    ContDiffOn ℝ 1 (hatFun n x i) (Ioo (x k) (x (k + 1))) := by
  obtain ⟨c, d, hcd, -⟩ := exists_affine_hatFun hx hk i
  exact ((contDiff_const.mul contDiff_id).add contDiff_const).contDiffOn.congr
    fun t ht ↦ hcd t (Ioo_subset_Icc_self ht)

/-! ### The hat function as an element of $H^1(a, b)$ -/

/-- **Almost every point of $(a, b)$ lies inside a panel.** Let $a = x_0 < \dots < x_n = b$ be a
partition with $n \ge 1$. Then almost every $t \in (a, b)$ lies in an open panel
$(x_k, x_{k+1})$ with $k < n$, because the points outside the open panels are the finitely many
nodes. -/
theorem _root_.IsIntervalPartition.ae_mem_Ioo_panel (hx : IsIntervalPartition a b n x)
    (hn : 1 ≤ n) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∃ k < n, t ∈ Ioo (x k) (x (k + 1)) := by
  have hfin : ∀ᵐ t : ℝ, t ∉ x '' Iic n := by
    rw [ae_iff]
    have hset : {t : ℝ | ¬ t ∉ x '' Iic n} = x '' Iic n := by ext t; simp
    rw [hset]
    exact ((Set.finite_Iic n).image x).measure_zero volume
  refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
  filter_upwards [hfin] with t ht htI
  obtain ⟨p, hp1, hpn, hpmem, -⟩ := hx.exists_mem_panel hn (Ioo_subset_Icc_self htI)
  have hne : ∀ m ≤ n, t ≠ x m := fun m hm hcon ↦ ht ⟨m, hm, hcon.symm⟩
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  refine ⟨k, by omega, ?_⟩
  simp only [Nat.add_sub_cancel] at hpmem
  exact ⟨lt_of_le_of_ne hpmem.1 (Ne.symm (hne k (by omega))),
    lt_of_le_of_ne hpmem.2 (hne (k + 1) (by omega))⟩

/-- For a partition of $[a, b]$ with $n \ge 1$, the classical derivative of $\varphi_i$ agrees
almost everywhere on $(a, b)$ with `FiniteElement.hatDerivFun`. The two differ only at the
nodes. -/
theorem ae_deriv_hatFun_eq (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) (i : ℕ) :
    deriv (hatFun n x i) =ᵐ[volume.restrict (Ioo a b)] hatDerivFun n x i := by
  filter_upwards [hx.ae_mem_Ioo_panel hn] with t ⟨k, hk, htk⟩
  exact deriv_hatFun_eq hx hk htk

/-- **The weak derivative of the hat function.** Let $a = x_0 < \dots < x_n = b$ be a partition with
$n \ge 1$. Then for every $i$ the function `FiniteElement.hatDerivFun` is a weak derivative of
the hat function $\varphi_i$ on $(a, b)$.

The hat function is continuous and piecewise $C^1$ with bounded panel derivatives, so
`memSobolevInterval_of_piecewise_contDiffOn` applies. -/
theorem hasWeakDerivOn_hatFun (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) (i : ℕ) :
    HasWeakDerivOn (hatFun n x i) (hatDerivFun n x i) (TopologicalSpace.Opens.Ioo a b) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  set y : Fin (N + 2) → ℝ := fun j ↦ x (j : ℕ) with hy
  have hymono : StrictMono y := fun i j hij ↦
    hx.lt (Fin.lt_def.1 hij) (by omega)
  have hy0 : y 0 = a := by simpa [hy] using hx.first
  have hylast : y (Fin.last (N + 1)) = b := by simpa [hy] using hx.last
  have hg' : ∀ j : Fin (N + 1), ContDiffOn ℝ 1 (hatFun (N + 1) x i)
      (Ioo (y j.castSucc) (y j.succ)) := fun j ↦ by
    simpa only [hy, Fin.val_castSucc, Fin.val_succ] using
      contDiffOn_hatFun_panel (i := i) hx (k := (j : ℕ)) j.isLt
  have hbdd : ∃ C, ∀ j : Fin (N + 1), ∀ t ∈ Ioo (y j.castSucc) (y j.succ),
      |deriv (hatFun (N + 1) x i) t| ≤ C := by
    refine ⟨hatBound x i, fun j t ht ↦ ?_⟩
    simp only [hy, Fin.val_castSucc, Fin.val_succ] at ht
    rw [deriv_hatFun_eq hx j.isLt ht]
    exact abs_hatDerivFun_le _ x i t
  obtain ⟨-, hweak⟩ := memSobolevInterval_of_piecewise_contDiffOn hymono hy0 hylast
    (continuous_hatFun _ x i).continuousOn hg' hbdd
  exact hweak.congr_ae (Filter.EventuallyEq.refl _ _) (ae_deriv_hatFun_eq hx hn i)

/-- **The hat function $\varphi_i$ of $X_h^1$** ((12.61) of [quarteroni2000numerical]), as an
element of $H^1(a, b)$, for a partition of $[a, b]$ with $n \ge 1$. Its function is the $L^2$
class of `FiniteElement.hatFun` and its weak derivative is the $L^2$ class of
`FiniteElement.hatDerivFun`.

The element is built with `SobolevInterval.mk`, not through an existence statement, so that both
components are available definitionally. The stiffness and mass integrals need this. -/
noncomputable def hatFunction (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) (i : ℕ) :
    SobolevInterval 1 a b :=
  SobolevInterval.mk ![(memLp_hatFun n x i).toLp _, (memLp_hatDerivFun n x i).toLp _]
    (fun j ↦ by
      fin_cases j
      · exact HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
          ((Lp.memLp _).locallyIntegrableOn (Ω := TopologicalSpace.Opens.Ioo a b) one_le_two)
      · exact hasWeakIteratedDerivOn_one.2 ((hasWeakDerivOn_hatFun hx hn i).congr_ae
          (memLp_hatFun n x i).coeFn_toLp.symm (memLp_hatDerivFun n x i).coeFn_toLp.symm))

/-- The function of the hat element $\varphi_i \in H^1(a, b)$ equals `FiniteElement.hatFun` almost
everywhere on $(a, b)$. -/
theorem coeFn_deriv_hatFunction_zero (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) (i : ℕ) :
    ⇑(SobolevInterval.deriv (hatFunction hx hn i) 0)
      =ᵐ[volume.restrict (Ioo a b)] hatFun n x i :=
  (memLp_hatFun n x i).coeFn_toLp

/-- The weak derivative of the hat element $\varphi_i \in H^1(a, b)$ equals
`FiniteElement.hatDerivFun` almost everywhere on $(a, b)$. It takes the value $1/h_{i-1}$ on the
panel $(x_{i-1}, x_i)$ and $-1/h_i$ on the panel $(x_i, x_{i+1})$, where $h_j = x_{j+1} - x_j$. -/
theorem coeFn_deriv_hatFunction_one (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) (i : ℕ) :
    ⇑(SobolevInterval.deriv (hatFunction hx hn i) 1)
      =ᵐ[volume.restrict (Ioo a b)] hatDerivFun n x i :=
  (memLp_hatDerivFun n x i).coeFn_toLp

/-- For a partition of $[a, b]$, every node $x_j$ with $j \le n$ lies in $[a, b]$. -/
theorem node_mem_Icc (hx : IsIntervalPartition a b n x) {j : ℕ} (hj : j ≤ n) : x j ∈ Icc a b :=
  Set.mem_Icc.2 ⟨hx.left_le hj, hx.le_right hj⟩

/-- The continuous representative of the hat element $\varphi_i \in H^1(a, b)$ equals
`FiniteElement.hatFun` on $[a, b]$. -/
theorem rep_hatFunction (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) (i : ℕ) {t : ℝ}
    (ht : t ∈ Icc a b) : SobolevInterval.rep (hatFunction hx hn i) t = hatFun n x i t :=
  SobolevInterval.rep_eq_of_continuousOn (hx.lt_of_pos hn) _
    (continuous_hatFun n x i).continuousOn (coeFn_deriv_hatFunction_zero hx hn i) ht

/-- **The Lagrange interpolation property of the hat elements.** Let $a = x_0 < \dots < x_n = b$ be
a partition with $n \ge 1$. For every index $i$ and every $j \le n$, the continuous
representative of the hat element $\varphi_i \in H^1(a, b)$ satisfies $$\varphi_i(x_j) =
\delta_{ij}.$$
-/
theorem rep_hatFunction_node (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) {i j : ℕ}
    (hj : j ≤ n) :
    SobolevInterval.rep (hatFunction hx hn i) (x j) = if i = j then 1 else 0 := by
  rw [rep_hatFunction hx hn i (node_mem_Icc hx hj)]
  exact hatFun_apply_node hx hn hj

/-- **The hat elements lie in $X_h^1$.** Let $a < b$ and let $a = x_0 < \dots < x_n = b$ be a
partition with $n \ge 1$. Then every hat element $\varphi_i$ lies in $X_h^1$, because it is
continuous and affine on every panel. -/
theorem hatFunction_mem_lagrangeSpace (hab : a < b) (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    (i : ℕ) : hatFunction hx hn i ∈ lagrangeSpace hab n x 1 := by
  refine ⟨hatFun n x i, ?_, fun t ↦ rep_hatFunction hx hn i t.2, fun j hj ↦ ?_⟩
  · rw [Nat.cast_zero]
    exact contDiffOn_zero.2 (continuous_hatFun n x i).continuousOn
  obtain ⟨c, d, hcd, -⟩ := exists_affine_hatFun hx hj i
  exact ⟨Polynomial.C c * Polynomial.X + Polynomial.C d, Polynomial.degree_linear_le,
    fun t ht ↦ by simpa using hcd t ht⟩

/-- **The interior hat elements lie in $X_h^{1,0}$.** Let $a < b$ and let
$a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$. Then every hat element $\varphi_i$
with $i \ne 0$ and $i \ne n$ lies in $X_h^{1,0}$, because it vanishes at both endpoints. -/
theorem hatFunction_mem_lagrangeSpaceZero (hab : a < b) (hx : IsIntervalPartition a b n x)
    (hn : 1 ≤ n) {i : ℕ} (h0 : i ≠ 0) (hi : i ≠ n) :
    hatFunction hx hn i ∈ lagrangeSpaceZero hab n x 1 := by
  refine ⟨hatFunction_mem_lagrangeSpace hab hx hn i,
    SobolevIntervalZero.mem_of_rep_eq_zero hab _ ?_ ?_⟩
  · have h := rep_hatFunction_node hx hn (i := i) (j := 0) (Nat.zero_le n)
    rw [hx.first] at h
    rw [h]
    simp [h0]
  · have h := rep_hatFunction_node hx hn (i := i) (j := n) le_rfl
    rw [hx.last] at h
    rw [h]
    simp [hi]

/-- The hat functions $\varphi_0, \dots, \varphi_n$ as elements of $X_h^1$, indexed by the $n + 1$
nodes. -/
noncomputable def hatElem (hab : a < b) (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    (i : Fin (n + 1)) : lagrangeSpace hab n x 1 :=
  ⟨hatFunction hx hn (i : ℕ), hatFunction_mem_lagrangeSpace hab hx hn (i : ℕ)⟩

/-- The hat functions $\varphi_0, \dots, \varphi_n$ are linearly independent in $X_h^1$. Evaluating
a vanishing combination at the node $x_j$ gives its $j$-th coefficient. -/
theorem linearIndependent_hatElem (hab : a < b) (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) :
    LinearIndependent ℝ (hatElem hab hx hn) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hjn : (j : ℕ) ≤ n := Nat.lt_succ_iff.1 j.isLt
  have hsub : (∑ i, g i • hatFunction hx hn (i : ℕ)) = 0 := by
    have := congrArg (Subtype.val) hg
    simpa [hatElem] using this
  have hval := congrArg (SobolevInterval.evalCLM hab ⟨_, node_mem_Icc hx hjn⟩) hsub
  simp only [map_sum, map_smul, smul_eq_mul, map_zero, SobolevInterval.evalCLM_apply] at hval
  rw [Finset.sum_congr rfl fun i _ ↦ congrArg (g i * ·)
    (rep_hatFunction_node hx hn (i := (i : ℕ)) (j := (j : ℕ)) hjn)] at hval
  simpa [Fin.val_inj] using hval

/-- **The hat basis of $X_h^1$** ((12.61) of [quarteroni2000numerical]). For a partition of $[a, b]$
with $n \ge 1$ and $a < b$, the $n + 1$ hat functions $\varphi_0, \dots, \varphi_n$ form a basis
of $X_h^1$. The nodal values are the degrees of freedom.

The basis comes from the linear independence and the dimension $\dim X_h^1 = n + 1$ of
`FiniteElement.finrank_lagrangeSpace`. -/
noncomputable def hatBasis (hab : a < b) (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) :
    Module.Basis (Fin (n + 1)) ℝ (lagrangeSpace hab n x 1) :=
  haveI := finiteDimensional_lagrangeSpace hab hx hn 1
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_hatElem hab hx hn)
    (by rw [Fintype.card_fin, finrank_lagrangeSpace hab hx hn 1]; ring)

/-- The $i$-th element of the hat basis is the hat function $\varphi_i$. -/
@[simp]
theorem hatBasis_apply (hab : a < b) (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    (i : Fin (n + 1)) : hatBasis hab hx hn i = hatElem hab hx hn i := by
  rw [hatBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- **The coordinates in the hat basis are the nodal values.** The $j$-th coordinate of
$v \in X_h^1$ in the hat basis is $v(x_j)$, the value of its continuous representative at $x_j$. -/
theorem hatBasis_repr (hab : a < b) (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    (v : lagrangeSpace hab n x 1) (j : Fin (n + 1)) :
    (hatBasis hab hx hn).repr v j
      = SobolevInterval.rep (v : SobolevInterval 1 a b) (x (j : ℕ)) := by
  have hjn : (j : ℕ) ≤ n := Nat.lt_succ_iff.1 j.isLt
  have hsub : (∑ i, (hatBasis hab hx hn).repr v i • hatFunction hx hn (i : ℕ))
      = (v : SobolevInterval 1 a b) := by
    have := congrArg (Subtype.val) ((hatBasis hab hx hn).sum_repr v)
    simpa [hatElem] using this
  have hval := congrArg (SobolevInterval.evalCLM hab ⟨_, node_mem_Icc hx hjn⟩) hsub
  simp only [map_sum, map_smul, smul_eq_mul, SobolevInterval.evalCLM_apply] at hval
  rw [Finset.sum_congr rfl fun i _ ↦ congrArg ((hatBasis hab hx hn).repr v i * ·)
    (rep_hatFunction_node hx hn (i := (i : ℕ)) (j := (j : ℕ)) hjn)] at hval
  simpa [Fin.val_inj] using hval

/-- **Every element of $X_h^1$ is the combination of the hat functions with its nodal values**
(§12.4.5 of [quarteroni2000numerical]). Let $a < b$, and let $a = x_0 < \dots < x_n = b$ be a
partition with $n \ge 1$. Then every $v_h \in X_h^1$ satisfies $$v_h = \sum_{i=0}^{n} v_h(x_i)\,
\varphi_i,$$ where $v_h(x_i)$ is the value of the continuous representative. -/
theorem eq_sum_hatFunction (hab : a < b) (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    (v : lagrangeSpace hab n x 1) :
    (v : SobolevInterval 1 a b) = ∑ i : Fin (n + 1),
      SobolevInterval.rep (v : SobolevInterval 1 a b) (x (i : ℕ)) • hatFunction hx hn (i : ℕ) := by
  have hsub : (∑ i, (hatBasis hab hx hn).repr v i • hatFunction hx hn (i : ℕ))
      = (v : SobolevInterval 1 a b) := by
    have := congrArg (Subtype.val) ((hatBasis hab hx hn).sum_repr v)
    simpa [hatElem] using this
  refine hsub.symm.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [hatBasis_repr hab hx hn v i]

/-- The interior hat functions $\varphi_1, \dots, \varphi_{n-1}$, as elements of $X_h^{1,0}$. -/
noncomputable def hatElemZero (hab : a < b) (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    (i : Fin (n - 1)) : lagrangeSpaceZero hab n x 1 :=
  ⟨hatFunction hx hn ((i : ℕ) + 1), hatFunction_mem_lagrangeSpaceZero hab hx hn (by omega)
    (by have := i.isLt; omega)⟩

/-- **The interior hat functions are linearly independent.** Let $a < b$, and let
$a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$. Then
$\varphi_1, \dots, \varphi_{n-1}$ are linearly independent in $H^1(a, b)$.

Evaluating a vanishing combination at the node $x_j$ gives its $j$-th coefficient. -/
theorem linearIndependent_hatFunction_succ (hab : a < b) (hx : IsIntervalPartition a b n x)
    (hn : 1 ≤ n) : LinearIndependent ℝ fun i : Fin (n - 1) ↦ hatFunction hx hn ((i : ℕ) + 1) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hjn : (j : ℕ) + 1 ≤ n := by have := j.isLt; omega
  have hval := congrArg (SobolevInterval.evalCLM hab ⟨_, node_mem_Icc hx hjn⟩) hg
  simp only [map_sum, map_smul, smul_eq_mul, map_zero, SobolevInterval.evalCLM_apply] at hval
  rw [Finset.sum_congr rfl fun i _ ↦ congrArg (g i * ·)
    (rep_hatFunction_node hx hn (i := (i : ℕ) + 1) (j := (j : ℕ) + 1) hjn)] at hval
  simpa [Fin.val_inj] using hval

/-- The interior hat functions $\varphi_1, \dots, \varphi_{n-1}$ are linearly independent in
$X_h^{1,0}$. -/
theorem linearIndependent_hatElemZero (hab : a < b) (hx : IsIntervalPartition a b n x)
    (hn : 1 ≤ n) : LinearIndependent ℝ (hatElemZero hab hx hn) :=
  (linearIndependent_hatFunction_succ hab hx hn).of_comp (lagrangeSpaceZero hab n x 1).subtype

/-- **Every element of $X_h^{1,0}$ is the combination of the interior hat functions with its nodal
values.** Let $a < b$, and let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$. Then
every $v \in X_h^{1,0}$ satisfies $$v = \sum_{i=1}^{n-1} v(x_i)\, \varphi_i,$$ where $v(x_i)$ is
the value of the continuous representative. -/
theorem eq_sum_hatFunction_zero (hab : a < b) (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    {v : SobolevInterval 1 a b} (hv : v ∈ lagrangeSpaceZero hab n x 1) :
    v = ∑ i : Fin (n - 1),
      SobolevInterval.rep v (x ((i : ℕ) + 1)) • hatFunction hx hn ((i : ℕ) + 1) := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hm
  have hrepr := eq_sum_hatFunction hab hx hn ⟨v, hv.1⟩
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at hrepr
  simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hrepr
  have hc0 : SobolevInterval.rep v (x 0) = 0 := by
    rw [hx.first]; exact SobolevIntervalZero.rep_left_eq_zero hab hv.2
  have hcl : SobolevInterval.rep v (x (m + 1)) = 0 := by
    rw [hx.last]; exact SobolevIntervalZero.rep_right_eq_zero hab hv.2
  rw [hc0, hcl] at hrepr
  simpa using hrepr

/-- The interior hat functions span $X_h^{1,0}$. An element of $X_h^{1,0}$ is the combination of all
the hat functions with its nodal values, and its two endpoint values are $0$. -/
theorem top_le_span_hatElemZero (hab : a < b) (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) :
    ⊤ ≤ Submodule.span ℝ (Set.range (hatElemZero hab hx hn)) := by
  rintro v -
  have hv : v = ∑ i : Fin (n - 1),
      SobolevInterval.rep (v : SobolevInterval 1 a b) (x ((i : ℕ) + 1))
        • hatElemZero hab hx hn i :=
    Subtype.ext ((eq_sum_hatFunction_zero hab hx hn v.2).trans (by simp [hatElemZero]))
  rw [hv]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **The interior hat basis of $X_h^{1,0}$** ((12.57) of [quarteroni2000numerical]). For a
partition of $[a, b]$ with $n \ge 1$ and $a < b$, the $n - 1$ hat functions
$\varphi_1, \dots, \varphi_{n-1}$ of the interior nodes form a basis of $X_h^{1,0}$. -/
noncomputable def hatBasisZero (hab : a < b) (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) :
    Module.Basis (Fin (n - 1)) ℝ (lagrangeSpaceZero hab n x 1) :=
  Module.Basis.mk (linearIndependent_hatElemZero hab hx hn) (top_le_span_hatElemZero hab hx hn)

/-- The $i$-th element of the interior hat basis is the hat function $\varphi_{i+1}$. -/
@[simp]
theorem hatBasisZero_apply (hab : a < b) (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    (i : Fin (n - 1)) : hatBasisZero hab hx hn i = hatElemZero hab hx hn i :=
  congrFun (Module.Basis.coe_mk _ _) i

/-- **The dimension of $X_h^{1,0}$.** Let $a < b$, and let $a = x_0 < \dots < x_n = b$ be a
partition with $n \ge 1$. Then $$\dim X_h^{1,0} = n - 1.$$ This is the dimension $N = nk - 1$ of
§12.4.5 of [quarteroni2000numerical] at $k = 1$. -/
theorem finrank_lagrangeSpaceZero_one (hab : a < b) (hx : IsIntervalPartition a b n x)
    (hn : 1 ≤ n) : Module.finrank ℝ (lagrangeSpaceZero hab n x 1) = n - 1 := by
  rw [Module.finrank_eq_card_basis (hatBasisZero hab hx hn), Fintype.card_fin]

end Partition

/-! ### Elementary integrals -/

/-- The integral of a quadratic polynomial: $$\int_u^v (p t^2 + q t + r)\, dt = \Big[\frac{p
t^3}{3} + \frac{q t^2}{2} + r t\Big]_u^v.$$
-/
theorem integral_quadratic (u v p q r : ℝ) :
    ∫ t in u..v, (p * t ^ 2 + q * t + r)
      = (p * v ^ 3 / 3 + q * v ^ 2 / 2 + r * v)
        - (p * u ^ 3 / 3 + q * u ^ 2 / 2 + r * u) := by
  have hcont : Continuous fun t : ℝ ↦ p * t ^ 2 + q * t + r :=
    ((continuous_const.mul (continuous_pow 2)).add
      (continuous_const.mul continuous_id)).add continuous_const
  refine integral_eq_sub_of_hasDerivAt (f := fun t : ℝ ↦ p * t ^ 3 / 3 + q * t ^ 2 / 2 + r * t)
    (fun t _ ↦ ?_) (hcont.intervalIntegrable _ _)
  have h1 : HasDerivAt (fun t : ℝ ↦ p * t ^ 3 / 3) (p * t ^ 2) t := by
    have := ((hasDerivAt_pow 3 t).const_mul p).div_const 3
    simpa using this.congr_deriv (by ring)
  have h2 : HasDerivAt (fun t : ℝ ↦ q * t ^ 2 / 2) (q * t) t := by
    have := ((hasDerivAt_pow 2 t).const_mul q).div_const 2
    simpa using this.congr_deriv (by ring)
  have h3 : HasDerivAt (fun t : ℝ ↦ r * t) r t := by
    simpa using (hasDerivAt_id t).const_mul r
  exact (h1.add h2).add h3

section Panel

variable {u v : ℝ}

/-- For $u < v$: $\int_u^v \frac{v - t}{v - u}\, dt = \frac{v - u}{2}$. -/
theorem integral_ramp_left (huv : u < v) :
    ∫ t in u..v, (v - t) / (v - u) = (v - u) / 2 := by
  have hne : v - u ≠ 0 := by linarith
  rw [integral_congr (g := fun t ↦ 0 * t ^ 2 + (-(v - u)⁻¹) * t + v * (v - u)⁻¹)
    (fun t _ ↦ by field_simp; ring), integral_quadratic]
  field_simp
  ring

/-- For $u < v$: $\int_u^v \frac{t - u}{v - u}\, dt = \frac{v - u}{2}$. -/
theorem integral_ramp_right (huv : u < v) :
    ∫ t in u..v, (t - u) / (v - u) = (v - u) / 2 := by
  have hne : v - u ≠ 0 := by linarith
  rw [integral_congr (g := fun t ↦ 0 * t ^ 2 + (v - u)⁻¹ * t + (-(u * (v - u)⁻¹)))
    (fun t _ ↦ by field_simp; ring), integral_quadratic]
  field_simp
  ring

/-- For $u < v$: $\int_u^v \Big(\frac{v - t}{v - u}\Big)^2 dt = \frac{v - u}{3}$. -/
theorem integral_ramp_left_sq (huv : u < v) :
    ∫ t in u..v, (v - t) / (v - u) * ((v - t) / (v - u)) = (v - u) / 3 := by
  have hne : v - u ≠ 0 := by linarith
  rw [integral_congr (g := fun t ↦ ((v - u) ^ 2)⁻¹ * t ^ 2 + (-(2 * v * ((v - u) ^ 2)⁻¹)) * t
      + v ^ 2 * ((v - u) ^ 2)⁻¹) (fun t _ ↦ by field_simp; ring), integral_quadratic]
  field_simp
  ring

/-- For $u < v$: $\int_u^v \Big(\frac{t - u}{v - u}\Big)^2 dt = \frac{v - u}{3}$. -/
theorem integral_ramp_right_sq (huv : u < v) :
    ∫ t in u..v, (t - u) / (v - u) * ((t - u) / (v - u)) = (v - u) / 3 := by
  have hne : v - u ≠ 0 := by linarith
  rw [integral_congr (g := fun t ↦ ((v - u) ^ 2)⁻¹ * t ^ 2 + (-(2 * u * ((v - u) ^ 2)⁻¹)) * t
      + u ^ 2 * ((v - u) ^ 2)⁻¹) (fun t _ ↦ by field_simp; ring), integral_quadratic]
  field_simp
  ring

/-- For $u < v$: $\int_u^v \frac{(v - t)(t - u)}{(v - u)^2}\, dt = \frac{v - u}{6}$. -/
theorem integral_ramp_cross (huv : u < v) :
    ∫ t in u..v, (v - t) / (v - u) * ((t - u) / (v - u)) = (v - u) / 6 := by
  have hne : v - u ≠ 0 := by linarith
  rw [integral_congr (g := fun t ↦ (-((v - u) ^ 2)⁻¹) * t ^ 2 + (u + v) * ((v - u) ^ 2)⁻¹ * t
      + (-(u * v * ((v - u) ^ 2)⁻¹))) (fun t _ ↦ by field_simp; ring), integral_quadratic]
  field_simp
  ring

end Panel

/-! ### The panel integrals of the hat functions -/

section Panel

variable {u v : ℝ}

/-- Let $u < v$, $h = v - u$, and let $L(t) = (v - t)/h$ and $R(t) = (t - u)/h$ be the nodal basis
of the affine functions on $[u, v]$. Then $\int_u^v (pL + qR) = (p + q) h/2$. -/
theorem integral_panel_affine (huv : u < v) (p q : ℝ) :
    ∫ t in u..v, (p * ((v - t) / (v - u)) + q * ((t - u) / (v - u))) = (p + q) * (v - u) / 2 := by
  have hne : v - u ≠ 0 := by linarith
  rw [integral_congr (g := fun t ↦ 0 * t ^ 2 + (q - p) / (v - u) * t + (p * v - q * u) / (v - u))
    (fun t _ ↦ by field_simp; ring), integral_quadratic]
  field_simp
  ring

/-- Let $u < v$, $h = v - u$, and let $L(t) = (v - t)/h$ and $R(t) = (t - u)/h$ be the nodal basis
of the affine functions on $[u, v]$. Then $$\int_u^v (pL + qR)(p'L + q'R) = (pp' +
qq')\frac{h}{3} + (pq' + qp')\frac{h}{6}.$$
-/
theorem integral_panel_affine_mul (huv : u < v) (p q p' q' : ℝ) :
    ∫ t in u..v, (p * ((v - t) / (v - u)) + q * ((t - u) / (v - u)))
        * (p' * ((v - t) / (v - u)) + q' * ((t - u) / (v - u)))
      = (p * p' + q * q') * (v - u) / 3 + (p * q' + q * p') * (v - u) / 6 := by
  have hne : v - u ≠ 0 := by linarith
  rw [integral_congr (g := fun t ↦ (q - p) * (q' - p') / (v - u) ^ 2 * t ^ 2
      + ((q - p) * (p' * v - q' * u) + (q' - p') * (p * v - q * u)) / (v - u) ^ 2 * t
      + (p * v - q * u) * (p' * v - q' * u) / (v - u) ^ 2)
    (fun t _ ↦ by field_simp; ring), integral_quadratic]
  field_simp
  ring

end Panel

section PanelHat

variable {n : ℕ} {x : ℕ → ℝ}

/-- **The hat functions on one panel.** For a partition of $[a, b]$ and $k < n$, on the panel
$[x_k, x_{k+1}]$ every hat function is the combination of the two panel ramps with its nodal
values: $$\varphi_i(t) = \delta_{ik} \frac{x_{k+1} - t}{x_{k+1} - x_k} + \delta_{i,k+1}
\frac{t - x_k}{x_{k+1} - x_k}.$$
-/
theorem hatFun_eq_panel (hx : IsIntervalPartition a b n x) {k : ℕ} (hk : k < n) (i : ℕ) {t : ℝ}
    (h1 : x k ≤ t) (h2 : t ≤ x (k + 1)) :
    hatFun n x i t = (if i = k then (1 : ℝ) else 0) * ((x (k + 1) - t) / (x (k + 1) - x k))
      + (if i = k + 1 then (1 : ℝ) else 0) * ((t - x k) / (x (k + 1) - x k)) := by
  rcases eq_or_ne i k with rfl | hik
  · rw [hatFun_eq_of_left hx hk h1 h2]
    simp
  rcases eq_or_ne i (k + 1) with rfl | hik'
  · rw [hatFun_eq_of_right hx hk h1 h2]
    simp
  · rw [hatFun_eq_zero_of_panel hx hk hik hik' h1 h2]
    simp [hik, hik']

/-- **The derivative of the hat functions on one panel.** For a partition of $[a, b]$ and $k < n$,
on the open panel $(x_k, x_{k+1})$ the derivative of $\varphi_i$ is the difference quotient of
its nodal values: $$\varphi_i'(t) = \frac{\delta_{i,k+1} - \delta_{ik}}{x_{k+1} - x_k}.$$
-/
theorem hatDerivFun_eq_panel (hx : IsIntervalPartition a b n x) {k : ℕ} (hk : k < n) (i : ℕ)
    {t : ℝ} (ht : t ∈ Ioo (x k) (x (k + 1))) :
    hatDerivFun n x i t = ((if i = k + 1 then (1 : ℝ) else 0) - (if i = k then (1 : ℝ) else 0))
      / (x (k + 1) - x k) := by
  rcases eq_or_ne i k with rfl | hik
  · rw [hatDerivFun_eq_of_left hx hk ht]
    simp [neg_div]
  rcases eq_or_ne i (k + 1) with rfl | hik'
  · rw [hatDerivFun_eq_of_right hx hk ht]
    simp
  · rw [hatDerivFun_eq_zero_of_panel hx hk hik hik' ht]
    simp [hik, hik']

/-- **The panel mass integral.** For a partition of $[a, b]$ and $k < n$, let $h_k = x_{k+1} - x_k$,
$p_i = \delta_{ik}$ and $q_i = \delta_{i,k+1}$. Then $$\int_{x_k}^{x_{k+1}} \varphi_i
\varphi_j = (p_i p_j + q_i q_j)\frac{h_k}{3} + (p_i q_j + q_i p_j)\frac{h_k}{6}.$$
-/
theorem integral_panel_hat_mul_hat (hx : IsIntervalPartition a b n x) {k : ℕ} (hk : k < n)
    (i j : ℕ) :
    ∫ t in (x k)..(x (k + 1)), hatFun n x i t * hatFun n x j t
      = ((if i = k then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)
          + (if i = k + 1 then (1 : ℝ) else 0) * (if j = k + 1 then (1 : ℝ) else 0))
        * (x (k + 1) - x k) / 3
      + ((if i = k then (1 : ℝ) else 0) * (if j = k + 1 then (1 : ℝ) else 0)
          + (if i = k + 1 then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0))
        * (x (k + 1) - x k) / 6 := by
  have hlt := hx.step k hk
  rw [integral_congr (f := fun t ↦ hatFun n x i t * hatFun n x j t)
    (g := fun t ↦ ((if i = k then (1 : ℝ) else 0) * ((x (k + 1) - t) / (x (k + 1) - x k))
        + (if i = k + 1 then (1 : ℝ) else 0) * ((t - x k) / (x (k + 1) - x k)))
      * ((if j = k then (1 : ℝ) else 0) * ((x (k + 1) - t) / (x (k + 1) - x k))
        + (if j = k + 1 then (1 : ℝ) else 0) * ((t - x k) / (x (k + 1) - x k))))
    (fun t ht ↦ by
      rw [uIcc_of_le hlt.le] at ht
      dsimp only
      rw [hatFun_eq_panel hx hk i ht.1 ht.2, hatFun_eq_panel hx hk j ht.1 ht.2]),
    integral_panel_affine_mul hlt]

/-- **The panel advection integral.** For a partition of $[a, b]$ and $k < n$, let
$p_i = \delta_{ik}$ and $q_i = \delta_{i,k+1}$. Then $$\int_{x_k}^{x_{k+1}} \varphi_i'
\varphi_j = \frac{(q_i - p_i)(p_j + q_j)}{2}.$$
-/
theorem integral_panel_hatDeriv_mul_hat (hx : IsIntervalPartition a b n x) {k : ℕ} (hk : k < n)
    (i j : ℕ) :
    ∫ t in (x k)..(x (k + 1)), hatDerivFun n x i t * hatFun n x j t
      = ((if i = k + 1 then (1 : ℝ) else 0) - (if i = k then (1 : ℝ) else 0))
        * ((if j = k then (1 : ℝ) else 0) + (if j = k + 1 then (1 : ℝ) else 0)) / 2 := by
  have hlt := hx.step k hk
  have hne : x (k + 1) - x k ≠ 0 := by linarith
  rw [intervalIntegral.integral_congr_Ioo_of_le hlt.le
    (f := fun t ↦ hatDerivFun n x i t * hatFun n x j t)
    (g := fun t ↦ (((if i = k + 1 then (1 : ℝ) else 0) - (if i = k then (1 : ℝ) else 0))
        / (x (k + 1) - x k))
      * ((if j = k then (1 : ℝ) else 0) * ((x (k + 1) - t) / (x (k + 1) - x k))
        + (if j = k + 1 then (1 : ℝ) else 0) * ((t - x k) / (x (k + 1) - x k))))
    (fun t ht ↦ by
      dsimp only
      rw [hatDerivFun_eq_panel hx hk i ht, hatFun_eq_panel hx hk j ht.1.le ht.2.le]),
    intervalIntegral.integral_const_mul, integral_panel_affine hlt]
  field_simp

/-- **The panel stiffness integral.** For a partition of $[a, b]$ and $k < n$, let
$h_k = x_{k+1} - x_k$, $p_i = \delta_{ik}$ and $q_i = \delta_{i,k+1}$. Then
$$\int_{x_k}^{x_{k+1}} \varphi_i' \varphi_j' = \frac{(q_i - p_i)(q_j - p_j)}{h_k}.$$
-/
theorem integral_panel_hatDeriv_mul_hatDeriv (hx : IsIntervalPartition a b n x) {k : ℕ}
    (hk : k < n) (i j : ℕ) :
    ∫ t in (x k)..(x (k + 1)), hatDerivFun n x i t * hatDerivFun n x j t
      = ((if i = k + 1 then (1 : ℝ) else 0) - (if i = k then (1 : ℝ) else 0))
        * ((if j = k + 1 then (1 : ℝ) else 0) - (if j = k then (1 : ℝ) else 0))
        / (x (k + 1) - x k) := by
  have hlt := hx.step k hk
  have hne : x (k + 1) - x k ≠ 0 := by linarith
  rw [intervalIntegral.integral_congr_Ioo_of_le hlt.le
    (f := fun t ↦ hatDerivFun n x i t * hatDerivFun n x j t)
    (g := fun _ ↦ (((if i = k + 1 then (1 : ℝ) else 0) - (if i = k then (1 : ℝ) else 0))
        / (x (k + 1) - x k))
      * (((if j = k + 1 then (1 : ℝ) else 0) - (if j = k then (1 : ℝ) else 0))
        / (x (k + 1) - x k)))
    (fun t ht ↦ by
      dsimp only
      rw [hatDerivFun_eq_panel hx hk i ht, hatDerivFun_eq_panel hx hk j ht]),
    intervalIntegral.integral_const, smul_eq_mul]
  field_simp

end PanelHat

/-! ### Integrability -/

/-- The normalized ramp is bounded by $1$ in absolute value, for any sequence of nodes:
$|R_j(t)| \le 1$. -/
theorem abs_rampFun_le_one (x : ℕ → ℝ) (j : ℕ) (t : ℝ) : |rampFun x j t| ≤ 1 := by
  have hm0 : (0 : ℝ) ≤ max (t - x j) 0 := le_max_right _ _
  rcases lt_trichotomy (x (j + 1) - x j) 0 with h | h | h
  · rw [rampFun, min_eq_right (by linarith), div_self (by linarith)]
    norm_num
  · rw [rampFun, h, div_zero]
    norm_num
  · have h1 : min (max (t - x j) 0) (x (j + 1) - x j) ≤ x (j + 1) - x j := min_le_right _ _
    rw [rampFun, abs_of_nonneg (by positivity), div_le_one h]
    exact h1

/-- The staircase is bounded by $1$ in absolute value. -/
theorem abs_hatStep_le_one (n : ℕ) (x : ℕ → ℝ) (i : ℕ) (t : ℝ) : |hatStep n x i t| ≤ 1 := by
  rw [hatStep]
  split_ifs
  · norm_num
  · exact abs_rampFun_le_one x _ t
  · norm_num

/-- The hat function is bounded by $2$ in absolute value, for any sequence of nodes. -/
theorem abs_hatFun_le_two (n : ℕ) (x : ℕ → ℝ) (i : ℕ) (t : ℝ) : |hatFun n x i t| ≤ 2 := by
  refine (abs_sub _ _).trans ?_
  have := abs_hatStep_le_one n x i t
  have := abs_hatStep_le_one n x (i + 1) t
  linarith

/-- The hat function is measurable. -/
theorem measurable_hatFun (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : Measurable (hatFun n x i) :=
  (continuous_hatFun n x i).measurable

/-- A measurable function $f : \mathbb{R} \to \mathbb{R}$ with $|f(t)| \le C$ for all $t$ is
interval integrable on every interval. -/
theorem intervalIntegrable_of_bounded {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ t, |f t| ≤ C) (u v : ℝ) : IntervalIntegrable f volume u v := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := C) ?_ hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ↦ by rw [Real.norm_eq_abs]; exact hb t)
  rw [Real.volume_uIoc]
  exact ENNReal.ofReal_ne_top

/-- The product $\varphi_i' \varphi_j'$ of two hat derivatives is interval integrable on every
interval. -/
theorem intervalIntegrable_hatDeriv_mul_hatDeriv (n : ℕ) (x : ℕ → ℝ) (i j : ℕ) (u v : ℝ) :
    IntervalIntegrable (fun t ↦ hatDerivFun n x i t * hatDerivFun n x j t) volume u v :=
  intervalIntegrable_of_bounded ((measurable_hatDerivFun n x i).mul (measurable_hatDerivFun n x j))
    (fun t ↦ by
      rw [Pi.mul_apply, abs_mul]
      exact mul_le_mul (abs_hatDerivFun_le n x i t) (abs_hatDerivFun_le n x j t) (abs_nonneg _)
        ((abs_nonneg _).trans (abs_hatDerivFun_le n x i t))) u v

/-- The product $\varphi_i' \varphi_j$ of a hat derivative and a hat function is interval integrable
on every interval. -/
theorem intervalIntegrable_hatDeriv_mul_hat (n : ℕ) (x : ℕ → ℝ) (i j : ℕ) (u v : ℝ) :
    IntervalIntegrable (fun t ↦ hatDerivFun n x i t * hatFun n x j t) volume u v :=
  intervalIntegrable_of_bounded ((measurable_hatDerivFun n x i).mul (measurable_hatFun n x j))
    (fun t ↦ by
      rw [Pi.mul_apply, abs_mul]
      exact mul_le_mul (abs_hatDerivFun_le n x i t) (abs_hatFun_le_two n x j t) (abs_nonneg _)
        ((abs_nonneg _).trans (abs_hatDerivFun_le n x i t))) u v

/-- The product $\varphi_i \varphi_j$ of two hat functions is interval integrable on every interval.
-/
theorem intervalIntegrable_hat_mul_hat (n : ℕ) (x : ℕ → ℝ) (i j : ℕ) (u v : ℝ) :
    IntervalIntegrable (fun t ↦ hatFun n x i t * hatFun n x j t) volume u v :=
  intervalIntegrable_of_bounded ((measurable_hatFun n x i).mul (measurable_hatFun n x j))
    (fun t ↦ by
      rw [Pi.mul_apply, abs_mul]
      exact mul_le_mul (abs_hatFun_le_two n x i t) (abs_hatFun_le_two n x j t) (abs_nonneg _)
        (by norm_num)) u v

/-- The integrand of the elliptic form with constant coefficients $\varepsilon$, $\beta$, $\gamma$
on two hat functions: $\varepsilon \varphi_i' \varphi_j' + \beta \varphi_i' \varphi_j + \gamma
\varphi_i \varphi_j$. -/
noncomputable def hatFormIntegrand (n : ℕ) (x : ℕ → ℝ) (ε β γ : ℝ) (i j : ℕ) : ℝ → ℝ :=
  fun t ↦ ε * (hatDerivFun n x i t * hatDerivFun n x j t)
    + β * (hatDerivFun n x i t * hatFun n x j t) + γ * (hatFun n x i t * hatFun n x j t)

/-- The integrand $\varepsilon \varphi_i' \varphi_j' + \beta \varphi_i' \varphi_j + \gamma \varphi_i
\varphi_j$ is interval integrable on every interval. -/
theorem intervalIntegrable_hatFormIntegrand (n : ℕ) (x : ℕ → ℝ) (ε β γ : ℝ) (i j : ℕ) (u v : ℝ) :
    IntervalIntegrable (hatFormIntegrand n x ε β γ i j) volume u v :=
  (((intervalIntegrable_hatDeriv_mul_hatDeriv n x i j u v).const_mul ε).add
    ((intervalIntegrable_hatDeriv_mul_hat n x i j u v).const_mul β)).add
      ((intervalIntegrable_hat_mul_hat n x i j u v).const_mul γ)

section PanelSum

variable {n : ℕ} {x : ℕ → ℝ}

/-- **The panel value of the elliptic form on two hat functions**, for constant coefficients. For a
partition of $[a, b]$ and $k < n$, the integral of $\varepsilon \varphi_i' \varphi_j' + \beta
\varphi_i' \varphi_j + \gamma \varphi_i \varphi_j$ over $[x_k, x_{k+1}]$ is $\varepsilon$ times
the panel stiffness integral, plus $\beta$ times the panel advection integral, plus $\gamma$
times the panel mass integral, in the closed forms of
`FiniteElement.integral_panel_hatDeriv_mul_hatDeriv`,
`FiniteElement.integral_panel_hatDeriv_mul_hat` and `FiniteElement.integral_panel_hat_mul_hat`. -/
theorem integral_panel_hatFormIntegrand (hx : IsIntervalPartition a b n x) {k : ℕ} (hk : k < n)
    (ε β γ : ℝ) (i j : ℕ) :
    ∫ t in (x k)..(x (k + 1)), hatFormIntegrand n x ε β γ i j t
      = ε * (((if i = k + 1 then (1 : ℝ) else 0) - (if i = k then (1 : ℝ) else 0))
          * ((if j = k + 1 then (1 : ℝ) else 0) - (if j = k then (1 : ℝ) else 0))
          / (x (k + 1) - x k))
        + β * (((if i = k + 1 then (1 : ℝ) else 0) - (if i = k then (1 : ℝ) else 0))
          * ((if j = k then (1 : ℝ) else 0) + (if j = k + 1 then (1 : ℝ) else 0)) / 2)
        + γ * (((if i = k then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)
              + (if i = k + 1 then (1 : ℝ) else 0) * (if j = k + 1 then (1 : ℝ) else 0))
            * (x (k + 1) - x k) / 3
          + ((if i = k then (1 : ℝ) else 0) * (if j = k + 1 then (1 : ℝ) else 0)
              + (if i = k + 1 then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0))
            * (x (k + 1) - x k) / 6) := by
  simp only [hatFormIntegrand]
  rw [intervalIntegral.integral_add
    (((intervalIntegrable_hatDeriv_mul_hatDeriv n x i j _ _).const_mul ε).add
      ((intervalIntegrable_hatDeriv_mul_hat n x i j _ _).const_mul β))
    ((intervalIntegrable_hat_mul_hat n x i j _ _).const_mul γ),
    intervalIntegral.integral_add
      ((intervalIntegrable_hatDeriv_mul_hatDeriv n x i j _ _).const_mul ε)
      ((intervalIntegrable_hatDeriv_mul_hat n x i j _ _).const_mul β),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_panel_hatDeriv_mul_hatDeriv hx hk,
    integral_panel_hatDeriv_mul_hat hx hk, integral_panel_hat_mul_hat hx hk]

/-- For a partition of $[a, b]$ and $k < n$, if $i \notin \{k, k + 1\}$ or $j \notin \{k, k + 1\}$,
then the integral of $\varepsilon \varphi_i' \varphi_j' + \beta \varphi_i' \varphi_j + \gamma
\varphi_i \varphi_j$ over $[x_k, x_{k+1}]$ is $0$. -/
theorem integral_panel_hatFormIntegrand_eq_zero (hx : IsIntervalPartition a b n x) {k : ℕ}
    (hk : k < n) (ε β γ : ℝ) {i j : ℕ} (h : (i ≠ k ∧ i ≠ k + 1) ∨ (j ≠ k ∧ j ≠ k + 1)) :
    ∫ t in (x k)..(x (k + 1)), hatFormIntegrand n x ε β γ i j t = 0 := by
  rw [integral_panel_hatFormIntegrand hx hk]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

/-- For a partition $a = x_0 < \dots < x_n = b$ and a function $F$ that is interval integrable on
every panel, $$\int_{(a, b)} F = \sum_{k=0}^{n-1} \int_{x_k}^{x_{k+1}} F.$$
-/
theorem integral_Ioo_eq_sum_panels (hx : IsIntervalPartition a b n x) {F : ℝ → ℝ}
    (hF : ∀ k, IntervalIntegrable F volume (x k) (x (k + 1))) :
    ∫ t in Ioo a b, F t = ∑ k ∈ Finset.range n, ∫ t in (x k)..(x (k + 1)), F t := by
  rw [intervalIntegral.sum_integral_adjacent_intervals (a := x) fun k _ ↦ hF k,
    ← intervalIntegral.integral_eq_setIntegral_Ioo hx.le, hx.first, hx.last]

end PanelSum

/-! ### The stiffness and mass matrices -/

open EllipticInterval

variable (a b) in
/-- **The stiffness matrix** $A_{fe}$ of (12.48) of [quarteroni2000numerical]. For coefficients
$\alpha, \beta, \gamma \in L^\infty(a, b)$ and a family $(\varphi_i)$ in $H^1(a, b)$, it is the
matrix with entries $$a_{ij} = a(\varphi_j, \varphi_i), \qquad a(u, v) = \int_a^b (\alpha u'
v' + \beta u' v + \gamma u v),$$ the Gram matrix of the elliptic form.

The form is `EllipticInterval.form` and the Gram matrix is `SesqForm.gramMatrix`. -/
noncomputable def stiffnessMatrix {ι : Type*} (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo a b)))
    (φ : ι → SobolevInterval 1 a b) : Matrix ι ι ℝ :=
  (EllipticInterval.form a b α β γ).gramMatrix φ

/-- The entries of the stiffness matrix are $a_{ij} = a(\varphi_j, \varphi_i)$. -/
theorem stiffnessMatrix_apply {ι : Type*} (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo a b)))
    (φ : ι → SobolevInterval 1 a b) (i j : ι) :
    stiffnessMatrix a b α β γ φ i j = EllipticInterval.form a b α β γ (φ j) (φ i) := rfl

variable (a b) in
/-- **The mass matrix** ((13.14) of [quarteroni2000numerical]). For a family $(\varphi_i)$ in
$H^1(a, b)$, it is the matrix with entries $$m_{ij} = \int_a^b \varphi_j \varphi_i,$$ the Gram
matrix of the family for the inner product of $L^2(a, b)$.

It is the stiffness matrix with the coefficients $\alpha = \beta = 0$ and $\gamma = 1$. -/
noncomputable def massMatrix {ι : Type*} (φ : ι → SobolevInterval 1 a b) : Matrix ι ι ℝ :=
  stiffnessMatrix a b (constLinf a b 0) (constLinf a b 0) (constLinf a b 1) φ

/-- The entries of the mass matrix are $m_{ij} = a(\varphi_j, \varphi_i)$ for the elliptic form with
$\alpha = \beta = 0$ and $\gamma = 1$, that is, $\int_a^b \varphi_j \varphi_i$. -/
theorem massMatrix_apply {ι : Type*} (φ : ι → SobolevInterval 1 a b) (i j : ι) :
    massMatrix a b φ i j =
      EllipticInterval.form a b (constLinf a b 0) (constLinf a b 0) (constLinf a b 1)
        (φ j) (φ i) := rfl

section Form

variable {n : ℕ} {x : ℕ → ℝ}

/-- For a partition of $[a, b]$ with $n \ge 1$, the elliptic form with constant coefficients
$\varepsilon$, $\beta$, $\gamma$ on two hat functions is $$a(\varphi_j, \varphi_i) = \int_{(a,
b)} (\varepsilon \varphi_j' \varphi_i' + \beta \varphi_j' \varphi_i + \gamma \varphi_j
\varphi_i).$$
-/
theorem form_apply_hatFunction (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) (ε β γ : ℝ)
    (i j : ℕ) :
    EllipticInterval.form a b (constLinf a b ε) (constLinf a b β) (constLinf a b γ)
        (hatFunction hx hn j) (hatFunction hx hn i)
      = ∫ t in Ioo a b, hatFormIntegrand n x ε β γ j i t := by
  rw [EllipticInterval.form_apply]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_constLinf a b ε, coeFn_constLinf a b β, coeFn_constLinf a b γ,
    coeFn_deriv_hatFunction_one hx hn j, coeFn_deriv_hatFunction_one hx hn i,
    coeFn_deriv_hatFunction_zero hx hn j, coeFn_deriv_hatFunction_zero hx hn i]
    with t h1 h2 h3 h4 h5 h6 h7
  simp only [h1, h2, h3, h4, h5, h6, h7, hatFormIntegrand]
  ring

/-- For a partition of $[a, b]$ with $n \ge 1$, the elliptic form with constant coefficients on two
hat functions is the sum over the panels: $$a(\varphi_j, \varphi_i) = \sum_{k=0}^{n-1}
\int_{x_k}^{x_{k+1}} (\varepsilon \varphi_j' \varphi_i' + \beta \varphi_j' \varphi_i + \gamma
\varphi_j \varphi_i).$$
-/
theorem form_apply_hatFunction_eq_sum (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    (ε β γ : ℝ) (i j : ℕ) :
    EllipticInterval.form a b (constLinf a b ε) (constLinf a b β) (constLinf a b γ)
        (hatFunction hx hn j) (hatFunction hx hn i)
      = ∑ k ∈ Finset.range n, ∫ t in (x k)..(x (k + 1)), hatFormIntegrand n x ε β γ j i t := by
  rw [form_apply_hatFunction hx hn ε β γ i j,
    integral_Ioo_eq_sum_panels hx fun k ↦ intervalIntegrable_hatFormIntegrand n x ε β γ j i _ _]

/-- **The entries of the stiffness matrix on a uniform mesh** (§12.4.5 of [quarteroni2000numerical],
the matrix that Program 95 assembles). Let $a = x_0 < \dots < x_n = b$ be a partition with
$n \ge 1$ and all panel lengths equal to $h > 0$, and let $\varepsilon$, $\beta$, $\gamma$ be
constant coefficients. For an interior node $1 \le i < n$ and every $j$,
$$a(\varphi_j, \varphi_i) = \begin{cases}
  2\varepsilon/h + 2\gamma h/3 & \text{if } j = i, \\
  -\varepsilon/h - \beta/2 + \gamma h/6 & \text{if } j = i - 1, \\
  -\varepsilon/h + \beta/2 + \gamma h/6 & \text{if } j = i + 1, \\
  0 & \text{otherwise.}
\end{cases}$$ -/
theorem form_apply_hatFunction_uniform (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    {h : ℝ} (hh : 0 < h) (huni : ∀ k < n, x (k + 1) - x k = h) (ε β γ : ℝ) {i j : ℕ}
    (hi1 : 1 ≤ i) (hi2 : i < n) :
    EllipticInterval.form a b (constLinf a b ε) (constLinf a b β) (constLinf a b γ)
        (hatFunction hx hn j) (hatFunction hx hn i)
      = if j = i then 2 * ε / h + 2 * γ * h / 3
        else if j + 1 = i then -(ε / h) - β / 2 + γ * h / 6
        else if i + 1 = j then -(ε / h) + β / 2 + γ * h / 6
        else 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rw [form_apply_hatFunction_eq_sum hx hn ε β γ (m + 1) j]
  have hne : h ≠ 0 := hh.ne'
  split_ifs with hd hs hp
  · have hsub : ({m, m + 1} : Finset ℕ) ⊆ Finset.range n := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      exact Finset.mem_range.2 (by omega)
    rw [← Finset.sum_subset hsub fun k hk hk' ↦ ?_, Finset.sum_pair (by omega : m ≠ m + 1),
      integral_panel_hatFormIntegrand hx (by omega : m < n),
      integral_panel_hatFormIntegrand hx (by omega : m + 1 < n), huni m (by omega),
      huni (m + 1) (by omega)]
    · subst hd
      norm_num
      field_simp
      ring
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
      exact integral_panel_hatFormIntegrand_eq_zero hx (Finset.mem_range.1 hk) ε β γ (by omega)
  · rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.2 (by omega)) fun k hk hk' ↦
        integral_panel_hatFormIntegrand_eq_zero hx (Finset.mem_range.1 hk) ε β γ (by omega),
      integral_panel_hatFormIntegrand hx (by omega : j < n), huni j (by omega)]
    have h2 : m + 1 = j + 1 := by omega
    simp only [h2]
    norm_num
    field_simp
    ring
  · rw [Finset.sum_eq_single_of_mem (m + 1) (Finset.mem_range.2 (by omega)) fun k hk hk' ↦
        integral_panel_hatFormIntegrand_eq_zero hx (Finset.mem_range.1 hk) ε β γ (by omega),
      integral_panel_hatFormIntegrand hx (by omega : m + 1 < n), huni (m + 1) (by omega)]
    have h4 : j = m + 1 + 1 := by omega
    simp only [h4]
    norm_num
    field_simp
  · exact Finset.sum_eq_zero fun k hk ↦
      integral_panel_hatFormIntegrand_eq_zero hx (Finset.mem_range.1 hk) ε β γ (by omega)

end Form

section Sparsity

variable {n : ℕ} {x : ℕ → ℝ}

/-- **Hat functions more than one node apart have supports that meet in a null set.** For a
partition of $[a, b]$ with $n \ge 1$ and $|i - j| \ge 2$, the three products
$\varphi_j' \varphi_i'$, $\varphi_j' \varphi_i$ and $\varphi_j \varphi_i$ vanish almost
everywhere on $(a, b)$. -/
theorem ae_hat_products_eq_zero (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) {i j : ℕ}
    (hij : i + 1 < j ∨ j + 1 < i) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      hatDerivFun n x j t * hatDerivFun n x i t = 0 ∧
        hatDerivFun n x j t * hatFun n x i t = 0 ∧ hatFun n x j t * hatFun n x i t = 0 := by
  filter_upwards [hx.ae_mem_Ioo_panel hn] with t ⟨k, hk, htk⟩
  rcases (by omega : (i ≠ k ∧ i ≠ k + 1) ∨ (j ≠ k ∧ j ≠ k + 1)) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hatFun_eq_zero_of_panel hx hk h1 h2 htk.1.le htk.2.le,
      hatDerivFun_eq_zero_of_panel hx hk h1 h2 htk]
    simp
  · rw [hatFun_eq_zero_of_panel hx hk h1 h2 htk.1.le htk.2.le,
      hatDerivFun_eq_zero_of_panel hx hk h1 h2 htk]
    simp

/-- **The elliptic form vanishes on two hat functions more than one node apart.** For a partition of
$[a, b]$ with $n \ge 1$, coefficients $\alpha, \beta, \gamma \in L^\infty(a, b)$ and
$|i - j| \ge 2$, $a(\varphi_j, \varphi_i) = 0$. -/
theorem form_apply_hatFunction_eq_zero (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo a b))) {i j : ℕ} (hij : i + 1 < j ∨ j + 1 < i) :
    EllipticInterval.form a b α β γ (hatFunction hx hn j) (hatFunction hx hn i) = 0 := by
  have hz : ∫ _t in Ioo a b, (0 : ℝ) = 0 := by simp
  rw [EllipticInterval.form_apply, ← hz]
  refine integral_congr_ae ?_
  filter_upwards [ae_hat_products_eq_zero hx hn hij, coeFn_deriv_hatFunction_one hx hn j,
    coeFn_deriv_hatFunction_one hx hn i, coeFn_deriv_hatFunction_zero hx hn j,
    coeFn_deriv_hatFunction_zero hx hn i] with t ⟨e1, e2, e3⟩ h1 h2 h3 h4
  simp only [h1, h2, h3, h4]
  rw [show α t * hatDerivFun n x j t * hatDerivFun n x i t
      = α t * (hatDerivFun n x j t * hatDerivFun n x i t) by ring, e1,
    show β t * hatDerivFun n x j t * hatFun n x i t
      = β t * (hatDerivFun n x j t * hatFun n x i t) by ring, e2,
    show γ t * hatFun n x j t * hatFun n x i t
      = γ t * (hatFun n x j t * hatFun n x i t) by ring, e3]
  ring

/-- **Sparsity of the stiffness matrix** (§12.4.5 of [quarteroni2000numerical]). Let
$a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, and let
$\alpha, \beta, \gamma \in L^\infty(a, b)$. In the family of all hat functions
$(\varphi_k)_{k \in \mathbb{N}}$, the stiffness matrix satisfies $a_{ij} = 0$ whenever
$|i - j| \ge 2$, that is, whenever $j \notin \{i - 1, i, i + 1\}$. -/
theorem stiffnessMatrix_eq_zero_of_lt (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo a b))) {i j : ℕ} (hij : i + 1 < j ∨ j + 1 < i) :
    stiffnessMatrix a b α β γ (fun k : ℕ ↦ hatFunction hx hn k) i j = 0 :=
  form_apply_hatFunction_eq_zero hx hn α β γ hij

/-- **The stiffness matrix of the interior hat functions is tridiagonal** (§12.4.5 of
[quarteroni2000numerical]). Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, and
let $\alpha, \beta, \gamma \in L^\infty(a, b)$. Then the stiffness matrix of the family
$\varphi_1, \dots, \varphi_{n-1}$ is tridiagonal.

The family is indexed by `Fin (n - 1)`, with index $k$ standing for $\varphi_{k+1}$. -/
theorem isTridiagonal_stiffnessMatrix (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo a b))) :
    (stiffnessMatrix a b α β γ fun k : Fin (n - 1) ↦ hatFunction hx hn ((k : ℕ) + 1))
      |>.IsTridiagonal := by
  rintro i j (⟨k, hjk, hki⟩ | ⟨k, hik, hkj⟩)
  · have h1 : (j : ℕ) < (k : ℕ) := hjk
    have h2 : (k : ℕ) < (i : ℕ) := hki
    exact form_apply_hatFunction_eq_zero hx hn α β γ (Or.inr (by omega))
  · have h1 : (i : ℕ) < (k : ℕ) := hik
    have h2 : (k : ℕ) < (j : ℕ) := hkj
    exact form_apply_hatFunction_eq_zero hx hn α β γ (Or.inl (by omega))

end Sparsity

section Uniform

variable {n : ℕ} {x : ℕ → ℝ}

/-- **The stiffness matrix on a uniform mesh** (§12.4.5 of [quarteroni2000numerical], the matrix
that Program 95 assembles). Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$ and
all panel lengths equal to $h > 0$, and let $\varepsilon$, $\beta$, $\gamma$ be constant
coefficients. Then the stiffness matrix of the interior hat functions
$\varphi_1, \dots, \varphi_{n-1}$ is $$A_{fe} = \frac{\varepsilon}{h} \operatorname{tridiag}(-1,
2, -1) + \frac{\beta}{2} \operatorname{tridiag}(-1, 0, 1) + \frac{\gamma h}{6}
\operatorname{tridiag}(1, 4, 1),$$ where $\operatorname{tridiag}(l, d, u)$ has $l$ on the
subdiagonal, $d$ on the diagonal and $u$ on the superdiagonal. For $\beta = \gamma = 0$ this is
$\varepsilon h$ times the centred finite difference matrix
$h^{-2} \operatorname{tridiag}(-1, 2, -1)$.

The tridiagonal matrices are `Matrix.symmTridiagonalToeplitz` and `Matrix.tridiagonalToeplitz`. -/
theorem stiffnessMatrix_uniform_eq (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) {h : ℝ}
    (hh : 0 < h) (huni : ∀ k < n, x (k + 1) - x k = h) (ε β γ : ℝ) :
    (stiffnessMatrix a b (constLinf a b ε) (constLinf a b β) (constLinf a b γ)
        fun i : Fin (n - 1) ↦ hatFunction hx hn ((i : ℕ) + 1))
      = (ε / h) • Matrix.symmTridiagonalToeplitz (n - 1) (-1) 2
        + (β / 2) • Matrix.tridiagonalToeplitz (n - 1) (-1) 0 1
        + (γ * h / 6) • Matrix.symmTridiagonalToeplitz (n - 1) 1 4 := by
  have hne : h ≠ 0 := hh.ne'
  ext i j
  have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
  rw [stiffnessMatrix_apply,
    form_apply_hatFunction_uniform hx hn hh huni ε β γ (Nat.le_add_left 1 (i : ℕ)) hi]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.symmTridiagonalToeplitz_apply', Matrix.tridiagonalToeplitz_apply]
  split_ifs <;> first | omega | (field_simp; ring) | field_simp

/-- **The mass matrix on a uniform mesh** (§13.3 of [quarteroni2000numerical]). Let
$a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$ and all panel lengths equal to
$h > 0$. Then the mass matrix of the interior hat functions $\varphi_1, \dots, \varphi_{n-1}$ is
$$M = \frac{h}{6} \operatorname{tridiag}(1, 4, 1),$$ that is, $\int \varphi_i^2 = 2h/3$ and
$\int \varphi_i \varphi_{i \pm 1} = h/6$. -/
theorem massMatrix_uniform_eq (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) {h : ℝ}
    (hh : 0 < h) (huni : ∀ k < n, x (k + 1) - x k = h) :
    (massMatrix a b fun i : Fin (n - 1) ↦ hatFunction hx hn ((i : ℕ) + 1))
      = (h / 6) • Matrix.symmTridiagonalToeplitz (n - 1) 1 4 := by
  rw [massMatrix, stiffnessMatrix_uniform_eq hx hn hh huni 0 0 1]
  simp

end Uniform

section PosDef

variable {n : ℕ} {x : ℕ → ℝ}

/-- The interior hat functions $\varphi_1, \dots, \varphi_{n-1}$, as elements of $H^1_0(a, b)$. -/
noncomputable def hatElemH0 (hab : a < b) (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    (i : Fin (n - 1)) : SobolevIntervalZero a b :=
  ⟨hatFunction hx hn ((i : ℕ) + 1),
    (hatFunction_mem_lagrangeSpaceZero hab hx hn (by omega) (by have := i.isLt; omega)).2⟩

/-- The interior hat functions $\varphi_1, \dots, \varphi_{n-1}$ are linearly independent in
$H^1_0(a, b)$. -/
theorem linearIndependent_hatElemH0 (hab : a < b) (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) :
    LinearIndependent ℝ (hatElemH0 hab hx hn) :=
  (linearIndependent_hatFunction_succ hab hx hn).of_comp (SobolevIntervalZero a b).subtype

/-- **The stiffness matrix is symmetric positive definite** (§12.4.4 of [quarteroni2000numerical]).
Let $a < b$, let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, and let
$\alpha, \gamma \in L^\infty(a, b)$ with $\alpha \ge \alpha_0$ and $\gamma \ge 0$ almost
everywhere, for a constant $\alpha_0 > 0$. Then the stiffness matrix of the interior hat
functions $\varphi_1, \dots, \varphi_{n-1}$ for the coefficients $\alpha$, $\beta = 0$, $\gamma$
is positive definite.

For $\beta = 0$ the form is symmetric and coercive on $H^1_0(a, b)$, and the interior hat
functions are linearly independent. -/
theorem stiffnessMatrix_posDef (hab : a < b) (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    (α γ : Lp ℝ ⊤ (volume.restrict (Ioo a b))) {α₀ : ℝ} (hα₀ : 0 < α₀)
    (hα : ∀ᵐ t ∂(volume.restrict (Ioo a b)), α₀ ≤ α t)
    (hγ : ∀ᵐ t ∂(volume.restrict (Ioo a b)), 0 ≤ γ t) :
    (stiffnessMatrix a b α 0 γ fun i : Fin (n - 1) ↦ hatFunction hx hn ((i : ℕ) + 1)).PosDef := by
  have hc : 0 < α₀ / (1 + (b - a) ^ 2 / 2) := by positivity
  have hsymm : ((EllipticInterval.form a b α 0 γ).restrict
      (SobolevIntervalZero a b)).IsHermitian := fun u v ↦ by
    simp only [SesqForm.restrict_apply, RCLike.conj_to_real]
    exact EllipticInterval.form_comm α γ _ _
  have heq : (stiffnessMatrix a b α 0 γ fun i : Fin (n - 1) ↦ hatFunction hx hn ((i : ℕ) + 1))
      = ((EllipticInterval.form a b α 0 γ).restrict (SobolevIntervalZero a b)).gramMatrix
        (hatElemH0 hab hx hn) := by
    ext i j
    rfl
  rw [heq]
  exact SesqForm.gramMatrix_posDef hc hsymm
    (EllipticInterval.form_isCoerciveWith_restrict hab α γ hα hγ hα₀.le)
    (linearIndependent_hatElemH0 hab hx hn)

end PosDef

section Conditioning

open scoped Matrix.Norms.L2Operator

variable {n : ℕ} {x : ℕ → ℝ}

/-- **The model stiffness matrix.** For the problem $-u'' = f$ ($\alpha = 1$, $\beta = \gamma = 0$)
on a partition with $n \ge 1$ and all panel lengths equal to $h > 0$, the stiffness matrix of
the interior hat functions is $$A_{fe} = h^{-1} \operatorname{tridiag}(-1, 2, -1),$$ which is
$h$ times the centred finite difference matrix. -/
theorem stiffnessMatrix_model_eq (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) {h : ℝ}
    (hh : 0 < h) (huni : ∀ k < n, x (k + 1) - x k = h) :
    (stiffnessMatrix a b (constLinf a b 1) (constLinf a b 0) (constLinf a b 0)
        fun i : Fin (n - 1) ↦ hatFunction hx hn ((i : ℕ) + 1))
      = h⁻¹ • Matrix.symmTridiagonalToeplitz (n - 1) (-1) 2 := by
  rw [stiffnessMatrix_uniform_eq hx hn hh huni 1 0 0]
  simp [one_div]

/-- **The spectral condition number of the model stiffness matrix** (§12.4.5 of
[quarteroni2000numerical]). For the problem $-u'' = f$ on a partition
$a = x_0 < \dots < x_n = b$ with $n \ge 1$ and all panel lengths equal to $h > 0$, the stiffness
matrix $A_{fe}$ of the interior hat functions satisfies $$K_2(A_{fe}) = \|A_{fe}\|_2
\|A_{fe}^{-1}\|_2 = \cot^2\Big(\frac{\pi}{2n}\Big).$$ In terms of the mesh size $h = (b - a)/n$
this is the growth $O(h^{-2})$ that the source quotes from its reference QV94.

The factor $h^{-1}$ of $A_{fe}$ cancels between $A_{fe}$ and its inverse. The norm is the
operator norm for the Euclidean norm, and the inverse is `Matrix.inv`. For $n = 1$ the matrix is
empty and both sides are $0$. -/
theorem condNumber_stiffnessMatrix_model (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) {h : ℝ}
    (hh : 0 < h) (huni : ∀ k < n, x (k + 1) - x k = h) :
    ‖stiffnessMatrix a b (constLinf a b 1) (constLinf a b 0) (constLinf a b 0)
        fun i : Fin (n - 1) ↦ hatFunction hx hn ((i : ℕ) + 1)‖
      * ‖(stiffnessMatrix a b (constLinf a b 1) (constLinf a b 0) (constLinf a b 0)
        fun i : Fin (n - 1) ↦ hatFunction hx hn ((i : ℕ) + 1))⁻¹‖
      = Real.cot (Real.pi / (2 * (n : ℝ))) ^ 2 := by
  rw [stiffnessMatrix_model_eq hx hn hh huni]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hcast : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by push_cast; ring
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h2 : Real.pi / (2 * ((0 + 1 : ℕ) : ℝ)) = Real.pi / 2 := by norm_num
    rw [show Matrix.symmTridiagonalToeplitz 0 (-1) 2 = 0 from Subsingleton.elim _ _, smul_zero,
      Matrix.inv_zero, norm_zero, zero_mul, h2, Real.cot_eq_cos_div_sin, Real.cos_pi_div_two,
      zero_div, zero_pow two_ne_zero]
  · have hu : (h⁻¹ : ℝ) ≠ 0 := by positivity
    have : Invertible (h⁻¹ : ℝ) := invertibleOfNonzero hu
    have hunit : IsUnit (Matrix.symmTridiagonalToeplitz m (-1) 2).det :=
      isUnit_iff_ne_zero.2 (Matrix.PosDef.det_pos
        (Matrix.posDef_symmTridiagonalToeplitz_neg_one_two m)).ne'
    rw [Matrix.inv_smul (k := (h⁻¹ : ℝ)) (A := Matrix.symmTridiagonalToeplitz m (-1) 2) hunit,
      norm_smul, norm_smul, invOf_eq_inv, inv_inv,
      show ‖h⁻¹‖ * ‖Matrix.symmTridiagonalToeplitz m (-1) 2‖
          * (‖h‖ * ‖(Matrix.symmTridiagonalToeplitz m (-1) 2)⁻¹‖)
        = ‖h⁻¹‖ * ‖h‖ * (‖Matrix.symmTridiagonalToeplitz m (-1) 2‖
          * ‖(Matrix.symmTridiagonalToeplitz m (-1) 2)⁻¹‖) by ring,
      ← norm_mul, inv_mul_cancel₀ hh.ne', norm_one, one_mul,
      Matrix.condNumber_symmTridiagonalToeplitz_neg_one_two, hcast]

end Conditioning

section Centred

variable {n : ℕ} {x : ℕ → ℝ}

/-- **The Galerkin equation at an interior node on a uniform mesh is the centred finite difference
stencil** ((12.75) of [quarteroni2000numerical]). Let $a = x_0 < \dots < x_n = b$ be a partition
with $n \ge 1$ and all panel lengths equal to $h > 0$, let $\varepsilon$ and $\beta$ be
constants and $\gamma = 0$, and let $u_0, \dots, u_n$ be real numbers. Then for every interior
node $1 \le i < n$ $$a\Big(\sum_{j=0}^{n} u_j \varphi_j,\ \varphi_i\Big) =
\frac{\varepsilon}{h}(-u_{i-1} + 2u_i - u_{i+1}) + \frac{\beta}{2}(u_{i+1} - u_{i-1}).$$
-/
theorem form_sum_hatFunction_uniform (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) {h : ℝ}
    (hh : 0 < h) (huni : ∀ k < n, x (k + 1) - x k = h) (ε β : ℝ) (u : ℕ → ℝ) {i : ℕ}
    (hi1 : 1 ≤ i) (hi2 : i < n) :
    EllipticInterval.form a b (constLinf a b ε) (constLinf a b β) (constLinf a b 0)
        (∑ j ∈ Finset.range (n + 1), u j • hatFunction hx hn j) (hatFunction hx hn i)
      = ε / h * (-u (i - 1) + 2 * u i - u (i + 1)) + β / 2 * (u (i + 1) - u (i - 1)) := by
  have hne : h ≠ 0 := hh.ne'
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have hlin : EllipticInterval.form a b (constLinf a b ε) (constLinf a b β)
        (constLinf a b 0) (∑ j ∈ Finset.range (n + 1), u j • hatFunction hx hn j)
        (hatFunction hx hn (m + 1))
      = ∑ j ∈ Finset.range (n + 1), u j * EllipticInterval.form a b (constLinf a b ε)
        (constLinf a b β) (constLinf a b 0) (hatFunction hx hn j)
        (hatFunction hx hn (m + 1)) := by
    rw [map_sum]
    simp only [sum_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smulₛₗ]
    simp
  rw [hlin, Finset.sum_congr rfl fun j _ ↦ congrArg (u j * ·)
    (form_apply_hatFunction_uniform hx hn hh huni ε β 0 (Nat.le_add_left 1 m) hi2)]
  have hsub : ({m, m + 1, m + 2} : Finset ℕ) ⊆ Finset.range (n + 1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    exact Finset.mem_range.2 (by omega)
  rw [← Finset.sum_subset hsub fun k hk hk' ↦ ?_]
  · rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
    have e1 : ¬ (m = m + 1) := by omega
    have e3 : ¬ (m + 2 = m + 1) := by omega
    have e4 : ¬ (m + 2 + 1 = m + 1) := by omega
    simp only [e1, e3, e4, Nat.add_sub_cancel, reduceIte]
    norm_num
    field_simp
    ring
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
    have e1 : ¬ (k = m + 1) := by omega
    have e2 : ¬ (k + 1 = m + 1) := by omega
    have e3 : ¬ (m + 1 + 1 = k) := by omega
    simp [e1, e3, hk'.1]

/-- **The Galerkin method with $X_h^1$ on a uniform mesh is the centred difference scheme** ((12.75)
of [quarteroni2000numerical]). Let $a < b$, let $a = x_0 < \dots < x_n = b$ be a partition with
$n \ge 1$ and all panel lengths equal to $h > 0$, let $\varepsilon$ and $\beta$ be constants and
$\gamma = 0$, and let $u_h = \sum_{j=0}^{n} u_j \varphi_j$ be the piecewise linear function with
nodal values $u_j$. Then $a(u_h, v) = 0$ for all $v \in X_h^{1,0}$ if and only if
$$\frac{\varepsilon}{h}(-u_{i-1} + 2u_i - u_{i+1}) + \frac{\beta}{2}(u_{i+1} - u_{i-1}) = 0
\quad \text{for every } 1 \le i < n.$$

The boundary values $u_0$ and $u_n$ are arbitrary, so the statement covers the problem with
homogeneous right-hand side and any Dirichlet data. -/
theorem galerkin_iff_centredScheme (hab : a < b) (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    {h : ℝ} (hh : 0 < h) (huni : ∀ k < n, x (k + 1) - x k = h) (ε β : ℝ) (u : ℕ → ℝ) :
    (∀ v ∈ lagrangeSpaceZero hab n x 1,
        EllipticInterval.form a b (constLinf a b ε) (constLinf a b β) (constLinf a b 0)
          (∑ j ∈ Finset.range (n + 1), u j • hatFunction hx hn j) v = 0)
      ↔ ∀ i, 1 ≤ i → i < n →
        ε / h * (-u (i - 1) + 2 * u i - u (i + 1)) + β / 2 * (u (i + 1) - u (i - 1)) = 0 := by
  constructor
  · intro H i hi1 hi2
    rw [← form_sum_hatFunction_uniform hx hn hh huni ε β u hi1 hi2]
    exact H _ (hatFunction_mem_lagrangeSpaceZero hab hx hn (by omega) (by omega))
  · intro H v hv
    rw [eq_sum_hatFunction_zero hab hx hn hv, map_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [map_smul, smul_eq_mul,
      form_sum_hatFunction_uniform hx hn hh huni ε β u (Nat.le_add_left 1 (i : ℕ))
        (by have := i.isLt; omega),
      H ((i : ℕ) + 1) (Nat.le_add_left 1 (i : ℕ)) (by have := i.isLt; omega), mul_zero]

end Centred

/-! ### The reference element -/

/-- **The affine map of the reference interval onto a panel** ((12.62) of
[quarteroni2000numerical]): $$x = \phi(\xi) = x_j + \xi (x_{j+1} - x_j).$$
-/
noncomputable def affineMap (x : ℕ → ℝ) (j : ℕ) : ℝ → ℝ := fun ξ ↦ x j + ξ * (x (j + 1) - x j)

/-- The reference coordinate $\xi(x) = (x - x_j)/(x_{j+1} - x_j)$ of the panel $[x_j, x_{j+1}]$
(§12.4.5 of [quarteroni2000numerical]), the inverse of `FiniteElement.affineMap`. -/
noncomputable def refCoord (x : ℕ → ℝ) (j : ℕ) : ℝ → ℝ := fun t ↦ (t - x j) / (x (j + 1) - x j)

/-- **The reference shape functions of $X_h^1$** (§12.4.5 of [quarteroni2000numerical]):
$\hat\varphi_0(\xi) = 1 - \xi$ and $\hat\varphi_1(\xi) = \xi$. -/
noncomputable def referenceHat : Fin 2 → ℝ → ℝ := ![fun ξ ↦ 1 - ξ, fun ξ ↦ ξ]

/-- **The reference shape functions of $X_h^2$** ((12.65) of [quarteroni2000numerical]):
$$\hat\varphi_0(\xi) = (1 - \xi)(1 - 2\xi), \qquad \hat\varphi_1(\xi) = 4(1 - \xi)\xi, \qquad
\hat\varphi_2(\xi) = \xi(2\xi - 1).$$
-/
noncomputable def referenceQuadratic : Fin 3 → ℝ → ℝ :=
  ![fun ξ ↦ (1 - ξ) * (1 - 2 * ξ), fun ξ ↦ 4 * (1 - ξ) * ξ, fun ξ ↦ ξ * (2 * ξ - 1)]

/-- **The hierarchical basis of $\mathbb{P}_2$ on the reference interval** ((12.66) of
[quarteroni2000numerical]): $$\hat\psi_0(\xi) = 1 - \xi, \qquad \hat\psi_1(\xi) = (1 - \xi)\xi,
\qquad \hat\psi_2(\xi) = \xi,$$ the two linear shape functions together with the bubble. -/
noncomputable def referenceHierarchical : Fin 3 → ℝ → ℝ :=
  ![fun ξ ↦ 1 - ξ, fun ξ ↦ (1 - ξ) * ξ, fun ξ ↦ ξ]

/-- The affine map of the reference interval sends $\xi$ to $x_j + \xi(x_{j+1} - x_j)$. -/
@[simp]
theorem affineMap_apply (x : ℕ → ℝ) (j : ℕ) (ξ : ℝ) :
    affineMap x j ξ = x j + ξ * (x (j + 1) - x j) := rfl

/-- The reference coordinate sends $t$ to $(t - x_j)/(x_{j+1} - x_j)$. -/
@[simp]
theorem refCoord_apply (x : ℕ → ℝ) (j : ℕ) (t : ℝ) :
    refCoord x j t = (t - x j) / (x (j + 1) - x j) := rfl

/-- If $x_j \ne x_{j+1}$, the affine map (12.62) inverts the reference coordinate:
$\phi(\xi(t)) = t$. -/
theorem affineMap_refCoord {x : ℕ → ℝ} {j : ℕ} (hj : x j ≠ x (j + 1)) (t : ℝ) :
    affineMap x j (refCoord x j t) = t := by
  have hne : x (j + 1) - x j ≠ 0 := sub_ne_zero.2 (Ne.symm hj)
  simp only [affineMap_apply, refCoord_apply]
  field_simp
  ring

/-- If $x_j \ne x_{j+1}$, the reference coordinate inverts the affine map (12.62):
$\xi(\phi(\xi)) = \xi$. -/
theorem refCoord_affineMap {x : ℕ → ℝ} {j : ℕ} (hj : x j ≠ x (j + 1)) (ξ : ℝ) :
    refCoord x j (affineMap x j ξ) = ξ := by
  have hne : x (j + 1) - x j ≠ 0 := sub_ne_zero.2 (Ne.symm hj)
  simp only [affineMap_apply, refCoord_apply]
  field_simp
  ring

section Reference

variable {n : ℕ} {x : ℕ → ℝ}

/-- **The hat function $\varphi_k$ is the reference function $\hat\varphi_0$ on the panel $I_k$**
(§12.4.5 of [quarteroni2000numerical]). For a partition of $[a, b]$ and $k < n$,
$$\varphi_k(t) = \hat\varphi_0(\xi(t)) \quad \text{for } x_k \le t \le x_{k+1},$$ where $\xi$ is
the reference coordinate of the panel $[x_k, x_{k+1}]$. -/
theorem hatFun_eq_referenceHat_zero (hx : IsIntervalPartition a b n x) {k : ℕ} (hk : k < n)
    {t : ℝ} (h1 : x k ≤ t) (h2 : t ≤ x (k + 1)) :
    hatFun n x k t = referenceHat 0 (refCoord x k t) := by
  have hne : x (k + 1) - x k ≠ 0 := by have := hx.step k hk; linarith
  rw [hatFun_eq_of_left hx hk h1 h2, referenceHat]
  simp only [Matrix.cons_val_zero, refCoord_apply]
  field_simp
  ring

/-- **The hat function $\varphi_{k+1}$ is the reference function $\hat\varphi_1$ on the panel
$I_k$** (§12.4.5 of [quarteroni2000numerical]). For a partition of $[a, b]$ and $k < n$,
$\varphi_{k+1}(t) = \hat\varphi_1(\xi(t))$ for $x_k \le t \le x_{k+1}$, where $\xi$ is the
reference coordinate of the panel $[x_k, x_{k+1}]$. -/
theorem hatFun_eq_referenceHat_one (hx : IsIntervalPartition a b n x) {k : ℕ} (hk : k < n)
    {t : ℝ} (h1 : x k ≤ t) (h2 : t ≤ x (k + 1)) :
    hatFun n x (k + 1) t = referenceHat 1 (refCoord x k t) := by
  rw [hatFun_eq_of_right hx hk h1 h2]
  simp [referenceHat]

end Reference

/-- **The hierarchical basis (12.66) is linearly independent** (§12.4.5 of
[quarteroni2000numerical]): the functions $\hat\psi_0$, $\hat\psi_1$, $\hat\psi_2$ on
$\mathbb{R}$ are linearly independent.

The combination $\alpha_0 \hat\psi_0 + \alpha_1 \hat\psi_1 + \alpha_2 \hat\psi_2 = \alpha_0 +
\xi(\alpha_1 - \alpha_0 + \alpha_2) - \alpha_1 \xi^2$ vanishes identically only for
$\alpha_0 = \alpha_1 = \alpha_2 = 0$, as the evaluations at $\xi = 0$, $1$ and $1/2$ in the
source show. -/
theorem referenceHierarchical_linearIndependent :
    LinearIndependent ℝ referenceHierarchical := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 := congrFun hg 0
  have h1 := congrFun hg 1
  have h2 := congrFun hg (1 / 2)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three,
    referenceHierarchical, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply] at h0 h1 h2
  norm_num at h0 h1 h2
  fin_cases i <;> simp <;> linarith

/-! ### The piecewise linear interpolation operator into $H^1(a, b)$ -/

section Interp

variable {n : ℕ} {x : ℕ → ℝ}

/-- **The piecewise linear interpolant** $\Pi_h^1 u$ of §8.3 of [quarteroni2000numerical], as an
element of $H^1(a, b)$. For a partition of $[a, b]$ with $n \ge 1$ and $u \in H^1(a, b)$ with
continuous representative $\tilde u$, $$\Pi_h^1 u = \sum_{i=0}^{n} \tilde u(x_i)\, \varphi_i.$$
-/
noncomputable def lagrangeInterp (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    (u : SobolevInterval 1 a b) : SobolevInterval 1 a b :=
  ∑ i ∈ Finset.range (n + 1), SobolevInterval.rep u (x i) • hatFunction hx hn i

/-- **The interpolant lies in $X_h^1$.** Let $a < b$, let $a = x_0 < \dots < x_n = b$ be a partition
with $n \ge 1$, and let $u \in H^1(a, b)$. Then $\Pi_h^1 u \in X_h^1$. -/
theorem lagrangeInterp_mem_lagrangeSpace (hab : a < b) (hx : IsIntervalPartition a b n x)
    (hn : 1 ≤ n) (u : SobolevInterval 1 a b) :
    lagrangeInterp hx hn u ∈ lagrangeSpace hab n x 1 :=
  Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
    (hatFunction_mem_lagrangeSpace hab hx hn i)

/-- **A combination of the hat functions takes the prescribed values at the nodes.** Let $a < b$,
let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, and let $c_0, \dots, c_n$ be real
numbers. Then the continuous representative of $\sum_{i=0}^{n} c_i \varphi_i$ takes the value
$c_j$ at $x_j$, for every $j \le n$. -/
theorem rep_sum_hatFunction (hab : a < b) (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    (c : ℕ → ℝ) {j : ℕ} (hj : j ≤ n) :
    SobolevInterval.rep (∑ i ∈ Finset.range (n + 1), c i • hatFunction hx hn i) (x j) = c j := by
  have h : SobolevInterval.rep (∑ i ∈ Finset.range (n + 1), c i • hatFunction hx hn i) (x j)
      = SobolevInterval.evalCLM hab ⟨_, node_mem_Icc hx hj⟩
        (∑ i ∈ Finset.range (n + 1), c i • hatFunction hx hn i) := rfl
  rw [h, map_sum]
  simp only [map_smul, smul_eq_mul, SobolevInterval.evalCLM_apply]
  rw [Finset.sum_congr rfl fun i _ ↦ congrArg (c i * ·)
    (rep_hatFunction_node hx hn (i := i) (j := j) hj)]
  simp [Finset.sum_ite_eq' (Finset.range (n + 1)) j, Nat.lt_succ_iff.2 hj]

/-- **The interpolant matches $u$ at the nodes.** Let $a < b$, let $a = x_0 < \dots < x_n = b$ be a
partition with $n \ge 1$, and let $u \in H^1(a, b)$. Then the continuous representatives satisfy
$(\Pi_h^1 u)(x_j) = u(x_j)$ for every $j \le n$. -/
theorem rep_lagrangeInterp_node (hab : a < b) (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    (u : SobolevInterval 1 a b) {j : ℕ} (hj : j ≤ n) :
    SobolevInterval.rep (lagrangeInterp hx hn u) (x j) = SobolevInterval.rep u (x j) :=
  rep_sum_hatFunction hab hx hn _ hj

/-- **A combination of the hat functions lies in $X_h^1$.** Let $a < b$, let
$a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, and let $c_0, \dots, c_n$ be real
numbers. Then $\sum_{i=0}^{n} c_i \varphi_i \in X_h^1$. -/
theorem sum_hatFunction_mem_lagrangeSpace (hab : a < b) (hx : IsIntervalPartition a b n x)
    (hn : 1 ≤ n) (c : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1), c i • hatFunction hx hn i) ∈ lagrangeSpace hab n x 1 :=
  Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
    (hatFunction_mem_lagrangeSpace hab hx hn i)

/-- **The interpolant of an element of $H^1_0(a, b)$ lies in $X_h^{1,0}$.** Let $a < b$, let
$a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, and let $u \in H^1_0(a, b)$. Then
$\Pi_h^1 u \in X_h^{1,0}$, because it vanishes at both endpoints where $u$ does. -/
theorem lagrangeInterp_mem_lagrangeSpaceZero (hab : a < b) (hx : IsIntervalPartition a b n x)
    (hn : 1 ≤ n) {u : SobolevInterval 1 a b} (hu : u ∈ SobolevIntervalZero a b) :
    lagrangeInterp hx hn u ∈ lagrangeSpaceZero hab n x 1 := by
  refine ⟨lagrangeInterp_mem_lagrangeSpace hab hx hn u,
    SobolevIntervalZero.mem_of_rep_eq_zero hab _ ?_ ?_⟩
  · have h := rep_lagrangeInterp_node hab hx hn u (j := 0) (Nat.zero_le n)
    rw [hx.first] at h
    rw [h]
    exact SobolevIntervalZero.rep_left_eq_zero hab hu
  · have h := rep_lagrangeInterp_node hab hx hn u (j := n) le_rfl
    rw [hx.last] at h
    rw [h]
    exact SobolevIntervalZero.rep_right_eq_zero hab hu

/-- The piecewise constant difference quotient of a function $f$ at the nodes,
$\sum_{i=0}^{n} f(x_i)\, \varphi_i'$: on each panel it is the derivative of the piecewise linear
interpolant of $f$. -/
noncomputable def diffQuotFun (n : ℕ) (x : ℕ → ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t ↦ ∑ i ∈ Finset.range (n + 1), f (x i) * hatDerivFun n x i t

/-- For a partition of $[a, b]$ and $k < n$, on the open panel $(x_k, x_{k+1})$ the difference
quotient of $f$ equals $(f(x_{k+1}) - f(x_k))/(x_{k+1} - x_k)$. -/
theorem diffQuotFun_eq (hx : IsIntervalPartition a b n x) {k : ℕ} (hk : k < n) (f : ℝ → ℝ)
    {t : ℝ} (ht : t ∈ Ioo (x k) (x (k + 1))) :
    diffQuotFun n x f t = (f (x (k + 1)) - f (x k)) / (x (k + 1) - x k) := by
  rw [diffQuotFun, Finset.sum_congr rfl fun i _ ↦ congrArg (f (x i) * ·)
    (hatDerivFun_eq_panel hx hk i ht)]
  have hk1 : k ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  have hk2 : k + 1 ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  have key : ∀ i ∈ Finset.range (n + 1),
      f (x i) * (((if i = k + 1 then (1 : ℝ) else 0) - (if i = k then (1 : ℝ) else 0))
          / (x (k + 1) - x k))
        = ((if i = k + 1 then f (x i) else 0) - (if i = k then f (x i) else 0))
          / (x (k + 1) - x k) := by
    intro i _
    split_ifs <;> ring
  rw [Finset.sum_congr rfl key, ← Finset.sum_div, Finset.sum_sub_distrib]
  simp [Finset.sum_ite_eq', hk1, hk2]

/-- The difference quotient of a function at the nodes is measurable. -/
theorem measurable_diffQuotFun (n : ℕ) (x : ℕ → ℝ) (f : ℝ → ℝ) :
    Measurable (diffQuotFun n x f) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_const.mul (measurable_hatDerivFun n x i)

/-- For a partition of $[a, b]$ with $n \ge 1$ and $u \in H^1(a, b)$, the weak derivative of
$\Pi_h^1 u$ equals almost everywhere on $(a, b)$ the difference quotient of the continuous
representative of $u$. -/
theorem coeFn_deriv_lagrangeInterp (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    (u : SobolevInterval 1 a b) :
    ⇑(SobolevInterval.deriv (lagrangeInterp hx hn u) 1)
      =ᵐ[volume.restrict (Ioo a b)] diffQuotFun n x (SobolevInterval.rep u) := by
  have hderivL : ∀ v : SobolevInterval 1 a b,
      SobolevInterval.deriv v 1 = SobolevInterval.derivL 1 a b 1 v := fun _ ↦ rfl
  have hsum : SobolevInterval.deriv (lagrangeInterp hx hn u) 1
      = ∑ i ∈ Finset.range (n + 1), SobolevInterval.rep u (x i)
        • SobolevInterval.deriv (hatFunction hx hn i) 1 := by
    rw [hderivL, lagrangeInterp, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, ← hderivL]
  rw [hsum]
  have hcoe := Lp.coeFn_sum (Finset.range (n + 1))
    (fun i ↦ SobolevInterval.rep u (x i) • SobolevInterval.deriv (hatFunction hx hn i) 1)
  have hall : ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ i ∈ Finset.range (n + 1),
      (SobolevInterval.rep u (x i) • SobolevInterval.deriv (hatFunction hx hn i) 1) t
        = SobolevInterval.rep u (x i) * hatDerivFun n x i t :=
    (Filter.eventually_all_finset _).2 fun i _ ↦ by
      filter_upwards [Lp.coeFn_smul (SobolevInterval.rep u (x i))
        (SobolevInterval.deriv (hatFunction hx hn i) 1),
        coeFn_deriv_hatFunction_one hx hn i] with t h1 h2
      rw [h1, Pi.smul_apply, smul_eq_mul, h2]
  filter_upwards [hcoe, hall] with t h1 h2
  rw [h1, diffQuotFun]
  exact Finset.sum_congr rfl h2

/-- **The interpolation estimate in the $H^1$ seminorm for $X_h^1$** ((8.27) and Theorem 8.3 of
[quarteroni2000numerical] at $k = 1$, $m = 1$, with the constant $1$). Let $a < b$, let
$a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$ whose panels have length at most $h$,
and let $u \in H^2(a, b)$. Then $$|u - \Pi_h^1 u|_{H^1(a, b)} \le h\, |u|_{H^2(a, b)}.$$

On the left $u$ is read in $H^1(a, b)$ through `SobolevInterval.inclusionCLM`, and the seminorm
$|v|_{H^m(a, b)}$ is the $L^2$ norm of $v^{(m)}$ (`SobolevInterval.seminorm`). The proof reads
`integral_sq_deriv_sub_piecewiseLinearInterpCLM_le` through the weak derivative of
`FiniteElement.lagrangeInterp`, which is the difference quotient on each panel. -/
theorem seminorm_sub_lagrangeInterp_le (hab : a < b) (hx : IsIntervalPartition a b n x)
    (hn : 1 ≤ n) {h : ℝ} (hmesh : ∀ k < n, x (k + 1) - x k ≤ h) (u : SobolevInterval 2 a b) :
    SobolevInterval.seminorm 1 a b (SobolevInterval.inclusionCLM 1 a b u
        - lagrangeInterp hx hn (SobolevInterval.inclusionCLM 1 a b u))
      ≤ h * SobolevInterval.seminorm 2 a b u := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  set u₁ := SobolevInterval.inclusionCLM 1 a b u with hu₁
  obtain ⟨f, hf, hae, hftc⟩ := SobolevInterval.exists_contDiff_ae_eq hab u
  have hfcont : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hftc' : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      deriv f t - deriv f s = ∫ r in s..t, SobolevInterval.deriv u (Fin.last 2) r := by
    simpa only [iteratedDeriv_one] using hftc
  -- the continuous representative of `u₁` is `f`
  have hfn : SobolevInterval.fn u₁ =ᵐ[volume.restrict (Ioo a b)] f := by
    rw [hu₁, SobolevInterval.fn_inclusionCLM]
    have h0 := hae 0
    simpa [SobolevInterval.deriv_zero] using h0
  have hrep : EqOn (SobolevInterval.rep u₁) f (Icc a b) :=
    SobolevInterval.rep_eq_of_continuousOn hab u₁ hf.continuous.continuousOn hfn
  have hderiv : ⇑(SobolevInterval.deriv u₁ 1) =ᵐ[volume.restrict (Ioo a b)] deriv f := by
    rw [hu₁, SobolevInterval.deriv_inclusionCLM]
    have h1 := hae 1
    simpa using h1
  have hdq : diffQuotFun (N + 1) x (SobolevInterval.rep u₁) = diffQuotFun (N + 1) x f := by
    funext t
    exact Finset.sum_congr rfl fun i hi ↦ by
      rw [hrep (node_mem_Icc hx (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))]
  -- integrability of the panel integrand
  have hint : ∀ k < N + 1, IntervalIntegrable
      (fun t ↦ (deriv f t - diffQuotFun (N + 1) x f t) ^ 2) volume (x k) (x (k + 1)) := by
    intro k hk
    have hlt := hx.step k hk
    have hcont : Continuous fun t ↦
        (deriv f t - (f (x (k + 1)) - f (x k)) / (x (k + 1) - x k)) ^ 2 :=
      (hfcont.sub continuous_const).pow 2
    refine (hcont.intervalIntegrable _ _).congr_uIoo ?_
    intro t ht
    rw [uIoo_of_le hlt.le] at ht
    dsimp only
    rw [diffQuotFun_eq hx hk f ht]
  -- the subtype form of the partition
  set y : ℕ → Icc a b := fun j ↦ ⟨x (min j (N + 1)), node_mem_Icc hx (min_le_right _ _)⟩ with hy
  have hyval : ∀ j ≤ N + 1, (y j : ℝ) = x j := fun j hj ↦ by simp [hy, min_eq_left hj]
  have hstep : ∀ i ≤ N, (y i : ℝ) < (y (i + 1) : ℝ) := fun i hi ↦ by
    rw [hyval i (by omega), hyval (i + 1) (by omega)]
    exact hx.step i (by omega)
  have hfirst : (y 0 : ℝ) = a := by rw [hyval 0 (by omega)]; exact hx.first
  have hlast : (y (N + 1) : ℝ) = b := by rw [hyval (N + 1) le_rfl]; exact hx.last
  have hmesh' : ∀ j ≤ N, (y (j + 1) : ℝ) - (y j : ℝ) ≤ h := fun j hj ↦ by
    rw [hyval j (by omega), hyval (j + 1) (by omega)]
    exact hmesh j (by omega)
  have key := integral_sq_deriv_sub_piecewiseLinearInterpCLM_le
    ⟨fun i hi ↦ hstep i (by omega), hfirst, hlast⟩ hmesh' hf
    (SobolevInterval.intervalIntegrable_deriv hab.le u (Fin.last 2))
    (SobolevInterval.intervalIntegrable_deriv_sq hab.le u (Fin.last 2)) hftc'
  -- the square of the seminorm
  have hsq : SobolevInterval.seminorm 1 a b (u₁ - lagrangeInterp hx hn u₁) ^ 2
      ≤ h ^ 2 * SobolevInterval.seminorm 2 a b u ^ 2 := by
    rw [SobolevInterval.seminorm_sq_eq_integral hab.le,
      SobolevInterval.seminorm_sq_eq_integral hab.le]
    have e1 : ∫ t in a..b,
          SobolevInterval.deriv (u₁ - lagrangeInterp hx hn u₁) (Fin.last 1) t ^ 2
        = ∫ t in a..b, (deriv f t - diffQuotFun (N + 1) x f t) ^ 2 := by
      refine intervalIntegral_congr_ae_Ioo ?_ (right_mem_Icc.2 hab.le)
      filter_upwards [Lp.coeFn_sub (SobolevInterval.deriv u₁ 1)
        (SobolevInterval.deriv (lagrangeInterp hx hn u₁) 1), hderiv,
        coeFn_deriv_lagrangeInterp hx hn u₁] with t k1 k2 k3
      have e : SobolevInterval.deriv (u₁ - lagrangeInterp hx hn u₁) (Fin.last 1)
          = SobolevInterval.deriv u₁ 1 - SobolevInterval.deriv (lagrangeInterp hx hn u₁) 1 := rfl
      rw [e, k1, Pi.sub_apply, k2, k3, hdq]
    rw [e1]
    have hsplit := intervalIntegral.sum_integral_adjacent_intervals (a := x) (n := N + 1)
      (f := fun t ↦ (deriv f t - diffQuotFun (N + 1) x f t) ^ 2) (μ := volume) hint
    rw [hx.first, hx.last] at hsplit
    rw [← hsplit]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun j hj ↦ ?_)) key
    have hjn : j < N + 1 := Finset.mem_range.1 hj
    have hlt := hx.step j hjn
    rw [hyval j (by omega), hyval (j + 1) (by omega)]
    refine intervalIntegral.integral_congr_Ioo_of_le hlt.le fun t ht ↦ ?_
    rw [diffQuotFun_eq hx hjn f ht]
  -- take square roots
  have h0 : 0 ≤ h := by
    have e1 := hx.step 0 (by omega : 0 < N + 1)
    have e2 := hmesh 0 (by omega : 0 < N + 1)
    linarith
  have hB : 0 ≤ h * SobolevInterval.seminorm 2 a b u :=
    mul_nonneg h0 (apply_nonneg (SobolevInterval.seminorm 2 a b) u)
  rw [show h ^ 2 * SobolevInterval.seminorm 2 a b u ^ 2
      = (h * SobolevInterval.seminorm 2 a b u) ^ 2 by ring] at hsq
  exact (pow_le_pow_iff_left₀
    (apply_nonneg (SobolevInterval.seminorm 1 a b) (u₁ - lagrangeInterp hx hn u₁)) hB
    two_ne_zero).1 hsq


/-- **The approximation property of $X_h^{1,0}$** that the Aubin–Nitsche estimate uses. Let $a < b$,
let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$ whose panels have length at most
$h$, and let $\Phi \in H^2(a, b)$ with $\Phi \in H^1_0(a, b)$. Then there is $v \in X_h^{1,0}$
with $$|\Phi - v|_{H^1(a, b)} \le h\, \|\Phi\|_{H^2(a, b)}.$$

The element $v$ is the piecewise linear interpolant $\Pi_h^1 \Phi$. -/
theorem exists_mem_lagrangeSpaceZero_seminorm_sub_le (hab : a < b)
    (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) {h : ℝ} (hmesh : ∀ k < n, x (k + 1) - x k ≤ h)
    (Φ : SobolevInterval 2 a b)
    (hΦ : SobolevInterval.inclusionCLM 1 a b Φ ∈ SobolevIntervalZero a b) :
    ∃ v ∈ lagrangeSpaceZero hab n x 1,
      SobolevInterval.seminorm 1 a b (SobolevInterval.inclusionCLM 1 a b Φ - v) ≤ h * ‖Φ‖ := by
  refine ⟨lagrangeInterp hx hn (SobolevInterval.inclusionCLM 1 a b Φ),
    lagrangeInterp_mem_lagrangeSpaceZero hab hx hn hΦ, ?_⟩
  refine (seminorm_sub_lagrangeInterp_le hab hx hn hmesh Φ).trans ?_
  have h0 : 0 ≤ h := by
    have e1 := hx.step 0 hn
    have e2 := hmesh 0 hn
    linarith
  exact mul_le_mul_of_nonneg_left (SobolevInterval.seminorm_le_norm Φ) h0

end Interp


/-!
### The quadratic element $X_h^2$

The shape functions of (12.63)–(12.64) of [quarteroni2000numerical] are built like the hat
functions: first as functions $\mathbb{R} \to \mathbb{R}$, and only then as elements of $H^1(a, b)$.
The nodes are the source's relabelling $x_0 < x_1 < \dots < x_{2n}$. The even-indexed nodes are the
endpoints of the $n$ elements $[x_{2m}, x_{2m+2}]$, and the odd-indexed nodes are their interior
nodes; `FiniteElement.evenNodes` extracts the element partition. The formulas (12.63)–(12.64) are
the local Lagrange bases of the three nodes of an element, so nothing below assumes that the
interior node is the midpoint. That hypothesis enters only in the reference description (12.65).

The ramp construction of the hat functions does not apply here: the sum of the two quadratic
branches of an even-indexed shape function is not $1$ on an element, because the bubble takes up the
difference. Instead each branch is clamped to its element. `FiniteElement.quadFall` is $1$ to the
left of its element and $0$ to its right, and `FiniteElement.quadRise` is the other way round. The
shape function at an even node is the product of the rise across the element on its left and the
fall across the element on its right. This product is $\hat\varphi_2$ on the one element,
$\hat\varphi_0$ on the other, and $0$ elsewhere. The shape function at an odd node is the bubble,
clamped to vanish outside its element.

The element of $H^1(a, b)$ comes from `FiniteElement.exists_mem_lagrangeSpace`: a continuous
piecewise polynomial is the continuous representative of an element of $X_h^2$. The embedding
$H^1(a, b) \hookrightarrow C([a, b])$ is injective, so the element is unique, and every statement
about its nodal values is a statement about `FiniteElement.quadShapeFun`.
-/

/-- The quadratic Lagrange basis polynomial at $p$ for the three nodes $p$, $q$, $r$: $$\frac{(X -
q)(X - r)}{(p - q)(p - r)},$$ written by its coefficients. If $p = q$ or $p = r$, the division
by zero makes it the zero polynomial. -/
noncomputable def quadPoly (p q r : ℝ) : Polynomial ℝ :=
  Polynomial.C ((p - q) * (p - r))⁻¹ * Polynomial.X ^ 2 +
    Polynomial.C (-(q + r) * ((p - q) * (p - r))⁻¹) * Polynomial.X +
    Polynomial.C (q * r * ((p - q) * (p - r))⁻¹)

/-- The quadratic Lagrange basis function at $p$ for the three nodes $p$, $q$, $r$:
$t \mapsto (t - q)(t - r)/((p - q)(p - r))$. If $p = q$ or $p = r$, the division by zero makes
it the zero function. -/
noncomputable def quadLagrangeFun (p q r : ℝ) : ℝ → ℝ :=
  fun t ↦ (t - q) * (t - r) / ((p - q) * (p - r))

/-- The quadratic Lagrange basis polynomial evaluates to the quadratic Lagrange basis function. -/
theorem quadPoly_eval (p q r t : ℝ) : (quadPoly p q r).eval t = quadLagrangeFun p q r t := by
  simp only [quadPoly, quadLagrangeFun, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, div_eq_mul_inv]
  ring

/-- The quadratic Lagrange basis polynomial has degree at most $2$. -/
theorem quadPoly_degree_le (p q r : ℝ) : (quadPoly p q r).degree ≤ 2 :=
  Polynomial.degree_quadratic_le

/-- If $p \ne q$ and $p \ne r$, the quadratic Lagrange basis function at $p$ for the nodes $p$, $q$,
$r$ takes the value $1$ at $p$. -/
theorem quadLagrangeFun_self {p q r : ℝ} (hq : p ≠ q) (hr : p ≠ r) :
    quadLagrangeFun p q r p = 1 := by
  rw [quadLagrangeFun, div_self]
  exact mul_ne_zero (sub_ne_zero.2 hq) (sub_ne_zero.2 hr)

/-- The quadratic Lagrange basis function at $p$ for the nodes $p$, $q$, $r$ vanishes at $q$. -/
theorem quadLagrangeFun_left (p q r : ℝ) : quadLagrangeFun p q r q = 0 := by
  simp [quadLagrangeFun]

/-- The quadratic Lagrange basis function at $p$ for the nodes $p$, $q$, $r$ vanishes at $r$. -/
theorem quadLagrangeFun_right (p q r : ℝ) : quadLagrangeFun p q r r = 0 := by
  simp [quadLagrangeFun]

/-- The quadratic Lagrange basis function is continuous. -/
theorem continuous_quadLagrangeFun (p q r : ℝ) : Continuous (quadLagrangeFun p q r) := by
  unfold quadLagrangeFun
  fun_prop


/-! ### The clamped pieces on an element -/

/-- The point $t$ clamped into the element $[x_{2k}, x_{2k+2}]$ of the quadratic mesh:
$\min(\max(t, x_{2k}), x_{2k+2})$. -/
noncomputable def quadClamp (x : ℕ → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  min (max t (x (2 * k))) (x (2 * k + 2))

/-- If $x_{2k} \le x_{2k+2}$ and $t \le x_{2k}$, then $t$ clamped into $[x_{2k}, x_{2k+2}]$ is
$x_{2k}$. -/
theorem quadClamp_of_le {x : ℕ → ℝ} {k : ℕ} {t : ℝ} (hx : x (2 * k) ≤ x (2 * k + 2))
    (ht : t ≤ x (2 * k)) : quadClamp x k t = x (2 * k) := by
  rw [quadClamp, max_eq_right ht, min_eq_left hx]

/-- If $x_{2k} \le t \le x_{2k+2}$, then $t$ clamped into $[x_{2k}, x_{2k+2}]$ is $t$. -/
theorem quadClamp_of_mem {x : ℕ → ℝ} {k : ℕ} {t : ℝ} (h1 : x (2 * k) ≤ t)
    (h2 : t ≤ x (2 * k + 2)) : quadClamp x k t = t := by
  rw [quadClamp, max_eq_left h1, min_eq_left h2]

/-- If $x_{2k} \le x_{2k+2}$ and $t \ge x_{2k+2}$, then $t$ clamped into $[x_{2k}, x_{2k+2}]$ is
$x_{2k+2}$. -/
theorem quadClamp_of_ge {x : ℕ → ℝ} {k : ℕ} {t : ℝ} (hx : x (2 * k) ≤ x (2 * k + 2))
    (ht : x (2 * k + 2) ≤ t) : quadClamp x k t = x (2 * k + 2) := by
  rw [quadClamp, max_eq_left (hx.trans ht), min_eq_right ht]

/-- Clamping into an element is continuous. -/
theorem continuous_quadClamp (x : ℕ → ℝ) (k : ℕ) : Continuous (quadClamp x k) :=
  (continuous_id.max continuous_const).min continuous_const

/-- The shape function $\hat\varphi_0$ on the element $k$: the quadratic that is $1$ at $x_{2k}$ and
$0$ at $x_{2k+1}$ and $x_{2k+2}$, evaluated at the point clamped into $[x_{2k}, x_{2k+2}]$. For
increasing nodes it is $1$ to the left of the element and $0$ to its right. -/
noncomputable def quadFall (x : ℕ → ℝ) (k : ℕ) : ℝ → ℝ :=
  fun t ↦ quadLagrangeFun (x (2 * k)) (x (2 * k + 1)) (x (2 * k + 2)) (quadClamp x k t)

/-- The bubble $\hat\varphi_1$ on the element $k$: the quadratic that is $1$ at the interior node
$x_{2k+1}$ and $0$ at $x_{2k}$ and $x_{2k+2}$, evaluated at the point clamped into
$[x_{2k}, x_{2k+2}]$. It is $0$ outside the element. -/
noncomputable def quadBubble (x : ℕ → ℝ) (k : ℕ) : ℝ → ℝ :=
  fun t ↦ quadLagrangeFun (x (2 * k + 1)) (x (2 * k)) (x (2 * k + 2)) (quadClamp x k t)

/-- The shape function $\hat\varphi_2$ on the element $k$: the quadratic that is $1$ at $x_{2k+2}$
and $0$ at $x_{2k}$ and $x_{2k+1}$, evaluated at the point clamped into $[x_{2k}, x_{2k+2}]$.
For increasing nodes it is $0$ to the left of the element and $1$ to its right. -/
noncomputable def quadRise (x : ℕ → ℝ) (k : ℕ) : ℝ → ℝ :=
  fun t ↦ quadLagrangeFun (x (2 * k + 2)) (x (2 * k)) (x (2 * k + 1)) (quadClamp x k t)

/-- The clamped function $\hat\varphi_0$ of an element is continuous. -/
theorem continuous_quadFall (x : ℕ → ℝ) (k : ℕ) : Continuous (quadFall x k) :=
  (continuous_quadLagrangeFun _ _ _).comp (continuous_quadClamp x k)

/-- The clamped bubble of an element is continuous. -/
theorem continuous_quadBubble (x : ℕ → ℝ) (k : ℕ) : Continuous (quadBubble x k) :=
  (continuous_quadLagrangeFun _ _ _).comp (continuous_quadClamp x k)

/-- The clamped function $\hat\varphi_2$ of an element is continuous. -/
theorem continuous_quadRise (x : ℕ → ℝ) (k : ℕ) : Continuous (quadRise x k) :=
  (continuous_quadLagrangeFun _ _ _).comp (continuous_quadClamp x k)

section Element

variable {x : ℕ → ℝ} {k : ℕ}

/-- If $x_{2k} < x_{2k+1} < x_{2k+2}$, the three nodes of the element are pairwise distinct. -/
theorem quad_ne (h1 : x (2 * k) < x (2 * k + 1)) (h2 : x (2 * k + 1) < x (2 * k + 2)) :
    x (2 * k) ≠ x (2 * k + 1) ∧ x (2 * k) ≠ x (2 * k + 2) ∧ x (2 * k + 1) ≠ x (2 * k + 2) :=
  ⟨h1.ne, (h1.trans h2).ne, h2.ne⟩

/-- On the element $[x_{2k}, x_{2k+2}]$ the clamped function $\hat\varphi_0$ is the quadratic
Lagrange basis function at $x_{2k}$ for the nodes $x_{2k}$, $x_{2k+1}$, $x_{2k+2}$. -/
theorem quadFall_of_mem {t : ℝ} (h1 : x (2 * k) ≤ t) (h2 : t ≤ x (2 * k + 2)) :
    quadFall x k t = quadLagrangeFun (x (2 * k)) (x (2 * k + 1)) (x (2 * k + 2)) t := by
  rw [quadFall, quadClamp_of_mem h1 h2]

/-- On the element $[x_{2k}, x_{2k+2}]$ the clamped bubble is the quadratic Lagrange basis function
at $x_{2k+1}$ for the nodes $x_{2k+1}$, $x_{2k}$, $x_{2k+2}$. -/
theorem quadBubble_of_mem {t : ℝ} (h1 : x (2 * k) ≤ t) (h2 : t ≤ x (2 * k + 2)) :
    quadBubble x k t = quadLagrangeFun (x (2 * k + 1)) (x (2 * k)) (x (2 * k + 2)) t := by
  rw [quadBubble, quadClamp_of_mem h1 h2]

/-- On the element $[x_{2k}, x_{2k+2}]$ the clamped function $\hat\varphi_2$ is the quadratic
Lagrange basis function at $x_{2k+2}$ for the nodes $x_{2k+2}$, $x_{2k}$, $x_{2k+1}$. -/
theorem quadRise_of_mem {t : ℝ} (h1 : x (2 * k) ≤ t) (h2 : t ≤ x (2 * k + 2)) :
    quadRise x k t = quadLagrangeFun (x (2 * k + 2)) (x (2 * k)) (x (2 * k + 1)) t := by
  rw [quadRise, quadClamp_of_mem h1 h2]

/-- If $x_{2k} < x_{2k+1} < x_{2k+2}$, the clamped function $\hat\varphi_0$ of the element equals
$1$ at every $t \le x_{2k}$. -/
theorem quadFall_of_le {t : ℝ} (h1 : x (2 * k) < x (2 * k + 1))
    (h2 : x (2 * k + 1) < x (2 * k + 2)) (ht : t ≤ x (2 * k)) : quadFall x k t = 1 := by
  rw [quadFall, quadClamp_of_le (h1.trans h2).le ht,
    quadLagrangeFun_self h1.ne (h1.trans h2).ne]

/-- If $x_{2k} \le x_{2k+2}$, the clamped function $\hat\varphi_0$ of the element vanishes at every
$t \ge x_{2k+2}$. -/
theorem quadFall_of_ge {t : ℝ} (h : x (2 * k) ≤ x (2 * k + 2)) (ht : x (2 * k + 2) ≤ t) :
    quadFall x k t = 0 := by
  rw [quadFall, quadClamp_of_ge h ht, quadLagrangeFun_right]

/-- If $x_{2k} \le x_{2k+2}$, the clamped function $\hat\varphi_2$ of the element vanishes at every
$t \le x_{2k}$. -/
theorem quadRise_of_le {t : ℝ} (h : x (2 * k) ≤ x (2 * k + 2)) (ht : t ≤ x (2 * k)) :
    quadRise x k t = 0 := by
  rw [quadRise, quadClamp_of_le h ht, quadLagrangeFun_left]

/-- If $x_{2k} < x_{2k+1} < x_{2k+2}$, the clamped function $\hat\varphi_2$ of the element equals
$1$ at every $t \ge x_{2k+2}$. -/
theorem quadRise_of_ge {t : ℝ} (h1 : x (2 * k) < x (2 * k + 1))
    (h2 : x (2 * k + 1) < x (2 * k + 2)) (ht : x (2 * k + 2) ≤ t) : quadRise x k t = 1 := by
  rw [quadRise, quadClamp_of_ge (h1.trans h2).le ht,
    quadLagrangeFun_self (h1.trans h2).ne' h2.ne']

/-- If $x_{2k} \le x_{2k+2}$, the clamped bubble of the element vanishes at every $t \le x_{2k}$. -/
theorem quadBubble_of_le {t : ℝ} (h : x (2 * k) ≤ x (2 * k + 2)) (ht : t ≤ x (2 * k)) :
    quadBubble x k t = 0 := by
  rw [quadBubble, quadClamp_of_le h ht, quadLagrangeFun_left]

/-- If $x_{2k} \le x_{2k+2}$, the clamped bubble of the element vanishes at every $t \ge x_{2k+2}$.
-/
theorem quadBubble_of_ge {t : ℝ} (h : x (2 * k) ≤ x (2 * k + 2)) (ht : x (2 * k + 2) ≤ t) :
    quadBubble x k t = 0 := by
  rw [quadBubble, quadClamp_of_ge h ht, quadLagrangeFun_right]

end Element


/-! ### The global shape functions of $X_h^2$ -/

/-- The left factor of the shape function at the even node $x_{2k}$: the constant $1$ for $k = 0$,
the clamped function $\hat\varphi_2$ of the element $k - 1$ for $1 \le k \le n$, and the
constant $0$ for $k > n$. -/
noncomputable def quadStepL (n : ℕ) (x : ℕ → ℝ) (k : ℕ) : ℝ → ℝ :=
  if k = 0 then fun _ ↦ 1 else if k ≤ n then quadRise x (k - 1) else fun _ ↦ 0

/-- The right factor of the shape function at the even node $x_{2k}$: the clamped function
$\hat\varphi_0$ of the element $k$ for $k < n$, and the constant $1$ for $k \ge n$. -/
noncomputable def quadStepR (n : ℕ) (x : ℕ → ℝ) (k : ℕ) : ℝ → ℝ :=
  if k < n then quadFall x k else fun _ ↦ 1

/-- The shape function at the odd node $x_{2k+1}$: the clamped bubble of the element $k$ for
$k < n$, and the constant $0$ for $k \ge n$. -/
noncomputable def quadStepB (n : ℕ) (x : ℕ → ℝ) (k : ℕ) : ℝ → ℝ :=
  if k < n then quadBubble x k else fun _ ↦ 0

/-- **The shape functions of $X_h^2$** of (12.63)–(12.64) of [quarteroni2000numerical], as functions
$\mathbb{R} \to \mathbb{R}$, for a quadratic mesh $x_0 < x_1 < \dots < x_{2n}$. The shape
function $\varphi_{2k}$ at an even node is the product of the left factor
`FiniteElement.quadStepL` and the right factor `FiniteElement.quadStepR` at $k$, and the shape
function $\varphi_{2k+1}$ at an odd node is `FiniteElement.quadStepB` at $k$.

On each element $[x_{2m}, x_{2m+2}]$ the shape functions of its three nodes are the local
quadratic Lagrange basis functions, and all other shape functions vanish there. -/
noncomputable def quadShapeFun (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : ℝ → ℝ :=
  fun t ↦ if i % 2 = 0 then quadStepL n x (i / 2) t * quadStepR n x (i / 2) t
    else quadStepB n x (i / 2) t

/-- The left factor at $k = 0$ is the constant $1$. -/
theorem quadStepL_zero (n : ℕ) (x : ℕ → ℝ) : quadStepL n x 0 = fun _ ↦ 1 := by simp [quadStepL]

/-- If $k + 1 \le n$, the left factor at $k + 1$ is the clamped function $\hat\varphi_2$ of the
element $k$. -/
theorem quadStepL_succ {n k : ℕ} (x : ℕ → ℝ) (hk : k + 1 ≤ n) :
    quadStepL n x (k + 1) = quadRise x k := by simp [quadStepL, hk]

/-- If $k > n$, the left factor at $k$ is the constant $0$. -/
theorem quadStepL_of_lt {n k : ℕ} (x : ℕ → ℝ) (hk : n < k) : quadStepL n x k = fun _ ↦ 0 := by
  rw [quadStepL]
  have hk0 : ¬ k = 0 := by omega
  simp [hk0, Nat.not_le.2 hk]

/-- If $k < n$, the right factor at $k$ is the clamped function $\hat\varphi_0$ of the element $k$.
-/
theorem quadStepR_of_lt {n k : ℕ} (x : ℕ → ℝ) (hk : k < n) : quadStepR n x k = quadFall x k := by
  simp [quadStepR, hk]

/-- If $k \ge n$, the right factor at $k$ is the constant $1$. -/
theorem quadStepR_of_le {n k : ℕ} (x : ℕ → ℝ) (hk : n ≤ k) : quadStepR n x k = fun _ ↦ 1 := by
  simp [quadStepR, Nat.not_lt.2 hk]

/-- If $k < n$, the odd shape function at $k$ is the clamped bubble of the element $k$. -/
theorem quadStepB_of_lt {n k : ℕ} (x : ℕ → ℝ) (hk : k < n) :
    quadStepB n x k = quadBubble x k := by simp [quadStepB, hk]

/-- If $k \ge n$, the odd shape function at $k$ is the constant $0$. -/
theorem quadStepB_of_le {n k : ℕ} (x : ℕ → ℝ) (hk : n ≤ k) :
    quadStepB n x k = fun _ ↦ 0 := by simp [quadStepB, Nat.not_lt.2 hk]

/-- The left factor is continuous. -/
theorem continuous_quadStepL (n : ℕ) (x : ℕ → ℝ) (k : ℕ) : Continuous (quadStepL n x k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [quadStepL_zero]; exact continuous_const
  rcases le_or_gt k n with hk | hk
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [quadStepL_succ x hk]; exact continuous_quadRise x k'
  · rw [quadStepL_of_lt x hk]; exact continuous_const

/-- The right factor is continuous. -/
theorem continuous_quadStepR (n : ℕ) (x : ℕ → ℝ) (k : ℕ) : Continuous (quadStepR n x k) := by
  rcases lt_or_ge k n with hk | hk
  · rw [quadStepR_of_lt x hk]; exact continuous_quadFall x k
  · rw [quadStepR_of_le x hk]; exact continuous_const

/-- The odd shape function is continuous. -/
theorem continuous_quadStepB (n : ℕ) (x : ℕ → ℝ) (k : ℕ) : Continuous (quadStepB n x k) := by
  rcases lt_or_ge k n with hk | hk
  · rw [quadStepB_of_lt x hk]; exact continuous_quadBubble x k
  · rw [quadStepB_of_le x hk]; exact continuous_const

/-- The shape function at the even node $x_{2k}$ is the product of the left and the right factor at
$k$. -/
theorem quadShapeFun_even (n : ℕ) (x : ℕ → ℝ) (k : ℕ) (t : ℝ) :
    quadShapeFun n x (2 * k) t = quadStepL n x k t * quadStepR n x k t := by
  have h1 : (2 * k) % 2 = 0 := by omega
  have h2 : (2 * k) / 2 = k := by omega
  simp only [quadShapeFun, h1, h2, reduceIte]

/-- The shape function at the even node $x_{2k+2}$ is the product of the left and the right factor
at $k + 1$. -/
theorem quadShapeFun_even_succ (n : ℕ) (x : ℕ → ℝ) (k : ℕ) (t : ℝ) :
    quadShapeFun n x (2 * k + 2) t = quadStepL n x (k + 1) t * quadStepR n x (k + 1) t := by
  have h1 : (2 * k + 2) % 2 = 0 := by omega
  have h2 : (2 * k + 2) / 2 = k + 1 := by omega
  simp only [quadShapeFun, h1, h2, reduceIte]

/-- The shape function at the odd node $x_{2k+1}$ is `FiniteElement.quadStepB` at $k$. -/
theorem quadShapeFun_odd (n : ℕ) (x : ℕ → ℝ) (k : ℕ) (t : ℝ) :
    quadShapeFun n x (2 * k + 1) t = quadStepB n x k t := by
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  simp only [quadShapeFun, h1, h2]
  norm_num

/-- Every shape function of $X_h^2$ is continuous. -/
theorem continuous_quadShapeFun (n : ℕ) (x : ℕ → ℝ) (i : ℕ) :
    Continuous (quadShapeFun n x i) := by
  rcases Nat.even_or_odd i with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hij : i = 2 * j := by omega
    subst hij
    have he : quadShapeFun n x (2 * j) = fun t ↦ quadStepL n x j t * quadStepR n x j t :=
      funext fun t ↦ quadShapeFun_even n x j t
    rw [he]
    exact (continuous_quadStepL n x j).mul (continuous_quadStepR n x j)
  · have hij : i = 2 * j + 1 := by omega
    subst hij
    have he : quadShapeFun n x (2 * j + 1) = quadStepB n x j :=
      funext fun t ↦ quadShapeFun_odd n x j t
    rw [he]
    exact continuous_quadStepB n x j

/-- Only the $2n + 1$ nodes carry a shape function: for $i > 2n$ the shape function $\varphi_i$ is
the constant $0$. -/
theorem quadShapeFun_of_lt {n : ℕ} (x : ℕ → ℝ) {i : ℕ} (hi : 2 * n < i) :
    quadShapeFun n x i = fun _ ↦ 0 := by
  funext t
  rcases Nat.even_or_odd i with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hij : i = 2 * j := by omega
    subst hij
    rw [quadShapeFun_even, quadStepL_of_lt x (by omega)]
    simp
  · have hij : i = 2 * j + 1 := by omega
    subst hij
    rw [quadShapeFun_odd, quadStepB_of_le x (by omega)]

section Panel

variable {n : ℕ} {x : ℕ → ℝ}

/-- For a quadratic mesh $a = x_0 < \dots < x_{2n} = b$ and $m < n$, on the element
$[x_{2m}, x_{2m+2}]$ the shape function $\varphi_{2m}$ of its left endpoint is the local
Lagrange basis function $\hat\varphi_0$ of (12.63) of [quarteroni2000numerical], the quadratic
at $x_{2m}$ for the nodes $x_{2m}$, $x_{2m+1}$, $x_{2m+2}$. -/
theorem quadShapeFun_even_left (hx : IsIntervalPartition a b (2 * n) x) {m : ℕ} (hm : m < n)
    {t : ℝ} (h1 : x (2 * m) ≤ t) (h2 : t ≤ x (2 * m + 2)) :
    quadShapeFun n x (2 * m) t
      = quadLagrangeFun (x (2 * m)) (x (2 * m + 1)) (x (2 * m + 2)) t := by
  have hL : quadStepL n x m t = 1 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · rw [quadStepL_zero]
    · obtain ⟨m2, rfl⟩ : ∃ m2, m = m2 + 1 := ⟨m - 1, by omega⟩
      rw [quadStepL_succ x (by omega)]
      refine quadRise_of_ge (hx.lt (by omega) (by omega)) (hx.lt (by omega) (by omega)) ?_
      have he : 2 * m2 + 2 = 2 * (m2 + 1) := by ring
      rw [he]; exact h1
  rw [quadShapeFun_even, hL, quadStepR_of_lt x hm, one_mul, quadFall_of_mem h1 h2]

/-- For $m < n$, on the element $[x_{2m}, x_{2m+2}]$ the shape function $\varphi_{2m+1}$ of its
interior node is the bubble $\hat\varphi_1$ of (12.64) of [quarteroni2000numerical], the
quadratic at $x_{2m+1}$ for the nodes $x_{2m+1}$, $x_{2m}$, $x_{2m+2}$. -/
theorem quadShapeFun_midpoint {m : ℕ} (hm : m < n) {t : ℝ} (h1 : x (2 * m) ≤ t)
    (h2 : t ≤ x (2 * m + 2)) :
    quadShapeFun n x (2 * m + 1) t
      = quadLagrangeFun (x (2 * m + 1)) (x (2 * m)) (x (2 * m + 2)) t := by
  rw [quadShapeFun_odd, quadStepB_of_lt x hm, quadBubble_of_mem h1 h2]

/-- For a quadratic mesh $a = x_0 < \dots < x_{2n} = b$ and $m < n$, on the element
$[x_{2m}, x_{2m+2}]$ the shape function $\varphi_{2m+2}$ of its right endpoint is
$\hat\varphi_2$ of (12.63) of [quarteroni2000numerical], the quadratic at $x_{2m+2}$ for the
nodes $x_{2m+2}$, $x_{2m}$, $x_{2m+1}$. -/
theorem quadShapeFun_even_right (hx : IsIntervalPartition a b (2 * n) x) {m : ℕ} (hm : m < n)
    {t : ℝ} (h1 : x (2 * m) ≤ t) (h2 : t ≤ x (2 * m + 2)) :
    quadShapeFun n x (2 * m + 2) t
      = quadLagrangeFun (x (2 * m + 2)) (x (2 * m)) (x (2 * m + 1)) t := by
  have hR : quadStepR n x (m + 1) t = 1 := by
    rcases lt_or_ge (m + 1) n with hm1 | hm1
    · rw [quadStepR_of_lt x hm1]
      refine quadFall_of_le (hx.lt (by omega) (by omega)) (hx.lt (by omega) (by omega)) ?_
      have he : 2 * (m + 1) = 2 * m + 2 := by ring
      rw [he]; exact h2
    · rw [quadStepR_of_le x hm1]
  rw [quadShapeFun_even_succ, quadStepL_succ x (by omega), hR, mul_one, quadRise_of_mem h1 h2]

/-- **The local support of the quadratic shape functions** (§12.4.5 of [quarteroni2000numerical]).
Let $a = x_0 < \dots < x_{2n} = b$ be a quadratic mesh and $m < n$. If
$i \notin \{2m, 2m + 1, 2m + 2\}$, then the shape function $\varphi_i$ vanishes on the element
$[x_{2m}, x_{2m+2}]$. -/
theorem quadShapeFun_eq_zero_of_panel (hx : IsIntervalPartition a b (2 * n) x) {m i : ℕ}
    (hm : m < n) (hne0 : i ≠ 2 * m) (hne1 : i ≠ 2 * m + 1) (hne2 : i ≠ 2 * m + 2)
    {t : ℝ} (ht1 : x (2 * m) ≤ t) (ht2 : t ≤ x (2 * m + 2)) : quadShapeFun n x i t = 0 := by
  rcases lt_or_ge (2 * n) i with hi | hi
  · rw [quadShapeFun_of_lt x hi]
  rcases Nat.even_or_odd i with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hij : i = 2 * j := by omega
    subst hij
    rw [quadShapeFun_even]
    rcases lt_trichotomy j m with h | h | h
    · have hz : quadStepR n x j t = 0 := by
        rw [quadStepR_of_lt x (by omega)]
        refine quadFall_of_ge (hx.mono (by omega) (by omega)) ?_
        exact (hx.mono (show 2 * j + 2 ≤ 2 * m by omega) (by omega)).trans ht1
      rw [hz, mul_zero]
    · omega
    · obtain ⟨j2, rfl⟩ : ∃ j2, j = j2 + 1 := ⟨j - 1, by omega⟩
      have hz : quadStepL n x (j2 + 1) t = 0 := by
        rw [quadStepL_succ x (by omega)]
        refine quadRise_of_le (hx.mono (by omega) (by omega)) (ht2.trans ?_)
        exact hx.mono (show 2 * m + 2 ≤ 2 * j2 by omega) (by omega)
      rw [hz, zero_mul]
  · have hij : i = 2 * j + 1 := by omega
    subst hij
    rw [quadShapeFun_odd, quadStepB_of_lt x (by omega)]
    rcases lt_trichotomy j m with h | h | h
    · refine quadBubble_of_ge (hx.mono (by omega) (by omega)) ?_
      exact (hx.mono (show 2 * j + 2 ≤ 2 * m by omega) (by omega)).trans ht1
    · omega
    · refine quadBubble_of_le (hx.mono (by omega) (by omega)) (ht2.trans ?_)
      exact hx.mono (show 2 * m + 2 ≤ 2 * j by omega) (by omega)

/-- **The Lagrange interpolation property on one element** (§12.4.5 of [quarteroni2000numerical]).
For a quadratic mesh $a = x_0 < \dots < x_{2n} = b$, $m < n$ and a node $x_l$ of the element
$[x_{2m}, x_{2m+2}]$, that is, $2m \le l \le 2m + 2$, every shape function satisfies
$\varphi_i(x_l) = \delta_{il}$. -/
theorem quadShapeFun_apply_node_of_panel (hx : IsIntervalPartition a b (2 * n) x) {m i l : ℕ}
    (hm : m < n) (hl1 : 2 * m ≤ l) (hl2 : l ≤ 2 * m + 2) :
    quadShapeFun n x i (x l) = if i = l then 1 else 0 := by
  have h01 : x (2 * m) < x (2 * m + 1) := hx.step _ (by omega)
  have h12 : x (2 * m + 1) < x (2 * m + 2) := hx.step _ (by omega)
  have ht1 : x (2 * m) ≤ x l := hx.mono hl1 (by omega)
  have ht2 : x l ≤ x (2 * m + 2) := hx.mono hl2 (by omega)
  have hnode : l = 2 * m ∨ l = 2 * m + 1 ∨ l = 2 * m + 2 := by omega
  by_cases hi0 : i = 2 * m
  · subst hi0
    rw [quadShapeFun_even_left hx hm ht1 ht2]
    rcases hnode with rfl | rfl | rfl
    · rw [quadLagrangeFun_self h01.ne (h01.trans h12).ne]; simp
    · rw [quadLagrangeFun_left]; simp
    · rw [quadLagrangeFun_right]; simp
  by_cases hi1 : i = 2 * m + 1
  · subst hi1
    rw [quadShapeFun_midpoint hm ht1 ht2]
    rcases hnode with rfl | rfl | rfl
    · rw [quadLagrangeFun_left]; simp
    · rw [quadLagrangeFun_self h01.ne' h12.ne]; simp
    · rw [quadLagrangeFun_right]; simp
  by_cases hi2 : i = 2 * m + 2
  · subst hi2
    rw [quadShapeFun_even_right hx hm ht1 ht2]
    rcases hnode with rfl | rfl | rfl
    · rw [quadLagrangeFun_left]; simp
    · rw [quadLagrangeFun_right]; simp
    · rw [quadLagrangeFun_self (h01.trans h12).ne' h12.ne']; simp
  · rw [quadShapeFun_eq_zero_of_panel hx hm hi0 hi1 hi2 ht1 ht2]
    have hil : i ≠ l := by rcases hnode with rfl | rfl | rfl <;> omega
    simp [hil]

/-- **The Lagrange interpolation property of the quadratic shape functions** ((12.63)–(12.64) of
[quarteroni2000numerical]). Let $a = x_0 < \dots < x_{2n} = b$ be a quadratic mesh with
$n \ge 1$. For every index $i$ and every $l \le 2n$, $$\varphi_i(x_l) = \delta_{il}.$$
-/
theorem quadShapeFun_apply_node (hx : IsIntervalPartition a b (2 * n) x) {i l : ℕ}
    (hl : l ≤ 2 * n) (hn : 1 ≤ n) : quadShapeFun n x i (x l) = if i = l then 1 else 0 := by
  rcases lt_or_ge l (2 * n) with hlt | hge
  · exact quadShapeFun_apply_node_of_panel hx (m := l / 2) (by omega) (by omega) (by omega)
  · have hll : l = 2 * n := le_antisymm hl hge
    subst hll
    exact quadShapeFun_apply_node_of_panel hx (m := n - 1) (by omega) (by omega) (by omega)

end Panel

/-! ### The element partition and the shape functions inside $H^1(a, b)$ -/

/-- The endpoints of the $n$ elements of a quadratic mesh (§12.4.5 of [quarteroni2000numerical]):
the even-indexed nodes $x_0 < x_2 < \dots < x_{2n}$, as a sequence $k \mapsto x_{2k}$. -/
noncomputable def evenNodes (x : ℕ → ℝ) : ℕ → ℝ := fun k ↦ x (2 * k)

/-- The $k$-th element endpoint is $x_{2k}$. -/
theorem evenNodes_apply (x : ℕ → ℝ) (k : ℕ) : evenNodes x k = x (2 * k) := rfl

/-- The $(k + 1)$-th element endpoint is $x_{2k+2}$. -/
theorem evenNodes_succ (x : ℕ → ℝ) (k : ℕ) : evenNodes x (k + 1) = x (2 * k + 2) := by
  simp only [evenNodes, Nat.mul_succ]

/-- If $a = x_0 < \dots < x_{2n} = b$ is a partition into $2n$ panels, then the even-indexed nodes
form a partition of $[a, b]$ into $n$ elements. -/
theorem isIntervalPartition_evenNodes {n : ℕ} {x : ℕ → ℝ} (hx : IsIntervalPartition a b (2 * n) x) :
    IsIntervalPartition a b n (evenNodes x) where
  step j hj := by
    rw [evenNodes_apply, evenNodes_succ]
    exact hx.lt (by omega) (by omega)
  first := hx.first
  last := hx.last

/-- The shape function $\varphi_i$ of $X_h^2$, as a continuous function on $[a, b]$. -/
noncomputable def quadShapeCM (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : C(Icc a b, ℝ) :=
  ⟨fun t ↦ quadShapeFun n x i t, (continuous_quadShapeFun n x i).comp continuous_subtype_val⟩

/-- The continuous function `FiniteElement.quadShapeCM` takes the values of
`FiniteElement.quadShapeFun`. -/
@[simp]
theorem quadShapeCM_apply (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) (i : ℕ) (t : Icc a b) :
    quadShapeCM a b n x i t = quadShapeFun n x i t := rfl

/-- **The shape functions of $X_h^2$ are continuous piecewise quadratics.** For a quadratic mesh
$a = x_0 < \dots < x_{2n} = b$, every shape function $\varphi_i$ lies in the spline space of
degree $2$ and smoothness $0$ on the element partition $x_0 < x_2 < \dots < x_{2n}$. On each
element it is one of the three local Lagrange polynomials, or zero. -/
theorem quadShapeCM_mem_splineSpace {n : ℕ} {x : ℕ → ℝ}
    (hx : IsIntervalPartition a b (2 * n) x) (i : ℕ) :
    quadShapeCM a b n x i ∈ Spline.splineSpace a b n (evenNodes x) 2 0 := by
  refine ⟨quadShapeFun n x i, ?_, fun t ↦ rfl, fun m hm ↦ ?_⟩
  · rw [Nat.cast_zero]
    exact contDiffOn_zero.2 (continuous_quadShapeFun n x i).continuousOn
  have hIcc : Icc (evenNodes x m) (evenNodes x (m + 1)) = Icc (x (2 * m)) (x (2 * m + 2)) := by
    rw [evenNodes_apply, evenNodes_succ]
  rw [hIcc]
  by_cases hi0 : i = 2 * m
  · subst hi0
    exact ⟨quadPoly (x (2 * m)) (x (2 * m + 1)) (x (2 * m + 2)), quadPoly_degree_le _ _ _,
      fun t ht ↦ by
        rw [quadShapeFun_even_left hx hm ht.1 ht.2]; exact (quadPoly_eval _ _ _ t).symm⟩
  by_cases hi1 : i = 2 * m + 1
  · subst hi1
    exact ⟨quadPoly (x (2 * m + 1)) (x (2 * m)) (x (2 * m + 2)), quadPoly_degree_le _ _ _,
      fun t ht ↦ by
        rw [quadShapeFun_midpoint hm ht.1 ht.2]; exact (quadPoly_eval _ _ _ t).symm⟩
  by_cases hi2 : i = 2 * m + 2
  · subst hi2
    exact ⟨quadPoly (x (2 * m + 2)) (x (2 * m)) (x (2 * m + 1)), quadPoly_degree_le _ _ _,
      fun t ht ↦ by
        rw [quadShapeFun_even_right hx hm ht.1 ht.2]; exact (quadPoly_eval _ _ _ t).symm⟩
  · exact ⟨0, by simp, fun t ht ↦ by
      rw [quadShapeFun_eq_zero_of_panel hx hm hi0 hi1 hi2 ht.1 ht.2]; simp⟩

section QuadElement

variable {n : ℕ} {x : ℕ → ℝ}

/-- **The shape functions $\varphi_i$ of $X_h^2$** ((12.63)–(12.64) of [quarteroni2000numerical]),
as elements of $H^1(a, b)$. Let $a < b$ and let $a = x_0 < \dots < x_{2n} = b$ be a quadratic
mesh with $n \ge 1$. Then $\varphi_i$ is the element of $H^1(a, b)$ whose continuous
representative is `FiniteElement.quadShapeFun`. The even-indexed nodes are the endpoints of the
$n$ elements and the odd-indexed nodes are their interior nodes, and
$\varphi_i(x_j) = \delta_{ij}$ (`FiniteElement.rep_quadraticShape_node`).

The element is chosen from `FiniteElement.exists_mem_lagrangeSpace`. It is unique, because the
embedding $H^1(a, b) \hookrightarrow C([a, b])$ is injective. -/
noncomputable def quadraticShape (hab : a < b) (hx : IsIntervalPartition a b (2 * n) x)
    (hn : 1 ≤ n) (i : ℕ) : SobolevInterval 1 a b :=
  (exists_mem_lagrangeSpace hab (isIntervalPartition_evenNodes hx) hn
    (quadShapeCM_mem_splineSpace hx i)).choose

/-- The continuous representative of the quadratic shape element $\varphi_i$ is
`FiniteElement.quadShapeCM`. -/
theorem toContinuousMap_quadraticShape (hab : a < b) (hx : IsIntervalPartition a b (2 * n) x)
    (hn : 1 ≤ n) (i : ℕ) :
    SobolevInterval.toContinuousMap hab (quadraticShape hab hx hn i) = quadShapeCM a b n x i :=
  (exists_mem_lagrangeSpace hab (isIntervalPartition_evenNodes hx) hn
    (quadShapeCM_mem_splineSpace hx i)).choose_spec

/-- The continuous representative of the quadratic shape element $\varphi_i$ takes the values of
`FiniteElement.quadShapeFun` on $[a, b]$. -/
theorem rep_quadraticShape (hab : a < b) (hx : IsIntervalPartition a b (2 * n) x) (hn : 1 ≤ n)
    (i : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    SobolevInterval.rep (quadraticShape hab hx hn i) t = quadShapeFun n x i t :=
  congrArg (fun f : C(Icc a b, ℝ) ↦ f ⟨t, ht⟩) (toContinuousMap_quadraticShape hab hx hn i)

/-- **The quadratic shape elements lie in $X_h^2$**, the space of continuous piecewise quadratics on
the element partition $x_0 < x_2 < \dots < x_{2n}$. -/
theorem quadraticShape_mem_lagrangeSpace (hab : a < b) (hx : IsIntervalPartition a b (2 * n) x)
    (hn : 1 ≤ n) (i : ℕ) :
    quadraticShape hab hx hn i ∈ lagrangeSpace hab n (evenNodes x) 2 := by
  rw [mem_lagrangeSpace_iff, toContinuousMap_quadraticShape]
  exact quadShapeCM_mem_splineSpace hx i

/-- **The Lagrange interpolation property of the quadratic shape elements** ((12.63)–(12.64) of
[quarteroni2000numerical]). Let $a < b$ and let $a = x_0 < \dots < x_{2n} = b$ be a quadratic
mesh with $n \ge 1$. For every index $i$ and every $l \le 2n$, the continuous representative of
$\varphi_i \in H^1(a, b)$ satisfies $$\varphi_i(x_l) = \delta_{il}.$$
-/
theorem rep_quadraticShape_node (hab : a < b) (hx : IsIntervalPartition a b (2 * n) x)
    (hn : 1 ≤ n) {i l : ℕ} (hl : l ≤ 2 * n) :
    SobolevInterval.rep (quadraticShape hab hx hn i) (x l) = if i = l then 1 else 0 := by
  have hmem : x l ∈ Icc a b := Set.mem_Icc.2 ⟨hx.left_le (by omega), hx.le_right (by omega)⟩
  rw [rep_quadraticShape hab hx hn i hmem]
  exact quadShapeFun_apply_node hx hl hn

/-- **The local support of the quadratic shape elements** (§12.4.5 of [quarteroni2000numerical]).
Let $a < b$, let $a = x_0 < \dots < x_{2n} = b$ be a quadratic mesh with $n \ge 1$, and let
$m < n$. If $i \notin \{2m, 2m + 1, 2m + 2\}$, then the continuous representative of
$\varphi_i \in H^1(a, b)$ vanishes on the element $[x_{2m}, x_{2m+2}]$. In particular the bubble
$\varphi_{2m+1}$ is supported in the single element $[x_{2m}, x_{2m+2}]$. -/
theorem rep_quadraticShape_eq_zero_of_panel (hab : a < b)
    (hx : IsIntervalPartition a b (2 * n) x) (hn : 1 ≤ n) {m i : ℕ} (hm : m < n)
    (hne0 : i ≠ 2 * m) (hne1 : i ≠ 2 * m + 1) (hne2 : i ≠ 2 * m + 2) {t : ℝ}
    (ht1 : x (2 * m) ≤ t) (ht2 : t ≤ x (2 * m + 2)) :
    SobolevInterval.rep (quadraticShape hab hx hn i) t = 0 := by
  have hmem : t ∈ Icc a b :=
    Set.mem_Icc.2 ⟨(hx.left_le (show 2 * m ≤ 2 * n by omega)).trans ht1,
      ht2.trans (hx.le_right (show 2 * m + 2 ≤ 2 * n by omega))⟩
  rw [rep_quadraticShape hab hx hn i hmem]
  exact quadShapeFun_eq_zero_of_panel hx hm hne0 hne1 hne2 ht1 ht2

/-- The quadratic shape functions $\varphi_0, \dots, \varphi_{2n}$ as elements of $X_h^2$, indexed
by the $2n + 1$ nodes. -/
noncomputable def quadraticElem (hab : a < b) (hx : IsIntervalPartition a b (2 * n) x)
    (hn : 1 ≤ n) (i : Fin (2 * n + 1)) : lagrangeSpace hab n (evenNodes x) 2 :=
  ⟨quadraticShape hab hx hn (i : ℕ), quadraticShape_mem_lagrangeSpace hab hx hn (i : ℕ)⟩

/-- The quadratic shape functions $\varphi_0, \dots, \varphi_{2n}$ are linearly independent in
$X_h^2$. Evaluating a vanishing combination at the node $x_j$ gives its $j$-th coefficient. -/
theorem linearIndependent_quadraticElem (hab : a < b)
    (hx : IsIntervalPartition a b (2 * n) x) (hn : 1 ≤ n) :
    LinearIndependent ℝ (quadraticElem hab hx hn) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hjn : (j : ℕ) ≤ 2 * n := Nat.lt_succ_iff.1 j.isLt
  have hmem : x (j : ℕ) ∈ Icc a b :=
    Set.mem_Icc.2 ⟨hx.left_le hjn, hx.le_right hjn⟩
  have hsub : (∑ i, g i • quadraticShape hab hx hn (i : ℕ)) = 0 := by
    have := congrArg (Subtype.val) hg
    simpa [quadraticElem] using this
  have hval := congrArg (SobolevInterval.evalCLM hab ⟨_, hmem⟩) hsub
  simp only [map_sum, map_smul, smul_eq_mul, map_zero, SobolevInterval.evalCLM_apply] at hval
  rw [Finset.sum_congr rfl fun i _ ↦ congrArg (g i * ·)
    (rep_quadraticShape_node hab hx hn (i := (i : ℕ)) (l := (j : ℕ)) hjn)] at hval
  simpa [Fin.val_inj] using hval

/-- **The nodal basis of $X_h^2$** ((12.63)–(12.64) of [quarteroni2000numerical]). Let $a < b$ and
let $a = x_0 < \dots < x_{2n} = b$ be a quadratic mesh with $n \ge 1$. Then the $2n + 1$ shape
functions $\varphi_0, \dots, \varphi_{2n}$ form a basis of $X_h^2$ on the element partition. The
nodal values are the degrees of freedom.

The basis comes from the linear independence and the dimension $\dim X_h^2 = 2n + 1$ of
`FiniteElement.finrank_lagrangeSpace`. -/
noncomputable def quadraticBasis (hab : a < b) (hx : IsIntervalPartition a b (2 * n) x)
    (hn : 1 ≤ n) : Module.Basis (Fin (2 * n + 1)) ℝ (lagrangeSpace hab n (evenNodes x) 2) :=
  haveI := finiteDimensional_lagrangeSpace hab (isIntervalPartition_evenNodes hx) hn 2
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_quadraticElem hab hx hn)
    (by
      rw [Fintype.card_fin, finrank_lagrangeSpace hab (isIntervalPartition_evenNodes hx) hn 2]
      ring)

/-- The $i$-th element of the quadratic basis is the shape function $\varphi_i$. -/
@[simp]
theorem quadraticBasis_apply (hab : a < b) (hx : IsIntervalPartition a b (2 * n) x) (hn : 1 ≤ n)
    (i : Fin (2 * n + 1)) : quadraticBasis hab hx hn i = quadraticElem hab hx hn i := by
  rw [quadraticBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-! ### The quadratic reference element -/

/-- The quadratic Lagrange basis function at $p$ for the nodes $p$, $q$, $r$ takes the value
$(t - q)(t - r)/((p - q)(p - r))$ at $t$. -/
theorem quadLagrangeFun_apply (p q r t : ℝ) :
    quadLagrangeFun p q r t = (t - q) * (t - r) / ((p - q) * (p - r)) := rfl

/-- For $p \ne q$, with midpoint $c = (p + q)/2$ and $\xi = (t - p)/(q - p)$: $$\frac{(t - c)(t -
q)}{(p - c)(p - q)} = (1 - \xi)(1 - 2\xi).$$ This identity gives
`FiniteElement.quadShapeFun_eq_referenceQuadratic_zero`. -/
theorem quadRef_aux_zero {p q t : ℝ} (hpq : p ≠ q) :
    (t - (p + q) / 2) * (t - q) / ((p - (p + q) / 2) * (p - q))
      = (1 - (t - p) / (q - p)) * (1 - 2 * ((t - p) / (q - p))) := by
  obtain ⟨d, hd, rfl⟩ : ∃ d, d ≠ 0 ∧ q = p + d := ⟨q - p, sub_ne_zero.2 hpq.symm, by ring⟩
  rw [show (p + (p + d)) / 2 = p + d / 2 by ring, show p - (p + d / 2) = -(d / 2) by ring,
    show p - (p + d) = -d by ring, show p + d - p = d by ring]
  field_simp
  ring

/-- For $p \ne q$, with midpoint $c = (p + q)/2$ and $\xi = (t - p)/(q - p)$: $$\frac{(t - p)(t -
q)}{(c - p)(c - q)} = 4(1 - \xi)\xi.$$ This identity gives
`FiniteElement.quadShapeFun_eq_referenceQuadratic_one`. -/
theorem quadRef_aux_one {p q t : ℝ} (hpq : p ≠ q) :
    (t - p) * (t - q) / (((p + q) / 2 - p) * ((p + q) / 2 - q))
      = 4 * (1 - (t - p) / (q - p)) * ((t - p) / (q - p)) := by
  obtain ⟨d, hd, rfl⟩ : ∃ d, d ≠ 0 ∧ q = p + d := ⟨q - p, sub_ne_zero.2 hpq.symm, by ring⟩
  rw [show (p + (p + d)) / 2 - p = d / 2 by ring,
    show (p + (p + d)) / 2 - (p + d) = -(d / 2) by ring, show p + d - p = d by ring]
  field_simp
  ring

/-- For $p \ne q$, with midpoint $c = (p + q)/2$ and $\xi = (t - p)/(q - p)$: $$\frac{(t - p)(t -
c)}{(q - p)(q - c)} = \xi(2\xi - 1).$$ This identity gives
`FiniteElement.quadShapeFun_eq_referenceQuadratic_two`. -/
theorem quadRef_aux_two {p q t : ℝ} (hpq : p ≠ q) :
    (t - p) * (t - (p + q) / 2) / ((q - p) * (q - (p + q) / 2))
      = (t - p) / (q - p) * (2 * ((t - p) / (q - p)) - 1) := by
  obtain ⟨d, hd, rfl⟩ : ∃ d, d ≠ 0 ∧ q = p + d := ⟨q - p, sub_ne_zero.2 hpq.symm, by ring⟩
  rw [show (p + (p + d)) / 2 = p + d / 2 by ring, show p + d - (p + d / 2) = d / 2 by ring,
    show p + d - p = d by ring]
  field_simp
  ring

/-- **The shape function $\varphi_{2m}$ is $\hat\varphi_0 \circ \xi$ on the element $I_m$** ((12.65)
of [quarteroni2000numerical]). Let $a = x_0 < \dots < x_{2n} = b$ be a quadratic mesh, let
$m < n$, and let the interior node be the midpoint: $x_{2m+1} = (x_{2m} + x_{2m+2})/2$. Then
$\varphi_{2m}(t) = \hat\varphi_0(\xi(t))$ for $x_{2m} \le t \le x_{2m+2}$, where $\xi$ is the
reference coordinate of the element. Without the midpoint condition the reference shape
functions do not describe the element. -/
theorem quadShapeFun_eq_referenceQuadratic_zero (hx : IsIntervalPartition a b (2 * n) x) {m : ℕ}
    (hm : m < n) (hmid : x (2 * m + 1) = (x (2 * m) + x (2 * m + 2)) / 2) {t : ℝ}
    (h1 : x (2 * m) ≤ t) (h2 : t ≤ x (2 * m + 2)) :
    quadShapeFun n x (2 * m) t = referenceQuadratic 0 (refCoord (evenNodes x) m t) := by
  have hne : x (2 * m) ≠ x (2 * m + 2) :=
    (hx.lt (show 2 * m < 2 * m + 2 by omega) (by omega)).ne
  rw [quadShapeFun_even_left hx hm h1 h2, quadLagrangeFun_apply, hmid]
  simp only [referenceQuadratic, Matrix.cons_val_zero, refCoord_apply, evenNodes_succ]
  exact quadRef_aux_zero hne

/-- **The shape function $\varphi_{2m+1}$ is $\hat\varphi_1 \circ \xi$ on the element $I_m$**
((12.65) of [quarteroni2000numerical]). For a quadratic mesh $a = x_0 < \dots < x_{2n} = b$,
$m < n$ and $x_{2m+1} = (x_{2m} + x_{2m+2})/2$, $\varphi_{2m+1}(t) = \hat\varphi_1(\xi(t))$ for
$x_{2m} \le t \le x_{2m+2}$. -/
theorem quadShapeFun_eq_referenceQuadratic_one (hx : IsIntervalPartition a b (2 * n) x) {m : ℕ}
    (hm : m < n) (hmid : x (2 * m + 1) = (x (2 * m) + x (2 * m + 2)) / 2) {t : ℝ}
    (h1 : x (2 * m) ≤ t) (h2 : t ≤ x (2 * m + 2)) :
    quadShapeFun n x (2 * m + 1) t = referenceQuadratic 1 (refCoord (evenNodes x) m t) := by
  have hne : x (2 * m) ≠ x (2 * m + 2) :=
    (hx.lt (show 2 * m < 2 * m + 2 by omega) (by omega)).ne
  rw [quadShapeFun_midpoint hm h1 h2, quadLagrangeFun_apply, hmid]
  simp only [referenceQuadratic, Matrix.cons_val_one, refCoord_apply, evenNodes_succ]
  exact quadRef_aux_one hne

/-- **The shape function $\varphi_{2m+2}$ is $\hat\varphi_2 \circ \xi$ on the element $I_m$**
((12.65) of [quarteroni2000numerical]). For a quadratic mesh $a = x_0 < \dots < x_{2n} = b$,
$m < n$ and $x_{2m+1} = (x_{2m} + x_{2m+2})/2$, $\varphi_{2m+2}(t) = \hat\varphi_2(\xi(t))$ for
$x_{2m} \le t \le x_{2m+2}$. -/
theorem quadShapeFun_eq_referenceQuadratic_two (hx : IsIntervalPartition a b (2 * n) x) {m : ℕ}
    (hm : m < n) (hmid : x (2 * m + 1) = (x (2 * m) + x (2 * m + 2)) / 2) {t : ℝ}
    (h1 : x (2 * m) ≤ t) (h2 : t ≤ x (2 * m + 2)) :
    quadShapeFun n x (2 * m + 2) t = referenceQuadratic 2 (refCoord (evenNodes x) m t) := by
  have hne : x (2 * m) ≠ x (2 * m + 2) :=
    (hx.lt (show 2 * m < 2 * m + 2 by omega) (by omega)).ne
  rw [quadShapeFun_even_right hx hm h1 h2, quadLagrangeFun_apply, hmid]
  simp only [referenceQuadratic, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    refCoord_apply, evenNodes_succ]
  exact quadRef_aux_two hne

/-- **The shape functions (12.63)–(12.64) are the images of the reference shape functions (12.65)
under the affine map (12.62)** (§12.4.5 of [quarteroni2000numerical]). Let $a < b$, let
$a = x_0 < \dots < x_{2n} = b$ be a quadratic mesh with $n \ge 1$, let $m < n$, and let the
interior node be the midpoint: $x_{2m+1} = (x_{2m} + x_{2m+2})/2$. Then for
$x_{2m} \le t \le x_{2m+2}$ the continuous representatives of the shape elements satisfy
$$\varphi_{2m}(t) = \hat\varphi_0(\xi(t)), \qquad \varphi_{2m+1}(t) = \hat\varphi_1(\xi(t)),
\qquad \varphi_{2m+2}(t) = \hat\varphi_2(\xi(t)),$$ where
$\xi(t) = (t - x_{2m})/(x_{2m+2} - x_{2m})$ is the reference coordinate of the element. -/
theorem rep_quadraticShape_eq_referenceQuadratic (hab : a < b)
    (hx : IsIntervalPartition a b (2 * n) x) (hn : 1 ≤ n) {m : ℕ} (hm : m < n)
    (hmid : x (2 * m + 1) = (x (2 * m) + x (2 * m + 2)) / 2) {t : ℝ}
    (h1 : x (2 * m) ≤ t) (h2 : t ≤ x (2 * m + 2)) :
    SobolevInterval.rep (quadraticShape hab hx hn (2 * m)) t
        = referenceQuadratic 0 (refCoord (evenNodes x) m t) ∧
      SobolevInterval.rep (quadraticShape hab hx hn (2 * m + 1)) t
        = referenceQuadratic 1 (refCoord (evenNodes x) m t) ∧
      SobolevInterval.rep (quadraticShape hab hx hn (2 * m + 2)) t
        = referenceQuadratic 2 (refCoord (evenNodes x) m t) := by
  have hmem : t ∈ Icc a b :=
    Set.mem_Icc.2 ⟨(hx.left_le (show 2 * m ≤ 2 * n by omega)).trans h1,
      h2.trans (hx.le_right (show 2 * m + 2 ≤ 2 * n by omega))⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [rep_quadraticShape hab hx hn _ hmem]
    exact quadShapeFun_eq_referenceQuadratic_zero hx hm hmid h1 h2
  · rw [rep_quadraticShape hab hx hn _ hmem]
    exact quadShapeFun_eq_referenceQuadratic_one hx hm hmid h1 h2
  · rw [rep_quadraticShape hab hx hn _ hmem]
    exact quadShapeFun_eq_referenceQuadratic_two hx hm hmid h1 h2

/-- **The interior quadratic shape elements lie in $X_h^{2,0}$** ((12.57) of
[quarteroni2000numerical] at $k = 2$). Let $a < b$ and let $a = x_0 < \dots < x_{2n} = b$ be a
quadratic mesh with $n \ge 1$. Then every shape element $\varphi_i$ with $i \ne 0$ and
$i \ne 2n$ lies in $X_h^{2,0}$, because it vanishes at both endpoints. -/
theorem quadraticShape_mem_lagrangeSpaceZero (hab : a < b)
    (hx : IsIntervalPartition a b (2 * n) x) (hn : 1 ≤ n) {i : ℕ} (h0 : i ≠ 0) (hi : i ≠ 2 * n) :
    quadraticShape hab hx hn i ∈ lagrangeSpaceZero hab n (evenNodes x) 2 := by
  refine ⟨quadraticShape_mem_lagrangeSpace hab hx hn i,
    SobolevIntervalZero.mem_of_rep_eq_zero hab _ ?_ ?_⟩
  · have h := rep_quadraticShape_node hab hx hn (i := i) (l := 0) (Nat.zero_le _)
    rw [hx.first] at h
    rw [h]
    simp [h0]
  · have h := rep_quadraticShape_node hab hx hn (i := i) (l := 2 * n) le_rfl
    rw [hx.last] at h
    rw [h]
    simp [hi]


end QuadElement
/-! ### The nodal values as degrees of freedom -/

section Nodal

variable {n : ℕ} {x : ℕ → ℝ}

/-- **The nodal values are the degrees of freedom of $X_h^1$** (§12.4.5 of
[quarteroni2000numerical]). Let $a < b$, and let $a = x_0 < \dots < x_n = b$ be a partition with
$n \ge 1$. If $v, w \in X_h^1$ have continuous representatives with $v(x_i) = w(x_i)$ for every
$i \le n$, then $v = w$. -/
theorem eq_of_rep_node_eq (hab : a < b) (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    {v w : SobolevInterval 1 a b} (hv : v ∈ lagrangeSpace hab n x 1)
    (hw : w ∈ lagrangeSpace hab n x 1)
    (h : ∀ i ≤ n, SobolevInterval.rep v (x i) = SobolevInterval.rep w (x i)) : v = w := by
  refine (eq_sum_hatFunction hab hx hn ⟨v, hv⟩).trans
    (Eq.trans ?_ (eq_sum_hatFunction hab hx hn ⟨w, hw⟩).symm)
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [h (i : ℕ) (Nat.lt_succ_iff.1 i.isLt)]

end Nodal

/-! ### The piecewise quadratic interpolation operator into $H^1(a, b)$ -/

section QuadInterp

variable {n : ℕ} {x : ℕ → ℝ}

/-- **The piecewise quadratic interpolant** $\Pi_h^2 u$ of §8.3 and §12.4.5 of
[quarteroni2000numerical], as an element of $H^1(a, b)$. For a quadratic mesh
$a = x_0 < \dots < x_{2n} = b$ with $n \ge 1$, $a < b$, and $u \in H^1(a, b)$ with continuous
representative $\tilde u$, $$\Pi_h^2 u = \sum_{i=0}^{2n} \tilde u(x_i)\, \varphi_i.$$
-/
noncomputable def quadraticInterp (hab : a < b) (hx : IsIntervalPartition a b (2 * n) x)
    (hn : 1 ≤ n) (u : SobolevInterval 1 a b) : SobolevInterval 1 a b :=
  ∑ i ∈ Finset.range (2 * n + 1), SobolevInterval.rep u (x i) • quadraticShape hab hx hn i

/-- **A combination of the quadratic shape functions has the expected representative.** Let $a < b$,
let $a = x_0 < \dots < x_{2n} = b$ be a quadratic mesh with $n \ge 1$, and let
$c_0, \dots, c_{2n}$ be real numbers. Then the continuous representative of
$\sum_{i=0}^{2n} c_i \varphi_i$ takes the value $\sum_{i=0}^{2n} c_i \varphi_i(t)$ at every
$t \in [a, b]$, with $\varphi_i$ the function `FiniteElement.quadShapeFun`. -/
theorem rep_sum_quadraticShape (hab : a < b) (hx : IsIntervalPartition a b (2 * n) x) (hn : 1 ≤ n)
    (c : ℕ → ℝ) {t : ℝ} (ht : t ∈ Icc a b) :
    SobolevInterval.rep (∑ i ∈ Finset.range (2 * n + 1), c i • quadraticShape hab hx hn i) t
      = ∑ i ∈ Finset.range (2 * n + 1), c i * quadShapeFun n x i t := by
  have h : SobolevInterval.rep
        (∑ i ∈ Finset.range (2 * n + 1), c i • quadraticShape hab hx hn i) t
      = SobolevInterval.evalCLM hab ⟨t, ht⟩
        (∑ i ∈ Finset.range (2 * n + 1), c i • quadraticShape hab hx hn i) :=
    rfl
  rw [h, map_sum]
  simp only [map_smul, smul_eq_mul, SobolevInterval.evalCLM_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [rep_quadraticShape hab hx hn i ht]

/-- The continuous representative of the quadratic interpolant is the nodal combination of the shape
functions. Let $a < b$, let $a = x_0 < \dots < x_{2n} = b$ be a quadratic mesh with $n \ge 1$,
and let $u \in H^1(a, b)$ with continuous representative $\tilde u$. Then for every
$t \in [a, b]$ $$(\Pi_h^2 u)(t) = \sum_{i=0}^{2n} \tilde u(x_i)\, \varphi_i(t).$$
-/
theorem rep_quadraticInterp (hab : a < b) (hx : IsIntervalPartition a b (2 * n) x) (hn : 1 ≤ n)
    (u : SobolevInterval 1 a b) {t : ℝ} (ht : t ∈ Icc a b) :
    SobolevInterval.rep (quadraticInterp hab hx hn u) t
      = ∑ i ∈ Finset.range (2 * n + 1), SobolevInterval.rep u (x i) * quadShapeFun n x i t :=
  rep_sum_quadraticShape hab hx hn _ ht

/-- **The quadratic interpolant matches $u$ at the nodes.** Let $a < b$, let
$a = x_0 < \dots < x_{2n} = b$ be a quadratic mesh with $n \ge 1$, and let $u \in H^1(a, b)$.
Then the continuous representatives satisfy $(\Pi_h^2 u)(x_l) = u(x_l)$ for every $l \le 2n$. -/
theorem rep_quadraticInterp_node (hab : a < b) (hx : IsIntervalPartition a b (2 * n) x)
    (hn : 1 ≤ n) (u : SobolevInterval 1 a b) {l : ℕ} (hl : l ≤ 2 * n) :
    SobolevInterval.rep (quadraticInterp hab hx hn u) (x l) = SobolevInterval.rep u (x l) := by
  have hmem : x l ∈ Icc a b := ⟨hx.left_le hl, hx.le_right hl⟩
  rw [rep_quadraticInterp hab hx hn u hmem,
    Finset.sum_congr rfl fun i _ ↦ congrArg (SobolevInterval.rep u (x i) * ·)
      (quadShapeFun_apply_node hx hl hn)]
  simp [Finset.sum_ite_eq' (Finset.range (2 * n + 1)) l, Nat.lt_succ_iff.2 hl]

/-- **The quadratic interpolant lies in $X_h^2$.** Let $a < b$, let $a = x_0 < \dots < x_{2n} = b$
be a quadratic mesh with $n \ge 1$, and let $u \in H^1(a, b)$. Then $\Pi_h^2 u \in X_h^2$ on the
element partition $x_0 < x_2 < \dots < x_{2n}$. -/
theorem quadraticInterp_mem_lagrangeSpace (hab : a < b) (hx : IsIntervalPartition a b (2 * n) x)
    (hn : 1 ≤ n) (u : SobolevInterval 1 a b) :
    quadraticInterp hab hx hn u ∈ lagrangeSpace hab n (evenNodes x) 2 :=
  Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
    (quadraticShape_mem_lagrangeSpace hab hx hn i)

/-- **The quadratic interpolant of an element of $H^1_0(a, b)$ lies in $X_h^{2,0}$.** Let $a < b$,
let $a = x_0 < \dots < x_{2n} = b$ be a quadratic mesh with $n \ge 1$, and let
$u \in H^1_0(a, b)$. Then $\Pi_h^2 u \in X_h^{2,0}$ on the element partition. -/
theorem quadraticInterp_mem_lagrangeSpaceZero (hab : a < b)
    (hx : IsIntervalPartition a b (2 * n) x) (hn : 1 ≤ n) {u : SobolevInterval 1 a b}
    (hu : u ∈ SobolevIntervalZero a b) :
    quadraticInterp hab hx hn u ∈ lagrangeSpaceZero hab n (evenNodes x) 2 := by
  refine ⟨quadraticInterp_mem_lagrangeSpace hab hx hn u,
    SobolevIntervalZero.mem_of_rep_eq_zero hab _ ?_ ?_⟩
  · have h := rep_quadraticInterp_node hab hx hn u (l := 0) (Nat.zero_le _)
    rw [hx.first] at h
    rw [h]
    exact SobolevIntervalZero.rep_left_eq_zero hab hu
  · have h := rep_quadraticInterp_node hab hx hn u (l := 2 * n) le_rfl
    rw [hx.last] at h
    rw [h]
    exact SobolevIntervalZero.rep_right_eq_zero hab hu

/-! ### The local Lagrange polynomial of an element -/

/-- **The local quadratic Lagrange interpolant** of the values $c$ on the element
$[x_{2m}, x_{2m+2}]$, as a polynomial: $$c_{2m}\, \ell_{2m} + c_{2m+1}\, \ell_{2m+1} +
c_{2m+2}\, \ell_{2m+2},$$ where $\ell_l$ is the quadratic Lagrange basis polynomial at $x_l$ for
the three nodes $x_{2m}$, $x_{2m+1}$, $x_{2m+2}$. -/
noncomputable def quadElemPoly (x : ℕ → ℝ) (c : ℕ → ℝ) (m : ℕ) : Polynomial ℝ :=
  c (2 * m) • quadPoly (x (2 * m)) (x (2 * m + 1)) (x (2 * m + 2))
    + c (2 * m + 1) • quadPoly (x (2 * m + 1)) (x (2 * m)) (x (2 * m + 2))
    + c (2 * m + 2) • quadPoly (x (2 * m + 2)) (x (2 * m)) (x (2 * m + 1))

/-- The local quadratic Lagrange interpolant has degree at most $2$. -/
theorem quadElemPoly_degree_le (x : ℕ → ℝ) (c : ℕ → ℝ) (m : ℕ) :
    (quadElemPoly x c m).degree ≤ 2 :=
  (Polynomial.degree_add_le _ _).trans (max_le
    ((Polynomial.degree_add_le _ _).trans (max_le
      ((Polynomial.degree_smul_le _ _).trans (quadPoly_degree_le _ _ _))
      ((Polynomial.degree_smul_le _ _).trans (quadPoly_degree_le _ _ _))))
    ((Polynomial.degree_smul_le _ _).trans (quadPoly_degree_le _ _ _)))

/-- The value of the local quadratic Lagrange interpolant at $t$ is $c_{2m}\, \ell_{2m}(t) +
c_{2m+1}\, \ell_{2m+1}(t) + c_{2m+2}\, \ell_{2m+2}(t)$, with $\ell_l$ the quadratic Lagrange
basis functions of the three nodes of the element. -/
theorem quadElemPoly_eval (x : ℕ → ℝ) (c : ℕ → ℝ) (m : ℕ) (t : ℝ) :
    (quadElemPoly x c m).eval t
      = c (2 * m) * quadLagrangeFun (x (2 * m)) (x (2 * m + 1)) (x (2 * m + 2)) t
        + c (2 * m + 1) * quadLagrangeFun (x (2 * m + 1)) (x (2 * m)) (x (2 * m + 2)) t
        + c (2 * m + 2) * quadLagrangeFun (x (2 * m + 2)) (x (2 * m)) (x (2 * m + 1)) t := by
  simp [quadElemPoly, quadPoly_eval]

/-- **The local Lagrange interpolant takes the prescribed values at the three nodes of its
element.** For a quadratic mesh $a = x_0 < \dots < x_{2n} = b$, $m < n$ and
$2m \le l \le 2m + 2$, the local quadratic Lagrange interpolant of $c$ on the element $m$ takes
the value $c_l$ at $x_l$. -/
theorem quadElemPoly_eval_node (hx : IsIntervalPartition a b (2 * n) x) (c : ℕ → ℝ) {m l : ℕ}
    (hm : m < n) (hl1 : 2 * m ≤ l) (hl2 : l ≤ 2 * m + 2) :
    (quadElemPoly x c m).eval (x l) = c l := by
  have h01 : x (2 * m) < x (2 * m + 1) := hx.step _ (by omega)
  have h12 : x (2 * m + 1) < x (2 * m + 2) := hx.step _ (by omega)
  have h02 : x (2 * m) < x (2 * m + 2) := h01.trans h12
  have hnode : l = 2 * m ∨ l = 2 * m + 1 ∨ l = 2 * m + 2 := by omega
  rw [quadElemPoly_eval]
  rcases hnode with rfl | rfl | rfl
  · rw [quadLagrangeFun_self h01.ne h02.ne, quadLagrangeFun_left, quadLagrangeFun_left]
    ring
  · rw [quadLagrangeFun_self h01.ne' h12.ne, quadLagrangeFun_left, quadLagrangeFun_right]
    ring
  · rw [quadLagrangeFun_self h02.ne' h12.ne', quadLagrangeFun_right, quadLagrangeFun_right]
    ring

/-- **On an element the quadratic interpolant is the local Lagrange polynomial.** Let $a < b$, let
$a = x_0 < \dots < x_{2n} = b$ be a quadratic mesh with $n \ge 1$, let $u \in H^1(a, b)$ with
continuous representative $\tilde u$, and let $m < n$. Then for $x_{2m} \le t \le x_{2m+2}$ the
continuous representative of $\Pi_h^2 u$ at $t$ equals the local quadratic Lagrange interpolant
of the values $\tilde u(x_l)$ on the element $m$, evaluated at $t$. -/
theorem rep_quadraticInterp_eq_eval (hab : a < b) (hx : IsIntervalPartition a b (2 * n) x)
    (hn : 1 ≤ n) (u : SobolevInterval 1 a b) {m : ℕ} (hm : m < n) {t : ℝ}
    (h1 : x (2 * m) ≤ t) (h2 : t ≤ x (2 * m + 2)) :
    SobolevInterval.rep (quadraticInterp hab hx hn u) t
      = (quadElemPoly x (fun i ↦ SobolevInterval.rep u (x i)) m).eval t := by
  have hmem : t ∈ Icc a b :=
    ⟨(hx.left_le (show 2 * m ≤ 2 * n by omega)).trans h1,
      h2.trans (hx.le_right (show 2 * m + 2 ≤ 2 * n by omega))⟩
  have hsub : ({2 * m, 2 * m + 1, 2 * m + 2} : Finset ℕ) ⊆ Finset.range (2 * n + 1) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rw [Finset.mem_range]
    rcases hi with rfl | rfl | rfl <;> omega
  have hzero : ∀ i ∈ Finset.range (2 * n + 1), i ∉ ({2 * m, 2 * m + 1, 2 * m + 2} : Finset ℕ) →
      SobolevInterval.rep u (x i) * quadShapeFun n x i t = 0 := by
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    rw [quadShapeFun_eq_zero_of_panel hx hm hi.1 hi.2.1 hi.2.2 h1 h2, mul_zero]
  rw [rep_quadraticInterp hab hx hn u hmem, ← Finset.sum_subset hsub hzero,
    Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; omega), Finset.sum_singleton,
    quadShapeFun_even_left hx hm h1 h2, quadShapeFun_midpoint hm h1 h2,
    quadShapeFun_even_right hx hm h1 h2, quadElemPoly_eval]
  ring

/-! ### The interpolation estimate for $X_h^2$ -/

/-- **The interpolation estimate in the $H^1$ seminorm for $X_h^2$** ((8.26) and Theorem 8.3 of
[quarteroni2000numerical] at $k = 2$, $m = 1$, with the constant $1$). Let $a < b$, let
$a = x_0 < x_1 < \dots < x_{2n} = b$ be a quadratic mesh with $n \ge 1$ whose $n$ elements
$[x_{2m}, x_{2m+2}]$ have length at most $h$, and let $u \in H^3(a, b)$. Then $$|u - \Pi_h^2
u|_{H^1(a, b)} \le h^2\, |u|_{H^3(a, b)}.$$

On the left $u$ is read in $H^1(a, b)$ through two applications of
`SobolevInterval.inclusionCLM`. The proof applies the panel estimate
`integral_sq_iteratedDeriv_sub_le` on each element to the local Lagrange polynomial
`FiniteElement.quadElemPoly`. Inside an element the continuous representative of $\Pi_h^2 u$ is
that polynomial (`FiniteElement.rep_quadraticInterp_eq_eval`), so the weak derivative of the
interpolant is its classical derivative there, by `SobolevInterval.ae_deriv_rep_eq`. -/
theorem seminorm_sub_quadraticInterp_le (hab : a < b) (hx : IsIntervalPartition a b (2 * n) x)
    (hn : 1 ≤ n) {h : ℝ} (hmesh : ∀ m < n, x (2 * m + 2) - x (2 * m) ≤ h)
    (u : SobolevInterval 3 a b) :
    SobolevInterval.seminorm 1 a b
        (SobolevInterval.inclusionCLM 1 a b (SobolevInterval.inclusionCLM 2 a b u)
          - quadraticInterp hab hx hn
              (SobolevInterval.inclusionCLM 1 a b (SobolevInterval.inclusionCLM 2 a b u)))
      ≤ h ^ 2 * SobolevInterval.seminorm 3 a b u := by
  set u₁ := SobolevInterval.inclusionCLM 1 a b (SobolevInterval.inclusionCLM 2 a b u) with hu₁
  set w := quadraticInterp hab hx hn u₁ with hw
  set c : ℕ → ℝ := fun i ↦ SobolevInterval.rep u₁ (x i) with hc
  obtain ⟨f, hf, hae, hftc⟩ := SobolevInterval.exists_contDiff_ae_eq hab u
  -- the continuous representative of `u₁` is the `C²` representative `f`
  have hfn : SobolevInterval.fn u₁ =ᵐ[volume.restrict (Ioo a b)] f := by
    rw [hu₁, SobolevInterval.fn_inclusionCLM, SobolevInterval.fn_inclusionCLM]
    have h0 := hae 0
    simpa [SobolevInterval.deriv_zero] using h0
  have hrep : EqOn (SobolevInterval.rep u₁) f (Icc a b) :=
    SobolevInterval.rep_eq_of_continuousOn hab u₁ hf.continuous.continuousOn hfn
  have hderiv : ⇑(SobolevInterval.deriv u₁ 1) =ᵐ[volume.restrict (Ioo a b)] _root_.deriv f := by
    rw [hu₁, SobolevInterval.deriv_inclusionCLM, SobolevInterval.deriv_inclusionCLM]
    have h1 := hae 1
    simpa using h1
  -- the elements
  have hstep : ∀ m, m < n → x (2 * m) < x (2 * m + 2) := fun m hm ↦ hx.lt (by omega) (by omega)
  have hIcc : ∀ m, m < n → Icc (x (2 * m)) (x (2 * m + 2)) ⊆ Icc a b := fun m hm s hs ↦
    ⟨(hx.left_le (show 2 * m ≤ 2 * n by omega)).trans hs.1,
      hs.2.trans (hx.le_right (show 2 * m + 2 ≤ 2 * n by omega))⟩
  have huIcc : ∀ m, m < n → Set.uIcc (x (2 * m)) (x (2 * m + 2)) ⊆ Set.uIcc a b := fun m hm ↦ by
    rw [Set.uIcc_of_le hab.le, Set.uIcc_of_le (hstep m hm).le]
    exact hIcc m hm
  -- the interpolant is the local Lagrange polynomial on each element
  have hlocal : ∀ m, m < n → ∀ t, x (2 * m) ≤ t → t ≤ x (2 * m + 2) →
      SobolevInterval.rep w t = (quadElemPoly x c m).eval t := by
    intro m hm t h1 h2
    rw [hw, rep_quadraticInterp_eq_eval hab hx hn u₁ hm h1 h2, hc]
  have hIoo : ∀ m, m < n → Ioo (x (2 * m)) (x (2 * m + 2)) ⊆ Ioo a b := fun m hm s hs ↦
    ⟨lt_of_le_of_lt (hx.left_le (show 2 * m ≤ 2 * n by omega)) hs.1,
      lt_of_lt_of_le hs.2 (hx.le_right (show 2 * m + 2 ≤ 2 * n by omega))⟩
  have hftc' : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      iteratedDeriv 2 f t - iteratedDeriv 2 f s
        = ∫ r in s..t, SobolevInterval.deriv u (Fin.last 3) r := hftc
  have hgint : IntervalIntegrable (⇑(SobolevInterval.deriv u (Fin.last 3))) volume a b :=
    SobolevInterval.intervalIntegrable_deriv hab.le u _
  have hg2int : IntervalIntegrable
      (fun t ↦ SobolevInterval.deriv u (Fin.last 3) t ^ 2) volume a b :=
    SobolevInterval.intervalIntegrable_deriv_sq hab.le u _
  -- the panel estimate on one element
  have hpanel : ∀ m, m < n →
      ∫ t in x (2 * m)..x (2 * m + 2), SobolevInterval.deriv (u₁ - w) (Fin.last 1) t ^ 2
        ≤ h ^ 4 * ∫ t in x (2 * m)..x (2 * m + 2),
            SobolevInterval.deriv u (Fin.last 3) t ^ 2 := by
    intro m hm
    have hlt := hstep m hm
    have heq : ∫ t in x (2 * m)..x (2 * m + 2),
          SobolevInterval.deriv (u₁ - w) (Fin.last 1) t ^ 2
        = ∫ t in x (2 * m)..x (2 * m + 2),
            (iteratedDeriv 1 f t
              - (Polynomial.derivative^[1] (quadElemPoly x c m)).eval t) ^ 2 := by
      rw [intervalIntegral.integral_of_le hlt.le, intervalIntegral.integral_of_le hlt.le,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_ae measurableSet_Ioo ?_
      filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1
          (Lp.coeFn_sub (SobolevInterval.deriv u₁ 1) (SobolevInterval.deriv w 1)),
        (ae_restrict_iff' measurableSet_Ioo).1 hderiv,
        SobolevInterval.ae_deriv_rep_eq w] with t hcs hdf hdr htmem
      have htab : t ∈ Ioo a b := hIoo m hm htmem
      have hev : SobolevInterval.rep w =ᶠ[nhds t] fun s ↦ (quadElemPoly x c m).eval s := by
        filter_upwards [Icc_mem_nhds htmem.1 htmem.2] with s hs
        exact hlocal m hm s hs.1 hs.2
      have hdw : SobolevInterval.deriv w 1 t
          = (Polynomial.derivative (quadElemPoly x c m)).eval t := by
        rw [← hdr ⟨htab.1, htab.2.le⟩, hev.deriv_eq, Polynomial.deriv]
      have he : SobolevInterval.deriv (u₁ - w) (Fin.last 1)
          = SobolevInterval.deriv u₁ 1 - SobolevInterval.deriv w 1 := rfl
      rw [he, hcs htab, Pi.sub_apply, hdf htab, hdw, iteratedDeriv_one, Function.iterate_one]
    have hinj : Function.Injective (fun i : Fin 3 ↦ x (2 * m + (i : ℕ))) := by
      intro i j hij
      dsimp only at hij
      by_contra hne
      have hi := i.isLt
      have hj := j.isLt
      have hij' : (i : ℕ) ≠ (j : ℕ) := fun hh ↦ hne (Fin.ext hh)
      rcases lt_or_gt_of_ne hij' with hlt' | hlt'
      · exact absurd hij (hx.lt (by omega) (by omega)).ne
      · exact absurd hij (hx.lt (by omega) (by omega)).ne'
    have hymem : ∀ i : Fin 3, x (2 * m + (i : ℕ)) ∈ Icc (x (2 * m)) (x (2 * m + 2)) := by
      intro i
      have hi := i.isLt
      exact ⟨hx.mono (by omega) (by omega), hx.mono (by omega) (by omega)⟩
    have hpy : ∀ i : Fin 3, (quadElemPoly x c m).eval (x (2 * m + (i : ℕ)))
        = f (x (2 * m + (i : ℕ))) := by
      intro i
      have hi := i.isLt
      rw [quadElemPoly_eval_node hx c hm (by omega) (by omega)]
      simp only [hc]
      exact hrep (hIcc m hm (hymem i))
    have key := integral_sq_iteratedDeriv_sub_le (m := 1) hlt (hmesh m hm) hf
      (hgint.mono_set (huIcc m hm)) (hg2int.mono_set (huIcc m hm))
      (fun s hs t ht ↦ hftc' s (hIcc m hm hs) t (hIcc m hm ht))
      (quadElemPoly_degree_le x c m) hinj hymem hpy (by norm_num)
    rw [heq]
    refine key.trans (le_of_eq ?_)
    norm_num
  -- summing over the elements
  have hDint : ∀ m, m < n → IntervalIntegrable
      (fun t ↦ SobolevInterval.deriv (u₁ - w) (Fin.last 1) t ^ 2) volume
        (x (2 * m)) (x (2 * m + 2)) := fun m hm ↦
    (SobolevInterval.intervalIntegrable_deriv_sq hab.le (u₁ - w) (Fin.last 1)).mono_set
      (huIcc m hm)
  have hGint : ∀ m, m < n → IntervalIntegrable
      (fun t ↦ SobolevInterval.deriv u (Fin.last 3) t ^ 2) volume
        (x (2 * m)) (x (2 * m + 2)) := fun m hm ↦ hg2int.mono_set (huIcc m hm)
  have hsplitD : ∑ m ∈ Finset.range n,
        ∫ t in x (2 * m)..x (2 * m + 2), SobolevInterval.deriv (u₁ - w) (Fin.last 1) t ^ 2
      = ∫ t in a..b, SobolevInterval.deriv (u₁ - w) (Fin.last 1) t ^ 2 := by
    have hsum := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun m ↦ x (2 * m)) (n := n)
      (f := fun t ↦ SobolevInterval.deriv (u₁ - w) (Fin.last 1) t ^ 2) (μ := volume)
      (fun k hk ↦ by rw [show 2 * (k + 1) = 2 * k + 2 from by ring]; exact hDint k hk)
    simpa only [Nat.mul_succ, Nat.mul_zero, hx.first, hx.last] using hsum
  have hsplitG : ∑ m ∈ Finset.range n,
        ∫ t in x (2 * m)..x (2 * m + 2), SobolevInterval.deriv u (Fin.last 3) t ^ 2
      = ∫ t in a..b, SobolevInterval.deriv u (Fin.last 3) t ^ 2 := by
    have hsum := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun m ↦ x (2 * m)) (n := n)
      (f := fun t ↦ SobolevInterval.deriv u (Fin.last 3) t ^ 2) (μ := volume)
      (fun k hk ↦ by rw [show 2 * (k + 1) = 2 * k + 2 from by ring]; exact hGint k hk)
    simpa only [Nat.mul_succ, Nat.mul_zero, hx.first, hx.last] using hsum
  have hkey : ∫ t in a..b, SobolevInterval.deriv (u₁ - w) (Fin.last 1) t ^ 2
      ≤ h ^ 4 * ∫ t in a..b, SobolevInterval.deriv u (Fin.last 3) t ^ 2 := by
    rw [← hsplitD, ← hsplitG, Finset.mul_sum]
    exact Finset.sum_le_sum fun m hm ↦ hpanel m (Finset.mem_range.1 hm)
  -- take square roots
  have hsq : SobolevInterval.seminorm 1 a b (u₁ - w) ^ 2
      ≤ (h ^ 2 * SobolevInterval.seminorm 3 a b u) ^ 2 := by
    rw [SobolevInterval.seminorm_sq_eq_integral hab.le,
      show (h ^ 2 * SobolevInterval.seminorm 3 a b u) ^ 2
        = h ^ 4 * SobolevInterval.seminorm 3 a b u ^ 2 from by ring,
      SobolevInterval.seminorm_sq_eq_integral hab.le u]
    exact hkey
  have hB : 0 ≤ h ^ 2 * SobolevInterval.seminorm 3 a b u :=
    mul_nonneg (by positivity) (apply_nonneg _ _)
  exact (pow_le_pow_iff_left₀ (apply_nonneg (SobolevInterval.seminorm 1 a b) (u₁ - w)) hB
    two_ne_zero).1 hsq

end QuadInterp

end FiniteElement
