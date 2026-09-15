import Numlib.Analysis.Sobolev.Interval
import Numlib.Approximation.SobolevInterpolation
import Numlib.Approximation.Spline
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz
import Numlib.Variational.EllipticInterval

/-!
# Lagrange finite elements on an interval

The spaces `X_h^k` of continuous piecewise polynomials of degree at most `k` on a partition
`a = x_0 < x_1 < ⋯ < x_n = b`, read inside `H^1(a, b)`, and their subspaces `X_h^{k,0}` of
elements vanishing at the endpoints, inside `H^1_0(a, b)`. This is
[quarteroni2000numerical] (8.22) and (12.57): the trial and test spaces of the finite element
method for a two-point boundary value problem.

**There is one space, not three.** `Spline.splineSpace a b n x k 0` of
`Numlib/Approximation/Spline.lean` *is* the space of continuous piecewise polynomials, as a
subspace of `C([a, b], ℝ)`. `FiniteElement.lagrangeSpace` is its preimage under the embedding
`SobolevInterval.toContinuousMap : H^1(a, b) ↪ C([a, b], ℝ)`, and the embedding restricts to a
linear isomorphism between the two (`FiniteElement.lagrangeSpaceEquiv`): it is injective because
a continuous function determines its `L²` class and the weak derivative is determined by the
function, and its image is all of `Spline.splineSpace` because a continuous piecewise polynomial
is piecewise `C¹` with bounded derivative, hence in `H^1(a, b)`
(`memSobolevInterval_of_piecewise_contDiffOn`). Every fact about one space therefore transfers
to the other, and the dimension `n k + 1` of `X_h^k` is `Spline.finrank_splineSpace`.

## Main definitions

* `FiniteElement.meshSize n x` — the mesh size `h = max_j (x_{j+1} - x_j)`.
* `FiniteElement.lagrangeSpace hab n x k` — `X_h^k` inside `H^1(a, b)`.
* `FiniteElement.lagrangeSpaceZero hab n x k` — `X_h^{k,0}`, its part inside `H^1_0(a, b)`.
* `FiniteElement.lagrangeSpaceEquiv` — the isomorphism `X_h^k ≃ₗ Spline.splineSpace`.
* `FiniteElement.hatFun`, `FiniteElement.hatDerivFun` — the hat (shape) function (12.61) and its
  weak derivative, as functions `ℝ → ℝ`; `FiniteElement.hatFunction` is the corresponding element
  of `H^1(a, b)`, and `FiniteElement.hatBasis`, `FiniteElement.hatBasisZero` the bases of `X_h^1`
  and `X_h^{1,0}` they form.
* `FiniteElement.affineMap`, `FiniteElement.referenceHat`, `FiniteElement.referenceQuadratic`,
  `FiniteElement.referenceHierarchical` — the reference element (12.62), (12.65), (12.66).
* `FiniteElement.stiffnessMatrix`, `FiniteElement.massMatrix` — the matrices `A_fe` of (12.48)
  and `M` of (13.14) of a family of trial functions.

## Main results

* `FiniteElement.toContinuousMap_injective` — the embedding `H^1(a, b) ↪ C([a, b], ℝ)` is
  injective.
* `FiniteElement.exists_mem_lagrangeSpace` — every continuous piecewise polynomial is the
  continuous representative of an element of `H^1(a, b)`.
* `FiniteElement.lagrangeSpace_eq_map_splineSpace` — the bridge between the two views.
* `FiniteElement.finrank_lagrangeSpace` — `dim X_h^k = n k + 1`, and
  `FiniteElement.finrank_lagrangeSpaceZero_one` — `dim X_h^{1,0} = n - 1`.
* `FiniteElement.rep_hatFunction_node` — `φ_i(x_j) = δ_{ij}`;
  `FiniteElement.hasWeakDerivOn_hatFun` — the weak derivative is `±1/h` on the two adjacent
  panels; `FiniteElement.eq_sum_hatFunction` — `v_h = ∑_i v_h(x_i) φ_i`.
* `FiniteElement.stiffnessMatrix_eq_zero_of_lt`, `FiniteElement.isTridiagonal_stiffnessMatrix` —
  sparsity from the local supports.
* `FiniteElement.stiffnessMatrix_uniform_eq`, `FiniteElement.massMatrix_uniform_eq` — the
  assembled matrices on a uniform mesh, `A_fe = (ε/h) tridiag(-1, 2, -1) + (β/2) tridiag(-1, 0, 1)
  + (γ h/6) tridiag(1, 4, 1)` and `M = (h/6) tridiag(1, 4, 1)`.
* `FiniteElement.stiffnessMatrix_posDef`, `FiniteElement.condNumber_stiffnessMatrix_model` —
  positive definiteness and `K₂(A_fe) = cot²(π h/2)` for the model problem.
* `FiniteElement.galerkin_iff_centredScheme` — the `P_1` Galerkin system on a uniform mesh is the
  centred difference scheme (12.75).

## Implementation notes on the hat functions

The shape functions are built as honest functions `ℝ → ℝ` and only then pushed into `H^1(a, b)`.
With `R_j` the normalized ramp of the panel `[x_j, x_{j+1}]` — zero to the left of `x_j`, rising
linearly to `1` at `x_{j+1}`, constant afterwards — and `R_{-1} = 1`, `R_j = 0` for `j ≥ n`, the
hat at the node `i` is `R_{i-1} - R_i` for every `i` at once, endpoints included. Its derivative
is the difference of the two panel indicators, and `memSobolevInterval_of_piecewise_contDiffOn`
supplies the weak derivative. The element of `H^1(a, b)` is assembled with `SobolevInterval.mk`
from the two `L²` classes rather than through an existence statement, so that both components are
available definitionally — which is what the stiffness and mass integrals need.

## Implementation notes

Two lemmas here are general facts about `H^1(a, b)` with no finite element content and belong in
`Numlib/Analysis/Sobolev/Interval.lean`; they are marked `TODO(backbone)`.
-/

open Set MeasureTheory intervalIntegral

namespace FiniteElement

variable {a b : ℝ}

/-! ### The mesh -/

/-- **The mesh size** `h = max_{0 ≤ j < n} (x_{j+1} - x_j)` of a partition, the `h` of the
finite element spaces `X_h^k` ([quarteroni2000numerical] §12.4.5). -/
noncomputable def meshSize (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  (Finset.range n).fold max 0 fun j ↦ x (j + 1) - x j

theorem meshSize_nonneg (n : ℕ) (x : ℕ → ℝ) : 0 ≤ meshSize n x :=
  (Finset.le_fold_max _).2 (Or.inl le_rfl)

theorem sub_le_meshSize {n : ℕ} (x : ℕ → ℝ) {j : ℕ} (hj : j < n) :
    x (j + 1) - x j ≤ meshSize n x :=
  (Finset.le_fold_max _).2 (Or.inr ⟨j, Finset.mem_range.2 hj, le_rfl⟩)

/-! ### The embedding `H^1(a, b) ↪ C([a, b], ℝ)` -/

-- TODO(backbone): general facts about `H^1(a, b)`; natural home
-- `Numlib/Analysis/Sobolev/Interval.lean`, beside `SobolevInterval.toContinuousMap`.
/-- **The embedding `H^1(a, b) ↪ C([a, b], ℝ)` is injective**: the continuous representative
determines the `L²` class of the function, and the weak derivative is determined by the function
almost everywhere (`SobolevMultiIndex.ext_of_fn_ae_eq`). -/
theorem toContinuousMap_injective (hab : a < b) :
    Function.Injective (SobolevInterval.toContinuousMap hab) := by
  intro u v huv
  have h1 := SobolevInterval.coe_toContinuousMap_ae_eq hab u
  have h2 := SobolevInterval.coe_toContinuousMap_ae_eq hab v
  rw [huv] at h1
  exact SobolevMultiIndex.ext_of_fn_ae_eq (h1.trans h2.symm)

-- TODO(backbone): same home as `toContinuousMap_injective`.
/-- **A function of `H^1(a, b)` continuous on `[a, b]` is the continuous representative of an
element**: if `g` is continuous on `[a, b]` and `MemSobolevInterval g 1 a b`, then some
`u ∈ H^1(a, b)` has `g` as its continuous representative. -/
theorem exists_toContinuousMap_eq (hab : a < b) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b))
    (hmem : MemSobolevInterval g 1 a b) :
    ∃ u : SobolevInterval 1 a b, ∀ t : Icc a b, SobolevInterval.toContinuousMap hab u t = g t := by
  obtain ⟨u, hu⟩ := hmem.exists_sobolevMultiIndex
  exact ⟨u, fun t ↦ SobolevInterval.toContinuousMap_eq_of_continuousOn hab u hg hu t⟩

/-! ### The finite element spaces -/

/-- **The finite element space `X_h^k`** of [quarteroni2000numerical] (8.22), read inside
`H^1(a, b)`: the elements of `H^1(a, b)` whose continuous representative is a continuous
piecewise polynomial of degree at most `k` on the partition `x`. -/
noncomputable def lagrangeSpace (hab : a < b) (n : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    Submodule ℝ (SobolevInterval 1 a b) :=
  Submodule.comap (SobolevInterval.toContinuousMap hab).toLinearMap
    (Spline.splineSpace a b n x k 0)

theorem mem_lagrangeSpace_iff {hab : a < b} {n k : ℕ} {x : ℕ → ℝ}
    {u : SobolevInterval 1 a b} :
    u ∈ lagrangeSpace hab n x k ↔
      SobolevInterval.toContinuousMap hab u ∈ Spline.splineSpace a b n x k 0 := Iff.rfl

/-- **The finite element space `X_h^{k,0}`** of [quarteroni2000numerical] (12.57): the part of
`X_h^k` inside `H^1_0(a, b)`, that is, the `v_h ∈ X_h^k` with `v_h(a) = v_h(b) = 0`. -/
noncomputable def lagrangeSpaceZero (hab : a < b) (n : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    Submodule ℝ (SobolevInterval 1 a b) :=
  lagrangeSpace hab n x k ⊓ SobolevIntervalZero a b

theorem lagrangeSpaceZero_le_sobolevIntervalZero (hab : a < b) (n : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    lagrangeSpaceZero hab n x k ≤ SobolevIntervalZero a b := inf_le_right

theorem lagrangeSpaceZero_le_lagrangeSpace (hab : a < b) (n : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    lagrangeSpaceZero hab n x k ≤ lagrangeSpace hab n x k := inf_le_left

/-- **(12.57) unfolded**: an element of `X_h^k` lies in `X_h^{k,0}` exactly when its continuous
representative vanishes at both endpoints. -/
theorem mem_lagrangeSpaceZero_iff (hab : a < b) (n : ℕ) (x : ℕ → ℝ) (k : ℕ)
    (u : SobolevInterval 1 a b) :
    u ∈ lagrangeSpaceZero hab n x k ↔ u ∈ lagrangeSpace hab n x k ∧
      SobolevInterval.toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩ = 0 ∧
      SobolevInterval.toContinuousMap hab u ⟨b, right_mem_Icc.2 hab.le⟩ = 0 :=
  Submodule.mem_inf.trans (and_congr_right' (mem_sobolevIntervalZero_iff hab u))

/-! ### The bridge to the spline space -/

/-- **Every continuous piecewise polynomial lies in `H^1(a, b)`**: a member of
`Spline.splineSpace a b n x k 0` is the continuous representative of an element of `H^1(a, b)`,
which therefore lies in `X_h^k`. This is
`memSobolevInterval_of_piecewise_contDiffOn` applied panel by panel, the panel derivatives being
the derivatives of the panel polynomials. -/
theorem exists_mem_lagrangeSpace {n k : ℕ} {x : ℕ → ℝ} (hab : a < b)
    (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
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
    hx.lt (Fin.lt_def.1 hij) (by have := j.isLt; omega)
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
  obtain ⟨u, hu⟩ := exists_toContinuousMap_eq hab hgcont hmem
  exact ⟨u, ContinuousMap.ext fun t ↦ (hu t).trans (hfg t).symm⟩

/-- **`X_h^k` is the spline space read inside `H^1(a, b)`**: an element of `H^1(a, b)` lies in
`X_h^k` exactly when its continuous representative is a continuous piecewise polynomial, and
every such function arises this way. `Spline.splineSpace` is the definition of the continuous
piecewise polynomials; `FiniteElement.lagrangeSpace` is its copy inside `H^1(a, b)` that the
Galerkin theory needs, and the two are identified by
`FiniteElement.lagrangeSpaceEquiv`. -/
theorem lagrangeSpace_eq_map_splineSpace (hab : a < b) {n k : ℕ} {x : ℕ → ℝ}
    {u : SobolevInterval 1 a b} :
    u ∈ lagrangeSpace hab n x k ↔
      ∃ f ∈ Spline.splineSpace a b n x k 0, SobolevInterval.toContinuousMap hab u = f :=
  ⟨fun h ↦ ⟨_, h, rfl⟩, fun ⟨_, hf, hu⟩ ↦ by rw [mem_lagrangeSpace_iff, hu]; exact hf⟩

/-- The embedding restricted to `X_h^k`, as a linear map into the spline space. -/
noncomputable def toSplineSpace (hab : a < b) (n : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    lagrangeSpace hab n x k →ₗ[ℝ] Spline.splineSpace a b n x k 0 :=
  (SobolevInterval.toContinuousMap hab).toLinearMap.restrict fun _ hu ↦ hu

@[simp]
theorem coe_toSplineSpace (hab : a < b) {n k : ℕ} {x : ℕ → ℝ} (u : lagrangeSpace hab n x k) :
    (toSplineSpace hab n x k u : C(Icc a b, ℝ))
      = SobolevInterval.toContinuousMap hab (u : SobolevInterval 1 a b) := rfl

/-- **`X_h^k` and the spline space are isomorphic**, by the embedding `H^1(a, b) ↪ C([a, b], ℝ)`
restricted to `X_h^k`. -/
noncomputable def lagrangeSpaceEquiv {n : ℕ} {x : ℕ → ℝ} (hab : a < b)
    (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) (k : ℕ) :
    lagrangeSpace hab n x k ≃ₗ[ℝ] Spline.splineSpace a b n x k 0 :=
  LinearEquiv.ofBijective (toSplineSpace hab n x k)
    ⟨fun u v huv ↦ Subtype.ext (toContinuousMap_injective hab (congrArg Subtype.val huv)),
      fun f ↦ by
        obtain ⟨u, hu⟩ := exists_mem_lagrangeSpace hab hx hn f.2
        exact ⟨⟨u, by rw [mem_lagrangeSpace_iff, hu]; exact f.2⟩, Subtype.ext hu⟩⟩

/-- **The dimension of `X_h^k`** ([quarteroni2000numerical] §12.4.5): `dim X_h^k = n k + 1`, the
number of nodal values of a continuous piecewise polynomial of degree `k` on `n` panels. It is
`Spline.finrank_splineSpace` at smoothness `r = 0`, transported by
`FiniteElement.lagrangeSpaceEquiv`. -/
theorem finrank_lagrangeSpace {n : ℕ} {x : ℕ → ℝ} (hab : a < b)
    (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) (k : ℕ) :
    Module.finrank ℝ (lagrangeSpace hab n x k) = n * k + 1 := by
  rw [(lagrangeSpaceEquiv hab hx hn k).finrank_eq, Spline.finrank_splineSpace hx hn (Nat.zero_le k)]
  simp

theorem finiteDimensional_lagrangeSpace {n : ℕ} {x : ℕ → ℝ} (hab : a < b)
    (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) (k : ℕ) :
    FiniteDimensional ℝ (lagrangeSpace hab n x k) := by
  have h : FiniteDimensional ℝ (Spline.splineSpace a b n x k 0) :=
    Spline.finiteDimensional_splineSpace hx hn
  exact (lagrangeSpaceEquiv hab hx hn k).symm.finiteDimensional

/-! ### The hat functions of `X_h^1`

The shape functions of [quarteroni2000numerical] (12.61) are built as honest functions `ℝ → ℝ`
and only then pushed into `H^1(a, b)`. Writing `R_j` for the normalized ramp of the panel
`[x_j, x_{j+1}]` — zero to the left of `x_j`, rising linearly to `1` at `x_{j+1}`, constant
afterwards — and setting `R_{-1} = 1`, `R_j = 0` for `j ≥ n`, the hat at the node `i` is the
difference `R_{i-1} - R_i` for every `i` at once, endpoints included; this is
`FiniteElement.hatStep` and `FiniteElement.hatFun`. Its derivative is the difference of the two
panel indicators `FiniteElement.hatDerivFun`, and the two are related by
`FiniteElement.hasWeakDerivOn_hatFun`, which is
`memSobolevInterval_of_piecewise_contDiffOn` (a piecewise-`C¹` continuous function lies in
`H^1`) followed by the identification of the classical derivative off the nodes.
-/

/-- The **normalized ramp** of the panel `[x_j, x_{j+1}]`: `0` to the left of `x_j`, the affine
function rising to `1` at `x_{j+1}` on the panel, and `1` afterwards. The hat functions of
[quarteroni2000numerical] (12.61) are the successive differences of these ramps. -/
noncomputable def rampFun (x : ℕ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun t ↦ min (max (t - x j) 0) (x (j + 1) - x j) / (x (j + 1) - x j)

/-- The ramp is continuous, for any node sequence. -/
theorem continuous_rampFun (x : ℕ → ℝ) (j : ℕ) : Continuous (rampFun x j) :=
  (((continuous_id.sub continuous_const).max continuous_const).min continuous_const).div_const _

/-- The ramp vanishes to the left of its panel. -/
theorem rampFun_of_le_left {x : ℕ → ℝ} {j : ℕ} {t : ℝ} (hx : x j ≤ x (j + 1)) (ht : t ≤ x j) :
    rampFun x j t = 0 := by
  rw [rampFun, max_eq_right (by linarith), min_eq_left (by linarith), zero_div]

/-- On its panel the ramp is the affine function `(t - x_j)/(x_{j+1} - x_j)`. -/
theorem rampFun_of_mem {x : ℕ → ℝ} {j : ℕ} {t : ℝ} (h1 : x j ≤ t) (h2 : t ≤ x (j + 1)) :
    rampFun x j t = (t - x j) / (x (j + 1) - x j) := by
  rw [rampFun, max_eq_left (by linarith), min_eq_left (by linarith)]

/-- The ramp is `1` to the right of its panel. -/
theorem rampFun_of_right_le {x : ℕ → ℝ} {j : ℕ} {t : ℝ} (hx : x j < x (j + 1))
    (ht : x (j + 1) ≤ t) : rampFun x j t = 1 := by
  rw [rampFun, max_eq_left (by linarith), min_eq_right (by linarith), div_self (by linarith)]

/-- The **staircase** `R_{i-1}` of the partition: the constant `1` for `i = 0`, the normalized
ramp of the panel `[x_{i-1}, x_i]` for `1 ≤ i ≤ n`, and `0` beyond. The hat function at the node
`i` is `hatStep i - hatStep (i + 1)`. -/
noncomputable def hatStep (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : ℝ → ℝ :=
  if i = 0 then fun _ ↦ 1 else if i ≤ n then rampFun x (i - 1) else fun _ ↦ 0

/-- **The hat (shape) function** `φ_i` of [quarteroni2000numerical] (12.61), as a function
`ℝ → ℝ`: the continuous piecewise linear function that is `1` at the node `x_i` and `0` at every
other node, `(t - x_{i-1})/(x_i - x_{i-1})` on `[x_{i-1}, x_i]`, `(x_{i+1} - t)/(x_{i+1} - x_i)`
on `[x_i, x_{i+1}]` and `0` elsewhere. The end functions `φ_0` and `φ_n` have a single ramp,
which the uniform formula `hatStep i - hatStep (i + 1)` produces automatically. -/
noncomputable def hatFun (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : ℝ → ℝ :=
  fun t ↦ hatStep n x i t - hatStep n x (i + 1) t

/-- The staircase at `i = 0` is the constant `1`. -/
@[simp]
theorem hatStep_zero (n : ℕ) (x : ℕ → ℝ) : hatStep n x 0 = fun _ ↦ 1 := by
  rw [hatStep]; simp

/-- The staircase at an index in range is the ramp of the preceding panel. -/
theorem hatStep_of_mem {n : ℕ} (x : ℕ → ℝ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ n) :
    hatStep n x i = rampFun x (i - 1) := by
  rw [hatStep]; split_ifs <;> first | rfl | omega

/-- The staircase vanishes beyond the last node. -/
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

/-- On the panel `k` the staircases of index at most `k` have already risen to `1`. -/
theorem hatStep_eq_one (hx : Spline.IsPartition a b n x) {k i : ℕ} (hk : k < n) (hi : i ≤ k)
    {t : ℝ} (ht : x k ≤ t) : hatStep n x i t = 1 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  · simp
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [hatStep_of_mem x (by omega) (by omega)]
    simp only [Nat.add_sub_cancel]
    exact rampFun_of_right_le (hx.lt (by omega) (by omega))
      ((hx.mono (by omega) (by omega)).trans ht)

/-- On the panel `k` the staircases of index at least `k + 2` have not yet started. -/
theorem hatStep_eq_zero (hx : Spline.IsPartition a b n x) {k i : ℕ} (hi : k + 2 ≤ i)
    {t : ℝ} (ht : t ≤ x (k + 1)) : hatStep n x i t = 0 := by
  rcases lt_or_ge n i with h | h
  · rw [hatStep_of_lt x h]
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [hatStep_of_mem x (by omega) (by omega)]
    simp only [Nat.add_sub_cancel]
    exact rampFun_of_le_left (hx.mono (by omega) (by omega))
      (ht.trans (hx.mono (by omega) (by omega)))

/-- **The descending branch of the hat**: on the panel `[x_k, x_{k+1}]`, `φ_k` is
`(x_{k+1} - t)/(x_{k+1} - x_k)`. -/
theorem hatFun_eq_of_left (hx : Spline.IsPartition a b n x) {k : ℕ} (hk : k < n) {t : ℝ}
    (h1 : x k ≤ t) (h2 : t ≤ x (k + 1)) :
    hatFun n x k t = (x (k + 1) - t) / (x (k + 1) - x k) := by
  have hlt := hx.step k hk
  rw [hatFun, hatStep_eq_one hx hk le_rfl h1, hatStep_of_mem x (by omega) (by omega)]
  simp only [Nat.add_sub_cancel]
  rw [rampFun_of_mem h1 h2]
  have hne : x (k + 1) - x k ≠ 0 := by linarith
  field_simp
  ring

/-- **The ascending branch of the hat**: on the panel `[x_k, x_{k+1}]`, `φ_{k+1}` is
`(t - x_k)/(x_{k+1} - x_k)`. -/
theorem hatFun_eq_of_right (hx : Spline.IsPartition a b n x) {k : ℕ} (hk : k < n) {t : ℝ}
    (h1 : x k ≤ t) (h2 : t ≤ x (k + 1)) :
    hatFun n x (k + 1) t = (t - x k) / (x (k + 1) - x k) := by
  have hkn : k + 1 ≤ n := hk
  rw [hatFun, hatStep_of_mem x (by omega) hkn, hatStep_eq_zero hx (by omega) h2]
  simp only [Nat.add_sub_cancel]
  rw [rampFun_of_mem h1 h2, sub_zero]

/-- **The local support of the hat functions** ([quarteroni2000numerical] §12.4.5): only `φ_k`
and `φ_{k+1}` are nonzero on the panel `[x_k, x_{k+1}]`. -/
theorem hatFun_eq_zero_of_panel (hx : Spline.IsPartition a b n x) {k i : ℕ} (hk : k < n)
    (h1 : i ≠ k) (h2 : i ≠ k + 1) {t : ℝ} (ht1 : x k ≤ t) (ht2 : t ≤ x (k + 1)) :
    hatFun n x i t = 0 := by
  rcases lt_or_gt_of_ne h1 with h | h
  · rw [hatFun, hatStep_eq_one hx hk (by omega) ht1, hatStep_eq_one hx hk (by omega) ht1, sub_self]
  · rw [hatFun, hatStep_eq_zero hx (by omega) ht2, hatStep_eq_zero hx (by omega) ht2, sub_self]

/-- **The Lagrange interpolation property** `φ_i(x_j) = δ_{ij}` of
[quarteroni2000numerical] (12.61). -/
theorem hatFun_apply_node (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) {i j : ℕ} (hj : j ≤ n) :
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

/-- The derivative of the normalized ramp: the indicator of the open panel, times `1/h_j`. -/
noncomputable def rampDerivFun (x : ℕ → ℝ) (j : ℕ) : ℝ → ℝ :=
  (Ioo (x j) (x (j + 1))).indicator fun _ ↦ (x (j + 1) - x j)⁻¹

/-- The derivative of the staircase `FiniteElement.hatStep`. -/
noncomputable def hatStepDeriv (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : ℝ → ℝ :=
  if i = 0 then fun _ ↦ 0 else if i ≤ n then rampDerivFun x (i - 1) else fun _ ↦ 0

/-- **The weak derivative of the hat function** `φ_i`: `1/h_{i-1}` on the panel
`(x_{i-1}, x_i)`, `-1/h_i` on the panel `(x_i, x_{i+1})` and `0` elsewhere
(`FiniteElement.hasWeakDerivOn_hatFun`). -/
noncomputable def hatDerivFun (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : ℝ → ℝ :=
  fun t ↦ hatStepDeriv n x i t - hatStepDeriv n x (i + 1) t

/-- The ramp derivative is measurable. -/
theorem measurable_rampDerivFun (x : ℕ → ℝ) (j : ℕ) : Measurable (rampDerivFun x j) :=
  measurable_const.indicator measurableSet_Ioo

/-- The staircase derivative is measurable. -/
theorem measurable_hatStepDeriv (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : Measurable (hatStepDeriv n x i) := by
  rw [hatStepDeriv]
  split_ifs
  · exact measurable_const
  · exact measurable_rampDerivFun x _
  · exact measurable_const

/-- The hat derivative is measurable. -/
theorem measurable_hatDerivFun (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : Measurable (hatDerivFun n x i) :=
  (measurable_hatStepDeriv n x i).sub (measurable_hatStepDeriv n x (i + 1))

/-- Inside its panel the ramp derivative is `1/h_j`. -/
theorem rampDerivFun_of_mem {x : ℕ → ℝ} {j : ℕ} {t : ℝ} (ht : t ∈ Ioo (x j) (x (j + 1))) :
    rampDerivFun x j t = (x (j + 1) - x j)⁻¹ := indicator_of_mem ht _

/-- Outside its panel the ramp derivative vanishes. -/
theorem rampDerivFun_of_notMem {x : ℕ → ℝ} {j : ℕ} {t : ℝ} (ht : t ∉ Ioo (x j) (x (j + 1))) :
    rampDerivFun x j t = 0 := indicator_of_notMem ht _

/-- The staircase derivative at an index in range is the ramp derivative of the preceding
panel. -/
theorem hatStepDeriv_of_mem {n : ℕ} (x : ℕ → ℝ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ n) :
    hatStepDeriv n x i = rampDerivFun x (i - 1) := by
  rw [hatStepDeriv]; split_ifs <;> first | rfl | omega

/-- The staircase derivative is bounded by the reciprocal of the panel length. -/
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

/-- The bound `1/h_{i-1} + 1/h_i` on the weak derivative of the hat function `φ_i`. -/
noncomputable def hatBound (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  |(x i - x (i - 1))⁻¹| + |(x (i + 1) - x i)⁻¹|

/-- The weak derivative of the hat function is bounded by `FiniteElement.hatBound`. -/
theorem abs_hatDerivFun_le (n : ℕ) (x : ℕ → ℝ) (i : ℕ) (t : ℝ) :
    |hatDerivFun n x i t| ≤ hatBound x i := by
  refine (abs_sub _ _).trans ?_
  have h1 := abs_hatStepDeriv_le n x i t
  have h2 := abs_hatStepDeriv_le n x (i + 1) t
  simp only [Nat.add_sub_cancel] at h2
  exact add_le_add h1 h2

/-- The hat function lies in `L²(a, b)`: it is continuous and the interval is bounded. -/
theorem memLp_hatFun (n : ℕ) (x : ℕ → ℝ) (i : ℕ) :
    MemLp (hatFun n x i) 2 (volume.restrict (Ioo a b)) :=
  ContinuousOn.memLp_two_restrict_Ioo (a := a) (b := b) (continuous_hatFun n x i).continuousOn

/-- The derivative of the hat function lies in `L²(a, b)`: it is measurable and bounded. -/
theorem memLp_hatDerivFun (n : ℕ) (x : ℕ → ℝ) (i : ℕ) :
    MemLp (hatDerivFun n x i) 2 (volume.restrict (Ioo a b)) :=
  MemLp.of_bound (measurable_hatDerivFun n x i).aestronglyMeasurable (hatBound x i)
    (Filter.Eventually.of_forall fun t ↦ by
      rw [Real.norm_eq_abs]; exact abs_hatDerivFun_le n x i t)

section Partition

variable {n : ℕ} {x : ℕ → ℝ}

/-- The panels are disjoint, so on the panel `k` every other ramp derivative vanishes. -/
theorem rampDerivFun_eq_zero_of_ne (hx : Spline.IsPartition a b n x) {k j : ℕ} (hk : k < n)
    (hj : j ≤ n) (hjk : j ≠ k) {t : ℝ} (ht : t ∈ Ioo (x k) (x (k + 1))) :
    rampDerivFun x j t = 0 := by
  refine rampDerivFun_of_notMem fun htj ↦ ?_
  rcases lt_or_gt_of_ne hjk with h | h
  · exact absurd ((hx.mono (by omega) (by omega) : x (j + 1) ≤ x k).trans_lt ht.1)
      (not_lt.2 htj.2.le)
  · exact absurd (ht.2.trans_le (hx.mono (by omega) hj : x (k + 1) ≤ x j)) (not_lt.2 htj.1.le)

/-- On the panel `k` only the staircase of index `k + 1` has a nonzero derivative. -/
theorem hatStepDeriv_eq_zero_of_ne (hx : Spline.IsPartition a b n x) {k i : ℕ} (hk : k < n)
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

/-- On the panel `k` the staircase of index `k + 1` has derivative `1/h_k`. -/
theorem hatStepDeriv_eq {n : ℕ} {x : ℕ → ℝ} {k : ℕ} (hk : k < n) {t : ℝ}
    (ht : t ∈ Ioo (x k) (x (k + 1))) :
    hatStepDeriv n x (k + 1) t = (x (k + 1) - x k)⁻¹ := by
  have hkn : k + 1 ≤ n := hk
  rw [hatStepDeriv_of_mem x (by omega) hkn]
  exact rampDerivFun_of_mem ht

/-- **The descending slope**: on the panel `(x_k, x_{k+1})`, `φ_k' = -1/h_k`. -/
theorem hatDerivFun_eq_of_left (hx : Spline.IsPartition a b n x) {k : ℕ} (hk : k < n) {t : ℝ}
    (ht : t ∈ Ioo (x k) (x (k + 1))) :
    hatDerivFun n x k t = -(x (k + 1) - x k)⁻¹ := by
  rw [hatDerivFun, hatStepDeriv_eq_zero_of_ne hx hk (by omega) ht, hatStepDeriv_eq hk ht, zero_sub]

/-- **The ascending slope**: on the panel `(x_k, x_{k+1})`, `φ_{k+1}' = 1/h_k`. -/
theorem hatDerivFun_eq_of_right (hx : Spline.IsPartition a b n x) {k : ℕ} (hk : k < n) {t : ℝ}
    (ht : t ∈ Ioo (x k) (x (k + 1))) :
    hatDerivFun n x (k + 1) t = (x (k + 1) - x k)⁻¹ := by
  rw [hatDerivFun, hatStepDeriv_eq hk ht, hatStepDeriv_eq_zero_of_ne hx hk (by omega) ht, sub_zero]

/-- The derivatives of the other hat functions vanish on the panel `k`. -/
theorem hatDerivFun_eq_zero_of_panel (hx : Spline.IsPartition a b n x) {k i : ℕ} (hk : k < n)
    (h1 : i ≠ k) (h2 : i ≠ k + 1) {t : ℝ} (ht : t ∈ Ioo (x k) (x (k + 1))) :
    hatDerivFun n x i t = 0 := by
  rw [hatDerivFun, hatStepDeriv_eq_zero_of_ne hx hk h2 ht,
    hatStepDeriv_eq_zero_of_ne hx hk (by omega) ht, sub_zero]

/-- On a panel the hat function is affine, with slope the value of `FiniteElement.hatDerivFun`
there. This is the single fact behind the membership in the spline space, the smoothness on the
open panels and the identification of the classical derivative. -/
theorem exists_affine_hatFun (hx : Spline.IsPartition a b n x) {k : ℕ} (hk : k < n) (i : ℕ) :
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

/-- Inside a panel the classical derivative of the hat function is
`FiniteElement.hatDerivFun`. -/
theorem deriv_hatFun_eq (hx : Spline.IsPartition a b n x) {k i : ℕ} (hk : k < n) {t : ℝ}
    (ht : t ∈ Ioo (x k) (x (k + 1))) : deriv (hatFun n x i) t = hatDerivFun n x i t := by
  obtain ⟨c, d, hcd, hc⟩ := exists_affine_hatFun hx hk i
  have hev : hatFun n x i =ᶠ[nhds t] fun s ↦ c * s + d :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs ↦ hcd s (Ioo_subset_Icc_self hs)
  rw [hev.deriv_eq, hc t ht]
  simp

/-- The hat function is `C¹` on each open panel. -/
theorem contDiffOn_hatFun_panel (hx : Spline.IsPartition a b n x) {k i : ℕ} (hk : k < n) :
    ContDiffOn ℝ 1 (hatFun n x i) (Ioo (x k) (x (k + 1))) := by
  obtain ⟨c, d, hcd, -⟩ := exists_affine_hatFun hx hk i
  exact ((contDiff_const.mul contDiff_id).add contDiff_const).contDiffOn.congr
    fun t ht ↦ hcd t (Ioo_subset_Icc_self ht)

/-! ### The hat function as an element of `H^1(a, b)` -/

/-- The classical derivative of the hat function agrees almost everywhere on `(a, b)` with
`FiniteElement.hatDerivFun`: they differ only at the finitely many nodes. -/
theorem ae_deriv_hatFun_eq (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) (i : ℕ) :
    deriv (hatFun n x i) =ᵐ[volume.restrict (Ioo a b)] hatDerivFun n x i := by
  have hfin : ∀ᵐ t : ℝ, t ∉ x '' Iic n := by
    rw [ae_iff]
    have hset : {t : ℝ | ¬ t ∉ x '' Iic n} = x '' Iic n := by ext t; simp
    rw [hset]
    exact ((Set.finite_Iic n).image x).measure_zero volume
  refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
  filter_upwards [hfin] with t ht htI
  obtain ⟨j, hj1, hjn, hjmem, -⟩ := hx.exists_mem_panel hn (Ioo_subset_Icc_self htI)
  have hne : ∀ m ≤ n, t ≠ x m := fun m hm hcon ↦ ht ⟨m, hm, hcon.symm⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hk : k < n := by omega
  have htk : t ∈ Ioo (x k) (x (k + 1)) := by
    simp only [Nat.add_sub_cancel] at hjmem
    exact ⟨lt_of_le_of_ne hjmem.1 (Ne.symm (hne k (by omega))),
      lt_of_le_of_ne hjmem.2 (hne (k + 1) (by omega))⟩
  exact deriv_hatFun_eq hx hk htk

/-- **The hat function has the weak derivative `FiniteElement.hatDerivFun`**: it is continuous
and piecewise `C¹` with bounded panel derivatives, so
`memSobolevInterval_of_piecewise_contDiffOn` applies. -/
theorem hasWeakDerivOn_hatFun (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) (i : ℕ) :
    HasWeakDerivOn (hatFun n x i) (hatDerivFun n x i) a b := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  set y : Fin (N + 2) → ℝ := fun j ↦ x (j : ℕ) with hy
  have hymono : StrictMono y := fun i j hij ↦
    hx.lt (Fin.lt_def.1 hij) (by have := j.isLt; omega)
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

/-- **The hat function `φ_i` of `X_h^1`** ([quarteroni2000numerical] (12.61)), as an element of
`H^1(a, b)`: the `L²` class of `FiniteElement.hatFun` together with its weak derivative
`FiniteElement.hatDerivFun`. Building it with `SobolevInterval.mk` rather than through an
existence statement makes both components available definitionally, which is what the stiffness
and mass integrals need. -/
noncomputable def hatFunction (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) (i : ℕ) :
    SobolevInterval 1 a b :=
  SobolevInterval.mk ![(memLp_hatFun n x i).toLp _, (memLp_hatDerivFun n x i).toLp _]
    (fun j ↦ by
      fin_cases j
      · exact HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
          ((Lp.memLp _).locallyIntegrableOn (Ω := TopologicalSpace.Opens.Ioo a b) one_le_two)
      · exact hasWeakIteratedDerivOn_one.2 ((hasWeakDerivOn_hatFun hx hn i).congr_ae
          (memLp_hatFun n x i).coeFn_toLp.symm (memLp_hatDerivFun n x i).coeFn_toLp.symm))

/-- The function of the hat element is `FiniteElement.hatFun` almost everywhere. -/
theorem coeFn_deriv_hatFunction_zero (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) (i : ℕ) :
    ⇑(SobolevInterval.deriv (hatFunction hx hn i) 0)
      =ᵐ[volume.restrict (Ioo a b)] hatFun n x i :=
  (memLp_hatFun n x i).coeFn_toLp

/-- **The weak derivative of the hat element is `±1/h`**: it is
`FiniteElement.hatDerivFun` almost everywhere. -/
theorem coeFn_deriv_hatFunction_one (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) (i : ℕ) :
    ⇑(SobolevInterval.deriv (hatFunction hx hn i) 1)
      =ᵐ[volume.restrict (Ioo a b)] hatDerivFun n x i :=
  (memLp_hatDerivFun n x i).coeFn_toLp

/-- A node of the partition lies in `[a, b]`. -/
theorem node_mem_Icc (hx : Spline.IsPartition a b n x) {j : ℕ} (hj : j ≤ n) : x j ∈ Icc a b :=
  Set.mem_Icc.2 ⟨hx.left_le hj, hx.le_right hj⟩

/-- The continuous representative of the hat element is `FiniteElement.hatFun`. -/
theorem rep_hatFunction (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) (i : ℕ) {t : ℝ}
    (ht : t ∈ Icc a b) : SobolevInterval.rep (hatFunction hx hn i) t = hatFun n x i t :=
  SobolevInterval.rep_eq_of_continuousOn (hx.lt_of_pos hn) _
    (continuous_hatFun n x i).continuousOn (coeFn_deriv_hatFunction_zero hx hn i) ht

/-- **`φ_i(x_j) = δ_{ij}`** for the hat elements of `H^1(a, b)`. -/
theorem rep_hatFunction_node (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) {i j : ℕ}
    (hj : j ≤ n) :
    SobolevInterval.rep (hatFunction hx hn i) (x j) = if i = j then 1 else 0 := by
  rw [rep_hatFunction hx hn i (node_mem_Icc hx hj)]
  exact hatFun_apply_node hx hn hj

/-- **The hat elements lie in `X_h^1`**: they are continuous and affine on every panel. -/
theorem hatFunction_mem_lagrangeSpace (hab : a < b) (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
    (i : ℕ) : hatFunction hx hn i ∈ lagrangeSpace hab n x 1 := by
  refine ⟨hatFun n x i, ?_, fun t ↦ rep_hatFunction hx hn i t.2, fun j hj ↦ ?_⟩
  · rw [Nat.cast_zero]
    exact contDiffOn_zero.2 (continuous_hatFun n x i).continuousOn
  obtain ⟨c, d, hcd, -⟩ := exists_affine_hatFun hx hj i
  exact ⟨Polynomial.C c * Polynomial.X + Polynomial.C d, Polynomial.degree_linear_le,
    fun t ht ↦ by simpa using hcd t ht⟩

/-- **The interior hat elements lie in `X_h^{1,0}`**: they vanish at both endpoints. -/
theorem hatFunction_mem_lagrangeSpaceZero (hab : a < b) (hx : Spline.IsPartition a b n x)
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

/-- Evaluation of the continuous representative at a point of `[a, b]`, as a bounded linear
functional on `H^1(a, b)`; it is what turns a nodal-value argument into a linear one. -/
noncomputable def nodalCLM (hab : a < b) (t : ℝ) (ht : t ∈ Icc a b) :
    SobolevInterval 1 a b →L[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ (⟨t, ht⟩ : Icc a b)).comp (SobolevInterval.toContinuousMap hab)

/-- Nodal evaluation is the continuous representative. -/
@[simp]
theorem nodalCLM_apply (hab : a < b) (t : ℝ) (ht : t ∈ Icc a b) (u : SobolevInterval 1 a b) :
    nodalCLM hab t ht u = SobolevInterval.rep u t := rfl

/-- The hat functions as elements of `X_h^1`, indexed by the `n + 1` nodes. -/
noncomputable def hatElem (hab : a < b) (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
    (i : Fin (n + 1)) : lagrangeSpace hab n x 1 :=
  ⟨hatFunction hx hn (i : ℕ), hatFunction_mem_lagrangeSpace hab hx hn (i : ℕ)⟩

/-- The hat functions are linearly independent: evaluating a vanishing combination at the node
`x_j` returns its `j`-th coefficient. -/
theorem linearIndependent_hatElem (hab : a < b) (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) :
    LinearIndependent ℝ (hatElem hab hx hn) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hjn : (j : ℕ) ≤ n := Nat.lt_succ_iff.1 j.isLt
  have hsub : (∑ i, g i • hatFunction hx hn (i : ℕ)) = 0 := by
    have := congrArg (Subtype.val) hg
    simpa [hatElem] using this
  have hval := congrArg (nodalCLM hab _ (node_mem_Icc hx hjn)) hsub
  simp only [map_sum, map_smul, smul_eq_mul, map_zero, nodalCLM_apply] at hval
  rw [Finset.sum_congr rfl fun i _ ↦ congrArg (g i * ·)
    (rep_hatFunction_node hx hn (i := (i : ℕ)) (j := (j : ℕ)) hjn)] at hval
  simpa [Fin.val_inj] using hval

/-- **The hat basis of `X_h^1`** ([quarteroni2000numerical] (12.61)): the `n + 1` shape
functions `φ_0, …, φ_n` are a basis, the nodal values being the degrees of freedom. -/
noncomputable def hatBasis (hab : a < b) (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) :
    Module.Basis (Fin (n + 1)) ℝ (lagrangeSpace hab n x 1) :=
  haveI := finiteDimensional_lagrangeSpace hab hx hn 1
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_hatElem hab hx hn)
    (by rw [Fintype.card_fin, finrank_lagrangeSpace hab hx hn 1]; ring)

/-- The hat basis consists of the hat functions. -/
@[simp]
theorem hatBasis_apply (hab : a < b) (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
    (i : Fin (n + 1)) : hatBasis hab hx hn i = hatElem hab hx hn i := by
  have := finiteDimensional_lagrangeSpace hab hx hn 1
  rw [hatBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- **The coordinates in the hat basis are the nodal values.** -/
theorem hatBasis_repr (hab : a < b) (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
    (v : lagrangeSpace hab n x 1) (j : Fin (n + 1)) :
    (hatBasis hab hx hn).repr v j
      = SobolevInterval.rep (v : SobolevInterval 1 a b) (x (j : ℕ)) := by
  have hjn : (j : ℕ) ≤ n := Nat.lt_succ_iff.1 j.isLt
  have hsub : (∑ i, (hatBasis hab hx hn).repr v i • hatFunction hx hn (i : ℕ))
      = (v : SobolevInterval 1 a b) := by
    have := congrArg (Subtype.val) ((hatBasis hab hx hn).sum_repr v)
    simpa [hatElem] using this
  have hval := congrArg (nodalCLM hab _ (node_mem_Icc hx hjn)) hsub
  simp only [map_sum, map_smul, smul_eq_mul, nodalCLM_apply] at hval
  rw [Finset.sum_congr rfl fun i _ ↦ congrArg ((hatBasis hab hx hn).repr v i * ·)
    (rep_hatFunction_node hx hn (i := (i : ℕ)) (j := (j : ℕ)) hjn)] at hval
  simpa [Fin.val_inj] using hval

/-- **Every element of `X_h^1` is the combination of the hat functions with its nodal values**,
`v_h = ∑_i v_h(x_i) φ_i` ([quarteroni2000numerical] §12.4.5). -/
theorem eq_sum_hatFunction (hab : a < b) (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
    (v : lagrangeSpace hab n x 1) :
    (v : SobolevInterval 1 a b) = ∑ i : Fin (n + 1),
      SobolevInterval.rep (v : SobolevInterval 1 a b) (x (i : ℕ)) • hatFunction hx hn (i : ℕ) := by
  have hsub : (∑ i, (hatBasis hab hx hn).repr v i • hatFunction hx hn (i : ℕ))
      = (v : SobolevInterval 1 a b) := by
    have := congrArg (Subtype.val) ((hatBasis hab hx hn).sum_repr v)
    simpa [hatElem] using this
  refine hsub.symm.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [hatBasis_repr hab hx hn v i]

/-- The interior hat functions `φ_1, …, φ_{n-1}`, a family in `X_h^{1,0}`. -/
noncomputable def hatElemZero (hab : a < b) (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
    (i : Fin (n - 1)) : lagrangeSpaceZero hab n x 1 :=
  ⟨hatFunction hx hn ((i : ℕ) + 1), hatFunction_mem_lagrangeSpaceZero hab hx hn (by omega)
    (by have := i.isLt; omega)⟩

/-- The interior hat functions are linearly independent. -/
theorem linearIndependent_hatElemZero (hab : a < b) (hx : Spline.IsPartition a b n x)
    (hn : 1 ≤ n) : LinearIndependent ℝ (hatElemZero hab hx hn) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hjn : (j : ℕ) + 1 ≤ n := by have := j.isLt; omega
  have hsub : (∑ i, g i • hatFunction hx hn ((i : ℕ) + 1)) = 0 := by
    have := congrArg (Subtype.val) hg
    simpa [hatElemZero] using this
  have hval := congrArg (nodalCLM hab _ (node_mem_Icc hx hjn)) hsub
  simp only [map_sum, map_smul, smul_eq_mul, map_zero, nodalCLM_apply] at hval
  rw [Finset.sum_congr rfl fun i _ ↦ congrArg (g i * ·)
    (rep_hatFunction_node hx hn (i := (i : ℕ) + 1) (j := (j : ℕ) + 1) hjn)] at hval
  simpa [Fin.val_inj] using hval

/-- The interior hat functions span `X_h^{1,0}`: an element of `X_h^{1,0}` is the combination of
all the hat functions with its nodal values, and the two endpoint values vanish. -/
theorem top_le_span_hatElemZero (hab : a < b) (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) :
    ⊤ ≤ Submodule.span ℝ (Set.range (hatElemZero hab hx hn)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rintro v -
  have hrepr := eq_sum_hatFunction hab hx hn ⟨(v : SobolevInterval 1 a b), v.2.1⟩
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at hrepr
  simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hrepr
  have hc0 : SobolevInterval.rep (v : SobolevInterval 1 a b) (x 0) = 0 := by
    rw [hx.first]; exact SobolevIntervalZero.rep_left_eq_zero hab v.2.2
  have hcl : SobolevInterval.rep (v : SobolevInterval 1 a b) (x (m + 1)) = 0 := by
    rw [hx.last]; exact SobolevIntervalZero.rep_right_eq_zero hab v.2.2
  rw [hc0, hcl] at hrepr
  simp only [zero_smul, zero_add, add_zero] at hrepr
  have hv : v = ∑ i : Fin m,
      SobolevInterval.rep (v : SobolevInterval 1 a b) (x ((i : ℕ) + 1))
        • hatElemZero hab hx hn i :=
    Subtype.ext (hrepr.trans (by simp [hatElemZero]))
  rw [hv]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **The interior hat basis of `X_h^{1,0}`** ([quarteroni2000numerical] (12.57)): the `n - 1`
shape functions attached to the interior nodes. -/
noncomputable def hatBasisZero (hab : a < b) (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) :
    Module.Basis (Fin (n - 1)) ℝ (lagrangeSpaceZero hab n x 1) :=
  Module.Basis.mk (linearIndependent_hatElemZero hab hx hn) (top_le_span_hatElemZero hab hx hn)

/-- The interior hat basis consists of the interior hat functions. -/
@[simp]
theorem hatBasisZero_apply (hab : a < b) (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
    (i : Fin (n - 1)) : hatBasisZero hab hx hn i = hatElemZero hab hx hn i :=
  congrFun (Module.Basis.coe_mk _ _) i

/-- **`dim X_h^{1,0} = n - 1`** ([quarteroni2000numerical] §12.4.5, the book's `N = nk - 1` at
`k = 1`). -/
theorem finrank_lagrangeSpaceZero_one (hab : a < b) (hx : Spline.IsPartition a b n x)
    (hn : 1 ≤ n) : Module.finrank ℝ (lagrangeSpaceZero hab n x 1) = n - 1 := by
  rw [Module.finrank_eq_card_basis (hatBasisZero hab hx hn), Fintype.card_fin]

end Partition

/-! ### Elementary integrals -/

/-- The integral of a quadratic polynomial over an interval. -/
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

/-- `∫_u^v (v - t)/(v - u) = (v - u)/2`. -/
theorem integral_ramp_left (huv : u < v) :
    ∫ t in u..v, (v - t) / (v - u) = (v - u) / 2 := by
  have hne : v - u ≠ 0 := by linarith
  rw [integral_congr (g := fun t ↦ 0 * t ^ 2 + (-(v - u)⁻¹) * t + v * (v - u)⁻¹)
    (fun t _ ↦ by field_simp; ring), integral_quadratic]
  field_simp
  ring

/-- `∫_u^v (t - u)/(v - u) = (v - u)/2`. -/
theorem integral_ramp_right (huv : u < v) :
    ∫ t in u..v, (t - u) / (v - u) = (v - u) / 2 := by
  have hne : v - u ≠ 0 := by linarith
  rw [integral_congr (g := fun t ↦ 0 * t ^ 2 + (v - u)⁻¹ * t + (-(u * (v - u)⁻¹)))
    (fun t _ ↦ by field_simp; ring), integral_quadratic]
  field_simp
  ring

/-- `∫_u^v ((v - t)/(v - u))² = (v - u)/3`. -/
theorem integral_ramp_left_sq (huv : u < v) :
    ∫ t in u..v, (v - t) / (v - u) * ((v - t) / (v - u)) = (v - u) / 3 := by
  have hne : v - u ≠ 0 := by linarith
  rw [integral_congr (g := fun t ↦ ((v - u) ^ 2)⁻¹ * t ^ 2 + (-(2 * v * ((v - u) ^ 2)⁻¹)) * t
      + v ^ 2 * ((v - u) ^ 2)⁻¹) (fun t _ ↦ by field_simp; ring), integral_quadratic]
  field_simp
  ring

/-- `∫_u^v ((t - u)/(v - u))² = (v - u)/3`. -/
theorem integral_ramp_right_sq (huv : u < v) :
    ∫ t in u..v, (t - u) / (v - u) * ((t - u) / (v - u)) = (v - u) / 3 := by
  have hne : v - u ≠ 0 := by linarith
  rw [integral_congr (g := fun t ↦ ((v - u) ^ 2)⁻¹ * t ^ 2 + (-(2 * u * ((v - u) ^ 2)⁻¹)) * t
      + u ^ 2 * ((v - u) ^ 2)⁻¹) (fun t _ ↦ by field_simp; ring), integral_quadratic]
  field_simp
  ring

/-- `∫_u^v (v - t)(t - u)/(v - u)² = (v - u)/6`. -/
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

/-- The integral of an affine function on `[u, v]` written in the nodal basis of the panel. -/
theorem integral_panel_affine (huv : u < v) (p q : ℝ) :
    ∫ t in u..v, (p * ((v - t) / (v - u)) + q * ((t - u) / (v - u))) = (p + q) * (v - u) / 2 := by
  have hne : v - u ≠ 0 := by linarith
  rw [integral_congr (g := fun t ↦ 0 * t ^ 2 + (q - p) / (v - u) * t + (p * v - q * u) / (v - u))
    (fun t _ ↦ by field_simp; ring), integral_quadratic]
  field_simp
  ring

/-- The integral of the product of two affine functions on `[u, v]`, written in the nodal basis
of the panel: `∫ (pL + qR)(p'L + q'R) = (pp' + qq') h/3 + (pq' + qp') h/6`. -/
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

/-- **The hat functions on one panel**: on `[x_k, x_{k+1}]`, `φ_i` is the combination of the two
panel ramps with its nodal values `δ_{ik}` and `δ_{i,k+1}`. -/
theorem hatFun_eq_panel (hx : Spline.IsPartition a b n x) {k : ℕ} (hk : k < n) (i : ℕ) {t : ℝ}
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

/-- **The derivative of the hat functions on one panel**: on `(x_k, x_{k+1})`, `φ_i'` is the
difference quotient of its two nodal values. -/
theorem hatDerivFun_eq_panel (hx : Spline.IsPartition a b n x) {k : ℕ} (hk : k < n) (i : ℕ)
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

/-- Interval integrals over a panel do not see the endpoints. -/
private theorem integral_congr_Ioo {u v : ℝ} (huv : u ≤ v) {f g : ℝ → ℝ}
    (h : EqOn f g (Ioo u v)) : ∫ t in u..v, f t = ∫ t in u..v, g t := by
  rw [integral_of_le huv, integral_of_le huv, integral_Ioc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

/-- **The panel mass integral** `∫_{x_k}^{x_{k+1}} φ_i φ_j`. -/
theorem integral_panel_hat_mul_hat (hx : Spline.IsPartition a b n x) {k : ℕ} (hk : k < n)
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

/-- **The panel advection integral** `∫_{x_k}^{x_{k+1}} φ_i' φ_j`. -/
theorem integral_panel_hatDeriv_mul_hat (hx : Spline.IsPartition a b n x) {k : ℕ} (hk : k < n)
    (i j : ℕ) :
    ∫ t in (x k)..(x (k + 1)), hatDerivFun n x i t * hatFun n x j t
      = ((if i = k + 1 then (1 : ℝ) else 0) - (if i = k then (1 : ℝ) else 0))
        * ((if j = k then (1 : ℝ) else 0) + (if j = k + 1 then (1 : ℝ) else 0)) / 2 := by
  have hlt := hx.step k hk
  have hne : x (k + 1) - x k ≠ 0 := by linarith
  rw [integral_congr_Ioo hlt.le (f := fun t ↦ hatDerivFun n x i t * hatFun n x j t)
    (g := fun t ↦ (((if i = k + 1 then (1 : ℝ) else 0) - (if i = k then (1 : ℝ) else 0))
        / (x (k + 1) - x k))
      * ((if j = k then (1 : ℝ) else 0) * ((x (k + 1) - t) / (x (k + 1) - x k))
        + (if j = k + 1 then (1 : ℝ) else 0) * ((t - x k) / (x (k + 1) - x k))))
    (fun t ht ↦ by
      dsimp only
      rw [hatDerivFun_eq_panel hx hk i ht, hatFun_eq_panel hx hk j ht.1.le ht.2.le]),
    intervalIntegral.integral_const_mul, integral_panel_affine hlt]
  field_simp

/-- **The panel stiffness integral** `∫_{x_k}^{x_{k+1}} φ_i' φ_j'`. -/
theorem integral_panel_hatDeriv_mul_hatDeriv (hx : Spline.IsPartition a b n x) {k : ℕ}
    (hk : k < n) (i j : ℕ) :
    ∫ t in (x k)..(x (k + 1)), hatDerivFun n x i t * hatDerivFun n x j t
      = ((if i = k + 1 then (1 : ℝ) else 0) - (if i = k then (1 : ℝ) else 0))
        * ((if j = k + 1 then (1 : ℝ) else 0) - (if j = k then (1 : ℝ) else 0))
        / (x (k + 1) - x k) := by
  have hlt := hx.step k hk
  have hne : x (k + 1) - x k ≠ 0 := by linarith
  rw [integral_congr_Ioo hlt.le (f := fun t ↦ hatDerivFun n x i t * hatDerivFun n x j t)
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

/-- The normalized ramp takes values in `[0, 1]`, for any node sequence. -/
theorem abs_rampFun_le_one (x : ℕ → ℝ) (j : ℕ) (t : ℝ) : |rampFun x j t| ≤ 1 := by
  have hm0 : (0 : ℝ) ≤ max (t - x j) 0 := le_max_right _ _
  rcases lt_trichotomy (x (j + 1) - x j) 0 with h | h | h
  · rw [rampFun, min_eq_right (by linarith), div_self (by linarith)]
    norm_num
  · rw [rampFun, h, div_zero]
    norm_num
  · have h1 : min (max (t - x j) 0) (x (j + 1) - x j) ≤ x (j + 1) - x j := min_le_right _ _
    have h2 : (0 : ℝ) ≤ min (max (t - x j) 0) (x (j + 1) - x j) := le_min hm0 h.le
    rw [rampFun, abs_of_nonneg (by positivity), div_le_one h]
    exact h1

/-- The staircase takes values in `[0, 1]`. -/
theorem abs_hatStep_le_one (n : ℕ) (x : ℕ → ℝ) (i : ℕ) (t : ℝ) : |hatStep n x i t| ≤ 1 := by
  rw [hatStep]
  split_ifs
  · norm_num
  · exact abs_rampFun_le_one x _ t
  · norm_num

/-- The hat function is bounded by `2`, for any node sequence. -/
theorem abs_hatFun_le_two (n : ℕ) (x : ℕ → ℝ) (i : ℕ) (t : ℝ) : |hatFun n x i t| ≤ 2 := by
  refine (abs_sub _ _).trans ?_
  have := abs_hatStep_le_one n x i t
  have := abs_hatStep_le_one n x (i + 1) t
  linarith

/-- The hat function is measurable. -/
theorem measurable_hatFun (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : Measurable (hatFun n x i) :=
  (continuous_hatFun n x i).measurable

/-- A globally measurable function with a global bound is interval integrable. -/
theorem intervalIntegrable_of_bounded {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ t, |f t| ≤ C) (u v : ℝ) : IntervalIntegrable f volume u v := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := C) ?_ hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ↦ by rw [Real.norm_eq_abs]; exact hb t)
  rw [Real.volume_uIoc]
  exact ENNReal.ofReal_ne_top

/-- The product of two hat derivatives is interval integrable. -/
theorem intervalIntegrable_hatDeriv_mul_hatDeriv (n : ℕ) (x : ℕ → ℝ) (i j : ℕ) (u v : ℝ) :
    IntervalIntegrable (fun t ↦ hatDerivFun n x i t * hatDerivFun n x j t) volume u v :=
  intervalIntegrable_of_bounded ((measurable_hatDerivFun n x i).mul (measurable_hatDerivFun n x j))
    (fun t ↦ by
      rw [Pi.mul_apply, abs_mul]
      exact mul_le_mul (abs_hatDerivFun_le n x i t) (abs_hatDerivFun_le n x j t) (abs_nonneg _)
        ((abs_nonneg _).trans (abs_hatDerivFun_le n x i t))) u v

/-- The product of a hat derivative and a hat function is interval integrable. -/
theorem intervalIntegrable_hatDeriv_mul_hat (n : ℕ) (x : ℕ → ℝ) (i j : ℕ) (u v : ℝ) :
    IntervalIntegrable (fun t ↦ hatDerivFun n x i t * hatFun n x j t) volume u v :=
  intervalIntegrable_of_bounded ((measurable_hatDerivFun n x i).mul (measurable_hatFun n x j))
    (fun t ↦ by
      rw [Pi.mul_apply, abs_mul]
      exact mul_le_mul (abs_hatDerivFun_le n x i t) (abs_hatFun_le_two n x j t) (abs_nonneg _)
        ((abs_nonneg _).trans (abs_hatDerivFun_le n x i t))) u v

/-- The product of two hat functions is interval integrable. -/
theorem intervalIntegrable_hat_mul_hat (n : ℕ) (x : ℕ → ℝ) (i j : ℕ) (u v : ℝ) :
    IntervalIntegrable (fun t ↦ hatFun n x i t * hatFun n x j t) volume u v :=
  intervalIntegrable_of_bounded ((measurable_hatFun n x i).mul (measurable_hatFun n x j))
    (fun t ↦ by
      rw [Pi.mul_apply, abs_mul]
      exact mul_le_mul (abs_hatFun_le_two n x i t) (abs_hatFun_le_two n x j t) (abs_nonneg _)
        (by norm_num)) u v

/-- The integrand of the elliptic form on two hat functions, with constant coefficients. -/
noncomputable def hatFormIntegrand (n : ℕ) (x : ℕ → ℝ) (ε β γ : ℝ) (i j : ℕ) : ℝ → ℝ :=
  fun t ↦ ε * (hatDerivFun n x i t * hatDerivFun n x j t)
    + β * (hatDerivFun n x i t * hatFun n x j t) + γ * (hatFun n x i t * hatFun n x j t)

/-- The integrand of the elliptic form on two hat functions is interval integrable. -/
theorem intervalIntegrable_hatFormIntegrand (n : ℕ) (x : ℕ → ℝ) (ε β γ : ℝ) (i j : ℕ) (u v : ℝ) :
    IntervalIntegrable (hatFormIntegrand n x ε β γ i j) volume u v :=
  (((intervalIntegrable_hatDeriv_mul_hatDeriv n x i j u v).const_mul ε).add
    ((intervalIntegrable_hatDeriv_mul_hat n x i j u v).const_mul β)).add
      ((intervalIntegrable_hat_mul_hat n x i j u v).const_mul γ)

section PanelSum

variable {n : ℕ} {x : ℕ → ℝ}

/-- **The panel value of the elliptic form on two hat functions**, for constant coefficients. -/
theorem integral_panel_hatFormIntegrand (hx : Spline.IsPartition a b n x) {k : ℕ} (hk : k < n)
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

/-- A panel on which neither hat function is supported contributes nothing. -/
theorem integral_panel_hatFormIntegrand_eq_zero (hx : Spline.IsPartition a b n x) {k : ℕ}
    (hk : k < n) (ε β γ : ℝ) {i j : ℕ} (h : (i ≠ k ∧ i ≠ k + 1) ∨ (j ≠ k ∧ j ≠ k + 1)) :
    ∫ t in (x k)..(x (k + 1)), hatFormIntegrand n x ε β γ i j t = 0 := by
  rw [integral_panel_hatFormIntegrand hx hk]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

/-- The integral over `(a, b)` is the sum of the panel integrals. -/
theorem integral_Ioo_eq_sum_panels (hx : Spline.IsPartition a b n x) {F : ℝ → ℝ}
    (hF : ∀ k, IntervalIntegrable F volume (x k) (x (k + 1))) :
    ∫ t in Ioo a b, F t = ∑ k ∈ Finset.range n, ∫ t in (x k)..(x (k + 1)), F t := by
  rw [intervalIntegral.sum_integral_adjacent_intervals (a := x) fun k _ ↦ hF k,
    ← EllipticInterval.intervalIntegral_eq_setIntegral_Ioo hx.le, hx.first, hx.last]

end PanelSum

/-! ### The stiffness and mass matrices -/

/-- A constant coefficient as an element of `L^∞(a, b)`. -/
noncomputable def constLinfty (a b : ℝ) (c : ℝ) : Lp ℝ ⊤ (volume.restrict (Ioo a b)) :=
  (ContinuousOn.memLp_top_restrict_Ioo (a := a) (b := b) (g := fun _ ↦ c) continuousOn_const).toLp _

/-- The `L^∞` class of a constant is that constant almost everywhere. -/
theorem coeFn_constLinfty (a b c : ℝ) :
    ⇑(constLinfty a b c) =ᵐ[volume.restrict (Ioo a b)] fun _ ↦ c :=
  MemLp.coeFn_toLp _

variable (a b) in
/-- **The stiffness matrix** `A_fe` of [quarteroni2000numerical] (12.48): `A_ij = a(φ_j, φ_i)`
for a family `φ` of trial functions, the Gram matrix of the elliptic form. -/
noncomputable def stiffnessMatrix {ι : Type*} (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo a b)))
    (φ : ι → SobolevInterval 1 a b) : Matrix ι ι ℝ :=
  (EllipticInterval.form a b α β γ).gramMatrix φ

/-- The entries of the stiffness matrix are `a_{ij} = a(φ_j, φ_i)`. -/
theorem stiffnessMatrix_apply {ι : Type*} (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo a b)))
    (φ : ι → SobolevInterval 1 a b) (i j : ι) :
    stiffnessMatrix a b α β γ φ i j = EllipticInterval.form a b α β γ (φ j) (φ i) := rfl

variable (a b) in
/-- **The mass matrix** `M_ij = ∫_a^b φ_j φ_i` ([quarteroni2000numerical] (13.14)): the Gram
matrix of the trial functions for the `L²(a, b)` inner product. -/
noncomputable def massMatrix {ι : Type*} (φ : ι → SobolevInterval 1 a b) : Matrix ι ι ℝ :=
  stiffnessMatrix a b (constLinfty a b 0) (constLinfty a b 0) (constLinfty a b 1) φ

/-- The entries of the mass matrix are `m_{ij} = ∫ φ_j φ_i`. -/
theorem massMatrix_apply {ι : Type*} (φ : ι → SobolevInterval 1 a b) (i j : ι) :
    massMatrix a b φ i j =
      EllipticInterval.form a b (constLinfty a b 0) (constLinfty a b 0) (constLinfty a b 1)
        (φ j) (φ i) := rfl

section Form

variable {n : ℕ} {x : ℕ → ℝ}

/-- The elliptic form with constant coefficients, on two hat functions, is the integral of
`FiniteElement.hatFormIntegrand`. -/
theorem form_apply_hatFunction (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) (ε β γ : ℝ)
    (i j : ℕ) :
    EllipticInterval.form a b (constLinfty a b ε) (constLinfty a b β) (constLinfty a b γ)
        (hatFunction hx hn j) (hatFunction hx hn i)
      = ∫ t in Ioo a b, hatFormIntegrand n x ε β γ j i t := by
  rw [EllipticInterval.form_apply]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_constLinfty a b ε, coeFn_constLinfty a b β, coeFn_constLinfty a b γ,
    coeFn_deriv_hatFunction_one hx hn j, coeFn_deriv_hatFunction_one hx hn i,
    coeFn_deriv_hatFunction_zero hx hn j, coeFn_deriv_hatFunction_zero hx hn i]
    with t h1 h2 h3 h4 h5 h6 h7
  simp only [h1, h2, h3, h4, h5, h6, h7, hatFormIntegrand]
  ring

/-- The elliptic form with constant coefficients, on two hat functions, is the sum of its panel
contributions. -/
theorem form_apply_hatFunction_eq_sum (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
    (ε β γ : ℝ) (i j : ℕ) :
    EllipticInterval.form a b (constLinfty a b ε) (constLinfty a b β) (constLinfty a b γ)
        (hatFunction hx hn j) (hatFunction hx hn i)
      = ∑ k ∈ Finset.range n, ∫ t in (x k)..(x (k + 1)), hatFormIntegrand n x ε β γ j i t := by
  rw [form_apply_hatFunction hx hn ε β γ i j,
    integral_Ioo_eq_sum_panels hx fun k ↦ intervalIntegrable_hatFormIntegrand n x ε β γ j i _ _]

/-- **The entries of the stiffness matrix on a uniform mesh** ([quarteroni2000numerical]
§12.4.5, the matrix Program 95 assembles): for constant coefficients `ε, β, γ` and a uniform
mesh of step `h`, the value `a(φ_j, φ_i)` at an interior node `i` is `2ε/h + 2γh/3` on the
diagonal, `-ε/h - β/2 + γh/6` at `j = i - 1` and `-ε/h + β/2 + γh/6` at `j = i + 1`, and
vanishes otherwise. -/
theorem form_apply_hatFunction_uniform (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
    {h : ℝ} (hh : 0 < h) (huni : ∀ k < n, x (k + 1) - x k = h) (ε β γ : ℝ) {i j : ℕ}
    (hi1 : 1 ≤ i) (hi2 : i < n) :
    EllipticInterval.form a b (constLinfty a b ε) (constLinfty a b β) (constLinfty a b γ)
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

/-- **The supports of two hat functions more than one node apart meet in a null set**: all three
products entering the elliptic form vanish almost everywhere. -/
theorem ae_hat_products_eq_zero (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) {i j : ℕ}
    (hij : i + 1 < j ∨ j + 1 < i) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      hatDerivFun n x j t * hatDerivFun n x i t = 0 ∧
        hatDerivFun n x j t * hatFun n x i t = 0 ∧ hatFun n x j t * hatFun n x i t = 0 := by
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
  have hk : k < n := by omega
  have htk : t ∈ Ioo (x k) (x (k + 1)) := by
    simp only [Nat.add_sub_cancel] at hpmem
    exact ⟨lt_of_le_of_ne hpmem.1 (Ne.symm (hne k (by omega))),
      lt_of_le_of_ne hpmem.2 (hne (k + 1) (by omega))⟩
  rcases (by omega : (i ≠ k ∧ i ≠ k + 1) ∨ (j ≠ k ∧ j ≠ k + 1)) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hatFun_eq_zero_of_panel hx hk h1 h2 htk.1.le htk.2.le,
      hatDerivFun_eq_zero_of_panel hx hk h1 h2 htk]
    simp
  · rw [hatFun_eq_zero_of_panel hx hk h1 h2 htk.1.le htk.2.le,
      hatDerivFun_eq_zero_of_panel hx hk h1 h2 htk]
    simp

/-- **The elliptic form vanishes on two hat functions more than one node apart**, for arbitrary
`L^∞` coefficients. -/
theorem form_apply_hatFunction_eq_zero (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
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

/-- **Sparsity of the stiffness matrix** ([quarteroni2000numerical] §12.4.5): in the hat basis,
`a_{ij} = 0` whenever `j ∉ {i - 1, i, i + 1}`, so `A_fe` is tridiagonal. -/
theorem stiffnessMatrix_eq_zero_of_lt (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
    (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo a b))) {i j : ℕ} (hij : i + 1 < j ∨ j + 1 < i) :
    stiffnessMatrix a b α β γ (fun k : ℕ ↦ hatFunction hx hn k) i j = 0 :=
  form_apply_hatFunction_eq_zero hx hn α β γ hij

/-- **The stiffness matrix in the interior hat basis is tridiagonal**
([quarteroni2000numerical] §12.4.5). -/
theorem isTridiagonal_stiffnessMatrix (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
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

/-- **The stiffness matrix on a uniform mesh** ([quarteroni2000numerical] §12.4.5, the matrix
assembled by Program 95): in the interior hat basis of `X_h^{1,0}` with constant coefficients,
`A_fe = (ε/h) tridiag(-1, 2, -1) + (β/2) tridiag(-1, 0, 1) + (γ h/6) tridiag(1, 4, 1)`. For
`β = γ = 0` this is `ε h` times the centred finite difference matrix. -/
theorem stiffnessMatrix_uniform_eq (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) {h : ℝ}
    (hh : 0 < h) (huni : ∀ k < n, x (k + 1) - x k = h) (ε β γ : ℝ) :
    (stiffnessMatrix a b (constLinfty a b ε) (constLinfty a b β) (constLinfty a b γ)
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

/-- **The mass matrix on a uniform mesh** ([quarteroni2000numerical] §13.3): `M = (h/6)
tridiag(1, 4, 1)`, that is `∫ φ_i² = 2h/3` and `∫ φ_i φ_{i±1} = h/6`. -/
theorem massMatrix_uniform_eq (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) {h : ℝ}
    (hh : 0 < h) (huni : ∀ k < n, x (k + 1) - x k = h) :
    (massMatrix a b fun i : Fin (n - 1) ↦ hatFunction hx hn ((i : ℕ) + 1))
      = (h / 6) • Matrix.symmTridiagonalToeplitz (n - 1) 1 4 := by
  rw [massMatrix, stiffnessMatrix_uniform_eq hx hn hh huni 0 0 1]
  simp

end Uniform

section PosDef

variable {n : ℕ} {x : ℕ → ℝ}

/-- The interior hat functions as a family in `H^1_0(a, b)`. -/
noncomputable def hatElemH0 (hab : a < b) (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
    (i : Fin (n - 1)) : SobolevIntervalZero a b :=
  ⟨hatFunction hx hn ((i : ℕ) + 1),
    (hatFunction_mem_lagrangeSpaceZero hab hx hn (by omega) (by have := i.isLt; omega)).2⟩

/-- The interior hat functions are linearly independent in `H^1_0(a, b)`. -/
theorem linearIndependent_hatElemH0 (hab : a < b) (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) :
    LinearIndependent ℝ (hatElemH0 hab hx hn) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hjn : (j : ℕ) + 1 ≤ n := by have := j.isLt; omega
  have hsub : (∑ i, g i • hatFunction hx hn ((i : ℕ) + 1)) = 0 := by
    have := congrArg (Subtype.val) hg
    simpa [hatElemH0] using this
  have hval := congrArg (nodalCLM hab _ (node_mem_Icc hx hjn)) hsub
  simp only [map_sum, map_smul, smul_eq_mul, map_zero, nodalCLM_apply] at hval
  rw [Finset.sum_congr rfl fun i _ ↦ congrArg (g i * ·)
    (rep_hatFunction_node hx hn (i := (i : ℕ) + 1) (j := (j : ℕ) + 1) hjn)] at hval
  simpa [Fin.val_inj] using hval

/-- **The stiffness matrix is symmetric positive definite** ([quarteroni2000numerical] §12.4.4):
for `β = 0`, `α ≥ α₀ > 0` and `γ ≥ 0` the form is symmetric and coercive on `H^1_0(a, b)`, and
the interior hat functions are linearly independent. -/
theorem stiffnessMatrix_posDef (hab : a < b) (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
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

/-- **The model stiffness matrix** `-u'' = f` on a uniform mesh: `A_fe = h⁻¹ tridiag(-1, 2, -1)`,
which is `h` times the centred finite difference matrix. -/
theorem stiffnessMatrix_model_eq (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) {h : ℝ}
    (hh : 0 < h) (huni : ∀ k < n, x (k + 1) - x k = h) :
    (stiffnessMatrix a b (constLinfty a b 1) (constLinfty a b 0) (constLinfty a b 0)
        fun i : Fin (n - 1) ↦ hatFunction hx hn ((i : ℕ) + 1))
      = h⁻¹ • Matrix.symmTridiagonalToeplitz (n - 1) (-1) 2 := by
  rw [stiffnessMatrix_uniform_eq hx hn hh huni 1 0 0]
  simp [one_div]

/-- **The spectral condition number of the model stiffness matrix**
([quarteroni2000numerical] §12.4.5): `K₂(A_fe) = cot²(π/(2n))`, the scaling `h⁻¹` cancelling
between `A_fe` and its inverse; in terms of the mesh size `h = (b - a)/n` this is the growth
`O(h⁻²)` that the book quotes from [QV94]. -/
theorem condNumber_stiffnessMatrix_model (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) {h : ℝ}
    (hh : 0 < h) (huni : ∀ k < n, x (k + 1) - x k = h) :
    ‖stiffnessMatrix a b (constLinfty a b 1) (constLinfty a b 0) (constLinfty a b 0)
        fun i : Fin (n - 1) ↦ hatFunction hx hn ((i : ℕ) + 1)‖
      * ‖(stiffnessMatrix a b (constLinfty a b 1) (constLinfty a b 0) (constLinfty a b 0)
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

/-- **Every element of `X_h^{1,0}` is the combination of the interior hat functions with its
nodal values.** -/
theorem eq_sum_hatFunction_zero (hab : a < b) (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
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

/-- **The Galerkin equation at an interior node on a uniform mesh** is the centred finite
difference stencil ([quarteroni2000numerical] (12.75)). -/
theorem form_sum_hatFunction_uniform (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) {h : ℝ}
    (hh : 0 < h) (huni : ∀ k < n, x (k + 1) - x k = h) (ε β : ℝ) (u : ℕ → ℝ) {i : ℕ}
    (hi1 : 1 ≤ i) (hi2 : i < n) :
    EllipticInterval.form a b (constLinfty a b ε) (constLinfty a b β) (constLinfty a b 0)
        (∑ j ∈ Finset.range (n + 1), u j • hatFunction hx hn j) (hatFunction hx hn i)
      = ε / h * (-u (i - 1) + 2 * u i - u (i + 1)) + β / 2 * (u (i + 1) - u (i - 1)) := by
  have hne : h ≠ 0 := hh.ne'
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have hlin : EllipticInterval.form a b (constLinfty a b ε) (constLinfty a b β)
        (constLinfty a b 0) (∑ j ∈ Finset.range (n + 1), u j • hatFunction hx hn j)
        (hatFunction hx hn (m + 1))
      = ∑ j ∈ Finset.range (n + 1), u j * EllipticInterval.form a b (constLinfty a b ε)
        (constLinfty a b β) (constLinfty a b 0) (hatFunction hx hn j)
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

/-- **Galerkin `P_1` on a uniform mesh is the centred difference scheme**
([quarteroni2000numerical] (12.75)): for constant `ε` and `β` and `γ = 0`, a piecewise linear
function with nodal values `u_j` is a Galerkin solution of the homogeneous problem on
`X_h^{1,0}` exactly when `(ε/h)(-u_{i-1} + 2u_i - u_{i+1}) + (β/2)(u_{i+1} - u_{i-1}) = 0` at
every interior node. -/
theorem galerkin_iff_centredScheme (hab : a < b) (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
    {h : ℝ} (hh : 0 < h) (huni : ∀ k < n, x (k + 1) - x k = h) (ε β : ℝ) (u : ℕ → ℝ) :
    (∀ v ∈ lagrangeSpaceZero hab n x 1,
        EllipticInterval.form a b (constLinfty a b ε) (constLinfty a b β) (constLinfty a b 0)
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

/-- **The affine map of the reference interval onto a panel**,
[quarteroni2000numerical] (12.62): `x = φ(ξ) = x_j + ξ (x_{j+1} - x_j)`. -/
noncomputable def affineMap (x : ℕ → ℝ) (j : ℕ) : ℝ → ℝ := fun ξ ↦ x j + ξ * (x (j + 1) - x j)

/-- The inverse of `FiniteElement.affineMap`, the reference coordinate
`ξ(x) = (x - x_j)/(x_{j+1} - x_j)` of [quarteroni2000numerical] §12.4.5. -/
noncomputable def refCoord (x : ℕ → ℝ) (j : ℕ) : ℝ → ℝ := fun t ↦ (t - x j) / (x (j + 1) - x j)

/-- **The reference shape functions of `X_h^1`** ([quarteroni2000numerical] §12.4.5):
`φ̂₀(ξ) = 1 - ξ` and `φ̂₁(ξ) = ξ`. -/
noncomputable def referenceHat : Fin 2 → ℝ → ℝ := ![fun ξ ↦ 1 - ξ, fun ξ ↦ ξ]

/-- **The reference shape functions of `X_h^2`**, [quarteroni2000numerical] (12.65):
`φ̂₀(ξ) = (1 - ξ)(1 - 2ξ)`, `φ̂₁(ξ) = 4(1 - ξ)ξ`, `φ̂₂(ξ) = ξ(2ξ - 1)`. -/
noncomputable def referenceQuadratic : Fin 3 → ℝ → ℝ :=
  ![fun ξ ↦ (1 - ξ) * (1 - 2 * ξ), fun ξ ↦ 4 * (1 - ξ) * ξ, fun ξ ↦ ξ * (2 * ξ - 1)]

/-- **The hierarchical basis of `P_2` on the reference interval**,
[quarteroni2000numerical] (12.66): `ψ̂₀(ξ) = 1 - ξ`, `ψ̂₁(ξ) = (1 - ξ)ξ`, `ψ̂₂(ξ) = ξ`, the two
linear shape functions together with the bubble. -/
noncomputable def referenceHierarchical : Fin 3 → ℝ → ℝ :=
  ![fun ξ ↦ 1 - ξ, fun ξ ↦ (1 - ξ) * ξ, fun ξ ↦ ξ]

/-- The affine map of the reference interval, unfolded. -/
@[simp]
theorem affineMap_apply (x : ℕ → ℝ) (j : ℕ) (ξ : ℝ) :
    affineMap x j ξ = x j + ξ * (x (j + 1) - x j) := rfl

/-- The reference coordinate, unfolded. -/
@[simp]
theorem refCoord_apply (x : ℕ → ℝ) (j : ℕ) (t : ℝ) :
    refCoord x j t = (t - x j) / (x (j + 1) - x j) := rfl

/-- The reference coordinate inverts the affine map (12.62). -/
theorem affineMap_refCoord {x : ℕ → ℝ} {j : ℕ} (hj : x j ≠ x (j + 1)) (t : ℝ) :
    affineMap x j (refCoord x j t) = t := by
  have hne : x (j + 1) - x j ≠ 0 := sub_ne_zero.2 (Ne.symm hj)
  simp only [affineMap_apply, refCoord_apply]
  field_simp
  ring

/-- The affine map inverts the reference coordinate (12.62). -/
theorem refCoord_affineMap {x : ℕ → ℝ} {j : ℕ} (hj : x j ≠ x (j + 1)) (ξ : ℝ) :
    refCoord x j (affineMap x j ξ) = ξ := by
  have hne : x (j + 1) - x j ≠ 0 := sub_ne_zero.2 (Ne.symm hj)
  simp only [affineMap_apply, refCoord_apply]
  field_simp
  ring

section Reference

variable {n : ℕ} {x : ℕ → ℝ}

/-- **`φ_k = φ̂₀ ∘ ξ` on the panel `I_k`** ([quarteroni2000numerical] §12.4.5). -/
theorem hatFun_eq_referenceHat_zero (hx : Spline.IsPartition a b n x) {k : ℕ} (hk : k < n)
    {t : ℝ} (h1 : x k ≤ t) (h2 : t ≤ x (k + 1)) :
    hatFun n x k t = referenceHat 0 (refCoord x k t) := by
  have hne : x (k + 1) - x k ≠ 0 := by have := hx.step k hk; linarith
  rw [hatFun_eq_of_left hx hk h1 h2, referenceHat]
  simp only [Matrix.cons_val_zero, refCoord_apply]
  field_simp
  ring

/-- **`φ_{k+1} = φ̂₁ ∘ ξ` on the panel `I_k`** ([quarteroni2000numerical] §12.4.5). -/
theorem hatFun_eq_referenceHat_one (hx : Spline.IsPartition a b n x) {k : ℕ} (hk : k < n)
    {t : ℝ} (h1 : x k ≤ t) (h2 : t ≤ x (k + 1)) :
    hatFun n x (k + 1) t = referenceHat 1 (refCoord x k t) := by
  rw [hatFun_eq_of_right hx hk h1 h2]
  simp [referenceHat]

end Reference

/-- **The hierarchical basis (12.66) is linearly independent**
([quarteroni2000numerical] §12.4.5): `α₀ + ξ(α₁ - α₀ + α₂) - α₁ξ² ≡ 0` forces
`α₀ = α₁ = α₂ = 0`, as the book's check evaluates at `ξ = 0`, `1` and `1/2`. -/
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

/-! ### The piecewise linear interpolation operator into `H^1(a, b)` -/

section Interp

variable {n : ℕ} {x : ℕ → ℝ}

/-- The coercion of a finite sum in `L^p` is almost everywhere the sum of the coercions. -/
theorem coeFn_lp_sum {μ : Measure ℝ} (s : Finset ℕ) (F : ℕ → Lp ℝ 2 μ) :
    ⇑(∑ i ∈ s, F i) =ᵐ[μ] fun t ↦ ∑ i ∈ s, F i t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℝ 2 μ
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ s, F j), ih] with t h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert hi]

/-- **The piecewise linear interpolant** `Π_h^1 u` of [quarteroni2000numerical] §8.3, as an
element of `H^1(a, b)`: the combination of the hat functions with the nodal values of the
continuous representative of `u`. -/
noncomputable def lagrangeInterp (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
    (u : SobolevInterval 1 a b) : SobolevInterval 1 a b :=
  ∑ i ∈ Finset.range (n + 1), SobolevInterval.rep u (x i) • hatFunction hx hn i

/-- The interpolant lies in `X_h^1`. -/
theorem lagrangeInterp_mem_lagrangeSpace (hab : a < b) (hx : Spline.IsPartition a b n x)
    (hn : 1 ≤ n) (u : SobolevInterval 1 a b) :
    lagrangeInterp hx hn u ∈ lagrangeSpace hab n x 1 :=
  Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
    (hatFunction_mem_lagrangeSpace hab hx hn i)

/-- **A combination of the hat functions takes the prescribed values at the nodes**. -/
theorem rep_sum_hatFunction (hab : a < b) (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
    (c : ℕ → ℝ) {j : ℕ} (hj : j ≤ n) :
    SobolevInterval.rep (∑ i ∈ Finset.range (n + 1), c i • hatFunction hx hn i) (x j) = c j := by
  have h : SobolevInterval.rep (∑ i ∈ Finset.range (n + 1), c i • hatFunction hx hn i) (x j)
      = nodalCLM hab _ (node_mem_Icc hx hj)
        (∑ i ∈ Finset.range (n + 1), c i • hatFunction hx hn i) := rfl
  rw [h, map_sum]
  simp only [map_smul, smul_eq_mul, nodalCLM_apply]
  rw [Finset.sum_congr rfl fun i _ ↦ congrArg (c i * ·)
    (rep_hatFunction_node hx hn (i := i) (j := j) hj)]
  simp [Finset.sum_ite_eq' (Finset.range (n + 1)) j, Nat.lt_succ_iff.2 hj]

/-- **The interpolant matches `u` at the nodes**. -/
theorem rep_lagrangeInterp_node (hab : a < b) (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
    (u : SobolevInterval 1 a b) {j : ℕ} (hj : j ≤ n) :
    SobolevInterval.rep (lagrangeInterp hx hn u) (x j) = SobolevInterval.rep u (x j) :=
  rep_sum_hatFunction hab hx hn _ hj

/-- **A combination of the hat functions lies in `X_h^1`**. -/
theorem sum_hatFunction_mem_lagrangeSpace (hab : a < b) (hx : Spline.IsPartition a b n x)
    (hn : 1 ≤ n) (c : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1), c i • hatFunction hx hn i) ∈ lagrangeSpace hab n x 1 :=
  Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
    (hatFunction_mem_lagrangeSpace hab hx hn i)

/-- **The interpolant of an element of `H^1_0(a, b)` lies in `X_h^{1,0}`**: it vanishes at both
endpoints because `u` does. -/
theorem lagrangeInterp_mem_lagrangeSpaceZero (hab : a < b) (hx : Spline.IsPartition a b n x)
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

/-- The piecewise constant difference quotient of a function at the nodes: the derivative of the
piecewise linear interpolant, panel by panel. -/
noncomputable def diffQuotFun (n : ℕ) (x : ℕ → ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t ↦ ∑ i ∈ Finset.range (n + 1), f (x i) * hatDerivFun n x i t

/-- On the panel `k` the difference quotient is `(f(x_{k+1}) - f(x_k))/h_k`. -/
theorem diffQuotFun_eq (hx : Spline.IsPartition a b n x) {k : ℕ} (hk : k < n) (f : ℝ → ℝ)
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

/-- The difference quotient is measurable. -/
theorem measurable_diffQuotFun (n : ℕ) (x : ℕ → ℝ) (f : ℝ → ℝ) :
    Measurable (diffQuotFun n x f) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_const.mul (measurable_hatDerivFun n x i)

/-- The weak derivative of the interpolant is the difference quotient of the representative. -/
theorem coeFn_deriv_lagrangeInterp (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n)
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
  have hcoe := coeFn_lp_sum (Finset.range (n + 1))
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

/-- **The interpolation estimate (8.27) in the `H^1` seminorm**
([quarteroni2000numerical] (8.27), Theorem 8.3 at `k = 1`, `m = 1`, with the constant `1`): for
`u ∈ H²(a, b)` on a partition of mesh at most `h`,
`|u - Π_h^1 u|_{H¹(a,b)} ≤ h |u|_{H²(a,b)}`. This is chapter 8's
`integral_sq_deriv_sub_piecewiseLinearInterpCLM_le` read through the weak derivative of
`FiniteElement.lagrangeInterp`, which is the panelwise difference quotient. -/
theorem seminorm_sub_lagrangeInterp_le (hab : a < b) (hx : Spline.IsPartition a b n x)
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
  have key := integral_sq_deriv_sub_piecewiseLinearInterpCLM_le hstep hfirst hlast hmesh' hf
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
    refine integral_congr_Ioo hlt.le fun t ht ↦ ?_
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


/-- **The approximation property of `X_h^{1,0}`** that the Aubin–Nitsche estimate consumes: every
`Φ ∈ H²(a, b)` whose inclusion lies in `H^1_0(a, b)` is approximated in the `H^1` seminorm to
within `h ‖Φ‖_{H²}` by an element of `X_h^{1,0}`, namely its piecewise linear interpolant. -/
theorem exists_mem_lagrangeSpaceZero_seminorm_sub_le (hab : a < b)
    (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) {h : ℝ} (hmesh : ∀ k < n, x (k + 1) - x k ≤ h)
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

end FiniteElement
