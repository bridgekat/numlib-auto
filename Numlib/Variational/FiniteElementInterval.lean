import Numlib.Analysis.Sobolev.Interval
import Numlib.Approximation.Spline

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

## Main results

* `FiniteElement.toContinuousMap_injective` — the embedding `H^1(a, b) ↪ C([a, b], ℝ)` is
  injective.
* `FiniteElement.exists_mem_lagrangeSpace` — every continuous piecewise polynomial is the
  continuous representative of an element of `H^1(a, b)`.
* `FiniteElement.lagrangeSpace_eq_map_splineSpace` — the bridge between the two views.
* `FiniteElement.finrank_lagrangeSpace` — `dim X_h^k = n k + 1`.

## Implementation notes

Two lemmas here are general facts about `H^1(a, b)` with no finite element content and belong in
`Numlib/Analysis/Sobolev/Interval.lean`; they are marked `TODO(backbone)`.
-/

open Set MeasureTheory

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

end FiniteElement
