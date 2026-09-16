import Numlib.Approximation.SobolevInterpolation
import Numlib.Approximation.Spline
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section01

/-!
# Quarteroni–Sacco–Saleri §8.3: piecewise Lagrange interpolation

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §8.3: the partition `𝒯_h` of `[a, b]` into `K` subintervals
`I_j = [x_j, x_{j+1}]`, the `k + 1` equally spaced nodes of every subinterval, the piecewise
polynomial space `X_h^k` of (8.22), the piecewise interpolation polynomial `Π_h^k f`, the uniform
error estimate (8.23), and the `L²` estimates of Theorem 8.3 with their `k = 1` case (8.27).
Example 8.5 is a table of computed errors and is skipped; (8.24)–(8.25) define `L²(a, b)` and
its norm, which are Mathlib's `Lp ℝ 2 (volume.restrict (Ioo a b))` and its norm.

The piecewise interpolation operator is `piecewisePolyInterpCLM` of
`Numlib/Approximation/Interpolation`, whose panel node systems `IsPanelNodes` are instantiated
here with the equally spaced nodes; the space `X_h^k` is the spline space of smoothness `C⁰`,
`Spline.splineSpace a b K x k 0` of `Numlib/Approximation/Spline`; the `L²` estimates are
`Numlib/Approximation/SobolevInterpolation`, over the Sobolev space `H^{k+1}(a, b)` of
`Numlib/Analysis/Sobolev/Interval`.

## Main definitions

* `equispacedPanelNodes x k` — the nodes `x_j^{(i)} = x_j + (i/k)(x_{j+1} - x_j)`, `0 ≤ i ≤ k`, of
  the subinterval `I_j`, with `isPanelNodes_equispacedPanelNodes`.
* `piecewiseLagrangeInterp x K k` — the operator `Π_h^k` on `C([a, b], ℝ)`, with
  `piecewiseLagrangeInterp_apply_of_mem`: on `I_j` it is the Lagrange interpolant at the nodes of
  `I_j`.
* `equation_8_22` — the space `X_h^k`, with `mem_equation_8_22_iff` in the book's phrasing and
  `range_piecewiseLagrangeInterp`: `X_h^k` is the range of `Π_h^k`.

## Main results

* `equation_8_23`, `equation_8_23_of_forall_le` — `‖f - Π_h^k f‖_∞ ≤ C h^{k+1} ‖f^{(k+1)}‖_∞` with
  `C = 1/(k+1)!`.
* `theorem_8_3`, `theorem_8_3_sq`, `theorem_8_3_L2` — `‖(f - Π_h^k f)^{(m)}‖_{L²(a,b)}
  ≤ C h^{k+1-m} ‖f^{(k+1)}‖_{L²(a,b)}` for `f ∈ H^{k+1}(a, b)` and `0 ≤ m ≤ k + 1`, with `C = 1`.
* `equation_8_27`, `equation_8_27_deriv` — the case `k = 1`, `m = 0, 1`, with `C₁ = C₂ = 1`.

## Conventions

The breakpoints are a sequence `x : ℕ → Icc a b` of points of `[a, b]` with
`Spline.IsPartition a b K (fun j => (x j : ℝ))`: `a = x 0 < x 1 < ⋯ < x K = b`, `K ≥ 1`
subintervals; the book's `n` (the local degree) is written `k ≥ 1` throughout, as the book does
from (8.22) on. The mesh `h = max_j h_j` enters as a bound `h_j ≤ h` for every `j`, which is what
the estimates use. A function `f ∈ C^{k+1}([a, b])` is a function `ℝ → ℝ` of class `C^{k+1}` on an
open set containing `[a, b]`, as in Theorem 8.2, and `‖g‖_∞` is `sSup ((fun s => |g s|) '' Icc a b)`
with an `_of_forall_le` companion carrying a bound `M`. In Theorem 8.3 the hypothesis
"`f^{(m)} ∈ L²(a, b)` for `0 ≤ m ≤ k + 1`" is `u ∈ H^{k+1}(a, b)` (`SobolevInterval (k + 1) a b`),
`f^{(m)}` is its `m`-th weak derivative `SobolevInterval.deriv u m`, its continuous representative
`F : C([a, b], ℝ)` is what `Π_h^k` is applied to, and `(Π_h^k f)^{(m)}` is the classical `m`-th
derivative of `Π_h^k F` (extended by its endpoint values), which for `m ≥ 2` exists only inside
the subintervals; `‖·‖_{L²(a,b)}` of such a broken function is the square root of the sum over the
subintervals of the integrals of its square, and `‖f^{(k+1)}‖_{L²(a,b)}` is the seminorm
`SobolevInterval.seminorm (k + 1) a b u`.
-/

open MeasureTheory Polynomial Set
open scoped Interval Topology

namespace QuarteroniSaccoSaleri.Chapter08

variable {a b : ℝ} {K k : ℕ} {x : ℕ → Icc a b}

/-! ### The equally spaced nodes and the piecewise interpolation operator -/

/-- **The equally spaced nodes of a subinterval** (§8.3): on `I_j = [x_j, x_{j+1}]` the `k + 1`
nodes `x_j^{(i)} = x_j + (i/k)(x_{j+1} - x_j)`, `0 ≤ i ≤ k`, as points of `[a, b]`. -/
noncomputable def equispacedPanelNodes (x : ℕ → Icc a b) (k : ℕ) (j : ℕ) (i : Fin (k + 1)) :
    Icc a b :=
  ⟨(x j : ℝ) + ((i : ℕ) : ℝ) / k * ((x (j + 1) : ℝ) - x j), by
    have hi : ((i : ℕ) : ℝ) / k ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, div_le_one_of_le₀ (by exact_mod_cast Nat.lt_succ_iff.mp i.2) (by positivity)⟩
    simpa only [smul_eq_mul] using (convex_Icc a b).add_smul_sub_mem (x j).2 (x (j + 1)).2 hi⟩

/-- The value of an equally spaced node. -/
@[simp]
theorem equispacedPanelNodes_val (x : ℕ → Icc a b) (k j : ℕ) (i : Fin (k + 1)) :
    (equispacedPanelNodes x k j i : ℝ) = (x j : ℝ) + ((i : ℕ) : ℝ) / k * ((x (j + 1) : ℝ) - x j) :=
  rfl

/-- **The equally spaced nodes form a panel node system**: for a partition
`a = x 0 < ⋯ < x K = b` with `K ≥ 1` and a degree `k ≥ 1`, the nodes of every subinterval lie in
it, are distinct, and start and end at its endpoints — `IsPanelNodes (K - 1) k x node` of
`Numlib/Approximation/Interpolation`, whose panels are numbered `0, …, K - 1`. -/
theorem isPanelNodes_equispacedPanelNodes (hx : Spline.IsPartition a b K fun j => (x j : ℝ))
    (hK : 1 ≤ K) (hk : 1 ≤ k) : IsPanelNodes (K - 1) k x (equispacedPanelNodes x k) where
  step i hi := hx.step i (by omega)
  first := hx.first
  last := by rw [Nat.sub_add_cancel hK]; exact hx.last
  mem j hj i := by
    have hd : 0 ≤ (x (j + 1) : ℝ) - x j := sub_nonneg.mpr (hx.step j (by omega)).le
    have hθ : ((i : ℕ) : ℝ) / k ≤ 1 :=
      div_le_one_of_le₀ (by exact_mod_cast Nat.lt_succ_iff.mp i.2) (by positivity)
    refine ⟨le_add_of_nonneg_right (mul_nonneg (by positivity) hd), ?_⟩
    rw [equispacedPanelNodes_val]
    nlinarith [mul_le_of_le_one_left hd hθ]
  injective j hj i i' hii' := by
    have hd : (x (j + 1) : ℝ) - x j ≠ 0 := sub_ne_zero.mpr (hx.step j (by omega)).ne'
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    simp only [equispacedPanelNodes_val, add_right_inj, mul_eq_mul_right_iff, hd, or_false,
      div_left_inj' hk', Nat.cast_inj] at hii'
    exact Fin.ext hii'
  node_zero j hj := Subtype.ext (by simp)
  node_last j hj := Subtype.ext (by
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    simp [div_self hk'])

/-- **The piecewise interpolation polynomial `Π_h^k`** (§8.3): the operator on `C([a, b], ℝ)`
sending `f` to the continuous function which on every subinterval `I_j` of the partition
`a = x 0 < ⋯ < x K = b` is the Lagrange interpolant of `f` at the `k + 1` equally spaced nodes of
`I_j` — `piecewisePolyInterpCLM` of `Numlib/Approximation/Interpolation` with the node system
`equispacedPanelNodes x k`. -/
noncomputable def piecewiseLagrangeInterp (x : ℕ → Icc a b) (K k : ℕ) :
    C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ) :=
  piecewisePolyInterpCLM (K - 1) k x (equispacedPanelNodes x k)

/-- **`Π_h^k f` on a subinterval** (§8.3): "the piecewise interpolation polynomial `Π_h^k f`
coincides on each `I_j` with the interpolating polynomial of `f|_{I_j}` at the `k + 1` nodes
`x_j^{(i)}`" — `piecewisePolyInterpCLM_apply_of_mem`. -/
theorem piecewiseLagrangeInterp_apply_of_mem (hx : Spline.IsPartition a b K fun j => (x j : ℝ))
    (hK : 1 ≤ K) (hk : 1 ≤ k) (f : C(Icc a b, ℝ)) {j : ℕ} (hj : j < K) {t : Icc a b}
    (h1 : (x j : ℝ) ≤ t) (h2 : (t : ℝ) ≤ x (j + 1)) :
    piecewiseLagrangeInterp x K k f t
      = (Lagrange.interpolate Finset.univ (fun i => (equispacedPanelNodes x k j i : ℝ))
          fun i => f (equispacedPanelNodes x k j i)).eval (t : ℝ) :=
  piecewisePolyInterpCLM_apply_of_mem (isPanelNodes_equispacedPanelNodes hx hK hk) f
    (by omega) h1 h2

/-! ### (8.22): the space `X_h^k` -/

/-- **(8.22), the piecewise polynomial space**
`X_h^k = {v ∈ C⁰([a, b]) : v|_{I_j} ∈ 𝒫_k(I_j) ∀ I_j ∈ 𝒯_h}`: the continuous functions on
`[a, b]` whose restrictions to the subintervals `I_j = [x_j, x_{j+1}]`, `j < K`, are polynomials
of degree `≤ k` — the spline space of degree `k` and smoothness `C⁰` of
`Numlib/Approximation/Spline`, `Spline.splineSpace a b K x k 0`; `mem_equation_8_22_iff` is the
book's phrasing. -/
noncomputable def equation_8_22 (a b : ℝ) (K : ℕ) (x : ℕ → Icc a b) (k : ℕ) :
    Submodule ℝ C(Icc a b, ℝ) :=
  Spline.splineSpace a b K (fun j => (x j : ℝ)) k 0

/-- **(8.22) unfolded**: a continuous function `v` on `[a, b]` lies in `X_h^k` exactly when on
every subinterval `I_j`, `j < K`, it agrees with a polynomial of degree at most `k`. -/
theorem mem_equation_8_22_iff (v : C(Icc a b, ℝ)) :
    v ∈ equation_8_22 a b K x k ↔
      ∀ j < K, ∃ p : ℝ[X], p.degree ≤ k ∧
        ∀ t : Icc a b, (t : ℝ) ∈ Icc (x j : ℝ) (x (j + 1) : ℝ) → v t = p.eval (t : ℝ) := by
  have hab : a ≤ b := (x 0).2.1.trans (x 0).2.2
  constructor
  · rintro ⟨g, -, hv, hp⟩ j hj
    obtain ⟨p, hpd, hpe⟩ := hp j hj
    exact ⟨p, hpd, fun t ht => (hv t).trans (hpe ht)⟩
  · intro hv
    refine ⟨IccExtend hab v, contDiffOn_zero.mpr v.continuous.Icc_extend'.continuousOn,
      fun t => (IccExtend_val hab v t).symm, fun j hj => ?_⟩
    obtain ⟨p, hpd, hpe⟩ := hv j hj
    refine ⟨p, hpd, fun t ht => ?_⟩
    have ht' : t ∈ Icc a b := ⟨(x j).2.1.trans ht.1, ht.2.trans (x (j + 1)).2.2⟩
    rw [IccExtend_of_mem hab v ht', hpe ⟨t, ht'⟩ ht]

/-- **`X_h^k` is the range of `Π_h^k`** (§8.3): for a partition with `K ≥ 1` subintervals and
`k ≥ 1`, the piecewise interpolation polynomials are exactly the elements of `X_h^k`. `Π_h^k f` is
a polynomial of degree `≤ k` on every subinterval (`piecewiseLagrangeInterp_apply_of_mem`), and an
element of `X_h^k` is its own Lagrange interpolant on every subinterval
(`Lagrange.eq_interpolate_of_eval_eq`), hence is reproduced by `Π_h^k`. -/
theorem range_piecewiseLagrangeInterp (hx : Spline.IsPartition a b K fun j => (x j : ℝ))
    (hK : 1 ≤ K) (hk : 1 ≤ k) :
    LinearMap.range (piecewiseLagrangeInterp x K k : C(Icc a b, ℝ) →ₗ[ℝ] C(Icc a b, ℝ))
      = equation_8_22 a b K x k := by
  have hnode := isPanelNodes_equispacedPanelNodes hx hK hk
  have hcard : (Finset.univ : Finset (Fin (k + 1))).card = k + 1 := by simp
  apply le_antisymm
  · rintro g ⟨f, rfl⟩
    refine (mem_equation_8_22_iff _).mpr fun j hj => ⟨panelPoly (equispacedPanelNodes x k) j f,
      ?_, fun t ht => ?_⟩
    · have := Lagrange.degree_interpolate_le (s := Finset.univ)
        (fun i => f (equispacedPanelNodes x k j i)) (hnode.injective j (by omega)).injOn
      rwa [hcard, Nat.add_sub_cancel] at this
    · exact piecewisePolyInterpCLM_apply_of_mem hnode f (by omega) ht.1 ht.2
  · intro v hv
    refine ⟨v, ContinuousMap.ext fun t => ?_⟩
    obtain ⟨j, hj, h1, h2⟩ := exists_mem_subinterval hnode.first hnode.last t
    obtain ⟨p, hpd, hpe⟩ := (mem_equation_8_22_iff v).mp hv j (by omega)
    have hp : p = panelPoly (equispacedPanelNodes x k) j v := by
      refine Lagrange.eq_interpolate_of_eval_eq _ (hnode.injective j hj).injOn ?_ fun i _ => ?_
      · rw [hcard]
        exact hpd.trans_lt (by exact_mod_cast Nat.lt_succ_self k)
      · exact (hpe _ (hnode.mem j hj i)).symm
    change piecewisePolyInterpCLM (K - 1) k x (equispacedPanelNodes x k) v t = v t
    rw [piecewisePolyInterpCLM_apply_of_mem hnode v hj h1 h2, ← hp, hpe t ⟨h1, h2⟩]

/-! ### (8.23): the uniform error estimate -/

/-- **(8.23), with an explicit bound on `f^{(k+1)}`.** For a partition with `K ≥ 1` subintervals
of length at most `h`, `k ≥ 1`, and `f` of class `C^{k+1}` on an open set `U ⊇ [a, b]` with
`|f^{(k+1)}| ≤ M` on `[a, b]`, the piecewise interpolant of the restriction `F` of `f` satisfies

`‖F - Π_h^k F‖_∞ ≤ h^{k+1}/(k+1)! · M`.

Theorem 8.2 on each subinterval (`exists_sub_piecewisePolyInterpCLM_apply_eq_of_contDiffOn`),
the nodal polynomial of a subinterval being bounded by `h^{k+1}` there. -/
theorem equation_8_23_of_forall_le (hx : Spline.IsPartition a b K fun j => (x j : ℝ))
    (hK : 1 ≤ K) (hk : 1 ≤ k) {h : ℝ} (hmesh : ∀ j < K, (x (j + 1) : ℝ) - x j ≤ h) {f : ℝ → ℝ}
    {U : Set ℝ} (hU : IsOpen U) (hUsub : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f U) {F : C(Icc a b, ℝ)}
    (hF : ∀ t, F t = f t) {M : ℝ} (hM : ∀ s ∈ Icc a b, |iteratedDeriv (k + 1) f s| ≤ M) :
    ‖F - piecewiseLagrangeInterp x K k F‖ ≤ h ^ (k + 1) / (k + 1).factorial * M := by
  have hab := hx.lt_of_pos hK
  have hnode := isPanelNodes_equispacedPanelNodes hx hK hk
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM a ⟨le_rfl, hab.le⟩)
  have hh0 : 0 ≤ h := (sub_pos.mpr (hx.step 0 hK)).le.trans (hmesh 0 hK)
  have hfact : (0 : ℝ) < (k + 1).factorial := by exact_mod_cast Nat.factorial_pos (k + 1)
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  obtain ⟨j, hj, h1, h2⟩ := exists_mem_subinterval hnode.first hnode.last t
  have hsub : Icc (x j : ℝ) (x (j + 1) : ℝ) ⊆ U :=
    (Icc_subset_Icc (x j).2.1 (x (j + 1)).2.2).trans hUsub
  obtain ⟨ξ, hξ, hξeq⟩ := exists_sub_piecewisePolyInterpCLM_apply_eq_of_contDiffOn hnode hU hj
    hsub hf hF h1 h2
  have hξmem : ξ ∈ Icc a b := ⟨(x j).2.1.trans hξ.1.le, hξ.2.le.trans (x (j + 1)).2.2⟩
  have hprod : |∏ i, ((t : ℝ) - (equispacedPanelNodes x k j i : ℝ))| ≤ h ^ (k + 1) := by
    rw [Finset.abs_prod]
    calc ∏ i, |(t : ℝ) - (equispacedPanelNodes x k j i : ℝ)| ≤ ∏ _i : Fin (k + 1), h := by
          refine Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => ?_
          rw [← Real.dist_eq]
          exact (Real.dist_le_of_mem_Icc ⟨h1, h2⟩ (hnode.mem j hj i)).trans (hmesh j (by omega))
      _ = h ^ (k + 1) := by simp
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs, piecewiseLagrangeInterp, hξeq, abs_mul, abs_div,
    abs_of_pos hfact]
  calc |iteratedDeriv (k + 1) f ξ| / ((k + 1).factorial : ℝ)
        * |∏ i, ((t : ℝ) - (equispacedPanelNodes x k j i : ℝ))|
      ≤ M / ((k + 1).factorial : ℝ) * h ^ (k + 1) :=
        mul_le_mul (by gcongr; exact hM ξ hξmem) hprod (abs_nonneg _) (by positivity)
    _ = h ^ (k + 1) / (k + 1).factorial * M := by ring

/-- **(8.23).** For a partition with `K ≥ 1` subintervals of length at most `h`, `k ≥ 1`, and
`f ∈ C^{k+1}([a, b])` (of class `C^{k+1}` on an open set `U ⊇ [a, b]`), the piecewise interpolant
of the restriction `F` of `f` satisfies

`‖F - Π_h^k F‖_∞ ≤ C h^{k+1} ‖f^{(k+1)}‖_∞` with `C = 1/(k+1)!`,

where `‖f^{(k+1)}‖_∞ = max_{[a,b]} |f^{(k+1)}|`. -/
theorem equation_8_23 (hx : Spline.IsPartition a b K fun j => (x j : ℝ)) (hK : 1 ≤ K) (hk : 1 ≤ k)
    {h : ℝ} (hmesh : ∀ j < K, (x (j + 1) : ℝ) - x j ≤ h) {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hUsub : Icc a b ⊆ U) (hf : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f U) {F : C(Icc a b, ℝ)}
    (hF : ∀ t, F t = f t) :
    ‖F - piecewiseLagrangeInterp x K k F‖
      ≤ 1 / (k + 1).factorial * h ^ (k + 1)
        * sSup ((fun s => |iteratedDeriv (k + 1) f s|) '' Icc a b) := by
  have hcont : ContinuousOn (iteratedDeriv (k + 1) f) (Icc a b) :=
    ((hf.continuousOn_iteratedDerivWithin le_rfl hU.uniqueDiffOn).congr
      (iteratedDerivWithin_of_isOpen hU).symm).mono hUsub
  have hbdd : BddAbove ((fun s => |iteratedDeriv (k + 1) f s|) '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hcont.abs).bddAbove
  rw [show 1 / ((k + 1).factorial : ℝ) * h ^ (k + 1) = h ^ (k + 1) / (k + 1).factorial by ring]
  exact equation_8_23_of_forall_le hx hK hk hmesh hU hUsub hf hF
    fun s hs => le_csSup hbdd (mem_image_of_mem _ hs)

/-! ### Theorem 8.3: the `L²` estimates -/

/-- Inside a subinterval `I_j`, the `m`-th derivative of `Π_h^k F` (extended to `ℝ` by its
endpoint values) is the `m`-th derivative of the Lagrange interpolant of `F` on `I_j`. -/
theorem iteratedDeriv_IccExtend_piecewiseLagrangeInterp
    (hx : Spline.IsPartition a b K fun j => (x j : ℝ)) (hK : 1 ≤ K) (hk : 1 ≤ k)
    (F : C(Icc a b, ℝ)) (m : ℕ) {j : ℕ} (hj : j < K) {t : ℝ}
    (ht : t ∈ Ioo (x j : ℝ) (x (j + 1) : ℝ)) :
    iteratedDeriv m (IccExtend hx.le (piecewiseLagrangeInterp x K k F)) t
      = (derivative^[m] (panelPoly (equispacedPanelNodes x k) j F)).eval t := by
  have hnode := isPanelNodes_equispacedPanelNodes hx hK hk
  have hev : IccExtend hx.le (piecewiseLagrangeInterp x K k F)
      =ᶠ[𝓝 t] fun s => (panelPoly (equispacedPanelNodes x k) j F).eval s := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    have hs' : s ∈ Icc a b := ⟨(x j).2.1.trans hs.1, hs.2.trans (x (j + 1)).2.2⟩
    rw [IccExtend_of_mem hx.le _ hs']
    exact piecewisePolyInterpCLM_apply_of_mem hnode F (by omega) hs.1 hs.2
  rw [hev.iteratedDeriv_eq m, Polynomial.iteratedDeriv_eval]

/-- **Theorem 8.3, squared** ((8.26) with `C = 1`): for a partition with `K ≥ 1` subintervals of
length at most `h`, `k ≥ 1`, `f ∈ H^{k+1}(a, b)` with continuous representative `F` and
`0 ≤ m ≤ k + 1`,

`‖(f - Π_h^k f)^{(m)}‖²_{L²(a,b)} = ∑_{j<K} ∫_{x_j}^{x_{j+1}} |f^{(m)} - (Π_h^k F)^{(m)}|²
≤ h^{2(k+1-m)} ‖f^{(k+1)}‖²_{L²(a,b)}`,

with `f^{(m)}` the `m`-th weak derivative of `f` and `(Π_h^k F)^{(m)}` the classical `m`-th
derivative of the piecewise interpolant inside the subintervals. For `m ≤ k` this is
`sobolevSeminorm_sub_piecewisePolyInterp_le` of `Numlib/Approximation/SobolevInterpolation`, the
weak derivative agreeing almost everywhere with the derivative of the `C^k` representative
(`SobolevInterval.exists_contDiff_ae_eq`); for `m = k + 1` the derivative of the interpolant
vanishes and the two sides are equal. -/
theorem theorem_8_3_sq (hx : Spline.IsPartition a b K fun j => (x j : ℝ)) (hK : 1 ≤ K)
    (hk : 1 ≤ k) {h : ℝ} (hmesh : ∀ j < K, (x (j + 1) : ℝ) - x j ≤ h)
    (u : SobolevInterval (k + 1) a b) {F : C(Icc a b, ℝ)}
    (hF : SobolevInterval.fn u =ᵐ[volume.restrict (Ioo a b)] IccExtend hx.le F) {m : ℕ}
    (hm : m ≤ k + 1) :
    ∑ j ∈ Finset.range K, ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
        (SobolevInterval.deriv u ⟨m, Nat.lt_succ_of_le hm⟩ t
          - iteratedDeriv m (IccExtend hx.le (piecewiseLagrangeInterp x K k F)) t) ^ 2
      ≤ h ^ (2 * (k + 1 - m)) * SobolevInterval.seminorm (k + 1) a b u ^ 2 := by
  have hab := hx.lt_of_pos hK
  have hnode := isPanelNodes_equispacedPanelNodes hx hK hk
  have hmesh' : ∀ j ≤ K - 1, (x (j + 1) : ℝ) - x j ≤ h := fun j hj => hmesh j (by omega)
  have hsub' : ∀ j, [[(x j : ℝ), (x (j + 1) : ℝ)]] ⊆ [[a, b]] := fun j => by
    rw [uIcc_of_le hab.le]; exact uIcc_subset_Icc (x j).2 (x (j + 1)).2
  -- a panel integral only sees the open panel, almost everywhere
  have hpanel_congr : ∀ j < K, ∀ {φ ψ : ℝ → ℝ},
      (∀ᵐ t, t ∈ Ioo (x j : ℝ) (x (j + 1) : ℝ) → φ t = ψ t) →
      ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), φ t = ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), ψ t := by
    intro j hj φ ψ hae
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ t : ℝ, t ≠ (x (j + 1) : ℝ) := by simp [ae_iff, measure_singleton]
    filter_upwards [hae, hne] with t ht htne htI
    rw [uIoc_of_le (hx.step j hj).le] at htI
    exact ht ⟨htI.1, lt_of_le_of_ne htI.2 htne⟩
  have hIoo : ∀ j < K, Ioo (x j : ℝ) (x (j + 1) : ℝ) ⊆ Ioo a b := fun j _ =>
    Ioo_subset_Ioo (x j).2.1 (x (j + 1)).2.2
  have hrange : ∀ j ∈ Finset.range K, j < K := fun j hj => Finset.mem_range.mp hj
  rcases eq_or_lt_of_le hm with rfl | hmk
  · -- `m = k + 1`: the derivative of the interpolant vanishes, and the two sides agree
    have hzero : ∀ j < K, ∀ t ∈ Ioo (x j : ℝ) (x (j + 1) : ℝ),
        iteratedDeriv (k + 1) (IccExtend hx.le (piecewiseLagrangeInterp x K k F)) t = 0 := by
      intro j hj t ht
      rw [iteratedDeriv_IccExtend_piecewiseLagrangeInterp hx hK hk F (k + 1) hj ht,
        Polynomial.iterate_derivative_eq_zero, eval_zero]
      have := Lagrange.degree_interpolate_le (s := Finset.univ)
        (fun i => F (equispacedPanelNodes x k j i)) (hnode.injective j (by omega)).injOn
      rw [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel] at this
      exact Nat.lt_succ_of_le (natDegree_le_of_degree_le this)
    have hint : ∀ j < K, IntervalIntegrable
        (fun t => SobolevInterval.deriv u (Fin.last (k + 1)) t ^ 2) volume (x j) (x (j + 1)) :=
      fun j _ => (SobolevInterval.intervalIntegrable_deriv_sq hab.le u _).mono_set (hsub' j)
    refine le_of_eq ?_
    calc ∑ j ∈ Finset.range K, ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
          (SobolevInterval.deriv u ⟨k + 1, Nat.lt_succ_of_le le_rfl⟩ t
            - iteratedDeriv (k + 1) (IccExtend hx.le (piecewiseLagrangeInterp x K k F)) t) ^ 2
        = ∑ j ∈ Finset.range K, ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
            SobolevInterval.deriv u (Fin.last (k + 1)) t ^ 2 :=
          Finset.sum_congr rfl fun j hj => hpanel_congr j (hrange j hj)
            (Filter.Eventually.of_forall fun t ht => by
              rw [hzero j (hrange j hj) t ht, sub_zero]; rfl)
      _ = ∫ t in a..b, SobolevInterval.deriv u (Fin.last (k + 1)) t ^ 2 := by
          rw [intervalIntegral.sum_integral_adjacent_intervals (a := fun j => (x j : ℝ))
            fun j hj => hint j hj]
          simp only [hx.first, hx.last]
      _ = h ^ (2 * (k + 1 - (k + 1))) * SobolevInterval.seminorm (k + 1) a b u ^ 2 := by
          rw [SobolevInterval.seminorm_sq_eq_integral hab.le, Nat.sub_self, mul_zero, pow_zero,
            one_mul]
  · -- `m ≤ k`: the backbone estimate, after replacing the weak derivative by the derivative of
    -- the `C^k` representative
    have hmk' : m ≤ k := Nat.lt_succ_iff.mp hmk
    obtain ⟨f, hf, hae, hftc⟩ := SobolevInterval.exists_contDiff_ae_eq hab u
    have hf0 : SobolevInterval.fn u =ᵐ[volume.restrict (Ioo a b)] f := by
      rw [← SobolevInterval.deriv_zero u]; simpa using hae 0
    have hFf : EqOn (IccExtend hab.le F) f (Icc a b) :=
      eqOn_Icc_of_ae_eq hab F.continuous.Icc_extend'.continuousOn hf.continuous.continuousOn
        (hF.symm.trans hf0)
    have hF' : ∀ t, F t = f t := fun t => by rw [← IccExtend_val hab.le F t, hFf t.2]
    have haem : ∀ᵐ t, t ∈ Ioo a b →
        SobolevInterval.deriv u ⟨m, Nat.lt_succ_of_le hm⟩ t = iteratedDeriv m f t := by
      have := (ae_restrict_iff' measurableSet_Ioo).1 (hae ⟨m, Nat.lt_succ_of_le hmk'⟩)
      simpa only [Fin.castSucc_mk] using this
    calc ∑ j ∈ Finset.range K, ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
          (SobolevInterval.deriv u ⟨m, Nat.lt_succ_of_le hm⟩ t
            - iteratedDeriv m (IccExtend hx.le (piecewiseLagrangeInterp x K k F)) t) ^ 2
        = ∑ j ∈ Finset.range (K - 1 + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
            (iteratedDeriv m f t
              - (derivative^[m] (panelPoly (equispacedPanelNodes x k) j F)).eval t) ^ 2 := by
          rw [Nat.sub_add_cancel hK]
          refine Finset.sum_congr rfl fun j hj => hpanel_congr j (hrange j hj) ?_
          filter_upwards [haem] with t ht htI
          rw [ht (hIoo j (hrange j hj) htI),
            iteratedDeriv_IccExtend_piecewiseLagrangeInterp hx hK hk F m (hrange j hj) htI]
      _ ≤ h ^ (2 * (k + 1 - m)) * ∫ t in a..b, SobolevInterval.deriv u (Fin.last (k + 1)) t ^ 2 :=
          sum_integral_sq_sub_panelPoly_le hnode hmesh' hf
            (SobolevInterval.intervalIntegrable_deriv hab.le u _)
            (SobolevInterval.intervalIntegrable_deriv_sq hab.le u _) hftc hF' hmk'
      _ = h ^ (2 * (k + 1 - m)) * SobolevInterval.seminorm (k + 1) a b u ^ 2 := by
          rw [SobolevInterval.seminorm_sq_eq_integral hab.le]

/-- The mesh bound `h` of a partition with at least one subinterval is nonnegative. -/
theorem mesh_nonneg (hx : Spline.IsPartition a b K fun j => (x j : ℝ)) (hK : 1 ≤ K) {h : ℝ}
    (hmesh : ∀ j < K, (x (j + 1) : ℝ) - x j ≤ h) : 0 ≤ h :=
  (sub_pos.mpr (hx.step 0 hK)).le.trans (hmesh 0 hK)

/-- **Theorem 8.3** ((8.26), with `C = 1`). Let `0 ≤ m ≤ k + 1`, with `k ≥ 1`, and assume that
`f^{(m)} ∈ L²(a, b)` for `0 ≤ m ≤ k + 1`, i.e. `f ∈ H^{k+1}(a, b)`, with continuous representative
`F`; then for a partition with `K ≥ 1` subintervals of length at most `h`,

`‖(f - Π_h^k f)^{(m)}‖_{L²(a,b)} ≤ C h^{k+1-m} ‖f^{(k+1)}‖_{L²(a,b)}` with `C = 1`,

the left side being the square root of `∑_{j<K} ∫_{x_j}^{x_{j+1}} |f^{(m)} - (Π_h^k F)^{(m)}|²`,
with `f^{(m)}` the `m`-th weak derivative of `f` and `(Π_h^k F)^{(m)}` the classical `m`-th
derivative of the piecewise interpolant inside the subintervals (for `m ≤ 1` it is the `L²(a, b)`
norm of `(f - Π_h^k f)^{(m)}` itself), and the right side the `H^{k+1}(a, b)` seminorm of `f`.
The book proves the case `k = 1` and refers to Quarteroni–Valli for the general one; here it is
`theorem_8_3_sq`, the panelwise estimate of `Numlib/Approximation/SobolevInterpolation`. -/
theorem theorem_8_3 (hx : Spline.IsPartition a b K fun j => (x j : ℝ)) (hK : 1 ≤ K) (hk : 1 ≤ k)
    {h : ℝ} (hmesh : ∀ j < K, (x (j + 1) : ℝ) - x j ≤ h) (u : SobolevInterval (k + 1) a b)
    {F : C(Icc a b, ℝ)} (hF : SobolevInterval.fn u =ᵐ[volume.restrict (Ioo a b)] IccExtend hx.le F)
    {m : ℕ} (hm : m ≤ k + 1) :
    √(∑ j ∈ Finset.range K, ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
        (SobolevInterval.deriv u ⟨m, Nat.lt_succ_of_le hm⟩ t
          - iteratedDeriv m (IccExtend hx.le (piecewiseLagrangeInterp x K k F)) t) ^ 2)
      ≤ h ^ (k + 1 - m) * SobolevInterval.seminorm (k + 1) a b u := by
  have hh0 := mesh_nonneg hx hK hmesh
  have hs0 : 0 ≤ SobolevInterval.seminorm (k + 1) a b u := apply_nonneg _ _
  calc √(∑ j ∈ Finset.range K, ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
          (SobolevInterval.deriv u ⟨m, Nat.lt_succ_of_le hm⟩ t
            - iteratedDeriv m (IccExtend hx.le (piecewiseLagrangeInterp x K k F)) t) ^ 2)
      ≤ √((h ^ (k + 1 - m) * SobolevInterval.seminorm (k + 1) a b u) ^ 2) := by
        refine Real.sqrt_le_sqrt ((theorem_8_3_sq hx hK hk hmesh u hF hm).trans_eq ?_)
        rw [mul_pow, ← pow_mul']
    _ = h ^ (k + 1 - m) * SobolevInterval.seminorm (k + 1) a b u :=
        Real.sqrt_sq (by positivity)

/-- **Theorem 8.3 for `m = 0`, as an `L²(a, b)` norm on `[a, b]`**: under the hypotheses of
`theorem_8_3`, `‖f - Π_h^k f‖_{L²(a,b)} ≤ h^{k+1} ‖f^{(k+1)}‖_{L²(a,b)}`, the left side written
as `√(∫_a^b |f - Π_h^k F|²)` with `f` the element of `H^{k+1}(a, b)` itself:
`integral_sq_sub_piecewisePolyInterpCLM_le_seminorm`. -/
theorem theorem_8_3_L2 (hx : Spline.IsPartition a b K fun j => (x j : ℝ)) (hK : 1 ≤ K) (hk : 1 ≤ k)
    {h : ℝ} (hmesh : ∀ j < K, (x (j + 1) : ℝ) - x j ≤ h) (u : SobolevInterval (k + 1) a b)
    {F : C(Icc a b, ℝ)}
    (hF : SobolevInterval.fn u =ᵐ[volume.restrict (Ioo a b)] IccExtend hx.le F) :
    √(∫ t in a..b,
        (SobolevInterval.fn u t - IccExtend hx.le (piecewiseLagrangeInterp x K k F) t) ^ 2)
      ≤ h ^ (k + 1) * SobolevInterval.seminorm (k + 1) a b u := by
  have hab := hx.lt_of_pos hK
  have hnode := isPanelNodes_equispacedPanelNodes hx hK hk
  have hh0 := mesh_nonneg hx hK hmesh
  have hs0 : 0 ≤ SobolevInterval.seminorm (k + 1) a b u := apply_nonneg _ _
  have hmesh' : ∀ j ≤ K - 1, (x (j + 1) : ℝ) - x j ≤ h := fun j hj => hmesh j (by omega)
  have hkey := integral_sq_sub_piecewisePolyInterpCLM_le_seminorm hab u hnode hmesh' hF
  rw [intervalIntegral.integral_congr_ae_Ioo_of_mem (g := fun t =>
      (IccExtend hab.le F t - IccExtend hab.le (piecewisePolyInterpCLM (K - 1) k x
        (equispacedPanelNodes x k) F) t) ^ 2) ?_ (left_mem_Icc.mpr hab.le)
      (right_mem_Icc.mpr hab.le)]
  · calc √(∫ t in a..b, (IccExtend hab.le F t - IccExtend hab.le
          (piecewisePolyInterpCLM (K - 1) k x (equispacedPanelNodes x k) F) t) ^ 2)
        ≤ √((h ^ (k + 1) * SobolevInterval.seminorm (k + 1) a b u) ^ 2) := by
          refine Real.sqrt_le_sqrt (hkey.trans_eq ?_)
          rw [mul_pow, ← pow_mul']
      _ = h ^ (k + 1) * SobolevInterval.seminorm (k + 1) a b u := Real.sqrt_sq (by positivity)
  · filter_upwards [hF] with t ht
    rw [ht]
    rfl

/-! ### (8.27): the case `k = 1` -/

/-- **(8.27), first estimate** (`C₁ = 1`). For `f ∈ H²(a, b)` with continuous representative
`F`, and a partition with `K ≥ 1` subintervals of length at most `h`,

`‖f - Π_h^1 f‖_{L²(a,b)} ≤ C₁ h² ‖f''‖_{L²(a,b)}`:

Theorem 8.3 with `k = 1` and `m = 0`, in the form `theorem_8_3_L2`. -/
theorem equation_8_27 (hx : Spline.IsPartition a b K fun j => (x j : ℝ)) (hK : 1 ≤ K) {h : ℝ}
    (hmesh : ∀ j < K, (x (j + 1) : ℝ) - x j ≤ h) (u : SobolevInterval 2 a b) {F : C(Icc a b, ℝ)}
    (hF : SobolevInterval.fn u =ᵐ[volume.restrict (Ioo a b)] IccExtend hx.le F) :
    √(∫ t in a..b,
        (SobolevInterval.fn u t - IccExtend hx.le (piecewiseLagrangeInterp x K 1 F) t) ^ 2)
      ≤ h ^ 2 * SobolevInterval.seminorm 2 a b u :=
  theorem_8_3_L2 (k := 1) hx hK le_rfl hmesh u hF

/-- **(8.27), second estimate** (`C₂ = 1`). For `f ∈ H²(a, b)` with continuous representative
`F`, and a partition with `K ≥ 1` subintervals of length at most `h`,

`‖(f - Π_h^1 f)'‖_{L²(a,b)} ≤ C₂ h ‖f''‖_{L²(a,b)}`,

the left side being `√(∑_{j<K} ∫_{x_j}^{x_{j+1}} |f' - (Π_h^1 F)'|²)` with `f'` the weak derivative
and `(Π_h^1 F)'` the slope of the interpolant on each subinterval: Theorem 8.3 with `k = 1` and
`m = 1`. -/
theorem equation_8_27_deriv (hx : Spline.IsPartition a b K fun j => (x j : ℝ)) (hK : 1 ≤ K)
    {h : ℝ} (hmesh : ∀ j < K, (x (j + 1) : ℝ) - x j ≤ h) (u : SobolevInterval 2 a b)
    {F : C(Icc a b, ℝ)}
    (hF : SobolevInterval.fn u =ᵐ[volume.restrict (Ioo a b)] IccExtend hx.le F) :
    √(∑ j ∈ Finset.range K, ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
        (SobolevInterval.deriv u 1 t
          - deriv (IccExtend hx.le (piecewiseLagrangeInterp x K 1 F)) t) ^ 2)
      ≤ h * SobolevInterval.seminorm 2 a b u := by
  have := theorem_8_3 (k := 1) hx hK le_rfl hmesh u hF (m := 1) (by norm_num)
  rw [Nat.add_sub_cancel, pow_one] at this
  simp only [iteratedDeriv_one] at this
  exact this

end QuarteroniSaccoSaleri.Chapter08
