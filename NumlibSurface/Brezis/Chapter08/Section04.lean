import Numlib.Variational.EllipticInterval.BoundaryConditions
import NumlibSurface.Brezis.Chapter08.Section01
import NumlibSurface.Brezis.Chapter08.Section03

/-!
# Brezis §8.4: some examples of boundary value problems

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §8.4: the Dirichlet problem (14) for `−u'' + u = f` on
`I = (0, 1)` (Proposition 8.15, Remark 22, Steps A, C and D, Remark 23) and Examples 1–8
(inhomogeneous Dirichlet, Proposition 8.16; Sturm–Liouville; homogeneous and inhomogeneous
Neumann, Propositions 8.17–8.18; mixed, Robin and periodic conditions; the problem on `ℝ`), with
Remarks 24–25 recorded in the docstrings where they are not formalized.

## Correspondence

* `H¹(0, 1)` is `SobolevInterval 1 0 1` (`= SobolevIntervalLp 1 2 (Opens.Ioo 0 1)` of §8.2),
  `H_0^1(0, 1)` is `SobolevIntervalZero 0 1` (`= H10 (Opens.Ioo 0 1)` of §8.3), `H²(0, 1)` is
  `SobolevInterval 2 0 1`, `C²(Ī)` is `ContDiffMapIcc zero_le_one 2`; `u(x)` for `u ∈ H¹` is
  the continuous representative `SobolevInterval.rep u x`.
* The bilinear form `a(u, v) = ∫ u' v' + ∫ u v` is `EllipticInterval.modelForm 0 1`, the linear
  functional `v ↦ ∫ f v` is `EllipticInterval.load 0 1 f`, and the general form of Example 2,
  `∫ p u' v' + ∫ r u' v + ∫ q u v`, is `EllipticInterval.form 0 1 p r q` with the coefficients as
  elements of `L^∞(0, 1)`.
* A weak solution of (14) is `IsWeakSolutionDirichlet f u`
  (`IsGalerkinSolution (modelForm 0 1) (load 0 1 f) (SobolevIntervalZero 0 1) u`, unfolded by
  `isWeakSolutionDirichlet_iff` to the book's (15)), a classical solution is
  `IsClassicalSolutionDirichlet f u` (§8.1's `IsClassicalSolution` on `[0, 1]`).
* "`u ∈ H²(I)` satisfies `−u'' + u = f`" is `Φ : SobolevInterval 2 0 1` with
  `Φ'' = Φ − f` a.e., i.e. `(SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ fun x ↦ Φ.fn x − f x`; `Φ'(0)`
  is `SobolevInterval.rep (derivCLM 1 0 1 Φ) 0`.

Everything delegates to `Numlib/Variational/EllipticInterval` and its child
`EllipticInterval/BoundaryConditions` (Steps A–D in general, Examples 1–8).

## Main results

* `dirichlet_stepA`, `proposition_8_15`, `proposition_8_15_dirichletPrinciple`, `remark_8_22`,
  `dirichlet_stepC`, `dirichlet_stepCD`, `remark_8_23` — the program of §8.1 for (14).
* `proposition_8_16` (Example 1, with both methods), `example_8_2` (Sturm–Liouville, with the
  coercivity cases (i)–(ii) and the symmetrization of `example_8_2_general`),
  `proposition_8_17`, `proposition_8_18` (Neumann), `example_8_5`, `example_8_6`, `example_8_7`
  (mixed, Robin, periodic), `example_8_8` (the problem on `ℝ`).

Remark 24 (the problem `−u'' = f` on `ℝ`) and Remark 25 (the half-line) are not formalized in
this file: see the report of the formalization (they are surface-level arguments that the book
leaves to the reader).
-/

open Filter MeasureTheory Set TopologicalSpace EllipticInterval
open scoped Distributions ENNReal InnerProductSpace Topology

noncomputable section

namespace Brezis.Chapter08

/-! ### The definitions -/

/-- **Definition (§8.4), classical solution of (14).** A classical solution of (14) is a
function `u ∈ C²(Ī)` satisfying `−u'' + u = f` on `Ī` and `u(0) = u(1) = 0`: §8.1's
`IsClassicalSolution` on `[0, 1]`. -/
abbrev IsClassicalSolutionDirichlet (f : ℝ → ℝ) (u : ContDiffMapIcc (zero_lt_one' ℝ).le 2) :
    Prop :=
  IsClassicalSolution (zero_lt_one' ℝ) f u

/-- **Definition (§8.4), weak solution of (14).** A weak solution of (14), for `f ∈ L²(0, 1)`,
is a function `u ∈ H_0^1(0, 1)` satisfying (15): `∫ u' v' + ∫ u v = ∫ f v` for all
`v ∈ H_0^1(0, 1)` — the Galerkin problem of the form `a(u, v) = ∫ u' v' + ∫ u v` and the load
`v ↦ ∫ f v` on `H_0^1(0, 1)`. -/
def IsWeakSolutionDirichlet (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (u : SobolevInterval 1 0 1) : Prop :=
  IsGalerkinSolution (modelForm 0 1) (load 0 1 f) (SobolevIntervalZero 0 1) u

/-- The product of two `L²` functions is integrable. -/
private theorem integrable_mul_L2 {μ : Measure ℝ} (f g : Lp ℝ 2 μ) :
    Integrable (fun x ↦ f x * g x) μ :=
  (L2.integrable_inner (𝕜 := ℝ) f g).congr (Eventually.of_forall fun x ↦ by
    simp [RCLike.inner_apply, mul_comm])

/-- The weak formulation (15) unfolded: `u ∈ H_0^1(0, 1)` and
`∫_0^1 u' v' + ∫_0^1 u v = ∫_0^1 f v` for all `v ∈ H_0^1(0, 1)`. -/
theorem isWeakSolutionDirichlet_iff (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (u : SobolevInterval 1 0 1) :
    IsWeakSolutionDirichlet f u ↔ u ∈ SobolevIntervalZero 0 1 ∧ ∀ v ∈ SobolevIntervalZero 0 1,
      (∫ x in Ioo (0 : ℝ) 1, SobolevInterval.deriv u 1 x * SobolevInterval.deriv v 1 x)
        + ∫ x in Ioo (0 : ℝ) 1, SobolevInterval.fn u x * SobolevInterval.fn v x
        = ∫ x in Ioo (0 : ℝ) 1, f x * SobolevInterval.fn v x := by
  refine and_congr_right fun _ ↦ forall₂_congr fun v _ ↦ ?_
  rw [modelForm_apply, SobolevInterval.inner_eq_intervalIntegral zero_le_one,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, load_apply]
  have e : ∫ x in Ioo (0 : ℝ) 1, (SobolevInterval.deriv u 1 x * SobolevInterval.deriv v 1 x
      + SobolevInterval.fn u x * SobolevInterval.fn v x)
      = (∫ x in Ioo (0 : ℝ) 1, SobolevInterval.deriv u 1 x * SobolevInterval.deriv v 1 x)
        + ∫ x in Ioo (0 : ℝ) 1, SobolevInterval.fn u x * SobolevInterval.fn v x :=
    integral_add (integrable_mul_L2 _ _) (integrable_mul_L2 (SobolevInterval.deriv u 0) _)
  rw [e]
  rfl

/-! ### Steps A and B -/

/-- **Step A.** Every classical solution of (14), with `f` continuous, is a weak solution: for
`f ∈ C(Ī)` with `L²` class `fL`, the element `EllipticInterval.ofContDiffMapIcc zero_lt_one u`
of `H¹(0, 1)` carried by a classical solution `u` is a weak solution of (14) — "obvious by
integration by parts (as justified in Corollary 8.10)", the backbone's
`EllipticInterval.isWeakSolution_of_classical`. -/
theorem dirichlet_stepA {f : ℝ → ℝ} (fL : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hfL : fL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f) (u : ContDiffMapIcc (zero_lt_one' ℝ).le 2)
    (hu : IsClassicalSolutionDirichlet f u) :
    IsWeakSolutionDirichlet fL (ofContDiffMapIcc (zero_lt_one' ℝ) u) := by
  refine isWeakSolution_of_classical (zero_lt_one' ℝ) (α := fun _ ↦ 1) (β := fun _ ↦ 0)
    (γ := fun _ ↦ 1) (constLinf 0 1 1) 0 (constLinf 0 1 1) fL (coeFn_constLinf 0 1 1)
    (Lp.coeFn_zero ℝ ⊤ _) (coeFn_constLinf 0 1 1) hfL contDiffOn_const continuousOn_const
    continuousOn_const u (fun x hx ↦ ?_) ?_ ?_
  · have e : (fun t ↦ (1 : ℝ) * u.shift.extend t) = u.shift.extend := funext fun t ↦ one_mul _
    rw [e, zero_mul, add_zero, one_mul, deriv_shift_extend (zero_lt_one' ℝ) u hx,
      ContDiffMapIcc.extend_of_mem _ (Ioo_subset_Icc_self hx)]
    exact hu.1 ⟨x, Ioo_subset_Icc_self hx⟩
  · rw [ContDiffMapIcc.extend_of_mem _ (left_mem_Icc.2 zero_le_one)]
    exact hu.2.1
  · rw [ContDiffMapIcc.extend_of_mem _ (right_mem_Icc.2 zero_le_one)]
    exact hu.2.2

/-- The coefficient `1` of the model problem is bounded below by `1` almost everywhere. -/
private theorem one_le_constLinf_ae :
    ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 1 ≤ constLinf 0 1 1 x :=
  (coeFn_constLinf 0 1 1).mono fun x hx ↦ by rw [hx]

/-- **Proposition 8.15 (Step B).** Given any `f ∈ L²(I)` there is a unique weak solution
`u ∈ H_0^1(I)` of (15). Lax–Milgram in the Hilbert space `H_0^1(I)` with the bilinear form
`a(u, v) = (u, v)_{H¹}` and the functional `v ↦ ∫ f v`; the backbone's
`EllipticInterval.existsUnique_isWeakSolution` with `α = γ = 1`. -/
theorem proposition_8_15 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! u, IsWeakSolutionDirichlet f u :=
  existsUnique_isWeakSolution (zero_lt_one' ℝ) (constLinf 0 1 1) (constLinf 0 1 1) one_pos
    one_le_constLinf_ae (one_le_constLinf_ae.mono fun _ hx ↦ zero_le_one.trans hx) f

/-- The energy of the model problem is the book's functional `½ ∫ (v'² + v²) − ∫ f v`. -/
theorem energy_dirichlet_eq (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (v : SobolevInterval 1 0 1) :
    (modelForm 0 1).energy (load 0 1 f) v
      = (1 / 2 : ℝ) * (∫ x in Ioo (0 : ℝ) 1,
          (SobolevInterval.deriv v 1 x ^ 2 + SobolevInterval.fn v x ^ 2))
        - ∫ x in Ioo (0 : ℝ) 1, f x * SobolevInterval.fn v x := by
  rw [SesqForm.energy, RCLike.re_to_real, RCLike.re_to_real, modelForm_apply,
    SobolevInterval.inner_eq_intervalIntegral zero_le_one,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, load_apply]
  congr 2
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [sq])

/-- **Proposition 8.15, Dirichlet's principle.** The weak solution `u` of (15) is obtained by
minimizing `½ ∫ (v'² + v²) − ∫ f v` over `v ∈ H_0^1(I)`: `u` minimizes the energy
`EllipticInterval.modelForm`'s `SesqForm.energy` (`energy_dirichlet_eq`) on `H_0^1(I)`, and
conversely (`SesqForm.isMinOn_energy_iff`, the form being symmetric and coercive). -/
theorem proposition_8_15_dirichletPrinciple (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {u : SobolevInterval 1 0 1} (hu : u ∈ SobolevIntervalZero 0 1) :
    IsWeakSolutionDirichlet f u ↔
      IsMinOn ((modelForm 0 1).energy (load 0 1 f)) (SobolevIntervalZero 0 1) u :=
  ⟨fun h ↦ (SesqForm.isMinOn_energy_iff (load 0 1 f) modelForm_isHermitian one_pos
    modelForm_isCoerciveWith _ hu).2 h.2, fun h ↦ ⟨hu, (SesqForm.isMinOn_energy_iff (load 0 1 f)
    modelForm_isHermitian one_pos modelForm_isCoerciveWith _ hu).1 h⟩⟩

/-- **Remark 22.** Given `F ∈ H^{-1}(I)`, the Riesz–Fréchet representation theorem gives a
unique `u ∈ H_0^1(I)` with `(u, v)_{H¹} = ⟨F, v⟩` for all `v ∈ H_0^1(I)`; the map `F ↦ u` is
the Riesz–Fréchet isomorphism `(InnerProductSpace.toDual ℝ H_0^1).symm` from `H^{-1}` onto
`H_0^1`. -/
theorem remark_8_22 (F : Hneg1 (Opens.Ioo 0 1)) :
    ∃! u : H10 (Opens.Ioo 0 1), ∀ v : H10 (Opens.Ioo 0 1), ⟪u, v⟫_ℝ = F v :=
  ⟨(InnerProductSpace.toDual ℝ (H10 (Opens.Ioo 0 1))).symm F,
    fun v ↦ InnerProductSpace.toDual_symm_apply, fun w hw ↦ by
      refine ext_inner_right ℝ fun v ↦ ?_
      rw [hw v, InnerProductSpace.toDual_symm_apply]⟩

/-- **Remark 22, "the function `u` coincides with the weak solution of (14)"**: for
`F = (v ↦ ∫ f v)`, `f ∈ L²(I)` (the inclusion `L² ⊆ H^{-1}` of §8.3,
`SobolevIntervalLpDual.ofL2`, whose values are these integrals by
`SobolevIntervalLpDual.ofL2_apply`), the element `u ∈ H_0^1(I)` given by the Riesz–Fréchet
isomorphism — the one with `(u, v)_{H¹} = ∫ f v` for all `v ∈ H_0^1` — is the weak solution of
(14) in the sense of (15). -/
theorem remark_8_22_eq_weakSolution (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (u : H10 (Opens.Ioo 0 1))
    (hu : ∀ v : H10 (Opens.Ioo 0 1),
      ⟪u, v⟫_ℝ = ∫ x in Ioo (0 : ℝ) 1, f x * SobolevInterval.fn (v : SobolevInterval 1 0 1) x) :
    IsWeakSolutionDirichlet f u :=
  ⟨u.2, fun v hv ↦ by
    have := hu ⟨v, hv⟩
    rw [Submodule.coe_inner] at this
    rw [modelForm_apply, load_apply]
    exact this⟩

/-! ### Steps C and D -/

/-- **Steps C and D, the `H²` regularity.** If `f ∈ L²` and `u ∈ H_0^1` is the weak solution of
(14), then `u ∈ H²`: `u' ∈ H¹` since `∫ u' v' = ∫ (f − u) v` for all test functions `v`; `u`
is the inclusion of a `Φ ∈ H²(0, 1)` with `Φ'' = Φ − f` a.e. The backbone's
`EllipticInterval.exists_sobolevInterval_two_of_forall_modelForm`. -/
theorem dirichlet_stepC (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {u : SobolevInterval 1 0 1} (hu : IsWeakSolutionDirichlet f u) :
    MemSobolevInterval (SobolevInterval.fn u) 2 0 1 ∧
      ∃ Φ : SobolevInterval 2 0 1, SobolevInterval.inclusionCLM 1 0 1 Φ = u ∧
        (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
          fun x ↦ SobolevInterval.fn Φ x - f x := by
  obtain ⟨Φ, hΦ, hΦ2⟩ := exists_sobolevInterval_two_of_forall_modelForm f hu.2
  refine ⟨?_, Φ, hΦ, hΦ2⟩
  have := SobolevInterval.memSobolevInterval_fn Φ
  rw [← SobolevInterval.fn_inclusionCLM Φ, hΦ] at this
  exact this

/-- **Steps C and D, the classical solution.** If, in addition, `f ∈ C(Ī)`, the weak solution
`u` belongs to `C²(Ī)` — `(u')' = u − f ∈ C(Ī)`, so `u' ∈ C¹(Ī)` by Remark 6 — and the passage
to a classical solution is Step D of §8.1: `u` is carried by a `v ∈ C²(Ī)` which is a classical
solution of (14). The backbone's `EllipticInterval.exists_contDiffMapIcc_of_deriv_two`, the
endpoint values from `u ∈ H_0^1`, and the equation at the endpoints by continuity. -/
theorem dirichlet_stepCD {f : ℝ → ℝ} (fL : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hfL : fL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f) (hf : ContinuousOn f (Icc 0 1))
    {u : SobolevInterval 1 0 1} (hu : IsWeakSolutionDirichlet fL u) :
    ∃ v : ContDiffMapIcc (zero_lt_one' ℝ).le 2,
      ofContDiffMapIcc (zero_lt_one' ℝ) v = u ∧ IsClassicalSolutionDirichlet f v := by
  obtain ⟨-, Φ, hΦ, hΦ2⟩ := dirichlet_stepC fL hu
  obtain ⟨v, hv, hode⟩ := exists_contDiffMapIcc_of_deriv_two (zero_lt_one' ℝ) fL hfL hf hΦ2
  rw [hΦ] at hv
  have hrep : ∀ x ∈ Icc (0 : ℝ) 1, v.extend x = SobolevInterval.rep u x := fun x hx ↦ by
    rw [← hv]; exact (rep_ofContDiffMapIcc (zero_lt_one' ℝ) v hx).symm
  refine ⟨v, hv, fun x ↦ ?_, ?_, ?_⟩
  · -- the equation on `(0, 1)`, extended to the endpoints by continuity
    have hae : (fun t ↦ -v.shift.shift.extend t + v.extend t)
        =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f := by
      refine (ae_restrict_mem measurableSet_Ioo).mono fun t ht ↦ ?_
      change -v.shift.shift.extend t + v.extend t = f t
      have := hode t ht
      rw [deriv_shift_extend (zero_lt_one' ℝ) v ht] at this
      rw [ContDiffMapIcc.extend_of_mem _ (Ioo_subset_Icc_self ht)]
      exact this
    have hEq := eqOn_Icc_of_ae_eq (zero_lt_one' ℝ)
      (v.shift.shift.extend.continuous.neg.add v.extend.continuous).continuousOn hf hae x.2
    change -v.shift.shift.extend x + v.extend x = f x at hEq
    rw [ContDiffMapIcc.extend_val, ContDiffMapIcc.extend_val] at hEq
    exact hEq
  · rw [← ContDiffMapIcc.extend_val, hrep 0 (left_mem_Icc.2 zero_le_one)]
    exact SobolevIntervalZero.rep_left_eq_zero (zero_lt_one' ℝ) hu.1
  · rw [← ContDiffMapIcc.extend_val, hrep 1 (right_mem_Icc.2 zero_le_one)]
    exact SobolevIntervalZero.rep_right_eq_zero (zero_lt_one' ℝ) hu.1

/-- **Remark 23.** If `f ∈ H^k(I)`, `k ≥ 1`, then the weak solution `u` of (15) belongs to
`H^{k+2}(I)` (by induction; `k = 0` is Step C). The backbone's
`EllipticInterval.memSobolevInterval_add_two_of_isWeakSolution`. -/
theorem remark_8_23 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {u : SobolevInterval 1 0 1}
    (hu : IsWeakSolutionDirichlet f u) {k : ℕ} (_hk : 1 ≤ k) (hf : MemSobolevInterval f k 0 1) :
    MemSobolevInterval (SobolevInterval.fn u) (k + 2) 0 1 :=
  memSobolevInterval_add_two_of_isWeakSolution f hu.2 hf

/-! ### Example 1: the inhomogeneous Dirichlet condition -/

/-- **Proposition 8.16 (Example 1).** Given `α, β ∈ ℝ` and `f ∈ L²(I)` there is a unique
`u ∈ H²(I)` satisfying (16): `−u'' + u = f` a.e. on `I`, `u(0) = α`, `u(1) = β`. The backbone's
`EllipticInterval.existsUnique_dirichlet_inhomogeneous` (Method 2, Stampacchia). -/
theorem proposition_8_16 (α β : ℝ) (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! Φ : SobolevInterval 2 0 1,
      ((SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
        fun x ↦ SobolevInterval.fn Φ x - f x) ∧
      SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 0 = α ∧
      SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 1 = β :=
  existsUnique_dirichlet_inhomogeneous (zero_lt_one' ℝ) f α β

/-- **Proposition 8.16, the minimization.** The solution `u` of (16) is obtained by minimizing
`½ ∫ (v'² + v²) − ∫ f v` over the closed convex set `K = {v ∈ H¹(I) : v(0) = α, v(1) = β}`
(`EllipticInterval.dirichletSet 0 1 α β`): its inclusion in `H¹` minimizes the energy on `K`
(Stampacchia's variational inequality (17), which it satisfies since the boundary terms of
Green's formula vanish against `v − u ∈ H_0^1`). -/
theorem proposition_8_16_min (α β : ℝ) (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - f x)
    (h0 : SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 0 = α)
    (h1 : SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 1 = β) :
    IsMinOn ((modelForm 0 1).energy (load 0 1 f)) (dirichletSet 0 1 α β)
      (SobolevInterval.inclusionCLM 1 0 1 Φ) := by
  have hK : SobolevInterval.inclusionCLM 1 0 1 Φ ∈ dirichletSet 0 1 α β := ⟨h0, h1⟩
  refine (dirichletSet_isMinOn_energy_iff (zero_lt_one' ℝ) f hK).2 fun v hv ↦ ?_
  have hmem : v - SobolevInterval.inclusionCLM 1 0 1 Φ ∈ SobolevIntervalZero 0 1 := by
    rw [mem_dirichletSet_iff_sub_mem (zero_lt_one' ℝ)] at hv hK
    have := (SobolevIntervalZero 0 1).sub_mem hv hK
    rwa [sub_sub_sub_cancel_right] at this
  exact (modelForm_inclusionCLM_eq_load_of_mem (zero_lt_one' ℝ) f hΦ hmem).ge

/-- **Proposition 8.16, "if in addition `f ∈ C(Ī)` then `u ∈ C²(Ī)`"**: the solution of (16)
is carried by a `v ∈ C²(Ī)` with `−v'' + v = f` on `(0, 1)`. The backbone's
`EllipticInterval.exists_contDiffMapIcc_of_deriv_two`. -/
theorem proposition_8_16_C2 {f : ℝ → ℝ} (fL : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hfL : fL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f) (hf : ContinuousOn f (Icc 0 1))
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - fL x) :
    ∃ v : ContDiffMapIcc (zero_lt_one' ℝ).le 2,
      ofContDiffMapIcc (zero_lt_one' ℝ) v = SobolevInterval.inclusionCLM 1 0 1 Φ ∧
      ∀ x ∈ Ioo (0 : ℝ) 1, -deriv v.shift.extend x + v.extend x = f x :=
  exists_contDiffMapIcc_of_deriv_two (zero_lt_one' ℝ) fL hfL hf hΦ

/-- **Proposition 8.16, Method 1.** Fix the affine `u₀` with `u₀(0) = α`, `u₀(1) = β`
(`EllipticInterval.affineLift`); the new unknown `ũ = u − u₀` satisfies the homogeneous problem
(14) with the datum `f + u₀'' − u₀ = f − u₀`: for the solution `Φ` of (16), `Φ − u₀` is the weak
solution of (14) with datum `f − u₀`. -/
theorem proposition_8_16_method1 (α β : ℝ) (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - f x)
    (h0 : SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 0 = α)
    (h1 : SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 1 = β) :
    IsWeakSolutionDirichlet (f - SobolevInterval.deriv (affineLift (zero_lt_one' ℝ) 2 α β) 0)
      (SobolevInterval.inclusionCLM 1 0 1 Φ - affineLift (zero_lt_one' ℝ) 1 α β) := by
  have hK : SobolevInterval.inclusionCLM 1 0 1 Φ ∈ dirichletSet 0 1 α β := ⟨h0, h1⟩
  refine ⟨(mem_dirichletSet_iff_sub_mem (zero_lt_one' ℝ) α β _).1 hK, fun v hv ↦ ?_⟩
  -- the affine lift solves the model equation with datum `u₀` (its second derivative is `0`)
  have hu₀ : (SobolevInterval.deriv (affineLift (zero_lt_one' ℝ) 2 α β) 2 : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun x ↦
        SobolevInterval.fn (affineLift (zero_lt_one' ℝ) 2 α β) x
          - SobolevInterval.deriv (affineLift (zero_lt_one' ℝ) 2 α β) 0 x := by
    rw [deriv_affineLift_two]
    refine (Lp.coeFn_zero ℝ 2 _).trans (Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.zero_apply, SobolevInterval.deriv_zero, sub_self]
  rw [form_sub_eq_of_forall _ _ _ f (fun w hw ↦ modelForm_inclusionCLM_eq_load_of_mem
    (zero_lt_one' ℝ) f hΦ hw) _ hv, ← inclusionCLM_affineLift (zero_lt_one' ℝ) α β,
    modelForm_inclusionCLM_eq_load_of_mem (zero_lt_one' ℝ) _ hu₀ hv, load_apply, load_apply,
    load_apply]
  have e : (fun x ↦ (f - SobolevInterval.deriv (affineLift (zero_lt_one' ℝ) 2 α β) 0) x
      * SobolevInterval.deriv v 0 x) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ f x * SobolevInterval.deriv v 0 x
        - SobolevInterval.deriv (affineLift (zero_lt_one' ℝ) 2 α β) 0 x
          * SobolevInterval.deriv v 0 x :=
    (Lp.coeFn_sub f (SobolevInterval.deriv (affineLift (zero_lt_one' ℝ) 2 α β) 0)).mono
      fun x hx ↦ by simp only [hx, Pi.sub_apply, sub_mul]
  rw [integral_congr_ae e, integral_sub (integrable_mul_L2 f (SobolevInterval.deriv v 0))
    (integrable_mul_L2 (SobolevInterval.deriv (affineLift (zero_lt_one' ℝ) 2 α β) 0)
      (SobolevInterval.deriv v 0))]

/-- **Proposition 8.16, Method 2 (Stampacchia).** On the closed convex set
`K = {v ∈ H¹(I) : v(0) = α, v(1) = β}` there is a unique `u ∈ K` satisfying the variational
inequality (17), `∫ u' (v − u)' + ∫ u (v − u) ≥ ∫ f (v − u)` for all `v ∈ K`; it minimizes
`½ ∫ (v'² + v²) − ∫ f v` over `K`, and it satisfies the weak equation (18) against `w ∈ H_0^1`
(set `v = u ± w`). The backbone's
`EllipticInterval.existsUnique_dirichletSet_of_variationalInequality`,
`dirichletSet_isMinOn_energy_iff` and `forall_modelForm_eq_load_of_variationalInequality`. -/
theorem proposition_8_16_method2 (α β : ℝ) (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! u, u ∈ dirichletSet 0 1 α β ∧
      (∀ v ∈ dirichletSet 0 1 α β, load 0 1 f (v - u) ≤ modelForm 0 1 u (v - u)) ∧
      IsMinOn ((modelForm 0 1).energy (load 0 1 f)) (dirichletSet 0 1 α β) u ∧
      ∀ w ∈ SobolevIntervalZero 0 1, modelForm 0 1 u w = load 0 1 f w := by
  obtain ⟨u, ⟨huK, hvi⟩, huniq⟩ := existsUnique_dirichletSet_of_variationalInequality
    (zero_lt_one' ℝ) f α β
  refine ⟨u, ⟨huK, hvi, (dirichletSet_isMinOn_energy_iff (zero_lt_one' ℝ) f huK).2 hvi,
    forall_modelForm_eq_load_of_variationalInequality (zero_lt_one' ℝ) f huK hvi⟩,
    fun w hw ↦ huniq w ⟨hw.1, hw.2.1⟩⟩

/-! ### Example 2: the Sturm–Liouville problem -/

section SturmLiouville

variable {p q r : ℝ → ℝ} {α₀ : ℝ}
  {pL rL qL : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))}

/-- A coefficient bounded below on `[0, 1]` is bounded below almost everywhere on `(0, 1)`. -/
private theorem ae_le_of_forall_Icc {g : ℝ → ℝ} {gL : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))}
    (hgL : gL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] g) {c : ℝ} (hg : ∀ x ∈ Icc (0 : ℝ) 1, c ≤ g x) :
    ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), c ≤ gL x := by
  filter_upwards [hgL, ae_restrict_mem measurableSet_Ioo] with x hx hxI
  rw [hx]
  exact hg x (Ioo_subset_Icc_self hxI)

/-- **Example 2 (Sturm–Liouville), existence and uniqueness.** For `p ∈ C¹(Ī)` with
`p ≥ α > 0`, `q ∈ C(Ī)` with `q ≥ 0` (carried by `pL, qL ∈ L^∞(I)`) and `f ∈ L²(I)`, there is a
unique `u ∈ H_0^1(I)` with `∫ p u' v' + ∫ q u v = ∫ f v` for all `v ∈ H_0^1(I)` (the Galerkin
problem of the symmetric form `a(u, v) = ∫ p u' v' + ∫ q u v`, `EllipticInterval.form 0 1 pL 0 qL`,
coercive by Poincaré's inequality); Lax–Milgram, the backbone's
`EllipticInterval.existsUnique_isWeakSolution`. -/
theorem example_8_2_existsUnique (hα₀ : 0 < α₀)
    (hpL : pL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] p) (hpα : ∀ x ∈ Icc (0 : ℝ) 1, α₀ ≤ p x)
    (hqL : qL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] q) (hq0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ q x)
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! u, IsGalerkinSolution (form 0 1 pL 0 qL) (load 0 1 f) (SobolevIntervalZero 0 1) u :=
  existsUnique_isWeakSolution (zero_lt_one' ℝ) pL qL hα₀ (ae_le_of_forall_Icc hpL hpα)
    (ae_le_of_forall_Icc hqL hq0) f

/-- The Sturm–Liouville form is symmetric. -/
private theorem form_isHermitian_of_symm : (form 0 1 pL 0 qL).IsHermitian := fun u v ↦ by
  rw [form_comm, RCLike.conj_to_real]

/-- **Example 2, the minimization.** The weak solution `u` is obtained by minimizing
`½ ∫ (p v'² + q v²) − ∫ f v` over `v ∈ H_0^1(I)`: it minimizes the energy of the form
restricted to `H_0^1(I)` over that space (the form is symmetric, `EllipticInterval.form_comm`,
and coercive on `H_0^1`). -/
theorem example_8_2_min (hα₀ : 0 < α₀)
    (hpL : pL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] p) (hpα : ∀ x ∈ Icc (0 : ℝ) 1, α₀ ≤ p x)
    (hqL : qL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] q) (hq0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ q x)
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {u : SobolevInterval 1 0 1}
    (hu : IsGalerkinSolution (form 0 1 pL 0 qL) (load 0 1 f) (SobolevIntervalZero 0 1) u) :
    IsMinOn (((form 0 1 pL 0 qL).restrict (SobolevIntervalZero 0 1)).energy
      ((load 0 1 f).comp (SobolevIntervalZero 0 1).subtypeL)) univ ⟨u, hu.1⟩ := by
  have hc : 0 < α₀ / (1 + ((1 : ℝ) - 0) ^ 2 / 2) := by positivity
  have := (SesqForm.isMinOn_energy_iff ((load 0 1 f).comp (SobolevIntervalZero 0 1).subtypeL)
    (form_isHermitian_of_symm.restrict _) hc
    (form_isCoerciveWith_restrict (zero_lt_one' ℝ) pL qL (ae_le_of_forall_Icc hpL hpα)
      (ae_le_of_forall_Icc hqL hq0) hα₀.le) ⊤ (u := ⟨u, hu.1⟩) Submodule.mem_top).2
    fun v _ ↦ by rw [SesqForm.restrict_apply]; exact hu.2 v v.2
  rwa [Submodule.top_coe] at this

/-- **Example 2, `u ∈ H²`.** It is clear from (19) that `p u' ∈ H¹`; thus (Corollary 8.10)
`u' = (1/p)(p u') ∈ H¹`, hence `u ∈ H²(I)`. The backbone's
`EllipticInterval.isWeakSolution_mem_sobolevInterval_two`. -/
theorem example_8_2_H2 (hα₀ : 0 < α₀) (hpL : pL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] p)
    (hp : ContDiffOn ℝ 1 p (Icc 0 1)) (hpα : ∀ x ∈ Icc (0 : ℝ) 1, α₀ ≤ p x)
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {u : SobolevInterval 1 0 1}
    (hu : IsGalerkinSolution (form 0 1 pL 0 qL) (load 0 1 f) (SobolevIntervalZero 0 1) u) :
    MemSobolevInterval (SobolevInterval.fn u) 2 0 1 :=
  isWeakSolution_mem_sobolevInterval_two (zero_lt_one' ℝ) pL 0 qL hpL hp
    (fun x hx ↦ (hα₀.trans_le (hpα x hx)).ne') f hu

/-- **Example 2, the classical solution.** If `f ∈ C(Ī)`, then `p u' ∈ C¹(Ī)`, so
`u ∈ C²(Ī)` and Step D carries over: `u` is carried by a `v ∈ C²(Ī)` with
`−(p v')' + q v = f` on `(0, 1)` and `v(0) = v(1) = 0`, a classical solution of (18). The
backbone's `EllipticInterval.exists_contDiffMapIcc_of_continuous`. -/
theorem example_8_2_C2 {f : ℝ → ℝ} (hpL : pL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] p)
    (hp : ContDiffOn ℝ 1 p (Icc 0 1)) (hpα : ∀ x ∈ Icc (0 : ℝ) 1, α₀ ≤ p x) (hα₀ : 0 < α₀)
    (hqL : qL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] q) (hq : ContinuousOn q (Icc 0 1))
    (fL : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hfL : fL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f) (hf : ContinuousOn f (Icc 0 1))
    {u : SobolevInterval 1 0 1}
    (hu : IsGalerkinSolution (form 0 1 pL 0 qL) (load 0 1 fL) (SobolevIntervalZero 0 1) u) :
    ∃ v : ContDiffMapIcc (zero_lt_one' ℝ).le 2, ofContDiffMapIcc (zero_lt_one' ℝ) v = u ∧
      (∀ x ∈ Ioo (0 : ℝ) 1,
        -deriv (fun t ↦ p t * v.shift.extend t) x + q x * v.extend x = f x) ∧
      v.extend 0 = 0 ∧ v.extend 1 = 0 := by
  obtain ⟨v, hv, hode⟩ := exists_contDiffMapIcc_of_continuous (zero_lt_one' ℝ) pL 0 qL fL
    (β := fun _ ↦ 0) hpL (Lp.coeFn_zero ℝ ⊤ _) hqL hfL hp (fun x hx ↦ (hα₀.trans_le (hpα x hx)).ne')
    continuousOn_const hq hf hu.2
  refine ⟨v, hv, fun x hx ↦ ?_, ?_, ?_⟩
  · have := hode x hx
    rwa [zero_mul, add_zero] at this
  · rw [← rep_ofContDiffMapIcc (zero_lt_one' ℝ) v (left_mem_Icc.2 zero_le_one), hv]
    exact SobolevIntervalZero.rep_left_eq_zero (zero_lt_one' ℝ) hu.1
  · rw [← rep_ofContDiffMapIcc (zero_lt_one' ℝ) v (right_mem_Icc.2 zero_le_one), hv]
    exact SobolevIntervalZero.rep_right_eq_zero (zero_lt_one' ℝ) hu.1

/-- **Example 2**, together: existence and uniqueness of the weak solution of the
Sturm–Liouville problem (18), its `H²` regularity, and the classical solution for continuous
`f`. -/
theorem example_8_2 (hα₀ : 0 < α₀)
    (hpL : pL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] p) (hp : ContDiffOn ℝ 1 p (Icc 0 1))
    (hpα : ∀ x ∈ Icc (0 : ℝ) 1, α₀ ≤ p x)
    (hqL : qL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] q) (hq : ContinuousOn q (Icc 0 1))
    (hq0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ q x) (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    (∃! u, IsGalerkinSolution (form 0 1 pL 0 qL) (load 0 1 f) (SobolevIntervalZero 0 1) u) ∧
    (∀ u, IsGalerkinSolution (form 0 1 pL 0 qL) (load 0 1 f) (SobolevIntervalZero 0 1) u →
      MemSobolevInterval (SobolevInterval.fn u) 2 0 1) ∧
    ∀ g : ℝ → ℝ, f =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] g → ContinuousOn g (Icc 0 1) →
      ∀ u, IsGalerkinSolution (form 0 1 pL 0 qL) (load 0 1 f) (SobolevIntervalZero 0 1) u →
      ∃ v : ContDiffMapIcc (zero_lt_one' ℝ).le 2, ofContDiffMapIcc (zero_lt_one' ℝ) v = u ∧
        (∀ x ∈ Ioo (0 : ℝ) 1,
          -deriv (fun t ↦ p t * v.shift.extend t) x + q x * v.extend x = g x) ∧
        v.extend 0 = 0 ∧ v.extend 1 = 0 :=
  ⟨example_8_2_existsUnique hα₀ hpL hpα hqL hq0 f,
    fun _ hu ↦ example_8_2_H2 hα₀ hpL hp hpα f hu,
    fun _ hfL hg _ hu ↦ example_8_2_C2 hpL hp hpα hα₀ hqL hq f hfL hg hu⟩

/-! #### The problem (20) with a first-order term -/

/-- `⟪γ f, f⟫_{L²} ≥ γ₀ ‖f‖²` for a coefficient `γ ≥ γ₀` a.e. -/
private theorem inner_mulL_self_ge {γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))} {γ₀ : ℝ}
    (hγ : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), γ₀ ≤ γ x)
    (g : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) : γ₀ * ‖g‖ ^ 2 ≤ ⟪mulL γ g, g⟫_ℝ := by
  rw [inner_mulL_eq_integral, ← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_const_mul]
  refine integral_mono_ae ((L2.integrable_inner (𝕜 := ℝ) g g).const_mul γ₀)
    (integrable_mul_mul _ _ _) ?_
  filter_upwards [hγ] with x hx
  simp only [RCLike.inner_apply, conj_trivial]
  nlinarith [mul_self_nonneg (g x)]

/-- **Example 2, the form of (20) is coercive in case (i)**: if `q ≥ 1` and
`‖r‖_∞² < 4α`, the form `a(u, v) = ∫ p u' v' + ∫ r u' v + ∫ q u v` is coercive on all of
`H¹(I)`, with the constant `(4α − ‖r‖_∞²) / (4(α + 1))`:
`a(v, v) ≥ α ‖v'‖² − ‖r‖_∞ ‖v'‖ ‖v‖ + ‖v‖²`, a positive definite quadratic form in
`(‖v'‖, ‖v‖)`. -/
theorem example_8_2_general_i_coercive (hα₀ : 0 < α₀)
    (hp : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ pL x)
    (hq : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 1 ≤ qL x) (_hr : ‖rL‖ ^ 2 < 4 * α₀) :
    (form 0 1 pL rL qL).IsCoerciveWith ((4 * α₀ - ‖rL‖ ^ 2) / (4 * (α₀ + 1))) := by
  intro v
  rw [RCLike.re_to_real, form_apply_inner, SobolevInterval.norm_sq_eq, Fin.sum_univ_two]
  have hX := inner_mulL_self_ge hp (SobolevInterval.deriv v 1)
  have hY := inner_mulL_self_ge hq (SobolevInterval.deriv v 0)
  have hR := abs_pairing_mulL_le rL 1 0 v v
  rw [pairing_apply, abs_le] at hR
  obtain ⟨c, hc⟩ : ∃ c, c = (4 * α₀ - ‖rL‖ ^ 2) / (4 * (α₀ + 1)) := ⟨_, rfl⟩
  rw [← hc]
  have hR0 := norm_nonneg rL
  have hX0 := norm_nonneg (SobolevInterval.deriv v 1)
  have hY0 := norm_nonneg (SobolevInterval.deriv v 0)
  -- the discriminant of the quadratic form in `(‖v'‖, ‖v‖)`: `4 (α₀ − c)(1 − c) = ‖r‖² + 4c²`
  have hdisc : 4 * c * (α₀ + 1) = 4 * α₀ - ‖rL‖ ^ 2 := by
    rw [hc]; field_simp
  have hcpos : 0 < α₀ - c := by
    have : c < α₀ := by
      rw [hc, div_lt_iff₀ (by positivity)]
      nlinarith [sq_nonneg ‖rL‖]
    linarith
  have key : 4 * (α₀ - c) * ((α₀ - c) * ‖SobolevInterval.deriv v 1‖ ^ 2
      - ‖rL‖ * ‖SobolevInterval.deriv v 1‖ * ‖SobolevInterval.deriv v 0‖
      + (1 - c) * ‖SobolevInterval.deriv v 0‖ ^ 2)
      = (2 * (α₀ - c) * ‖SobolevInterval.deriv v 1‖ - ‖rL‖ * ‖SobolevInterval.deriv v 0‖) ^ 2
        + (4 * c ^ 2) * ‖SobolevInterval.deriv v 0‖ ^ 2 := by
    nlinarith [hdisc]
  have hquad : 0 ≤ (α₀ - c) * ‖SobolevInterval.deriv v 1‖ ^ 2
      - ‖rL‖ * ‖SobolevInterval.deriv v 1‖ * ‖SobolevInterval.deriv v 0‖
      + (1 - c) * ‖SobolevInterval.deriv v 0‖ ^ 2 := by
    have h4 : 0 ≤ 4 * (α₀ - c) * ((α₀ - c) * ‖SobolevInterval.deriv v 1‖ ^ 2
        - ‖rL‖ * ‖SobolevInterval.deriv v 1‖ * ‖SobolevInterval.deriv v 0‖
        + (1 - c) * ‖SobolevInterval.deriv v 0‖ ^ 2) := by
      rw [key]; positivity
    exact nonneg_of_mul_nonneg_right h4 (by positivity) |> fun h ↦ by
      rcases le_or_gt 0 ((α₀ - c) * ‖SobolevInterval.deriv v 1‖ ^ 2
        - ‖rL‖ * ‖SobolevInterval.deriv v 1‖ * ‖SobolevInterval.deriv v 0‖
        + (1 - c) * ‖SobolevInterval.deriv v 0‖ ^ 2) with h' | h'
      · exact h'
      · exact absurd h4 (not_le.2 (mul_neg_of_pos_of_neg (by positivity) h'))
  nlinarith [hX, hY, hR.1, hquad]

/-- **Example 2, case (i): the problem (20) with `q ≥ 1` and `‖r‖_∞² < 4α`** has a unique weak
solution `u ∈ H_0^1(I)` (Lax–Milgram; "there is no straightforward associated minimization
problem", the form not being symmetric). -/
theorem example_8_2_general_i (hα₀ : 0 < α₀)
    (hp : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ pL x)
    (hq : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 1 ≤ qL x) (hr : ‖rL‖ ^ 2 < 4 * α₀)
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! u, IsGalerkinSolution (form 0 1 pL rL qL) (load 0 1 f) (SobolevIntervalZero 0 1) u :=
  existsUnique_isGalerkinSolution_of_isClosed (by
      rw [div_pos_iff_of_pos_right (by positivity)]; linarith)
    (example_8_2_general_i_coercive hα₀ hp hq hr) (load 0 1 f) SobolevMultiIndexZero.isClosed

/-- **Example 2, case (ii): the form of (20) is coercive on `H_0^1(I)`** if `q ≥ 1`,
`r ∈ C¹(Ī)` and `r' ≤ 2`, using `∫ r v' v = −½ ∫ r' v²` for `v ∈ H_0^1`
(`EllipticInterval.integral_mul_deriv_mul_rep_eq`): `a(v, v) ≥ α ‖v'‖²`, hence, by Poincaré's
inequality, the restricted form is coercive with constant `α / (1 + 1/2)`. The backbone's
`EllipticInterval.form_isCoerciveWith_seminorm_of_le`. -/
theorem example_8_2_general_ii_coercive (hα₀ : 0 < α₀)
    (hp : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ pL x)
    (hq : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 1 ≤ qL x)
    (hrL : rL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] r) (hr : ContDiffOn ℝ 1 r (Icc 0 1))
    (hr' : ∀ x ∈ Icc (0 : ℝ) 1, deriv r x ≤ 2) :
    ((form 0 1 pL rL qL).restrict (SobolevIntervalZero 0 1)).IsCoerciveWith
      (α₀ / (1 + ((1 : ℝ) - 0) ^ 2 / 2)) := by
  intro v
  rw [SesqForm.restrict_apply, RCLike.re_to_real, ← Submodule.norm_coe]
  have hcond : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), deriv r x / 2 ≤ qL x := by
    filter_upwards [hq, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    linarith [hr' x (Ioo_subset_Icc_self hxI)]
  have h1 := form_isCoerciveWith_seminorm_of_le (zero_lt_one' ℝ) pL rL qL hp hrL hr hcond v.2
  have h2 := SobolevIntervalZero.norm_le_seminorm (zero_lt_one' ℝ) v.2
  have h3 : 0 ≤ SobolevInterval.seminorm 1 0 1 (v : SobolevInterval 1 0 1) := apply_nonneg _ _
  have h4 : 0 < 1 + ((1 : ℝ) - 0) ^ 2 / 2 := by norm_num
  rw [div_mul_eq_mul_div, div_le_iff₀ h4]
  have h5 : ‖(v : SobolevInterval 1 0 1)‖ ^ 2
      ≤ (1 + ((1 : ℝ) - 0) ^ 2 / 2)
        * SobolevInterval.seminorm 1 0 1 (v : SobolevInterval 1 0 1) ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) h2 2
    rw [mul_pow, Real.sq_sqrt h4.le] at this
    exact this
  nlinarith [h1, h5]

/-- **Example 2, case (ii): the problem (20) with `q ≥ 1`, `r ∈ C¹(Ī)`, `r' ≤ 2`** has a unique
weak solution `u ∈ H_0^1(I)` (Lax–Milgram on `H_0^1`). -/
theorem example_8_2_general_ii (hα₀ : 0 < α₀)
    (hp : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ pL x)
    (hq : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 1 ≤ qL x)
    (hrL : rL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] r) (hr : ContDiffOn ℝ 1 r (Icc 0 1))
    (hr' : ∀ x ∈ Icc (0 : ℝ) 1, deriv r x ≤ 2) (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! u, IsGalerkinSolution (form 0 1 pL rL qL) (load 0 1 f) (SobolevIntervalZero 0 1) u := by
  have hc : 0 < α₀ / (1 + ((1 : ℝ) - 0) ^ 2 / 2) := by positivity
  obtain ⟨w, hw, hwu⟩ := SesqForm.laxMilgram
    ((form 0 1 pL rL qL).restrict (SobolevIntervalZero 0 1))
    ((load 0 1 f).comp (SobolevIntervalZero 0 1).subtypeL) hc
    (example_8_2_general_ii_coercive hα₀ hp hq hrL hr hr')
  refine ⟨(w : SobolevInterval 1 0 1), ⟨w.2, fun v hv ↦ hw ⟨v, hv⟩⟩, fun u hu ↦ ?_⟩
  have := hwu ⟨u, hu.1⟩ fun v ↦ hu.2 v v.2
  rw [← this]

/-- **Example 2, the more general problem (20)** `−(p u')' + r u' + q u = f`, `u(0) = u(1) = 0`,
with `p, q, f` as before and `r ∈ C(Ī)`: the bilinear form `∫ p u' v' + ∫ r u' v + ∫ q u v` is
not symmetric, but it is coercive, and Lax–Milgram gives a unique weak solution in `H_0^1(I)`,
(i) if `q ≥ 1` and `‖r‖_∞² < 4α`, or (ii) if `q ≥ 1`, `r ∈ C¹(Ī)` and `r' ≤ 2`. The
symmetrization by `ζ = e^{−R}`, `R' = r/p`, is `example_8_2_symmetrization`. -/
theorem example_8_2_general (hα₀ : 0 < α₀)
    (hp : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ pL x)
    (hq : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 1 ≤ qL x)
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    (‖rL‖ ^ 2 < 4 * α₀ →
      ∃! u, IsGalerkinSolution (form 0 1 pL rL qL) (load 0 1 f) (SobolevIntervalZero 0 1) u) ∧
    ∀ r : ℝ → ℝ, rL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] r → ContDiffOn ℝ 1 r (Icc 0 1) →
      (∀ x ∈ Icc (0 : ℝ) 1, deriv r x ≤ 2) →
      ∃! u, IsGalerkinSolution (form 0 1 pL rL qL) (load 0 1 f) (SobolevIntervalZero 0 1) u :=
  ⟨fun hr ↦ example_8_2_general_i hα₀ hp hq hr f,
    fun _ hrL hr hr' ↦ example_8_2_general_ii hα₀ hp hq hrL hr hr' f⟩

/-- **Example 2, the symmetrization: `ζ' p + ζ r = 0`.** With `R` a primitive of `r/p` and
`ζ = e^{−R}`, `ζ' p + ζ r = 0` at every point where `p ≠ 0`. -/
theorem example_8_2_symmetrization_deriv {R : ℝ → ℝ} {x : ℝ}
    (hR : HasDerivAt R (r x / p x) x) (hpx : p x ≠ 0) :
    deriv (fun t ↦ Real.exp (-R t)) x * p x + Real.exp (-R x) * r x = 0 := by
  have hζ : HasDerivAt (fun t ↦ Real.exp (-R t)) (Real.exp (-R x) * -(r x / p x)) x :=
    (Real.hasDerivAt_exp _).comp x hR.neg
  rw [hζ.deriv]
  field_simp
  ring

/-- **Example 2, the symmetrization of (20).** Let `R` be a primitive of `r/p` and
`ζ = e^{−R}`. For `u ∈ C²`, the equation (20), `−(p u')' + r u' + q u = f`, holds at `x` if and
only if `−(ζ p u')' + ζ q u = ζ f` does (multiply by `ζ > 0` and use `ζ' p + ζ r = 0`). -/
theorem example_8_2_symmetrization {R u f : ℝ → ℝ} (hR : ∀ x, HasDerivAt R (r x / p x) x)
    (hp : ∀ x, p x ≠ 0) (hpd : Differentiable ℝ p) (hu : ContDiff ℝ 2 u) (x : ℝ) :
    -deriv (fun t ↦ p t * deriv u t) x + r x * deriv u x + q x * u x = f x ↔
      -deriv (fun t ↦ Real.exp (-R t) * (p t * deriv u t)) x
        + Real.exp (-R x) * (q x * u x) = Real.exp (-R x) * f x := by
  have hu1 : Differentiable ℝ (deriv u) :=
    (hu.iterate_deriv' 1 1).differentiable one_ne_zero
  have hζ : HasDerivAt (fun t ↦ Real.exp (-R t)) (Real.exp (-R x) * -(r x / p x)) x :=
    (Real.hasDerivAt_exp _).comp x (hR x).neg
  have hpu : HasDerivAt (fun t ↦ p t * deriv u t) (deriv (fun t ↦ p t * deriv u t) x) x :=
    ((hpd x).hasDerivAt.mul (hu1 x).hasDerivAt).differentiableAt.hasDerivAt
  have hd := (hζ.fun_mul hpu).deriv
  rw [hd]
  have hζpos : 0 < Real.exp (-R x) := Real.exp_pos _
  constructor
  · intro h
    field_simp
    have := hp x
    field_simp at h ⊢
    nlinarith [h, hζpos]
  · intro h
    have hp' := hp x
    field_simp at h
    have : Real.exp (-R x) * (-deriv (fun t ↦ p t * deriv u t) x + r x * deriv u x + q x * u x)
        = Real.exp (-R x) * f x := by
      field_simp
      nlinarith [h]
    exact mul_left_cancel₀ hζpos.ne' this

end SturmLiouville

/-! ### Examples 3–7: Neumann, mixed, Robin and periodic conditions -/

/-- **Proposition 8.17 (Example 3, homogeneous Neumann).** Given `f ∈ L²(I)` there is a unique
`u ∈ H²(I)` satisfying (21): `−u'' + u = f` a.e. on `I`, `u'(0) = u'(1) = 0` (`u ∈ H²` implies
`u ∈ C¹(Ī)`, footnote 13, so `u'(0)` makes sense). The backbone's
`EllipticInterval.existsUnique_neumann`: Lax–Milgram on all of `H¹(I)` for the weak
formulation (22), then the natural boundary conditions from (23). -/
theorem proposition_8_17 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! Φ : SobolevInterval 2 0 1,
      ((SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
        fun x ↦ SobolevInterval.fn Φ x - f x) ∧
      SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 0 = 0 ∧
      SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 1 = 0 :=
  existsUnique_neumann (zero_lt_one' ℝ) f

/-- **Proposition 8.17, the weak formulation (22) and the minimization.** The solution `u` of
(21) satisfies `∫ u' v' + ∫ u v = ∫ f v` for all `v ∈ H¹(I)` (Green's formula, the boundary
terms vanishing), and it is obtained by minimizing `½ ∫ (v'² + v²) − ∫ f v` over all of
`H¹(I)`. -/
theorem proposition_8_17_min (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - f x)
    (h0 : SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 0 = 0)
    (h1 : SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 1 = 0) :
    (∀ v, modelForm 0 1 (SobolevInterval.inclusionCLM 1 0 1 Φ) v = load 0 1 f v) ∧
      IsMinOn ((modelForm 0 1).energy (load 0 1 f)) univ
        (SobolevInterval.inclusionCLM 1 0 1 Φ) := by
  have hweak : ∀ v, modelForm 0 1 (SobolevInterval.inclusionCLM 1 0 1 Φ) v = load 0 1 f v :=
    fun v ↦ by
      rw [modelForm_inclusionCLM_eq_of_deriv_two (zero_lt_one' ℝ) f hΦ v, h0, h1]; ring
  exact ⟨hweak, (neumann_isMinOn_energy_iff (load 0 1 f) _).2 hweak⟩

/-- **Proposition 8.17, "if in addition `f ∈ C(Ī)` then `u ∈ C²(Ī)`"**. -/
theorem proposition_8_17_C2 {f : ℝ → ℝ} (fL : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hfL : fL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f) (hf : ContinuousOn f (Icc 0 1))
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - fL x) :
    ∃ v : ContDiffMapIcc (zero_lt_one' ℝ).le 2,
      ofContDiffMapIcc (zero_lt_one' ℝ) v = SobolevInterval.inclusionCLM 1 0 1 Φ ∧
      ∀ x ∈ Ioo (0 : ℝ) 1, -deriv v.shift.extend x + v.extend x = f x :=
  exists_contDiffMapIcc_of_deriv_two (zero_lt_one' ℝ) fL hfL hf hΦ

/-- **Proposition 8.18 (Example 4, inhomogeneous Neumann).** Given any `f ∈ L²(I)` and
`α, β ∈ ℝ` there is a unique `u ∈ H²(I)` satisfying (24): `−u'' + u = f` a.e., `u'(0) = α`,
`u'(1) = β`; it is obtained by minimizing `½ ∫ (v'² + v²) − ∫ f v + α v(0) − β v(1)` over
`H¹(I)` — the energy of the load `EllipticInterval.neumannLoad`, `v ↦ ∫ f v − α v(0) + β v(1)`,
which is continuous by Theorem 8.8. The backbone's
`EllipticInterval.existsUnique_neumann_inhomogeneous`. -/
theorem proposition_8_18 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (α β : ℝ) :
    ∃! Φ : SobolevInterval 2 0 1,
      ((SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
        fun x ↦ SobolevInterval.fn Φ x - f x) ∧
      SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 0 = α ∧
      SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 1 = β :=
  existsUnique_neumann_inhomogeneous (zero_lt_one' ℝ) f α β

/-- **Proposition 8.18, the minimization.** The solution of (24) minimizes
`½ ∫ (v'² + v²) − ∫ f v + α v(0) − β v(1)` over `H¹(I)`: it satisfies the weak formulation with
the load `neumannLoad`, and Dirichlet's principle on `H¹(I)`. -/
theorem proposition_8_18_min (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (α β : ℝ)
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - f x)
    (h0 : SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 0 = α)
    (h1 : SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 1 = β) :
    IsMinOn ((modelForm 0 1).energy (neumannLoad (zero_lt_one' ℝ) f α β)) univ
      (SobolevInterval.inclusionCLM 1 0 1 Φ) := by
  refine (neumann_isMinOn_energy_iff _ _).2 fun v ↦ ?_
  rw [modelForm_inclusionCLM_eq_of_deriv_two (zero_lt_one' ℝ) f hΦ v, h0, h1,
    neumannLoad_apply]
  ring

/-- **Example 5 (mixed boundary condition).** For `f ∈ L²(I)` there is a unique `u ∈ H²(I)`
with `−u'' + u = f` a.e., `u(0) = 0`, `u'(1) = 0` (25); the weak formulation (26) is set in
`H = {v ∈ H¹(I) : v(0) = 0}` (`EllipticInterval.mixedSpace`), "the rest is left to the reader":
the backbone's `EllipticInterval.existsUnique_mixed`. -/
theorem example_8_5 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! Φ : SobolevInterval 2 0 1,
      ((SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
        fun x ↦ SobolevInterval.fn Φ x - f x) ∧
      SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 0 = 0 ∧
      SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 1 = 0 :=
  existsUnique_mixed (zero_lt_one' ℝ) f

/-- **Example 6 (Robin boundary condition), the form.** On `H = {v ∈ H¹(I) : v(1) = 0}`
(`EllipticInterval.robinSpace`) the bilinear form
`a(u, v) = ∫ u' v' + ∫ u v + k u(0) v(0)` (`EllipticInterval.robinForm`) is symmetric and
continuous, and coercive if `k ≥ 0`. -/
theorem example_8_6_coercive {k : ℝ} (hk : 0 ≤ k) :
    (∀ u v : SobolevInterval 1 0 1, robinForm (zero_lt_one' ℝ) k u v
      = modelForm 0 1 u v + k * (SobolevInterval.rep u 0 * SobolevInterval.rep v 0)) ∧
    (robinForm (zero_lt_one' ℝ) k).IsHermitian ∧ (robinForm (zero_lt_one' ℝ) k).IsCoerciveWith 1 :=
  ⟨robinForm_apply (zero_lt_one' ℝ) k, robinForm_isHermitian (zero_lt_one' ℝ) k,
    robinForm_isCoerciveWith (zero_lt_one' ℝ) hk⟩

/-- **Example 6 (Robin boundary condition).** For `k ≥ 0` and `f ∈ L²(I)` there is a unique
`u ∈ H²(I)` with `−u'' + u = f` a.e., `u'(0) = k u(0)`, `u(1) = 0` (27): Lax–Milgram for the
Robin form on `H = {v ∈ H¹(I) : v(1) = 0}`. The backbone's `EllipticInterval.existsUnique_robin`.
(Footnotes 14–15, the general third-type condition and small negative `k`, are not
formalized.) -/
theorem example_8_6 {k : ℝ} (hk : 0 ≤ k) (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! Φ : SobolevInterval 2 0 1,
      ((SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
        fun x ↦ SobolevInterval.fn Φ x - f x) ∧
      SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 0
        = k * SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 0 ∧
      SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 1 = 0 :=
  existsUnique_robin (zero_lt_one' ℝ) f hk

/-- **Example 7 (periodic boundary conditions).** For `f ∈ L²(I)` there is a unique
`u ∈ H²(I)` with `−u'' + u = f` a.e., `u(0) = u(1)`, `u'(0) = u'(1)` (28): Lax–Milgram for the
form `∫ u' v' + ∫ u v` on `H = {v ∈ H¹(I) : v(0) = v(1)}` (`EllipticInterval.periodicSpace`),
the weak formulation being (29). The backbone's `EllipticInterval.existsUnique_periodic`. -/
theorem example_8_7 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! Φ : SobolevInterval 2 0 1,
      ((SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
        fun x ↦ SobolevInterval.fn Φ x - f x) ∧
      SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 0
        = SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 1 ∧
      SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 0
        = SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 1 :=
  existsUnique_periodic (zero_lt_one' ℝ) f

/-- **Examples 5–7, the `C²` clause.** For each of the mixed, Robin and periodic problems, if
`f ∈ C(Ī)` the solution is classical: it is carried by a `v ∈ C²(Ī)` with `−v'' + v = f` on
`(0, 1)`. The backbone's `EllipticInterval.exists_contDiffMapIcc_of_deriv_two`. -/
theorem example_8_5_6_7_C2 {f : ℝ → ℝ} (fL : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hfL : fL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f) (hf : ContinuousOn f (Icc 0 1))
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - fL x) :
    ∃ v : ContDiffMapIcc (zero_lt_one' ℝ).le 2,
      ofContDiffMapIcc (zero_lt_one' ℝ) v = SobolevInterval.inclusionCLM 1 0 1 Φ ∧
      ∀ x ∈ Ioo (0 : ℝ) 1, -deriv v.shift.extend x + v.extend x = f x :=
  exists_contDiffMapIcc_of_deriv_two (zero_lt_one' ℝ) fL hfL hf hΦ

/-! ### Example 8: a boundary value problem on `ℝ` -/

/-- **Example 8, a classical solution is a weak solution.** For `f ∈ L²(ℝ)` (class `fL` of the
function `f`), a classical solution of (30) — `u ∈ C²(ℝ)` with `−u'' + u = f` on `ℝ` and
`u(x) → 0` as `|x| → ∞` — lies in `H¹(ℝ)` (the cut-off argument with `ζ_n`), and it is a weak
solution: `∫ u' v' + ∫ u v = ∫ f v` for all `v ∈ H¹(ℝ)` (31), i.e. `u` is the element
`EllipticInterval.Line.solution fL` with `⟪u, v⟫_{H¹} = ∫ f v`. The backbone's
`EllipticInterval.Line.memSobolevIntervalLp_of_classical` and `Line.isWeakSolution_of_classical`. -/
theorem example_8_8_classical_weak {u f : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (fL : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hfL : fL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] f)
    (hode : ∀ x, -deriv (deriv u) x + u x = f x) (hlim : Tendsto u (cocompact ℝ) (𝓝 0)) :
    MemSobolevIntervalLp u 1 2 ⊤ ∧
      ∃ U : SobolevIntervalLp 1 2 ⊤, (∀ x, U.rep x = u x) ∧
        ∀ v : SobolevIntervalLp 1 2 ⊤, Line.form U v = Line.load fL v :=
  have hf : MemLp f 2 volume :=
    (SobolevIntervalLp.memLp_restrict_top_iff.1 (Lp.memLp fL)).ae_eq
      (SobolevIntervalLp.eventuallyEq_restrict_top_iff.1 hfL)
  let ⟨U, hU, hUrep, _⟩ := Line.isWeakSolution_of_classical hu fL hfL hode hlim
  ⟨Line.memSobolevIntervalLp_of_classical hu hf hode hlim, U, hUrep, fun v ↦ by
    rw [hU]; exact Line.form_solution fL v⟩

/-- **Example 8, existence and uniqueness of the weak solution.** For `f ∈ L²(ℝ)` there is
exactly one `u ∈ H¹(ℝ)` with `∫ u' v' + ∫ u v = ∫ f v` for all `v ∈ H¹(ℝ)` (31): Lax–Milgram
(the Riesz–Fréchet theorem) in the Hilbert space `H¹(ℝ)`, the backbone's
`EllipticInterval.Line.solution`. -/
theorem example_8_8_existsUnique (fL : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    ∃! u : SobolevIntervalLp 1 2 ⊤, ∀ v, Line.form u v = Line.load fL v :=
  ⟨Line.solution fL, Line.form_solution fL, fun _ hu ↦ Line.eq_solution_of_forall hu⟩

/-- **Example 8, regularity and the classical solution.** The weak solution `u` of (30) belongs
to `H²(ℝ)`; if furthermore `f ∈ C(ℝ)` then `u ∈ C²(ℝ)` and, using Corollary 8.9, `u(x) → 0` at
infinity: for `f ∈ L²(ℝ) ∩ C(ℝ)`, problem (30) has a unique classical solution, which belongs to
`H²(ℝ)`. The backbone's `EllipticInterval.Line.memSobolevIntervalLp_two_solution`,
`contDiff_rep_solution`, `tendsto_rep_solution_cocompact` and `exists_classical_solution`. -/
theorem example_8_8_regularity (fL : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    MemSobolevIntervalLp (Line.solution fL).fn 2 2 ⊤ ∧
      Tendsto (Line.solution fL).rep (cocompact ℝ) (𝓝 0) ∧
      ∀ f : ℝ → ℝ, fL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] f → Continuous f →
        (ContDiff ℝ 2 (Line.solution fL).rep ∧
          ∀ x, -deriv (deriv (Line.solution fL).rep) x + (Line.solution fL).rep x = f x) ∧
        ∃! w : ℝ → ℝ, ContDiff ℝ 2 w ∧ (∀ x, -deriv (deriv w) x + w x = f x) ∧
          Tendsto w (cocompact ℝ) (𝓝 0) :=
  ⟨Line.memSobolevIntervalLp_two_solution fL, Line.tendsto_rep_solution_cocompact fL,
    fun _ hfL hf ↦ ⟨Line.contDiff_rep_solution fL hfL hf, Line.exists_classical_solution fL hfL hf⟩⟩

/-- **Example 8**, together: a classical solution of (30) lies in `H¹(ℝ)` and is the weak
solution; the weak solution exists and is unique, lies in `H²(ℝ)`, tends to `0` at infinity, and
for `f ∈ L²(ℝ) ∩ C(ℝ)` is the unique classical solution. -/
theorem example_8_8 (fL : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    (∀ u f : ℝ → ℝ, ContDiff ℝ 2 u → fL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] f →
      (∀ x, -deriv (deriv u) x + u x = f x) → Tendsto u (cocompact ℝ) (𝓝 0) →
      MemSobolevIntervalLp u 1 2 ⊤ ∧ ∀ x, (Line.solution fL).rep x = u x) ∧
    (∃! u : SobolevIntervalLp 1 2 ⊤, ∀ v, Line.form u v = Line.load fL v) ∧
    MemSobolevIntervalLp (Line.solution fL).fn 2 2 ⊤ ∧
    ∀ f : ℝ → ℝ, fL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] f → Continuous f →
      ∃! w : ℝ → ℝ, ContDiff ℝ 2 w ∧ (∀ x, -deriv (deriv w) x + w x = f x) ∧
        Tendsto w (cocompact ℝ) (𝓝 0) :=
  ⟨fun u _ hu hfL hode hlim ↦
    ⟨(example_8_8_classical_weak hu fL hfL hode hlim).1, fun x ↦ by
      rw [Line.eq_rep_solution_of_classical fL hfL hu hode hlim]⟩,
    example_8_8_existsUnique fL, Line.memSobolevIntervalLp_two_solution fL,
    fun _ hfL hf ↦ Line.exists_classical_solution fL hfL hf⟩

/-! ### Remarks 24 and 25 -/

/-- **Remark 24, "this problem need not have a solution even if `f` is smooth with compact
support (why?)".** There is `f ∈ C_c^∞(ℝ)` (a nonnegative bump with `f(0) = 1`) such that
the problem `−u'' = f` on `ℝ`, `u(x) → 0` as `|x| → ∞`, has no classical solution: for such
a solution `u'' = −f ≤ 0`, so `u'` is nonincreasing; if `u'(x₀) < 0` then `u(y) ≤ u(x₀) +
u'(x₀)(y − x₀) → −∞` as `y → +∞`, and if `u'(x₀) > 0` then `u(y) → −∞` as `y → −∞`; so
`u' ≡ 0`, `u` is constant, hence `0`, and `f = 0`. -/
theorem remark_8_24_exists_not_solvable :
    ∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      ¬ ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ (∀ x, -deriv (deriv u) x = f x) ∧
        Tendsto u (cocompact ℝ) (𝓝 0) := by
  obtain ⟨φ, hφin⟩ : ∃ φ : ContDiffBump (0 : ℝ), φ.rIn = 1 := ⟨⟨1, 2, one_pos, one_lt_two⟩, rfl⟩
  refine ⟨φ, φ.contDiff, φ.hasCompactSupport, ?_⟩
  rintro ⟨u, hu, hode, hlim⟩
  rw [cocompact_eq_atBot_atTop, tendsto_sup] at hlim
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hu2 : Differentiable ℝ (deriv u) := (hu.iterate_deriv' 1 1).differentiable one_ne_zero
  have hanti : Antitone (deriv u) := antitone_of_deriv_nonpos hu2 fun x ↦ by
    have := hode x
    linarith [φ.nonneg' x]
  -- `u' ≡ 0`
  have hderiv : ∀ x, deriv u x = 0 := fun x₀ ↦ by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · -- `u → −∞` at `+∞`
      have hbd : ∀ y, x₀ ≤ y → u y - u x₀ ≤ deriv u x₀ * (y - x₀) := fun y hy ↦
        (convex_Ici x₀).image_sub_le_mul_sub_of_deriv_le hu1.continuous.continuousOn
          hu1.differentiableOn (fun z hz ↦ hanti (interior_subset (s := Ici x₀) hz).out)
          x₀ self_mem_Ici y hy hy
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.2.eventually (eventually_gt_nhds
        (show (-1 : ℝ) < 0 by norm_num)))
      obtain ⟨y, hy₁, hy₂⟩ : ∃ y, max N x₀ ≤ y ∧ deriv u x₀ * (y - x₀) ≤ -(2 + |u x₀|) := by
        refine ⟨max (max N x₀) (x₀ + (2 + |u x₀|) / (-deriv u x₀)), le_max_left _ _, ?_⟩
        have h1 : x₀ + (2 + |u x₀|) / (-deriv u x₀)
            ≤ max (max N x₀) (x₀ + (2 + |u x₀|) / (-deriv u x₀)) := le_max_right _ _
        have h2 : 0 < -deriv u x₀ := by linarith
        have h3 : (2 + |u x₀|) / (-deriv u x₀) * (-deriv u x₀) = 2 + |u x₀| := by
          field_simp
        nlinarith [abs_nonneg (u x₀), h1, h2, h3]
      have := hbd y ((le_max_right N x₀).trans hy₁)
      have := hN y ((le_max_left N x₀).trans hy₁)
      linarith [le_abs_self (u x₀), neg_abs_le (u x₀)]
    · -- `u → −∞` at `−∞`
      have hbd : ∀ y, y ≤ x₀ → deriv u x₀ * (x₀ - y) ≤ u x₀ - u y := fun y hy ↦
        (convex_Iic x₀).mul_sub_le_image_sub_of_le_deriv hu1.continuous.continuousOn
          hu1.differentiableOn (fun z hz ↦ hanti (Set.mem_Iic.1 (interior_subset hz)))
          y hy x₀ self_mem_Iic hy
      obtain ⟨N, hN⟩ := eventually_atBot.1 (hlim.1.eventually (eventually_gt_nhds
        (show (-1 : ℝ) < 0 by norm_num)))
      obtain ⟨y, hy₁, hy₂⟩ : ∃ y, y ≤ min N x₀ ∧ 2 + |u x₀| ≤ deriv u x₀ * (x₀ - y) := by
        refine ⟨min (min N x₀) (x₀ - (2 + |u x₀|) / deriv u x₀), min_le_left _ _, ?_⟩
        have h1 : min (min N x₀) (x₀ - (2 + |u x₀|) / deriv u x₀)
            ≤ x₀ - (2 + |u x₀|) / deriv u x₀ := min_le_right _ _
        have h3 : (2 + |u x₀|) / deriv u x₀ * deriv u x₀ = 2 + |u x₀| := by
          field_simp
        nlinarith [abs_nonneg (u x₀), h1, hpos, h3]
      have := hbd y (hy₁.trans (min_le_right N x₀))
      have := hN y (hy₁.trans (min_le_left N x₀))
      linarith [le_abs_self (u x₀), neg_abs_le (u x₀)]
  -- so `u` is constant, hence `0`, hence `f = 0`
  have hconst : ∀ x, u x = u 0 := fun x ↦ is_const_of_deriv_eq_zero hu1 hderiv x 0
  have hu0 : u 0 = 0 := by
    have h1 : Tendsto u atTop (𝓝 (u 0)) :=
      tendsto_const_nhds.congr fun x ↦ (hconst x).symm
    exact tendsto_nhds_unique h1 hlim.2
  have hf0 : φ 0 = 0 := by
    rw [← hode 0]
    have : deriv u = fun _ ↦ 0 := funext hderiv
    rw [this, deriv_const]
    simp
  rw [φ.one_of_mem_closedBall (by rw [hφin]; exact Metric.mem_closedBall_self zero_le_one)] at hf0
  exact one_ne_zero hf0

/-- The square of a smooth compactly supported function is integrable on `ℝ`. -/
private theorem integrable_sq_of_hasCompactSupport {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (fun x ↦ g x ^ 2) := by
  refine (hg.pow 2).integrable_of_hasCompactSupport (hgc.mono' fun x hx ↦ subset_tsupport g ?_)
  intro h
  rw [Function.mem_support] at hx
  exact hx (by rw [Pi.pow_apply, h]; norm_num)

/-- The `L²(ℝ)` inner product of an element with itself, through an a.e. representative. -/
private theorem inner_self_eq_integral_sq {g : ℝ → ℝ}
    (F : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hF : ⇑F =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] g) : ⟪F, F⟫_ℝ = ∫ x, g x ^ 2 := by
  rw [L2.inner_def]
  change ∫ a in (univ : Set ℝ), ⟪F a, F a⟫_ℝ = _
  rw [Measure.restrict_univ]
  have hF' : ⇑F =ᵐ[volume] g := SobolevIntervalLp.eventuallyEq_restrict_top_iff.1 hF
  refine integral_congr_ae (hF'.mono fun x hx ↦ ?_)
  simp only [RCLike.inner_apply, conj_trivial, hx, sq]

/-- **Remark 24, "the bilinear form `a(u, v) = ∫ u' v'` is not coercive in `H¹(ℝ)`"**: there
is no `c > 0` with `c ‖v‖²_{H¹} ≤ ∫ v'²` for all `v ∈ H¹(ℝ)`. The dilations `v_n(x) = φ(x/n)`
of a bump `φ` have `∫ v_n'² = n⁻¹ ∫ φ'²` while `‖v_n‖²_{H¹} ≥ ‖v_n‖²_{L²} = n ∫ φ² ≥ 2n`. -/
theorem remark_8_24_not_coercive :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ v : SobolevIntervalLp 1 2 ⊤,
      c * ‖v‖ ^ 2 ≤ ∫ x, (SobolevIntervalLp.deriv v 1 x) ^ 2 := by
  rintro ⟨c, hc, hcoer⟩
  obtain ⟨φ, hφin⟩ : ∃ φ : ContDiffBump (0 : ℝ), φ.rIn = 1 := ⟨⟨1, 2, one_pos, one_lt_two⟩, rfl⟩
  have hφc : Continuous φ := φ.continuous
  have hφ'c : Continuous (deriv φ) := (φ.contDiff (n := 1)).continuous_deriv le_rfl
  -- `∫ φ² ≥ 2`, `φ` being `1` on `[-1, 1]`
  have hφ2 : 2 ≤ ∫ x, (φ x) ^ 2 := by
    have hint := integrable_sq_of_hasCompactSupport hφc φ.hasCompactSupport
    have h1 : ∫ x in Icc (-1 : ℝ) 1, (φ x) ^ 2 = 2 := by
      rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ ↦ (1 : ℝ)) fun x hx ↦ by
        rw [φ.one_of_mem_closedBall (by
          rw [hφin, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le]
          exact hx), one_pow]]
      rw [setIntegral_const, Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul]
      norm_num
    rw [← h1]
    exact setIntegral_le_integral hint (Eventually.of_forall fun x ↦ sq_nonneg _)
  -- the dilations `x ↦ φ((n+1)⁻¹ x)`, as test functions on `ℝ`
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℕ → 𝓓((⊤ : Opens ℝ), ℝ), ∀ n, ⇑(ψ n) = fun x ↦ φ (((n : ℝ) + 1)⁻¹ * x) :=
    ⟨fun n ↦ ⟨fun x ↦ φ (((n : ℝ) + 1)⁻¹ * x),
      (φ.contDiff (n := ⊤)).comp (contDiff_const.mul contDiff_id),
      φ.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft₀ ((n : ℝ) + 1)⁻¹ (by positivity)),
      fun _ _ ↦ trivial⟩, fun n ↦ rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℕ → SobolevIntervalLp 1 2 ⊤,
      ∀ n, v n = TestFunction.toSobolevIntervalLp 2 (ψ n) := ⟨_, fun n ↦ rfl⟩
  -- the derivative of the dilation
  have hderiv : ∀ n x, deriv (ψ n) x = ((n : ℝ) + 1)⁻¹ * deriv φ (((n : ℝ) + 1)⁻¹ * x) :=
    fun n x ↦ by rw [hψ]; exact deriv_comp_mul_left _ _ _
  -- the two integrals, by the change of variables `x ↦ (n+1)⁻¹ x`
  have hA : ∀ n, ∫ x, (SobolevIntervalLp.deriv (v n) 1 x) ^ 2
      = ((n : ℝ) + 1)⁻¹ * ∫ y, (deriv φ y) ^ 2 := fun n ↦ by
    have e1 : (fun x ↦ (SobolevIntervalLp.deriv (v n) 1 x) ^ 2) =ᵐ[volume]
        fun x ↦ (((n : ℝ) + 1)⁻¹ * deriv φ (((n : ℝ) + 1)⁻¹ * x)) ^ 2 := by
      have := SobolevIntervalLp.eventuallyEq_restrict_top_iff.1
        (TestFunction.coeFn_deriv_toSobolevIntervalLp_one (p := 2) (ψ n))
      rw [← hv] at this
      filter_upwards [this] with x hx
      rw [hx, hderiv]
    rw [integral_congr_ae e1]
    have e2 : (fun x ↦ (((n : ℝ) + 1)⁻¹ * deriv φ (((n : ℝ) + 1)⁻¹ * x)) ^ 2)
        = fun x ↦ (((n : ℝ) + 1)⁻¹) ^ 2 * (fun y ↦ (deriv φ y) ^ 2) (((n : ℝ) + 1)⁻¹ * x) :=
      funext fun x ↦ by ring
    rw [e2, integral_const_mul, Measure.integral_comp_mul_left (fun y ↦ (deriv φ y) ^ 2),
      inv_inv, abs_of_pos (by positivity), smul_eq_mul]
    field_simp
  have hB : ∀ n, ‖SobolevIntervalLp.deriv (v n) 0‖ ^ 2 = ((n : ℝ) + 1) * ∫ y, (φ y) ^ 2 :=
    fun n ↦ by
    rw [← real_inner_self_eq_norm_sq, inner_self_eq_integral_sq _
      (g := fun x ↦ φ (((n : ℝ) + 1)⁻¹ * x)) (by
        rw [hv, SobolevIntervalLp.deriv_zero, ← hψ]
        exact TestFunction.fn_toSobolevIntervalLp_ae_eq (ψ n))]
    rw [Measure.integral_comp_mul_left (fun y ↦ (φ y) ^ 2), inv_inv, abs_of_pos (by positivity),
      smul_eq_mul]
  -- the contradiction for `n` large
  obtain ⟨M, hM⟩ : ∃ M, M = ∫ y, (deriv φ y) ^ 2 := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, M / (2 * c) < n := exists_nat_gt _
  have h1 := hcoer (v n)
  rw [hA n, ← hM] at h1
  have h2 : ((n : ℝ) + 1) * 2 ≤ ‖v n‖ ^ 2 := by
    calc ((n : ℝ) + 1) * 2 ≤ ((n : ℝ) + 1) * ∫ y, (φ y) ^ 2 := by gcongr
      _ = ‖SobolevIntervalLp.deriv (v n) 0‖ ^ 2 := (hB n).symm
      _ ≤ ‖v n‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (SobolevIntervalLp.norm_deriv_le _ 0) 2
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h3 : M < 2 * c * n := by
    rw [div_lt_iff₀ (by positivity)] at hn
    linarith
  have h4 : c * (((n : ℝ) + 1) * 2) ≤ ((n : ℝ) + 1)⁻¹ * M := by
    calc c * (((n : ℝ) + 1) * 2) ≤ c * ‖v n‖ ^ 2 := by gcongr
      _ ≤ ((n : ℝ) + 1)⁻¹ * M := h1
  have h5 : c * (((n : ℝ) + 1) * 2) * ((n : ℝ) + 1) ≤ M := by
    have := mul_le_mul_of_nonneg_right h4 hn1.le
    have e : ((n : ℝ) + 1)⁻¹ * M * ((n : ℝ) + 1) = M := by field_simp
    rwa [e] at this
  have h6 : 2 * c * n ≤ c * (((n : ℝ) + 1) * 2) * ((n : ℝ) + 1) := by
    have : 0 ≤ c * ((n : ℝ) ^ 2 + n + 1) := mul_nonneg hc.le (by positivity)
    nlinarith
  linarith

/-- **Remark 24.** The problem `−u'' = f` on `ℝ`, `u(x) → 0` as `|x| → ∞`, cannot be attacked by
the preceding technique, because the bilinear form `a(u, v) = ∫ u' v'` is not coercive in
`H¹(ℝ)` (`remark_8_24_not_coercive`); in fact it need not have a solution even if `f` is smooth
with compact support (`remark_8_24_exists_not_solvable`). -/
theorem remark_8_24 :
    (¬ ∃ c : ℝ, 0 < c ∧ ∀ v : SobolevIntervalLp 1 2 ⊤,
      c * ‖v‖ ^ 2 ≤ ∫ x, (SobolevIntervalLp.deriv v 1 x) ^ 2) ∧
    ∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      ¬ ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ (∀ x, -deriv (deriv u) x = f x) ∧
        Tendsto u (cocompact ℝ) (𝓝 0) :=
  ⟨remark_8_24_not_coercive, remark_8_24_exists_not_solvable⟩

/-- **Remark 25, the space.** `H_0^1(0, +∞) = {u ∈ H¹(0, +∞) : u(0) = 0}`: Theorem 8.12 on the
half-line `(0, ∞)`, whose boundary is `{0}`. -/
theorem remark_8_25_space (u : SobolevIntervalLp 1 2 (Opens.Ioi 0)) :
    u ∈ SobolevIntervalLpZero 1 2 (Opens.Ioi 0) ↔ u.rep 0 = 0 := by
  rw [mem_sobolevIntervalLpZero_iff (p := 2) (SobolevIntervalLp.ordConnected_coe_Ioi 0)
    ENNReal.ofNat_ne_top, Opens.coe_Ioi, frontier_Ioi]
  simp

/-- The load `v ↦ ∫_0^∞ f v` on `H_0^1(0, ∞)`, as a continuous linear functional. -/
private def halfLineLoad (f : Lp ℝ 2 (volume.restrict ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ))) :
    SobolevIntervalLpZero 1 2 (Opens.Ioi 0) →L[ℝ] ℝ :=
  (innerSL ℝ f).comp ((SobolevIntervalLp.derivL 1 2 (Opens.Ioi 0) 0).comp
    (SobolevIntervalLpZero 1 2 (Opens.Ioi 0)).subtypeL)

private theorem halfLineLoad_apply
    (f : Lp ℝ 2 (volume.restrict ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ)))
    (v : SobolevIntervalLpZero 1 2 (Opens.Ioi 0)) :
    halfLineLoad f v = ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ),
      f x * (v : SobolevIntervalLp 1 2 (Opens.Ioi 0)).fn x := by
  change ⟪f, SobolevIntervalLp.deriv (v : SobolevIntervalLp 1 2 (Opens.Ioi 0)) 0⟫_ℝ = _
  rw [L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  change ⟪f x, SobolevIntervalLp.deriv (v : SobolevIntervalLp 1 2 (Opens.Ioi 0)) 0 x⟫_ℝ
    = f x * (v : SobolevIntervalLp 1 2 (Opens.Ioi 0)).fn x
  rw [RCLike.inner_apply, conj_trivial, mul_comm]
  rfl

/-- **Remark 25, existence and uniqueness of the weak solution.** The problem
`−u'' + u = f` on `I = (0, +∞)`, `u(0) = 0`, `u(x) → 0` as `x → +∞`, with `f ∈ L²(0, +∞)`, has
exactly one weak solution: one `u ∈ H_0^1(0, ∞)` with `(u, v)_{H¹} = ∫_0^∞ f v` for all
`v ∈ H_0^1(0, ∞)` — Lax–Milgram (the Riesz–Fréchet theorem) for the `H¹` inner product on the
closed subspace `H_0^1(0, ∞)`, "the same method" as in Example 8. -/
theorem remark_8_25_existsUnique
    (f : Lp ℝ 2 (volume.restrict ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ))) :
    ∃! u : SobolevIntervalLpZero 1 2 (Opens.Ioi 0), ∀ v : SobolevIntervalLpZero 1 2 (Opens.Ioi 0),
      ⟪u, v⟫_ℝ = ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ),
        f x * (v : SobolevIntervalLp 1 2 (Opens.Ioi 0)).fn x :=
  ⟨(InnerProductSpace.toDual ℝ (SobolevIntervalLpZero 1 2 (Opens.Ioi 0))).symm (halfLineLoad f),
    fun v ↦ by rw [← halfLineLoad_apply]; exact InnerProductSpace.toDual_symm_apply,
    fun w hw ↦ by
      refine ext_inner_right ℝ fun v ↦ ?_
      rw [hw v, ← halfLineLoad_apply, InnerProductSpace.toDual_symm_apply]⟩

/-- **Remark 25, regularity.** The weak solution `u` of the half-line problem lies in
`H²(0, ∞)`, with `u'' = u − f`: testing the weak equation against `𝓓((0, ∞), ℝ)` gives
`∫ u' φ' = ∫ (f − u) φ`, so `u' ∈ H¹(0, ∞)` with weak derivative `u − f` (Steps C of §8.4). -/
theorem remark_8_25_regularity
    (f : Lp ℝ 2 (volume.restrict ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ)))
    {u : SobolevIntervalLpZero 1 2 (Opens.Ioi 0)}
    (hu : ∀ v : SobolevIntervalLpZero 1 2 (Opens.Ioi 0),
      ⟪u, v⟫_ℝ = ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ),
        f x * (v : SobolevIntervalLp 1 2 (Opens.Ioi 0)).fn x) :
    HasWeakDerivOn (SobolevIntervalLp.deriv (u : SobolevIntervalLp 1 2 (Opens.Ioi 0)) 1)
      (fun x ↦ (u : SobolevIntervalLp 1 2 (Opens.Ioi 0)).fn x - f x) (Opens.Ioi 0) ∧
    MemSobolevIntervalLp (u : SobolevIntervalLp 1 2 (Opens.Ioi 0)).fn 2 2 (Opens.Ioi 0) := by
  obtain ⟨U, hU⟩ : ∃ U : SobolevIntervalLp 1 2 (Opens.Ioi 0), U = u := ⟨_, rfl⟩
  have hweak : HasWeakDerivOn (SobolevIntervalLp.deriv U 1) (fun x ↦ U.fn x - f x)
      (Opens.Ioi 0) := by
    refine hasWeakDerivOn_iff.2 ⟨SobolevIntervalLp.locallyIntegrableOn_deriv U 1,
      ((Lp.memLp (SobolevIntervalLp.deriv U 0)).sub (Lp.memLp f)).locallyIntegrableOn one_le_two,
      fun φ ↦ ?_⟩
    have h := hu ⟨TestFunction.toSobolevIntervalLp 2 φ, TestFunction.toSobolevIntervalLp_mem φ⟩
    rw [Submodule.coe_inner, ← hU, SobolevIntervalLp.inner_eq_integral] at h
    have hφ0 := TestFunction.fn_toSobolevIntervalLp_ae_eq (p := 2) φ
    have hφ1 := TestFunction.coeFn_deriv_toSobolevIntervalLp_one (p := 2) φ
    have e1 : ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ),
        (U.fn x * (TestFunction.toSobolevIntervalLp 2 φ).fn x
          + SobolevIntervalLp.deriv U 1 x
            * SobolevIntervalLp.deriv (TestFunction.toSobolevIntervalLp 2 φ) 1 x)
        = (∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ), U.fn x * φ x)
          + ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ),
            SobolevIntervalLp.deriv U 1 x * deriv φ x := by
      rw [← integral_add]
      · refine integral_congr_ae ?_
        filter_upwards [hφ0, hφ1] with x hx0 hx1
        rw [hx0, hx1]
      · exact (Lp.memLp (SobolevIntervalLp.deriv U 0)).integrable_mul (φ.memLp' 2)
      · exact (Lp.memLp (SobolevIntervalLp.deriv U 1)).integrable_mul (φ.memLp_deriv 2)
    have e2 : ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ),
        f x * (TestFunction.toSobolevIntervalLp 2 φ).fn x
        = ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ), f x * φ x :=
      integral_congr_ae (hφ0.mono fun x hx ↦ by simp only [hx])
    rw [e1, e2] at h
    have e3 : ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ), φ x * (U.fn x - f x)
        = (∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ), U.fn x * φ x)
          - ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ), f x * φ x := by
      rw [← integral_sub]
      · refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        ring
      · exact ((Lp.memLp (SobolevIntervalLp.deriv U 0)).integrable_mul (φ.memLp' 2)).congr
          (Eventually.of_forall fun x ↦ rfl)
      · exact ((Lp.memLp f).integrable_mul (φ.memLp' 2)).congr
          (Eventually.of_forall fun x ↦ rfl)
    rw [e3]
    have e4 : ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ),
          deriv φ x * SobolevIntervalLp.deriv U 1 x
        = ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ),
          SobolevIntervalLp.deriv U 1 x * deriv φ x :=
      integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
    rw [e4]
    linarith
  rw [← hU]
  refine ⟨hweak, memSobolevIntervalLp_succ_iff.2 ⟨Lp.memLp _, SobolevIntervalLp.deriv U 1,
    U.hasWeakDerivOn_fn, memSobolevIntervalLp_one_iff.2 ⟨Lp.memLp _, _, hweak,
      (Lp.memLp (SobolevIntervalLp.deriv U 0)).sub (Lp.memLp f)⟩⟩⟩

/-- **Remark 25, the decay at infinity and the boundary condition.** The weak solution `u` of
the half-line problem satisfies `u(0) = 0` and `u(x) → 0` as `x → +∞` (Corollary 8.9). -/
theorem remark_8_25_boundary (u : SobolevIntervalLpZero 1 2 (Opens.Ioi 0)) :
    (u : SobolevIntervalLp 1 2 (Opens.Ioi 0)).rep 0 = 0 ∧
      Tendsto (u : SobolevIntervalLp 1 2 (Opens.Ioi 0)).rep atTop (𝓝 0) :=
  ⟨(remark_8_25_space _).1 u.2, SobolevIntervalLp.tendsto_rep_atTop
    (SobolevIntervalLp.ordConnected_coe_Ioi 0) ENNReal.ofNat_ne_top
    (by rw [Opens.coe_Ioi]; exact not_bddAbove_Ioi 0) _⟩

/-- **Remark 25.** The same method as in Example 8 applies to the problem `−u'' + u = f` on
`I = (0, +∞)`, `u(0) = 0`, `u(x) → 0` as `x → +∞`, with `f ∈ L²(0, +∞)`: in the space
`H_0^1(0, ∞) = {u ∈ H¹(0, ∞) : u(0) = 0}` (Theorem 8.12) there is exactly one weak solution
(Lax–Milgram), it lies in `H²(0, ∞)`, vanishes at `0` and tends to `0` at `+∞`
(Corollary 8.9). -/
theorem remark_8_25 (f : Lp ℝ 2 (volume.restrict ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ))) :
    (∀ u : SobolevIntervalLp 1 2 (Opens.Ioi 0),
      u ∈ SobolevIntervalLpZero 1 2 (Opens.Ioi 0) ↔ u.rep 0 = 0) ∧
    ∃! u : SobolevIntervalLpZero 1 2 (Opens.Ioi 0),
      (∀ v : SobolevIntervalLpZero 1 2 (Opens.Ioi 0),
        ⟪u, v⟫_ℝ = ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ),
          f x * (v : SobolevIntervalLp 1 2 (Opens.Ioi 0)).fn x) ∧
      MemSobolevIntervalLp (u : SobolevIntervalLp 1 2 (Opens.Ioi 0)).fn 2 2 (Opens.Ioi 0) ∧
      (u : SobolevIntervalLp 1 2 (Opens.Ioi 0)).rep 0 = 0 ∧
      Tendsto (u : SobolevIntervalLp 1 2 (Opens.Ioi 0)).rep atTop (𝓝 0) := by
  obtain ⟨u, hu, huniq⟩ := remark_8_25_existsUnique f
  exact ⟨remark_8_25_space, u, ⟨hu, (remark_8_25_regularity f hu).2, (remark_8_25_boundary u).1,
    (remark_8_25_boundary u).2⟩, fun w hw ↦ huniq w hw.1⟩


end Brezis.Chapter08
