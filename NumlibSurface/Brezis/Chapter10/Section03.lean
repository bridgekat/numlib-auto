import Numlib.Analysis.PDE.Wave
import NumlibSurface.Brezis.Chapter10.Section02

/-!
# Brezis §10.3: The wave equation

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §10.3: the wave equation `∂ₜₜu − Δu = 0` in
`Q = Ω × (0, ∞)`, `u = 0` on `Σ`, `u(·, 0) = u₀`, `∂ₜu(·, 0) = v₀`, solved as the first-order system
(33)–(35) in the phase space `H = H¹₀(Ω) × L²(Ω)` with the scalar product (34): Theorem 10.7
(existence, uniqueness, the energy identity (32)), Remark 6, Remark 7 (the Dirichlet scalar
product on bounded `Ω`, `A` and `−A` maximal monotone, the group of isometries), Remark 8
(d'Alembert's formula and the characteristics), Remark 9 (the Fourier method) and Theorem 10.8
with Remark 10 (regularity and the compatibility conditions). The backbone is
`Numlib/Analysis/PDE/Wave`.

## Conventions

* As in §10.1, a solution is the curve `u : ℝ → L²(Ω)` of the book's unknown `u(x, t)` (not the
  phase-space curve `U = (u, ∂ₜu)`), and the classes of (31) are the Bochner classes of
  `Numlib/Analysis/PDE/Bochner`; the data are `u₀, v₀ ∈ H¹₀(Ω) = hZeroSpace N Ω`, the datum
  `u₀ ∈ H²(Ω) ∩ H¹₀(Ω)` being `fnL u₀ ∈ D(A)` for the operator `A = −Δ` of §10.1
  (`heatOperator_mem_domain_iff`). The phase space is the backbone's `Wave.phaseSpace Ω`
  (`WithLp 2 (H¹₀(Ω) × L²(Ω))`, whose inner product is (34)), and the book's operator (35),
  `A(u, v) = (−v, −Δu)` with `D(A) = (H²(Ω) ∩ H¹₀(Ω)) × H¹₀(Ω)`, is `waveOperator Ω`: the
  backbone's `Wave.operator Ω` (weak domain `D(−Δ) × H¹₀(Ω)`) restricted to the pairs whose first
  component lies in `H²(Ω)`; on a `C²` domain with bounded boundary the two coincide
  (`waveOperator_eq`, Theorem 9.25).
* The book's citation "Remark 7.7" in the proof of Theorem 10.7 means chapter 7's Remark 6 (the
  shift `V = e^{λt} U`), `Brezis.Chapter07.remark_7_6` (erratum recorded in
  `notes/book-errata.md`). The class `u ∈ C([0, ∞); H² ∩ H¹₀)` of (31) is a consequence of
  `U ∈ C¹([0, ∞); H)` and the equation, not a separate output of Theorem 7.4.
* Footnote 10's `|∇u(t)|²_{L²} = ∑ᵢ ∫_Ω |∂ᵢu(x, t)|²` is written, as in §10.1, for the
  `H¹₀`-lift of `u(t)` (`sum_integral_partialDeriv_sq`).
* The standing hypothesis "`Ω` of class `C^∞` with `Γ` bounded" is carried by Theorem 10.7 as
  stated; the energy identity (32), Remark 6, Remark 7 and Remark 9 hold on every open set (or
  every bounded one) and are stated so.
* Remark 8 is stated on `Ω = ⊤ : Opens ℝ¹` (`ℝ¹ = EuclideanSpace ℝ (Fin 1)`), the data
  `u₀ ∈ H²(ℝ)`, `v₀ ∈ H¹(ℝ)` read in `H¹₀(ℝ) = H¹(ℝ)` through the backbone's `Wave.toZeroTopL`,
  and the formula (40) through `Wave.lineEmbed : ℝ → ℝ¹` and the coordinate `x ↦ x 0`
  (`Wave.coeFn_dAlembertL2_dAlembert`).
* Remark 7's clause `A* = −A` (the adjoint for the Dirichlet scalar product) is not restated:
  the backbone does not formalize it. The two-sided solvability and `|U(t)|_H = |U₀|_H` for all
  `t ∈ ℝ` are obtained by time reversal (`Wave.existsUnique_isSolution_backward`), which needs
  neither the boundedness of `Ω` nor the Dirichlet scalar product.
* Theorem 10.8's compatibility conditions `Δ^j u₀ = Δ^j v₀ = 0` on `Γ` for every `j` are read,
  as the display of its proof does, through the domains `D_m` of the Dirichlet Laplacian
  (`Wave.MemLaplacianDomain`: `D_0 = L²`, `D_1 = H¹₀`, `D_{m+2} = {w ∈ D(−Δ) : −Δw ∈ D_m}`) as
  `u₀, v₀ ∈ D_k` for every `k`; the hypothesis `u₀, v₀ ∈ H^k(Ω)` for every `k` is then a
  consequence (`Wave.MemLaplacianDomain.exists_sobolev`, as for Theorem 10.2 (c)), and
  `D(A^k) = D_{k+1} × D_k` with the continuous injection into `H^{k+1} × H^k` is
  `theorem_10_8_domain`, `theorem_10_8_domain_norm`. Remark 10 (necessity) is stated as
  Remark 4 of §10.1 is, for a `C^∞` function on `ℝ^N × ℝ`.

## Main results

* `waveOperator`, `waveOperator_mem_domain_iff`, `waveOperator_apply`,
  `waveOperator_add_id_inner_self_nonneg`, `waveOperator_eq`,
  `waveOperator_add_id_isMaximalMonotone`.
* `IsWaveSolution`, `IsWaveSolution.isSolution`, `isWaveSolution_iff`, `theorem_10_7`,
  `theorem_10_7_energy`, `remark_10_6`.
* `remark_10_7`, `remark_10_7_group`, `remark_10_8`, `remark_10_8_characteristics`,
  `remark_10_9`.
* `theorem_10_8_domain`, `theorem_10_8_domain_norm`, `theorem_10_8`, `remark_10_10`.
-/

open Filter MeasureTheory Metric Set Topology TopologicalSpace Laplacian
open scoped ContDiff Distributions ENNReal NNReal InnerProductSpace

namespace Brezis.Chapter10

open Brezis.Chapter07 Brezis.Chapter09 SobolevMultiIndex

section General

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- The standard basis of `ℝ^N`. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-! ### The operator (35) on the phase space `H¹₀(Ω) × L²(Ω)` -/

variable (Ω) in
/-- **The operator `A` of (35)** on the phase space `H = H¹₀(Ω) × L²(Ω)` with the scalar product
(34), `A(u, v) = (−v, −Δu)`, with `D(A) = (H²(Ω) ∩ H¹₀(Ω)) × H¹₀(Ω)`: the backbone's
`Wave.operator Ω` (whose domain is `D(−Δ) × H¹₀(Ω)` for the weak Dirichlet Laplacian) restricted
to the pairs `(u, v)` whose first component is the function of an element of `H²(Ω)`
(`LinearPMap.domRestrict`); "the boundary condition (28) has been incorporated in the space
`H`". -/
noncomputable def waveOperator : Wave.phaseSpace Ω →ₗ.[ℝ] Wave.phaseSpace Ω :=
  (Wave.operator Ω).domRestrict ((LinearMap.range (fnL ℝ 𝔟 2 2 Ω volume).toLinearMap).comap
    ((SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume).comp (Wave.phaseSpace.fstL Ω)).toLinearMap)

/-- `D(A)` is contained in the weak domain of the backbone's wave operator. -/
theorem waveOperator_domain_le : (waveOperator Ω).domain ≤ (Wave.operator Ω).domain :=
  inf_le_right

/-- **`D(A) = (H²(Ω) ∩ H¹₀(Ω)) × H¹₀(Ω)`**: `(u, v) ∈ D(A)` iff `u ∈ H¹₀(Ω)` is the function of
an element of `H²(Ω)` and `v ∈ L²(Ω)` is the function of an element of `H¹₀(Ω)`. -/
theorem waveOperator_mem_domain_iff {U : Wave.phaseSpace Ω} :
    U ∈ (waveOperator Ω).domain ↔
      (∃ w : sobolevSpaceHigher N 2 2 Ω,
        fnL ℝ 𝔟 2 2 Ω volume w = SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume U.fst) ∧
      ∃ z : hZeroSpace N Ω, SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume z = U.snd := by
  -- both memberships unfold to the stated conjunctions (`Submodule.mem_inf`, `mem_comap`,
  -- `LinearMap.mem_range` and `Wave.mem_operatorDomain_iff` are all `Iff.rfl`)
  exact ⟨fun h ↦ ⟨h.1, h.2.2⟩,
    fun h ↦ ⟨h.1, mem_dirichletLaplacianDomain_of_exists_sobolev_two h.1 ⟨U.fst, U.fst.2, rfl⟩,
      h.2⟩⟩

/-- `A U` is the value of the backbone's wave operator at `U`, for `U ∈ D(A)`. -/
theorem waveOperator_apply_eq (U : (waveOperator Ω).domain) :
    waveOperator Ω U = Wave.operator Ω ⟨U, waveOperator_domain_le U.2⟩ :=
  rfl

/-- **`A(u, v) = (−v, −Δu)`**: for `U = (u, v) ∈ D(A)`, the first component of `A U` is `−v`
(read in `L²(Ω)`: its function is `−v`) and the second is `−Δu = −∑ᵢ ∂ᵢᵢw` for the `H²`-element
`w` with function `u`. -/
theorem waveOperator_apply (U : (waveOperator Ω).domain) (w : sobolevSpaceHigher N 2 2 Ω)
    (hw : fnL ℝ 𝔟 2 2 Ω volume w
      = SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume (U : Wave.phaseSpace Ω).fst) :
    SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume (waveOperator Ω U).fst
        = -(U : Wave.phaseSpace Ω).snd ∧
      (waveOperator Ω U).snd
        = -∑ i, weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i)) := by
  refine ⟨(congrArg (fun V ↦ SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume V.fst)
    (waveOperator_apply_eq U)).trans (Wave.fnL_operator_apply_fst _), ?_⟩
  -- the ascription fixes `Ω` before the anonymous constructor is elaborated (a minute otherwise)
  exact (congrArg Wave.phaseSpace.snd (waveOperator_apply_eq U)).trans
    ((Wave.operator_apply_snd
      (⟨U, waveOperator_domain_le U.2⟩ : (Wave.operator Ω).domain)).trans
      ((dirichletLaplacian_apply_eq_neg_sobolevLaplacianL w _ hw).trans
        (congrArg Neg.neg (sobolevLaplacianL_apply w))))

/-- **Claim (i) of the proof of Theorem 10.7: `A + I` is monotone** —
`(AU, U)_H + |U|²_H = −∫ uv + ∫ u² + ∫ v² + ∫ |∇u|² ≥ 0` for `U = (u, v) ∈ D(A)`; on every open
set (the backbone's `Wave.operator_add_id_inner_self_nonneg`). -/
theorem waveOperator_add_id_inner_self_nonneg (U : (waveOperator Ω).domain) :
    0 ≤ ⟪waveOperator Ω U, (U : Wave.phaseSpace Ω)⟫_ℝ + ‖(U : Wave.phaseSpace Ω)‖ ^ 2 := by
  have h := Wave.operator_add_id_inner_self_nonneg
    (⟨U, waveOperator_domain_le U.2⟩ : (Wave.operator Ω).domain)
  exact h

/-! ### The problem (27)–(30) in the class (31) -/

variable (Ω) in
/-- **The problem (27), (28), (29), (30) in the class (31) of Theorem 10.7**, for data
`u₀, v₀ ∈ H¹₀(Ω)`: `u : ℝ → L²(Ω)` (the book's `u(x, t)`, read as the curve `t ↦ u(·, t)`) is a
solution if `u ∈ C([0, ∞); H²(Ω) ∩ H¹₀(Ω))` — `u(t) ∈ D(A) = H² ∩ H¹₀` for `t ≥ 0`, which is the
boundary condition (28), and `u` lifts continuously to `H²(Ω)` —, `u ∈ C¹([0, ∞); H¹₀(Ω))`,
`u ∈ C²([0, ∞); L²(Ω))`, `∂ₜₜu = Δu = −A u` in `L²(Ω)` on `[0, ∞)` (27), `u(0) = u₀` (29) and
`∂ₜu(0) = v₀` (30), the derivatives at `t = 0` being one-sided. -/
structure IsWaveSolution (u₀ v₀ : hZeroSpace N Ω) (u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) :
    Prop where
  /-- `u ∈ C([0, ∞); H²(Ω))`. -/
  contDiffOnThrough_two : Bochner.ContDiffOnThrough (fnL ℝ 𝔟 2 2 Ω volume) 0 u (Ici 0)
  /-- `u(t) ∈ H²(Ω) ∩ H¹₀(Ω)` for `t ≥ 0`: the boundary condition (28). -/
  mem_domain : ∀ t, 0 ≤ t → u t ∈ (heatOperator Ω).domain
  /-- `u ∈ C¹([0, ∞); H¹₀(Ω))`. -/
  contDiffOnThrough_one :
    Bochner.ContDiffOnThrough (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume) 1 u (Ici 0)
  /-- `u ∈ C²([0, ∞); L²(Ω))`. -/
  contDiffOn : ContDiffOn ℝ 2 u (Ici 0)
  /-- The wave equation (27): `∂ₜₜu(t) = Δu(t) = −A u(t)` for `t ≥ 0`. -/
  eqn : ∀ t (ht : 0 ≤ t),
    iteratedDerivWithin 2 u (Ici 0) t = -(heatOperator Ω ⟨u t, mem_domain t ht⟩)
  /-- The initial condition (29): `u(0) = u₀`. -/
  apply_zero : u 0 = SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume u₀
  /-- The initial condition (30): `∂ₜu(0) = v₀`. -/
  derivWithin_zero : derivWithin u (Ici 0) 0 = SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀

variable {u₀ v₀ : hZeroSpace N Ω}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- **A solution in the class (31) is a solution of the backbone's weak class** `Wave.IsSolution`,
on every open set: `D(A) ⊆ D(−Δ)`, and the clause `u ∈ C([0, ∞); D(−Δ))` follows from
`u ∈ C²([0, ∞); L²)` and the equation, `−Δu = −∂ₜₜu`. -/
theorem IsWaveSolution.isSolution (h : IsWaveSolution Ω u₀ v₀ u) :
    Wave.IsSolution Ω u₀ (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀) u where
  contDiffOn := h.contDiffOn
  contDiffOnThrough := h.contDiffOnThrough_one
  mem_domain t ht := heatOperator_domain_le (h.mem_domain t ht)
  contDiffOnPowDomain := by
    rw [LinearPMap.contDiffOnPowDomain_iff dirichletLaplacian_isClosed]
    refine ⟨![u, fun t ↦ -iteratedDerivWithin 2 u (Ici 0) t], fun t _ ↦ rfl, ?_, ?_⟩
    · rw [Fin.forall_fin_two]
      exact ⟨h.contDiffOn.of_le (by simp), contDiffOn_zero.2
        (h.contDiffOn.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Ici 0)).neg⟩
    · intro t ht i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      refine ⟨heatOperator_domain_le (h.mem_domain t ht), ?_⟩
      change dirichletLaplacian Ω ⟨u t, heatOperator_domain_le (h.mem_domain t ht)⟩
        = -iteratedDerivWithin 2 u (Ici 0) t
      rw [h.eqn t ht, neg_neg]
      exact (heatOperator_apply_eq ⟨u t, h.mem_domain t ht⟩).symm
  eqn t ht := (h.eqn t ht).trans (congrArg Neg.neg (heatOperator_apply_eq ⟨u t, h.mem_domain t ht⟩))
  apply_zero := h.apply_zero
  derivWithin_zero := h.derivWithin_zero

/-- The gradient norm of `u(t)`, read on any `H¹₀`-lift, is `(−Δu(t), u(t))_{L²}`. -/
theorem IsWaveSolution.inner_apply_self_eq (h : IsWaveSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t)
    {w : hSpace N Ω} (hw : w ∈ hZeroSpace N Ω) (hwt : fnL ℝ 𝔟 1 2 Ω volume w = u t) :
    ⟪dirichletLaplacian Ω ⟨u t, h.isSolution.mem_domain t ht⟩, u t⟫_ℝ
      = ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv w i x ^ 2 :=
  (dirichletLaplacian_inner_self_eq_dirichletForm _ hw hwt).trans
    (sum_integral_partialDeriv_sq w).symm

/-! ### Theorem 10.7, the energy identity (32), and Remark 6 -/

/-- **Theorem 10.7, the energy identity (32)**: for a solution `u` of (27)–(30) and every
`t ≥ 0`, `|∂ₜu(t)|²_{L²} + |∇u(t)|²_{L²} = |v₀|²_{L²} + |∇u₀|²_{L²}`, with
`|∇u(t)|²_{L²} = ∑ᵢ ∫_Ω |∂ᵢu(x, t)|²` read on any `H¹₀`-lift `w` of `u(t)` (footnote 10).
"Multiply (27) by `∂ₜu` and integrate on `Ω`": `∫ ∂ₜₜu ∂ₜu = ½ ∂ₜ ∫ |∂ₜu|²` and
`∫ (−Δu) ∂ₜu = ½ ∂ₜ ∫ |∇u|²`; the backbone's `Wave.IsSolution.energy_dirichletForm`, on every
open set. -/
theorem theorem_10_7_energy (hu : IsWaveSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t)
    {w : hSpace N Ω} (hw : w ∈ hZeroSpace N Ω) (hwt : fnL ℝ 𝔟 1 2 Ω volume w = u t) :
    ‖derivWithin u (Ici 0) t‖ ^ 2 + ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv w i x ^ 2
      = ‖SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀‖ ^ 2
        + ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv (u₀ : hSpace N Ω) i x ^ 2 := by
  have e := hu.isSolution.energy ht
  have e1 := hu.inner_apply_self_eq ht hw hwt
  have e2 : ⟪dirichletLaplacian Ω ⟨SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume u₀,
        hu.isSolution.memOperatorDomain_mk.1⟩, SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume u₀⟫_ℝ
      = ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv (u₀ : hSpace N Ω) i x ^ 2 :=
    (dirichletLaplacian_inner_self_eq_dirichletForm _ u₀.2 rfl).trans
      (sum_integral_partialDeriv_sq _).symm
  exact (congrArg (‖derivWithin u (Ici 0) t‖ ^ 2 + ·) e1).symm.trans
    (e.trans (congrArg (‖SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀‖ ^ 2 + ·) e2))

/-- **Remark 6.** Equation (32) is a conservation law: the energy
`E(t) = |∂ₜu(t)|²_{L²} + |∇u(t)|²_{L²}` of the system is invariant in time — for any function
`E` with `E(t) = ‖∂ₜu(t)‖² + ∑ᵢ ∫_Ω |∂ᵢu(x, t)|²` (on the `H¹₀`-lift of `u(t)`) for `t ≥ 0`,
`E(t) = E(0)` for every `t ≥ 0`. -/
theorem remark_10_6 (hu : IsWaveSolution Ω u₀ v₀ u) {E : ℝ → ℝ}
    (hE : ∀ t, 0 ≤ t → ∃ w : hSpace N Ω, w ∈ hZeroSpace N Ω ∧ fnL ℝ 𝔟 1 2 Ω volume w = u t ∧
      E t = ‖derivWithin u (Ici 0) t‖ ^ 2 + ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv w i x ^ 2) :
    ∀ t, 0 ≤ t → E t = E 0 := by
  intro t ht
  obtain ⟨w, hw, hwt, hEt⟩ := hE t ht
  obtain ⟨w₀, hw₀, hw₀t, hE0⟩ := hE 0 le_rfl
  rw [hEt, hE0, theorem_10_7_energy hu ht hw hwt, theorem_10_7_energy hu le_rfl hw₀ hw₀t]

/-! ### Remark 8: d'Alembert's formula, the characteristics -/

/-- **Remark 8, the propagation of singularities.** On `Ω = ℝ` with `v₀ = 0`, the solution (41),
`u(x, t) = ½ (u₀(x + t) + u₀(x − t))` (the backbone's `Wave.dAlembert u₀ 0`), is not more regular
than `u₀`; precisely, if `u₀ ∈ C^∞(ℝ ∖ {x₀})` then `u(x, t)` is `C^∞` on `ℝ × ℝ` except on the
characteristics `x + t = x₀` and `x − t = x₀` through `(x₀, 0)`: singularities propagate along
the characteristics. The backbone's `Wave.dAlembert_contDiffOn_off_characteristics`. -/
theorem remark_10_8_characteristics {u₀ : ℝ → ℝ} {x₀ : ℝ} (hu₀ : ContDiffOn ℝ ∞ u₀ {x₀}ᶜ) :
    (∀ t x, Wave.dAlembert u₀ 0 t x = (1 / 2) * (u₀ (x + t) + u₀ (x - t))) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ Wave.dAlembert u₀ 0 p.2 p.1)
        {p : ℝ × ℝ | p.1 + p.2 ≠ x₀ ∧ p.1 - p.2 ≠ x₀} :=
  ⟨fun t x ↦ Wave.dAlembert_zero_apply u₀ t x, Wave.dAlembert_contDiffOn_off_characteristics hu₀⟩

end General

section Regular

variable {d : ℕ}

/-- The book's `ℝ^N`, with `N = d + 1`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

/-- The standard basis of `ℝ^N`. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin (d + 1)) ℝ)

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-! ### The operator on a regular domain, and Theorem 10.7 -/

/-- **`A` is the backbone's wave operator** on a domain of class `C²` with `Γ` bounded: the weak
domain `D(−Δ) × H¹₀(Ω)` is `(H²(Ω) ∩ H¹₀(Ω)) × H¹₀(Ω)` by Theorem 9.25
(`heatOperator_eq_dirichletLaplacian`). -/
theorem waveOperator_eq (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    waveOperator Ω = Wave.operator Ω := by
  have hdom := (dirichletLaplacianDomain_eq_of_isContDiffChartDomain hΩ hΓ).1
  refine LinearPMap.eq_of_le_of_domain_eq LinearPMap.domRestrict_le
    (le_antisymm inf_le_right (le_inf (fun U hU ↦ ?_) le_rfl))
  -- `U ∈ D(−Δ) × H¹₀` has an `H²` first component by Theorem 9.25
  exact ((hdom _).1 (Wave.memOperatorDomain_of_mem hU).1).1

/-- **The claim of the proof of Theorem 10.7: `A + I` is maximal monotone in `H`**, on a `C²`
domain with `Γ` bounded — (i) `(AU, U)_H + |U|²_H ≥ 0` (`waveOperator_add_id_inner_self_nonneg`),
(ii) `A + 2I` is onto: given `F = (f, g)`, solve `−Δu + 4u = 2f + g` (Theorem 9.25; on the weak
domain, the Riesz representation on `H¹₀`) and set `v = 2u − f`. The backbone's
`Wave.operator_add_id_isMaximalMonotone` through `waveOperator_eq`. -/
theorem waveOperator_add_id_isMaximalMonotone (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    Brezis.Chapter07.IsMaximalMonotone
      ((LinearMap.id : Wave.phaseSpace Ω →ₗ[ℝ] Wave.phaseSpace Ω) +ᵥ waveOperator Ω) := by
  rw [waveOperator_eq hΩ hΓ, isMaximalMonotone_iff]
  exact Wave.operator_add_id_isMaximalMonotone

variable {u₀ v₀ : hZeroSpace (d + 1) Ω}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- **The class (31) is the backbone's weak class** on a `C²` domain with `Γ` bounded:
`IsWaveSolution Ω u₀ v₀ u ↔ Wave.IsSolution Ω u₀ (fnL v₀) u`. The forward direction holds on
every open set (`IsWaveSolution.isSolution`); conversely a weak solution has `u(t) ∈ H² ∩ H¹₀`
and lifts continuously to `H²(Ω)` by the graph-norm estimate of Theorem 9.25. -/
theorem isWaveSolution_iff (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    IsWaveSolution Ω u₀ v₀ u
      ↔ Wave.IsSolution Ω u₀ (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀) u := by
  refine ⟨fun h ↦ h.isSolution, fun h ↦ ?_⟩
  have hdom := (dirichletLaplacianDomain_eq_of_isContDiffChartDomain hΩ hΓ).1
  have hmem : ∀ t, 0 ≤ t → u t ∈ (heatOperator Ω).domain := fun t ht ↦
    heatOperator_mem_domain_iff.2 ((hdom _).1 (h.mem_domain t ht))
  have hΩ' : IsContDiffChartDomain (2 * 1) (Ω : Set 𝔼) := hΩ.of_le (by norm_num)
  exact
    { contDiffOnThrough_two := Bochner.ContDiffOnThrough.of_contDiffOnPowDomain
        h.contDiffOnPowDomain (dirichletLaplacian.powDomainToSobolevL hΩ' hΓ) _
        (fnL_powDomainToSobolevL hΩ' hΓ)
      mem_domain := hmem
      contDiffOnThrough_one := h.contDiffOnThrough
      contDiffOn := h.contDiffOn
      eqn := fun t ht ↦ (h.eqn t ht).trans
        (congrArg Neg.neg (heatOperator_apply_eq ⟨u t, hmem t ht⟩).symm)
      apply_zero := h.apply_zero
      derivWithin_zero := h.derivWithin_zero }

/-- **Theorem 10.7 (existence and uniqueness).** Let `Ω` be of class `C^∞` with `Γ` bounded,
`u₀ ∈ H²(Ω) ∩ H¹₀(Ω)` and `v₀ ∈ H¹₀(Ω)`. Then there exists a unique solution `u` of (27), (28),
(29), (30) in the class (31),
`u ∈ C([0, ∞); H²(Ω) ∩ H¹₀(Ω)) ∩ C¹([0, ∞); H¹₀(Ω)) ∩ C²([0, ∞); L²(Ω))` — unique on `[0, ∞)`,
the class not constraining negative times. The book's proof: `A + I` is maximal monotone in
`H = H¹₀(Ω) × L²(Ω)` (`waveOperator_add_id_isMaximalMonotone`), Theorem 7.4 with chapter 7's
Remark 6 (the shift `e^{−t}`) gives `U ∈ C¹([0, ∞); H) ∩ C([0, ∞); D(A))` solving (38) with
`U(0) = (u₀, v₀) ∈ D(A)`, and (31) is read off (39). The backbone's
`Wave.existsUnique_isSolution` (on every open set, for the weak class) through
`isWaveSolution_iff`; the energy identity (32) is `theorem_10_7_energy`. -/
theorem theorem_10_7 (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (u₀ v₀ : hZeroSpace (d + 1) Ω)
    (hu₀ : SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume u₀ ∈ (heatOperator Ω).domain) :
    ∃ u, IsWaveSolution Ω u₀ v₀ u ∧ ∀ v, IsWaveSolution Ω u₀ v₀ v → EqOn v u (Ici 0) := by
  have hΩ2 : IsOfClassC 2 (Ω : Set 𝔼) := hΩ.of_le le_top
  obtain ⟨u, hu, huniq⟩ :=
    Wave.existsUnique_isSolution (heatOperator_domain_le hu₀) (v₀ := _) ⟨v₀, rfl⟩
  exact ⟨u, (isWaveSolution_iff hΩ2 hΓ).2 hu, fun v hv ↦ huniq v hv.isSolution⟩

/-! ### Remark 7: the Dirichlet scalar product, the group of isometries -/

/-- **Remark 7 (i)–(ii), for bounded `Ω`.** With the scalar product `∫_Ω ∇u₁ · ∇u₂` on `H¹₀(Ω)`
(Corollary 9.19) and `(U₁, U₂) = ∫_Ω ∇u₁ · ∇u₂ + ∫_Ω v₁ v₂` on `H = H¹₀(Ω) × L²(Ω)` — the
backbone's `Wave.dirichletPhaseSpace Ω hb`, whose scalar product is this (first clause) — the
operator `A(u, v) = (−v, −Δu)` (`Wave.operator' Ω hb`, whose domain is
`D(A) = (H²(Ω) ∩ H¹₀(Ω)) × H¹₀(Ω)` on a `C²` domain with `Γ` bounded, second clause) satisfies
`(AU, U) = −∫_Ω ∇v · ∇u + ∫_Ω (−Δu) v = 0` for all `U = (u, v) ∈ D(A)`, and (i) `A` and `−A` are
maximal monotone. The clause (ii) `A* = −A` is not restated (the backbone does not formalize the
adjoint for this scalar product). -/
theorem remark_10_7 (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    (∀ U V : Wave.dirichletPhaseSpace Ω hb, ⟪U, V⟫_ℝ
      = (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv (U.fst : hSpace (d + 1) Ω) i x
          * partialDeriv (V.fst : hSpace (d + 1) Ω) i x)
        + ∫ x in (Ω : Set 𝔼), U.snd x * V.snd x) ∧
    (∀ U : Wave.dirichletPhaseSpace Ω hb, U ∈ (Wave.operator' Ω hb).domain ↔
      (∃ w : sobolevSpaceHigher (d + 1) 2 2 Ω,
        fnL ℝ 𝔟 2 2 Ω volume w = SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume U.fst) ∧
      ∃ z : hZeroSpace (d + 1) Ω, SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume z = U.snd) ∧
    (∀ U : (Wave.operator' Ω hb).domain,
      ⟪Wave.operator' Ω hb U, (U : Wave.dirichletPhaseSpace Ω hb)⟫_ℝ = 0) ∧
    Brezis.Chapter07.IsMaximalMonotone (Wave.operator' Ω hb) ∧
    Brezis.Chapter07.IsMaximalMonotone (-Wave.operator' Ω hb) := by
  have hdom := (dirichletLaplacianDomain_eq_of_isContDiffChartDomain hΩ hΓ).1
  refine ⟨fun U V ↦ ?_, fun U ↦ ?_, Wave.operator'_inner_self_eq_zero,
    (isMaximalMonotone_iff _).2 Wave.operator'_isMaximalMonotone,
    (isMaximalMonotone_iff _).2 Wave.neg_operator'_isMaximalMonotone⟩
  · rw [Wave.dirichletPhaseSpace.inner_def, Elliptic.dirichletForm_apply,
      MeasureTheory.L2.inner_eq_integral_mul]
    rfl
  · exact (Wave.mem_operator'_domain_iff.trans Wave.memOperatorDomain'_iff).trans
      ⟨fun h ↦ ⟨((hdom _).1 h.1).1, h.2⟩, fun h ↦
        ⟨mem_dirichletLaplacianDomain_of_exists_sobolev_two h.1 ⟨U.fst, U.fst.2, rfl⟩, h.2⟩⟩

/-- **Remark 7, the group of isometries.** The problem `dU/dt + AU = 0` may also be solved on
`(−∞, 0]` ("just change `t` into `−t`", footnote 12: time is reversible for the wave equation):
for `Ω` of class `C^∞` with `Γ` bounded, `u₀ ∈ H² ∩ H¹₀` and `v₀ ∈ H¹₀`, there is a unique
`u : ℝ → L²(Ω)` which solves (27)–(30) on `[0, ∞)` and whose reflection `t ↦ u(−t)` solves
(27)–(30) with the data `(u₀, −v₀)` on `[0, ∞)`; and for such a `u` the relation (32) holds for
all `t ∈ ℝ`, `|U(t)|_H = |U₀|_H` in the energy norm: `|∂ₜu(t)|² + |∇u(t)|² = |v₀|² + |∇u₀|²`, the
time derivative at `t ≤ 0` being that of the reflected solution. The backbone's
`Wave.existsUnique_isSolution_backward` and `Wave.IsSolution.energy_neg`, which need neither the
boundedness of `Ω` nor the Dirichlet scalar product. -/
theorem remark_10_7_group (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (u₀ v₀ : hZeroSpace (d + 1) Ω)
    (hu₀ : SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume u₀ ∈ (heatOperator Ω).domain) :
    (∃! u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)),
      IsWaveSolution Ω u₀ v₀ u ∧ IsWaveSolution Ω u₀ (-v₀) fun t ↦ u (-t)) ∧
    ∀ u, IsWaveSolution Ω u₀ v₀ u → IsWaveSolution Ω u₀ (-v₀) (fun t ↦ u (-t)) →
      ∀ t (w : hSpace (d + 1) Ω), w ∈ hZeroSpace (d + 1) Ω → fnL ℝ 𝔟 1 2 Ω volume w = u t →
        (0 ≤ t → ‖derivWithin u (Ici 0) t‖ ^ 2
            + ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv w i x ^ 2
          = ‖SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀‖ ^ 2
            + ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv (u₀ : hSpace (d + 1) Ω) i x ^ 2) ∧
        (t ≤ 0 → ‖derivWithin (fun s ↦ u (-s)) (Ici 0) (-t)‖ ^ 2
            + ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv w i x ^ 2
          = ‖SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀‖ ^ 2
            + ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv (u₀ : hSpace (d + 1) Ω) i x ^ 2) := by
  have hΩ2 : IsOfClassC 2 (Ω : Set 𝔼) := hΩ.of_le le_top
  have hneg : SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume (-v₀)
      = -SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀ := _root_.map_neg _ _
  -- the reflected class, with the datum `−v₀` read in `L²(Ω)`
  have hrefl : ∀ u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)),
      IsWaveSolution Ω u₀ (-v₀) (fun t ↦ u (-t)) →
      Wave.IsSolution Ω u₀ (-(SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀)) (fun t ↦ u (-t)) :=
    fun u hu' ↦ Eq.mp (congrArg (fun z ↦ Wave.IsSolution Ω u₀ z (fun t ↦ u (-t))) hneg)
      hu'.isSolution
  have hrefl' : ∀ u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)),
      Wave.IsSolution Ω u₀ (-(SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀))
      (fun t ↦ u (-t)) → IsWaveSolution Ω u₀ (-v₀) (fun t ↦ u (-t)) :=
    fun u h ↦ (isWaveSolution_iff hΩ2 hΓ).2
      (Eq.mp (congrArg (fun z ↦ Wave.IsSolution Ω u₀ z (fun t ↦ u (-t))) hneg.symm) h)
  refine ⟨?_, fun u hu hu' t w hw hwt ↦ ⟨fun ht ↦ theorem_10_7_energy hu ht hw hwt, fun ht ↦ ?_⟩⟩
  · obtain ⟨U, ⟨hU1, hU2⟩, huniq⟩ := Wave.existsUnique_isSolution_backward
      (heatOperator_domain_le hu₀) (v₀ := _) ⟨v₀, rfl⟩
    exact ⟨U, ⟨(isWaveSolution_iff hΩ2 hΓ).2 hU1, hrefl' U hU2⟩,
      fun v ⟨hv1, hv2⟩ ↦ huniq v ⟨hv1.isSolution, hrefl v hv2⟩⟩
  · have h' := hrefl u hu'
    have e := h'.energy_neg ht
    have hmem : u t ∈ (dirichletLaplacian Ω).domain :=
      neg_neg t ▸ h'.mem_domain (-t) (neg_nonneg.2 ht)
    have e1 : ⟪dirichletLaplacian Ω ⟨u t, hmem⟩, u t⟫_ℝ
        = ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv w i x ^ 2 :=
      (dirichletLaplacian_inner_self_eq_dirichletForm _ hw hwt).trans
        (sum_integral_partialDeriv_sq w).symm
    have e2 : ⟪dirichletLaplacian Ω ⟨SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume u₀,
          h'.memOperatorDomain_mk.1⟩, SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume u₀⟫_ℝ
        = ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv (u₀ : hSpace (d + 1) Ω) i x ^ 2 :=
      (dirichletLaplacian_inner_self_eq_dirichletForm _ u₀.2 rfl).trans
        (sum_integral_partialDeriv_sq _).symm
    exact (congrArg (‖derivWithin (fun s ↦ u (-s)) (Ici 0) (-t)‖ ^ 2 + ·) e1).symm.trans
      (e.trans (congrArg (‖SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀‖ ^ 2 + ·) e2))

/-! ### Remark 9: the Fourier method -/

/-- **Remark 9, the Fourier method for the wave equation.** For a bounded (nonempty) `Ω`, let
`(eₙ)`, `(λₙ)` be the Dirichlet eigenbasis of `−Δ` of Theorem 9.31 (`Elliptic.dirichletEigenbasis`,
`Elliptic.dirichletEigenvalue`, `λₙ > 0`), and let `u` be a solution of (27)–(30). Then the
coefficients `aₙ(t) = (u(t), eₙ)_{L²}` of `u(t) = ∑ₙ aₙ(t) eₙ` satisfy `aₙ'' + λₙ aₙ = 0` on
`[0, ∞)` — `aₙ' = (∂ₜu, eₙ)` and `(aₙ')' = −λₙ aₙ` —, so that (42):
`aₙ(t) = aₙ(0) cos(√λₙ t) + (aₙ'(0)/√λₙ) sin(√λₙ t)` with `aₙ(0) = ∫_Ω u₀ eₙ`,
`aₙ'(0) = ∫_Ω v₀ eₙ` the components of the data, and `u(t) = ∑ₙ aₙ(t) eₙ` in `L²(Ω)` for every
`t ≥ 0`. The backbone's `Wave.IsSolution.hasDerivWithinAt_inner_eigenbasis`,
`hasDerivWithinAt_inner_derivWithin_eigenbasis`, `inner_eigenfunction` and
`hasSum_eigenfunction`; no regularity of `Ω` is needed. -/
theorem remark_10_9 (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hne : (Ω : Set 𝔼).Nonempty)
    (hu : IsWaveSolution Ω u₀ v₀ u) :
    (∀ n, ∀ t, 0 ≤ t →
      HasDerivWithinAt (fun t ↦ ⟪u t, Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ)
        ⟪derivWithin u (Ici 0) t, Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ (Ici 0) t ∧
      HasDerivWithinAt
        (fun t ↦ ⟪derivWithin u (Ici 0) t, Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ)
        (-(Elliptic.dirichletEigenvalue Ω hb n
          * ⟪u t, Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ)) (Ici 0) t) ∧
    (∀ n, ∀ t, 0 ≤ t → ⟪u t, Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ
      = (∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn (u₀ : hSpace (d + 1) Ω) x
          * Elliptic.dirichletEigenbasis Ω hb hne n x)
          * Real.cos (√(Elliptic.dirichletEigenvalue Ω hb n) * t)
        + (∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn (v₀ : hSpace (d + 1) Ω) x
          * Elliptic.dirichletEigenbasis Ω hb hne n x) / √(Elliptic.dirichletEigenvalue Ω hb n)
          * Real.sin (√(Elliptic.dirichletEigenvalue Ω hb n) * t)) ∧
    ∀ t, 0 ≤ t → HasSum (fun n ↦ ⟪u t, Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ
      • Elliptic.dirichletEigenbasis Ω hb hne n) (u t) := by
  have h := hu.isSolution
  refine ⟨fun n t ht ↦ ⟨h.hasDerivWithinAt_inner_eigenbasis hb hne n ht,
    (h.hasDerivWithinAt_inner_derivWithin_eigenbasis hb hne n ht).congr_deriv (neg_mul _ _)⟩,
    fun n t ht ↦ ?_, fun t ht ↦ ?_⟩
  · have h1 : ⟪SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume u₀,
          Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ
        = ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn (u₀ : hSpace (d + 1) Ω) x
          * Elliptic.dirichletEigenbasis Ω hb hne n x :=
      MeasureTheory.L2.inner_eq_integral_mul _ _
    have h2 : ⟪SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀,
          Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ
        = ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn (v₀ : hSpace (d + 1) Ω) x
          * Elliptic.dirichletEigenbasis Ω hb hne n x :=
      MeasureTheory.L2.inner_eq_integral_mul _ _
    exact (h.inner_eigenfunction hb hne n ht).trans (congrArg₂ (· + ·)
      (congrArg (· * Real.cos (√(Elliptic.dirichletEigenvalue Ω hb n) * t)) h1)
      (congrArg (fun z ↦ z / √(Elliptic.dirichletEigenvalue Ω hb n)
        * Real.sin (√(Elliptic.dirichletEigenvalue Ω hb n) * t)) h2))
  · have := (Elliptic.dirichletEigenbasis Ω hb hne).hasSum_repr (u t)
    refine this.congr_fun fun n ↦ ?_
    rw [HilbertBasis.repr_apply_apply, real_inner_comm]

/-! ### Theorem 10.8: regularity -/

/-- **The display in the proof of Theorem 10.8.** For `Ω` of class `C^∞` with `Γ` bounded and
every `k`, `D(A^k) = {(u, v) : u ∈ H^{k+1}(Ω), Δ^j u = 0 on Γ for 0 ≤ j ≤ [k/2];
v ∈ H^k(Ω), Δ^j v = 0 on Γ for 0 ≤ j ≤ [(k+1)/2] − 1}` ("easy to see, by induction on `k`"),
read with the backbone's domains `D_m` of the Dirichlet Laplacian (`Wave.MemLaplacianDomain`:
`D_0 = L²(Ω)`, `D_1 = H¹₀(Ω)`, `D_{m+2} = {w ∈ D(−Δ) : −Δw ∈ D_m}` — the book's "`w ∈ H^m(Ω)`,
`Δ^j w = 0` on `Γ` for `2j < m`", with "`= 0` on `Γ`" as membership of `H¹₀(Ω)` and each
iterate in `D(−Δ) = H² ∩ H¹₀`):
`(u, v) ∈ D(A^k)` (chapter 7's `domainPow`) iff `u ∈ D_{k+1}` and `v ∈ D_k`
(`Wave.mem_operator_powGraph_iff`, on every open set), and in particular
`D(A^k) ⊆ H^{k+1}(Ω) × H^k(Ω)`: `u` and `v` are the functions of elements of `H^{k+1}(Ω)` and
`H^k(Ω)` (`Wave.MemLaplacianDomain.exists_sobolev`, Theorem 9.25 at every order). The book's `A`
is the backbone's `Wave.operator Ω` on a `C²` domain (`waveOperator_eq`); the continuity of the
injection is `theorem_10_8_domain_norm`. -/
theorem theorem_10_8_domain (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (k : ℕ) :
    (∀ U : Wave.phaseSpace Ω, U ∈ domainPow (waveOperator Ω) k ↔
      Wave.MemLaplacianDomain Ω (k + 1) (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume U.fst) ∧
        Wave.MemLaplacianDomain Ω k U.snd) ∧
    ∀ U : Wave.phaseSpace Ω, U ∈ domainPow (waveOperator Ω) k →
      (∃ w : sobolevSpaceHigher (d + 1) (k + 1) 2 Ω,
        fnL ℝ 𝔟 (k + 1) 2 Ω volume w = SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume U.fst) ∧
      ∃ z : sobolevSpaceHigher (d + 1) k 2 Ω, fnL ℝ 𝔟 k 2 Ω volume z = U.snd := by
  have hΩk : IsContDiffChartDomain (k + 1) (Ω : Set 𝔼) := hΩ.of_le (by simp)
  have hΩk' : IsContDiffChartDomain k (Ω : Set 𝔼) := hΩ.of_le (by simp)
  have e := waveOperator_eq (hΩ.of_le le_top) hΓ
  -- membership in `D(A^k)` is transported along `A = Wave.operator Ω` by `congrArg` (a `rw` of
  -- `e` in a goal mentioning `MemLaplacianDomain Ω (k + 1)` exhausts the budget)
  have hmem : ∀ U : Wave.phaseSpace Ω, U ∈ domainPow (waveOperator Ω) k ↔
      Wave.MemLaplacianDomain Ω (k + 1) (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume U.fst) ∧
        Wave.MemLaplacianDomain Ω k U.snd := fun U ↦
    (Iff.of_eq (congrArg (fun A ↦ U ∈ domainPow A k) e)).trans
      (mem_domainPow_iff.trans (Wave.mem_operator_powGraph_iff k U))
  exact ⟨hmem, fun U hU ↦ ⟨((hmem U).1 hU).1.exists_sobolev (k + 1) hΩk hΓ,
    ((hmem U).1 hU).2.exists_sobolev k hΩk' hΓ⟩⟩

/-- **"`D(A^k) ⊂ H^{k+1}(Ω) × H^k(Ω)` with continuous injection"** (proof of Theorem 10.8): for
`Ω` of class `C^∞` with `Γ` bounded and every `k` there is `C` with `‖w‖_{H^{k+1}} ≤ C ‖x‖_{D(A^k)}`
and `‖z‖_{H^k} ≤ C ‖x‖_{D(A^k)}` for every `x ∈ D(A^k)` (chapter 7's Hilbert space `PowDomain`,
graph norm `(∑ⱼ |A^j U|²)^{1/2}`) and the lifts `w ∈ H^{k+1}(Ω)`, `z ∈ H^k(Ω)` of the components
`(u, v) = A^0 x` given by `theorem_10_8_domain`. The backbone's bounded linear map
`Wave.operator.powDomainToSobolevL` (closed graph theorem), whose two components the lifts are
since `fnL` is injective. -/
theorem theorem_10_8_domain_norm (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : (waveOperator Ω).PowDomain k)
      (w : sobolevSpaceHigher (d + 1) (k + 1) 2 Ω) (z : sobolevSpaceHigher (d + 1) k 2 Ω),
      fnL ℝ 𝔟 (k + 1) 2 Ω volume w = SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume
          (LinearPMap.PowDomain.applyL (waveOperator Ω) k 0 x).fst →
        fnL ℝ 𝔟 k 2 Ω volume z = (LinearPMap.PowDomain.applyL (waveOperator Ω) k 0 x).snd →
        ‖w‖ ≤ C * ‖x‖ ∧ ‖z‖ ≤ C * ‖x‖ := by
  have hΩk : IsContDiffChartDomain (k + 1) (Ω : Set 𝔼) := hΩ.of_le (by simp)
  -- the statement is transported from the backbone's operator along `A = Wave.operator Ω` with
  -- an explicit motive (`rw`, `simp only` and `generalize` all fail on the dependent binder
  -- `x : D(A^k)`: the first two exhaust the budget, the third cannot rewrite it)
  refine Eq.mpr (congrArg (fun A : Wave.phaseSpace Ω →ₗ.[ℝ] Wave.phaseSpace Ω ↦
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : A.PowDomain k)
      (w : sobolevSpaceHigher (d + 1) (k + 1) 2 Ω) (z : sobolevSpaceHigher (d + 1) k 2 Ω),
      fnL ℝ 𝔟 (k + 1) 2 Ω volume w = SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume
          (LinearPMap.PowDomain.applyL A k 0 x).fst →
        fnL ℝ 𝔟 k 2 Ω volume z = (LinearPMap.PowDomain.applyL A k 0 x).snd →
        ‖w‖ ≤ C * ‖x‖ ∧ ‖z‖ ≤ C * ‖x‖) (waveOperator_eq (hΩ.of_le le_top) hΓ)) ?_
  refine ⟨‖Wave.operator.powDomainToSobolevL k hΩk hΓ‖, norm_nonneg _, fun x w z hw hz ↦ ?_⟩
  -- the lifts are the components of `powDomainToSobolevL x` (`fnL` is injective; its
  -- injectivity is stated with the type spelled out, instance search on the implicit form being
  -- a minute)
  have hJ : Function.Injective (fnL ℝ 𝔟 (k + 1) 2 Ω volume) := fnL_injective
  have hJ' : Function.Injective (fnL ℝ 𝔟 k 2 Ω volume) := fnL_injective
  have e1 : w = (Wave.operator.powDomainToSobolevL k hΩk hΓ x).1 :=
    hJ (hw.trans (Wave.fnL_powDomainToSobolevL_fst k hΩk hΓ x).symm)
  have e2 : z = (Wave.operator.powDomainToSobolevL k hΩk hΓ x).2 :=
    hJ' (hz.trans (Wave.fnL_powDomainToSobolevL_snd k hΩk hΓ x).symm)
  rw [e1, e2]
  exact ⟨(norm_fst_le _).trans ((Wave.operator.powDomainToSobolevL k hΩk hΓ).le_opNorm x),
    (norm_snd_le _).trans ((Wave.operator.powDomainToSobolevL k hΩk hΓ).le_opNorm x)⟩

/-- **Theorem 10.8 (regularity).** Let `Ω` be of class `C^∞` with `Γ` bounded. Assume that the
initial data satisfy `u₀, v₀ ∈ H^k(Ω)` for every `k` and the compatibility conditions
`Δ^j u₀ = 0`, `Δ^j v₀ = 0` on `Γ` for every integer `j ≥ 0` — read, as in the display of the
proof (`theorem_10_8_domain`), as `u₀ ∈ D_k` and `v₀ ∈ D_k` for every `k`
(`Wave.MemLaplacianDomain`: the iterates `u₀, −Δu₀, (−Δ)²u₀, …` lie in `D(−Δ) = H² ∩ H¹₀`
with `(−Δ)^j u₀ ∈ H¹₀(Ω)` for every `j`, likewise for `v₀`), which on a `C^∞` domain contains
`u₀, v₀ ∈ H^k(Ω)` for every `k` (`Wave.MemLaplacianDomain.exists_sobolev`). Then the solution
`u` of (27), (28), (29), (30) belongs to `C^∞(Ω̄ × [0, ∞))`: there is `U : ℝ^N × ℝ → ℝ` with
`U(·, t) = u(t)` a.e. on `Ω` for every `t ≥ 0`, of class `C^∞` on `Ω × (0, ∞)` with every
derivative extending continuously to `closure (Ω × (0, ∞)) = Ω̄ × [0, ∞)` (`ContDiffOnClosure`,
the shape of `theorem_10_2_c`). The book's proof: `U₀ = (u₀, v₀) ∈ D(A^k)` for every `k`
(`theorem_10_8_domain`), Theorem 7.5 gives `U ∈ C^{k−j}([0, ∞); D(A^j))` for `0 ≤ j ≤ k`, so
`u ∈ C^{k−j}([0, ∞); H^{j+1}(Ω))` (`theorem_10_8_domain_norm`), and Corollary 9.15 — the
backbone's `Wave.IsSolution.contDiffOnThrough_of_powDomain` and
`Wave.IsSolution.contDiffOnClosure_spaceTime` (through the space–time bridge
`Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ici`). -/
theorem theorem_10_8 (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼)))
    (hu₀ : ∀ k, Wave.MemLaplacianDomain Ω k (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume u₀))
    (hv₀ : ∀ k, Wave.MemLaplacianDomain Ω k (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀))
    (hu : IsWaveSolution Ω u₀ v₀ u) :
    ∃ U : 𝔼 × ℝ → ℝ, (∀ t, 0 ≤ t → (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set 𝔼)] u t) ∧
      ContDiffOnClosure ℝ ∞ U ((Ω : Set 𝔼) ×ˢ Ioi 0) := by
  -- `(u₀, v₀) ∈ D(A^k)` for every `k`: the display of the proof, `D(A^k) = D_{k+1} × D_k`
  have hU₀ : ∀ k, ∃ x : (Wave.operator Ω).PowDomain k,
      LinearPMap.PowDomain.applyL (Wave.operator Ω) k 0 x
        = Wave.phaseSpace.mk Ω u₀ (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀) := fun k ↦
    (Wave.mem_operator_powGraph_iff k _).2 ⟨hu₀ (k + 1), hv₀ k⟩
  obtain ⟨U, hU, hc⟩ := hu.isSolution.contDiffOnClosure_spaceTime hU₀ hΩ hΓ
  exact ⟨U, fun t ht ↦ hU t ht, hc⟩

end Regular

section DAlembert

/-- The line `ℝ` as `ℝ¹`. -/
local notation "𝔼₁" => EuclideanSpace ℝ (Fin 1)

/-! ### Remark 8: d'Alembert's formula is the solution on `Ω = ℝ` -/

/-- **Remark 8, d'Alembert's formula (40).** On `Ω = ℝ` (`N = 1`, `Ω = ⊤`), for `u₀ ∈ H²(ℝ)` and
`v₀ ∈ H¹(ℝ)` — the data of Theorem 10.7, `H¹₀(ℝ) = H¹(ℝ)` (Remark 17 of chapter 9,
`Wave.toZeroTopL`) — the curve `u` of the `L²(ℝ)` classes of
`u(x, t) = ½ (u₀(x + t) + u₀(x − t)) + ½ ∫_{x−t}^{x+t} v₀(s) ds` (the backbone's
`Wave.dAlembertL2`, whose value is `Wave.dAlembert` read on the line through the coordinate
`x ↦ x₀` and `Wave.lineEmbed : ℝ → ℝ¹`) is the solution of (27)–(30) in the class (31): it is a
solution (`Wave.isSolution_dAlembert`), and every solution agrees with it on `[0, ∞)`
(`Wave.IsSolution.eqOn_dAlembertL2`). For `v₀ = 0` it is (41). -/
theorem remark_10_8 (u₀ : sobolevSpaceHigher 1 2 2 ⊤) (v₀ : hSpace 1 ⊤) :
    IsWaveSolution ⊤ (Wave.toZeroTopL (by simp) (Wave.dAlembertU₀ u₀))
        (Wave.toZeroTopL (by simp) v₀) (Wave.dAlembertL2 u₀ v₀) ∧
      (∀ v, IsWaveSolution ⊤ (Wave.toZeroTopL (by simp) (Wave.dAlembertU₀ u₀))
        (Wave.toZeroTopL (by simp) v₀) v → EqOn v (Wave.dAlembertL2 u₀ v₀) (Ici 0)) ∧
      ∀ t, Wave.dAlembertL2 u₀ v₀ t =ᵐ[volume.restrict ((⊤ : Opens 𝔼₁) : Set 𝔼₁)]
        fun x ↦ Wave.dAlembert (fun r ↦ fn u₀ (Wave.lineEmbed r))
          (fun r ↦ fn v₀ (Wave.lineEmbed r)) t (x 0) := by
  have hΩ : IsOfClassC 2 ((⊤ : Opens 𝔼₁) : Set 𝔼₁) :=
    ⟨isOpen_univ, fun _ h ↦ by simp [frontier_univ] at h⟩
  have hΓ : Bornology.IsBounded (frontier ((⊤ : Opens 𝔼₁) : Set 𝔼₁)) := by
    rw [Opens.coe_top, frontier_univ]
    exact Bornology.isBounded_empty
  have h := Wave.isSolution_dAlembert u₀ v₀
  refine ⟨(isWaveSolution_iff hΩ hΓ).2 h, fun v hv ↦ hv.isSolution.unique h, fun t ↦ ?_⟩
  exact Wave.coeFn_dAlembertL2_dAlembert u₀ v₀ t

end DAlembert

section Necessity

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-! ### Remark 10: the compatibility conditions are necessary -/

/-- **Remark 10.** The compatibility conditions of Theorem 10.8 are necessary and sufficient in
order to have a solution `u ∈ C^∞(Ω̄ × [0, ∞))` of (27), (28), (29), (30). Sufficiency is
`theorem_10_8`; necessity, "the proof is the same as in Remark 4" (`remark_10_4`): if
`u : ℝ^N × ℝ → ℝ` is of class `C^∞` (on `ℝ^N × ℝ`, so that `u ∈ C^∞(Ω̄ × [0, ∞))` and the
boundary values of `Δ^j u(·, 0)` and `Δ^j ∂ₜu(·, 0)` are meaningful as written), satisfies
`∂ₜₜu = Δu` in `Q = Ω × (0, ∞)` and `u = 0` on `Σ = Γ × (0, ∞)`, then `Δ^j u₀ = 0` and
`Δ^j v₀ = 0` on `Γ` for every `j`, where `u₀ = u(·, 0)` and `v₀ = ∂ₜu(·, 0)`: all time derivatives
of `u` vanish on `Γ × [0, ∞)` by continuity, `∂ₜ^{2j} u = Δ^j u` and `∂ₜ^{2j+1} u = Δ^j ∂ₜu` in
`Q̄` by induction and continuity, and the two are compared on `Γ × {0}`. The backbone's
`Wave.IsClassicalSolution.iteratedLaplacian_eq_zero_frontier` (on the cylinder `Ω × (0, 1)`). -/
theorem remark_10_10 {u : 𝔼 × ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (heq : ∀ x ∈ Ω, ∀ t, 0 < t →
      deriv (deriv fun s ↦ u (x, s)) t = Δ (fun y ↦ u (y, t)) x)
    (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), ∀ t, 0 < t → u (x, t) = 0) (j : ℕ) :
    ∀ x ∈ frontier (Ω : Set 𝔼), (Δ^[j] fun y ↦ u (y, 0)) x = 0 ∧
      (Δ^[j] fun y ↦ deriv (fun s ↦ u (y, s)) 0) x = 0 :=
  Wave.IsClassicalSolution.iteratedLaplacian_eq_zero_frontier Ω.isOpen one_pos
    ⟨fun p hp ↦ heq p.1 hp.1 p.2 hp.2.1⟩ hu (fun x hx t ht ↦ hΓ x hx t ht.1) j

end Necessity

end Brezis.Chapter10
