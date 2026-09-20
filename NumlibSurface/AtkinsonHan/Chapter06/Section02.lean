import Mathlib.Analysis.Calculus.Deriv.Slope
import Numlib.Analysis.PDE.Heat.SineSeries
import Numlib.FiniteDifference.LaxEquivalence

/-!
# Atkinson–Han §6.2: the Lax equivalence theorem

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §6.2.

The section studies the abstract initial value problem `u' = L u`, `u(0) = u₀`, on `[0, T]` in a
Banach space `V` over `ℝ` or `ℂ`, for a linear, generally unbounded operator `L` defined on a dense
subspace `V₀ ⊆ V`.  The surface takes the real scalars and reads `L : V₀ ⊆ V → V` as Mathlib's
`LinearPMap`, `L : V →ₗ.[ℝ] V` with `Dense (L.domain : Set V)`, as §8.2 of this surface already
does for closed operators.

Every result is a specialization of `Numlib/FiniteDifference/LaxEquivalence`, which is stated in
the same generality.  The surface does work of its own in exactly two places, both of them the
passage from a limit the book writes with a quotient to the form the backbone takes:

* **Definition 6.2.1** is the limit of the difference quotient `(u(s) - u(t))/(s - t)` as `s → t`
  *within* `[0, T]`, which is the book's one-sided convention at the two endpoints; the backbone
  writes it as `HasDerivWithinAt`, and `isSolution_iff` is that identification, through Mathlib's
  `hasDerivWithinAt_iff_tendsto_slope`.
* **Definition 6.2.7** is `‖(C(Δt) u(t) - u(t + Δt))/Δt‖ ≤ ε` with the division present; the
  backbone clears it, and `isConsistent_iff` is that identification.

**Definition 6.2.3, the solution operators, is a definition here and an existence theorem there.**
`FiniteDifference.exists_solutionOperator` produces the family from well-posedness and density —
the book's appeal to its Theorem 2.4.1, which this surface proves as
`AtkinsonHan.Chapter02.theorem_2_4_1` — so `solutionOperator` opens that existential once and
`solutionOperator_zero`, `norm_solutionOperator_le` and `solutionOperator_apply` are its three
properties.  `solutionOperator L hdense hT hc₀ hwp t u₀` for `u₀ ∉ L.domain` is the book's
*generalized* solution.

## Main results

* `IsSolution`, `IsWellPosed`, `solutionOperator` — Definitions 6.2.1, 6.2.2, 6.2.3.
* `proposition_6_2_5` — the generalized solution is continuous in time.
* `proposition_6_2_6` — the solution operators form a semigroup.
* `IsConsistent`, `IsConvergent`, `IsStable` — Definitions 6.2.7, 6.2.9, 6.2.10.
* `theorem_6_2_11` — the Lax equivalence theorem.
* `corollary_6_2_12` — the order of convergence.

## Two readings that the book leaves implicit

**Convergence is restricted to steps within the horizon**, `m Δt ≤ T`.  Outside it the evolution
family is evaluated where nothing has been assumed about it, so the continuity hypothesis of the
equivalence theorem says nothing there and the definition would be about junk.

**The semigroup property needs well-posedness at every horizon `T' ≤ T`**, not only at `T`:
translating a solution back by `t₀` produces a solution on `[0, T - t₀]`, and it is uniqueness
*there* that identifies it with the trajectory started at `S(t₀) u₀`.  `proposition_6_2_6`
therefore carries that hypothesis.  The Lax equivalence theorem does not use the semigroup
property at all.

## The heat equation: Examples 6.2.4, 6.2.8 and 6.2.13

The book's running example is `u_t = ν u_xx` on `(0, π) × (0, T)` with homogeneous Dirichlet
boundary values, in `V = C₀[0, π]` (`C₀`, a closed subspace of `C[0, π]` with the maximum norm)
with `V₀` the finite sine polynomials (`sinePolynomials`, (6.2.5)) and `L = ν ∂²/∂x²` on `V₀`
(`heatOperator`, presented through its action on the sines and identified with the second
derivative by `heatOperator_apply_eq_laplacian`).

* **Example 6.2.4**: `V₀` is dense (`example_6_2_4_dense`, the book's Exercise 6.2.1, from the
  uniform density of trigonometric polynomials on the circle applied to the odd periodic extension,
  `exists_mem_span_sinMap_norm_sub_lt`); for a sine polynomial the solution is the explicit
  series (6.2.7) (`sineSolution`, `isSolution_sineSolution`); every solution in the sense of
  Definition 6.2.1 is a classical solution of the heat equation and the maximum principle
  (`Heat.IsClassicalSolution.abs_le_of_eq_zero_frontier`, Brezis's Theorem 10.6) bounds it by its
  initial value (`norm_le_of_isSolution`); so the problem is well posed with `c₀ = 1`
  (`example_6_2_4`) and the solution operators are bounded by `1`
  (`example_6_2_4_norm_solutionOperator_le`).
* **Example 6.2.8**: the forward scheme `C (Δt) v = (1 - 2r) v + r [ṽ (· + Δx) + ṽ (· - Δx)]`,
  on the odd `2π`-periodic extension `ṽ` (`oddPeriodicExtend`,
  `Numlib.Analysis.PDE.Heat.SineSeries`), as a bounded operator `forwardScheme` with
  `‖C (Δt)‖ ≤ |1 - 2r| + 2r` (6.2.8) (`norm_forwardScheme_le`); its consistency on `V_c = V₀` by
  the Taylor expansion of (6.2.7) (`example_6_2_8`); the backward scheme `backwardScheme = Q₁⁻¹`
  inverted by a Neumann series, with `‖C (Δt)‖ ≤ 1` for every `r` (`norm_backwardScheme_le`)
  and, the clause the book leaves to the reader, its consistency (`example_6_2_8_backward`).
* **Example 6.2.13**: the equivalence theorem applied — the forward scheme is stable and
  convergent for `r ≤ 1/2` (`example_6_2_13`), the backward one unconditionally
  (`example_6_2_13_backward`); and the book's Exercise 6.2.3 as helpers — the exact norm
  `‖C (Δt)‖ = |1 - 2r| + 2r` (`norm_forwardScheme_eq`, valid once `Δx < π/2`) and the
  instability of the forward scheme for `r > 1/2` (`not_isStable_forwardScheme`, from the
  amplification factor `1 - 2r + 2r cos ((k + 1) Δx)` on the modes `sin ((k + 1) x)`), so that
  the forward scheme is stable if and only if `r ≤ 1/2`: it is *conditionally* stable.

**The consistency horizon.** Definition 6.2.7 evaluates `S (t + Δt) u₀` for `t ∈ [0, T]`, and the
solution operators of Definition 6.2.3 are determined only on their own horizon; the book's
definition is read with the restriction `t + Δt ≤ T`, which is all the proof of Theorem 6.2.11
uses, so that the consistency and convergence statements take the solution operators on `[0, T]`
itself and `theorem_6_2_11` applies to them directly.

Not formalized: the book's Exercise 6.2.2 (Crank–Nicolson).
-/

open Filter Set Topology

namespace AtkinsonHan.Chapter06

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### The abstract initial value problem -/

/-- **Definition 6.2.1** and (6.2.2).  `u` is a solution of `u' = L u`, `u(0) = u₀`, on `[0, T]`
when `u(t)` lies in the domain of `L` for every `t ∈ [0, T]` and the difference quotient
`(u(s) - u(t))/(s - t)` tends to `L u(t)` as `s → t` within `[0, T]` — a limit within the closed
interval being exactly the book's one-sided convention at the two endpoints. -/
def IsSolution (L : V →ₗ.[ℝ] V) (T : ℝ) (u₀ : V) (u : ℝ → V) : Prop :=
  u 0 = u₀ ∧ ∀ t ∈ Icc (0 : ℝ) T, ∃ h : u t ∈ L.domain,
    Tendsto (fun s : ℝ => (s - t)⁻¹ • (u s - u t)) (𝓝[Icc 0 T \ {t}] t) (𝓝 (L ⟨u t, h⟩))

/-- The book's difference quotient is Mathlib's `slope`. -/
private theorem slope_eq (u : ℝ → V) (t : ℝ) :
    slope u t = fun s : ℝ => (s - t)⁻¹ • (u s - u t) := rfl

/-- (6.2.2) is the backbone's `HasDerivWithinAt` formulation. -/
theorem isSolution_iff (L : V →ₗ.[ℝ] V) (T : ℝ) (u₀ : V) (u : ℝ → V) :
    IsSolution L T u₀ u ↔ FiniteDifference.IsSolution L T u₀ u := by
  simp only [IsSolution, FiniteDifference.IsSolution, hasDerivWithinAt_iff_tendsto_slope, slope_eq]

/-- **Definition 6.2.2** and (6.2.3).  The initial value problem is *well posed* on `[0, T]` with
stability constant `c₀` when every initial value in the domain of `L` has a solution, that solution
is unique on `[0, T]`, and solutions depend continuously on the initial value,
`‖u(t) - ū(t)‖ ≤ c₀ ‖u₀ - ū₀‖`.

Uniqueness is stated as `Set.EqOn` on `[0, T]` rather than as `∃!` over all of `ℝ → V`, because the
book constrains `u` only there.  It is in fact implied by the stability bound at `u₀ = ū₀`
(`FiniteDifference.IsWellPosed.eqOn`), which is why the backbone predicate has two clauses where
this one has three; `isWellPosed_iff` records that they agree. -/
def IsWellPosed (L : V →ₗ.[ℝ] V) (T c₀ : ℝ) : Prop :=
  (∀ u₀ ∈ L.domain, ∃ u, IsSolution L T u₀ u) ∧
    (∀ u₀ ∈ L.domain, ∀ u ū, IsSolution L T u₀ u → IsSolution L T u₀ ū → EqOn u ū (Icc 0 T)) ∧
      ∀ u₀ ū₀ u ū, IsSolution L T u₀ u → IsSolution L T ū₀ ū →
        ∀ t ∈ Icc (0 : ℝ) T, ‖u t - ū t‖ ≤ c₀ * ‖u₀ - ū₀‖

/-- Definition 6.2.2 is the backbone's well-posedness: its uniqueness clause is redundant. -/
theorem isWellPosed_iff (L : V →ₗ.[ℝ] V) (T c₀ : ℝ) :
    IsWellPosed L T c₀ ↔ FiniteDifference.IsWellPosed L T c₀ := by
  constructor
  · rintro ⟨hex, -, hst⟩
    refine ⟨fun u₀ hu₀ => (hex u₀ hu₀).imp fun u hu => (isSolution_iff L T u₀ u).1 hu,
      fun u₀ ū₀ u ū hu hū => hst u₀ ū₀ u ū ((isSolution_iff L T u₀ u).2 hu)
        ((isSolution_iff L T ū₀ ū).2 hū)⟩
  · intro hwp
    refine ⟨fun u₀ hu₀ => (hwp.1 u₀ hu₀).imp fun u hu => (isSolution_iff L T u₀ u).2 hu,
      fun u₀ _ u ū hu hū => hwp.eqOn ((isSolution_iff L T u₀ u).1 hu)
        ((isSolution_iff L T u₀ ū).1 hū),
      fun u₀ ū₀ u ū hu hū => hwp.2 u₀ ū₀ u ū ((isSolution_iff L T u₀ u).1 hu)
        ((isSolution_iff L T ū₀ ū).1 hū)⟩

/-- A solution on `[0, T]` restricts to a solution on any shorter horizon: a derivative within a
set is a derivative within a subset. -/
private theorem isSolution_mono {L : V →ₗ.[ℝ] V} {T T' : ℝ} {u₀ : V} {u : ℝ → V}
    (hu : FiniteDifference.IsSolution L T u₀ u) (hT' : T' ≤ T) :
    FiniteDifference.IsSolution L T' u₀ u := by
  refine ⟨hu.1, fun t ht => ?_⟩
  obtain ⟨h, hd⟩ := hu.2 t ⟨ht.1, ht.2.trans hT'⟩
  exact ⟨h, hd.mono (Icc_subset_Icc le_rfl hT')⟩

/-! ### Definition 6.2.3: the solution operators and the generalized solution -/

section SolutionOperator

variable [CompleteSpace V]

/-- **Definition 6.2.3, the solution operators.**  For a well-posed problem with a dense domain
there is a family of bounded operators `S(t) : V → V` with `S(0) = I`, `‖S(t)‖ ≤ c₀` on `[0, T]`,
and `S(t) u₀ = u(t)` whenever `u₀` lies in the domain of `L` and `u` is the solution started there.
Its value at an initial value outside the domain is the book's *generalized* solution.

The backbone delivers the family as an existential (`FiniteDifference.exists_solutionOperator`,
which is the book's appeal to its Theorem 2.4.1 on extending a bounded operator from a dense
subspace), and this definition opens it once.  The three properties are `solutionOperator_zero`,
`norm_solutionOperator_le` and `solutionOperator_apply`; nothing else about the family should be
used, since the choice is not canonical outside `[0, T]`. -/
noncomputable def solutionOperator (L : V →ₗ.[ℝ] V) (hdense : Dense (L.domain : Set V)) {T c₀ : ℝ}
    (hT : 0 ≤ T) (hc₀ : 0 ≤ c₀) (hwp : IsWellPosed L T c₀) : ℝ → V →L[ℝ] V :=
  (FiniteDifference.exists_solutionOperator L hdense hT hc₀
    ((isWellPosed_iff L T c₀).1 hwp)).choose

variable (L : V →ₗ.[ℝ] V) (hdense : Dense (L.domain : Set V)) {T c₀ : ℝ} (hT : 0 ≤ T)
  (hc₀ : 0 ≤ c₀) (hwp : IsWellPosed L T c₀)

private theorem solutionOperator_spec :
    solutionOperator L hdense hT hc₀ hwp 0 = 1 ∧
      (∀ t ∈ Icc (0 : ℝ) T, ‖solutionOperator L hdense hT hc₀ hwp t‖ ≤ c₀) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ u₀ ∈ L.domain, ∀ u, FiniteDifference.IsSolution L T u₀ u →
        solutionOperator L hdense hT hc₀ hwp t u₀ = u t :=
  (FiniteDifference.exists_solutionOperator L hdense hT hc₀
    ((isWellPosed_iff L T c₀).1 hwp)).choose_spec

/-- `S(0) = I`. -/
theorem solutionOperator_zero : solutionOperator L hdense hT hc₀ hwp 0 = 1 :=
  (solutionOperator_spec L hdense hT hc₀ hwp).1

/-- `sup_{0 ≤ t ≤ T} ‖S(t)‖ ≤ c₀`, the stability bound of (6.2.3). -/
theorem norm_solutionOperator_le :
    ∀ t ∈ Icc (0 : ℝ) T, ‖solutionOperator L hdense hT hc₀ hwp t‖ ≤ c₀ :=
  (solutionOperator_spec L hdense hT hc₀ hwp).2.1

/-- `S(t) u₀ = u(t)` for an initial value in the domain of `L`: the solution operator really does
carry the solution. -/
theorem solutionOperator_apply {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {u₀ : V} (hu₀ : u₀ ∈ L.domain)
    (u : ℝ → V) (hu : IsSolution L T u₀ u) : solutionOperator L hdense hT hc₀ hwp t u₀ = u t :=
  (solutionOperator_spec L hdense hT hc₀ hwp).2.2 t ht u₀ hu₀ u ((isSolution_iff L T u₀ u).1 hu)

/-- **Proposition 6.2.5.**  For every `u₀ ∈ V` — not only for `u₀` in the domain of `L` — the
generalized solution `t ↦ S(t) u₀` is continuous on `[0, T]`.

On the dense domain it is a genuine solution, hence differentiable within `[0, T]`, hence
continuous; the uniform bound `‖S(t)‖ ≤ c₀` then carries continuity to every `u₀` by the
Banach–Steinhaus density criterion. -/
theorem proposition_6_2_5 (u₀ : V) :
    ContinuousOn (fun t => solutionOperator L hdense hT hc₀ hwp t u₀) (Icc 0 T) := by
  refine FiniteDifference.continuousOn_of_dense hdense
    (norm_solutionOperator_le L hdense hT hc₀ hwp) (fun v hv => ?_) u₀
  obtain ⟨u, hu⟩ := hwp.1 v hv
  refine ContinuousOn.congr ?_ (fun t ht =>
    solutionOperator_apply L hdense hT hc₀ hwp ht hv u hu)
  intro t ht
  obtain ⟨_, hd⟩ := ((isSolution_iff L T v u).1 hu).2 t ht
  exact HasDerivWithinAt.continuousWithinAt hd

/-- **Proposition 6.2.6.**  The solution operators form a semigroup:
`S(t₁ + t₀) = S(t₁) ∘ S(t₀)` whenever `t₀, t₁ ≥ 0` and `t₁ + t₀ ≤ T`.

Well-posedness is asked for at *every* horizon `T' ≤ T`, not only at `T`.  Translating a solution
back by `t₀` produces a solution on `[0, T - t₀]`, and it is uniqueness there — a statement about
curves defined only on the shorter interval — that identifies it with the trajectory started at
`S(t₀) u₀`.

**The Lax equivalence theorem does not use this**; it is recorded because the book states it. -/
theorem proposition_6_2_6 (hwp' : ∀ T' ∈ Icc (0 : ℝ) T, IsWellPosed L T' c₀) {t₀ t₁ : ℝ}
    (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁) (hsum : t₁ + t₀ ≤ T) :
    solutionOperator L hdense hT hc₀ hwp (t₁ + t₀)
      = solutionOperator L hdense hT hc₀ hwp t₁ ∘L solutionOperator L hdense hT hc₀ hwp t₀ := by
  refine FiniteDifference.solutionOperator_add hdense
    (fun u₀ hu₀ => (hwp.1 u₀ hu₀).imp fun u hu => (isSolution_iff L T u₀ u).1 hu) ?_ ht₀ ht₁ hsum
  intro T' hT' t ht u₀ hu₀ u hu
  obtain ⟨w, hw⟩ := hwp.1 u₀ hu₀
  have hwb : FiniteDifference.IsSolution L T u₀ w := (isSolution_iff L T u₀ w).1 hw
  have hwT' : IsSolution L T' u₀ w := (isSolution_iff L T' u₀ w).2 (isSolution_mono hwb hT'.2)
  have hEq := (hwp' T' hT').2.1 u₀ hu₀ u w ((isSolution_iff L T' u₀ u).2 hu) hwT'
  rw [solutionOperator_apply L hdense hT hc₀ hwp ⟨ht.1, ht.2.trans hT'.2⟩ hu₀ w hw]
  exact (hEq ht).symm

end SolutionOperator

/-! ### Consistency, stability and convergence -/

/-- **Definition 6.2.7, consistency.**  The difference method `{C(Δt)}` is consistent with the
evolution family `S` on `[0, T]`, for step sizes in `(0, Δ₀]` and initial values in the dense set
`V_c`, when the local truncation error

  `(C(Δt) u(t) - u(t + Δt)) / Δt`

tends to `0` as `Δt → 0`, uniformly in `t ∈ [0, T]`.  Here `u(t) = S(t) u₀`, so the condition is
tested on the trajectories of the family, and only where the family is known: at the `t` with
`t + Δt ≤ T` (the solution operators of Definition 6.2.3 exist on their horizon `[0, T]` alone,
and the proof of Theorem 6.2.11 uses the truncation error at the grid points `k Δt` with
`(k + 1) Δt ≤ m Δt ≤ T` only).

The division is written out, as the book writes it; the backbone clears it, and
`isConsistent_iff` is that identification. -/
def IsConsistent (S C : ℝ → V →L[ℝ] V) (T Δ₀ : ℝ) (D : Set V) : Prop :=
  Dense D ∧ ∀ u₀ ∈ D, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, Δt < δ →
    ∀ t ∈ Icc (0 : ℝ) T, t + Δt ≤ T → ‖(Δt)⁻¹ • (C Δt (S t u₀) - S (t + Δt) u₀)‖ ≤ ε

/-- Clearing the division in Definition 6.2.7. -/
private theorem norm_inv_smul_le_iff {x : V} {Δt ε : ℝ} (hΔt : 0 < Δt) :
    ‖(Δt)⁻¹ • x‖ ≤ ε ↔ ‖x‖ ≤ ε * Δt := by
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hΔt, ← div_eq_inv_mul, div_le_iff₀ hΔt]

/-- Definition 6.2.7 is the backbone's consistency, whose statement has the division cleared. -/
theorem isConsistent_iff (S C : ℝ → V →L[ℝ] V) (T Δ₀ : ℝ) (D : Set V) :
    IsConsistent S C T Δ₀ D ↔ FiniteDifference.IsConsistent S C T Δ₀ D := by
  constructor
  · rintro ⟨hD, h⟩
    refine ⟨hD, fun u₀ hu₀ ε hε => ?_⟩
    obtain ⟨δ, hδ, hb⟩ := h u₀ hu₀ ε hε
    exact ⟨δ, hδ, fun Δt hΔt hlt t ht htΔ =>
      (norm_inv_smul_le_iff hΔt.1).1 (hb Δt hΔt hlt t ht htΔ)⟩
  · rintro ⟨hD, h⟩
    refine ⟨hD, fun u₀ hu₀ ε hε => ?_⟩
    obtain ⟨δ, hδ, hb⟩ := h u₀ hu₀ ε hε
    exact ⟨δ, hδ, fun Δt hΔt hlt t ht htΔ =>
      (norm_inv_smul_le_iff hΔt.1).2 (hb Δt hΔt hlt t ht htΔ)⟩

/-- **Definition 6.2.9, convergence.**  The method converges to the evolution family when
`‖(C(Δt_i)^{m_i} - S(t)) u₀‖ → 0` for every `t ∈ [0, T]`, every `u₀ ∈ V` and every refinement:
every pair of sequences of step sizes `Δt_i ∈ (0, Δ₀]` and step counts `m_i` with `Δt_i → 0` and
`m_i Δt_i → t`.

Two readings the book leaves implicit.  The limit is along *sequences*, because it is not a limit
along one sequence of step sizes but along every refinement whose discrete time tends to `t`.  And
the step counts are restricted to the horizon, `m_i Δt_i ≤ T`: outside it the evolution family is
evaluated where nothing has been assumed about it. -/
def IsConvergent (S C : ℝ → V →L[ℝ] V) (T Δ₀ : ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) T, ∀ u₀ : V, ∀ (Δt : ℕ → ℝ) (m : ℕ → ℕ), (∀ i, Δt i ∈ Ioc (0 : ℝ) Δ₀) →
    (∀ i, (m i : ℝ) * Δt i ≤ T) → Tendsto Δt atTop (𝓝 0) →
    Tendsto (fun i => (m i : ℝ) * Δt i) atTop (𝓝 t) →
    Tendsto (fun i => ‖(C (Δt i) ^ m i - S t) u₀‖) atTop (𝓝 0)

/-- Definition 6.2.9 is the backbone's convergence. -/
theorem isConvergent_iff (S C : ℝ → V →L[ℝ] V) (T Δ₀ : ℝ) :
    IsConvergent S C T Δ₀ ↔ FiniteDifference.IsConvergent S C T Δ₀ := by
  simp only [IsConvergent, FiniteDifference.IsConvergent, sub_apply]

/-- **Definition 6.2.10, stability.**  The method is stable when the powers `C(Δt)^m` taken within
the horizon, `m Δt ≤ T` and `0 < Δt ≤ Δ₀`, are bounded in norm uniformly in the step size. -/
def IsStable (C : ℝ → V →L[ℝ] V) (T Δ₀ : ℝ) : Prop :=
  ∃ M₀ : ℝ, ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, ∀ m : ℕ, (m : ℝ) * Δt ≤ T → ‖C Δt ^ m‖ ≤ M₀

/-- Definition 6.2.10 is the backbone's stability, definitionally. -/
theorem isStable_iff (C : ℝ → V →L[ℝ] V) (T Δ₀ : ℝ) :
    IsStable C T Δ₀ ↔ FiniteDifference.IsStable C T Δ₀ := Iff.rfl

/-! ### The equivalence theorem -/

section Equivalence

variable [CompleteSpace V] (L : V →ₗ.[ℝ] V) (hdense : Dense (L.domain : Set V)) {T c₀ : ℝ}
  (hT : 0 ≤ T) (hc₀ : 0 ≤ c₀) (hwp : IsWellPosed L T c₀)

/-- **Theorem 6.2.11, the Lax equivalence theorem.**  For a well-posed initial value problem and a
difference method that is uniformly bounded in norm and consistent on a dense set of initial
values, stability is equivalent to convergence.

The uniform bound `‖C(Δt)‖ ≤ c₁` is a hypothesis the book makes silently when it introduces the
family, a page before the theorem, and its proof of the backward direction uses it: without it the
step `sup_k ‖C(Δt_k)^{m_k}‖ ≤ sup_k ‖C(Δt_k)‖^{m_k} < ∞` for step sizes bounded away from zero is
unjustified.  The semigroup property of Proposition 6.2.6 is **not** used. -/
theorem theorem_6_2_11 {C : ℝ → V →L[ℝ] V} {Δ₀ c₁ : ℝ} {D : Set V}
    (hC : ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, ‖C Δt‖ ≤ c₁)
    (hcons : IsConsistent (solutionOperator L hdense hT hc₀ hwp) C T Δ₀ D) :
    IsStable C T Δ₀ ↔ IsConvergent (solutionOperator L hdense hT hc₀ hwp) C T Δ₀ := by
  rw [isStable_iff, isConvergent_iff]
  exact FiniteDifference.isStable_iff_isConvergent hT (solutionOperator_zero L hdense hT hc₀ hwp)
    (proposition_6_2_5 L hdense hT hc₀ hwp) hC ((isConsistent_iff _ _ _ _ _).1 hcons)

/-- **Corollary 6.2.12, the order of convergence.**  If the scheme is stable up to step `m` with
constant `M₀` and the local error at the initial value `u₀` is `O(Δt^{k+1})` uniformly on `[0, T]`,
then

  `‖C(Δt)^m u₀ - S(t) u₀‖ ≤ M₀ t c Δt^k`  whenever `m Δt = t`.

No limit is taken, so this is an inequality with explicit constants.  For `u₀` in the domain of `L`
the right-hand term is the value `u(t)` of the exact solution, by `solutionOperator_apply`. -/
theorem corollary_6_2_12 {C : ℝ → V →L[ℝ] V} {Δt c M₀ t : ℝ} {k m : ℕ} (u₀ : V) (hΔt : 0 < Δt)
    (hmΔt : (m : ℝ) * Δt = t) (ht : t ∈ Icc (0 : ℝ) T)
    (hstab : ∀ i ≤ m, ‖C Δt ^ i‖ ≤ M₀)
    (hloc : ∀ s ∈ Icc (0 : ℝ) T,
      ‖C Δt (solutionOperator L hdense hT hc₀ hwp s u₀)
        - solutionOperator L hdense hT hc₀ hwp (s + Δt) u₀‖ ≤ c * Δt ^ (k + 1)) :
    ‖(C Δt ^ m) u₀ - solutionOperator L hdense hT hc₀ hwp t u₀‖ ≤ M₀ * t * c * Δt ^ k :=
  FiniteDifference.norm_iterate_sub_le u₀ (solutionOperator_zero L hdense hT hc₀ hwp) hΔt hmΔt
    hstab fun s hs => hloc s ⟨hs.1, hs.2.trans ht.2⟩

end Equivalence

/-! ### Example 6.2.4: the heat equation on `(0, π)` in `C₀[0, π]` -/

section HeatExample

open Submodule InnerProductSpace Laplacian
open scoped Real

/-- **Example 6.2.4, the space `V = C₀[0, π]`**: the continuous functions on `[0, π]` vanishing
at both ends, a closed subspace of `C[0, π]` with the maximum norm, hence a Banach space. -/
def C₀ : Submodule ℝ C(Icc (0 : ℝ) π, ℝ) where
  carrier := {v | v ⟨0, left_mem_Icc.2 Real.pi_pos.le⟩ = 0 ∧
    v ⟨π, right_mem_Icc.2 Real.pi_pos.le⟩ = 0}
  add_mem' ha hb := ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' c v hv := ⟨by simp [hv.1], by simp [hv.2]⟩

/-- Membership in `C₀[0, π]`: vanishing at both ends. -/
theorem mem_C₀_iff {v : C(Icc (0 : ℝ) π, ℝ)} :
    v ∈ C₀ ↔ v ⟨0, left_mem_Icc.2 Real.pi_pos.le⟩ = 0 ∧
      v ⟨π, right_mem_Icc.2 Real.pi_pos.le⟩ = 0 :=
  Iff.rfl

/-- `C₀[0, π]` is closed in `C[0, π]`: it is cut out by two evaluations. -/
theorem isClosed_C₀ : IsClosed (C₀ : Set C(Icc (0 : ℝ) π, ℝ)) :=
  (isClosed_eq (continuous_eval_const _) continuous_const).inter
    (isClosed_eq (continuous_eval_const _) continuous_const)

/-- `C₀[0, π]` is a Banach space, being closed in the Banach space `C[0, π]`. -/
instance : CompleteSpace C₀ := isClosed_C₀.completeSpace_coe

/-- A sine polynomial vanishes at both ends of `[0, π]`. -/
theorem sinePolynomial_mem_C₀ (n : ℕ) (c : ℕ → ℝ) : sinePolynomial n c ∈ C₀ :=
  ⟨sinePolynomial_zero_apply n c, sinePolynomial_pi_apply n c⟩

/-- The sine `sin ((k + 1) x)` as an element of `C₀[0, π]`. -/
noncomputable def sinV (k : ℕ) : C₀ :=
  ⟨sinMap k, by
    refine ⟨by simp [sinMap_apply], ?_⟩
    rw [sinMap_apply]
    exact_mod_cast Real.sin_nat_mul_pi (k + 1)⟩

@[simp]
theorem coe_sinV (k : ℕ) : (sinV k : C(Icc (0 : ℝ) π, ℝ)) = sinMap k := rfl

/-- **Example 6.2.4, the subspace `V₀`** of (6.2.5): the finite sine polynomials
`∑_{j = 1}^n a_j sin (j x)`, the span of the sines in `C₀[0, π]`. -/
noncomputable def sinePolynomials : Submodule ℝ C₀ := span ℝ (range sinV)

/-- The sine polynomial `∑ c j sin ((j + 1) x)` as an element of `C₀[0, π]`. -/
noncomputable def sinePolyV (n : ℕ) (c : ℕ → ℝ) : C₀ := ∑ j ∈ Finset.range n, c j • sinV j

@[simp]
theorem coe_sinePolyV (n : ℕ) (c : ℕ → ℝ) :
    (sinePolyV n c : C(Icc (0 : ℝ) π, ℝ)) = sinePolynomial n c := by
  simp [sinePolyV, sinePolynomial]

/-- A sine polynomial lies in `V₀`. -/
theorem sinePolyV_mem (n : ℕ) (c : ℕ → ℝ) : sinePolyV n c ∈ sinePolynomials :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (subset_span ⟨j, rfl⟩)

/-- Under the inclusion `C₀ ⊆ C[0, π]` the sine polynomials of `C₀` are the span of the sine
system. -/
theorem sinePolynomials_map_subtype :
    sinePolynomials.map C₀.subtype = span ℝ (range sinMap) := by
  rw [sinePolynomials, Submodule.map_span, ← Set.range_comp]
  rfl

/-- The elements of `V₀` are exactly the sine polynomials `sinePolyV n c`. -/
theorem mem_sinePolynomials_iff {v : C₀} :
    v ∈ sinePolynomials ↔ ∃ (n : ℕ) (c : ℕ → ℝ), v = sinePolyV n c := by
  constructor
  · intro hv
    have h : (v : C(Icc (0 : ℝ) π, ℝ)) ∈ span ℝ (range sinMap) := by
      rw [← sinePolynomials_map_subtype]
      exact Submodule.mem_map_of_mem hv
    obtain ⟨n, c, hc⟩ := mem_span_sinMap_iff.1 h
    exact ⟨n, c, Subtype.ext (by rw [coe_sinePolyV, hc])⟩
  · rintro ⟨n, c, rfl⟩
    exact sinePolyV_mem n c

/-- The sines are linearly independent in `C₀[0, π]`. -/
theorem linearIndependent_sinV : LinearIndependent ℝ sinV :=
  LinearIndependent.of_comp C₀.subtype linearIndependent_sinMap

/-- The linear map `sin ((k + 1) x) ↦ -ν (k + 1)² sin ((k + 1) x)` on the sine polynomials, the
underlying map of `heatOperator`. -/
noncomputable def heatOperatorAux (ν : ℝ) : sinePolynomials →ₗ[ℝ] C₀ :=
  (Module.Basis.span linearIndependent_sinV).constr ℝ fun k => (-ν * ((k : ℝ) + 1) ^ 2) • sinV k

/-- **Example 6.2.4, the operator `L`**: `L = ν ∂²/∂x²` with domain `V₀`, the finite sine
polynomials, as a partially defined linear map `C₀ →ₗ.[ℝ] C₀`.

It is presented through its action on the basis `sin ((k + 1) x)` of `V₀`, which it multiplies
by `-ν (k + 1)²`, which is what `ν ∂²/∂x²` does to it; `heatOperator_apply_eq_laplacian` records
that on every element of `V₀` it is indeed `ν` times the second derivative. The domain is the
sine polynomials rather than all of `C² ∩ C₀`, because well-posedness (Definition 6.2.2) asks
for a solution from *every* initial value in the domain, and the book produces one only for
the sine polynomials, by the explicit formula (6.2.7). -/
noncomputable def heatOperator (ν : ℝ) : C₀ →ₗ.[ℝ] C₀ := ⟨sinePolynomials, heatOperatorAux ν⟩

variable {ν : ℝ}

@[simp]
theorem heatOperator_domain : (heatOperator ν).domain = sinePolynomials := rfl

/-- `L` acts through its underlying linear map `heatOperatorAux`. -/
theorem heatOperator_apply (x : sinePolynomials) : heatOperator ν x = heatOperatorAux ν x := rfl

/-- `L (sin ((k + 1) x)) = -ν (k + 1)² sin ((k + 1) x)`. -/
theorem heatOperatorAux_sinV (k : ℕ) (hk : sinV k ∈ sinePolynomials) :
    heatOperatorAux ν ⟨sinV k, hk⟩ = (-ν * ((k : ℝ) + 1) ^ 2) • sinV k := by
  have h : (⟨sinV k, hk⟩ : sinePolynomials) = Module.Basis.span linearIndependent_sinV k :=
    Subtype.ext (by rw [Module.Basis.span_apply])
  rw [heatOperatorAux, h]
  exact Module.Basis.constr_basis (Module.Basis.span linearIndependent_sinV) ℝ
    (fun k => (-ν * ((k : ℝ) + 1) ^ 2) • sinV k) k

/-- `L` on a sine polynomial: `L (∑ c j sin ((j + 1) x)) = ∑ c j (-ν (j + 1)²) sin ((j + 1) x)`. -/
theorem heatOperatorAux_sinePolyV (n : ℕ) (c : ℕ → ℝ) (h : sinePolyV n c ∈ sinePolynomials) :
    heatOperatorAux ν ⟨sinePolyV n c, h⟩
      = sinePolyV n fun j => c j * (-ν * ((j : ℝ) + 1) ^ 2) := by
  have hmem : ∀ j, sinV j ∈ sinePolynomials := fun j => subset_span ⟨j, rfl⟩
  have e : (⟨sinePolyV n c, h⟩ : sinePolynomials)
      = ∑ j ∈ Finset.range n, c j • (⟨sinV j, hmem j⟩ : sinePolynomials) :=
    Subtype.ext (by simp only [sinePolyV, Submodule.coe_sum, Submodule.coe_smul])
  rw [e, map_sum]
  simp only [map_smul, heatOperatorAux_sinV, sinePolyV, smul_smul]

/-- `L (∑ c j sin ((j + 1) x)) = ∑ c j (-ν (j + 1)²) sin ((j + 1) x)`, for the partial map. -/
theorem heatOperator_sinePolyV (n : ℕ) (c : ℕ → ℝ) (h : sinePolyV n c ∈ sinePolynomials) :
    heatOperator ν ⟨sinePolyV n c, h⟩ = sinePolyV n fun j => c j * (-ν * ((j : ℝ) + 1) ^ 2) :=
  heatOperatorAux_sinePolyV n c h

/-- The value of a sine polynomial of `C₀` at a point. -/
theorem sinePolyV_apply (n : ℕ) (c : ℕ → ℝ) (x : Icc (0 : ℝ) π) :
    (sinePolyV n c : C(Icc (0 : ℝ) π, ℝ)) x
      = ∑ j ∈ Finset.range n, c j * Real.sin (((j : ℝ) + 1) * (x : ℝ)) := by
  rw [coe_sinePolyV, sinePolynomial_apply]

/-- **`L` is `ν ∂²/∂x²`**: on a sine polynomial `v`, `(L v) (x) = ν Δ v (x)` at every interior
point, the second derivative being that of the (smooth) sine polynomial `v` read as a function
on the line. -/
theorem heatOperatorAux_apply_eq_laplacian (n : ℕ) (c : ℕ → ℝ)
    (h : sinePolyV n c ∈ sinePolynomials) (x : Icc (0 : ℝ) π) :
    (heatOperatorAux ν ⟨sinePolyV n c, h⟩ : C(Icc (0 : ℝ) π, ℝ)) x
      = ν * Δ (fun y : ℝ => ∑ j ∈ Finset.range n, c j * Real.sin (((j : ℝ) + 1) * y)) (x : ℝ) := by
  rw [heatOperatorAux_sinePolyV, sinePolyV_apply, ← Heat.sineSeries_zero_nu_eq n c 0,
    Heat.laplacian_sineSeries_fst, Heat.sineSeriesDerivX_two, mul_neg, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [neg_zero, zero_mul, Real.exp_zero]
  ring

/-- The same for the partial map `L`. -/
theorem heatOperator_apply_eq_laplacian (n : ℕ) (c : ℕ → ℝ)
    (h : sinePolyV n c ∈ sinePolynomials) (x : Icc (0 : ℝ) π) :
    (heatOperator ν ⟨sinePolyV n c, h⟩ : C(Icc (0 : ℝ) π, ℝ)) x
      = ν * Δ (fun y : ℝ => ∑ j ∈ Finset.range n, c j * Real.sin (((j : ℝ) + 1) * y)) (x : ℝ) :=
  heatOperatorAux_apply_eq_laplacian n c h x

/-! #### The solution (6.2.7) -/

/-- **(6.2.7), the solution for a sine-polynomial initial value**: for
`u₀ = ∑_{j < n} b j sin ((j + 1) x)`, the curve
`u (t) = ∑_{j < n} b j exp (-ν (j + 1)² t) sin ((j + 1) x)` in `C₀[0, π]`. -/
noncomputable def sineSolution (ν : ℝ) (n : ℕ) (b : ℕ → ℝ) (t : ℝ) : C₀ :=
  sinePolyV n fun j => b j * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * t)

/-- At `t = 0` the solution (6.2.7) is its initial value `∑ b j sin ((j + 1) x)`. -/
theorem sineSolution_zero (n : ℕ) (b : ℕ → ℝ) : sineSolution ν n b 0 = sinePolyV n b := by
  simp [sineSolution]

/-- The solution (6.2.7) read pointwise is the sine series `Heat.sineSeries`. -/
theorem sineSolution_apply (n : ℕ) (b : ℕ → ℝ) (t : ℝ) (x : Icc (0 : ℝ) π) :
    (sineSolution ν n b t : C(Icc (0 : ℝ) π, ℝ)) x = Heat.sineSeries ν n b ((x : ℝ), t) := by
  rw [sineSolution, sinePolyV_apply, Heat.sineSeries]

/-- The solution (6.2.7) stays in `V₀`. -/
theorem sineSolution_mem (n : ℕ) (b : ℕ → ℝ) (t : ℝ) :
    sineSolution ν n b t ∈ sinePolynomials := sinePolyV_mem _ _

/-- The curve (6.2.7) is differentiable, with derivative `L u (t)`. -/
theorem hasDerivAt_sineSolution (n : ℕ) (b : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (sineSolution ν n b) (heatOperator ν ⟨sineSolution ν n b t, sineSolution_mem n b t⟩)
      t := by
  rw [show heatOperator ν ⟨sineSolution ν n b t, sineSolution_mem n b t⟩
      = sinePolyV n fun j => b j * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * t) * (-ν * ((j : ℝ) + 1) ^ 2)
    from heatOperator_sinePolyV _ _ _]
  unfold sineSolution sinePolyV
  refine HasDerivAt.fun_sum (A := fun j s => (b j * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * s)) • sinV j)
    fun j _ => ?_
  have h1 : HasDerivAt (fun s : ℝ => -ν * ((j : ℝ) + 1) ^ 2 * s) (-ν * ((j : ℝ) + 1) ^ 2) t :=
    (hasDerivAt_id t).const_mul (-ν * ((j : ℝ) + 1) ^ 2) |>.congr_deriv (mul_one _)
  have h2 := (((Real.hasDerivAt_exp _).comp t h1).const_mul (b j)).smul_const (sinV j)
  refine h2.congr_deriv ?_
  simp only
  ring_nf

/-- **(6.2.7) solves (6.2.4)**: for the initial value `∑_{j < n} b j sin ((j + 1) x) ∈ V₀`, the
curve `sineSolution ν n b` is a solution in the sense of Definition 6.2.1, on every horizon. -/
theorem isSolution_sineSolution (T : ℝ) (n : ℕ) (b : ℕ → ℝ) :
    IsSolution (heatOperator ν) T (sinePolyV n b) (sineSolution ν n b) := by
  rw [isSolution_iff]
  exact ⟨sineSolution_zero n b, fun t _ =>
    ⟨sineSolution_mem n b t, (hasDerivAt_sineSolution n b t).hasDerivWithinAt⟩⟩

/-! #### The maximum principle and well-posedness -/

/-- A solution of the abstract problem read as a function of `(x, t)`: `U (x, t) = u (t) (x)`,
the space variable clamped to `[0, π]`. -/
private noncomputable def spaceTime (u : ℝ → C₀) (p : ℝ × ℝ) : ℝ :=
  (u p.2 : C(Icc (0 : ℝ) π, ℝ)) (projIcc 0 π Real.pi_pos.le p.1)

/-- Evaluation at a point of `[0, π]`, as a bounded linear functional on `C₀`. -/
private noncomputable def evalC₀ (x : Icc (0 : ℝ) π) : C₀ →L[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ x).comp C₀.subtypeL

private theorem evalC₀_apply (x : Icc (0 : ℝ) π) (v : C₀) :
    evalC₀ x v = (v : C(Icc (0 : ℝ) π, ℝ)) x := rfl

/-- **Every solution with values in `V₀` is a classical solution of the heat equation** on the
cylinder `(0, π) × (0, T)`, in the sense of `Heat.IsClassicalSolution`: continuity on the closed
cylinder comes from the continuity of `t ↦ u (t)` in the maximum norm, differentiability in `t`
from the derivative of Definition 6.2.1 evaluated at `x`, and the equation from
`L = ν ∂²/∂x²` on the sine polynomials. -/
private theorem isClassicalSolution_of_isSolution {T : ℝ} {u₀ : C₀} {u : ℝ → C₀}
    (hu : FiniteDifference.IsSolution (heatOperator ν) T u₀ u) :
    Heat.IsClassicalSolution ν (Ioo 0 π) T (spaceTime u) := by
  have hcl : closure (Ioo (0 : ℝ) π) = Icc 0 π := closure_Ioo Real.pi_pos.ne
  -- the representation of `u t` as a sine polynomial, at every time
  have hrep : ∀ t ∈ Icc (0 : ℝ) T, ∃ (n : ℕ) (c : ℕ → ℝ), u t = sinePolyV n c :=
    fun t ht => mem_sinePolynomials_iff.1 (hu.2 t ht).1
  -- the derivative of `u` at an interior time
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) T, ∃ h : u t ∈ sinePolynomials,
      HasDerivAt u (heatOperator ν ⟨u t, h⟩) t := fun t ht => by
    obtain ⟨h, hd⟩ := hu.2 t (Ioo_subset_Icc_self ht)
    exact ⟨h, hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩
  refine ⟨?_, fun x _ t ht => ?_, fun x hx t _ => ?_, fun x hx t ht => ?_⟩
  · -- continuity on the closed cylinder
    have hcont : ContinuousOn u (Icc 0 T) := fun t ht =>
      (hu.2 t ht).2.continuousWithinAt
    have h1 : ContinuousOn (fun p : ℝ × ℝ => ((u p.2 : C(Icc (0 : ℝ) π, ℝ)),
        projIcc 0 π Real.pi_pos.le p.1)) (closure (Ioo 0 π) ×ˢ Icc 0 T) := by
      refine ContinuousOn.prodMk ?_ (continuous_projIcc.comp continuous_fst).continuousOn
      exact continuous_subtype_val.comp_continuousOn
        (hcont.comp continuous_snd.continuousOn fun p hp => hp.2)
    exact continuous_eval.comp_continuousOn h1
  · -- differentiability in `t`
    obtain ⟨h, hd⟩ := hderiv t ht
    exact ((evalC₀ (projIcc 0 π Real.pi_pos.le x)).hasFDerivAt.comp_hasDerivAt t
      hd).differentiableAt
  · -- `C²` in `x`: near `x ∈ (0, π)`, the slice is a sine polynomial
    obtain ⟨n, c, hc⟩ := hrep t (Ioo_subset_Icc_self ‹_›)
    have heq : (fun y => spaceTime u (y, t))
        =ᶠ[𝓝 x] fun y => Heat.sineSeries 0 n c (y, 0) := by
      filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
      simp only [spaceTime, hc, coe_sinePolyV, projIcc_of_mem _ hy, sinePolynomial_apply]
      exact (congrFun (Heat.sineSeries_zero_nu_eq n c 0) y).symm
    exact ((Heat.contDiff_sineSeries_fst (ν := 0) (n := n) (b := c) 0).contDiffAt
      ).congr_of_eventuallyEq heq
  · -- the equation
    obtain ⟨h, hd⟩ := hderiv t ht
    obtain ⟨n, c, hc⟩ := hrep t (Ioo_subset_Icc_self ht)
    have hdx : HasDerivAt (fun s => spaceTime u (x, s))
        (evalC₀ (projIcc 0 π Real.pi_pos.le x) (heatOperator ν ⟨u t, h⟩)) t :=
      (evalC₀ (projIcc 0 π Real.pi_pos.le x)).hasFDerivAt.comp_hasDerivAt t hd
    rw [hdx.deriv]
    have hval : evalC₀ (projIcc 0 π Real.pi_pos.le x) (heatOperator ν ⟨u t, h⟩)
        = ν * Δ (fun y : ℝ => ∑ j ∈ Finset.range n, c j * Real.sin (((j : ℝ) + 1) * y)) x := by
      have e : (⟨u t, h⟩ : sinePolynomials) = ⟨sinePolyV n c, hc ▸ h⟩ := Subtype.ext hc
      refine (congrArg (fun z : sinePolynomials =>
        evalC₀ (projIcc 0 π Real.pi_pos.le x) (heatOperatorAux ν z)) e).trans ?_
      rw [evalC₀_apply, heatOperatorAux_apply_eq_laplacian,
        projIcc_of_mem _ (Ioo_subset_Icc_self hx)]
    rw [hval]
    congr 1
    refine Filter.EventuallyEq.eq_of_nhds (laplacian_congr_nhds ?_)
    filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
    simp only [spaceTime, hc, coe_sinePolyV, projIcc_of_mem _ hy, sinePolynomial_apply]

/-- **The maximum principle for the abstract problem**: every solution of (6.2.4) in the sense
of Definition 6.2.1, on a horizon `T ≥ 0` and for `ν > 0`, satisfies
`max_x |u (x, t)| ≤ max_x |u₀ (x)|`, i.e. `‖u (t)‖ ≤ ‖u₀‖`, for `t ∈ [0, T]`. -/
theorem norm_le_of_isSolution (hν : 0 < ν) {T : ℝ} {u₀ : C₀} {u : ℝ → C₀}
    (hu : IsSolution (heatOperator ν) T u₀ u) : ∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ ‖u₀‖ := by
  rw [isSolution_iff] at hu
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | htpos
  · rw [hu.1]
  have hT : 0 < T := htpos.trans_le ht.2
  have hcl : closure (Ioo (0 : ℝ) π) = Icc 0 π := closure_Ioo Real.pi_pos.ne
  have hfr : frontier (Ioo (0 : ℝ) π) = {0, π} := frontier_Ioo Real.pi_pos
  have hbound := (isClassicalSolution_of_isSolution hu).abs_le_of_eq_zero_frontier isOpen_Ioo
    (Metric.isBounded_Ioo 0 π) hν hT (M := ‖u₀‖) ?_ ?_
  · rw [← Submodule.norm_coe]
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_
    have := hbound x (by rw [hcl]; exact x.2) t ht
    rw [spaceTime, projIcc_val] at this
    rw [Real.norm_eq_abs]
    exact this
  · intro x hx s _
    rw [hfr] at hx
    rcases hx with rfl | rfl
    · change (u s : C(Icc (0 : ℝ) π, ℝ)) (projIcc 0 π Real.pi_pos.le 0) = 0
      rw [projIcc_left]
      exact (u s).2.1
    · change (u s : C(Icc (0 : ℝ) π, ℝ)) (projIcc 0 π Real.pi_pos.le π) = 0
      rw [projIcc_right]
      exact (u s).2.2
  · intro y hy
    rw [spaceTime, hu.1, ← Real.norm_eq_abs, ← Submodule.norm_coe]
    exact ContinuousMap.norm_coe_le_norm _ _

/-- **Example 6.2.4, the well-posedness of the heat equation (6.2.4)** in `V = C₀[0, π]` with
`L = ν ∂²/∂x²` on the sine polynomials `V₀` (6.2.5): the problem is well posed in the sense of
Definition 6.2.2, with stability constant `c₀ = 1`. Existence is the explicit solution (6.2.7),
`isSolution_sineSolution`; uniqueness and the continuous dependence
`sup_t ‖u (t) - ū (t)‖ ≤ ‖u₀ - ū₀‖` are the maximum principle `norm_le_of_isSolution` applied to
the difference of two solutions. Consequently the solution operators `S (t) : V₀ ⊆ V → V` are
bounded by `1` (`example_6_2_4_norm_solutionOperator_le`). -/
theorem example_6_2_4 (hν : 0 < ν) (T : ℝ) : IsWellPosed (heatOperator ν) T 1 := by
  rw [isWellPosed_iff]
  refine ⟨fun u₀ hu₀ => ?_, fun u₀ ū₀ u ū hu hū t ht => ?_⟩
  · obtain ⟨n, c, rfl⟩ := mem_sinePolynomials_iff.1 hu₀
    exact ⟨sineSolution ν n c, (isSolution_iff _ _ _ _).1 (isSolution_sineSolution T n c)⟩
  · have h := norm_le_of_isSolution hν ((isSolution_iff _ _ _ _).2 (hu.sub hū)) t ht
    rwa [one_mul]

/-- **Example 6.2.4, the density of `V₀` in `V`** (the book's Exercise 6.2.1): the finite sine
polynomials are dense in `C₀[0, π]` for the maximum norm. -/
theorem example_6_2_4_dense : Dense (sinePolynomials : Set C₀) := by
  refine Metric.dense_iff.2 fun v ε hε => ?_
  obtain ⟨p, hp, hvp⟩ := exists_mem_span_sinMap_norm_sub_lt v.2.1 v.2.2 hε
  obtain ⟨n, c, rfl⟩ := mem_span_sinMap_iff.1 hp
  refine ⟨sinePolyV n c, ?_, sinePolyV_mem n c⟩
  rw [Metric.mem_ball, dist_eq_norm, ← Submodule.norm_coe, Submodule.coe_sub, coe_sinePolyV,
    norm_sub_rev]
  exact hvp

/-- The domain of `L` is dense in `V`. -/
theorem dense_heatOperator_domain : Dense ((heatOperator ν).domain : Set C₀) :=
  example_6_2_4_dense

/-- **Example 6.2.4, the solution operators**: `S (t) = solutionOperator …` of Definition 6.2.3
for the heat equation satisfies `‖S (t)‖ ≤ 1` on `[0, T]`, the bound
`max_x |u (x, t)| ≤ max_x |u₀ (x)|` read on the extended operators. -/
theorem example_6_2_4_norm_solutionOperator_le (hν : 0 < ν) {T : ℝ} (hT : 0 ≤ T) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖solutionOperator (heatOperator ν) dense_heatOperator_domain hT zero_le_one
      (example_6_2_4 hν T) t‖ ≤ 1 :=
  norm_solutionOperator_le _ _ _ _ _

/-- **Example 6.2.4, (6.2.7) through the solution operators**: for the initial value
`u₀ = ∑_{j < n} b j sin ((j + 1) x)`, `S (t) u₀` is the sine series (6.2.7). -/
theorem example_6_2_4_solutionOperator_apply (hν : 0 < ν) {T : ℝ} (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (n : ℕ) (b : ℕ → ℝ) :
    solutionOperator (heatOperator ν) dense_heatOperator_domain hT zero_le_one
      (example_6_2_4 hν T) t (sinePolyV n b) = sineSolution ν n b t :=
  solutionOperator_apply _ _ _ _ _ ht (sinePolyV_mem n b) _ (isSolution_sineSolution T n b)

/-! ### Examples 6.2.8 and 6.2.13: the forward and backward schemes on `C₀[0, π]` -/

section Schemes

/-- The odd `2π`-periodic extension of `v ∈ C₀[0, π]`, the `ṽ` of Example 6.2.8. -/
noncomputable abbrev ext (v : C₀) : ℝ → ℝ := oddPeriodicExtend (v : C(Icc (0 : ℝ) π, ℝ))

/-- The extension `ṽ` is continuous. -/
theorem continuous_ext (v : C₀) : Continuous (ext v) := continuous_oddPeriodicExtend v.2.1 v.2.2

/-- The extension `ṽ` is odd. -/
theorem ext_neg (v : C₀) (x : ℝ) : ext v (-x) = -ext v x := oddPeriodicExtend_neg v.2.1 v.2.2 x

/-- The extension `ṽ` agrees with `v` on `[0, π]`. -/
theorem ext_of_mem (v : C₀) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) π) :
    ext v x = (v : C(Icc (0 : ℝ) π, ℝ)) ⟨x, hx⟩ := oddPeriodicExtend_of_mem v.2.2 hx

/-- The extension `ṽ` is bounded by `‖v‖`. -/
theorem abs_ext_le (v : C₀) (x : ℝ) : |ext v x| ≤ ‖v‖ := abs_oddPeriodicExtend_le _ x

/-- The extension of a sine polynomial is the sine polynomial on the whole line. -/
theorem ext_sinePolyV (n : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    ext (sinePolyV n c) x = ∑ j ∈ Finset.range n, c j * Real.sin (((j : ℝ) + 1) * x) := by
  rw [ext, coe_sinePolyV, oddPeriodicExtend_sinePolynomial]

/-- The extension of the solution (6.2.7) at time `t` is the sine series `Heat.sineSeries`. -/
theorem ext_sineSolution (n : ℕ) (b : ℕ → ℝ) (t x : ℝ) :
    ext (sineSolution ν n b t) x = Heat.sineSeries ν n b (x, t) := by
  rw [sineSolution, ext_sinePolyV, Heat.sineSeries]

/-- The translated sum `v ↦ ṽ (· + Δx) + ṽ (· - Δx)` on `C₀[0, π]`, as a function: the operator
common to the forward and backward schemes of Example 6.2.8. It maps `C₀` to itself because the
extension is odd about `0` and about `π`. -/
noncomputable def translateSumFun (Δx : ℝ) (v : C₀) : C₀ :=
  ⟨⟨fun x => ext v ((x : ℝ) + Δx) + ext v ((x : ℝ) - Δx), by
      have hc := continuous_ext v
      exact (hc.comp (continuous_subtype_val.add continuous_const)).add
        (hc.comp (continuous_subtype_val.sub continuous_const))⟩, by
    refine ⟨?_, ?_⟩
    · change ext v ((0 : ℝ) + Δx) + ext v ((0 : ℝ) - Δx) = 0
      rw [zero_add, zero_sub, ext_neg, add_neg_cancel]
    · change ext v (π + Δx) + ext v (π - Δx) = 0
      have h : ext v (π + Δx) = -ext v (π - Δx) := by
        have hp := (oddPeriodicExtend_periodic (v : C(Icc (0 : ℝ) π, ℝ))).sub_eq (π + Δx)
        rw [show π + Δx - 2 * π = -(π - Δx) by ring] at hp
        rw [ext, ← hp, ← ext, ext_neg]
      rw [h, neg_add_cancel]⟩

/-- The value of the translated sum at a point. -/
theorem translateSumFun_apply (Δx : ℝ) (v : C₀) (x : Icc (0 : ℝ) π) :
    (translateSumFun Δx v : C(Icc (0 : ℝ) π, ℝ)) x = ext v ((x : ℝ) + Δx) + ext v ((x : ℝ) - Δx) :=
  rfl

/-- The translated sum is bounded by `2 ‖v‖`. -/
theorem norm_translateSumFun_le (Δx : ℝ) (v : C₀) : ‖translateSumFun Δx v‖ ≤ 2 * ‖v‖ := by
  rw [← Submodule.norm_coe]
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
  rw [translateSumFun_apply, Real.norm_eq_abs]
  calc |ext v ((x : ℝ) + Δx) + ext v ((x : ℝ) - Δx)|
      ≤ |ext v ((x : ℝ) + Δx)| + |ext v ((x : ℝ) - Δx)| := abs_add_le _ _
    _ ≤ ‖v‖ + ‖v‖ := add_le_add (abs_ext_le v _) (abs_ext_le v _)
    _ = 2 * ‖v‖ := by ring

/-- The translated sum `v ↦ ṽ (· + Δx) + ṽ (· - Δx)` as a bounded operator on `C₀[0, π]`, of norm
at most `2`. -/
noncomputable def translateSum (Δx : ℝ) : C₀ →L[ℝ] C₀ :=
  LinearMap.mkContinuous
    { toFun := translateSumFun Δx
      map_add' := fun v w => Subtype.ext (ContinuousMap.ext fun x => by
        simp only [translateSumFun_apply, Submodule.coe_add, ContinuousMap.add_apply, ext,
          oddPeriodicExtend_add]
        ring)
      map_smul' := fun a v => Subtype.ext (ContinuousMap.ext fun x => by
        simp only [translateSumFun_apply, Submodule.coe_smul, ContinuousMap.smul_apply, ext,
          oddPeriodicExtend_smul, RingHom.id_apply, smul_eq_mul]
        ring) }
    2 (norm_translateSumFun_le Δx)

/-- The value of the translated sum at a point. -/
theorem translateSum_apply (Δx : ℝ) (v : C₀) (x : Icc (0 : ℝ) π) :
    (translateSum Δx v : C(Icc (0 : ℝ) π, ℝ)) x = ext v ((x : ℝ) + Δx) + ext v ((x : ℝ) - Δx) :=
  rfl

/-- `‖ṽ (· + Δx) + ṽ (· - Δx)‖ ≤ 2 ‖v‖`, as an operator norm bound. -/
theorem norm_translateSum_le (Δx : ℝ) : ‖translateSum Δx‖ ≤ 2 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

/-- **Example 6.2.8, the forward scheme as an operator on `C₀[0, π]`**:
`C (Δt) v (x) = (1 - 2r) v (x) + r [ṽ (x + Δx) + ṽ (x - Δx)]` with `Δx = √(ν Δt / r)` and `ṽ`
the odd `2π`-periodic extension of `v`; `r = ν Δt / Δx²` is the mesh ratio, held fixed as
`Δt → 0`. -/
noncomputable def forwardScheme (ν r Δt : ℝ) : C₀ →L[ℝ] C₀ :=
  (1 - 2 * r) • (1 : C₀ →L[ℝ] C₀) + r • translateSum (Real.sqrt (ν * Δt / r))

/-- The value of `C (Δt) v` at a point, the formula of Example 6.2.8. -/
theorem forwardScheme_apply (ν r Δt : ℝ) (v : C₀) (x : Icc (0 : ℝ) π) :
    (forwardScheme ν r Δt v : C(Icc (0 : ℝ) π, ℝ)) x
      = (1 - 2 * r) * (v : C(Icc (0 : ℝ) π, ℝ)) x
        + r * (ext v ((x : ℝ) + Real.sqrt (ν * Δt / r))
          + ext v ((x : ℝ) - Real.sqrt (ν * Δt / r))) := by
  simp only [forwardScheme, add_apply, smul_apply, one_apply_eq_self, Submodule.coe_add,
    Submodule.coe_smul, ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul,
    translateSum_apply]

/-- **(6.2.8)**: `‖C (Δt)‖ ≤ |1 - 2r| + 2r`, so the forward family is uniformly bounded. -/
theorem norm_forwardScheme_le {r : ℝ} (hr : 0 ≤ r) (ν Δt : ℝ) :
    ‖forwardScheme ν r Δt‖ ≤ |1 - 2 * r| + 2 * r := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) ContinuousLinearMap.norm_id_le
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_translateSum_le _) hr

/-- The forward family is uniformly bounded by `|1 - 2r| + 2r` on every range of step sizes. -/
theorem forall_norm_forwardScheme_le {r : ℝ} (hr : 0 ≤ r) (ν Δ₀ : ℝ) :
    ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, ‖forwardScheme ν r Δt‖ ≤ |1 - 2 * r| + 2 * r :=
  fun Δt _ => norm_forwardScheme_le hr ν Δt

/-! #### Consistency of the forward scheme (Example 6.2.8) -/

/-- The Taylor-expansion constant of Example 6.2.8 for the initial value `∑ b j sin ((j + 1) x)`:
`(∑ |b j| (ν (j + 1)²)²) / 2 + ν² (∑ |b j| (j + 1)⁴) / (12 r)`, the sum of the bounds on
`u_tt / 2` and on `(ν² / 12 r) u_xxxx`. -/
noncomputable def forwardConsistencyConst (ν r : ℝ) (n : ℕ) (b : ℕ → ℝ) : ℝ :=
  (∑ j ∈ Finset.range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2) / 2
    + ν ^ 2 * (∑ j ∈ Finset.range n, |b j| * ((j : ℝ) + 1) ^ 4) / (12 * r)

/-- The consistency constant is nonnegative. -/
theorem forwardConsistencyConst_nonneg {ν r : ℝ} (hr : 0 ≤ r) (n : ℕ) (b : ℕ → ℝ) :
    0 ≤ forwardConsistencyConst ν r n b := by
  unfold forwardConsistencyConst
  have h1 : 0 ≤ ∑ j ∈ Finset.range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2 :=
    Finset.sum_nonneg fun j _ => by positivity
  have h2 : 0 ≤ ∑ j ∈ Finset.range n, |b j| * ((j : ℝ) + 1) ^ 4 :=
    Finset.sum_nonneg fun j _ => by positivity
  positivity

/-- **The local truncation error of the forward scheme on the solution (6.2.7)**: by the Taylor
expansions of Example 6.2.8, `‖C (Δt) u (t) - u (t + Δt)‖ ≤ c Δt²` for `t ≥ 0` and `Δt ≥ 0`,
with `c = forwardConsistencyConst ν r n b`. -/
theorem norm_forwardScheme_sineSolution_sub_le (hν : 0 < ν) {r : ℝ} (hr : 0 < r) (n : ℕ)
    (b : ℕ → ℝ) {t Δt : ℝ} (ht : 0 ≤ t) (hΔt : 0 ≤ Δt) :
    ‖forwardScheme ν r Δt (sineSolution ν n b t) - sineSolution ν n b (t + Δt)‖
      ≤ forwardConsistencyConst ν r n b * Δt ^ 2 := by
  set Δx := Real.sqrt (ν * Δt / r) with hΔx
  have hΔx0 : 0 ≤ Δx := Real.sqrt_nonneg _
  have hΔx2 : Δx ^ 2 = ν * Δt / r := Real.sq_sqrt (by positivity)
  have hrΔx : r * Δx ^ 2 = ν * Δt := by rw [hΔx2]; field_simp
  set Mt := ∑ j ∈ Finset.range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2 with hMt
  set Mx := ∑ j ∈ Finset.range n, |b j| * ((j : ℝ) + 1) ^ 4 with hMx
  have hMt0 : 0 ≤ Mt := Finset.sum_nonneg fun j _ => by positivity
  have hMx0 : 0 ≤ Mx := Finset.sum_nonneg fun j _ => by positivity
  rw [← Submodule.norm_coe]
  refine (ContinuousMap.norm_le _ (by
    have := forwardConsistencyConst_nonneg (ν := ν) hr.le n b
    positivity)).2 fun x => ?_
  rw [Submodule.coe_sub, ContinuousMap.sub_apply, forwardScheme_apply, ext_sineSolution,
    ext_sineSolution, sineSolution_apply, sineSolution_apply, Real.norm_eq_abs]
  -- the identity `C (Δt) u (t) - u (t + Δt) = r B - A`
  set U := Heat.sineSeries ν n b with hU
  have hUt : Heat.sineSeriesDerivT ν n b 1 ((x : ℝ), t)
      = ν * Heat.sineSeriesDerivX ν n b 2 ((x : ℝ), t) := Heat.sineSeriesDerivT_one _
  have e : (1 - 2 * r) * U ((x : ℝ), t) + r * (U ((x : ℝ) + Δx, t) + U ((x : ℝ) - Δx, t))
        - U ((x : ℝ), t + Δt)
      = r * (U ((x : ℝ) + Δx, t) - 2 * U ((x : ℝ), t) + U ((x : ℝ) - Δx, t)
          - Δx ^ 2 * Heat.sineSeriesDerivX ν n b 2 ((x : ℝ), t))
        - (U ((x : ℝ), t + Δt) - U ((x : ℝ), t)
          - Δt * Heat.sineSeriesDerivT ν n b 1 ((x : ℝ), t)) := by
    rw [hUt]
    linear_combination (Heat.sineSeriesDerivX ν n b 2 ((x : ℝ), t)) * hrΔx
  rw [e]
  have hA := Heat.abs_sineSeries_sub_forward_time_le (ν := ν) (n := n) (b := b) hν.le (x := x) ht
    hΔt
  have hB := Heat.abs_sineSeries_centred_sub_le (ν := ν) (n := n) (b := b) hν.le (x := x) ht hΔx0
  have hΔx4 : r * Δx ^ 4 = ν ^ 2 * Δt ^ 2 / r := by
    rw [show Δx ^ 4 = (Δx ^ 2) ^ 2 by ring, hΔx2]; field_simp
  calc _ ≤ r * (Mx * Δx ^ 4 / 12) + Mt * Δt ^ 2 / 2 := by
        refine (abs_sub _ _).trans (add_le_add ?_ hA)
        rw [abs_mul, abs_of_pos hr]
        exact mul_le_mul_of_nonneg_left hB hr.le
    _ = forwardConsistencyConst ν r n b * Δt ^ 2 := by
        rw [forwardConsistencyConst, ← hMt, ← hMx,
          show r * (Mx * Δx ^ 4 / 12) = (r * Δx ^ 4) * Mx / 12 by ring, hΔx4]
        field_simp
        ring

/-- **Example 6.2.8, consistency of the forward scheme** with `V_c = V₀`: for every sine polynomial
initial value the local truncation error satisfies `‖[C (Δt) u (t) - u (t + Δt)] / Δt‖ ≤ c Δt`,
so the forward family is consistent (Definition 6.2.7) with the solution operators of the heat
equation on `[0, T]`, for step sizes in `(0, Δ₀]`.

The family is the solution operators of Definition 6.2.3 on the horizon `[0, T]` itself:
Definition 6.2.7 evaluates `S (t + Δt)` for `t + Δt ≤ T` only. -/
theorem example_6_2_8 (hν : 0 < ν) {r : ℝ} (hr : 0 < r) {T Δ₀ : ℝ} (hT : 0 ≤ T) :
    IsConsistent (solutionOperator (heatOperator ν) dense_heatOperator_domain hT zero_le_one
      (example_6_2_4 hν T)) (forwardScheme ν r) T Δ₀ sinePolynomials := by
  refine ⟨example_6_2_4_dense, fun u₀ hu₀ ε hε => ?_⟩
  obtain ⟨n, b, rfl⟩ := mem_sinePolynomials_iff.1 hu₀
  set c := forwardConsistencyConst ν r n b with hc
  have hc0 : 0 ≤ c := forwardConsistencyConst_nonneg hr.le n b
  refine ⟨ε / (c + 1), by positivity, fun Δt hΔt hlt t ht htΔ => ?_⟩
  have htΔT : t + Δt ∈ Icc (0 : ℝ) T := ⟨by linarith [ht.1, hΔt.1], htΔ⟩
  rw [example_6_2_4_solutionOperator_apply hν hT ht, example_6_2_4_solutionOperator_apply hν hT
    htΔT, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hΔt.1, ← div_eq_inv_mul,
    div_le_iff₀ hΔt.1]
  calc ‖forwardScheme ν r Δt (sineSolution ν n b t) - sineSolution ν n b (t + Δt)‖
      ≤ c * Δt ^ 2 := norm_forwardScheme_sineSolution_sub_le hν hr n b ht.1 hΔt.1.le
    _ = (c * Δt) * Δt := by ring
    _ ≤ ε * Δt := by
        refine mul_le_mul_of_nonneg_right ?_ hΔt.1.le
        calc c * Δt ≤ c * (ε / (c + 1)) := mul_le_mul_of_nonneg_left hlt.le hc0
          _ ≤ ε := by
              rw [mul_div_assoc', div_le_iff₀ (by positivity)]
              nlinarith

/-! #### The backward scheme (Example 6.2.8, second half) -/

/-- The operator `Q₁ = (1 + 2r) I - r [ṽ (· + Δx) + ṽ (· - Δx)]` of the backward scheme, the
left-hand side of the implicit relation
`(1 + 2r) u (x, t + Δt) - r [u (x - Δx, t + Δt) + u (x + Δx, t + Δt)] = u (x, t)` of Example 6.2.8,
with `Δx = √(ν Δt / r)`. -/
noncomputable def backwardSchemeInv (ν r Δt : ℝ) : C₀ →L[ℝ] C₀ :=
  (1 + 2 * r) • (1 : C₀ →L[ℝ] C₀) - r • translateSum (Real.sqrt (ν * Δt / r))

/-- The value of `Q₁ v` at a point. -/
theorem backwardSchemeInv_apply (ν r Δt : ℝ) (v : C₀) (x : Icc (0 : ℝ) π) :
    (backwardSchemeInv ν r Δt v : C(Icc (0 : ℝ) π, ℝ)) x
      = (1 + 2 * r) * (v : C(Icc (0 : ℝ) π, ℝ)) x
        - r * (ext v ((x : ℝ) + Real.sqrt (ν * Δt / r))
          + ext v ((x : ℝ) - Real.sqrt (ν * Δt / r))) := by
  simp only [backwardSchemeInv, sub_apply, smul_apply, one_apply_eq_self, Submodule.coe_sub,
    Submodule.coe_smul, ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul,
    translateSum_apply]

/-- `Q₁` is invertible for `r ≥ 0`: `Q₁ = (1 + 2r) (I - B)` with `‖B‖ ≤ 2r / (1 + 2r) < 1`, a
Neumann series. -/
theorem isUnit_backwardSchemeInv {r : ℝ} (hr : 0 ≤ r) (ν Δt : ℝ) :
    IsUnit (backwardSchemeInv ν r Δt) := by
  have h12 : (0 : ℝ) < 1 + 2 * r := by linarith
  have hB : ‖(r / (1 + 2 * r)) • translateSum (Real.sqrt (ν * Δt / r))‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc r / (1 + 2 * r) * ‖translateSum (Real.sqrt (ν * Δt / r))‖ ≤ r / (1 + 2 * r) * 2 :=
          mul_le_mul_of_nonneg_left (norm_translateSum_le _) (by positivity)
      _ < 1 := by rw [div_mul_eq_mul_div, div_lt_one h12]; linarith
  have e : backwardSchemeInv ν r Δt
      = ((1 + 2 * r) • (1 : C₀ →L[ℝ] C₀))
        * (1 - (r / (1 + 2 * r)) • translateSum (Real.sqrt (ν * Δt / r))) := by
    rw [backwardSchemeInv, mul_sub, mul_one, smul_mul_assoc, one_mul, smul_smul,
      mul_div_cancel₀ _ h12.ne']
  rw [e]
  refine IsUnit.mul ?_ (isUnit_one_sub_of_norm_lt_one hB)
  rw [← Algebra.algebraMap_eq_smul_one]
  exact (algebraMap ℝ (C₀ →L[ℝ] C₀)).isUnit_map (isUnit_iff_ne_zero.2 h12.ne')

/-- **Example 6.2.8, the backward scheme as an operator on `C₀[0, π]`**: `C (Δt) = Q₁⁻¹`, the
solution operator of the implicit relation
`(1 + 2r) w (x) - r [w̃ (x - Δx) + w̃ (x + Δx)] = v (x)`. Outside `r ≥ 0` the inverse is Mathlib's
junk value `Ring.inverse`. -/
noncomputable def backwardScheme (ν r Δt : ℝ) : C₀ →L[ℝ] C₀ :=
  Ring.inverse (backwardSchemeInv ν r Δt)

/-- `Q₁ C (Δt) = I` for `r ≥ 0`. -/
theorem backwardSchemeInv_mul_backwardScheme {r : ℝ} (hr : 0 ≤ r) (ν Δt : ℝ) :
    backwardSchemeInv ν r Δt * backwardScheme ν r Δt = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_backwardSchemeInv hr ν Δt)

/-- `C (Δt) Q₁ = I` for `r ≥ 0`. -/
theorem backwardScheme_mul_backwardSchemeInv {r : ℝ} (hr : 0 ≤ r) (ν Δt : ℝ) :
    backwardScheme ν r Δt * backwardSchemeInv ν r Δt = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_backwardSchemeInv hr ν Δt)

/-- `Q₁ (C (Δt) v) = v`: the backward scheme solves its implicit relation. -/
theorem backwardSchemeInv_backwardScheme {r : ℝ} (hr : 0 ≤ r) (ν Δt : ℝ) (v : C₀) :
    backwardSchemeInv ν r Δt (backwardScheme ν r Δt v) = v := by
  rw [← mul_apply_eq_comp, backwardSchemeInv_mul_backwardScheme hr, one_apply_eq_self]

/-- **Example 6.2.8, `‖C (Δt)‖ ≤ 1` for the backward scheme, whatever `r ≥ 0`**: the book's
argument — with `w = C (Δt) v`, `(1 + 2r) w = v + r [w̃ (· - Δx) + w̃ (· + Δx)]` gives
`(1 + 2r) ‖w‖ ≤ ‖v‖ + 2r ‖w‖`. -/
theorem norm_backwardScheme_le {r : ℝ} (hr : 0 ≤ r) (ν Δt : ℝ) : ‖backwardScheme ν r Δt‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul]
  set w := backwardScheme ν r Δt v with hw
  have h12 : (0 : ℝ) < 1 + 2 * r := by linarith
  have hQ : (1 + 2 * r) • w = v + r • translateSum (Real.sqrt (ν * Δt / r)) w := by
    have := backwardSchemeInv_backwardScheme hr ν Δt v
    rw [backwardSchemeInv, sub_apply, smul_apply, one_apply_eq_self, smul_apply] at this
    rw [← this]
    abel
  have hnorm : (1 + 2 * r) * ‖w‖ ≤ ‖v‖ + 2 * r * ‖w‖ := by
    calc (1 + 2 * r) * ‖w‖ = ‖(1 + 2 * r) • w‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos h12]
      _ ≤ ‖v‖ + ‖r • translateSum (Real.sqrt (ν * Δt / r)) w‖ := by
          rw [hQ]; exact norm_add_le _ _
      _ ≤ ‖v‖ + r * (2 * ‖w‖) := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
          exact mul_le_mul_of_nonneg_left (norm_translateSumFun_le _ w) hr
      _ = ‖v‖ + 2 * r * ‖w‖ := by ring
  linarith

/-- The backward family is uniformly bounded by `1` on every range of step sizes. -/
theorem forall_norm_backwardScheme_le {r : ℝ} (hr : 0 ≤ r) (ν Δ₀ : ℝ) :
    ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, ‖backwardScheme ν r Δt‖ ≤ 1 :=
  fun Δt _ => norm_backwardScheme_le hr ν Δt

/-- **The local truncation error of the backward scheme on the solution (6.2.7)**: as
`C (Δt) u (t) - u (t + Δt) = C (Δt) [u (t) - Q₁ u (t + Δt)]` and `‖C (Δt)‖ ≤ 1`, the Taylor
expansions at `(x, t + Δt)` give `‖C (Δt) u (t) - u (t + Δt)‖ ≤ c Δt²` with the same constant
`c = forwardConsistencyConst ν r n b` as for the forward scheme. -/
theorem norm_backwardScheme_sineSolution_sub_le (hν : 0 < ν) {r : ℝ} (hr : 0 < r) (n : ℕ)
    (b : ℕ → ℝ) {t Δt : ℝ} (ht : 0 ≤ t) (hΔt : 0 ≤ Δt) :
    ‖backwardScheme ν r Δt (sineSolution ν n b t) - sineSolution ν n b (t + Δt)‖
      ≤ forwardConsistencyConst ν r n b * Δt ^ 2 := by
  set Δx := Real.sqrt (ν * Δt / r) with hΔx
  have hΔx0 : 0 ≤ Δx := Real.sqrt_nonneg _
  have hΔx2 : Δx ^ 2 = ν * Δt / r := Real.sq_sqrt (by positivity)
  have hrΔx : r * Δx ^ 2 = ν * Δt := by rw [hΔx2]; field_simp
  set Mt := ∑ j ∈ Finset.range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2 with hMt
  set Mx := ∑ j ∈ Finset.range n, |b j| * ((j : ℝ) + 1) ^ 4 with hMx
  have hMt0 : 0 ≤ Mt := Finset.sum_nonneg fun j _ => by positivity
  have hMx0 : 0 ≤ Mx := Finset.sum_nonneg fun j _ => by positivity
  -- the difference is `C (Δt)` of the residual of `u (t + Δt)` in the implicit relation
  have e : backwardScheme ν r Δt (sineSolution ν n b t) - sineSolution ν n b (t + Δt)
      = backwardScheme ν r Δt
          (sineSolution ν n b t - backwardSchemeInv ν r Δt (sineSolution ν n b (t + Δt))) := by
    rw [map_sub, ← mul_apply_eq_comp, backwardScheme_mul_backwardSchemeInv hr.le,
      one_apply_eq_self]
  rw [e]
  refine ((backwardScheme ν r Δt).le_opNorm _).trans ?_
  refine (mul_le_mul_of_nonneg_right (norm_backwardScheme_le hr.le ν Δt) (norm_nonneg _)).trans ?_
  rw [one_mul, ← Submodule.norm_coe]
  refine (ContinuousMap.norm_le _ (by
    have := forwardConsistencyConst_nonneg (ν := ν) hr.le n b
    positivity)).2 fun x => ?_
  rw [Submodule.coe_sub, ContinuousMap.sub_apply, backwardSchemeInv_apply, ext_sineSolution,
    ext_sineSolution, sineSolution_apply, sineSolution_apply, Real.norm_eq_abs]
  set U := Heat.sineSeries ν n b with hU
  have hUt : Heat.sineSeriesDerivT ν n b 1 ((x : ℝ), t + Δt)
      = ν * Heat.sineSeriesDerivX ν n b 2 ((x : ℝ), t + Δt) := Heat.sineSeriesDerivT_one _
  have e2 : U ((x : ℝ), t) - ((1 + 2 * r) * U ((x : ℝ), t + Δt)
        - r * (U ((x : ℝ) + Δx, t + Δt) + U ((x : ℝ) - Δx, t + Δt)))
      = r * (U ((x : ℝ) + Δx, t + Δt) - 2 * U ((x : ℝ), t + Δt) + U ((x : ℝ) - Δx, t + Δt)
          - Δx ^ 2 * Heat.sineSeriesDerivX ν n b 2 ((x : ℝ), t + Δt))
        - (U ((x : ℝ), t + Δt) - U ((x : ℝ), t)
          - Δt * Heat.sineSeriesDerivT ν n b 1 ((x : ℝ), t + Δt)) := by
    rw [hUt]
    linear_combination (Heat.sineSeriesDerivX ν n b 2 ((x : ℝ), t + Δt)) * hrΔx
  rw [e2]
  have hA := Heat.abs_sineSeries_sub_backward_time_le (ν := ν) (n := n) (b := b) hν.le (x := x) ht
    hΔt
  have hB := Heat.abs_sineSeries_centred_sub_le (ν := ν) (n := n) (b := b) hν.le (x := x)
    (by linarith : 0 ≤ t + Δt) hΔx0
  have hΔx4 : r * Δx ^ 4 = ν ^ 2 * Δt ^ 2 / r := by
    rw [show Δx ^ 4 = (Δx ^ 2) ^ 2 by ring, hΔx2]; field_simp
  calc _ ≤ r * (Mx * Δx ^ 4 / 12) + Mt * Δt ^ 2 / 2 := by
        refine (abs_sub _ _).trans (add_le_add ?_ hA)
        rw [abs_mul, abs_of_pos hr]
        exact mul_le_mul_of_nonneg_left hB hr.le
    _ = forwardConsistencyConst ν r n b * Δt ^ 2 := by
        rw [forwardConsistencyConst, ← hMt, ← hMx,
          show r * (Mx * Δx ^ 4 / 12) = (r * Δx ^ 4) * Mx / 12 by ring, hΔx4]
        field_simp
        ring

/-- **Example 6.2.8, consistency of the backward scheme** with `V_c = V₀` — the clause the book
says is "more involved" and leaves to the reader: the same statement as `example_6_2_8` for
`backwardScheme`, from `norm_backwardScheme_sineSolution_sub_le`. -/
theorem example_6_2_8_backward (hν : 0 < ν) {r : ℝ} (hr : 0 < r) {T Δ₀ : ℝ} (hT : 0 ≤ T) :
    IsConsistent (solutionOperator (heatOperator ν) dense_heatOperator_domain hT zero_le_one
      (example_6_2_4 hν T)) (backwardScheme ν r) T Δ₀ sinePolynomials := by
  refine ⟨example_6_2_4_dense, fun u₀ hu₀ ε hε => ?_⟩
  obtain ⟨n, b, rfl⟩ := mem_sinePolynomials_iff.1 hu₀
  set c := forwardConsistencyConst ν r n b with hc
  have hc0 : 0 ≤ c := forwardConsistencyConst_nonneg hr.le n b
  refine ⟨ε / (c + 1), by positivity, fun Δt hΔt hlt t ht htΔ => ?_⟩
  have htΔT : t + Δt ∈ Icc (0 : ℝ) T := ⟨by linarith [ht.1, hΔt.1], htΔ⟩
  rw [example_6_2_4_solutionOperator_apply hν hT ht, example_6_2_4_solutionOperator_apply hν hT
    htΔT, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hΔt.1, ← div_eq_inv_mul,
    div_le_iff₀ hΔt.1]
  calc ‖backwardScheme ν r Δt (sineSolution ν n b t) - sineSolution ν n b (t + Δt)‖
      ≤ c * Δt ^ 2 := norm_backwardScheme_sineSolution_sub_le hν hr n b ht.1 hΔt.1.le
    _ = (c * Δt) * Δt := by ring
    _ ≤ ε * Δt := by
        refine mul_le_mul_of_nonneg_right ?_ hΔt.1.le
        calc c * Δt ≤ c * (ε / (c + 1)) := mul_le_mul_of_nonneg_left hlt.le hc0
          _ ≤ ε := by
              rw [mul_div_assoc', div_le_iff₀ (by positivity)]
              nlinarith

/-! #### Example 6.2.13: the Lax equivalence theorem applied -/

/-- **Example 6.2.13, the forward scheme**: for `r ≤ 1/2`, `‖C (Δt)‖ ≤ 1` by (6.2.8), hence
`‖C (Δt)^m‖ ≤ 1` for all `m` — the scheme is stable — and, being consistent, it is convergent
(6.2.11) by the Lax equivalence theorem: `‖u_{Δt} (·, m_i Δt_i) - u (·, t)‖ → 0` whenever
`m_i Δt_i → t`, for every initial value in `C₀[0, π]`.

The evolution family is that of `example_6_2_8`, the solution operators on `[0, T]`, and the
equivalence theorem is the surface `theorem_6_2_11`. -/
theorem example_6_2_13 (hν : 0 < ν) {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 1 / 2) {T Δ₀ : ℝ}
    (hT : 0 ≤ T) :
    IsStable (forwardScheme ν r) T Δ₀ ∧
      IsConvergent (solutionOperator (heatOperator ν) dense_heatOperator_domain hT zero_le_one
        (example_6_2_4 hν T)) (forwardScheme ν r) T Δ₀ := by
  have hC : ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, ‖forwardScheme ν r Δt‖ ≤ 1 := fun Δt hΔt => by
    refine (norm_forwardScheme_le hr.le ν Δt).trans ?_
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hstab := (isStable_iff _ _ _).2 (FiniteDifference.isStable_of_forall_norm_le_one hC T)
  exact ⟨hstab, (theorem_6_2_11 (heatOperator ν) dense_heatOperator_domain hT zero_le_one
    (example_6_2_4 hν T) hC (example_6_2_8 hν hr hT)).1 hstab⟩

/-- **Example 6.2.13, the backward scheme**: `‖C (Δt)‖ ≤ 1` for every `r`, so the scheme is
unconditionally stable, and, being consistent, unconditionally convergent. -/
theorem example_6_2_13_backward (hν : 0 < ν) {r : ℝ} (hr : 0 < r) {T Δ₀ : ℝ} (hT : 0 ≤ T) :
    IsStable (backwardScheme ν r) T Δ₀ ∧
      IsConvergent (solutionOperator (heatOperator ν) dense_heatOperator_domain hT zero_le_one
        (example_6_2_4 hν T)) (backwardScheme ν r) T Δ₀ := by
  have hC := forall_norm_backwardScheme_le hr.le ν Δ₀
  have hstab := (isStable_iff _ _ _).2 (FiniteDifference.isStable_of_forall_norm_le_one hC T)
  exact ⟨hstab, (theorem_6_2_11 (heatOperator ν) dense_heatOperator_domain hT zero_le_one
    (example_6_2_4 hν T) hC (example_6_2_8_backward hν hr hT)).1 hstab⟩

/-! #### Exercise 6.2.3: the exact norm of the forward scheme -/

section ExactNorm

/-- The test function of Exercise 6.2.3: on `[0, π]`, the plateau `1` on
`[π/2 - Δx, π/2 + Δx]` joined linearly to `0` at the ends, minus twice the hat of height `1` and
half-width `Δx` at `π/2` when `r > 1/2`. It has `|v| ≤ 1`, `v = 1` at `π/2 ± Δx`, and `v = ±1`
at `π/2`, the sign being that of `1 - 2r`. -/
private noncomputable def testFun (r Δx : ℝ) : C(Icc (0 : ℝ) π, ℝ) :=
  ⟨fun x => min 1 (min ((x : ℝ) / (π / 2 - Δx)) ((π - (x : ℝ)) / (π / 2 - Δx)))
    - (if r ≤ 1 / 2 then 0 else 2) * max 0 (1 - |(x : ℝ) - π / 2| / Δx), by fun_prop⟩

private theorem testFun_apply (r Δx : ℝ) (x : Icc (0 : ℝ) π) :
    testFun r Δx x = min 1 (min ((x : ℝ) / (π / 2 - Δx)) ((π - (x : ℝ)) / (π / 2 - Δx)))
      - (if r ≤ 1 / 2 then 0 else 2) * max 0 (1 - |(x : ℝ) - π / 2| / Δx) := rfl

variable {r Δx : ℝ} (hΔx : 0 < Δx) (hΔx' : Δx < π / 2)
include hΔx hΔx'

omit hΔx' in
private theorem hat_eq_zero {y : ℝ} (hy : Δx ≤ |y - π / 2|) :
    max 0 (1 - |y - π / 2| / Δx) = 0 :=
  max_eq_left (by rw [sub_nonpos, one_le_div hΔx]; exact hy)

private theorem testFun_mem_C₀ : testFun r Δx ∈ C₀ := by
  have ha : 0 < π / 2 - Δx := by linarith
  refine ⟨?_, ?_⟩
  · change min 1 (min ((0 : ℝ) / (π / 2 - Δx)) ((π - 0) / (π / 2 - Δx)))
      - (if r ≤ 1 / 2 then 0 else 2) * max 0 (1 - |0 - π / 2| / Δx) = 0
    have h0 : Δx ≤ |(0 : ℝ) - π / 2| := by
      rw [zero_sub, abs_neg, abs_of_pos (by positivity)]; exact hΔx'.le
    rw [hat_eq_zero hΔx h0, zero_div,
      min_eq_left (a := (0 : ℝ)) (b := (π - 0) / (π / 2 - Δx))
        (div_nonneg (by linarith [Real.pi_pos]) ha.le),
      min_eq_right zero_le_one]
    ring
  · change min 1 (min (π / (π / 2 - Δx)) ((π - π) / (π / 2 - Δx)))
      - (if r ≤ 1 / 2 then 0 else 2) * max 0 (1 - |π - π / 2| / Δx) = 0
    have hπ : Δx ≤ |π - π / 2| := by
      rw [show π - π / 2 = π / 2 by ring, abs_of_pos (by positivity)]; exact hΔx'.le
    rw [hat_eq_zero hΔx hπ, sub_self, zero_div,
      min_eq_right (a := π / (π / 2 - Δx)) (b := (0 : ℝ)) (div_nonneg Real.pi_pos.le ha.le),
      min_eq_right zero_le_one]
    ring

private theorem abs_testFun_le (x : Icc (0 : ℝ) π) : |testFun r Δx x| ≤ 1 := by
  have ha : 0 < π / 2 - Δx := by linarith
  rw [testFun_apply]
  set w := min 1 (min ((x : ℝ) / (π / 2 - Δx)) ((π - (x : ℝ)) / (π / 2 - Δx))) with hw
  set h := max 0 (1 - |(x : ℝ) - π / 2| / Δx) with hh
  have hw1 : w ≤ 1 := min_le_left _ _
  have hw0 : 0 ≤ w := le_min zero_le_one (le_min (by have := x.2.1; positivity)
    (by have := x.2.2; exact div_nonneg (by linarith) ha.le))
  have hh0 : 0 ≤ h := le_max_left _ _
  have hh1 : h ≤ 1 := max_le zero_le_one (by
    have : 0 ≤ |(x : ℝ) - π / 2| / Δx := by positivity
    linarith)
  split_ifs with hr
  · rw [zero_mul, sub_zero, abs_le]; constructor <;> linarith
  · -- off the plateau the hat vanishes, on it `w = 1`
    rw [abs_le]
    rcases le_or_gt (|(x : ℝ) - π / 2|) Δx with hin | hout
    · have hw' : w = 1 := by
        rw [hw]
        refine min_eq_left (le_min ?_ ?_)
        · rw [le_div_iff₀ ha]
          have := abs_le.1 hin
          linarith
        · rw [le_div_iff₀ ha]
          have := abs_le.1 hin
          linarith
      rw [hw']
      constructor <;> linarith
    · have hh' : h = 0 := hat_eq_zero hΔx hout.le
      rw [hh', mul_zero, sub_zero]
      exact ⟨by linarith, hw1⟩

private theorem testFun_mid :
    testFun r Δx ⟨π / 2, ⟨by positivity, by linarith [Real.pi_pos]⟩⟩
      = if r ≤ 1 / 2 then 1 else -1 := by
  have ha : 0 < π / 2 - Δx := by linarith
  change min 1 (min (π / 2 / (π / 2 - Δx)) ((π - π / 2) / (π / 2 - Δx)))
    - (if r ≤ 1 / 2 then 0 else 2) * max 0 (1 - |π / 2 - π / 2| / Δx) = _
  have h1 : min 1 (min (π / 2 / (π / 2 - Δx)) ((π - π / 2) / (π / 2 - Δx))) = 1 := by
    refine min_eq_left (le_min ?_ ?_)
    · rw [le_div_iff₀ ha]; linarith
    · rw [le_div_iff₀ ha]; linarith
  rw [h1, sub_self, abs_zero, zero_div, sub_zero, max_eq_right zero_le_one, mul_one]
  split_ifs <;> norm_num

private theorem testFun_mid_add :
    testFun r Δx ⟨π / 2 + Δx, ⟨by positivity, by linarith [Real.pi_pos]⟩⟩ = 1 := by
  have ha : 0 < π / 2 - Δx := by linarith
  change min 1 (min ((π / 2 + Δx) / (π / 2 - Δx)) ((π - (π / 2 + Δx)) / (π / 2 - Δx)))
    - (if r ≤ 1 / 2 then 0 else 2) * max 0 (1 - |π / 2 + Δx - π / 2| / Δx) = 1
  have h1 : Δx ≤ |π / 2 + Δx - π / 2| := by rw [add_sub_cancel_left, abs_of_pos hΔx]
  rw [hat_eq_zero hΔx h1, mul_zero, sub_zero]
  refine min_eq_left (le_min ?_ ?_)
  · rw [le_div_iff₀ ha]; linarith
  · rw [le_div_iff₀ ha]; linarith

private theorem testFun_mid_sub :
    testFun r Δx ⟨π / 2 - Δx, ⟨by linarith, by linarith [Real.pi_pos]⟩⟩ = 1 := by
  have ha : 0 < π / 2 - Δx := by linarith
  change min 1 (min ((π / 2 - Δx) / (π / 2 - Δx)) ((π - (π / 2 - Δx)) / (π / 2 - Δx)))
    - (if r ≤ 1 / 2 then 0 else 2) * max 0 (1 - |π / 2 - Δx - π / 2| / Δx) = 1
  have h1 : Δx ≤ |π / 2 - Δx - π / 2| := by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hΔx]
  rw [hat_eq_zero hΔx h1, mul_zero, sub_zero]
  refine min_eq_left (le_min ?_ ?_)
  · rw [div_self ha.ne']
  · rw [le_div_iff₀ ha]; linarith

omit hΔx hΔx' in
/-- **Exercise 6.2.3, the exact norm of the forward scheme**: `‖C (Δt)‖ = |1 - 2r| + 2r` as soon
as the space step `Δx = √(ν Δt / r)` is smaller than `π / 2`. The bound `≤` is (6.2.8); the test
function `testFun` has `|v| ≤ 1`, `v (π/2 ± Δx) = 1` and `v (π/2) = sign (1 - 2r)`, so
`C (Δt) v (π/2) = |1 - 2r| + 2r`.

Some smallness of `Δx` is needed, though the book states none: for `Δx = 2π` the shifts are
trivial, `C (Δt) = I`, and `‖C (Δt)‖ = 1 < |1 - 2r| + 2r` when `r > 1/2`. -/
theorem norm_forwardScheme_eq {ν r Δt : ℝ} (hr : 0 < r) (hΔx : 0 < Real.sqrt (ν * Δt / r))
    (hΔx' : Real.sqrt (ν * Δt / r) < π / 2) :
    ‖forwardScheme ν r Δt‖ = |1 - 2 * r| + 2 * r := by
  refine le_antisymm (norm_forwardScheme_le hr.le ν Δt) ?_
  set Δx := Real.sqrt (ν * Δt / r) with hΔxdef
  set v : C₀ := ⟨testFun r Δx, testFun_mem_C₀ hΔx hΔx'⟩ with hv
  have hv1 : ‖v‖ ≤ 1 := by
    rw [← Submodule.norm_coe]
    exact (ContinuousMap.norm_le _ zero_le_one).2 fun x => by
      rw [Real.norm_eq_abs]; exact abs_testFun_le hΔx hΔx' x
  have hmid : π / 2 ∈ Icc (0 : ℝ) π := ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hval : (forwardScheme ν r Δt v : C(Icc (0 : ℝ) π, ℝ)) ⟨π / 2, hmid⟩
      = |1 - 2 * r| + 2 * r := by
    rw [forwardScheme_apply, ← hΔxdef, ext_of_mem v (x := π / 2 + Δx)
      ⟨by positivity, by linarith [Real.pi_pos]⟩, ext_of_mem v (x := π / 2 - Δx)
      ⟨by linarith, by linarith [Real.pi_pos]⟩]
    change (1 - 2 * r) * testFun r Δx ⟨π / 2, hmid⟩ + r * (testFun r Δx ⟨π / 2 + Δx, _⟩
      + testFun r Δx ⟨π / 2 - Δx, _⟩) = _
    rw [testFun_mid hΔx hΔx', testFun_mid_add hΔx hΔx', testFun_mid_sub hΔx hΔx']
    split_ifs with h
    · rw [abs_of_nonneg (by linarith)]; ring
    · rw [abs_of_neg (by linarith)]; ring
  calc |1 - 2 * r| + 2 * r = ‖(forwardScheme ν r Δt v : C(Icc (0 : ℝ) π, ℝ)) ⟨π / 2, hmid⟩‖ := by
        rw [hval, Real.norm_eq_abs, abs_of_nonneg (a := |1 - 2 * r| + 2 * r) (by positivity)]
    _ ≤ ‖forwardScheme ν r Δt v‖ := by
        rw [← Submodule.norm_coe]; exact ContinuousMap.norm_coe_le_norm _ _
    _ ≤ ‖forwardScheme ν r Δt‖ * ‖v‖ := (forwardScheme ν r Δt).le_opNorm v
    _ ≤ ‖forwardScheme ν r Δt‖ := mul_le_of_le_one_right (norm_nonneg _) hv1

end ExactNorm

/-! #### Exercise 6.2.3, second half: the forward scheme is unstable for `r > 1/2` -/

section Instability

/-- The sines are eigenfunctions of the translated sum:
`ṽ (x + Δx) + ṽ (x - Δx) = 2 cos ((k + 1) Δx) sin ((k + 1) x)` for `v = sin ((k + 1) x)`. -/
theorem ext_sinV (k : ℕ) (y : ℝ) : ext (sinV k) y = Real.sin (((k : ℝ) + 1) * y) := by
  have h : sinV k = sinePolyV (k + 1) fun j => if j = k then 1 else 0 := by
    apply Subtype.ext
    rw [coe_sinePolyV, coe_sinV]
    ext x
    rw [sinePolynomial_apply, Finset.sum_eq_single k (fun j _ hj => by simp [hj])
      (fun h => absurd (Finset.mem_range.2 (Nat.lt_succ_self k)) h)]
    simp [sinMap_apply]
  rw [h, ext_sinePolyV, Finset.sum_eq_single k (fun j _ hj => by simp [hj])
    (fun h => absurd (Finset.mem_range.2 (Nat.lt_succ_self k)) h)]
  simp

/-- **The amplification factor of the forward scheme on the mode `sin ((k + 1) x)`**:
`C (Δt) sin ((k + 1) x) = (1 - 2r + 2r cos ((k + 1) Δx)) sin ((k + 1) x)`. -/
theorem forwardScheme_sinV (ν r Δt : ℝ) (k : ℕ) :
    forwardScheme ν r Δt (sinV k)
      = (1 - 2 * r + 2 * r * Real.cos (((k : ℝ) + 1) * Real.sqrt (ν * Δt / r))) • sinV k := by
  apply Subtype.ext
  ext x
  rw [forwardScheme_apply, ext_sinV, ext_sinV, Submodule.coe_smul, ContinuousMap.smul_apply,
    coe_sinV, sinMap_apply, smul_eq_mul]
  simp only [mul_add, mul_sub, Real.sin_add, Real.sin_sub]
  ring

/-- The powers of the forward scheme on the mode `sin ((k + 1) x)`. -/
theorem forwardScheme_pow_sinV (ν r Δt : ℝ) (k m : ℕ) :
    (forwardScheme ν r Δt ^ m) (sinV k)
      = (1 - 2 * r + 2 * r * Real.cos (((k : ℝ) + 1) * Real.sqrt (ν * Δt / r))) ^ m • sinV k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ']
    change forwardScheme ν r Δt ((forwardScheme ν r Δt ^ m) (sinV k)) = _
    rw [ih, map_smul, forwardScheme_sinV, smul_smul, pow_succ, mul_comm]

/-- `‖sin ((k + 1) x)‖ = 1` in `C₀[0, π]`: attained at `x = π / (2 (k + 1))`. -/
theorem norm_sinV (k : ℕ) : ‖sinV k‖ = 1 := by
  rw [← Submodule.norm_coe, coe_sinV]
  refine le_antisymm ((ContinuousMap.norm_le _ zero_le_one).2 fun x => by
    rw [sinMap_apply, Real.norm_eq_abs]; exact Real.abs_sin_le_one _) ?_
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hmem : π / (2 * ((k : ℝ) + 1)) ∈ Icc (0 : ℝ) π := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  calc (1 : ℝ) = ‖sinMap k ⟨π / (2 * ((k : ℝ) + 1)), hmem⟩‖ := by
        rw [sinMap_apply, Real.norm_eq_abs]
        change (1 : ℝ) = |Real.sin (((k : ℝ) + 1) * (π / (2 * ((k : ℝ) + 1))))|
        rw [show ((k : ℝ) + 1) * (π / (2 * ((k : ℝ) + 1))) = π / 2 by field_simp,
          Real.sin_pi_div_two, abs_one]
    _ ≤ ‖sinMap k‖ := ContinuousMap.norm_coe_le_norm _ _

/-- `‖C (Δt)^m‖ ≥ |1 - 2r + 2r cos ((k + 1) Δx)|^m`, from the mode `sin ((k + 1) x)`. -/
theorem pow_le_norm_forwardScheme_pow (ν r Δt : ℝ) (k m : ℕ) :
    |1 - 2 * r + 2 * r * Real.cos (((k : ℝ) + 1) * Real.sqrt (ν * Δt / r))| ^ m
      ≤ ‖forwardScheme ν r Δt ^ m‖ := by
  have h := (forwardScheme ν r Δt ^ m).le_opNorm (sinV k)
  rw [forwardScheme_pow_sinV, norm_smul, norm_sinV, mul_one, mul_one, Real.norm_eq_abs,
    abs_pow] at h
  exact h

/-- **Exercise 6.2.3, the necessity of `r ≤ 1/2`**: for `r > 1/2` the forward scheme is not
stable on any horizon `T > 0`, for any range `(0, Δ₀]` of step sizes. On the mode
`sin ((k + 1) x)` with `(k + 1) Δx` within `Δx` of `π` the amplification factor
`1 - 2r + 2r cos ((k + 1) Δx)` is at most `-2r` once `Δx² ≤ (2r - 1) / r`, so `‖C (Δt)^m‖ ≥ (2r)^m`
with `2r > 1`, unbounded as `Δt → 0` and `m Δt ≤ T`. Together with `example_6_2_13`, the forward
scheme is stable if and only if `r ≤ 1/2`: it is *conditionally* stable. -/
theorem not_isStable_forwardScheme (hν : 0 < ν) {r : ℝ} (hr : 1 / 2 < r) {T Δ₀ : ℝ} (hT : 0 < T)
    (hΔ₀ : 0 < Δ₀) : ¬ IsStable (forwardScheme ν r) T Δ₀ := by
  rintro ⟨M₀, hM₀⟩
  have hr0 : 0 < r := by linarith
  have h2r : 1 < 2 * r := by linarith
  -- a number of steps `m ≥ 1` with `(2r)^m > M₀`
  obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt h2r).eventually_gt_atTop M₀ |>.exists
  set m' := m + 1
  have hm' : M₀ < (2 * r) ^ m' :=
    hm.trans_le (pow_le_pow_right₀ h2r.le (Nat.le_succ m))
  have hm'pos : (0 : ℝ) < m' := by positivity
  -- the step size
  set Δt := min (T / m') (min Δ₀ ((2 * r - 1) / ν)) with hΔt
  have hΔt0 : 0 < Δt := lt_min (by positivity) (lt_min hΔ₀ (by
    have : 0 < 2 * r - 1 := by linarith
    positivity))
  have hΔtT : (m' : ℝ) * Δt ≤ T := by
    calc (m' : ℝ) * Δt ≤ m' * (T / m') := mul_le_mul_of_nonneg_left (min_le_left _ _) hm'pos.le
      _ = T := by field_simp
  have hΔtΔ₀ : Δt ≤ Δ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hΔtν : Δt ≤ (2 * r - 1) / ν := (min_le_right _ _).trans (min_le_right _ _)
  -- the space step and the mode
  set Δx := Real.sqrt (ν * Δt / r) with hΔx
  have hΔx0 : 0 < Δx := Real.sqrt_pos.2 (by positivity)
  have hΔx2 : Δx ^ 2 ≤ (2 * r - 1) / r := by
    rw [hΔx, Real.sq_sqrt (by positivity), div_le_div_iff_of_pos_right hr0]
    calc ν * Δt ≤ ν * ((2 * r - 1) / ν) := mul_le_mul_of_nonneg_left hΔtν hν.le
      _ = 2 * r - 1 := by field_simp
  set k := ⌈π / Δx⌉₊ - 1 with hk
  have hk1 : 1 ≤ ⌈π / Δx⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; positivity)
  have hkcast : ((k : ℕ) : ℝ) + 1 = (⌈π / Δx⌉₊ : ℝ) := by
    rw [hk, Nat.cast_sub hk1, Nat.cast_one, sub_add_cancel]
  -- `(k + 1) Δx ∈ [π, π + Δx)`
  have hlow : π ≤ ((k : ℝ) + 1) * Δx := by
    rw [hkcast, ← div_le_iff₀ hΔx0]
    exact Nat.le_ceil _
  have hupp : ((k : ℝ) + 1) * Δx < π + Δx := by
    rw [hkcast, ← lt_div_iff₀ hΔx0, add_div, div_self hΔx0.ne']
    exact Nat.ceil_lt_add_one (by positivity)
  -- the amplification factor is at most `-2r`
  have hcos : Real.cos (((k : ℝ) + 1) * Δx) ≤ -(1 - Δx ^ 2 / 2) := by
    have h1 : Real.cos (((k : ℝ) + 1) * Δx) = -Real.cos (((k : ℝ) + 1) * Δx - π) := by
      rw [Real.cos_sub_pi, neg_neg]
    rw [h1, neg_le_neg_iff]
    refine (Real.one_sub_sq_div_two_le_cos (x := ((k : ℝ) + 1) * Δx - π)).trans' ?_
    have h2 : (((k : ℝ) + 1) * Δx - π) ^ 2 ≤ Δx ^ 2 :=
      sq_le_sq' (by linarith) (by linarith)
    linarith
  have hlam : 1 - 2 * r + 2 * r * Real.cos (((k : ℝ) + 1) * Δx) ≤ -(2 * r) := by
    have h3 : 2 * r * Real.cos (((k : ℝ) + 1) * Δx) ≤ 2 * r * (-(1 - Δx ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left hcos (by positivity)
    have h4 : r * Δx ^ 2 ≤ 2 * r - 1 := by
      rw [mul_comm, ← le_div_iff₀ hr0]; exact hΔx2
    nlinarith
  have habs : 2 * r ≤ |1 - 2 * r + 2 * r * Real.cos (((k : ℝ) + 1) * Δx)| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  -- the contradiction
  have hbound := hM₀ Δt ⟨hΔt0, hΔtΔ₀⟩ m' hΔtT
  have hlower := pow_le_norm_forwardScheme_pow ν r Δt k m'
  rw [← hΔx] at hlower
  have : (2 * r) ^ m' ≤ ‖forwardScheme ν r Δt ^ m'‖ :=
    (pow_le_pow_left₀ (by positivity) habs m').trans hlower
  linarith

end Instability

end Schemes

end HeatExample

end AtkinsonHan.Chapter06
