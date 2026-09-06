import Mathlib.Analysis.Calculus.Deriv.Slope
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

Not formalized: the specific difference schemes of §6.1 and the examples of §6.2, which are Taylor
expansions of a solution assumed smooth.
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
theorem norm_solutionOperator_le : ∀ t ∈ Icc (0 : ℝ) T, ‖solutionOperator L hdense hT hc₀ hwp t‖
    ≤ c₀ := (solutionOperator_spec L hdense hT hc₀ hwp).2.1

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
tested on the trajectories of the family.

The division is written out, as the book writes it; the backbone clears it, and
`isConsistent_iff` is that identification. -/
def IsConsistent (S C : ℝ → V →L[ℝ] V) (T Δ₀ : ℝ) (D : Set V) : Prop :=
  Dense D ∧ ∀ u₀ ∈ D, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, Δt < δ →
    ∀ t ∈ Icc (0 : ℝ) T, ‖(Δt)⁻¹ • (C Δt (S t u₀) - S (t + Δt) u₀)‖ ≤ ε

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
    exact ⟨δ, hδ, fun Δt hΔt hlt t ht => (norm_inv_smul_le_iff hΔt.1).1 (hb Δt hΔt hlt t ht)⟩
  · rintro ⟨hD, h⟩
    refine ⟨hD, fun u₀ hu₀ ε hε => ?_⟩
    obtain ⟨δ, hδ, hb⟩ := h u₀ hu₀ ε hε
    exact ⟨δ, hδ, fun Δt hΔt hlt t ht => (norm_inv_smul_le_iff hΔt.1).2 (hb Δt hΔt hlt t ht)⟩

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

theorem isConvergent_iff (S C : ℝ → V →L[ℝ] V) (T Δ₀ : ℝ) :
    IsConvergent S C T Δ₀ ↔ FiniteDifference.IsConvergent S C T Δ₀ := by
  simp only [IsConvergent, FiniteDifference.IsConvergent, sub_apply]

/-- **Definition 6.2.10, stability.**  The method is stable when the powers `C(Δt)^m` taken within
the horizon, `m Δt ≤ T` and `0 < Δt ≤ Δ₀`, are bounded in norm uniformly in the step size. -/
def IsStable (C : ℝ → V →L[ℝ] V) (T Δ₀ : ℝ) : Prop :=
  ∃ M₀ : ℝ, ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, ∀ m : ℕ, (m : ℝ) * Δt ≤ T → ‖C Δt ^ m‖ ≤ M₀

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

end AtkinsonHan.Chapter06
