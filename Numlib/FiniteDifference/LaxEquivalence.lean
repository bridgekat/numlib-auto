import Numlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.MetricSpace.Sequences

/-!
# The Lax equivalence theorem

For a consistent one-step approximation of a well-posed abstract initial value problem in a Banach
space, stability and convergence are the same thing.

**The initial value problem.**  `L : V →ₗ.[𝕜] V` is a densely defined, generally unbounded
operator.  A *solution* on `[0, T]` is a curve `u` taking values in the domain of `L` there, whose
derivative within `Icc 0 T` is `L` applied to it — a derivative *within* the closed interval is
exactly the one-sided convention at the two endpoints, so no case split is needed
(`FiniteDifference.IsSolution`).  The problem is *well posed* (`FiniteDifference.IsWellPosed`) when
every initial value in the domain has a solution and any two solutions satisfy
`‖u t - ū t‖ ≤ c₀ ‖u₀ - ū₀‖` on `Icc 0 T`; that bound with `u₀ = ū₀` is uniqueness, which is
`FiniteDifference.IsWellPosed.eqOn`.  The solution map is then linear and bounded on the dense
domain, so it extends to bounded operators `S t : V →L[𝕜] V`
(`FiniteDifference.exists_solutionOperator`), and `S t u₀` for `u₀` outside the domain is the
*generalized solution*.

**What the equivalence theorem uses** is only `S 0 = 1` and strong continuity of `t ↦ S t u` on
`Icc 0 T`, so it is stated for a family `S` rather than reconstructed from `L`; the bridge from the
initial value problem is `exists_solutionOperator`, and the semigroup property
`solutionOperator_add` is recorded because the sources state it but is **not** a hypothesis
anywhere.  Keeping the two apart makes the equivalence usable for any evolution family and keeps
the `LinearPMap` machinery out of the interesting proof.

**The three properties** are `Prop`-valued predicates on the pair `(S, C)`, not bundles of data: a
scheme *is* consistent, stable or convergent.  `FiniteDifference.IsConsistent` is written with the
division cleared, `‖C Δt (S t u₀) - S (t + Δt) u₀‖ ≤ ε Δt`, so that no `Δt⁻¹` occurs;
`FiniteDifference.IsConvergent` quantifies over *sequences* of step sizes and step counts with
`m Δt → t`, because the limit is along an arbitrary refinement of the discrete time and not along
one sequence of step sizes.

**The two directions** of `FiniteDifference.isStable_iff_isConvergent`.  Forward: the telescoping
identity behind `FiniteDifference.norm_iterate_sub_le`, whose sum stability bounds by
`M₀ (m Δt) ε`, plus continuity of `t ↦ S t u₀` to pass from `m Δt` to `t`, and then the ε/3 density
argument for initial values outside the dense set on which consistency is assumed.  Backward: a
uniformly bounded `C` makes the step sizes bounded away from zero harmless, so instability produces
step sizes tending to zero; the discrete times then have a convergent subsequence, along which
convergence bounds every orbit and the uniform boundedness principle bounds the operator norms.
Both directions rest on `Numlib/Analysis/Normed/Operator/BanachSteinhaus`, which is the only reason
the theorem asks for `[CompleteSpace V]`.

`FiniteDifference.norm_iterate_sub_le` is the order of convergence read off the same telescoping
estimate: an inequality with explicit constants, no limit and no order symbol.

The material is Section 6.2 of Atkinson–Han[^atkinson-han] (Definitions 6.2.1, 6.2.2, 6.2.3, 6.2.7,
6.2.9 and 6.2.10, Propositions 6.2.5 and 6.2.6, Theorem 6.2.11 and Corollary 6.2.12); the theorem
is due to Lax and Richtmyer[^lax-richtmyer], and Chapter 3 of Richtmyer and
Morton[^richtmyer-morton] is the standard account.

## References

[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
[^lax-richtmyer]: Peter D. Lax and Robert D. Richtmyer, *Survey of the stability of linear finite
  difference equations*, Communications on Pure and Applied Mathematics 9 (1956), 267–293.
[^richtmyer-morton]: Robert D. Richtmyer and K. W. Morton, *Difference Methods for Initial-Value
  Problems*, 2nd edition, Wiley, 1967.
-/

open Filter Set Topology

namespace FiniteDifference

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-! ### The abstract initial value problem -/

section InitialValueProblem

variable [NormedSpace ℝ V]

/-- **A solution of the abstract initial value problem** `u' = L u`, `u 0 = u₀`, on `Icc 0 T`: the
curve takes values in the domain of the densely defined operator `L` there, and its derivative
*within* `Icc 0 T` is `L` applied to it.  Taking the derivative within the closed interval is what
gives the one-sided limits at the two endpoints, so the two ends need no special case.

Atkinson–Han, *Theoretical Numerical Analysis*, Definition 6.2.1 and (6.2.2). -/
def IsSolution (L : V →ₗ.[𝕜] V) (T : ℝ) (u₀ : V) (u : ℝ → V) : Prop :=
  u 0 = u₀ ∧ ∀ t ∈ Icc (0 : ℝ) T, ∃ h : u t ∈ L.domain,
    HasDerivWithinAt u (L ⟨u t, h⟩) (Icc 0 T) t

/-- **Well-posedness** of the abstract initial value problem on `Icc 0 T` with stability constant
`c₀`: every initial value in the domain of `L` has a solution, and any two solutions satisfy
`‖u t - ū t‖ ≤ c₀ ‖u₀ - ū₀‖` on `Icc 0 T`.

The second clause with `u₀ = ū₀` is uniqueness of the solution on `Icc 0 T`, which is
`FiniteDifference.IsWellPosed.eqOn`, so uniqueness is not assumed separately.

Atkinson–Han, *Theoretical Numerical Analysis*, Definition 6.2.2 and (6.2.3). -/
def IsWellPosed (L : V →ₗ.[𝕜] V) (T c₀ : ℝ) : Prop :=
  (∀ u₀ ∈ L.domain, ∃ u, IsSolution L T u₀ u) ∧
    ∀ u₀ ū₀ u ū, IsSolution L T u₀ u → IsSolution L T ū₀ ū →
      ∀ t ∈ Icc (0 : ℝ) T, ‖u t - ū t‖ ≤ c₀ * ‖u₀ - ū₀‖

/-- Uniqueness of the solution on `Icc 0 T`: the stability bound of `IsWellPosed` applied to two
solutions with the same initial value. -/
theorem IsWellPosed.eqOn {L : V →ₗ.[𝕜] V} {T c₀ : ℝ} (hwp : IsWellPosed L T c₀) {u₀ : V}
    {u ū : ℝ → V} (hu : IsSolution L T u₀ u) (hū : IsSolution L T u₀ ū) :
    EqOn u ū (Icc 0 T) := by
  intro t ht
  have h := hwp.2 u₀ u₀ u ū hu hū t ht
  rw [sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

/-- The constant zero curve solves the initial value problem with initial value `0`. -/
private theorem isSolution_zero (L : V →ₗ.[𝕜] V) (T : ℝ) : IsSolution L T 0 (fun _ => 0) := by
  refine ⟨rfl, fun t _ => ⟨L.domain.zero_mem, ?_⟩⟩
  have hz : (L ⟨(0 : V), L.domain.zero_mem⟩) = 0 := by
    rw [show (⟨(0 : V), L.domain.zero_mem⟩ : L.domain) = 0 from rfl]
    exact L.map_zero
  rw [hz]
  exact hasDerivWithinAt_const _ _ _

/-- Sums of solutions are solutions, by linearity of `L`. -/
private theorem isSolution_add {L : V →ₗ.[𝕜] V} {T : ℝ} {u₀ ū₀ : V} {u ū : ℝ → V}
    (hu : IsSolution L T u₀ u) (hū : IsSolution L T ū₀ ū) :
    IsSolution L T (u₀ + ū₀) (fun t => u t + ū t) := by
  refine ⟨by dsimp only; rw [hu.1, hū.1], fun t ht => ?_⟩
  obtain ⟨h1, hd1⟩ := hu.2 t ht
  obtain ⟨h2, hd2⟩ := hū.2 t ht
  refine ⟨L.domain.add_mem h1 h2, ?_⟩
  have hL : (L ⟨u t + ū t, L.domain.add_mem h1 h2⟩) = L ⟨u t, h1⟩ + L ⟨ū t, h2⟩ := by
    rw [show (⟨u t + ū t, L.domain.add_mem h1 h2⟩ : L.domain) = ⟨u t, h1⟩ + ⟨ū t, h2⟩ from rfl]
    exact L.map_add _ _
  rw [hL]
  exact HasDerivWithinAt.add hd1 hd2

/-- **The semigroup property.**  Atkinson–Han, *Theoretical Numerical Analysis*, Proposition 6.2.6:
the solution operators satisfy `S (t₁ + t₀) = S t₁ ∘L S t₀` for `t₀, t₁ ≥ 0` with `t₁ + t₀ ≤ T`,
by time-translation invariance of the equation and uniqueness of solutions.

`S` is asked to represent the solution at every horizon `T' ≤ T`, not only at `T`: translating a
solution back by `t₀` produces a solution on `Icc 0 (T - t₀)`, and it is the representation *there*
that identifies it with the trajectory started at `S t₀ u₀`.  A statement about the horizon `T`
alone says nothing about curves defined only on a shorter interval.

**The Lax equivalence theorem does not use this**, and it must not become a hypothesis of
`isStable_iff_isConvergent`; it is recorded because the sources state it. -/
theorem solutionOperator_add {L : V →ₗ.[𝕜] V} (hdense : Dense (L.domain : Set V)) {T : ℝ}
    {S : ℝ → V →L[𝕜] V} (hex : ∀ u₀ ∈ L.domain, ∃ u, IsSolution L T u₀ u)
    (hS : ∀ T' ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T', ∀ u₀ ∈ L.domain, ∀ u,
      IsSolution L T' u₀ u → S t u₀ = u t)
    {t₀ t₁ : ℝ} (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁) (hsum : t₁ + t₀ ≤ T) :
    S (t₁ + t₀) = S t₁ ∘L S t₀ := by
  have hT : (0 : ℝ) ≤ T := le_trans (by linarith) hsum
  have hTT : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have key : EqOn (S (t₁ + t₀)) (S t₁ ∘L S t₀) (L.domain : Set V) := by
    intro u₀ hu₀
    obtain ⟨u, hu⟩ := hex u₀ hu₀
    have h1 : S (t₁ + t₀) u₀ = u (t₁ + t₀) :=
      hS T hTT _ ⟨by linarith, hsum⟩ u₀ hu₀ u hu
    have h2 : S t₀ u₀ = u t₀ := hS T hTT _ ⟨ht₀, by linarith⟩ u₀ hu₀ u hu
    obtain ⟨hmem, -⟩ := hu.2 t₀ ⟨ht₀, by linarith⟩
    -- the solution translated back by `t₀`, on the horizon `T - t₀`
    have hw : IsSolution L (T - t₀) (u t₀) (fun τ => u (τ + t₀)) := by
      refine ⟨by norm_num, fun τ hτ => ?_⟩
      obtain ⟨h, hd⟩ := hu.2 (τ + t₀) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      refine ⟨h, ?_⟩
      have hshift : HasDerivWithinAt (fun ρ : ℝ => ρ + t₀) 1 (Icc 0 (T - t₀)) τ := by
        simpa using (hasDerivWithinAt_id τ (Icc 0 (T - t₀))).add_const t₀
      have hmaps : MapsTo (fun ρ : ℝ => ρ + t₀) (Icc 0 (T - t₀)) (Icc 0 T) := fun ρ hρ =>
        ⟨by linarith [hρ.1], by linarith [hρ.2]⟩
      have hcomp : HasDerivWithinAt (u ∘ fun ρ : ℝ => ρ + t₀)
          ((1 : ℝ) • (L ⟨u (τ + t₀), h⟩)) (Icc 0 (T - t₀)) τ :=
        HasDerivWithinAt.scomp τ hd hshift hmaps
      rw [one_smul] at hcomp
      exact hcomp
    have h3 : S t₁ (u t₀) = u (t₁ + t₀) :=
      hS (T - t₀) ⟨by linarith, by linarith⟩ t₁ ⟨ht₁, by linarith⟩ (u t₀) hmem _ hw
    rw [ContinuousLinearMap.comp_apply, h2, h3, h1]
  exact DFunLike.coe_injective
    (Continuous.ext_on hdense (S (t₁ + t₀)).continuous (S t₁ ∘L S t₀).continuous key)

section Smul

variable [SMulCommClass ℝ 𝕜 V]

/-- Scalar multiples of solutions are solutions, by linearity of `L`. -/
private theorem isSolution_smul {L : V →ₗ.[𝕜] V} {T : ℝ} {u₀ : V} {u : ℝ → V}
    (hu : IsSolution L T u₀ u) (c : 𝕜) : IsSolution L T (c • u₀) (fun t => c • u t) := by
  refine ⟨by dsimp only; rw [hu.1], fun t ht => ?_⟩
  obtain ⟨h1, hd1⟩ := hu.2 t ht
  refine ⟨L.domain.smul_mem c h1, ?_⟩
  have hL : (L ⟨c • u t, L.domain.smul_mem c h1⟩) = c • L ⟨u t, h1⟩ := by
    rw [show (⟨c • u t, L.domain.smul_mem c h1⟩ : L.domain) = c • ⟨u t, h1⟩ from rfl]
    exact L.map_smul c _
  rw [hL]
  exact HasDerivWithinAt.const_smul c hd1

/-- **The solution operators.**  For a well-posed problem on `Icc 0 T` with a dense domain there is
a family of bounded operators `S t : V →L[𝕜] V` with `S 0 = 1`, `‖S t‖ ≤ c₀` on `Icc 0 T`, and
`S t u₀` the value at `t` of the solution with initial value `u₀` whenever `u₀` lies in the domain
of `L`.

The solution map at time `t` is linear on the domain — sums and scalar multiples of solutions are
solutions, and the solution is unique — and bounded by `c₀`, by comparison with the zero solution;
it therefore extends uniquely to the whole space along the dense inclusion of the domain.  The
value `S t u₀` at an initial value outside the domain is the *generalized solution* of
Atkinson–Han, *Theoretical Numerical Analysis*, Definition 6.2.3, and the extension theorem the
book cites there is `ContinuousLinearMap.extend`.

The family produced here is defined for every real `t` by clamping the parameter into `Icc 0 T`,
which is why every clause about it carries the membership hypothesis. -/
theorem exists_solutionOperator [CompleteSpace V] (L : V →ₗ.[𝕜] V)
    (hdense : Dense (L.domain : Set V)) {T c₀ : ℝ} (hT : 0 ≤ T) (hc₀ : 0 ≤ c₀)
    (hwp : IsWellPosed L T c₀) :
    ∃ S : ℝ → V →L[𝕜] V, S 0 = 1 ∧ (∀ t ∈ Icc (0 : ℝ) T, ‖S t‖ ≤ c₀) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ u₀ ∈ L.domain, ∀ u, IsSolution L T u₀ u → S t u₀ = u t := by
  classical
  choose sol hsol using hwp.1
  have hval : ∀ t ∈ Icc (0 : ℝ) T, ∀ (u₀ : V) (h : u₀ ∈ L.domain) (u : ℝ → V),
      IsSolution L T u₀ u → sol u₀ h t = u t :=
    fun t ht u₀ h u hu => hwp.eqOn (hsol u₀ h) hu ht
  -- clamping the parameter into `Icc 0 T` makes the solution map linear for *every* parameter
  have hclmem : ∀ t : ℝ, max 0 (min t T) ∈ Icc (0 : ℝ) T := fun t =>
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hclid : ∀ t ∈ Icc (0 : ℝ) T, max 0 (min t T) = t := fun t ht => by
    rw [min_eq_left ht.2, max_eq_right ht.1]
  obtain ⟨g, hgapp⟩ : ∃ g : ℝ → (L.domain →ₗ[𝕜] V),
      ∀ (t : ℝ) (x : L.domain), g t x = sol (x : V) x.2 (max 0 (min t T)) :=
    ⟨fun t =>
      { toFun := fun x => sol (x : V) x.2 (max 0 (min t T))
        map_add' := fun x y =>
          hval _ (hclmem t) ((x : V) + (y : V)) (L.domain.add_mem x.2 y.2) _
            (isSolution_add (hsol _ x.2) (hsol _ y.2))
        map_smul' := fun c x =>
          hval _ (hclmem t) (c • (x : V)) (L.domain.smul_mem c x.2) _
            (isSolution_smul (hsol _ x.2) c) }, fun _ _ => rfl⟩
  have hgb : ∀ (t : ℝ) (x : L.domain), ‖g t x‖ ≤ c₀ * ‖x‖ := by
    intro t x
    have h := hwp.2 (x : V) 0 (sol (x : V) x.2) (fun _ => 0) (hsol _ x.2) (isSolution_zero L T)
      _ (hclmem t)
    rw [hgapp]
    simpa using h
  obtain ⟨G, hGapp, hGnorm⟩ : ∃ G : ℝ → (L.domain →L[𝕜] V),
      (∀ (t : ℝ) (x : L.domain), G t x = g t x) ∧ ∀ t : ℝ, ‖G t‖ ≤ c₀ :=
    ⟨fun t => (g t).mkContinuous c₀ (hgb t), fun _ _ => rfl,
      fun t => LinearMap.mkContinuous_norm_le _ hc₀ _⟩
  have hdr : DenseRange (L.domain.subtypeL : L.domain →L[𝕜] V) := by
    have hrange : Set.range (L.domain.subtypeL : L.domain →L[𝕜] V) = (L.domain : Set V) :=
      Subtype.range_coe
    rw [DenseRange, hrange]
    exact hdense
  have hbd : ∀ x : L.domain, ‖x‖ ≤ (1 : NNReal) * ‖L.domain.subtypeL x‖ := by
    intro x
    simp
  have hui : IsUniformInducing (L.domain.subtypeL : L.domain →L[𝕜] V) :=
    (ContinuousLinearMap.isUniformEmbedding_of_bound _ hbd).isUniformInducing
  have hext : ∀ (t : ℝ) (v : V) (hv : v ∈ L.domain),
      ContinuousLinearMap.extend (G t) L.domain.subtypeL v = sol v hv (max 0 (min t T)) := by
    intro t v hv
    have h := ContinuousLinearMap.extend_eq (G t) hdr hui ⟨v, hv⟩
    rw [hGapp, hgapp] at h
    exact h
  refine ⟨fun t => ContinuousLinearMap.extend (G t) L.domain.subtypeL, ?_, fun t _ => ?_, ?_⟩
  · refine DFunLike.coe_injective (Continuous.ext_on hdense
      (ContinuousLinearMap.extend (G 0) L.domain.subtypeL).continuous
      (1 : V →L[𝕜] V).continuous fun v hv => ?_)
    have h0 : max 0 (min (0 : ℝ) T) = 0 := by rw [min_eq_left hT, max_self]
    rw [hext 0 v hv, h0, (hsol v hv).1]
    rfl
  · exact le_trans (by simpa using ContinuousLinearMap.opNorm_extend_le (G t) hdr hbd) (hGnorm t)
  · intro t ht u₀ hu₀ u hu
    rw [hext t u₀ hu₀, hclid t ht]
    exact hval t ht u₀ hu₀ u hu

end Smul

end InitialValueProblem

/-! ### Strong continuity of a uniformly bounded family -/

/-- **Atkinson–Han, *Theoretical Numerical Analysis*, Proposition 6.2.5.**  A family of operators
that is uniformly bounded on a set `P` of parameters and strongly continuous there on a dense set
of vectors is strongly continuous on `P` at *every* vector.  So the generalized solution is
continuous in time even though only the genuine solutions were assumed differentiable.

An instance of the Banach–Steinhaus density criterion
`ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded`, stated for an arbitrary parameter set
rather than for `Icc 0 T` only; neither completeness nor a Baire argument is used. -/
theorem continuousOn_of_dense {D : Set V} (hD : Dense D) {S : ℝ → V →L[𝕜] V} {P : Set ℝ} {c₀ : ℝ}
    (hb : ∀ t ∈ P, ‖S t‖ ≤ c₀) (hcont : ∀ u ∈ D, ContinuousOn (fun t => S t u) P) (u : V) :
    ContinuousOn (fun t => S t u) P := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  have hrestrict : ∀ v ∈ D, Tendsto (fun t : ↥P => S (t : ℝ) v) (𝓝 t₀) (𝓝 (S (t₀ : ℝ) v)) :=
    fun v hv => (continuous_iff_continuousAt.1 (hcont v hv).domRestrict) t₀
  exact ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded hD
    (fun t : ↥P => hb (t : ℝ) t.2) hrestrict u

/-! ### Consistency, stability and convergence -/

/-- **Consistency** of the scheme `C` for the evolution family `S` on `Icc 0 T`, for step sizes in
`Ioc 0 Δ₀`, tested on the dense set `D` of initial values: the local truncation error is `o(Δt)`
uniformly in `t ∈ Icc 0 T`.

The division is cleared — the condition reads `‖C Δt (S t u₀) - S (t + Δt) u₀‖ ≤ ε Δt` — so that no
`Δt⁻¹` occurs anywhere.  Atkinson–Han, *Theoretical Numerical Analysis*, Definition 6.2.7. -/
def IsConsistent (S C : ℝ → V →L[𝕜] V) (T Δ₀ : ℝ) (D : Set V) : Prop :=
  Dense D ∧ ∀ u₀ ∈ D, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, Δt < δ →
    ∀ t ∈ Icc (0 : ℝ) T, ‖C Δt (S t u₀) - S (t + Δt) u₀‖ ≤ ε * Δt

/-- **Stability** of the scheme `C` on `Icc 0 T` for step sizes in `Ioc 0 Δ₀`: the powers taken
within the horizon are bounded in norm, uniformly in the step size.  Atkinson–Han, *Theoretical
Numerical Analysis*, Definition 6.2.10; the power is taken in the monoid of bounded operators. -/
def IsStable (C : ℝ → V →L[𝕜] V) (T Δ₀ : ℝ) : Prop :=
  ∃ M₀ : ℝ, ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, ∀ m : ℕ, (m : ℝ) * Δt ≤ T → ‖C Δt ^ m‖ ≤ M₀

/-- **Convergence** of the scheme `C` to the evolution family `S` on `Icc 0 T` for step sizes in
`Ioc 0 Δ₀`: along every refinement — every pair of sequences of step sizes `Δt i ∈ Ioc 0 Δ₀` and
step counts `m i` staying within the horizon, with `Δt i → 0` and the discrete times
`m i · Δt i → t` — the discrete solution converges to `S t u₀`, for every `u₀` and every
`t ∈ Icc 0 T`.

The sequences are quantified over because the limit is along an arbitrary refinement whose discrete
time tends to `t`, not along a single sequence of step sizes.  Atkinson–Han, *Theoretical Numerical
Analysis*, Definition 6.2.9. -/
def IsConvergent (S C : ℝ → V →L[𝕜] V) (T Δ₀ : ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) T, ∀ u₀ : V, ∀ (Δt : ℕ → ℝ) (m : ℕ → ℕ), (∀ i, Δt i ∈ Ioc (0 : ℝ) Δ₀) →
    (∀ i, (m i : ℝ) * Δt i ≤ T) → Tendsto Δt atTop (𝓝 0) →
    Tendsto (fun i => (m i : ℝ) * Δt i) atTop (𝓝 t) →
    Tendsto (fun i => ‖(C (Δt i) ^ m i) u₀ - S t u₀‖) atTop (𝓝 0)

/-! ### The telescoping estimate -/

/-- **The telescoping estimate.**  If the powers `C ^ i` up to `i = m` are bounded by `M₀` and each
one-step error `‖C (v i) - v (i + 1)‖` is at most `δ`, then `‖C ^ m (v 0) - v m‖ ≤ m M₀ δ`.

This is the whole computational content of both the Lax equivalence theorem and its
convergence-order corollary: the discrete evolution differs from the sampled exact evolution by the
accumulated local errors, each propagated by a power of `C` that stability controls. -/
private theorem norm_iterate_sub_le_aux (C : V →L[𝕜] V) (M₀ δ : ℝ) :
    ∀ (m : ℕ) (v : ℕ → V), (∀ i ≤ m, ‖C ^ i‖ ≤ M₀) → (∀ i < m, ‖C (v i) - v (i + 1)‖ ≤ δ) →
      ‖(C ^ m) (v 0) - v m‖ ≤ m * (M₀ * δ) := by
  intro m
  induction m with
  | zero => intro v _ _; simp
  | succ n ih =>
    intro v hC hloc
    have hpow : (C ^ (n + 1)) (v 0) = (C ^ n) (C (v 0)) := by rw [pow_succ]; rfl
    have hstep : (C ^ (n + 1)) (v 0) - v (n + 1)
        = (C ^ n) (C (v 0) - v 1) + ((C ^ n) (v 1) - v (n + 1)) := by
      rw [map_sub, hpow]
      abel
    have hM : 0 ≤ M₀ := le_trans (norm_nonneg _) (hC n (Nat.le_succ n))
    have h1 : ‖(C ^ n) (C (v 0) - v 1)‖ ≤ M₀ * δ :=
      ((C ^ n).le_opNorm _).trans (mul_le_mul (hC n (Nat.le_succ n)) (hloc 0 (Nat.succ_pos n))
        (norm_nonneg _) hM)
    have h2 : ‖(C ^ n) ((fun i => v (i + 1)) 0) - (fun i => v (i + 1)) n‖ ≤ n * (M₀ * δ) :=
      ih (fun i => v (i + 1)) (fun i hi => hC i (hi.trans (Nat.le_succ n)))
        (fun i hi => hloc (i + 1) (Nat.succ_lt_succ hi))
    rw [hstep]
    calc ‖(C ^ n) (C (v 0) - v 1) + ((C ^ n) (v 1) - v (n + 1))‖
        ≤ ‖(C ^ n) (C (v 0) - v 1)‖ + ‖(C ^ n) (v 1) - v (n + 1)‖ := norm_add_le _ _
      _ ≤ M₀ * δ + n * (M₀ * δ) := add_le_add h1 h2
      _ = (n + 1 : ℕ) * (M₀ * δ) := by push_cast; ring

/-- The discrete evolution differs from the sampled exact evolution by the accumulated local
errors: if the powers of `C` up to `m` are bounded by `M₀` and every local error on the grid of
step `Δt` is at most `δ`, then `‖C ^ m u₀ - S (m Δt) u₀‖ ≤ m M₀ δ`. -/
private theorem norm_iterate_sub_le_grid {S : ℝ → V →L[𝕜] V} {C : V →L[𝕜] V} (hS0 : S 0 = 1)
    (M₀ δ Δt : ℝ) (u₀ : V) (m : ℕ) (hC : ∀ i ≤ m, ‖C ^ i‖ ≤ M₀)
    (hloc : ∀ i < m, ‖C (S ((i : ℝ) * Δt) u₀) - S ((i : ℝ) * Δt + Δt) u₀‖ ≤ δ) :
    ‖(C ^ m) u₀ - S ((m : ℝ) * Δt) u₀‖ ≤ m * (M₀ * δ) := by
  have hgrid : ∀ i < m, ‖C ((fun j : ℕ => S ((j : ℝ) * Δt) u₀) i)
      - (fun j : ℕ => S ((j : ℝ) * Δt) u₀) (i + 1)‖ ≤ δ := by
    intro i hi
    have hcast : ((i + 1 : ℕ) : ℝ) * Δt = (i : ℝ) * Δt + Δt := by push_cast; ring
    simpa only [hcast] using hloc i hi
  have h := norm_iterate_sub_le_aux C M₀ δ m (fun j : ℕ => S ((j : ℝ) * Δt) u₀) hC hgrid
  have hz : S (((0 : ℕ) : ℝ) * Δt) u₀ = u₀ := by
    rw [Nat.cast_zero, zero_mul, hS0]
    rfl
  rwa [hz] at h

/-- **Order of convergence.**  Atkinson–Han, *Theoretical Numerical Analysis*, Corollary 6.2.12: if
the scheme is stable with constant `M₀` up to step `m` and the local error at the initial value
`u₀` satisfies `‖C Δt (S t u₀) - S (t + Δt) u₀‖ ≤ c Δt ^ (k + 1)` uniformly on `Icc 0 T`, then

  `‖(C Δt) ^ m u₀ - S T u₀‖ ≤ M₀ T c Δt ^ k`  whenever `m Δt = T`.

This is the telescoping estimate with no limit taken, so the statement is an inequality with
explicit constants. -/
theorem norm_iterate_sub_le {S C : ℝ → V →L[𝕜] V} {T Δt c M₀ : ℝ} {k m : ℕ} (u₀ : V)
    (hS0 : S 0 = 1) (hΔt : 0 < Δt) (hmΔt : (m : ℝ) * Δt = T)
    (hstab : ∀ i ≤ m, ‖C Δt ^ i‖ ≤ M₀)
    (hloc : ∀ t ∈ Icc (0 : ℝ) T, ‖C Δt (S t u₀) - S (t + Δt) u₀‖ ≤ c * Δt ^ (k + 1)) :
    ‖(C Δt ^ m) u₀ - S T u₀‖ ≤ M₀ * T * c * Δt ^ k := by
  have hgrid : ‖(C Δt ^ m) u₀ - S ((m : ℝ) * Δt) u₀‖ ≤ m * (M₀ * (c * Δt ^ (k + 1))) := by
    refine norm_iterate_sub_le_grid hS0 M₀ (c * Δt ^ (k + 1)) Δt u₀ m hstab fun i hi => ?_
    refine hloc _ ⟨by positivity, ?_⟩
    rw [← hmΔt]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi.le) hΔt.le
  rw [← hmΔt]
  calc ‖(C Δt ^ m) u₀ - S ((m : ℝ) * Δt) u₀‖ ≤ m * (M₀ * (c * Δt ^ (k + 1))) := hgrid
    _ = M₀ * ((m : ℝ) * Δt) * c * Δt ^ k := by ring

/-! ### The Lax equivalence theorem -/

/-- A power of an operator of norm at most `b ≥ 1` has norm at most `b ^ m`. -/
private theorem norm_pow_le_pow {A : V →L[𝕜] V} {b : ℝ} (hb : 1 ≤ b) (h : ‖A‖ ≤ b) (m : ℕ) :
    ‖A ^ m‖ ≤ b ^ m := by
  induction m with
  | zero =>
    simp only [pow_zero]
    calc ‖(1 : V →L[𝕜] V)‖ = ‖ContinuousLinearMap.id 𝕜 V‖ := rfl
      _ ≤ 1 := ContinuousLinearMap.norm_id_le
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans
      (mul_le_mul ih h (norm_nonneg _) (le_trans zero_le_one (one_le_pow₀ hb)))

/-- Stability on small step sizes is stability: for a uniformly bounded `C` the step sizes bounded
away from zero allow only boundedly many steps within the horizon. -/
private theorem isStable_of_isStable_below {C : ℝ → V →L[𝕜] V} {T Δ₀ c₁ a : ℝ}
    (ha : 0 < a) (hC : ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, ‖C Δt‖ ≤ c₁)
    (h : ∃ M, ∀ Δt ∈ Ioc (0 : ℝ) a, ∀ m : ℕ, (m : ℝ) * Δt ≤ T → ‖C Δt ^ m‖ ≤ M) :
    IsStable C T Δ₀ := by
  obtain ⟨M, hM⟩ := h
  have hc₁ : (1 : ℝ) ≤ max c₁ 1 := le_max_right _ _
  refine ⟨max M (max c₁ 1 ^ ⌈T / a⌉₊), fun Δt hΔt m hm => ?_⟩
  rcases le_or_gt Δt a with hle | hgt
  · exact le_max_of_le_left (hM Δt ⟨hΔt.1, hle⟩ m hm)
  · have h1 : (m : ℝ) * a ≤ T :=
      le_trans (mul_le_mul_of_nonneg_left hgt.le (Nat.cast_nonneg _)) hm
    have h2 : (m : ℝ) ≤ (⌈T / a⌉₊ : ℝ) := ((le_div_iff₀ ha).2 h1).trans (Nat.le_ceil _)
    have hmle : m ≤ ⌈T / a⌉₊ := by exact_mod_cast h2
    refine le_max_of_le_right ?_
    exact (norm_pow_le_pow hc₁ ((hC Δt hΔt).trans (le_max_left _ _)) m).trans
      (pow_le_pow_right₀ hc₁ hmle)

/-- **The Lax equivalence theorem.**  Atkinson–Han, *Theoretical Numerical Analysis*,
Theorem 6.2.11.  For an evolution family `S` with `S 0 = 1` that is strongly continuous on
`Icc 0 T`, and a family `C` of one-step operators that is uniformly bounded in norm and consistent
on a dense set of initial values, the scheme is stable if and only if it is convergent.

Forward: telescope the error over the grid, bound the accumulated local errors by `M₀ (m Δt) ε`
using stability, pass from the discrete time `m Δt` to `t` by strong continuity of `S`, and go from
the dense set to all initial values by the Banach–Steinhaus density criterion, whose uniform bound
is again stability.  Backward: uniform boundedness of `C` makes the step sizes bounded away from
zero harmless, so instability yields step sizes tending to zero whose discrete times have a
convergent subsequence; along it convergence bounds every orbit, and the uniform boundedness
principle bounds the operator norms, contradicting instability.

The uniform bound on `‖C Δt‖` is needed and is not implied by the rest: it is what the sources use
silently when they introduce the family, and without it the bounded-step-count case of the backward
direction is unjustified.  The semigroup property of `S` is **not** used. -/
theorem isStable_iff_isConvergent [CompleteSpace V] {S C : ℝ → V →L[𝕜] V} {T Δ₀ c₁ : ℝ}
    {D : Set V} (hT : 0 ≤ T) (hS0 : S 0 = 1)
    (hScont : ∀ u : V, ContinuousOn (fun t => S t u) (Icc 0 T))
    (hC : ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, ‖C Δt‖ ≤ c₁) (hcons : IsConsistent S C T Δ₀ D) :
    IsStable C T Δ₀ ↔ IsConvergent S C T Δ₀ := by
  constructor
  · -- stability and consistency give convergence
    rintro ⟨M₀, hM₀⟩
    have hMnn : (0 : ℝ) ≤ max M₀ 0 := le_max_right _ _
    have hM : ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, ∀ m : ℕ, (m : ℝ) * Δt ≤ T → ‖C Δt ^ m‖ ≤ max M₀ 0 :=
      fun Δt hΔt m hm => (hM₀ Δt hΔt m hm).trans (le_max_left _ _)
    have hP : (0 : ℝ) ≤ max M₀ 0 * T := mul_nonneg hMnn hT
    have hden : (0 : ℝ) < 2 * (max M₀ 0 * T + 1) := by linarith
    intro t ht u₀ Δt m hΔt hmT hΔt0 hmt
    -- on the dense set, the telescoping estimate and strong continuity of `S`
    have hdense : ∀ v ∈ D, Tendsto (fun i => (C (Δt i) ^ m i) v) atTop (𝓝 (S t v)) := by
      intro v hv
      refine Metric.tendsto_atTop.2 fun ε' hε' => ?_
      have hεpos : (0 : ℝ) < ε' / (2 * (max M₀ 0 * T + 1)) := div_pos hε' hden
      obtain ⟨δ, hδ, hloc⟩ := hcons.2 v hv (ε' / (2 * (max M₀ 0 * T + 1))) hεpos
      have hA : ∀ᶠ i in atTop, Δt i < δ := by
        simpa using hΔt0.eventually (eventually_lt_nhds hδ)
      have hB : ∀ᶠ i in atTop, ‖S ((m i : ℝ) * Δt i) v - S t v‖ < ε' / 2 := by
        have hmem : ∀ i, (m i : ℝ) * Δt i ∈ Icc (0 : ℝ) T := fun i =>
          ⟨mul_nonneg (Nat.cast_nonneg _) (hΔt i).1.le, hmT i⟩
        have hwithin : Tendsto (fun i => (m i : ℝ) * Δt i) atTop (𝓝[Icc 0 T] t) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hmt
            (Eventually.of_forall hmem)
        have hlim : Tendsto (fun i => S ((m i : ℝ) * Δt i) v) atTop (𝓝 (S t v)) :=
          (hScont v t ht).tendsto.comp hwithin
        have hconst : Tendsto (fun _ : ℕ => S t v) atTop (𝓝 (S t v)) := tendsto_const_nhds
        have hz := (hlim.sub hconst).norm
        simp only [sub_self, norm_zero] at hz
        exact hz.eventually (eventually_lt_nhds (by linarith))
      rw [← Filter.eventually_atTop]
      filter_upwards [hA, hB] with i hAi hBi
      have hgrid : ‖(C (Δt i) ^ m i) v - S ((m i : ℝ) * Δt i) v‖
          ≤ m i * (max M₀ 0 * (ε' / (2 * (max M₀ 0 * T + 1)) * Δt i)) := by
        refine norm_iterate_sub_le_grid hS0 (max M₀ 0) (ε' / (2 * (max M₀ 0 * T + 1)) * Δt i)
          (Δt i) v (m i) (fun k hk => ?_) fun k hk => ?_
        · refine hM (Δt i) (hΔt i) k ?_
          exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (hΔt i).1.le) (hmT i)
        · refine hloc (Δt i) (hΔt i) hAi _
            ⟨mul_nonneg (Nat.cast_nonneg _) (hΔt i).1.le, ?_⟩
          refine le_trans (mul_le_mul_of_nonneg_right ?_ (hΔt i).1.le) (hmT i)
          exact_mod_cast hk.le
      have hbound : m i * (max M₀ 0 * (ε' / (2 * (max M₀ 0 * T + 1)) * Δt i)) < ε' / 2 := by
        have hexp : (m i : ℝ) * (max M₀ 0 * (ε' / (2 * (max M₀ 0 * T + 1)) * Δt i))
            = (max M₀ 0 * ((m i : ℝ) * Δt i)) * (ε' / (2 * (max M₀ 0 * T + 1))) := by ring
        have h1 : max M₀ 0 * ((m i : ℝ) * Δt i) ≤ max M₀ 0 * T :=
          mul_le_mul_of_nonneg_left (hmT i) hMnn
        have h3 : max M₀ 0 * T * (ε' / (2 * (max M₀ 0 * T + 1))) < ε' / 2 := by
          have hne : (max M₀ 0 * T + 1) ≠ 0 := ne_of_gt (by linarith)
          have key : ε' / 2 - max M₀ 0 * T * (ε' / (2 * (max M₀ 0 * T + 1)))
              = ε' / (2 * (max M₀ 0 * T + 1)) := by
            field_simp
            ring
          linarith [hεpos, key]
        rw [hexp]
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h1 hεpos.le) h3
      have htri : ‖(C (Δt i) ^ m i) v - S t v‖
          ≤ ‖(C (Δt i) ^ m i) v - S ((m i : ℝ) * Δt i) v‖ + ‖S ((m i : ℝ) * Δt i) v - S t v‖ := by
        have h := norm_add_le ((C (Δt i) ^ m i) v - S ((m i : ℝ) * Δt i) v)
          (S ((m i : ℝ) * Δt i) v - S t v)
        rwa [sub_add_sub_cancel] at h
      rw [dist_eq_norm]
      calc ‖(C (Δt i) ^ m i) v - S t v‖
          ≤ ‖(C (Δt i) ^ m i) v - S ((m i : ℝ) * Δt i) v‖
            + ‖S ((m i : ℝ) * Δt i) v - S t v‖ := htri
        _ < ε' / 2 + ε' / 2 := add_lt_add (hgrid.trans_lt hbound) hBi
        _ = ε' := by ring
    -- and then everywhere, by the density criterion
    have hall : Tendsto (fun i => (C (Δt i) ^ m i) u₀) atTop (𝓝 (S t u₀)) :=
      ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded hcons.1
        (fun i => hM (Δt i) (hΔt i) (m i) (hmT i)) hdense u₀
    have hconst : Tendsto (fun _ : ℕ => S t u₀) atTop (𝓝 (S t u₀)) := tendsto_const_nhds
    have hz := (hall.sub hconst).norm
    simp only [sub_self, norm_zero] at hz
    exact hz
  · -- convergence gives stability
    intro hconv
    rcases le_or_gt Δ₀ 0 with hΔ₀ | hΔ₀
    · exact ⟨0, fun Δt hΔt => absurd (lt_of_lt_of_le hΔt.1 (hΔt.2.trans hΔ₀)) (lt_irrefl 0)⟩
    by_contra hns
    -- instability at every scale of step size
    have hsmall : ∀ k : ℕ, ∃ Δt : ℝ, Δt ∈ Ioc (0 : ℝ) Δ₀ ∧ Δt ≤ 1 / (k + 1) ∧
        ∃ mm : ℕ, (mm : ℝ) * Δt ≤ T ∧ (k : ℝ) < ‖C Δt ^ mm‖ := by
      intro k
      by_contra hcon
      push Not at hcon
      refine hns (isStable_of_isStable_below (a := min Δ₀ (1 / (k + 1)))
        (lt_min hΔ₀ (by positivity)) hC ⟨(k : ℝ), fun Δt hΔt mm hm => ?_⟩)
      exact hcon Δt ⟨hΔt.1, hΔt.2.trans (min_le_left _ _)⟩ (hΔt.2.trans (min_le_right _ _)) mm hm
    choose Δt hΔtmem hΔtsmall m hmT hnorm using hsmall
    -- the step sizes tend to zero and the discrete times have a convergent subsequence
    have hΔt0 : Tendsto Δt atTop (𝓝 0) := by
      refine squeeze_zero (fun k => (hΔtmem k).1.le) hΔtsmall ?_
      simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hmem : ∀ k, (m k : ℝ) * Δt k ∈ Icc (0 : ℝ) T := fun k =>
      ⟨mul_nonneg (Nat.cast_nonneg _) (hΔtmem k).1.le, hmT k⟩
    obtain ⟨t, ht, φ, hφ, hφlim⟩ :=
      (isCompact_Icc (a := (0 : ℝ)) (b := T)).tendsto_subseq hmem
    -- along it, convergence bounds every orbit, so uniform boundedness bounds the norms
    have hbdd : BddAbove (Set.range fun k => ‖C (Δt (φ k)) ^ m (φ k)‖) := by
      by_contra hnb
      obtain ⟨v, hv⟩ := ContinuousLinearMap.exists_not_tendsto_of_not_bddAbove hnb (S t)
      refine hv (tendsto_iff_norm_sub_tendsto_zero.2 ?_)
      exact hconv t ht v (fun k => Δt (φ k)) (fun k => m (φ k)) (fun k => hΔtmem (φ k))
        (fun k => hmT (φ k)) (hΔt0.comp hφ.tendsto_atTop) hφlim
    obtain ⟨M, hMbd⟩ := hbdd
    obtain ⟨k, hk⟩ := exists_nat_gt M
    refine absurd (hMbd ⟨k, rfl⟩) (not_le.2 ?_)
    exact lt_of_lt_of_le hk (le_trans (by exact_mod_cast hφ.le_apply) (hnorm (φ k)).le)

end FiniteDifference
