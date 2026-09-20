import Numlib.Analysis.PDE.Bochner.SpaceTime
import Numlib.Analysis.PDE.DirichletLaplacian
import Numlib.Analysis.PDE.Elliptic.Spectral

/-!
# The heat equation

The heat equation `∂ₜu − Δu = 0` on `Ω × (0, ∞)`, `u = 0` on `∂Ω × (0, ∞)`, `u(·, 0) = u₀`, in the
form of [brezis2011functional] chapter 10: a curve `u : ℝ → L²(Ω)` with `u' + A u = 0`, `A` the
Dirichlet Laplacian of `Numlib/Analysis/PDE/DirichletLaplacian`, to which the Hille–Yosida theory
of chapter 7 (`Numlib/Analysis/InnerProductSpace/MaximalMonotone`,
`Numlib/Analysis/ODE/HilleYosida`) applies because `A` is self-adjoint and maximal monotone. This
module carries §10.1 — existence, uniqueness, the smoothing estimates, the regularity classes,
the energy identities (Theorems 10.1 and 10.2, Remarks 1, 3) — and is the parent of
`Heat/MaximumPrinciple` (§10.2, Theorems 10.3–10.5, Stampacchia's truncation in time) and
`Heat/Classical` (§10.2, Theorem 10.6, the classical maximum principle, and Remark 4).
`Ω : Opens (EuclideanSpace ℝ (Fin N))`, `L²(Ω) = Lp ℝ 2 (volume.restrict Ω)`.

## The solution notion

The book fixes the Bochner reading ("when we write `u(t)` we mean the function `x ↦ u(x, t)`, an
element of `H`"): `Heat.IsSolution Ω u₀ u` is chapter 7's
`LinearPMap.IsSolutionOn (dirichletLaplacian Ω) u₀ (Ioi 0) u` (`u 0 = u₀`, `u t ∈ D(A)` and
`u' = −A u` for `t > 0`) together with `ContinuousOn u (Ici 0)` and `ContDiffOn ℝ 1 u (Ioi 0)`,
the class `C([0, ∞); H) ∩ C¹((0, ∞); H) ∩ C((0, ∞); D(A))` of Theorem 7.7 (the last clause is
automatic from the equation). The solution is the semigroup,
`Heat.solution Ω u₀ = fun t ↦ (dirichletLaplacian Ω).semigroup t u₀`, so that its linearity in
`u₀` and the contraction `‖u(t)‖ ≤ ‖u₀‖` are chapter 7's. The boundary condition sits in
`D(A) ⊆ H¹₀(Ω)`, as the book says ("the boundary condition (2) has been incorporated in the
definition of the domain of `A`").

## What holds on an arbitrary open set, and what needs a regular domain

With the weak domain `D(A) = {u ∈ H¹₀ : Δu ∈ L²}`, existence and uniqueness
(`Heat.existsUnique_isSolution`), the estimates `‖u(t)‖ ≤ ‖u₀‖` and `‖u'(t)‖ ≤ ‖u₀‖ / t`, the
smoothing `u ∈ C^∞((0, ∞); L²)` with `u(t) ∈ D(A^ℓ)` and the parabolic bound
`‖u^{(k)}(t)‖ ≤ (k/t)^k ‖u₀‖`, the energy identity (6), Theorem 10.2 (a)'s `u ∈ C([0, ∞); H¹₀)`
with (11), and (b)'s `u ∈ C([0, ∞); D(A))` with its identity all hold for every open `Ω` — they
are Theorems 7.4, 7.5, 7.7 plus the identity `⟪A u, u⟫ = ∫ |∇u|²`. The regular-domain hypothesis
of the book (`IsContDiffChartDomain n Ω`, `Bornology.IsBounded (frontier Ω)`) enters only through
the identification of `D(A^ℓ)` with `H^{2ℓ}(Ω)` (`dirichletLaplacian.powDomainToSobolevL`,
Theorem 9.25) to yield the clauses `u ∈ C^k((0, ∞); H^{2ℓ}(Ω))` and, with the Sobolev embedding
of Corollary 9.15 and the space–time bridge of `Numlib/Analysis/PDE/Bochner/SpaceTime`, the
book's `u ∈ C^∞(Ω̄ × [ε, ∞))`.

## The semigroup lifts

The derivatives `u^{(j)} = (−A)^j u` and the parabolic bounds are proved for the semigroup of any
self-adjoint maximal monotone operator: `LinearPMap.semigroupLift A u₀ ℓ t` is the unique element
of `D(A^ℓ)` over `S_A(t) u₀` (`t > 0`), its coordinates `A^j S_A(t) u₀` are differentiable in
`t` with `d/dt A^j S_A(t) u₀ = −A^{j+1} S_A(t) u₀`
(`LinearPMap.hasDerivAt_applyL_semigroupLift`), and `‖A^j S_A(t) u₀‖ ≤ (j/t)^j ‖u₀‖`
(`LinearPMap.norm_applyL_semigroupLift_le`). The energy identity (6) is likewise abstract
(`LinearPMap.IsSolutionOn.energy_Ioi`, for a monotone `A`). These belong beside Theorem 7.7 in
`Numlib/Analysis/ODE/HilleYosida` and are recorded here because chapter 10 is their consumer.

## Two clauses stated in weaker form, deliberately

`u ∈ L²(0, ∞; H¹₀(Ω))` in Theorem 10.1 and `u ∈ L²(0, ∞; H²)`, `L²(0, ∞; H³)` in Theorem 10.2
are false on unbounded domains as written (on `Ω = ℝ` with a Gaussian datum,
`‖u(t)‖²_{L²} ~ (1 + 2t)^{−1/2}` is not integrable in `t`); what the book's proofs show, and what
is stated here, is `∫₀^∞ ‖∇u(t)‖² dt ≤ ½ ‖u₀‖²`, `∫₀^∞ ‖u'(t)‖² dt ≤ ½ ‖∇u₀‖²`,
`∫₀^∞ ‖∇Δu(t)‖² dt ≤ ½ ‖Δu₀‖²`; the Bochner memberships follow for bounded `Ω` by Poincaré
(Corollary 9.19, `SobolevEuclideanZero.norm_le_gradNorm`) and are stated under
`Bornology.IsBounded (Ω : Set _)`.

## References

[brezis2011functional], §10.1: Theorems 10.1, 10.2, Remarks 1, 3; chapter 7, Theorems 7.4, 7.5,
7.7.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

/-! ### The solution notion, existence and uniqueness -/

namespace Heat

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

variable (Ω) in
/-- **A solution of the heat equation** `∂ₜu − Δu = 0` in `Ω × (0, ∞)`, `u = 0` on `Γ × (0, ∞)`,
`u(·, 0) = u₀` ([brezis2011functional] §10.1, (1)–(3)) in the class (4) of Theorem 10.1 with the
weak domain `D(A)` in place of `H² ∩ H¹₀`: a curve `u : ℝ → L²(Ω)` which solves `u' + A u = 0`
on `(0, ∞)` with `u(0) = u₀` for the Dirichlet Laplacian `A` (chapter 7's `IsSolutionOn`: (1) is
the derivative clause, (2) is `u t ∈ D(A) ⊆ H¹₀(Ω)`, (3) is `u 0 = u₀`), continuous on `[0, ∞)`
and `C¹` on `(0, ∞)`. The clause `u ∈ C((0, ∞); D(A))` follows
(`Heat.IsSolution.continuousOn_apply`), since `A (u t) = −u'(t)`. -/
structure IsSolution (u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) : Prop where
  /-- `u' + A u = 0` on `(0, ∞)`, `u 0 = u₀`, `u t ∈ D(A)` for `t > 0`. -/
  toIsSolutionOn : (dirichletLaplacian Ω).IsSolutionOn u₀ (Ioi 0) u
  /-- `u ∈ C([0, ∞); L²(Ω))`. -/
  continuousOn : ContinuousOn u (Ici 0)
  /-- `u ∈ C¹((0, ∞); L²(Ω))`. -/
  contDiffOn : ContDiffOn ℝ 1 u (Ioi 0)

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u v : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- The initial condition (3): `u 0 = u₀`. -/
theorem apply_zero (h : IsSolution Ω u₀ u) : u 0 = u₀ := h.toIsSolutionOn.apply_zero

/-- The boundary condition (2): `u t ∈ D(A) ⊆ H¹₀(Ω)` for `t > 0`. -/
theorem mem_domain (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    u t ∈ (dirichletLaplacian Ω).domain :=
  h.toIsSolutionOn.mem_domain t ht

/-- The equation (1): `u'(t) = −A (u t) = Δ u(t)` for `t > 0`. -/
theorem hasDerivAt (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    HasDerivAt u (-(dirichletLaplacian Ω ⟨u t, h.mem_domain ht⟩)) t :=
  (h.toIsSolutionOn.hasDerivWithinAt t ht).hasDerivAt (Ioi_mem_nhds ht)

/-- `deriv u t = −A (u t)` for `t > 0`. -/
theorem deriv_eq (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    deriv u t = -(dirichletLaplacian Ω ⟨u t, h.mem_domain ht⟩) :=
  (h.hasDerivAt ht).deriv

/-- **Uniqueness** ([brezis2011functional] Theorem 10.1): two solutions with the same datum agree
on `[0, ∞)` — chapter 7's Step 1 (`‖u − v‖` is nonincreasing on `(0, ∞)` by the monotonicity of
`A`, continuous on `[0, ∞)`, and zero at `0`). -/
theorem unique (h : IsSolution Ω u₀ u) (h' : IsSolution Ω u₀ v) : EqOn u v (Ici 0) :=
  dirichletLaplacian_isMonotone.eqOn_of_isSolutionOn_Ioi h.toIsSolutionOn h'.toIsSolutionOn
    h.continuousOn h'.continuousOn

end IsSolution

variable (Ω) in
/-- **The solution of the heat equation with datum `u₀`**: the contraction semigroup of chapter 7
(Remark 5) applied to the datum, `t ↦ S_A(t) u₀` for the Dirichlet Laplacian `A`. -/
def solution (u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  fun t ↦ (dirichletLaplacian Ω).semigroup t u₀

variable (u₀ v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))

/-- `solution Ω u₀ t = S_A(t) u₀`. -/
theorem solution_apply (t : ℝ) : solution Ω u₀ t = (dirichletLaplacian Ω).semigroup t u₀ :=
  rfl

/-- The solution is additive in the datum. -/
theorem solution_add (t : ℝ) : solution Ω (u₀ + v₀) t = solution Ω u₀ t + solution Ω v₀ t :=
  map_add _ _ _

/-- The solution is homogeneous in the datum. -/
theorem solution_smul (c : ℝ) (t : ℝ) : solution Ω (c • u₀) t = c • solution Ω u₀ t :=
  map_smul _ _ _

/-- The solution of a difference of data is the difference of the solutions. -/
theorem solution_sub (t : ℝ) : solution Ω (u₀ - v₀) t = solution Ω u₀ t - solution Ω v₀ t :=
  map_sub _ _ _

/-- The solution with datum `0` is `0`. -/
theorem solution_zero (t : ℝ) : solution Ω 0 t = 0 :=
  map_zero _

/-- **The contraction property** `‖u(t)‖ ≤ ‖u₀‖` for `t ≥ 0` (chapter 7's Remark 5 (a)); applied
to differences of solutions it is the estimate of Corollary 10.5's proof. -/
theorem norm_solution_le {t : ℝ} (ht : 0 ≤ t) : ‖solution Ω u₀ t‖ ≤ ‖u₀‖ :=
  dirichletLaplacian_isMaximalMonotone.norm_semigroup_apply_le ht u₀

/-- **Existence** ([brezis2011functional] Theorem 10.1): on every open `Ω` and for every
`u₀ ∈ L²(Ω)`, `t ↦ S_A(t) u₀` is a solution — Theorem 7.7 for the self-adjoint maximal monotone
Dirichlet Laplacian (`LinearPMap.isSolutionOn_semigroup_Ioi`). -/
theorem isSolution_solution : IsSolution Ω u₀ (solution Ω u₀) :=
  let h := isSolutionOn_semigroup_Ioi dirichletLaplacian_isMaximalMonotone
    dirichletLaplacian_isFormalAdjoint u₀
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- **Theorem 10.1, existence and uniqueness** ([brezis2011functional]) on an arbitrary open
set: for every `u₀ ∈ L²(Ω)` there is a solution, and any two solutions agree on `[0, ∞)`
(`IsSolution` does not constrain negative times). -/
theorem existsUnique_isSolution :
    ∃ u, IsSolution Ω u₀ u ∧ ∀ v, IsSolution Ω u₀ v → EqOn v u (Ici 0) :=
  ⟨solution Ω u₀, isSolution_solution u₀, fun _ hv ↦ hv.unique (isSolution_solution u₀)⟩

variable {u₀ v₀}

namespace IsSolution

variable {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- Every solution is the semigroup applied to its datum, on `[0, ∞)`. -/
theorem eqOn_solution (h : IsSolution Ω u₀ u) : EqOn u (solution Ω u₀) (Ici 0) :=
  h.unique (isSolution_solution u₀)

/-- `u t = S_A(t) u₀` for `t ≥ 0`. -/
theorem apply_eq (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 ≤ t) :
    u t = (dirichletLaplacian Ω).semigroup t u₀ :=
  h.eqOn_solution ht

/-- **`‖u(t)‖ ≤ ‖u₀‖` for `t ≥ 0`** ([brezis2011functional] Theorem 7.7's first estimate). -/
theorem norm_le (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 ≤ t) : ‖u t‖ ≤ ‖u₀‖ := by
  rw [h.eqOn_solution ht]
  exact norm_solution_le u₀ ht

/-- **The smoothing estimate `‖A u(t)‖ ≤ ‖u₀‖ / t`** for `t > 0` ([brezis2011functional]
Theorem 7.7 (26)). -/
theorem norm_apply_le (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    ‖dirichletLaplacian Ω ⟨u t, h.mem_domain ht⟩‖ ≤ ‖u₀‖ / t := by
  obtain ⟨hmem, hb⟩ := semigroup_apply_mem_domain_of_isFormalAdjoint
    dirichletLaplacian_isMaximalMonotone dirichletLaplacian_isFormalAdjoint u₀ ht
  have : (⟨u t, h.mem_domain ht⟩ : (dirichletLaplacian Ω).domain)
      = ⟨(dirichletLaplacian Ω).semigroup t u₀, hmem⟩ := Subtype.ext (h.apply_eq ht.le)
  rw [this]
  exact hb

/-- **The parabolic smoothing bound `‖u'(t)‖ = ‖A u(t)‖ ≤ ‖u₀‖ / t`** for `t > 0`
([brezis2011functional] Theorem 7.7 (26)). -/
theorem norm_deriv_le (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) : ‖deriv u t‖ ≤ ‖u₀‖ / t := by
  rw [h.deriv_eq ht, norm_neg]
  exact h.norm_apply_le ht

/-- **Smoothing in time, chapter 7's form** ([brezis2011functional] Theorem 7.7 (27)):
`u ∈ C^k((0, ∞); D(A^ℓ))` for all `k, ℓ`. -/
theorem contDiffOnPowDomain (h : IsSolution Ω u₀ u) (k ℓ : ℕ) :
    (dirichletLaplacian Ω).ContDiffOnPowDomain k ℓ u (Ioi 0) :=
  (contDiffOnPowDomain_semigroup_Ioi dirichletLaplacian_isMaximalMonotone
    dirichletLaplacian_isFormalAdjoint u₀ k ℓ).congr fun _ ht ↦ (h.apply_eq (le_of_lt ht)).symm

/-- `u ∈ C((0, ∞); D(A))`, in chapter 7's spelling. -/
theorem contDiffOnPowDomain_one (h : IsSolution Ω u₀ u) :
    (dirichletLaplacian Ω).ContDiffOnPowDomain 0 1 u (Ioi 0) :=
  h.contDiffOnPowDomain 0 1

/-- **`u ∈ C((0, ∞); D(A))`**: any function equal to `t ↦ A (u t)` on `(0, ∞)` is continuous
there, being `−u'` ([brezis2011functional] Theorem 10.1, (4)). -/
theorem continuousOn_apply (h : IsSolution Ω u₀ u)
    {g : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hg : ∀ t (ht : 0 < t), g t = dirichletLaplacian Ω ⟨u t, h.mem_domain ht⟩) :
    ContinuousOn g (Ioi 0) := by
  refine (h.contDiffOn.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).neg.congr fun t ht ↦ ?_
  change g t = -deriv u t
  rw [hg t ht, h.deriv_eq ht, neg_neg]

/-- **`u(t) ∈ D(A^ℓ)` for every `t > 0` and every `ℓ`** ([brezis2011functional] Theorem 7.7,
and Remark 1's necessary condition (12) on final data). -/
theorem exists_powDomain (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) (ℓ : ℕ) :
    ∃ x : (dirichletLaplacian Ω).PowDomain ℓ, applyL (dirichletLaplacian Ω) ℓ 0 x = u t := by
  rw [h.apply_eq ht.le]
  exact exists_powDomain_semigroup_apply_of_isFormalAdjoint dirichletLaplacian_isMaximalMonotone
    dirichletLaplacian_isFormalAdjoint u₀ ℓ ht

/-- **`u ∈ C^∞((0, ∞); L²(Ω))`** ([brezis2011functional] Theorem 10.1, the smoothing). -/
theorem contDiffOn_top (h : IsSolution Ω u₀ u) : ContDiffOn ℝ ∞ u (Ioi 0) := by
  refine contDiffOn_infty.2 fun k ↦ ?_
  obtain ⟨w, hw0, hw⟩ := h.contDiffOnPowDomain k 0
  exact ((applyL (dirichletLaplacian Ω) 0 0).contDiff.comp_contDiffOn hw).congr
    fun t ht ↦ (hw0 t ht).symm

/-- `u` agrees near every `t > 0` with `τ ↦ A^0 (semigroupLift τ)`. -/
theorem eventuallyEq_applyL_semigroupLift (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) (ℓ : ℕ) :
    u =ᶠ[𝓝 t] fun τ ↦ applyL (dirichletLaplacian Ω) ℓ 0
      (semigroupLift (dirichletLaplacian Ω) u₀ ℓ τ) := by
  filter_upwards [Ioi_mem_nhds ht] with τ hτ
  rw [applyL_zero_semigroupLift dirichletLaplacian_isMaximalMonotone
    dirichletLaplacian_isFormalAdjoint hτ, h.apply_eq (le_of_lt hτ)]

/-- **The derivatives are the iterates**: `u^{(j)}(t) = (−A)^j u(t)` for `t > 0` and `j ≤ ℓ`,
the iterate read on the lift `semigroupLift`. Induction on `j` with
`LinearPMap.hasDerivAt_applyL_semigroupLift`. -/
theorem iteratedDeriv_eq_applyL_semigroupLift (h : IsSolution Ω u₀ u) (ℓ : ℕ) :
    ∀ j : ℕ, ∀ hj : j ≤ ℓ, ∀ t : ℝ, 0 < t → iteratedDeriv j u t
      = (-1 : ℝ) ^ j • applyL (dirichletLaplacian Ω) ℓ ⟨j, Nat.lt_succ_of_le hj⟩
        (semigroupLift (dirichletLaplacian Ω) u₀ ℓ t) := by
  intro j
  induction j with
  | zero =>
    intro _ t ht
    rw [iteratedDeriv_zero, pow_zero, one_smul]
    exact (h.eventuallyEq_applyL_semigroupLift ht ℓ).eq_of_nhds
  | succ j ih =>
    intro hj t ht
    have hj' : j ≤ ℓ := Nat.le_of_succ_le hj
    have hloc : iteratedDeriv j u =ᶠ[𝓝 t] fun τ ↦ (-1 : ℝ) ^ j •
        applyL (dirichletLaplacian Ω) ℓ ⟨j, Nat.lt_succ_of_le hj'⟩
          (semigroupLift (dirichletLaplacian Ω) u₀ ℓ τ) := by
      filter_upwards [Ioi_mem_nhds ht] with τ hτ
      exact ih hj' τ hτ
    have hd : HasDerivAt (fun τ ↦ (-1 : ℝ) ^ j •
        applyL (dirichletLaplacian Ω) ℓ ⟨j, Nat.lt_succ_of_le hj'⟩
          (semigroupLift (dirichletLaplacian Ω) u₀ ℓ τ))
        ((-1 : ℝ) ^ j • -(applyL (dirichletLaplacian Ω) ℓ ⟨j + 1, Nat.lt_succ_of_le hj⟩
          (semigroupLift (dirichletLaplacian Ω) u₀ ℓ t))) t :=
      (hasDerivAt_applyL_semigroupLift dirichletLaplacian_isMaximalMonotone
        dirichletLaplacian_isFormalAdjoint (u₀ := u₀) ht ⟨j, Nat.lt_of_succ_le hj⟩).const_smul
        ((-1 : ℝ) ^ j)
    rw [iteratedDeriv_succ, hloc.deriv_eq, hd.deriv, smul_neg, pow_succ, mul_neg, mul_one,
      neg_smul]

/-- **`u^{(j)} = (−A)^j u` on `(0, ∞)`** ([brezis2011functional] §10.1, lines after (7)): for
`t > 0`, any lift `x ∈ D(A^ℓ)` of `u(t)` and `j ≤ ℓ`, `iteratedDeriv j u t = (−1)^j A^j x`. -/
theorem iteratedDeriv_eq (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) {ℓ : ℕ}
    (x : (dirichletLaplacian Ω).PowDomain ℓ) (hx : applyL (dirichletLaplacian Ω) ℓ 0 x = u t)
    (j : Fin (ℓ + 1)) :
    iteratedDeriv j u t = (-1 : ℝ) ^ (j : ℕ) • applyL (dirichletLaplacian Ω) ℓ j x := by
  have hx' : x = semigroupLift (dirichletLaplacian Ω) u₀ ℓ t :=
    eq_semigroupLift dirichletLaplacian_isMaximalMonotone dirichletLaplacian_isFormalAdjoint ht
      (hx.trans (h.apply_eq ht.le))
  rw [hx']
  exact h.iteratedDeriv_eq_applyL_semigroupLift ℓ j (Nat.lt_succ_iff.1 j.2) t ht

/-- **Parabolic smoothing of every order**: `‖u^{(k)}(t)‖ ≤ (k/t)^k ‖u₀‖` for `t > 0`
(`Heat.IsSolution.norm_deriv_le` iterated along the subdivision `0 < t/k < 2t/k < ⋯ < t` with
the semigroup law, `LinearPMap.norm_applyL_semigroupLift_le`). Not in the book; it is the
ingredient `‖u_t(t)‖ ≤ C ‖u₀‖ / t` of parabolic error analyses. -/
theorem norm_iteratedDeriv_le (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ‖iteratedDeriv k u t‖ ≤ ((k : ℝ) / t) ^ k * ‖u₀‖ := by
  have := h.iteratedDeriv_eq_applyL_semigroupLift k k le_rfl t ht
  rw [this, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hb := norm_applyL_semigroupLift_le dirichletLaplacian_isMaximalMonotone
    dirichletLaplacian_isFormalAdjoint (u₀ := u₀) (ℓ := k) ht ⟨k, Nat.lt_succ_self k⟩
  exact hb

/-- **The energy identity (6)** ([brezis2011functional] Theorem 10.1): for `T > 0` and
`g t = ⟪A u(t), u(t)⟫ = ∫_Ω |∇u(t)|²` (`dirichletLaplacian_inner_self_eq_dirichletForm`) on
`(0, ∞)`, `g` is integrable on `(0, T]` and `½ ‖u(T)‖² + ∫₀ᵀ g = ½ ‖u₀‖²`
(`LinearPMap.IsSolutionOn.energy_Ioi`). -/
theorem energy (h : IsSolution Ω u₀ u) {g : ℝ → ℝ}
    (hg : ∀ t (ht : 0 < t), g t = ⟪dirichletLaplacian Ω ⟨u t, h.mem_domain ht⟩, u t⟫_ℝ)
    {T : ℝ} (hT : 0 < T) :
    IntegrableOn g (Ioc 0 T) ∧
      1 / 2 * ‖u T‖ ^ 2 + ∫ t in (0 : ℝ)..T, g t = 1 / 2 * ‖u₀‖ ^ 2 :=
  IsSolutionOn.energy_Ioi dirichletLaplacian_isMonotone h.toIsSolutionOn h.continuousOn
    h.contDiffOn hg hT

/-- **The gradient part of `u ∈ L²(0, ∞; H¹₀(Ω))`** ([brezis2011functional] Theorem 10.1): the
function `g t = ⟪A u(t), u(t)⟫ = ∫_Ω |∇u(t)|²` is integrable on `(0, ∞)` with
`∫₀^∞ g ≤ ½ ‖u₀‖²`, by the energy identity for every `T` and `‖u(T)‖² ≥ 0`. -/
theorem integral_inner_apply_le (h : IsSolution Ω u₀ u) {g : ℝ → ℝ}
    (hg : ∀ t (ht : 0 < t), g t = ⟪dirichletLaplacian Ω ⟨u t, h.mem_domain ht⟩, u t⟫_ℝ) :
    IntegrableOn g (Ioi 0) ∧ ∫ t in Ioi 0, g t ≤ 1 / 2 * ‖u₀‖ ^ 2 := by
  have hg0 : ∀ t, 0 < t → 0 ≤ g t := fun t ht ↦ by
    rw [hg t ht]
    exact dirichletLaplacian_inner_self_nonneg _
  have hT : ∀ T : ℝ, 0 < T → ∫ t in (0 : ℝ)..T, g t ≤ 1 / 2 * ‖u₀‖ ^ 2 := fun T hT ↦ by
    have := (h.energy hg hT).2
    nlinarith [norm_nonneg (u T)]
  have hb : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hfi : ∀ n : ℕ, IntegrableOn g (Ioc 0 ((n : ℝ) + 1)) := fun n ↦
    (h.energy hg (by positivity)).1
  have hgi : IntegrableOn g (Ioi 0) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (1 / 2 * ‖u₀‖ ^ 2) 0 hfi hb
      (Eventually.of_forall fun n ↦ ?_)
    have hn : (0 : ℝ) ≤ n + 1 := by positivity
    refine (le_of_eq ?_).trans (hT ((n : ℝ) + 1) (by positivity))
    rw [intervalIntegral.integral_of_le hn, intervalIntegral.integral_of_le hn]
    exact setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ Real.norm_of_nonneg (hg0 t ht.1)
  refine ⟨hgi, ?_⟩
  refine le_of_tendsto (intervalIntegral_tendsto_integral_Ioi 0 hgi hb)
    (Eventually.of_forall fun n ↦ hT ((n : ℝ) + 1) (by positivity))

end IsSolution

end Heat

/-! ### The second derivative, and the `H¹₀`-lift of `D(A)` -/

namespace Heat

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- `deriv u t = −A² x` on the lift `x ∈ D(A²)` of `u(t)`, `t > 0`. -/
theorem deriv_eq_neg_applyL_semigroupLift (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    deriv u t = -applyL (dirichletLaplacian Ω) 2 1
      (semigroupLift (dirichletLaplacian Ω) u₀ 2 t) := by
  have := h.iteratedDeriv_eq_applyL_semigroupLift 2 1 (by norm_num) t ht
  rwa [iteratedDeriv_one, pow_one, neg_one_smul] at this

/-- **`u'(t) ∈ D(A)` for `t > 0`**: `u'(t) = −A u(t)` and `u(t) ∈ D(A²)`. -/
theorem deriv_mem_domain (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    deriv u t ∈ (dirichletLaplacian Ω).domain := by
  rw [h.deriv_eq_neg_applyL_semigroupLift ht]
  exact neg_mem (applyL_mem_domain _ 1)

/-- **The equation for the derivative, `u'' = −A u'`** on `(0, ∞)`: `u'` is again a solution of
the equation, since `u' = −A u = −A² x` on the lift and the iterates are differentiable
(`LinearPMap.hasDerivAt_applyL_semigroupLift`). -/
theorem hasDerivAt_deriv (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (deriv u) (-(dirichletLaplacian Ω ⟨deriv u t, h.deriv_mem_domain ht⟩)) t := by
  have hloc : deriv u =ᶠ[𝓝 t] fun τ ↦ -applyL (dirichletLaplacian Ω) 2 1
      (semigroupLift (dirichletLaplacian Ω) u₀ 2 τ) := by
    filter_upwards [Ioi_mem_nhds ht] with τ hτ
    exact h.deriv_eq_neg_applyL_semigroupLift hτ
  have hd := (hasDerivAt_applyL_semigroupLift dirichletLaplacian_isMaximalMonotone
    dirichletLaplacian_isFormalAdjoint (u₀ := u₀) ht (1 : Fin 2)).neg
  rw [neg_neg] at hd
  refine (hd.congr_of_eventuallyEq hloc).congr_deriv ?_
  have e1 : (⟨deriv u t, h.deriv_mem_domain ht⟩ : (dirichletLaplacian Ω).domain)
      = -⟨applyL (dirichletLaplacian Ω) 2 1 (semigroupLift (dirichletLaplacian Ω) u₀ 2 t),
          applyL_mem_domain _ 1⟩ :=
    Subtype.ext (h.deriv_eq_neg_applyL_semigroupLift ht)
  rw [e1, LinearPMap.map_neg, neg_neg]
  exact (apply_applyL _ 1).symm

/-- `‖u'(t)‖² = ⟪A u(t), u(t)⟫`'s companion: `⟪A u'(t), u(t)⟫ = −‖u'(t)‖²` for `t > 0`, by the
symmetry of `A` and `u' = −A u`. -/
theorem inner_apply_deriv_eq (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    ⟪dirichletLaplacian Ω ⟨deriv u t, h.deriv_mem_domain ht⟩, u t⟫_ℝ = -‖deriv u t‖ ^ 2 := by
  have hFA := dirichletLaplacian_isFormalAdjoint ⟨deriv u t, h.deriv_mem_domain ht⟩
    ⟨u t, h.mem_domain ht⟩
  have e2 : dirichletLaplacian Ω ⟨u t, h.mem_domain ht⟩ = -deriv u t := by
    rw [h.deriv_eq ht, neg_neg]
  rw [e2] at hFA
  refine hFA.trans ?_
  change ⟪deriv u t, -deriv u t⟫_ℝ = -‖deriv u t‖ ^ 2
  rw [inner_neg_right, real_inner_self_eq_norm_sq]

end IsSolution

end Heat

/-! ### Theorem 10.2 (a): `u₀ ∈ H¹₀(Ω)` -/

namespace Heat

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- **The solution of the `H¹₀`-realization is a solution in `L²`**: for `v₀ ∈ H¹₀(Ω)` and the
Theorem 7.7 solution `w` of `w' + A₁ w = 0`, `w(0) = v₀`, in `H¹₀(Ω)`, the curve `fnL ∘ w` solves
the heat equation in `L²(Ω)` with datum `fnL v₀` (`fnL_dirichletLaplacianH10_apply`). -/
theorem _root_.Heat.isSolution_fnL_of_isSolutionOn_H10 {v₀ : SobolevEuclideanZero N 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v₀
      = u₀) {w : ℝ → SobolevEuclideanZero N 1 2 Ω}
    (hw : (dirichletLaplacianH10 Ω).IsSolutionOn v₀ (Ioi 0) w) (hwc : ContinuousOn w (Ici 0))
    (hwd : ContDiffOn ℝ 1 w (Ioi 0)) :
    IsSolution Ω u₀ fun t ↦ SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      1 2 Ω volume (w t) where
  toIsSolutionOn :=
    { apply_zero := by rw [hw.apply_zero, hv₀]
      mem_domain := fun t ht ↦ (hw.mem_domain t ht).1
      hasDerivWithinAt := fun t ht ↦ by
        have h1 := (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
          volume).hasFDerivAt.comp_hasDerivWithinAt t (hw.hasDerivWithinAt t ht)
        exact h1.congr_deriv ((_root_.map_neg _ _).trans
          (congrArg Neg.neg (fnL_dirichletLaplacianH10_apply ⟨w t, hw.mem_domain t ht⟩))) }
  continuousOn := (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
    volume).continuous.comp_continuousOn hwc
  contDiffOn := (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
    volume).contDiff.comp_contDiffOn hwd

/-- **Theorem 10.2 (a), first clause** ([brezis2011functional]): if `u₀ = fnL v₀` with
`v₀ ∈ H¹₀(Ω)`, then `u ∈ C([0, ∞); H¹₀(Ω))`. Theorem 7.7 for the self-adjoint maximal monotone
`A₁ = dirichletLaplacianH10 Ω` in the Hilbert space `H¹₀(Ω)` gives `w ∈ C([0, ∞); H¹₀)` solving
`w' + A₁ w = 0`, `w(0) = v₀`; `fnL ∘ w` is a solution in `L²`, so it is `u` by uniqueness. Any
open `Ω`. -/
theorem contDiffOnThrough_sobolevZero_of_mem (h : IsSolution Ω u₀ u)
    {v₀ : SobolevEuclideanZero N 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v₀
      = u₀) :
    Bochner.ContDiffOnThrough (SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume) 0 u (Ici 0) := by
  have h4 := isSolutionOn_semigroup_Ioi dirichletLaplacianH10_isMaximalMonotone
    dirichletLaplacianH10_isFormalAdjoint v₀
  have hsol := Heat.isSolution_fnL_of_isSolutionOn_H10 hv₀ h4.1 h4.2.1 h4.2.2.1
  exact ⟨_, contDiffOn_zero.2 h4.2.1, fun t ht ↦ h.unique hsol ht⟩

/-- **The solution is the `A₁`-semigroup read in `L²`**: for `u₀ = fnL v₀`, `v₀ ∈ H¹₀(Ω)`,
`u(t) = fnL (S_{A₁}(t) v₀)` for `t ≥ 0`. -/
theorem apply_eq_fnL_semigroup_H10 (h : IsSolution Ω u₀ u) {v₀ : SobolevEuclideanZero N 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v₀
      = u₀) {t : ℝ} (ht : 0 ≤ t) :
    u t = SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      ((dirichletLaplacianH10 Ω).semigroup t v₀) := by
  have h4 := isSolutionOn_semigroup_Ioi dirichletLaplacianH10_isMaximalMonotone
    dirichletLaplacianH10_isFormalAdjoint v₀
  have hsol := Heat.isSolution_fnL_of_isSolutionOn_H10 hv₀ h4.1 h4.2.1 h4.2.2.1
  exact h.unique hsol ht

/-- The `0`-th coordinate of the `A₁`-semigroup lift is `u(t)` in `L²`, for `t > 0`. -/
theorem fnL_applyL_zero_semigroupLift_H10 (h : IsSolution Ω u₀ u)
    {v₀ : SobolevEuclideanZero N 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v₀
      = u₀) {t : ℝ} (ht : 0 < t) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (applyL (dirichletLaplacianH10 Ω) 1 0 (semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t))
      = u t :=
  (congrArg _ (applyL_zero_semigroupLift dirichletLaplacianH10_isMaximalMonotone
    dirichletLaplacianH10_isFormalAdjoint ht)).trans (h.apply_eq_fnL_semigroup_H10 hv₀ ht.le).symm

/-- The `1`-st coordinate of the `A₁`-semigroup lift is `−u'(t)` in `L²`, for `t > 0`:
`fnL (A₁ y) = A (fnL y) = A u(t) = −u'(t)`. -/
theorem fnL_applyL_one_semigroupLift_H10 (h : IsSolution Ω u₀ u)
    {v₀ : SobolevEuclideanZero N 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v₀
      = u₀) {t : ℝ} (ht : 0 < t) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (applyL (dirichletLaplacianH10 Ω) 1 1 (semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t))
      = -deriv u t := by
  have h1 := apply_applyL (semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t) 0
  have hmem := applyL_mem_domain (semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t) 0
  have h2 := fnL_dirichletLaplacianH10_apply ⟨applyL (dirichletLaplacianH10 Ω) 1 0
    (semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t), hmem⟩
  have h3 : (⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
      volume (applyL (dirichletLaplacianH10 Ω) 1 0 (semigroupLift (dirichletLaplacianH10 Ω) v₀ 1
        t)), hmem.1⟩ : (dirichletLaplacian Ω).domain) = ⟨u t, h.mem_domain ht⟩ :=
    Subtype.ext (h.fnL_applyL_zero_semigroupLift_H10 hv₀ ht)
  have h4 := congrArg (fun z : (dirichletLaplacian Ω).domain ↦ dirichletLaplacian Ω z) h3
  exact (congrArg _ h1.symm).trans (h2.trans (h4.trans (neg_eq_iff_eq_neg.1 (h.deriv_eq ht).symm)))

/-- `⟪A u(t), u(t)⟫ = ∫_Ω |∇v|²` for an `H¹₀`-lift `v` of `u(t)`, `t > 0`. -/
theorem inner_apply_self_eq_dirichletForm (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t)
    {v : SobolevEuclideanZero N 1 2 Ω}
    (hv : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v
      = u t) :
    ⟪dirichletLaplacian Ω ⟨u t, h.mem_domain ht⟩, u t⟫_ℝ
      = dirichletForm Ω (v : SobolevEuclidean N 1 2 Ω) (v : SobolevEuclidean N 1 2 Ω) :=
  dirichletLaplacian_inner_self_eq_dirichletForm ⟨u t, h.mem_domain ht⟩ v.2 hv

/-- `−½ ⟪u'(t), u(t)⟫ = ½ ⟪A u(t), u(t)⟫` for `t > 0`: the book's `φ(t) = ½ ‖∇u(t)‖²` written
without the membership proof. -/
theorem neg_half_inner_deriv_eq (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    -(1 / 2) * ⟪deriv u t, u t⟫_ℝ
      = 1 / 2 * ⟪dirichletLaplacian Ω ⟨u t, h.mem_domain ht⟩, u t⟫_ℝ := by
  rw [h.deriv_eq ht, inner_neg_left]
  ring

/-- **`φ' = −‖u'‖²`** for `φ(t) = −½ ⟪u'(t), u(t)⟫ = ½ ‖∇u(t)‖²` on `(0, ∞)` (the book's
computation in the proof of Theorem 10.2 (a)): `u'' = −A u'` and the symmetry of `A`. -/
theorem hasDerivAt_neg_half_inner_deriv (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t ↦ -(1 / 2) * ⟪deriv u t, u t⟫_ℝ) (-(‖deriv u t‖ ^ 2)) t := by
  have := ((h.hasDerivAt_deriv ht).inner ℝ (h.hasDerivAt ht)).const_mul (-(1 / 2))
  convert this using 1
  rw [← h.deriv_eq ht, inner_neg_left, h.inner_apply_deriv_eq ht, real_inner_self_eq_norm_sq]
  ring

/-- **`½ ‖∇u(t)‖² → ½ ‖∇v₀‖²` as `t → 0⁺`** for `u₀ = fnL v₀`, `v₀ ∈ H¹₀(Ω)`: the continuity
into `H¹₀` at `0` of Theorem 10.2 (a). -/
theorem tendsto_neg_half_inner_deriv_of_mem (h : IsSolution Ω u₀ u)
    {v₀ : SobolevEuclideanZero N 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v₀
      = u₀) :
    Tendsto (fun t ↦ -(1 / 2) * ⟪deriv u t, u t⟫_ℝ) (𝓝[>] 0)
      (𝓝 (1 / 2 * dirichletForm Ω (v₀ : SobolevEuclidean N 1 2 Ω)
        (v₀ : SobolevEuclidean N 1 2 Ω))) := by
  obtain ⟨w, hw, huw⟩ := h.contDiffOnThrough_sobolevZero_of_mem hv₀
  rw [contDiffOn_zero] at hw
  have hw0 : w 0 = v₀ := SobolevMultiIndexZero.fnL_injective
    ((huw 0 self_mem_Ici).symm.trans (h.apply_zero.trans hv₀.symm))
  have hw' : ContinuousOn (fun t ↦ (w t : SobolevEuclidean N 1 2 Ω)) (Ici 0) :=
    continuous_subtype_val.comp_continuousOn hw
  have hwc : ContinuousOn (fun t ↦ 1 / 2 * dirichletForm Ω (w t : SobolevEuclidean N 1 2 Ω)
      (w t : SobolevEuclidean N 1 2 Ω)) (Ici 0) :=
    continuousOn_const.mul (((dirichletForm Ω).continuous.comp_continuousOn hw').clm_apply hw')
  have h1 : Tendsto (fun t ↦ 1 / 2 * dirichletForm Ω (w t : SobolevEuclidean N 1 2 Ω)
      (w t : SobolevEuclidean N 1 2 Ω)) (𝓝[>] 0)
      (𝓝 (1 / 2 * dirichletForm Ω (w 0 : SobolevEuclidean N 1 2 Ω)
        (w 0 : SobolevEuclidean N 1 2 Ω))) :=
    (hwc 0 self_mem_Ici).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have h2 : (fun t ↦ -(1 / 2) * ⟪deriv u t, u t⟫_ℝ) =ᶠ[𝓝[>] 0]
      fun t ↦ 1 / 2 * dirichletForm Ω (w t : SobolevEuclidean N 1 2 Ω)
        (w t : SobolevEuclidean N 1 2 Ω) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact (h.neg_half_inner_deriv_eq ht).trans (congrArg (1 / 2 * ·)
      (h.inner_apply_self_eq_dirichletForm ht (huw t (le_of_lt ht)).symm))
  rw [hw0] at h1
  exact h1.congr' h2.symm

/-- **(11) of Theorem 10.2 (a)** ([brezis2011functional]): for `u₀ = fnL v₀`, `v₀ ∈ H¹₀(Ω)`, and
`T > 0`, `t ↦ ‖u'(t)‖²` is integrable on `(0, T]` and
`∫₀ᵀ ‖u'(t)‖² dt + ½ ⟪A u(T), u(T)⟫ = ½ ∫_Ω |∇v₀|²`, i.e.
`∫₀ᵀ ‖∂ₜu‖² + ½ ‖∇u(T)‖² = ½ ‖∇u₀‖²`. The function `φ(t) = ½ ⟪A u, u⟫ = −½ ⟪u', u⟫` has
`φ' = −‖u'‖²` on `(0, ∞)` (`hasDerivAt_neg_half_inner_deriv`), and `φ(ε) → ½ ∫ |∇v₀|²` by the
continuity into `H¹₀` at `0` (`tendsto_neg_half_inner_deriv_of_mem`). -/
theorem energy_sobolevZero (h : IsSolution Ω u₀ u) {v₀ : SobolevEuclideanZero N 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v₀
      = u₀) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun t ↦ ‖deriv u t‖ ^ 2) (Ioc 0 T) ∧
      (∫ t in (0 : ℝ)..T, ‖deriv u t‖ ^ 2)
        + 1 / 2 * ⟪dirichletLaplacian Ω ⟨u T, h.mem_domain hT⟩, u T⟫_ℝ
      = 1 / 2 * dirichletForm Ω (v₀ : SobolevEuclidean N 1 2 Ω)
        (v₀ : SobolevEuclidean N 1 2 Ω) := by
  have hgc : ContinuousOn (fun t ↦ ‖deriv u t‖ ^ 2) (Ioi 0) :=
    (h.contDiffOn.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).norm.pow 2
  have hφ0 : ∀ t, 0 < t → 0 ≤ -(1 / 2) * ⟪deriv u t, u t⟫_ℝ := fun t ht ↦ by
    rw [h.neg_half_inner_deriv_eq ht]
    exact mul_nonneg (by norm_num) (dirichletLaplacian_inner_self_nonneg _)
  obtain ⟨h1, h2⟩ := integrableOn_Ioc_and_integral_eq_of_hasDerivAt_neg hT
    (fun t ht ↦ h.hasDerivAt_neg_half_inner_deriv ht) (fun t _ ↦ by positivity) hgc hφ0
    (h.tendsto_neg_half_inner_deriv_of_mem hv₀)
  refine ⟨h1, ?_⟩
  rw [← h.neg_half_inner_deriv_eq hT]
  beta_reduce at h2
  linarith

/-- **`∂ₜu ∈ L²(0, ∞; L²(Ω))`** for `u₀ = fnL v₀`, `v₀ ∈ H¹₀(Ω)` ([brezis2011functional]
Theorem 10.2 (a)): `u' ∈ L²((0, ∞); L²(Ω))` with `∫₀^∞ ‖u'(t)‖² dt ≤ ½ ∫_Ω |∇v₀|²`. -/
theorem memLp_deriv (h : IsSolution Ω u₀ u) {v₀ : SobolevEuclideanZero N 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v₀
      = u₀) :
    MemLp (deriv u) 2 (volume.restrict (Ioi 0)) ∧
      ∫ t in Ioi 0, ‖deriv u t‖ ^ 2
        ≤ 1 / 2 * dirichletForm Ω (v₀ : SobolevEuclidean N 1 2 Ω)
          (v₀ : SobolevEuclidean N 1 2 Ω) := by
  have key := integrableOn_Ioi_and_integral_le_of_forall_integral_le
    (g := fun t ↦ ‖deriv u t‖ ^ 2)
    (L := 1 / 2 * dirichletForm Ω (v₀ : SobolevEuclidean N 1 2 Ω) (v₀ : SobolevEuclidean N 1 2 Ω))
    (fun t _ ↦ by positivity)
    (fun T hT ↦ (h.energy_sobolevZero hv₀ hT).1) fun T hT ↦ by
      have := (h.energy_sobolevZero hv₀ hT).2
      have h0 : 0 ≤ ⟪dirichletLaplacian Ω ⟨u T, h.mem_domain hT⟩, u T⟫_ℝ :=
        dirichletLaplacian_inner_self_nonneg ⟨u T, h.mem_domain hT⟩
      beta_reduce
      linarith
  refine ⟨?_, key.2⟩
  rw [memLp_two_iff_integrable_sq_norm
    ((h.contDiffOn.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).aestronglyMeasurable
      measurableSet_Ioi)]
  exact key.1

/-! ### Theorem 10.2 (b): `u₀ ∈ D(A)` -/

/-- **Theorem 10.2 (b), first clause, abstractly** ([brezis2011functional], and Theorem 7.4):
for `u₀ ∈ D(A)`, `u ∈ C¹([0, ∞); L²(Ω))` with `u'(0) = −A u₀` (one-sided), and
`u ∈ C([0, ∞); D(A))`. This is the Hille–Yosida theorem for the datum `u₀ ∈ D(A)`, transported
along `u = S_A(·) u₀`. Any open `Ω`. -/
theorem contDiffOn_Ici_of_mem_domain (h : IsSolution Ω u₀ u)
    (hu₀ : u₀ ∈ (dirichletLaplacian Ω).domain) :
    ContDiffOn ℝ 1 u (Ici 0) ∧
      HasDerivWithinAt u (-(dirichletLaplacian Ω ⟨u₀, hu₀⟩)) (Ici 0) 0 ∧
      (dirichletLaplacian Ω).ContDiffOnPowDomain 0 1 u (Ici 0) := by
  have hA := dirichletLaplacian_isMaximalMonotone (Ω := Ω)
  refine ⟨(hA.contDiffOn_semigroup_apply ⟨u₀, hu₀⟩).congr fun t ht ↦ h.apply_eq ht, ?_, ?_⟩
  · have h1 := (hA.isSolutionOn_semigroup ⟨u₀, hu₀⟩).hasDerivWithinAt 0 self_mem_Ici
    have e : (⟨(dirichletLaplacian Ω).semigroup 0
          ((⟨u₀, hu₀⟩ : (dirichletLaplacian Ω).domain) :
            Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))),
          hA.semigroup_apply_mem_domain ⟨u₀, hu₀⟩ le_rfl⟩ : (dirichletLaplacian Ω).domain)
        = ⟨u₀, hu₀⟩ := Subtype.ext (by simp [hA.semigroup_zero])
    exact (h1.congr_deriv (congrArg (fun z ↦ -(dirichletLaplacian Ω z)) e)).congr
      (fun t ht ↦ h.apply_eq ht) (h.apply_eq le_rfl)
  · obtain ⟨x, hx0, -⟩ := exists_powDomain_one (A := dirichletLaplacian Ω) ⟨u₀, hu₀⟩
    have := hA.contDiffOnPowDomain_semigroup x (j := 1) le_rfl
    rw [hx0] at this
    exact this.congr fun t ht ↦ (h.apply_eq ht).symm

/-- **`u'(t) → −A u₀` as `t → 0⁺`** for `u₀ ∈ D(A)`: `u'(t) = −S_A(t) (A u₀)` and the semigroup
is continuous at `0`. -/
theorem tendsto_deriv_of_mem_domain (h : IsSolution Ω u₀ u)
    (hu₀ : u₀ ∈ (dirichletLaplacian Ω).domain) :
    Tendsto (deriv u) (𝓝[>] 0) (𝓝 (-(dirichletLaplacian Ω ⟨u₀, hu₀⟩))) := by
  have hA := dirichletLaplacian_isMaximalMonotone (Ω := Ω)
  have h1 := ((hA.continuousOn_semigroup_apply (dirichletLaplacian Ω ⟨u₀, hu₀⟩) 0
    self_mem_Ici).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)).neg
  rw [hA.semigroup_zero, one_apply_eq_self] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [h.deriv_eq ht, ← hA.semigroup_apply_apply ⟨u₀, hu₀⟩ (le_of_lt ht)]
  congr 2
  exact Subtype.ext (h.apply_eq (le_of_lt ht)).symm

/-- **Theorem 10.2 (b), the identity** ([brezis2011functional], lines after (b)): for
`u₀ ∈ D(A)`, `T > 0` and `g t = ⟪A u'(t), u'(t)⟫ = ∫_Ω |∇ Δu(t)|²` on `(0, ∞)`, `g` is
integrable on `(0, T]` and `½ ‖u'(T)‖² + ∫₀ᵀ g = ½ ‖A u₀‖²`, i.e.
`½ ‖Δu(T)‖² + ∫₀ᵀ ‖∇Δu‖² = ½ ‖Δu₀‖²`. The function `φ = ½ ‖u'‖²` has `φ' = ⟪u', u''⟫ = −g`
(`u'' = −A u'`) and `φ(ε) → ½ ‖A u₀‖²` (`tendsto_deriv_of_mem_domain`). -/
theorem energy_domain (h : IsSolution Ω u₀ u) (hu₀ : u₀ ∈ (dirichletLaplacian Ω).domain)
    {g : ℝ → ℝ}
    (hg : ∀ t (ht : 0 < t),
      g t = ⟪dirichletLaplacian Ω ⟨deriv u t, h.deriv_mem_domain ht⟩, deriv u t⟫_ℝ)
    {T : ℝ} (hT : 0 < T) :
    IntegrableOn g (Ioc 0 T) ∧
      1 / 2 * ‖deriv u T‖ ^ 2 + ∫ t in (0 : ℝ)..T, g t
        = 1 / 2 * ‖dirichletLaplacian Ω ⟨u₀, hu₀⟩‖ ^ 2 := by
  have hφ : ∀ t, 0 < t → HasDerivAt (fun t ↦ 1 / 2 * ‖deriv u t‖ ^ 2) (-(g t)) t := by
    intro t ht
    have := (h.hasDerivAt_deriv ht).norm_sq.const_mul (1 / 2)
    convert this using 1
    rw [hg t ht, inner_neg_right, real_inner_comm]
    ring
  have hg0 : ∀ t, 0 < t → 0 ≤ g t := fun t ht ↦ by
    rw [hg t ht]
    exact dirichletLaplacian_inner_self_nonneg _
  have hgc : ContinuousOn g (Ioi 0) := by
    have h1 : ContinuousOn (fun t ↦ ⟪-deriv (deriv u) t, deriv u t⟫_ℝ) (Ioi 0) := by
      have h2 : ContDiffOn ℝ (1 + 1) u (Ioi 0) := h.contDiffOn_top.of_le (by simp)
      have h3 : ContDiffOn ℝ 1 (deriv u) (Ioi 0) :=
        ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).1 h2).2.2
      exact (h3.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).neg.inner
        (h.contDiffOn.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl)
    refine h1.congr fun t ht ↦ ?_
    change g t = ⟪-deriv (deriv u) t, deriv u t⟫_ℝ
    rw [hg t ht, (h.hasDerivAt_deriv ht).deriv, neg_neg]
  have hL : Tendsto (fun t ↦ 1 / 2 * ‖deriv u t‖ ^ 2) (𝓝[>] 0)
      (𝓝 (1 / 2 * ‖dirichletLaplacian Ω ⟨u₀, hu₀⟩‖ ^ 2)) := by
    have := ((h.tendsto_deriv_of_mem_domain hu₀).norm.pow 2).const_mul (1 / 2)
    rwa [norm_neg] at this
  exact integrableOn_Ioc_and_integral_eq_of_hasDerivAt_neg hT hφ hg0 hgc
    (fun t _ ↦ by positivity) hL

/-- **Theorem 10.2 (c), Bochner form** ([brezis2011functional], and Theorem 7.5): if
`u₀ ∈ D(A^k)` (`u₀ = A^0 x` for some `x ∈ D(A^k)`) then `u ∈ C^{k−j}([0, ∞); D(A^j))` for every
`j ≤ k`. Any open `Ω`. -/
theorem contDiffOnPowDomain_Ici_of_powDomain (h : IsSolution Ω u₀ u) {k : ℕ}
    (x : (dirichletLaplacian Ω).PowDomain k) (hx : applyL (dirichletLaplacian Ω) k 0 x = u₀)
    {j : ℕ} (hj : j ≤ k) :
    (dirichletLaplacian Ω).ContDiffOnPowDomain (k - j : ℕ) j u (Ici 0) := by
  have := dirichletLaplacian_isMaximalMonotone.contDiffOnPowDomain_semigroup x hj
  rw [hx] at this
  exact this.congr fun t ht ↦ (h.apply_eq ht).symm

end IsSolution

end Heat

/-! ### The regular-domain clauses: `H^{2ℓ}(Ω)` -/

namespace Heat

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- **`u ∈ C^∞((0, ∞); H^{2ℓ}(Ω))` on a `C^{2ℓ}` domain with bounded boundary**
([brezis2011functional] §10.1, the display after (7)): the `C^∞` lift into `D(A^ℓ)`
(`LinearPMap.contDiffOn_semigroupLift`) composed with the bounded injection
`D(A^ℓ) ↪ H^{2ℓ}(Ω)` of Theorem 9.25 (`dirichletLaplacian.powDomainToSobolevL`). Every finite
order follows by `Bochner.ContDiffOnThrough.of_le`. -/
theorem contDiffOnThrough_sobolev (h : IsSolution Ω u₀ u) {ℓ : ℕ}
    (hΩ : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    Bochner.ContDiffOnThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ) 2 Ω
      volume) ∞ u (Ioi 0) :=
  ⟨fun t ↦ dirichletLaplacian.powDomainToSobolevL hΩ hΓ
      (semigroupLift (dirichletLaplacian Ω) u₀ ℓ t),
    (dirichletLaplacian.powDomainToSobolevL hΩ hΓ).contDiff.comp_contDiffOn
      (contDiffOn_semigroupLift dirichletLaplacian_isMaximalMonotone
        dirichletLaplacian_isFormalAdjoint u₀ ℓ),
    fun t ht ↦ by
      rw [fnL_powDomainToSobolevL, applyL_zero_semigroupLift dirichletLaplacian_isMaximalMonotone
        dirichletLaplacian_isFormalAdjoint ht, h.apply_eq ht.le]⟩

/-- **The clause `u ∈ C((0, ∞); H²(Ω) ∩ H¹₀(Ω))` of (4)** ([brezis2011functional] Theorem 10.1),
on a `C²` domain with bounded boundary: `u` factors continuously through `H²(Ω) → L²(Ω)` on
`(0, ∞)`, and `u(t)` lies in `H¹₀(Ω)` (the range of `SobolevMultiIndexZero.fnL`) for `t > 0`. -/
theorem contDiffOnThrough_two (h : IsSolution Ω u₀ u)
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    Bochner.ContDiffOnThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 2 Ω
      volume) 0 u (Ioi 0) ∧
    ∀ t, 0 < t → u t ∈ Set.range (SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume) := by
  have hΩ' : IsContDiffChartDomain (2 * 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    hΩ.of_le (by norm_num)
  exact ⟨(h.contDiffOnThrough_sobolev hΩ' hΓ).of_le bot_le, fun t ht ↦
    dirichletLaplacian_exists_sobolevZero_lift ⟨u t, h.mem_domain ht⟩⟩

/-- **Theorem 10.2 (c), the `H^{2ℓ}` reading** ([brezis2011functional]): if `u₀ ∈ D(A^k)` then,
on a `C^{2ℓ}` domain with bounded boundary and `ℓ ≤ k`, `u ∈ C^{k−ℓ}([0, ∞); H^{2ℓ}(Ω))`. -/
theorem contDiffOnThrough_sobolev_Ici_of_powDomain (h : IsSolution Ω u₀ u) {k : ℕ}
    (x : (dirichletLaplacian Ω).PowDomain k) (hx : applyL (dirichletLaplacian Ω) k 0 x = u₀)
    {ℓ : ℕ} (hℓ : ℓ ≤ k)
    (hΩ : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    Bochner.ContDiffOnThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ) 2 Ω
      volume) (k - ℓ : ℕ) u (Ici 0) :=
  Bochner.ContDiffOnThrough.of_contDiffOnPowDomain (h.contDiffOnPowDomain_Ici_of_powDomain x hx hℓ)
    (dirichletLaplacian.powDomainToSobolevL hΩ hΓ) _ (fnL_powDomainToSobolevL hΩ hΓ)

/-- **`u ∈ C([0, ∞); H²(Ω))` for `u₀ ∈ D(A)`** ([brezis2011functional] Theorem 10.2 (b)) on a
`C²` domain with bounded boundary. -/
theorem contDiffOnThrough_two_Ici_of_mem_domain (h : IsSolution Ω u₀ u)
    (hu₀ : u₀ ∈ (dirichletLaplacian Ω).domain)
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    Bochner.ContDiffOnThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 2 Ω
      volume) 0 u (Ici 0) := by
  have hΩ' : IsContDiffChartDomain (2 * 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    hΩ.of_le (by norm_num)
  obtain ⟨x, hx0, -⟩ := exists_powDomain_one (A := dirichletLaplacian Ω) ⟨u₀, hu₀⟩
  exact h.contDiffOnThrough_sobolev_Ici_of_powDomain x hx0 le_rfl hΩ' hΓ

end IsSolution

end Heat

/-! ### The Bochner memberships `L²(0, ∞; H¹₀(Ω))`, `L²(0, ∞; H²(Ω))` on bounded domains -/

/-- **Poincaré's inequality on `H¹₀(Ω)`, squared**: for a bounded `Ω` there is `C ≥ 0` with
`‖v‖²_{H¹} ≤ C ∫_Ω |∇v|²` for every `v ∈ H¹₀(Ω)` (Corollary 9.19,
`Elliptic.dirichletForm_restrict_isCoercive`). -/
theorem SobolevEuclideanZero.exists_norm_sq_le_dirichletForm {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : SobolevEuclideanZero (d + 1) 1 2 Ω,
      ‖v‖ ^ 2 ≤ C * Elliptic.dirichletForm Ω (v : SobolevEuclidean (d + 1) 1 2 Ω)
        (v : SobolevEuclidean (d + 1) 1 2 Ω) := by
  obtain ⟨c, hc, hcoer⟩ := Elliptic.dirichletForm_restrict_isCoercive Ω hΩ
  refine ⟨c⁻¹, by positivity, fun v ↦ ?_⟩
  have := hcoer v
  rw [RCLike.re_to_real, SesqForm.restrict_apply] at this
  rw [← div_eq_inv_mul, le_div_iff₀' hc]
  exact this

namespace Heat

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

end IsSolution

variable (Ω) in
/-- **The `H¹₀`-lift of the solution curve**: `t ↦ v(t) ∈ H¹₀(Ω)` with `fnL (v t) = u t` for
`t > 0` (`Heat.IsSolution.fnL_sobolevZeroLift`), the bounded lift `D(A) → H¹₀(Ω)` applied to the
semigroup lift into `D(A)`; `C^∞` on `(0, ∞)`. -/
def sobolevZeroLift (u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (t : ℝ) : SobolevEuclideanZero (d + 1) 1 2 Ω :=
  dirichletLaplacian.sobolevZeroLiftL Ω (semigroupLift (dirichletLaplacian Ω) u₀ 1 t)

/-- The `H¹₀`-lift is `C^∞` on `(0, ∞)`. -/
theorem contDiffOn_sobolevZeroLift
    (u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ContDiffOn ℝ ∞ (sobolevZeroLift Ω u₀) (Ioi 0) :=
  (dirichletLaplacian.sobolevZeroLiftL Ω).contDiff.comp_contDiffOn
    (contDiffOn_semigroupLift dirichletLaplacian_isMaximalMonotone
      dirichletLaplacian_isFormalAdjoint u₀ 1)

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- The function of the `H¹₀`-lift is `u(t)`, for `t > 0`. -/
theorem fnL_sobolevZeroLift (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
      (sobolevZeroLift Ω u₀ t) = u t :=
  (fnL_sobolevZeroLiftL _).trans ((applyL_zero_semigroupLift dirichletLaplacian_isMaximalMonotone
    dirichletLaplacian_isFormalAdjoint ht).trans (h.apply_eq ht.le).symm)

/-- **`‖v(t)‖²_{H¹} ≤ C ⟪A u(t), u(t)⟫`** for the `H¹₀`-lift `v`, with the Poincaré constant
`C` of `SobolevEuclideanZero.exists_norm_sq_le_dirichletForm`. -/
theorem norm_sq_sobolevZeroLift_le (h : IsSolution Ω u₀ u) {C : ℝ}
    (hC : ∀ v : SobolevEuclideanZero (d + 1) 1 2 Ω,
      ‖v‖ ^ 2 ≤ C * dirichletForm Ω (v : SobolevEuclidean (d + 1) 1 2 Ω)
        (v : SobolevEuclidean (d + 1) 1 2 Ω))
    {t : ℝ} (ht : 0 < t) :
    ‖sobolevZeroLift Ω u₀ t‖ ^ 2
      ≤ C * ⟪dirichletLaplacian Ω ⟨u t, h.mem_domain ht⟩, u t⟫_ℝ :=
  (hC _).trans_eq (congrArg (C * ·)
    (h.inner_apply_self_eq_dirichletForm ht (h.fnL_sobolevZeroLift ht)).symm)

/-- **`∫₀^∞ ‖v(t)‖²_{H¹} dt < ∞` on a bounded `Ω`** for the `H¹₀`-lift `v`: Poincaré's
inequality and the energy identity (`integral_inner_apply_le`). -/
theorem integrableOn_norm_sq_sobolevZeroLift
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (h : IsSolution Ω u₀ u) :
    IntegrableOn (fun t ↦ ‖sobolevZeroLift Ω u₀ t‖ ^ 2) (Ioi 0) := by
  obtain ⟨C, hC0, hC⟩ := SobolevEuclideanZero.exists_norm_sq_le_dirichletForm hΩ
  obtain ⟨hgi, -⟩ := h.integral_inner_apply_le (g := fun t ↦ dirichletForm Ω
    (sobolevZeroLift Ω u₀ t : SobolevEuclidean (d + 1) 1 2 Ω)
    (sobolevZeroLift Ω u₀ t : SobolevEuclidean (d + 1) 1 2 Ω))
    fun t ht ↦ (h.inner_apply_self_eq_dirichletForm ht (h.fnL_sobolevZeroLift ht)).symm
  refine (hgi.const_mul C).mono' (((contDiffOn_sobolevZeroLift u₀).continuousOn.norm.pow 2
    |>.aestronglyMeasurable measurableSet_Ioi)) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t _ ↦ ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact hC _

/-- **`u ∈ L²(0, ∞; H¹₀(Ω))` for bounded `Ω`** ([brezis2011functional] Theorem 10.1, the clause
"`u ∈ L²(0, ∞; H¹₀(Ω))`", which on an unbounded domain only holds in its gradient form
`Heat.IsSolution.integral_inner_apply_le`): `u` factors through `H¹₀(Ω) → L²(Ω)` on `(0, ∞)` by a
curve of `L²((0, ∞); H¹₀(Ω))`, the `H¹₀`-lift. -/
theorem memLpThrough_sobolevZero_of_isBounded
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (h : IsSolution Ω u₀ u) :
    Bochner.MemLpThrough (SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume) 2 u (Ioi 0) := by
  have hint := h.integrableOn_norm_sq_sobolevZeroLift hΩ
  have hint2 : IntegrableOn (fun t ↦ ‖sobolevZeroLift Ω u₀ t‖ ^ (2 : ℝ≥0∞).toReal) (Ioi 0) := by
    refine hint.congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
    rw [ENNReal.toReal_ofNat, Real.rpow_two]
  exact Bochner.MemLpThrough.of_contDiffOnThrough_of_integrable
    (contDiffOn_sobolevZeroLift u₀).continuousOn (fun t ht ↦ (h.fnL_sobolevZeroLift ht).symm)
    measurableSet_Ioi two_ne_zero ENNReal.ofNat_ne_top hint2

/-- `∫₀^∞ ‖u(t)‖² dt < ∞` on a bounded `Ω`: `‖u(t)‖ ≤ ‖v(t)‖_{H¹}` for the `H¹₀`-lift. -/
theorem integrableOn_norm_sq_of_isBounded
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (h : IsSolution Ω u₀ u) :
    IntegrableOn (fun t ↦ ‖u t‖ ^ 2) (Ioi 0) := by
  refine (h.integrableOn_norm_sq_sobolevZeroLift hΩ).mono'
    ((h.contDiffOn.continuousOn.norm.pow 2).aestronglyMeasurable measurableSet_Ioi) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_
  rw [Real.norm_of_nonneg (by positivity), ← h.fnL_sobolevZeroLift ht]
  exact pow_le_pow_left₀ (norm_nonneg _) (SobolevMultiIndexZero.norm_fnL_apply_le _) 2

/-- `∫₀^∞ ‖u'(t)‖² dt < ∞` for `u₀ ∈ H¹₀(Ω)`, as an `IntegrableOn` (the form of (11) that the
Bochner memberships consume). -/
theorem integrableOn_norm_sq_deriv (h : IsSolution Ω u₀ u) {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) :
    IntegrableOn (fun t ↦ ‖deriv u t‖ ^ 2) (Ioi 0) :=
  (memLp_two_iff_integrable_sq_norm ((h.contDiffOn.continuousOn_deriv_of_isOpen isOpen_Ioi
    le_rfl).aestronglyMeasurable measurableSet_Ioi)).1 (h.memLp_deriv hv₀).1

/-- `deriv u t = −A x_t` on the lift `x_t ∈ D(A)` of `u(t)`, `t > 0`. -/
theorem deriv_eq_neg_applyL_semigroupLift_one (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    deriv u t = -applyL (dirichletLaplacian Ω) 1 1
      (semigroupLift (dirichletLaplacian Ω) u₀ 1 t) := by
  have := h.iteratedDeriv_eq_applyL_semigroupLift 1 1 le_rfl t ht
  rwa [iteratedDeriv_one, pow_one, neg_one_smul] at this

/-- **The graph norm of the semigroup lift**: `‖x_t‖²_{D(A)} = ‖u(t)‖² + ‖u'(t)‖²` for the lift
`x_t ∈ D(A)` of `u(t)`, `t > 0`. -/
theorem norm_sq_semigroupLift_one (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    ‖semigroupLift (dirichletLaplacian Ω) u₀ 1 t‖ ^ 2 = ‖u t‖ ^ 2 + ‖deriv u t‖ ^ 2 := by
  have h1 : applyL (dirichletLaplacian Ω) 1 0 (semigroupLift (dirichletLaplacian Ω) u₀ 1 t) = u t :=
    (applyL_zero_semigroupLift dirichletLaplacian_isMaximalMonotone
      dirichletLaplacian_isFormalAdjoint ht).trans (h.apply_eq ht.le).symm
  have h2 : applyL (dirichletLaplacian Ω) 1 1 (semigroupLift (dirichletLaplacian Ω) u₀ 1 t)
      = -deriv u t := neg_eq_iff_eq_neg.1 (h.deriv_eq_neg_applyL_semigroupLift_one ht).symm
  rw [PowDomain.norm_sq_eq, Fin.sum_univ_two, h1, h2, norm_neg]

end IsSolution

variable (Ω) in
/-- **The `H²`-lift of the solution curve** on a `C²` domain with bounded boundary:
`dirichletLaplacian.powDomainToSobolevL` applied to the semigroup lift into `D(A)`, so that
`fnL (w t) = u t` for `t > 0` (`Heat.IsSolution.fnL_sobolevTwoLift`). -/
def sobolevTwoLift
    (hΩ : IsContDiffChartDomain (2 * 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) (t : ℝ) :
    SobolevEuclidean (d + 1) (2 * 1) 2 Ω :=
  dirichletLaplacian.powDomainToSobolevL hΩ hΓ (semigroupLift (dirichletLaplacian Ω) u₀ 1 t)

/-- The `H²`-lift is `C^∞` on `(0, ∞)`. -/
theorem contDiffOn_sobolevTwoLift
    (hΩ : IsContDiffChartDomain (2 * 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ContDiffOn ℝ ∞ (sobolevTwoLift Ω hΩ hΓ u₀) (Ioi 0) :=
  (dirichletLaplacian.powDomainToSobolevL hΩ hΓ).contDiff.comp_contDiffOn
    (contDiffOn_semigroupLift dirichletLaplacian_isMaximalMonotone
      dirichletLaplacian_isFormalAdjoint u₀ 1)

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- The function of the `H²`-lift is `u(t)`, for `t > 0`. -/
theorem fnL_sobolevTwoLift
    (hΩ : IsContDiffChartDomain (2 * 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * 1) 2 Ω volume
      (sobolevTwoLift Ω hΩ hΓ u₀ t) = u t :=
  (fnL_powDomainToSobolevL hΩ hΓ _).trans
    ((applyL_zero_semigroupLift dirichletLaplacian_isMaximalMonotone
      dirichletLaplacian_isFormalAdjoint ht).trans (h.apply_eq ht.le).symm)

/-- **`‖w(t)‖²_{H²} ≤ C (‖u(t)‖² + ‖u'(t)‖²)`** for the `H²`-lift `w`, with
`C = ‖powDomainToSobolevL‖²`. -/
theorem norm_sq_sobolevTwoLift_le
    (hΩ : IsContDiffChartDomain (2 * 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    ‖sobolevTwoLift Ω hΩ hΓ u₀ t‖ ^ 2
      ≤ ‖dirichletLaplacian.powDomainToSobolevL hΩ hΓ‖ ^ 2 * (‖u t‖ ^ 2 + ‖deriv u t‖ ^ 2) := by
  have h1 := (dirichletLaplacian.powDomainToSobolevL hΩ hΓ).le_opNorm
    (semigroupLift (dirichletLaplacian Ω) u₀ 1 t)
  calc ‖sobolevTwoLift Ω hΩ hΓ u₀ t‖ ^ 2
      ≤ (‖dirichletLaplacian.powDomainToSobolevL hΩ hΓ‖
        * ‖semigroupLift (dirichletLaplacian Ω) u₀ 1 t‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = ‖dirichletLaplacian.powDomainToSobolevL hΩ hΓ‖ ^ 2 * (‖u t‖ ^ 2 + ‖deriv u t‖ ^ 2) := by
        rw [mul_pow, h.norm_sq_semigroupLift_one ht]

/-- **`u ∈ L²(0, ∞; H²(Ω))` for `u₀ ∈ H¹₀(Ω)` on a bounded `C²` domain** ([brezis2011functional]
Theorem 10.2 (a)): the `H²`-lift satisfies `‖w(t)‖²_{H²} ≤ C (‖u(t)‖² + ‖u'(t)‖²)`, both
integrable on `(0, ∞)` (Poincaré and (11)). On an unbounded domain only
`∫₀^∞ ‖Δu(t)‖² dt < ∞` holds. -/
theorem memLpThrough_two_of_isBounded
    (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : IsSolution Ω u₀ u) {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) :
    Bochner.MemLpThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 2 Ω volume) 2
      u (Ioi 0) := by
  have hΩ2 : IsContDiffChartDomain (2 * 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    hΩ.of_le (by norm_num)
  have hint : IntegrableOn (fun t ↦ ‖sobolevTwoLift Ω hΩ2 hΓ u₀ t‖ ^ 2) (Ioi 0) := by
    refine (((h.integrableOn_norm_sq_of_isBounded hΩb).add (h.integrableOn_norm_sq_deriv hv₀))
      |>.const_mul (‖dirichletLaplacian.powDomainToSobolevL hΩ2 hΓ‖ ^ 2)).mono'
      (((contDiffOn_sobolevTwoLift hΩ2 hΓ u₀).continuousOn.norm.pow 2).aestronglyMeasurable
        measurableSet_Ioi) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_
    rw [Real.norm_of_nonneg (by positivity)]
    exact h.norm_sq_sobolevTwoLift_le hΩ2 hΓ ht
  have hint2 : IntegrableOn (fun t ↦ ‖sobolevTwoLift Ω hΩ2 hΓ u₀ t‖ ^ (2 : ℝ≥0∞).toReal)
      (Ioi 0) := by
    refine hint.congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
    rw [ENNReal.toReal_ofNat, Real.rpow_two]
  exact Bochner.MemLpThrough.of_contDiffOnThrough_of_integrable
    (contDiffOn_sobolevTwoLift hΩ2 hΓ u₀).continuousOn
    (fun t ht ↦ (h.fnL_sobolevTwoLift hΩ2 hΓ ht).symm) measurableSet_Ioi two_ne_zero
    ENNReal.ofNat_ne_top hint2

end IsSolution

end Heat

/-! ### Remark 1: the well-posed backward problem -/

namespace Heat

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

variable (Ω) in
/-- **A solution of the backward-in-time problem (9'), (10), (11)** of [brezis2011functional]
Chapter 10, Remark 1: `−∂ₜu − Δu = 0` on `Ω × (−∞, T)`, `u = 0` on `Γ × (−∞, T)`, with the final
datum `u(T) = u_T`, in the class `C((−∞, T]; L²) ∩ C¹((−∞, T); L²)` with `u(t) ∈ D(A)` for
`t < T`. The equation reads `u' = A u` (`A = −Δ`). -/
structure IsBackwardSolution (T : ℝ)
    (uT : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) : Prop where
  /-- The final condition `u(T) = u_T`. -/
  apply_eq : u T = uT
  /-- `u(t) ∈ D(A)` for `t < T`. -/
  mem_domain : ∀ t, t < T → u t ∈ (dirichletLaplacian Ω).domain
  /-- The equation `u' = A u = −Δu` for `t < T`. -/
  hasDerivAt : ∀ t (ht : t < T), HasDerivAt u (dirichletLaplacian Ω ⟨u t, mem_domain t ht⟩) t
  /-- `u ∈ C((−∞, T]; L²(Ω))`. -/
  continuousOn : ContinuousOn u (Iic T)
  /-- `u ∈ C¹((−∞, T); L²(Ω))`. -/
  contDiffOn : ContDiffOn ℝ 1 u (Iio T)

variable {T : ℝ} {uT : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- **The change of variables `t ↦ T − t`**: `u` solves the backward problem with final datum
`u_T` iff `s ↦ u(T − s)` solves the heat equation with initial datum `u_T`. -/
theorem isBackwardSolution_iff :
    IsBackwardSolution Ω T uT u ↔ IsSolution Ω uT fun s ↦ u (T - s) := by
  constructor
  · intro h
    refine ⟨⟨by simpa using h.apply_eq, fun s hs ↦ h.mem_domain _ (sub_lt_self T hs),
      fun s hs ↦ ?_⟩, ?_, ?_⟩
    · exact ((h.hasDerivAt (T - s) (sub_lt_self T hs)).comp_const_sub T s).hasDerivWithinAt
    · exact h.continuousOn.comp (continuousOn_const.sub continuousOn_id)
        fun s (hs : 0 ≤ s) ↦ show T - s ∈ Iic T from sub_le_self T hs
    · exact h.contDiffOn.comp (contDiffOn_const.sub contDiffOn_id)
        fun s (hs : 0 < s) ↦ show T - s ∈ Iio T from sub_lt_self T hs
  · intro h
    have hmem : ∀ t, t < T → u t ∈ (dirichletLaplacian Ω).domain := fun t ht ↦ by
      have := h.mem_domain (sub_pos.2 ht)
      rwa [sub_sub_cancel] at this
    refine ⟨by simpa using h.apply_zero, hmem, fun t ht ↦ ?_, ?_, ?_⟩
    · have h1 := (h.hasDerivAt (sub_pos.2 ht)).comp_const_sub T t
      have e2 : (⟨(fun s ↦ u (T - s)) (T - t), h.mem_domain (sub_pos.2 ht)⟩ :
          (dirichletLaplacian Ω).domain) = ⟨u t, hmem t ht⟩ :=
        Subtype.ext (by simp only [sub_sub_cancel])
      refine (h1.congr_of_eventuallyEq (Eventually.of_forall fun x ↦ ?_)).congr_deriv ?_
      · change u x = u (T - (T - x))
        rw [sub_sub_cancel]
      · rw [neg_neg]
        exact congrArg (fun z ↦ dirichletLaplacian Ω z) e2
    · have := h.continuousOn.comp (continuousOn_const.sub continuousOn_id)
        (fun t (ht : t ≤ T) ↦ show T - t ∈ Ici (0 : ℝ) from sub_nonneg.2 ht)
      refine this.congr fun t _ ↦ ?_
      change u t = u (T - (T - t))
      rw [sub_sub_cancel]
    · have := h.contDiffOn.comp (contDiffOn_const.sub contDiffOn_id)
        (fun t (ht : t < T) ↦ show T - t ∈ Ioi (0 : ℝ) from sub_pos.2 ht)
      refine this.congr fun t _ ↦ ?_
      change u t = u (T - (T - t))
      rw [sub_sub_cancel]

/-- **Remark 1, the well-posed half** ([brezis2011functional] Chapter 10, Remark 1): for every
`T` and `u_T ∈ L²(Ω)` the backward problem `−∂ₜu − Δu = 0` on `Ω × (−∞, T)`, `u = 0` on
`Γ × (−∞, T)`, `u(T) = u_T` has exactly one solution on `(−∞, T]`, namely
`t ↦ solution Ω u_T (T − t)` ("change `t` into `T − t` and apply Theorem 10.1"). The ill-posed
problem (9), (10), (11) is not a theorem of the book; its necessary condition (12) is
`Heat.IsSolution.exists_powDomain`. -/
theorem existsUnique_isSolution_backward (T : ℝ)
    (uT : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ∃ u, IsBackwardSolution Ω T uT u ∧ ∀ v, IsBackwardSolution Ω T uT v → EqOn v u (Iic T) := by
  refine ⟨fun t ↦ solution Ω uT (T - t), isBackwardSolution_iff.2 ?_, fun v hv t ht ↦ ?_⟩
  · have e : (fun s ↦ solution Ω uT (T - (T - s))) = solution Ω uT :=
      funext fun s ↦ by rw [sub_sub_cancel]
    rw [e]
    exact isSolution_solution uT
  · have := (isBackwardSolution_iff.1 hv).eqOn_solution
      (show T - t ∈ Ici (0 : ℝ) from mem_Ici.2 (sub_nonneg.2 (mem_Iic.1 ht)))
    simpa only [sub_sub_cancel] using this

end Heat

/-! ### Remark 3: the eigenfunction expansion -/

section Eigen

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
  (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)

/-- **The Dirichlet eigenfunctions lie in `D(A)` with `A e_n = λ_n e_n`**: the weak eigenvalue
equation (83) of Theorem 9.31 is the defining identity of the weak domain
(`dirichletLaplacianDomain`) with the datum `λ_n e_n`. -/
theorem dirichletLaplacian_apply_dirichletEigenbasis (n : ℕ) :
    ∃ h : dirichletEigenbasis Ω hΩ hne n ∈ (dirichletLaplacian Ω).domain,
      dirichletLaplacian Ω ⟨dirichletEigenbasis Ω hΩ hne n, h⟩
        = dirichletEigenvalue Ω hΩ n • dirichletEigenbasis Ω hΩ hne n := by
  have hv : (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω)
      ∈ SobolevEuclideanZero (d + 1) 1 2 Ω := (dirichletEigenfunction Ω hΩ hne n).2
  have hvf : fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
      (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω)
      = dirichletEigenbasis Ω hΩ hne n := fnL_dirichletEigenfunction Ω hΩ hne n
  have hg : ∀ φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
      dirichletForm Ω (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω) φ
        = load Ω (dirichletEigenvalue Ω hΩ n • dirichletEigenbasis Ω hΩ hne n) φ := fun φ hφ ↦ by
    have h1 := dirichletForm_dirichletEigenfunction Ω hΩ hne n ⟨φ, hφ⟩
    have h2 : load Ω (dirichletEigenvalue Ω hΩ n • dirichletEigenbasis Ω hΩ hne n) φ
        = dirichletEigenvalue Ω hΩ n * ⟪dirichletEigenbasis Ω hΩ hne n,
          fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume φ⟫_ℝ := by
      rw [load_apply_inner, real_inner_smul_left]
      rfl
    exact h1.trans h2.symm
  exact ⟨⟨_, hv, hvf, _, hg⟩, dirichletLaplacian_apply_unique _ hv hvf hg⟩

namespace Heat.IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- The coefficient `a_n(t) = ⟪u(t), e_n⟫` satisfies `a_n' = −λ_n a_n` on `(0, ∞)`:
`⟪u', e_n⟫ = −⟪A u, e_n⟫ = −⟪u, A e_n⟫ = −λ_n ⟪u, e_n⟫`. -/
theorem hasDerivAt_inner_eigenfunction (h : IsSolution Ω u₀ u) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t ↦ ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ)
      (-dirichletEigenvalue Ω hΩ n * ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ) t := by
  obtain ⟨hmem, hAe⟩ := dirichletLaplacian_apply_dirichletEigenbasis hΩ hne n
  have h1 := (h.hasDerivAt ht).inner ℝ (hasDerivAt_const t (dirichletEigenbasis Ω hΩ hne n))
  refine h1.congr_deriv ?_
  rw [inner_zero_right, zero_add, inner_neg_left,
    dirichletLaplacian_isFormalAdjoint ⟨u t, h.mem_domain ht⟩ ⟨_, hmem⟩, hAe,
    inner_smul_right, neg_mul]

/-- **Remark 3, the coefficients (13)** ([brezis2011functional] Chapter 10, Remark 3): for
bounded nonempty `Ω`, the coefficients `a_n(t) = ⟪u(t), e_n⟫` of the solution in the Dirichlet
eigenbasis are `a_n(t) = e^{−λ_n t} ⟪u₀, e_n⟫` for `t ≥ 0`: `e^{λ_n t} a_n(t)` has zero
derivative on `(0, ∞)` and is continuous on `[0, ∞)`. -/
theorem inner_eigenfunction (h : IsSolution Ω u₀ u) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ
      = Real.exp (-dirichletEigenvalue Ω hΩ n * t) * ⟪u₀, dirichletEigenbasis Ω hΩ hne n⟫_ℝ := by
  set lam := dirichletEigenvalue Ω hΩ n with hlam
  set F : ℝ → ℝ := fun t ↦ Real.exp (lam * t) * ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ with hF
  have hFd : ∀ t, 0 < t → HasDerivAt F 0 t := fun t ht ↦ by
    have h1 : HasDerivAt (fun t ↦ Real.exp (lam * t)) (Real.exp (lam * t) * lam) t := by
      simpa using ((hasDerivAt_id t).const_mul lam).exp
    have := h1.mul (h.hasDerivAt_inner_eigenfunction hΩ hne n ht)
    convert this using 1
    ring
  have hFc : ContinuousOn F (Ici 0) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      (h.continuousOn.inner continuousOn_const)
  have hFdiff : DifferentiableOn ℝ F (interior (Ici 0)) := by
    rw [interior_Ici]
    exact fun t ht ↦ (hFd t ht).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn F (Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0) hFc hFdiff fun t ht ↦ by
      rw [interior_Ici] at ht
      rw [(hFd t ht).deriv]
  have hanti : AntitoneOn F (Ici 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0) hFc hFdiff fun t ht ↦ by
      rw [interior_Ici] at ht
      rw [(hFd t ht).deriv]
  have hconst : F t = F 0 := le_antisymm (hanti self_mem_Ici ht ht) (hmono self_mem_Ici ht ht)
  have hF0 : F 0 = ⟪u₀, dirichletEigenbasis Ω hΩ hne n⟫_ℝ := by
    simp [hF, h.apply_zero]
  have hFt : F t = Real.exp (lam * t) * ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ := rfl
  rw [hF0] at hconst
  rw [← hconst, hFt, neg_mul, Real.exp_neg, ← mul_assoc, inv_mul_cancel₀ (Real.exp_pos _).ne',
    one_mul]

/-- **Remark 3, the series (14)** ([brezis2011functional] Chapter 10, Remark 3): for bounded
nonempty `Ω` and `t ≥ 0`, `u(t) = ∑ₙ e^{−λ_n t} ⟪u₀, e_n⟫ e_n` in `L²(Ω)` — the expansion of
`u(t)` in the Hilbert basis with the coefficients of `inner_eigenfunction`. -/
theorem hasSum_eigenfunction (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun n ↦ (Real.exp (-dirichletEigenvalue Ω hΩ n * t)
      * ⟪u₀, dirichletEigenbasis Ω hΩ hne n⟫_ℝ) • dirichletEigenbasis Ω hΩ hne n) (u t) := by
  have := (dirichletEigenbasis Ω hΩ hne).hasSum_repr (u t)
  refine this.congr_fun fun n ↦ ?_
  rw [HilbertBasis.repr_apply_apply, real_inner_comm (u t) (dirichletEigenbasis Ω hΩ hne n),
    h.inner_eigenfunction hΩ hne n ht]

end Heat.IsSolution

end Eigen

/-! ### Theorem 10.2 (b): `u ∈ L²(0, ∞; H³(Ω))` and `∂ₜu ∈ L²(0, ∞; H¹₀(Ω))` -/

section SobolevThree

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

namespace Heat

variable (Ω) in
/-- **The `H¹₀`-lift of `u'`**: `t ↦ −A₁^1 x_t ∈ H¹₀(Ω)` on the `A₁`-semigroup lift
`x_t ∈ D(A₁)` of the datum `v₀ ∈ H¹₀(Ω)`; its function is `u'(t)` for `t > 0`
(`Heat.IsSolution.fnL_sobolevZeroLiftDeriv`). -/
def sobolevZeroLiftDeriv (v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω) (t : ℝ) :
    SobolevEuclideanZero (d + 1) 1 2 Ω :=
  -applyL (dirichletLaplacianH10 Ω) 1 1 (semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t)

/-- The `H¹₀`-lift of `u'` is `C^∞` on `(0, ∞)`. -/
theorem contDiffOn_sobolevZeroLiftDeriv (v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω) :
    ContDiffOn ℝ ∞ (sobolevZeroLiftDeriv Ω v₀) (Ioi 0) :=
  ((applyL (dirichletLaplacianH10 Ω) 1 1).contDiff.comp_contDiffOn
    (contDiffOn_semigroupLift dirichletLaplacianH10_isMaximalMonotone
      dirichletLaplacianH10_isFormalAdjoint v₀ 1)).neg

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- The function of the `H¹₀`-lift of `u'` is `u'(t)`, for `t > 0`. -/
theorem fnL_sobolevZeroLiftDeriv (h : IsSolution Ω u₀ u) {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) {t : ℝ} (ht : 0 < t) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
      (sobolevZeroLiftDeriv Ω v₀ t) = deriv u t :=
  (_root_.map_neg _ _).trans ((congrArg Neg.neg (h.fnL_applyL_one_semigroupLift_H10 hv₀ ht)).trans
    (neg_neg _))

/-- `∫_Ω |∇z(t)|² = ⟪A u'(t), u'(t)⟫` for the `H¹₀`-lift `z` of `u'`, `t > 0`. -/
theorem dirichletForm_sobolevZeroLiftDeriv (h : IsSolution Ω u₀ u)
    {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) {t : ℝ} (ht : 0 < t) :
    dirichletForm Ω (sobolevZeroLiftDeriv Ω v₀ t : SobolevEuclidean (d + 1) 1 2 Ω)
        (sobolevZeroLiftDeriv Ω v₀ t : SobolevEuclidean (d + 1) 1 2 Ω)
      = ⟪dirichletLaplacian Ω ⟨deriv u t, h.deriv_mem_domain ht⟩, deriv u t⟫_ℝ :=
  (dirichletLaplacian_inner_self_eq_dirichletForm ⟨deriv u t, h.deriv_mem_domain ht⟩
    (sobolevZeroLiftDeriv Ω v₀ t).2 (h.fnL_sobolevZeroLiftDeriv hv₀ ht)).symm

/-- **`∫₀^∞ ‖z(t)‖²_{H¹} dt < ∞`** for the `H¹₀`-lift `z` of `u'`, on a bounded `Ω` with
`u₀ ∈ D(A)`: Poincaré's inequality and the identity of Theorem 10.2 (b). -/
theorem integrableOn_norm_sq_sobolevZeroLiftDeriv
    (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (h : IsSolution Ω u₀ u) (hu₀ : u₀ ∈ (dirichletLaplacian Ω).domain)
    {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) :
    IntegrableOn (fun t ↦ ‖sobolevZeroLiftDeriv Ω v₀ t‖ ^ 2) (Ioi 0) := by
  obtain ⟨C, hC0, hC⟩ := SobolevEuclideanZero.exists_norm_sq_le_dirichletForm hΩb
  obtain ⟨hgi, -⟩ := integrableOn_Ioi_and_integral_le_of_forall_integral_le
    (g := fun t ↦ dirichletForm Ω (sobolevZeroLiftDeriv Ω v₀ t : SobolevEuclidean (d + 1) 1 2 Ω)
      (sobolevZeroLiftDeriv Ω v₀ t : SobolevEuclidean (d + 1) 1 2 Ω))
    (L := 1 / 2 * ‖dirichletLaplacian Ω ⟨u₀, hu₀⟩‖ ^ 2)
    (fun t _ ↦ dirichletForm_self_nonneg Ω _)
    (fun T hT ↦ (h.energy_domain hu₀ (fun t ht ↦ h.dirichletForm_sobolevZeroLiftDeriv hv₀ ht)
      hT).1) fun T hT ↦ by
      have := (h.energy_domain hu₀ (fun t ht ↦ h.dirichletForm_sobolevZeroLiftDeriv hv₀ ht) hT).2
      nlinarith [norm_nonneg (deriv u T)]
  refine (hgi.const_mul C).mono' (((contDiffOn_sobolevZeroLiftDeriv v₀).continuousOn.norm.pow 2
    |>.aestronglyMeasurable measurableSet_Ioi)) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t _ ↦ ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact hC _

/-- **`∂ₜu ∈ L²(0, ∞; H¹₀(Ω))`** for `u₀ ∈ D(A)` on a bounded `Ω` ([brezis2011functional]
Theorem 10.2 (b)): `u'` factors through `H¹₀(Ω) → L²(Ω)` on `(0, ∞)` by a curve of
`L²((0, ∞); H¹₀(Ω))`, the `H¹₀`-lift of `u'`. -/
theorem memLpThrough_sobolevZero_deriv_of_isBounded
    (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (h : IsSolution Ω u₀ u) (hu₀ : u₀ ∈ (dirichletLaplacian Ω).domain) :
    Bochner.MemLpThrough (SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume) 2 (deriv u) (Ioi 0) := by
  obtain ⟨v₀, hv₀⟩ := dirichletLaplacian_exists_sobolevZero_lift ⟨u₀, hu₀⟩
  have hint := h.integrableOn_norm_sq_sobolevZeroLiftDeriv hΩb hu₀ hv₀
  have hint2 : IntegrableOn (fun t ↦ ‖sobolevZeroLiftDeriv Ω v₀ t‖ ^ (2 : ℝ≥0∞).toReal)
      (Ioi 0) := by
    refine hint.congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
    rw [ENNReal.toReal_ofNat, Real.rpow_two]
  exact Bochner.MemLpThrough.of_contDiffOnThrough_of_integrable
    (contDiffOn_sobolevZeroLiftDeriv v₀).continuousOn
    (fun t ht ↦ (h.fnL_sobolevZeroLiftDeriv hv₀ ht).symm) measurableSet_Ioi two_ne_zero
    ENNReal.ofNat_ne_top hint2

/-- The `0`-th coordinate of the `A₁`-semigroup lift is the `H¹₀`-lift of `u`, for `t > 0`. -/
theorem applyL_zero_semigroupLift_H10_eq (h : IsSolution Ω u₀ u)
    {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) {t : ℝ} (ht : 0 < t) :
    applyL (dirichletLaplacianH10 Ω) 1 0 (semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t)
      = sobolevZeroLift Ω u₀ t :=
  SobolevMultiIndexZero.fnL_injective
    ((h.fnL_applyL_zero_semigroupLift_H10 hv₀ ht).trans (h.fnL_sobolevZeroLift ht).symm)

/-- `‖z(t)‖ = ‖A₁^1 x_t‖` for the `H¹₀`-lift `z` of `u'`. -/
theorem _root_.Heat.norm_sobolevZeroLiftDeriv (v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω) (t : ℝ) :
    ‖sobolevZeroLiftDeriv Ω v₀ t‖
      = ‖applyL (dirichletLaplacianH10 Ω) 1 1 (semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t)‖ :=
  norm_neg _

/-- **The graph norm of the `A₁`-semigroup lift**: `‖x_t‖²_{D(A₁)} = ‖v(t)‖²_{H¹} + ‖z(t)‖²_{H¹}`
for the `H¹₀`-lifts `v` of `u` and `z` of `u'`, `t > 0`. -/
theorem norm_sq_semigroupLift_H10_one (h : IsSolution Ω u₀ u)
    {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) {t : ℝ} (ht : 0 < t) :
    ‖semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t‖ ^ 2
      = ‖sobolevZeroLift Ω u₀ t‖ ^ 2 + ‖sobolevZeroLiftDeriv Ω v₀ t‖ ^ 2 :=
  (norm_sq_powDomain_one _).trans (congrArg₂ (· + ·)
    (congrArg (‖·‖ ^ 2) (h.applyL_zero_semigroupLift_H10_eq hv₀ ht))
    (congrArg (· ^ 2) (Heat.norm_sobolevZeroLiftDeriv v₀ t).symm))

end IsSolution

variable (Ω) in
/-- **The `H³`-lift of the solution curve** on a `C³` domain with bounded boundary, for a datum
`u₀ = fnL v₀ ∈ D(A)`: the injection `D(A₁) ↪ H³(Ω)` applied to the `A₁`-semigroup lift. -/
def sobolevThreeLift (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω) (t : ℝ) : SobolevEuclidean (d + 1) 3 2 Ω :=
  dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ
    (semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t)

/-- The `H³`-lift is `C^∞` on `(0, ∞)`. -/
theorem contDiffOn_sobolevThreeLift
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω) :
    ContDiffOn ℝ ∞ (sobolevThreeLift Ω hΩ hΓ v₀) (Ioi 0) :=
  (dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ).contDiff.comp_contDiffOn
    (contDiffOn_semigroupLift dirichletLaplacianH10_isMaximalMonotone
      dirichletLaplacianH10_isFormalAdjoint v₀ 1)

/-- `‖U(t)‖_{H³} ≤ ‖T‖ ‖x_t‖_{D(A₁)}` for the `H³`-lift `U`. -/
theorem norm_sobolevThreeLift_le
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω) (t : ℝ) :
    ‖sobolevThreeLift Ω hΩ hΓ v₀ t‖
      ≤ ‖dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ‖
        * ‖semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t‖ :=
  (dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ).le_opNorm _

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- The function of the `H³`-lift is `u(t)`, for `t > 0`. -/
theorem fnL_sobolevThreeLift
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : IsSolution Ω u₀ u) {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) {t : ℝ} (ht : 0 < t) :
    fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 3 2 Ω volume
      (sobolevThreeLift Ω hΩ hΓ v₀ t) = u t :=
  (fnL_powDomainOneToSobolevThreeL hΩ hΓ _).trans (h.fnL_applyL_zero_semigroupLift_H10 hv₀ ht)

/-- **`‖U(t)‖²_{H³} ≤ ‖T‖² (‖v(t)‖²_{H¹} + ‖z(t)‖²_{H¹})`** for the `H³`-lift `U` and the
`H¹₀`-lifts `v`, `z` of `u`, `u'`. -/
theorem norm_sq_sobolevThreeLift_le
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : IsSolution Ω u₀ u) {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) {t : ℝ} (ht : 0 < t) :
    ‖sobolevThreeLift Ω hΩ hΓ v₀ t‖ ^ 2
      ≤ ‖dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ‖ ^ 2
        * (‖sobolevZeroLift Ω u₀ t‖ ^ 2 + ‖sobolevZeroLiftDeriv Ω v₀ t‖ ^ 2) := by
  have h1 := norm_sobolevThreeLift_le hΩ hΓ v₀ t
  have h2 := h.norm_sq_semigroupLift_H10_one hv₀ ht
  calc ‖sobolevThreeLift Ω hΩ hΓ v₀ t‖ ^ 2
      ≤ (‖dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ‖
        * ‖semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = ‖dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ‖ ^ 2
        * ‖semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t‖ ^ 2 := mul_pow _ _ 2
    _ = ‖dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ‖ ^ 2
        * (‖sobolevZeroLift Ω u₀ t‖ ^ 2 + ‖sobolevZeroLiftDeriv Ω v₀ t‖ ^ 2) :=
        congrArg (‖dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ‖ ^ 2 * ·) h2

/-- The bound of `norm_sq_sobolevThreeLift_le` in the form the integrability comparison uses. -/
theorem norm_norm_sq_sobolevThreeLift_le
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : IsSolution Ω u₀ u) {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) {t : ℝ} (ht : 0 < t) :
    ‖‖sobolevThreeLift Ω hΩ hΓ v₀ t‖ ^ 2‖
      ≤ ‖dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ‖ ^ 2
        * (‖sobolevZeroLift Ω u₀ t‖ ^ 2 + ‖sobolevZeroLiftDeriv Ω v₀ t‖ ^ 2) :=
  (Real.norm_of_nonneg (sq_nonneg _)).le.trans (h.norm_sq_sobolevThreeLift_le hΩ hΓ hv₀ ht)

/-- **`∫₀^∞ ‖U(t)‖²_{H³} dt < ∞`** for the `H³`-lift `U` on a bounded `C³` domain with
`u₀ ∈ D(A)`. -/
theorem integrableOn_norm_sq_sobolevThreeLift
    (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : IsSolution Ω u₀ u) (hu₀ : u₀ ∈ (dirichletLaplacian Ω).domain)
    {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) :
    IntegrableOn (fun t ↦ ‖sobolevThreeLift Ω hΩ hΓ v₀ t‖ ^ 2) (Ioi 0) := by
  have hint0 : IntegrableOn (fun t ↦ ‖dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ‖ ^ 2
      * (‖sobolevZeroLift Ω u₀ t‖ ^ 2 + ‖sobolevZeroLiftDeriv Ω v₀ t‖ ^ 2)) (Ioi 0) :=
    ((h.integrableOn_norm_sq_sobolevZeroLift hΩb).add
      (h.integrableOn_norm_sq_sobolevZeroLiftDeriv hΩb hu₀ hv₀)).const_mul _
  exact hint0.mono' (((contDiffOn_sobolevThreeLift hΩ hΓ v₀).continuousOn.norm.pow 2
    |>.aestronglyMeasurable measurableSet_Ioi))
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦
      h.norm_norm_sq_sobolevThreeLift_le hΩ hΓ hv₀ ht)

/-- **`u ∈ L²(0, ∞; H³(Ω))` for `u₀ ∈ D(A)` on a bounded `C³` domain** ([brezis2011functional]
Theorem 10.2 (b), the "why?"): the `H³`-lift `U` of the solution satisfies
`‖U(t)‖²_{H³} ≤ ‖T‖² (‖v(t)‖²_{H¹} + ‖z(t)‖²_{H¹})` with `v`, `z` the `H¹₀`-lifts of `u`, `u'`,
both square integrable on `(0, ∞)` (Poincaré with the identities of Theorems 10.1 and
10.2 (b)). -/
theorem memLpThrough_three_of_isBounded
    (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : IsSolution Ω u₀ u) (hu₀ : u₀ ∈ (dirichletLaplacian Ω).domain) :
    Bochner.MemLpThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 3 2 Ω volume) 2
      u (Ioi 0) := by
  obtain ⟨v₀, hv₀⟩ := dirichletLaplacian_exists_sobolevZero_lift ⟨u₀, hu₀⟩
  have hint2 : IntegrableOn (fun t ↦ ‖sobolevThreeLift Ω hΩ hΓ v₀ t‖ ^ (2 : ℝ≥0∞).toReal)
      (Ioi 0) := by
    refine (h.integrableOn_norm_sq_sobolevThreeLift hΩb hΩ hΓ hu₀ hv₀).congr_fun (fun t _ ↦ ?_)
      measurableSet_Ioi
    rw [ENNReal.toReal_ofNat, Real.rpow_two]
  exact Bochner.MemLpThrough.of_contDiffOnThrough_of_integrable
    (contDiffOn_sobolevThreeLift hΩ hΓ v₀).continuousOn
    (fun t ht ↦ (h.fnL_sobolevThreeLift hΩ hΓ hv₀ ht).symm) measurableSet_Ioi two_ne_zero
    ENNReal.ofNat_ne_top hint2

end IsSolution

end Heat

end SobolevThree

/-! ### The space–time reading: `u ∈ C^∞(Ω̄ × [ε, ∞))`, `u ∈ C^∞(Ω̄ × [0, ∞))` -/

section SpaceTime

namespace Heat

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- **`u ∈ C^∞((0, ∞); H^m(Ω))` for every `m` on a `C^∞` domain with bounded boundary**: the
`H^{2ℓ}` clauses `contDiffOnThrough_sobolev` for every `ℓ`, lowered to every order `m ≤ 2ℓ`
(`Bochner.ContDiffOnThrough.sobolev_of_le`). -/
theorem contDiffOnThrough_sobolev_forall (h : IsSolution Ω u₀ u)
    (hΩ : IsContDiffChartDomain ∞ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) (m : ℕ) :
    Bochner.ContDiffOnThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis m 2 Ω
      volume) ∞ u (Ioi 0) :=
  (h.contDiffOnThrough_sobolev (ℓ := m) (hΩ.of_le (WithTop.coe_le_coe.2 le_top)) hΓ).sobolev_of_le
    (by omega)

/-- **(5): `u ∈ C^∞(Ω̄ × [ε, ∞))` for every `ε > 0`** ([brezis2011functional] Theorem 10.1), on a
`C^∞` domain with bounded boundary: there is `U : ℝ^N × ℝ → ℝ` with `U(·, t) = u(t)` almost
everywhere on `Ω` for every `t > 0`, such that for every `ε > 0`, `U` is `C^∞` on `Ω × (ε, ∞)`
with every derivative extending continuously to `closure Ω × [ε, ∞)` (`ContDiffOnClosure`). The
conclusion cannot be strengthened to `Ω̄ × [0, ∞)`: with `L²` data the solution is not smooth
up to `t = 0`. Proof: `u ∈ C^∞((0, ∞); H^m(Ω))` for every `m` (`contDiffOnThrough_sobolev_forall`,
Theorem 9.25 through `D(A^ℓ) ↪ H^{2ℓ}`) and the space–time bridge
`Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ioi` on the extension domain
`Ω` (`IsSobolevExtensionDomainAll.of_isContDiffChartDomain`). The book invokes Corollary 9.15
for `H^{2ℓ} ⊆ C^k(Ω̄)`, whose hypothesis "`m − N/p` not an integer" fails at `p = 2` for even
`N`; the bridge uses the integer-safe form `k + N/2 < m`. -/
theorem contDiffOnClosure_spaceTime (h : IsSolution Ω u₀ u)
    (hΩ : IsContDiffChartDomain ∞ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ U : EuclideanSpace ℝ (Fin (d + 1)) × ℝ → ℝ,
      (∀ t ∈ Ioi (0 : ℝ),
        (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] u t) ∧
      ∀ ε > (0 : ℝ),
        ContDiffOnClosure ℝ ∞ U ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ×ˢ Ioi ε) :=
  Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ioi
    (IsSobolevExtensionDomainAll.of_isContDiffChartDomain (hΩ.of_le (by simp)) hΓ)
    (h.contDiffOnThrough_sobolev_forall hΩ hΓ)

/-- **`u ∈ C^∞([0, ∞); H^{2ℓ}(Ω))` for `u₀ ∈ D(A^k)` for every `k`**: one lift for all orders.
The lifts of `contDiffOnThrough_sobolev_Ici_of_powDomain` at the orders `n` agree on `[0, ∞)`
(`SobolevMultiIndex.fnL_injective`), so the lift at order `0` is `C^n` on `[0, ∞)` for every
`n`. -/
theorem contDiffOnThrough_sobolev_Ici_of_forall_powDomain (h : IsSolution Ω u₀ u)
    (hu₀ : ∀ k, ∃ x : (dirichletLaplacian Ω).PowDomain k, applyL (dirichletLaplacian Ω) k 0 x = u₀)
    {ℓ : ℕ}
    (hΩ : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    Bochner.ContDiffOnThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ) 2 Ω
      volume) ∞ u (Ici 0) := by
  have hn : ∀ n : ℕ, Bochner.ContDiffOnThrough
      (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ) 2 Ω volume) n u (Ici 0) := by
    intro n
    obtain ⟨x, hx⟩ := hu₀ (ℓ + n)
    have := h.contDiffOnThrough_sobolev_Ici_of_powDomain x hx (ℓ := ℓ) (by omega) hΩ hΓ
    rwa [show ℓ + n - ℓ = n by omega] at this
  obtain ⟨v, hv0, huv⟩ := hn 0
  refine ⟨v, ?_, huv⟩
  rw [contDiffOn_infty]
  intro n
  obtain ⟨w, hw, huw⟩ := hn n
  refine hw.congr fun t ht ↦ ?_
  exact fnL_injective ((huv t ht).symm.trans (huw t ht))

/-- **`u ∈ C^∞([0, ∞); H^m(Ω))` for every `m`** when `u₀ ∈ D(A^k)` for every `k`, on a `C^∞`
domain with bounded boundary. -/
theorem contDiffOnThrough_sobolev_Ici_forall (h : IsSolution Ω u₀ u)
    (hu₀ : ∀ k, ∃ x : (dirichletLaplacian Ω).PowDomain k, applyL (dirichletLaplacian Ω) k 0 x = u₀)
    (hΩ : IsContDiffChartDomain ∞ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) (m : ℕ) :
    Bochner.ContDiffOnThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis m 2 Ω
      volume) ∞ u (Ici 0) :=
  (h.contDiffOnThrough_sobolev_Ici_of_forall_powDomain hu₀ (ℓ := m)
    (hΩ.of_le (WithTop.coe_le_coe.2 le_top)) hΓ).sobolev_of_le (by omega)

/-- **Theorem 10.2 (c)** ([brezis2011functional]): on a `C^∞` domain with bounded boundary, if
`u₀ ∈ D(A^k)` for every `k` — the book's `u₀ ∈ H^{2k}(Ω)` with the compatibility conditions (8)
`Δ^j u₀ = 0` on `Γ`, by `dirichletLaplacian_mem_powDomain_iff` — then `u ∈ C^∞(Ω̄ × [0, ∞))`:
there is `U : ℝ^N × ℝ → ℝ` with `U(·, t) = u(t)` almost everywhere on `Ω` for every `t ≥ 0`,
`C^∞` on `Ω × (0, ∞)` with every derivative extending continuously to `closure Ω × [0, ∞)`
(`ContDiffOnClosure`). Proof: `u ∈ C^∞([0, ∞); H^m(Ω))` for every `m`
(`contDiffOnThrough_sobolev_Ici_forall`) and the space–time bridge on `[0, ∞)`
(`Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ici`). -/
theorem contDiffOnClosure_spaceTime_Ici (h : IsSolution Ω u₀ u)
    (hu₀ : ∀ k, ∃ x : (dirichletLaplacian Ω).PowDomain k, applyL (dirichletLaplacian Ω) k 0 x = u₀)
    (hΩ : IsContDiffChartDomain ∞ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ U : EuclideanSpace ℝ (Fin (d + 1)) × ℝ → ℝ,
      (∀ t ∈ Ici (0 : ℝ),
        (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] u t) ∧
      ContDiffOnClosure ℝ ∞ U ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ×ˢ Ioi 0) :=
  Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ici
    (IsSobolevExtensionDomainAll.of_isContDiffChartDomain (hΩ.of_le (by simp)) hΓ)
    (h.contDiffOnThrough_sobolev_Ici_forall hu₀ hΩ hΓ)

end IsSolution

end Heat

end SpaceTime
