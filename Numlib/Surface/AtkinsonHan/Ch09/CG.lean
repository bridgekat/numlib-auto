import Numlib.Surface.AtkinsonHan.Ch05.ConjugateGradient
import Numlib.Surface.AtkinsonHan.Ch09.Galerkin

/-!
# The conjugate gradient method: variational formulation (§9.4)

Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009.

The variational problem (9.4.1) is turned into the operator equation (9.4.7) `A u = f` through the
Riesz representation (9.4.5)–(9.4.6), and Algorithm 1 of §9.4 -- written here as `cgIterate`,
directly in the book's variables `u_k`, `r_k`, `s_k`, `α_k`, `β_k` -- is shown to be the backbone's
`CG.iterate` for that operator (`cgIterate_eq`).  All of the algorithm's properties (residual
orthogonality, `A`-conjugacy of the search directions, the Galerkin/energy-minimization
characterization, the convergence rates of Theorem 5.6.1) then transfer.

Algorithm 2 of §9.4 (nonlinear conjugate gradients for a strictly convex `J`) is **out of scope**:
the book quotes its convergence without proof, and its line search is an argmin that need not
exist in general.
-/

open Filter Topology
open scoped InnerProductSpace

namespace AtkinsonHan.Ch09

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {a : BilinForm V} {M α : ℝ}

/-- The residual of §9.4: the `r ∈ V` with `(r, v) = ℓ(v) − a(u, v)` for all `v`. -/
noncomputable def residual (a : BilinForm V) (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V)
    (u : V) : V :=
  SesqForm.rieszRep (ℓ - a.toCLM hM u)

/-- The step length `α_k = ‖r_k‖²/a(s_k, s_k)` of Algorithm 1. -/
noncomputable def cgAlpha (a : BilinForm V) (st : CG.State V) : ℝ :=
  ‖st.r‖ ^ 2 / a st.p st.p

/-- One step of Algorithm 1 of §9.4: `u_{k+1} = u_k + α_k s_k`, `r_{k+1}` the residual at
`u_{k+1}`, `s_{k+1} = r_{k+1} + β_k s_k` with `β_k = ‖r_{k+1}‖²/‖r_k‖²`.  The state is the
backbone's `CG.State`, whose fields `x`, `r`, `p` are the book's `u_k`, `r_k`, `s_k`. -/
noncomputable def cgStep (a : BilinForm V) (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V)
    (st : CG.State V) : CG.State V :=
  { x := st.x + cgAlpha a st • st.p
    r := residual a hM ℓ (st.x + cgAlpha a st • st.p)
    p := residual a hM ℓ (st.x + cgAlpha a st • st.p)
          + (‖residual a hM ℓ (st.x + cgAlpha a st • st.p)‖ ^ 2 / ‖st.r‖ ^ 2) • st.p }

/-- Algorithm 1 of §9.4 started at `u₀` with `s_0 = r_0`. -/
noncomputable def cgIterate (a : BilinForm V) (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V)
    (u₀ : V) (k : ℕ) : CG.State V :=
  (cgStep a hM ℓ)^[k] ⟨u₀, residual a hM ℓ u₀, residual a hM ℓ u₀⟩

/-! ### The residual -/

theorem inner_residual (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V) (u v : V) :
    ⟪residual a hM ℓ u, v⟫_ℝ = ℓ v - a u v := by
  rw [residual, SesqForm.inner_rieszRep]
  rfl

/-- The residual is `f − A u` for the operator `A` and right-hand side `f` of (9.4.5)–(9.4.6). -/
theorem residual_eq (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V) (u : V) :
    residual a hM ℓ u = SesqForm.rieszRep ℓ - BilinForm.toOperator a hM u := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_residual, inner_sub_left, SesqForm.inner_rieszRep, BilinForm.inner_toOperator]

/-- `r_k = 0` exactly at the solution: the residual is minus the Riesz representative of the
Gâteaux derivative of the energy (see `hasFDerivAt_energy`). -/
theorem residual_eq_neg_rieszRep (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V) (u : V) :
    residual a hM ℓ u = -SesqForm.rieszRep (a.toCLM hM u - ℓ) := by
  rw [residual, show (ℓ - a.toCLM hM u) = -(a.toCLM hM u - ℓ) from by abel, SesqForm.rieszRep,
    SesqForm.rieszRep, map_neg]

/-! ### Algorithm 1 is the backbone's conjugate gradient iteration -/

private theorem cgAlpha_eq (hM : a.IsBoundedWith M) (st : CG.State V) :
    cgAlpha a st = CG.alpha (BilinForm.toOperator a hM : V →ₗ[ℝ] V) st := by
  rw [cgAlpha, CG.alpha, real_inner_self_eq_norm_sq]
  congr 1
  exact (BilinForm.inner_toOperator hM st.p st.p).symm

private theorem cgStep_eq (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V) (st : CG.State V)
    (hst : st.r = SesqForm.rieszRep ℓ - BilinForm.toOperator a hM st.x) :
    cgStep a hM ℓ st = CG.step (BilinForm.toOperator a hM : V →ₗ[ℝ] V) st := by
  have hα := cgAlpha_eq hM st
  have hr : residual a hM ℓ (st.x + cgAlpha a st • st.p)
      = st.r - CG.alpha (BilinForm.toOperator a hM : V →ₗ[ℝ] V) st •
        (BilinForm.toOperator a hM : V →ₗ[ℝ] V) st.p := by
    rw [residual_eq hM, hst, hα, map_add, map_smul]
    abel
  have hβ : ∀ w : V, ‖w‖ ^ 2 / ‖st.r‖ ^ 2 = (inner ℝ w w : ℝ) / inner ℝ st.r st.r := by
    intro w
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  simp only [cgStep, CG.step, CG.State.mk.injEq]
  refine ⟨by rw [hα], hr, ?_⟩
  rw [hr, hβ]

/-- Algorithm 1 of §9.4 is the backbone's conjugate gradient iteration for the operator `A` and
right-hand side `f` of (9.4.5)–(9.4.6). -/
theorem cgIterate_eq (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V) (u₀ : V) (k : ℕ) :
    cgIterate a hM ℓ u₀ k
      = CG.iterate (BilinForm.toOperator a hM : V →ₗ[ℝ] V) (SesqForm.rieszRep ℓ) u₀ k := by
  induction k with
  | zero =>
    rw [cgIterate, Function.iterate_zero_apply, CG.iterate_zero, CG.init, residual_eq hM]
    rfl
  | succ k ih =>
    have hstep : cgIterate a hM ℓ u₀ (k + 1) = cgStep a hM ℓ (cgIterate a hM ℓ u₀ k) := by
      rw [cgIterate, cgIterate, Function.iterate_succ_apply']
    rw [hstep, ih, CG.iterate_succ]
    refine cgStep_eq hM ℓ _ ?_
    have := CG.residual_eq (BilinForm.toOperator a hM : V →ₗ[ℝ] V) (SesqForm.rieszRep ℓ) u₀ k
    exact this

/-! ### Properties of `A` and `f`, and the operator form of the problem -/

/-- (9.4.2)–(9.4.3): for a bounded symmetric `V`-elliptic form, `A` is symmetric with quadratic
form between `α ‖v‖²` and `M ‖v‖²`. -/
theorem isSymmetricBoundedBy_toOperator (hM : a.IsBoundedWith M)
    (hs : LinearMap.BilinForm.IsSymm a) (ha : a.IsEllipticWith α) :
    (BilinForm.toOperator a hM : V →ₗ[ℝ] V).IsSymmetricBoundedBy α M where
  isSymmetric := (SesqForm.isHermitian_iff_toOperator_isSymmetric _).mp
    ((BilinForm.isSymm_iff_isHermitian hM).mp hs)
  le_re_inner := fun x => by
    have h1 : RCLike.re (inner ℝ ((BilinForm.toOperator a hM : V →ₗ[ℝ] V) x) x) = a x x := by
      rw [show ((BilinForm.toOperator a hM : V →ₗ[ℝ] V)) x = BilinForm.toOperator a hM x from rfl,
        BilinForm.inner_toOperator hM x x]
      simp
    rw [h1]
    exact ha x
  re_inner_le := fun x => by
    have h1 : RCLike.re (inner ℝ ((BilinForm.toOperator a hM : V →ₗ[ℝ] V) x) x) = a x x := by
      rw [show ((BilinForm.toOperator a hM : V →ₗ[ℝ] V)) x = BilinForm.toOperator a hM x from rfl,
        BilinForm.inner_toOperator hM x x]
      simp
    rw [h1]
    calc a x x ≤ |a x x| := le_abs_self _
      _ ≤ M * ‖x‖ * ‖x‖ := hM x x
      _ = M * ‖x‖ ^ 2 := by ring

/-- The operator form (9.4.7) of the solution `u` of (9.4.4). -/
theorem toOperator_eq_rieszRep (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V) {u : V}
    (hu : ∀ v, a u v = ℓ v) :
    (BilinForm.toOperator a hM : V →ₗ[ℝ] V) u = SesqForm.rieszRep ℓ :=
  (BilinForm.toOperator_eq_rieszRep_iff hM ℓ u).mpr hu

/-! ### Properties of Algorithm 1 transported from the backbone -/

variable {ℓ : StrongDual ℝ V} {u₀ : V}

/-- The iterates of Algorithm 1 solve the Galerkin problem on the Krylov spaces
`u₀ + 𝒦_k(A, r₀)`; equivalently they minimize the energy there. -/
theorem cg_isGalerkinIterate (hM : a.IsBoundedWith M) (hs : LinearMap.BilinForm.IsSymm a)
    (hα : 0 < α) (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) (u₀ : V) (k : ℕ) :
    Krylov.IsGalerkinIterate (BilinForm.toOperator a hM : V →ₗ[ℝ] V) (SesqForm.rieszRep ℓ) u₀ k
      (cgIterate a hM ℓ u₀ k).x := by
  rw [cgIterate_eq hM ℓ u₀ k]
  exact CG.isGalerkinIterate _ _
    ((isSymmetricBoundedBy_toOperator hM hs ha).isSymmetricCoercive hα) k

/-- Residual orthogonality: `(r_i, r_j) = 0` for `i ≠ j`. -/
theorem cg_inner_residual_eq_zero (hM : a.IsBoundedWith M) (hs : LinearMap.BilinForm.IsSymm a)
    (hα : 0 < α) (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) (u₀ : V) {i j : ℕ} (h : i ≠ j) :
    ⟪(cgIterate a hM ℓ u₀ i).r, (cgIterate a hM ℓ u₀ j).r⟫_ℝ = 0 := by
  rw [cgIterate_eq hM ℓ u₀ i, cgIterate_eq hM ℓ u₀ j]
  exact CG.inner_residual_eq_zero _ _
    ((isSymmetricBoundedBy_toOperator hM hs ha).isSymmetricCoercive hα) h

/-- `a`-conjugacy of the search directions: `a(s_i, s_j) = 0` for `i ≠ j`. -/
theorem cg_apply_direction_eq_zero (hM : a.IsBoundedWith M) (hs : LinearMap.BilinForm.IsSymm a)
    (hα : 0 < α) (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) (u₀ : V) {i j : ℕ} (h : i ≠ j) :
    a (cgIterate a hM ℓ u₀ i).p (cgIterate a hM ℓ u₀ j).p = 0 := by
  rw [← BilinForm.inner_toOperator hM, cgIterate_eq hM ℓ u₀ i, cgIterate_eq hM ℓ u₀ j]
  exact CG.inner_apply_direction_eq_zero _ _
    ((isSymmetricBoundedBy_toOperator hM hs ha).isSymmetricCoercive hα) h

/-- The energy norm of the error decreases along Algorithm 1. -/
theorem cg_energyNorm_error_antitone (hM : a.IsBoundedWith M) (hs : LinearMap.BilinForm.IsSymm a)
    (hα : 0 < α) (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) {u : V} (hu : ∀ v, a u v = ℓ v)
    (u₀ : V) : Antitone fun k => a.energyNorm (u - (cgIterate a hM ℓ u₀ k).x) := by
  have h := CG.energyNorm_error_antitone (A := (BilinForm.toOperator a hM : V →ₗ[ℝ] V))
    (SesqForm.rieszRep ℓ) u₀ ((isSymmetricBoundedBy_toOperator hM hs ha).isSymmetricCoercive hα)
    (toOperator_eq_rieszRep hM ℓ hu)
  intro i j hij
  simp only [BilinForm.energyNorm_eq_energyNorm_toOperator hM, cgIterate_eq hM ℓ u₀]
  exact h hij

/-! ### Convergence (Theorem 5.6.1 transported through `cgIterate_eq`) -/

/-- (5.6.4) for Algorithm 1: `‖u − u_{k+1}‖_a ≤ ((M − α)/(M + α)) ‖u − u_k‖_a`.  The rate is the
backbone's `Krylov.IsGalerkinIterate.energyNorm_error_succ_le`, read through `cgIterate_eq`. -/
theorem cg_energy_rate (hM : a.IsBoundedWith M) (hs : LinearMap.BilinForm.IsSymm a) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) {u : V} (hu : ∀ v, a u v = ℓ v) (u₀ : V)
    (k : ℕ) :
    a.energyNorm (u - (cgIterate a hM ℓ u₀ (k + 1)).x)
      ≤ (M - α) / (M + α) * a.energyNorm (u - (cgIterate a hM ℓ u₀ k).x) := by
  have hAc := (isSymmetricBoundedBy_toOperator hM hs ha).isSymmetricCoercive hα
  simp only [BilinForm.energyNorm_eq_energyNorm_toOperator hM, cgIterate_eq hM ℓ u₀]
  exact Krylov.IsGalerkinIterate.energyNorm_error_succ_le hα
    (isSymmetricBoundedBy_toOperator hM hs ha) (CG.isGalerkinIterate _ _ hAc k)
    (CG.isGalerkinIterate _ _ hAc (k + 1)) (toOperator_eq_rieszRep hM ℓ hu)

/-- (5.6.5) for Algorithm 1: `‖u − u_k‖_a ≤ 2 ((√κ − 1)/(√κ + 1))^k ‖u − u_0‖_a` with
`κ = M/α`.  The hypothesis `α < M` is not needed for this bound (the backbone states it for
`α ≤ M`); it is kept here only because `cg_converges` below uses it. -/
theorem cg_energy_bound (hM : a.IsBoundedWith M) (hs : LinearMap.BilinForm.IsSymm a) (hα : 0 < α)
    (hαM : α < M) (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) {u : V} (hu : ∀ v, a u v = ℓ v)
    (u₀ : V) (k : ℕ) :
    a.energyNorm (u - (cgIterate a hM ℓ u₀ k).x)
      ≤ 2 * ((Real.sqrt (M / α) - 1) / (Real.sqrt (M / α) + 1)) ^ k *
          a.energyNorm (u - u₀) := by
  simp only [BilinForm.energyNorm_eq_energyNorm_toOperator hM, cgIterate_eq hM ℓ u₀]
  exact Krylov.IsGalerkinIterate.energyNorm_error_le hα hαM.le
    (isSymmetricBoundedBy_toOperator hM hs ha)
    (CG.isGalerkinIterate _ _ ((isSymmetricBoundedBy_toOperator hM hs ha).isSymmetricCoercive hα) k)
    (toOperator_eq_rieszRep hM ℓ hu)

/-- Convergence of Algorithm 1: `u_k → u`.  It follows from (5.6.5) together with
`√α ‖v‖ ≤ ‖v‖_a`. -/
theorem cg_converges (hM : a.IsBoundedWith M) (hs : LinearMap.BilinForm.IsSymm a) (hα : 0 < α)
    (hαM : α < M) (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) {u : V} (hu : ∀ v, a u v = ℓ v)
    (u₀ : V) : Tendsto (fun k => (cgIterate a hM ℓ u₀ k).x) atTop (𝓝 u) := by
  set ρ : ℝ := (Real.sqrt (M / α) - 1) / (Real.sqrt (M / α) + 1) with hρdef
  have hsa : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have hone : (1 : ℝ) < Real.sqrt (M / α) := by
    have h1 : (1 : ℝ) < M / α := (one_lt_div hα).mpr hαM
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (M / α) := Real.sqrt_lt_sqrt (by norm_num) h1
  have hρ0 : 0 ≤ ρ := div_nonneg (by linarith) (by linarith)
  have hρ1 : ρ < 1 := by
    rw [hρdef, div_lt_one (by linarith)]
    linarith
  have hmaj : Tendsto (fun k => 2 * a.energyNorm (u - u₀) / Real.sqrt α * ρ ^ k) atTop (𝓝 0) := by
    have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul
      (2 * a.energyNorm (u - u₀) / Real.sqrt α)
    simpa using hpow
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hmaj
  have h1 : Real.sqrt α * ‖u - (cgIterate a hM ℓ u₀ k).x‖
      ≤ a.energyNorm (u - (cgIterate a hM ℓ u₀ k).x) :=
    BilinForm.sqrt_mul_norm_le_energyNorm hM hα.le ha _
  have h2 := cg_energy_bound hM hs hα hαM ha ℓ hu u₀ k
  have hrw : 2 * a.energyNorm (u - u₀) / Real.sqrt α * ρ ^ k
      = 2 * a.energyNorm (u - u₀) * ρ ^ k / Real.sqrt α := by ring
  rw [norm_sub_rev, hrw, le_div_iff₀ hsa]
  calc ‖u - (cgIterate a hM ℓ u₀ k).x‖ * Real.sqrt α
      = Real.sqrt α * ‖u - (cgIterate a hM ℓ u₀ k).x‖ := mul_comm _ _
    _ ≤ 2 * ρ ^ k * a.energyNorm (u - u₀) := h1.trans h2
    _ = 2 * a.energyNorm (u - u₀) * ρ ^ k := by ring

/-! ### The energy functional and its derivative -/

omit [CompleteSpace V] in
/-- The Fréchet (hence Gâteaux) derivative of the energy functional (§9.4):
`⟨E'(u), v⟩ = a(u,v) − ℓ(v)`. -/
theorem hasFDerivAt_energy (hM0 : 0 ≤ M) (hM : a.IsBoundedWith M)
    (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V) (u : V) :
    HasFDerivAt (a.energy ℓ) (a.toCLM hM u - ℓ) u := by
  have hkey : ∀ y : V, a.energy ℓ y - a.energy ℓ u - (a.toCLM hM u - ℓ) (y - u)
      = (1 / 2 : ℝ) * a (y - u) (y - u) := by
    intro y
    have hsym : a y u = a u y := BilinForm.isSymm_iff.mp hs y u
    have h1 : (a.toCLM hM u - ℓ) (y - u) = a u y - a u u - (ℓ y - ℓ u) := by simp
    have h2 : a (y - u) (y - u) = a y y - a u y - (a y u - a u u) := by simp [map_sub]
    simp only [BilinForm.energy]
    rw [h1, h2, hsym]
    ring
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [Metric.ball_mem_nhds u (show (0 : ℝ) < 2 * c / (M + 1) by positivity)] with y hy
  have hd : ‖y - u‖ < 2 * c / (M + 1) := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.mp hy
  have hd' : M * ‖y - u‖ ≤ 2 * c := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < M + 1)] at hd
    nlinarith [norm_nonneg (y - u)]
  rw [hkey y, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hb : |a (y - u) (y - u)| ≤ M * ‖y - u‖ * ‖y - u‖ := hM _ _
  have hnn : (0 : ℝ) ≤ ‖y - u‖ := norm_nonneg _
  calc (1 / 2 : ℝ) * |a (y - u) (y - u)| ≤ (1 / 2 : ℝ) * (M * ‖y - u‖ * ‖y - u‖) := by linarith
    _ ≤ c * ‖y - u‖ := by nlinarith

/-- The residual is minus the Riesz representative of the derivative of the energy:
`(r_k, v) = −⟨E'(u_k), v⟩`. -/
theorem inner_residual_eq_neg_fderiv (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V) (u v : V) :
    ⟪residual a hM ℓ u, v⟫_ℝ = -((a.toCLM hM u - ℓ) v) := by
  rw [inner_residual]
  have h1 : (a.toCLM hM u - ℓ) v = a u v - ℓ v := rfl
  rw [h1]
  ring

/-- (9.4.4) is equivalent to minimizing the energy over all of `V` (the case `V_N = ⊤` of
(9.1.6)). -/
theorem energy_isMinOn_iff (hM : a.IsBoundedWith M) (hα : 0 < α) (ha : a.IsEllipticWith α)
    (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V) (u : V) :
    IsMinOn (a.energy ℓ) Set.univ u ↔ ∀ v, a u v = ℓ v := by
  simpa using Ch08.thm_8_3_3_subspace hM hα ha hs ℓ ⊤ Submodule.mem_top

end AtkinsonHan.Ch09
