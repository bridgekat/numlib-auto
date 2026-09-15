import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The linear transport equation and hyperbolic systems, solved along characteristics

Classical (pointwise) solutions of the scalar transport equation

  `∂_t u + a ∂_x u + a₀ u = f`,  `u(·, 0) = u₀`

on the closed half plane `ℝ × [0, ∞)` (`Transport.IsSolution`), of the constant-coefficient system
`∂_t u + A ∂_x u = 0` (`Transport.IsSystemSolutionOn`, `Transport.IsSystemSolution`), and of the
wave equation `∂_tt u = γ² ∂_xx u` on a strip (`Transport.IsWaveSolution`).

**Everything is the chain rule.** A *characteristic* (`Transport.IsCharacteristic`) is an integral
curve `x' = a(x, t)` of the speed field; along it a differentiable solution satisfies the ordinary
differential equation `d/dt u(x(t), t) = f - a₀ u`
(`Transport.IsSolution.hasDerivAt_comp_characteristic`). For the homogeneous equation with constant
speed the characteristics are the lines `x₀ + a t` (`Transport.characteristic_const`, unique by
`Transport.IsCharacteristic.eq_of_const`) and the solution is constant along them
(`Transport.IsSolution.comp_characteristic_const`), which gives at once the travelling wave
`u₀(x - a t)` (`Transport.isSolution_comp_sub`), its uniqueness
(`Transport.IsSolution.eq_comp_sub`) and the sup bound `|u| ≤ sup |u₀|`
(`Transport.IsSolution.abs_le_sup`).

**Hyperbolic systems.** `A` is *hyperbolic* when it is diagonalizable over `ℝ`,
`A = T Λ T⁻¹` (`Transport.IsHyperbolic`), and *strictly hyperbolic* when the eigenvalues are
distinct (`Transport.IsStrictlyHyperbolic`); the columns of `T` are then right eigenvectors
(`Transport.mulVec_col_eq_smul`). The *characteristic variables* `w = T⁻¹ u` solve `p` decoupled
scalar equations (`Transport.IsSystemSolution.characteristicVariables`), whence the solution
formula `u(x, t) = ∑_k w_k(x - λ_k t, 0) ω^k` (`Transport.isSystemSolution_sum`,
`Transport.IsSystemSolution.eq_sum`) and the *domain of dependence*
`Transport.domainOfDependence`: the value at `(x̄, t̄)` reads the datum only at the `p` feet
`x̄ - λ_k t̄` (`Transport.IsSystemSolution.eq_of_eqOn_domainOfDependence`). The wave equation is the
system for `(∂_x u, ∂_t u)` with the matrix `Transport.waveMatrix γ = !![0, -1; -γ², 0]`
(`Transport.IsWaveSolution.isSystemSolution`), which is strictly hyperbolic with eigenvalues `±γ`
(`Transport.waveMatrix_isStrictlyHyperbolic`).

## Conventions

A function of the two variables is written curried, `u : ℝ → ℝ → ℝ` with arguments `x t`, and its
differentiability is that of the uncurried `fun q : ℝ × ℝ => u q.1 q.2` *within* the closed region,
so that the one-sided derivative at `t = 0` needs no separate case. `Transport.HasPartialsOn`
bundles this together with the two partial derivatives, which are named functions rather than
`fderivWithin` expressions: the derivative at `(x, t)` is `Transport.partialsCLM (ux x t) (ut x t)`,
the functional `(y, s) ↦ ux y + ut s`. Only differentiability is assumed, never continuity of the
derivative; every result below holds at that strength, and a `C¹` solution in the sense of
[quarteroni2000numerical] §13.5 is in particular one of these.

`Transport.IsWaveSolution` is the one place where a second derivative occurs. It asks for the
partial derivatives of `ux` and of `ut`, with *one* function `uxt` for the two mixed partials; for
a `C²` function that is no restriction, by the symmetry of the second derivative
(`ContDiffWithinAt.isSymmSndFDerivWithinAt`), and it is what the change of variables to the
first-order system uses.

The material is [quarteroni2000numerical] §13.5–13.6, with the inflow problem (13.64) of §13.10 as
`Transport.IsInflowSolution`; it opens every text on hyperbolic equations.
-/

open Set Matrix

namespace Transport

/-! ### Partial derivatives of a function of two real variables -/

/-- The continuous linear functional `(y, s) ↦ ux * y + ut * s` on `ℝ × ℝ`: the Fréchet derivative
of a function of `(x, t)` whose partial derivatives are `ux` and `ut`. -/
noncomputable def partialsCLM (ux ut : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  ux • ContinuousLinearMap.fst ℝ ℝ ℝ + ut • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp]
theorem partialsCLM_apply (ux ut : ℝ) (q : ℝ × ℝ) : partialsCLM ux ut q = ux * q.1 + ut * q.2 :=
  rfl

/-- A pair of vanishing partial derivatives is the zero functional. -/
theorem partialsCLM_zero : partialsCLM 0 0 = 0 :=
  ContinuousLinearMap.ext fun q => by simp

/-- The functional of a pair of partial derivatives is additive in the pair. -/
theorem partialsCLM_add (a b c d : ℝ) :
    partialsCLM a b + partialsCLM c d = partialsCLM (a + c) (b + d) :=
  ContinuousLinearMap.ext fun q => by
    simp only [_root_.add_apply, partialsCLM_apply]
    ring

/-- The functional of a pair of partial derivatives is homogeneous in the pair. -/
theorem partialsCLM_smul (r a b : ℝ) : r • partialsCLM a b = partialsCLM (r * a) (r * b) :=
  ContinuousLinearMap.ext fun q => by
    simp only [_root_.smul_apply, partialsCLM_apply, smul_eq_mul]
    ring

/-- A linear combination of pairs of partial derivatives. -/
theorem partialsCLM_sum {ι : Type*} (s : Finset ι) (c ux ut : ι → ℝ) :
    ∑ i ∈ s, c i • partialsCLM (ux i) (ut i)
      = partialsCLM (∑ i ∈ s, c i * ux i) (∑ i ∈ s, c i * ut i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using partialsCLM_zero.symm
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi, ih, partialsCLM_smul,
      partialsCLM_add]

/-- **A function of two real variables with the given partial derivatives on a region**: at every
point of `s` the uncurried `u` is differentiable within `s`, with derivative
`Transport.partialsCLM (ux x t) (ut x t)`. Differentiability *within* `s` is what makes the
one-sided derivatives at the boundary of `s` the right notion. -/
def HasPartialsOn (s : Set (ℝ × ℝ)) (u ux ut : ℝ → ℝ → ℝ) : Prop :=
  ∀ q ∈ s, HasFDerivWithinAt (fun r : ℝ × ℝ => u r.1 r.2)
    (partialsCLM (ux q.1 q.2) (ut q.1 q.2)) s q

/-- Partial derivatives restrict to a smaller region. -/
theorem HasPartialsOn.mono {s t : Set (ℝ × ℝ)} {u ux ut : ℝ → ℝ → ℝ} (h : HasPartialsOn s u ux ut)
    (hts : t ⊆ s) : HasPartialsOn t u ux ut :=
  fun q hq => (h q (hts hq)).mono hts

/-- A finite linear combination of functions with partial derivatives has the combined partial
derivatives. -/
theorem HasPartialsOn.sum {ι : Type*} {s : Finset ι} {S : Set (ℝ × ℝ)} {c : ι → ℝ}
    {u ux ut : ι → ℝ → ℝ → ℝ} (h : ∀ i ∈ s, HasPartialsOn S (u i) (ux i) (ut i)) :
    HasPartialsOn S (fun x t => ∑ i ∈ s, c i * u i x t) (fun x t => ∑ i ∈ s, c i * ux i x t)
      (fun x t => ∑ i ∈ s, c i * ut i x t) := by
  intro q hq
  have h0 := HasFDerivWithinAt.sum fun i (hi : i ∈ s) => (h i hi q hq).const_mul (c i)
  rw [show (∑ i ∈ s, fun r : ℝ × ℝ => c i * u i r.1 r.2)
      = fun r : ℝ × ℝ => ∑ i ∈ s, c i * u i r.1 r.2 from funext fun r => Finset.sum_apply r s _,
    partialsCLM_sum] at h0
  exact h0

/-- **The travelling wave has partial derivatives `g'` and `-a g'`**: the chain rule for
`(x, t) ↦ g (x - a t)`. -/
theorem hasPartialsOn_comp_sub {g : ℝ → ℝ} (hg : Differentiable ℝ g) (a : ℝ) (S : Set (ℝ × ℝ)) :
    HasPartialsOn S (fun x t => g (x - a * t)) (fun x t => deriv g (x - a * t))
      (fun x t => -(a * deriv g (x - a * t))) := by
  intro q _
  have h1 : HasFDerivAt (fun r : ℝ × ℝ => r.1 - a * r.2) (partialsCLM 1 (-a)) q := by
    refine ((hasFDerivAt_fst (𝕜 := ℝ)).sub ((hasFDerivAt_snd (𝕜 := ℝ)).const_mul a)).congr_fderiv ?_
    exact ContinuousLinearMap.ext fun r => by simp [sub_eq_add_neg]
  have h2 := ((hg (q.1 - a * q.2)).hasDerivAt.comp_hasFDerivAt q h1).hasFDerivWithinAt (s := S)
  refine h2.congr_fderiv (ContinuousLinearMap.ext fun r => ?_)
  simp only [_root_.smul_apply, smul_eq_mul, partialsCLM_apply]
  ring

/-! ### The scalar transport equation and its characteristics -/

/-- **A classical solution of the transport equation** `∂_t u + a ∂_x u + a₀ u = f` with datum `u₀`
on the closed half plane `ℝ × [0, ∞)` ([quarteroni2000numerical] (13.28), and (13.26) when
`a₀ = f = 0`): `u` has partial derivatives `ux`, `ut` there, they satisfy the equation at every
point with `t ≥ 0`, and `u(·, 0) = u₀`. -/
def IsSolution (a a₀ f : ℝ → ℝ → ℝ) (u₀ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ ux ut : ℝ → ℝ → ℝ, HasPartialsOn (univ ×ˢ Ici 0) u ux ut ∧
    (∀ x t : ℝ, 0 ≤ t → ut x t + a x t * ux x t + a₀ x t * u x t = f x t) ∧ ∀ x, u x 0 = u₀ x

/-- **A characteristic curve** of the speed field `a` through `x₀` ([quarteroni2000numerical]
(13.27)): the solution of `x' = a(x, t)` on `[0, ∞)` with `x 0 = x₀`. -/
def IsCharacteristic (a : ℝ → ℝ → ℝ) (x₀ : ℝ) (x : ℝ → ℝ) : Prop :=
  x 0 = x₀ ∧ ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt x (a (x t) t) (Ici 0) t

/-- **The characteristics of a constant speed field are the lines** `x₀ + a t`. -/
theorem characteristic_const (a x₀ : ℝ) :
    IsCharacteristic (fun _ _ => a) x₀ (fun t => x₀ + a * t) := by
  refine ⟨by simp, fun t _ => ?_⟩
  simpa using (((hasDerivAt_id t).const_mul a).const_add x₀).hasDerivWithinAt

/-- A curve with vanishing derivative on `[0, ∞)` is constant there. -/
private theorem eq_zero_of_hasDerivWithinAt_zero {g : ℝ → ℝ}
    (hg : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt g 0 (Ici 0) t) {t : ℝ} (ht : 0 ≤ t) : g t = g 0 := by
  have hcont : ContinuousOn g (Icc 0 t) := fun s hs =>
    ((hg s hs.1).continuousWithinAt).mono (Icc_subset_Ici_self)
  refine constant_of_has_deriv_right_zero hcont (fun s hs => ?_) t (right_mem_Icc.2 ht)
  exact (hg s hs.1).mono (Ici_subset_Ici.2 hs.1)

/-- **Uniqueness of the characteristic of a constant speed field**: every characteristic of
`a` through `x₀` is the line `x₀ + a t`. -/
theorem IsCharacteristic.eq_of_const {a x₀ : ℝ} {x : ℝ → ℝ}
    (hx : IsCharacteristic (fun _ _ => a) x₀ x) {t : ℝ} (ht : 0 ≤ t) : x t = x₀ + a * t := by
  have hg : ∀ s : ℝ, 0 ≤ s → HasDerivWithinAt (fun s => x s - a * s) 0 (Ici 0) s := fun s hs => by
    have h0 : HasDerivWithinAt x a (Ici 0) s := hx.2 s hs
    have h1 : HasDerivWithinAt (fun y : ℝ => a * y) a (Ici 0) s := by
      simpa using ((hasDerivAt_id s).const_mul a).hasDerivWithinAt
    have := h0.sub h1
    rwa [sub_self] at this
  have h := eq_zero_of_hasDerivWithinAt_zero hg ht
  simp only [mul_zero, sub_zero, hx.1] at h
  linarith

/-- **The solution satisfies an ordinary differential equation along a characteristic**:
`d/dt u(x(t), t) = f - a₀ u` on `(x(t), t)` ([quarteroni2000numerical] §13.5). This is the chain
rule for `t ↦ (x t, t)`. -/
theorem IsSolution.hasDerivAt_comp_characteristic {a a₀ f : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ}
    {u : ℝ → ℝ → ℝ} (hu : IsSolution a a₀ f u₀ u) {x₀ : ℝ} {x : ℝ → ℝ}
    (hx : IsCharacteristic a x₀ x) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t => u (x t) t) (f (x t) t - a₀ (x t) t * u (x t) t) (Ici 0) t := by
  obtain ⟨ux, ut, hd, hpde, -⟩ := hu
  have hcurve : HasDerivWithinAt (fun s => (x s, s)) (a (x t) t, 1) (Ici 0) t :=
    (hx.2 t ht).prodMk (hasDerivWithinAt_id t _)
  have hmaps : MapsTo (fun s => (x s, s)) (Ici (0 : ℝ)) (univ ×ˢ Ici 0) :=
    fun s hs => ⟨mem_univ _, hs⟩
  have h := (hd (x t, t) ⟨mem_univ _, ht⟩).comp_hasDerivWithinAt_of_eq
    (f := fun s => (x s, s)) t hcurve hmaps rfl
  have hval : partialsCLM (ux (x t) t) (ut (x t) t) (a (x t) t, 1)
      = f (x t) t - a₀ (x t) t * u (x t) t := by
    have := hpde (x t) t ht
    simp only [partialsCLM_apply, mul_one]
    linarith
  rw [hval] at h
  exact h

/-- **A solution of the homogeneous equation with constant speed is constant along
characteristics**: `u(x(t), t) = u₀(x₀)` ([quarteroni2000numerical] §13.5, `du/dt = 0`). -/
theorem IsSolution.comp_characteristic_const {a : ℝ} {u₀ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hu : IsSolution (fun _ _ => a) 0 0 u₀ u) {x₀ : ℝ} {x : ℝ → ℝ}
    (hx : IsCharacteristic (fun _ _ => a) x₀ x) {t : ℝ} (ht : 0 ≤ t) : u (x t) t = u₀ x₀ := by
  have hg : ∀ s : ℝ, 0 ≤ s → HasDerivWithinAt (fun s => u (x s) s) 0 (Ici 0) s := fun s hs => by
    simpa using hu.hasDerivAt_comp_characteristic hx hs
  have hconst := eq_zero_of_hasDerivWithinAt_zero hg ht
  obtain ⟨-, -, -, -, hinit⟩ := hu
  rw [hconst, hx.1]
  exact hinit x₀

/-- **The travelling wave solves the transport equation**: `u(x, t) = u₀(x - a t)` is a solution of
`∂_t u + a ∂_x u = 0` with datum `u₀` ([quarteroni2000numerical] §13.5). -/
theorem isSolution_comp_sub {a : ℝ} {u₀ : ℝ → ℝ} (hu₀ : Differentiable ℝ u₀) :
    IsSolution (fun _ _ => a) 0 0 u₀ fun x t => u₀ (x - a * t) := by
  exact ⟨_, _, hasPartialsOn_comp_sub hu₀ a _, fun x t _ => by simp, fun x => by simp⟩

/-- **Uniqueness for the transport equation**: every solution of `∂_t u + a ∂_x u = 0` with datum
`u₀` is the travelling wave `u₀(x - a t)` ([quarteroni2000numerical] §13.5). -/
theorem IsSolution.eq_comp_sub {a : ℝ} {u₀ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hu : IsSolution (fun _ _ => a) 0 0 u₀ u) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    u x t = u₀ (x - a * t) := by
  simpa using hu.comp_characteristic_const (characteristic_const a (x - a * t)) ht

/-- **The maximum principle for the transport equation**: `|u(x, t)| ≤ sup_s |u₀(s)|`
([quarteroni2000numerical] §13.8.4). -/
theorem IsSolution.abs_le_sup {a : ℝ} {u₀ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hu : IsSolution (fun _ _ => a) 0 0 u₀ u) (hb : BddAbove (range fun s => |u₀ s|)) (x : ℝ)
    {t : ℝ} (ht : 0 ≤ t) : |u x t| ≤ ⨆ s, |u₀ s| := by
  rw [hu.eq_comp_sub x ht]
  exact le_ciSup hb _

/-! ### Hyperbolic systems -/

variable {p : ℕ}

/-- **A classical solution of the system** `∂_t u + A ∂_x u = 0` with datum `u₀`, on the region
`s × [0, ∞)` ([quarteroni2000numerical] (13.30)): every component has partial derivatives there,
the vector equation holds at every point with `t ≥ 0`, and `u(·, 0) = u₀` on `s`. -/
def IsSystemSolutionOn (s : Set ℝ) (A : Matrix (Fin p) (Fin p) ℝ) (u₀ : ℝ → Fin p → ℝ)
    (u : ℝ → ℝ → Fin p → ℝ) : Prop :=
  ∃ ux ut : ℝ → ℝ → Fin p → ℝ,
    (∀ k, HasPartialsOn (s ×ˢ Ici 0) (fun x t => u x t k) (fun x t => ux x t k)
      fun x t => ut x t k) ∧
    (∀ x ∈ s, ∀ t : ℝ, 0 ≤ t → ut x t + A *ᵥ ux x t = 0) ∧ ∀ x ∈ s, u x 0 = u₀ x

/-- **A classical solution of the system** `∂_t u + A ∂_x u = 0` on the whole half plane
([quarteroni2000numerical] (13.30)). -/
def IsSystemSolution (A : Matrix (Fin p) (Fin p) ℝ) (u₀ : ℝ → Fin p → ℝ)
    (u : ℝ → ℝ → Fin p → ℝ) : Prop := IsSystemSolutionOn univ A u₀ u

/-- **A hyperbolic system**: `A` is diagonalizable over `ℝ`, `A = T Λ T⁻¹` with `Λ` the diagonal
matrix of its (real) eigenvalues ([quarteroni2000numerical] §13.6). -/
def IsHyperbolic (A : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  ∃ (T : Matrix (Fin p) (Fin p) ℝ) (lam : Fin p → ℝ), IsUnit T ∧ A = T * diagonal lam * T⁻¹

/-- **A strictly hyperbolic system**: hyperbolic with distinct eigenvalues
([quarteroni2000numerical] §13.6). -/
def IsStrictlyHyperbolic (A : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  ∃ (T : Matrix (Fin p) (Fin p) ℝ) (lam : Fin p → ℝ),
    IsUnit T ∧ Function.Injective lam ∧ A = T * diagonal lam * T⁻¹

/-- A strictly hyperbolic system is hyperbolic. -/
theorem IsStrictlyHyperbolic.isHyperbolic {A : Matrix (Fin p) (Fin p) ℝ}
    (h : IsStrictlyHyperbolic A) : IsHyperbolic A :=
  let ⟨T, lam, hT, _, hA⟩ := h; ⟨T, lam, hT, hA⟩

/-- A matrix–vector product is the combination of the columns: `T v = ∑_k v_k ω^k`. -/
theorem mulVec_eq_sum_smul_col (T : Matrix (Fin p) (Fin p) ℝ) (v : Fin p → ℝ) :
    T *ᵥ v = ∑ k, v k • Tᵀ k := by
  ext j
  simp [Matrix.mulVec, dotProduct, mul_comm]

/-- **The columns of `T` are right eigenvectors**: `A ω^k = λ_k ω^k` for `A = T Λ T⁻¹`
([quarteroni2000numerical] §13.6). -/
theorem mulVec_col_eq_smul {A T : Matrix (Fin p) (Fin p) ℝ} {lam : Fin p → ℝ} (hT : IsUnit T)
    (hA : A = T * diagonal lam * T⁻¹) (k : Fin p) : A *ᵥ Tᵀ k = lam k • Tᵀ k := by
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).1 hT
  have hAT : A * T = T * diagonal lam := by
    rw [hA, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
  ext i
  have h1 : (A *ᵥ Tᵀ k) i = (A * T) i k := by
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have h2 : (lam k • Tᵀ k) i = (T * diagonal lam) i k := by
    simp [Matrix.mul_apply, Matrix.diagonal_apply, mul_comm]
  rw [h1, h2, hAT]

/-- **The characteristic variables decouple the system**: if `A = T Λ T⁻¹` and `u` solves
`∂_t u + A ∂_x u = 0`, then each component of `w = T⁻¹ u` solves the scalar transport equation with
speed `λ_k` and datum `(T⁻¹ u₀)_k` ([quarteroni2000numerical] §13.6). -/
theorem IsSystemSolution.characteristicVariables {A T : Matrix (Fin p) (Fin p) ℝ}
    {lam : Fin p → ℝ} (hT : IsUnit T) (hA : A = T * diagonal lam * T⁻¹) {u₀ : ℝ → Fin p → ℝ}
    {u : ℝ → ℝ → Fin p → ℝ} (hu : IsSystemSolution A u₀ u) (k : Fin p) :
    IsSolution (fun _ _ => lam k) 0 0 (fun x => (T⁻¹ *ᵥ u₀ x) k) fun x t => (T⁻¹ *ᵥ u x t) k := by
  obtain ⟨ux, ut, hd, hpde, hinit⟩ := hu
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).1 hT
  have hTA : T⁻¹ * A = diagonal lam * T⁻¹ := by
    rw [hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  refine ⟨fun x t => (T⁻¹ *ᵥ ux x t) k, fun x t => (T⁻¹ *ᵥ ut x t) k, ?_, fun x t ht => ?_,
    fun x => by change (T⁻¹ *ᵥ u x 0) k = (T⁻¹ *ᵥ u₀ x) k; rw [hinit x (mem_univ x)]⟩
  · have := HasPartialsOn.sum (s := (Finset.univ : Finset (Fin p))) (c := fun j => T⁻¹ k j)
      (u := fun j x t => u x t j) (ux := fun j x t => ux x t j) (ut := fun j x t => ut x t j)
      fun j _ => hd j
    simpa [Matrix.mulVec, dotProduct] using this
  · have hz := hpde x (mem_univ x) t ht
    have key : (T⁻¹ *ᵥ ut x t) k + lam k * (T⁻¹ *ᵥ ux x t) k = 0 := by
      have h1 : T⁻¹ *ᵥ (ut x t + A *ᵥ ux x t) = 0 := by rw [hz, Matrix.mulVec_zero]
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hTA, ← Matrix.mulVec_mulVec] at h1
      have h2 := congrFun h1 k
      rwa [Pi.add_apply, Matrix.mulVec_diagonal, Pi.zero_apply] at h2
    simp only [Pi.zero_apply, zero_mul, add_zero]
    linarith

/-- **The solution formula for a hyperbolic system**: `u(x, t) = ∑_k w_k(x - λ_k t, 0) ω^k`, with
`w = T⁻¹ u₀` the characteristic variables of the datum and `ω^k` the columns of `T`, solves
`∂_t u + A ∂_x u = 0` ([quarteroni2000numerical] §13.6). -/
theorem isSystemSolution_sum {A T : Matrix (Fin p) (Fin p) ℝ} {lam : Fin p → ℝ} (hT : IsUnit T)
    (hA : A = T * diagonal lam * T⁻¹) {u₀ : ℝ → Fin p → ℝ}
    (hu₀ : ∀ k, Differentiable ℝ fun x => (T⁻¹ *ᵥ u₀ x) k) :
    IsSystemSolution A u₀ fun x t => ∑ k, (T⁻¹ *ᵥ u₀ (x - lam k * t)) k • Tᵀ k := by
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).1 hT
  set c : Fin p → ℝ → ℝ := fun k x => (T⁻¹ *ᵥ u₀ x) k with hc
  refine ⟨fun x t j => ∑ k, deriv (c k) (x - lam k * t) * T j k,
    fun x t j => ∑ k, -(lam k * deriv (c k) (x - lam k * t)) * T j k, fun j => ?_,
    fun x _ t _ => ?_, fun x _ => ?_⟩
  · have := HasPartialsOn.sum (s := (Finset.univ : Finset (Fin p))) (c := fun k => T j k)
      (u := fun k x t => c k (x - lam k * t))
      (ux := fun k x t => deriv (c k) (x - lam k * t))
      (ut := fun k x t => -(lam k * deriv (c k) (x - lam k * t)))
      (S := (univ ×ˢ Ici 0 : Set (ℝ × ℝ)))
      fun k _ => hasPartialsOn_comp_sub (hu₀ k) (lam k) _
    simpa [hc, mul_comm] using this
  · ext j
    have hcol : ∀ k, (A *ᵥ Tᵀ k) j = lam k * T j k := fun k => by
      have := congrFun (mulVec_col_eq_smul hT hA k) j
      simpa using this
    have hAx : (A *ᵥ fun j => ∑ k, deriv (c k) (x - lam k * t) * T j k) j
        = ∑ k, deriv (c k) (x - lam k * t) * (lam k * T j k) := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hcol k]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [Pi.add_apply, Pi.zero_apply, hAx, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun k _ => by ring
  · have h0 : ∑ k, c k (x - lam k * 0) • Tᵀ k = T *ᵥ (T⁻¹ *ᵥ u₀ x) := by
      rw [mulVec_eq_sum_smul_col]
      exact Finset.sum_congr rfl fun k _ => by rw [mul_zero, sub_zero]
    change ∑ k, c k (x - lam k * 0) • Tᵀ k = u₀ x
    rw [h0, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- **Uniqueness for a hyperbolic system**: every solution is given by the solution formula
`u(x, t) = ∑_k w_k(x - λ_k t, 0) ω^k` ([quarteroni2000numerical] §13.6). -/
theorem IsSystemSolution.eq_sum {A T : Matrix (Fin p) (Fin p) ℝ} {lam : Fin p → ℝ} (hT : IsUnit T)
    (hA : A = T * diagonal lam * T⁻¹) {u₀ : ℝ → Fin p → ℝ} {u : ℝ → ℝ → Fin p → ℝ}
    (hu : IsSystemSolution A u₀ u) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    u x t = ∑ k, (T⁻¹ *ᵥ u₀ (x - lam k * t)) k • Tᵀ k := by
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).1 hT
  have hw : ∀ k, (T⁻¹ *ᵥ u x t) k = (T⁻¹ *ᵥ u₀ (x - lam k * t)) k := fun k =>
    (hu.characteristicVariables hT hA k).eq_comp_sub x ht
  have hTT : u x t = T *ᵥ (T⁻¹ *ᵥ u x t) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  rw [hTT, mulVec_eq_sum_smul_col]
  exact Finset.sum_congr rfl fun k _ => by rw [hw k]

/-- **The domain of dependence** of `u(x̄, t̄)` ([quarteroni2000numerical] (13.31)): the `p` feet
`x̄ - λ_k t̄` of the characteristics issuing from `(x̄, t̄)`. -/
def domainOfDependence (lam : Fin p → ℝ) (xb tb : ℝ) : Set ℝ := range fun k => xb - lam k * tb

/-- **The solution reads the datum only on the domain of dependence**: two data agreeing on
`domainOfDependence lam x̄ t̄` give solutions agreeing at `(x̄, t̄)`
([quarteroni2000numerical] §13.6). -/
theorem IsSystemSolution.eq_of_eqOn_domainOfDependence {A T : Matrix (Fin p) (Fin p) ℝ}
    {lam : Fin p → ℝ} (hT : IsUnit T) (hA : A = T * diagonal lam * T⁻¹)
    {u₀ v₀ : ℝ → Fin p → ℝ} {u v : ℝ → ℝ → Fin p → ℝ} (hu : IsSystemSolution A u₀ u)
    (hv : IsSystemSolution A v₀ v) {xb tb : ℝ} (htb : 0 ≤ tb)
    (h : EqOn u₀ v₀ (domainOfDependence lam xb tb)) : u xb tb = v xb tb := by
  rw [hu.eq_sum hT hA xb htb, hv.eq_sum hT hA xb htb]
  exact Finset.sum_congr rfl fun k _ => by rw [h ⟨k, rfl⟩]

/-! ### The wave equation as a first-order system -/

/-- **The matrix of the wave equation** ([quarteroni2000numerical] (13.35)):
`A = !![0, -1; -γ², 0]`, the coefficient of the first-order system satisfied by
`(∂_x u, ∂_t u)`. -/
def waveMatrix (γ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; -γ ^ 2, 0]

/-- **The wave equation is strictly hyperbolic** for `γ ≠ 0`, with eigenvalues `±γ` and
eigenvectors `(1, ∓γ)` ([quarteroni2000numerical] §13.6.1). -/
theorem waveMatrix_isStrictlyHyperbolic {γ : ℝ} (hγ : γ ≠ 0) :
    IsStrictlyHyperbolic (waveMatrix γ) := by
  refine ⟨!![1, 1; -γ, γ], ![γ, -γ], ?_, ?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_fin_two_of]
    intro h
    apply hγ
    linarith
  · have hne : γ ≠ -γ := fun h => hγ (by linarith)
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] at hij
      exact absurd hij hne
    · simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] at hij
      exact absurd hij.symm hne
    · rfl
  · have hdet : IsUnit (!![(1 : ℝ), 1; -γ, γ]).det := by
      rw [isUnit_iff_ne_zero, Matrix.det_fin_two_of]
      intro h
      apply hγ
      linarith
    have hmul : waveMatrix γ * !![(1 : ℝ), 1; -γ, γ]
        = !![(1 : ℝ), 1; -γ, γ] * diagonal ![γ, -γ] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [waveMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal_apply] <;> ring
    calc waveMatrix γ = waveMatrix γ * !![(1 : ℝ), 1; -γ, γ] * (!![(1 : ℝ), 1; -γ, γ])⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = !![(1 : ℝ), 1; -γ, γ] * diagonal ![γ, -γ] * (!![(1 : ℝ), 1; -γ, γ])⁻¹ := by rw [hmul]

/-- **A classical solution of the wave equation** `∂_tt u - γ² ∂_xx u = f` on the strip
`[α, β] × [0, ∞)`, with initial displacement `u₀`, initial velocity `v₀` and the homogeneous
Dirichlet conditions at the two ends ([quarteroni2000numerical] (13.33)–(13.34)). The first
partial derivatives `ux`, `ut` have partial derivatives in turn, with a single function `uxt` for
the two mixed partials — no restriction for a `C²` function, by the symmetry of the second
derivative. -/
def IsWaveSolution (γ : ℝ) (f : ℝ → ℝ → ℝ) (u₀ v₀ : ℝ → ℝ) (α β : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ ux ut uxx uxt utt : ℝ → ℝ → ℝ,
    HasPartialsOn (Icc α β ×ˢ Ici 0) u ux ut ∧ HasPartialsOn (Icc α β ×ˢ Ici 0) ux uxx uxt ∧
      HasPartialsOn (Icc α β ×ˢ Ici 0) ut uxt utt ∧
      (∀ x ∈ Icc α β, ∀ t : ℝ, 0 ≤ t → utt x t - γ ^ 2 * uxx x t = f x t) ∧
      (∀ x ∈ Icc α β, u x 0 = u₀ x ∧ ut x 0 = v₀ x) ∧
      ∀ t : ℝ, 0 ≤ t → u α t = 0 ∧ u β t = 0

/-- **The wave equation as a first-order system** ([quarteroni2000numerical] (13.35)): for a
homogeneous wave solution the pair `ω = (∂_x u, ∂_t u)` satisfies `∂_t ω + A ∂_x ω = 0` with
`A = waveMatrix γ`, and its datum is `(u₀', v₀)`. The first row of the system is the symmetry of
the mixed partials, the second is the wave equation itself. -/
theorem IsWaveSolution.isSystemSolution {γ : ℝ} {u₀ v₀ : ℝ → ℝ} {α β : ℝ} {u : ℝ → ℝ → ℝ}
    (h : IsWaveSolution γ 0 u₀ v₀ α β u) :
    ∃ w : ℝ → ℝ → Fin 2 → ℝ, IsSystemSolutionOn (Icc α β) (waveMatrix γ) (fun x => w x 0) w ∧
      (∀ x ∈ Icc α β, HasDerivWithinAt u₀ (w x 0 0) (Icc α β) x) ∧
      ∀ x ∈ Icc α β, w x 0 1 = v₀ x := by
  obtain ⟨ux, ut, uxx, uxt, utt, h1, h2, h3, heq, hinit, -⟩ := h
  refine ⟨fun x t => ![ux x t, ut x t], ⟨fun x t => ![uxx x t, uxt x t],
    fun x t => ![uxt x t, utt x t], fun k => ?_, fun x hx t ht => ?_, fun _ _ => rfl⟩,
    fun x hx => ?_, fun x hx => (hinit x hx).2⟩
  · fin_cases k
    · exact h2
    · exact h3
  · ext k
    have hz := heq x hx t ht
    simp only [Pi.zero_apply] at hz
    fin_cases k <;>
      simp only [Fin.zero_eta, Fin.mk_one, Pi.add_apply, Pi.zero_apply, waveMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.of_apply] <;> linarith
  · have hmaps : MapsTo (fun s : ℝ => (s, (0 : ℝ))) (Icc α β) (Icc α β ×ˢ Ici 0) :=
      fun s hs => ⟨hs, by simp⟩
    have hcurve : HasDerivWithinAt (fun s : ℝ => (s, (0 : ℝ))) (1, 0) (Icc α β) x :=
      (hasDerivWithinAt_id x _).prodMk (hasDerivWithinAt_const x _ _)
    have hd := (h1 (x, 0) ⟨hx, by simp⟩).comp_hasDerivWithinAt_of_eq
      (f := fun s : ℝ => (s, (0 : ℝ))) x hcurve hmaps rfl
    simp only [partialsCLM_apply, mul_one, mul_zero, add_zero] at hd
    refine hd.congr (fun s hs => ((hinit s hs).1).symm) ?_
    exact ((hinit x hx).1).symm

/-! ### The inflow problem on a strip -/

/-- **The inflow problem** on the strip `[α, β] × [0, T]` ([quarteroni2000numerical] (13.64)):
`∂_t u + a ∂_x u + a₀ u = f` with the datum `u₀` at `t = 0` and the boundary value `φ` at the
inflow end `x = α` (the inflow end for `a > 0`). -/
def IsInflowSolution (a : ℝ → ℝ) (a₀ f : ℝ → ℝ → ℝ) (φ u₀ : ℝ → ℝ) (α β T : ℝ)
    (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ ux ut : ℝ → ℝ → ℝ, HasPartialsOn (Icc α β ×ˢ Icc 0 T) u ux ut ∧
    (∀ x ∈ Icc α β, ∀ t ∈ Icc (0 : ℝ) T,
      ut x t + a x * ux x t + a₀ x t * u x t = f x t) ∧
    (∀ t ∈ Icc (0 : ℝ) T, u α t = φ t) ∧ ∀ x ∈ Icc α β, u x 0 = u₀ x

end Transport
