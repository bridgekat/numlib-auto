import NumlibSurface.QuarteroniSaccoSaleri.Chapter13.Section06
import NumlibSurface.QuarteroniSaccoSaleri.Chapter13.Section07

/-!
# Quarteroni–Sacco–Saleri §13.8: analysis of the finite difference methods

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §13.8.

*Consistency* (§13.8.1) is the vanishing of the local truncation error `τ(Δt, Δx) = sup_{j,n}
|τ_j^n|`; because the exact solution of (13.26) is the travelling wave `u₀(x - a t)`, `τ_j^n` is a
combination of values of the single-variable `u₀` near the foot `ξ = x_j - a t^n` of the
characteristic, and Table 13.1's orders `O(Δt + Δx²)`, `O(Δx²/Δt + Δt + Δx²)`, `O(Δt² + Δx²)`,
`O(Δt + Δx)` come out with explicit constants.

*Stability* (13.46) in the discrete norms (13.47) is uniform boundedness of the powers over a
finite horizon. §13.8.3's **CFL condition** `|aλ| ≤ 1` (13.48) is necessary, by the numerical
domain of dependence: the value at `(0, 1)` reads the datum only on `|x| ≤ 1/λ`, while the exact
solution reads it at `-a`. The book calls it necessary *and sufficient*; that is an erratum, since
its own §13.8.4 shows the forward Euler/centred scheme satisfies it and is unstable. Sufficiency
is scheme by scheme: upwind and Lax–Friedrichs are monotone under the CFL condition, hence
nonexpansive in `ℓ¹` and subject to the discrete maximum principle (13.53); Lax–Wendroff and
upwind are `ℓ²`-stable by Theorem 13.1.

*Von Neumann analysis* (§13.8.4) diagonalizes the periodic scheme in the discrete Fourier basis:
(13.52) `u^n_j = ∑_k α_k γ_k^n e^{ikjh}`, Theorem 13.1 (`|γ_k| ≤ 1` gives `‖·‖_{Δ,2}` stability)
and its converse half. The amplification factors of the four schemes and of the implicit one are
computed, and their moduli characterize the stability conditions: `λ|a| ≤ 1` for upwind
(Exercise 6), `|λa| ≤ 1` for Lax–Friedrichs and Lax–Wendroff, and no condition at all for backward
Euler/centred (Exercise 7).

A second erratum: §13.8.4 prints the upwind amplification factor for `a < 0` with `e^{-ikh} - 1`;
the scheme gives `e^{ikh} - 1`. The modulus, hence the stability condition, is unaffected;
`FiniteDifference.Hyperbolic.amplificationFactor_upwind` states a single formula covering both
signs.

The backbone homes are `Numlib/FiniteDifference/{Stencil,VonNeumann,Hyperbolic}`.
-/

open Set Matrix FiniteDifference
open scoped ENNReal

namespace QuarteroniSaccoSaleri.Chapter13

/-! ### §13.8.1, consistency and order -/

/-- **The local truncation error** of §13.8.1 for the scheme `c` and the exact solution
`u₀(x - a t)`, expressed at the foot `ξ = x_j - a t^n` of the characteristic:
`τ = [u₀(ξ - aΔt) - ∑_s c_s u₀(ξ - sΔx)] / Δt`. -/
noncomputable def truncationError (c : Stencil) (a Δt Δx : ℝ) (u₀ : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  Hyperbolic.truncationError c a Δt Δx u₀ ξ

/-- The truncation error is the residual left at the grid point `(x_j, t^n)` by the exact solution
of (13.26) (Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.8.1). -/
theorem truncationError_eq {a : ℝ} {u₀ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} (hu : equation_13_26 a u₀ u)
    (c : Stencil) {Δt Δx : ℝ} (hΔt : 0 ≤ Δt) (j : ℤ) (n : ℕ) :
    truncationError c a Δt Δx u₀ ((j : ℝ) * Δx - a * (n * Δt))
      = (u ((j : ℝ) * Δx) (((n : ℝ) + 1) * Δt)
          - Stencil.apply c (fun i : ℤ => u ((i : ℝ) * Δx) (n * Δt)) j) / Δt :=
  Hyperbolic.truncationError_eq_of_isSolution hu c hΔt j n

/-- **Consistency** (§13.8.1): `τ(Δt, Δx) = sup_ξ |τ| → 0` as `Δt` and `Δx` tend to `0`
independently. -/
def isConsistent (c : ℝ → ℝ → Stencil) (a : ℝ) (u₀ : ℝ → ℝ) : Prop :=
  Hyperbolic.IsConsistent c a u₀

/-- **Order `p` in time and `q` in space** (§13.8.1): `τ(Δt, Δx) = O(Δt^p + Δx^q)`; a scheme of
positive order in each variable is consistent. -/
def isOfOrder (c : ℝ → ℝ → Stencil) (a : ℝ) (u₀ : ℝ → ℝ) (p q : ℕ) : Prop :=
  Hyperbolic.IsOfOrder c a u₀ p q

/-- A scheme of positive order in each variable is consistent
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.8.1). -/
theorem isOfOrder_isConsistent {c : ℝ → ℝ → Stencil} {a : ℝ} {u₀ : ℝ → ℝ} {p q : ℕ} (hp : p ≠ 0)
    (hq : q ≠ 0) (h : isOfOrder c a u₀ p q) : isConsistent c a u₀ :=
  Hyperbolic.IsOfOrder.isConsistent hp hq h

/-- **Table 13.1, forward (and backward) Euler/centred**: the truncation error is
`O(Δt + Δx²)` — explicitly `(a²/2) M₂ Δt + (|a|/6) M₃ Δx²` for a datum with `|u₀''| ≤ M₂` and
`|u₀'''| ≤ M₃` (Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.8.1). -/
theorem table_13_1_truncation_forwardEulerCentred {u₀ : ℝ → ℝ} {M₂ M₃ a Δt Δx lam : ℝ}
    (hu : ContDiff ℝ 3 u₀) (hM₂ : ∀ y, |iteratedDeriv 2 u₀ y| ≤ M₂)
    (hM₃ : ∀ y, |iteratedDeriv 3 u₀ y| ≤ M₃) (hΔt : 0 < Δt) (hΔx : 0 < Δx)
    (hlam : lam = Δt / Δx) (ξ : ℝ) :
    |truncationError (equation_13_37 a lam) a Δt Δx u₀ ξ|
      ≤ a ^ 2 / 2 * M₂ * Δt + |a| / 6 * M₃ * Δx ^ 2 :=
  Hyperbolic.abs_truncationError_forwardEulerCentred_le hu hM₂ hM₃ hΔt hΔx hlam ξ

/-- **Table 13.1, Lax–Friedrichs**: the truncation error is `O(Δx²/Δt + Δt + Δx²)`
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, Table 13.1). -/
theorem table_13_1_truncation_laxFriedrichs {u₀ : ℝ → ℝ} {M₂ M₃ a Δt Δx lam : ℝ}
    (hu : ContDiff ℝ 3 u₀) (hM₂ : ∀ y, |iteratedDeriv 2 u₀ y| ≤ M₂)
    (hM₃ : ∀ y, |iteratedDeriv 3 u₀ y| ≤ M₃) (hΔt : 0 < Δt) (hΔx : 0 < Δx)
    (hlam : lam = Δt / Δx) (ξ : ℝ) :
    |truncationError (equation_13_39 a lam) a Δt Δx u₀ ξ|
      ≤ M₂ / 2 * Δx ^ 2 / Δt + a ^ 2 / 2 * M₂ * Δt + |a| / 6 * M₃ * Δx ^ 2 :=
  Hyperbolic.abs_truncationError_laxFriedrichs_le hu hM₂ hM₃ hΔt hΔx hlam ξ

/-- **Table 13.1, Lax–Wendroff**: the truncation error is `O(Δt² + Δx²)`, the only second-order
scheme of §13.7 (Quarteroni–Sacco–Saleri, *Numerical Mathematics*, Table 13.1). -/
theorem table_13_1_truncation_laxWendroff {u₀ : ℝ → ℝ} {M₃ M₄ a Δt Δx lam : ℝ}
    (hu : ContDiff ℝ 4 u₀) (hM₃ : ∀ y, |iteratedDeriv 3 u₀ y| ≤ M₃)
    (hM₄ : ∀ y, |iteratedDeriv 4 u₀ y| ≤ M₄) (hΔt : 0 < Δt) (hΔt1 : Δt ≤ 1) (hΔx : 0 < Δx)
    (hΔx1 : Δx ≤ 1) (hlam : lam = Δt / Δx) (ξ : ℝ) :
    |truncationError (equation_13_40 a lam) a Δt Δx u₀ ξ|
      ≤ |a| ^ 3 / 6 * M₃ * Δt ^ 2 + (|a| / 6 * M₃ + (|a| + a ^ 2) / 24 * M₄) * Δx ^ 2 :=
  Hyperbolic.abs_truncationError_laxWendroff_le hu hM₃ hM₄ hΔt hΔt1 hΔx hΔx1 hlam ξ

/-- **Table 13.1, upwind**: the truncation error is `O(Δt + Δx)`
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, Table 13.1). -/
theorem table_13_1_truncation_upwind {u₀ : ℝ → ℝ} {M₂ a Δt Δx lam : ℝ} (hu : ContDiff ℝ 2 u₀)
    (hM₂ : ∀ y, |iteratedDeriv 2 u₀ y| ≤ M₂) (hΔt : 0 < Δt) (hΔx : 0 < Δx)
    (hlam : lam = Δt / Δx) (ξ : ℝ) :
    |truncationError (equation_13_41 a lam) a Δt Δx u₀ ξ|
      ≤ a ^ 2 / 2 * M₂ * Δt + |a| / 2 * M₂ * Δx :=
  Hyperbolic.abs_truncationError_upwind_le hu hM₂ hΔt hΔx hlam ξ

/-- **Convergence** (end of §13.8.1): the iterates started from the sampled datum approach the
exact solution uniformly on the grid, over a finite horizon. -/
def isConvergent (a : ℝ) (u₀ : ℝ → ℝ) (c : ℝ → ℝ → Stencil) (T : ℝ) : Prop :=
  Hyperbolic.IsConvergent a u₀ c T

/-! ### §13.8.2, the discrete norms and stability -/

/-- **(13.47)**, the discrete norms `‖v‖_{Δ,p} = (Δx ∑_j |v_j|^p)^{1/p}` and
`‖v‖_{Δ,∞} = sup_j |v_j|`. -/
noncomputable def equation_13_47 (p : ℝ≥0∞) (Δx : ℝ) (v : lp (fun _ : ℤ => ℝ) p) : ℝ :=
  FiniteDifference.discreteNorm p Δx v

/-- **(13.46)**, stability: for every horizon `T` there are `C_T` and `δ₀ > 0` with
`‖Q^n‖ ≤ C_T` whenever the steps lie in `(0, δ₀]` and `n Δt ≤ T`, i.e.
`‖u^n‖_Δ ≤ C_T ‖u^0‖_Δ`. -/
def equation_13_46 {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (Δt Δx : ι → ℝ) (Q : ∀ i, E i →L[ℝ] E i) : Prop :=
  FiniteDifference.IsStableFamily Δt Δx Q

/-- **Exercise 7**: the implicit backward Euler/centred scheme is unconditionally stable in
`‖·‖_{Δ,2}` with constant `1`, because the centred difference is skew-adjoint
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, Exercise 13.7 and §13.8.2). -/
theorem exercise_13_7 {a lam Δx : ℝ} (hΔx : 0 ≤ Δx) (u : lp (fun _ : ℤ => ℝ) 2) :
    equation_13_47 2 Δx (equation_13_43 a lam u) ≤ equation_13_47 2 Δx u := by
  refine mul_le_mul_of_nonneg_left (Hyperbolic.norm_backwardEulerCentred_apply_le a lam u)
    (Real.rpow_nonneg hΔx _)

/-! ### §13.8.3, the CFL condition -/

/-- **(13.48)**, the CFL condition `|a λ| ≤ 1`; the CFL number is `a λ`. The two variants of
§13.8.3 are `CFLVariable` (a variable speed field) and `CFLSystem` (a hyperbolic system). -/
def equation_13_48 (a lam : ℝ) : Prop := Hyperbolic.CFL a lam

/-- **The numerical domain of dependence** (§13.8.3): for a three-point stencil, `(c^n u)_j`
depends only on `u_{j-n}, …, u_{j+n}`, so `D_Δt(x_j, t^n) ⊆ {x : |x - x_j| ≤ n Δx = t^n/λ}`
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.8.3). -/
theorem numericalDomainOfDependence {c : Stencil} (hc : ∀ s ∈ c.support, |s| ≤ 1) (n : ℕ)
    {u v : ℤ → ℝ} {j : ℤ} (h : ∀ i : ℤ, |i - j| ≤ (n : ℤ) → u i = v i) :
    (Stencil.apply c)^[n] u j = (Stencil.apply c)^[n] v j :=
  Stencil.iterate_apply_congr_of_eqOn hc n (by simpa using h)

/-- **(13.49)**: for the scalar equation the CFL condition holds exactly when the domain of
dependence `D(x̄, t̄) = {x̄ - a t̄}` of (13.31) is contained in the limiting numerical one
`D₀(x̄, t̄) = {x : |x - x̄| ≤ t̄/λ}` (Quarteroni–Sacco–Saleri, *Numerical Mathematics*, equation
(13.49)). -/
theorem equation_13_49 {a lam xb tb : ℝ} (hlam : 0 < lam) (htb : 0 < tb) :
    equation_13_48 a lam ↔ |(xb - a * tb) - xb| ≤ tb / lam := by
  rw [equation_13_48, Hyperbolic.CFL, show (xb - a * tb) - xb = -(a * tb) from by ring, abs_neg,
    abs_mul, abs_mul, abs_of_pos htb, abs_of_pos hlam, le_div_iff₀ hlam]
  constructor <;> intro h <;> nlinarith [abs_nonneg a]

/-- **The CFL condition is necessary for convergence** (§13.8.3, with the book's "sufficient"
removed — see the module doc): if `|a| λ > 1`, a smooth bump datum concentrated at `-a` defeats
every three-point explicit scheme family, because the numerical value at `(0, 1)` reads the datum
only on `|x| ≤ 1/λ`, where it vanishes, while the exact solution there is `u₀(-a) = 1`. -/
theorem cfl_necessary {a lam : ℝ} (hlam : 0 < lam) (hcfl : 1 < |a| * lam)
    (c : ℝ → ℝ → Stencil) (hc : ∀ Δt Δx : ℝ, ∀ s ∈ (c Δt Δx).support, |s| ≤ 1) :
    ∃ u₀ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u₀ ∧ ¬isConvergent a u₀ c 1 :=
  Hyperbolic.not_isConvergent_of_one_lt_abs_mul hlam hcfl c hc

/-- **Under the CFL condition the upwind and Lax–Friedrichs stencils are monotone**: nonnegative
weights summing to `1` (Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.8.3). -/
theorem upwind_isMonotone {a lam : ℝ} (h0 : 0 ≤ lam * |a|) (h1 : lam * |a| ≤ 1)
    (h2 : |lam * a| ≤ 1) :
    Stencil.IsMonotone (equation_13_41 a lam) ∧ Stencil.IsMonotone (equation_13_39 a lam) :=
  ⟨Hyperbolic.upwind_isMonotone h0 h1, Hyperbolic.laxFriedrichs_isMonotone h2⟩

/-- **`ℓ¹` stability of the upwind scheme under the CFL condition**:
`‖u^{n+1}‖_{Δ,1} ≤ ‖u^n‖_{Δ,1}`, so (13.46) holds with `C_T = 1`
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.8.3). -/
theorem upwind_discreteNorm_le {a lam Δx : ℝ} (hΔx : 0 ≤ Δx) (h0 : 0 ≤ lam * |a|)
    (h1 : lam * |a| ≤ 1) (u : lp (fun _ : ℤ => ℝ) 1) :
    equation_13_47 1 Δx (Stencil.lpCLM (equation_13_41 a lam) 1 u) ≤ equation_13_47 1 Δx u :=
  mul_le_mul_of_nonneg_left
    ((Hyperbolic.upwind_isMonotone h0 h1).norm_lpCLM_apply_le u) (Real.rpow_nonneg hΔx _)

/-- **`ℓ¹` stability of the Lax–Friedrichs scheme under the CFL condition**
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.8.3). -/
theorem laxFriedrichs_discreteNorm_le {a lam Δx : ℝ} (hΔx : 0 ≤ Δx) (h : |lam * a| ≤ 1)
    (u : lp (fun _ : ℤ => ℝ) 1) :
    equation_13_47 1 Δx (Stencil.lpCLM (equation_13_39 a lam) 1 u) ≤ equation_13_47 1 Δx u :=
  mul_le_mul_of_nonneg_left
    ((Hyperbolic.laxFriedrichs_isMonotone h).norm_lpCLM_apply_le u) (Real.rpow_nonneg hΔx _)

/-! ### §13.8.4, the von Neumann analysis -/

/-- **(13.52)**: on the periodic grid of `N` nodes each Fourier mode is an eigenvector of a
constant-coefficient explicit scheme, so `u^n` multiplies the `k`-th coefficient by `γ_k^n`
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, equation (13.52)). -/
theorem equation_13_52 {N : ℕ} (c : Fin N → ℂ) (k : Fin N) (n : ℕ) :
    (FiniteDifference.periodicScheme c ^ n) *ᵥ FiniteDifference.fourierMode N k
      = FiniteDifference.amplificationFactor c k ^ n • FiniteDifference.fourierMode N k :=
  FiniteDifference.periodicScheme_pow_mulVec_fourierMode c k n

/-- **The forward Euler/centred amplification factor** `γ_k = 1 - i λ a sin φ_k`, with
`|γ_k|² = 1 + (λ a sin φ_k)²`, so `|γ_k| > 1` whenever `λ a sin φ_k ≠ 0` — the scheme is
unconditionally unstable (Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.8.4). -/
theorem amplificationFactor_forwardEulerCentred {N : ℕ} [NeZero N] (a lam : ℝ) (k : Fin N) :
    FiniteDifference.amplificationFactor
        (Stencil.toPeriodic N (equation_13_37 a lam)) k
        = 1 - Complex.I * (lam * a) * (Real.sin (Hyperbolic.gridPhase N k) : ℂ) ∧
      ‖FiniteDifference.amplificationFactor (Stencil.toPeriodic N (equation_13_37 a lam)) k‖ ^ 2
        = 1 + (lam * a) ^ 2 * Real.sin (Hyperbolic.gridPhase N k) ^ 2 ∧
      (lam * a * Real.sin (Hyperbolic.gridPhase N k) ≠ 0 →
        1 < ‖FiniteDifference.amplificationFactor
          (Stencil.toPeriodic N (equation_13_37 a lam)) k‖) :=
  ⟨Hyperbolic.amplificationFactor_forwardEulerCentred a lam k,
    Hyperbolic.norm_amplificationFactor_forwardEulerCentred_sq a lam k,
    fun h => Hyperbolic.one_lt_norm_amplificationFactor_forwardEulerCentred h⟩

/-- **Forward Euler/centred is unconditionally unstable in `‖·‖_{Δ,2}`**
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.8.4): at every fixed `λ > 0` and `a ≠ 0`
the family of periodic schemes with `Δx = 2π/N`, `Δt = λ Δx` violates (13.46), because the mode
nearest to `φ = π/2` has `|γ_k| ≥ √(1 + (λ a)²/2) > 1` on every grid. So the CFL condition is not
sufficient, and §13.8.3's "necessary and sufficient" is an erratum. -/
theorem forwardEulerCentred_not_isStable {a lam : ℝ} (ha : a ≠ 0) (hlam : 0 < lam) :
    ¬equation_13_46 (fun m : ℕ => lam * (2 * Real.pi / (m + 8)))
      (fun m : ℕ => 2 * Real.pi / (m + 8)) (Hyperbolic.forwardEulerCentredFamily a lam) :=
  Hyperbolic.forwardEulerCentred_not_isStableFamily ha hlam

/-- **The exact solution is bounded by its datum**: `|u(x, t)| = |u₀(x - a t)| ≤ sup |u₀|`,
against which the growth of the centred scheme is measured
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.8.4). -/
theorem exactSolution_abs_le {a : ℝ} {u₀ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} (hu : equation_13_26 a u₀ u)
    (hb : BddAbove (range fun s => |u₀ s|)) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    |u x t| ≤ ⨆ s, |u₀ s| :=
  hu.abs_le_sup hb x ht

/-- **Theorem 13.1**: if `|γ_k| ≤ 1` for every `k`, the periodic scheme is stable in `‖·‖_{Δ,2}`
with constant `1`, `‖Q^n u‖₂ ≤ ‖u‖₂`. The proof is the discrete Parseval identity of Lemma 10.1.
-/
theorem theorem_13_1 {N : ℕ} (c : Fin N → ℂ)
    (h : ∀ k, ‖FiniteDifference.amplificationFactor c k‖ ≤ 1) (n : ℕ)
    (u : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanLin (FiniteDifference.periodicScheme c ^ n) u‖ ≤ ‖u‖ :=
  FiniteDifference.norm_toEuclideanLin_periodicScheme_pow_le c h n u

/-- **The converse half of the von Neumann criterion** (used in the book's instability argument):
`|γ_k|^n ≤ ‖Q^n‖₂`, so a family stable with constant `C_T` over `[0, T]` has
`|γ_k| ≤ 1 + 2 (C_T - 1) Δt / T` (Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.8.4). -/
theorem theorem_13_1_necessary {N : ℕ} (c : Fin N → ℂ) {C Δt T : ℝ} (hC : 1 ≤ C) (hΔt : 0 < Δt)
    (hΔT : Δt ≤ T / 2)
    (hstab : ∀ n : ℕ, (n : ℝ) * Δt ≤ T →
      ‖toEuclideanCLM (𝕜 := ℂ) (FiniteDifference.periodicScheme c ^ n)‖ ≤ C) (k : Fin N) :
    (∀ n : ℕ, ‖FiniteDifference.amplificationFactor c k‖ ^ n
        ≤ ‖toEuclideanCLM (𝕜 := ℂ) (FiniteDifference.periodicScheme c ^ n)‖) ∧
      ‖FiniteDifference.amplificationFactor c k‖ ≤ 1 + 2 * (C - 1) * Δt / T :=
  ⟨fun n => FiniteDifference.norm_amplificationFactor_pow_le c k n,
    FiniteDifference.norm_amplificationFactor_le_one_add_of_forall_norm_pow_le c hC hΔt hΔT
      hstab k⟩

/-- **Exercise 6**, the upwind amplification factor: `γ_k = 1 - λ|a|(1 - cos φ_k) - i λ a sin φ_k`
(a single formula for both signs of `a`), with `|γ_k|² = 1 - 2λ|a|(1 - λ|a|)(1 - cos φ_k)`; hence
`|γ_k| ≤ 1` for every `k` exactly when `λ|a| ≤ 1`, the CFL condition
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, Exercise 13.6). -/
theorem exercise_13_6 {N : ℕ} [NeZero N] (hN : 2 ≤ N) {a lam : ℝ} (hlam : 0 ≤ lam) (k : Fin N) :
    FiniteDifference.amplificationFactor (Stencil.toPeriodic N (equation_13_41 a lam)) k
        = ((1 - lam * |a| * (1 - Real.cos (Hyperbolic.gridPhase N k)) : ℝ) : ℂ)
          - Complex.I * (lam * a) * (Real.sin (Hyperbolic.gridPhase N k) : ℂ) ∧
      ‖FiniteDifference.amplificationFactor (Stencil.toPeriodic N (equation_13_41 a lam)) k‖ ^ 2
        = 1 - 2 * (lam * |a|) * (1 - lam * |a|)
          * (1 - Real.cos (Hyperbolic.gridPhase N k)) ∧
      ((∀ k : Fin N, ‖FiniteDifference.amplificationFactor
          (Stencil.toPeriodic N (equation_13_41 a lam)) k‖ ≤ 1) ↔ lam * |a| ≤ 1) :=
  ⟨Hyperbolic.amplificationFactor_upwind a lam k,
    Hyperbolic.norm_amplificationFactor_upwind_sq a lam k,
    Hyperbolic.norm_amplificationFactor_upwind_le_one_iff hN hlam⟩

/-- **Under the CFL condition the upwind scheme is `ℓ²`-stable** on the periodic grid, by
Theorem 13.1 and Exercise 6 (Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.8.4). -/
theorem upwind_stable_l2 {N : ℕ} [NeZero N] (hN : 2 ≤ N) {a lam : ℝ} (hlam : 0 ≤ lam)
    (h : lam * |a| ≤ 1) (n : ℕ) (u : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanLin
        (FiniteDifference.periodicScheme (Stencil.toPeriodic N (equation_13_41 a lam)) ^ n) u‖
      ≤ ‖u‖ :=
  theorem_13_1 _ ((Hyperbolic.norm_amplificationFactor_upwind_le_one_iff hN hlam).2 h) n u

/-- **The Lax–Friedrichs amplification factor** `γ_k = cos φ_k - i λ a sin φ_k`, with
`|γ_k|² = cos² φ_k + (λ a)² sin² φ_k`; `|γ_k| ≤ 1` for every `k` exactly when `|λ a| ≤ 1`
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.8.4 and Figure 13.7). -/
theorem amplificationFactor_laxFriedrichs {N : ℕ} [NeZero N] (hN : 3 ≤ N) (a lam : ℝ)
    (k : Fin N) :
    FiniteDifference.amplificationFactor (Stencil.toPeriodic N (equation_13_39 a lam)) k
        = (Real.cos (Hyperbolic.gridPhase N k) : ℂ)
          - Complex.I * (lam * a) * (Real.sin (Hyperbolic.gridPhase N k) : ℂ) ∧
      ‖FiniteDifference.amplificationFactor (Stencil.toPeriodic N (equation_13_39 a lam)) k‖ ^ 2
        = Real.cos (Hyperbolic.gridPhase N k) ^ 2
          + (lam * a) ^ 2 * Real.sin (Hyperbolic.gridPhase N k) ^ 2 ∧
      ((∀ k : Fin N, ‖FiniteDifference.amplificationFactor
          (Stencil.toPeriodic N (equation_13_39 a lam)) k‖ ≤ 1) ↔ |lam * a| ≤ 1) :=
  ⟨Hyperbolic.amplificationFactor_laxFriedrichs a lam k,
    Hyperbolic.norm_amplificationFactor_laxFriedrichs_sq a lam k,
    Hyperbolic.norm_amplificationFactor_laxFriedrichs_le_one_iff hN a lam⟩

/-- **The Lax–Wendroff amplification factor** `γ_k = 1 - (λ a)²(1 - cos φ_k) - i λ a sin φ_k`,
with `|γ_k|² = 1 - (λ a)²(1 - (λ a)²)(1 - cos φ_k)²` (the book's
`1 - 4 (λ a)²(1 - (λ a)²) sin⁴(φ_k/2)`); `|γ_k| ≤ 1` for every `k` exactly when `|λ a| ≤ 1`
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.8.4 and Figure 13.7). -/
theorem amplificationFactor_laxWendroff {N : ℕ} [NeZero N] (hN : 2 ≤ N) (a lam : ℝ) (k : Fin N) :
    FiniteDifference.amplificationFactor (Stencil.toPeriodic N (equation_13_40 a lam)) k
        = ((1 - (lam * a) ^ 2 * (1 - Real.cos (Hyperbolic.gridPhase N k)) : ℝ) : ℂ)
          - Complex.I * (lam * a) * (Real.sin (Hyperbolic.gridPhase N k) : ℂ) ∧
      ‖FiniteDifference.amplificationFactor (Stencil.toPeriodic N (equation_13_40 a lam)) k‖ ^ 2
        = 1 - (lam * a) ^ 2 * (1 - (lam * a) ^ 2)
          * (1 - Real.cos (Hyperbolic.gridPhase N k)) ^ 2 ∧
      ((∀ k : Fin N, ‖FiniteDifference.amplificationFactor
          (Stencil.toPeriodic N (equation_13_40 a lam)) k‖ ≤ 1) ↔ |lam * a| ≤ 1) :=
  ⟨Hyperbolic.amplificationFactor_laxWendroff a lam k,
    Hyperbolic.norm_amplificationFactor_laxWendroff_sq a lam k,
    Hyperbolic.norm_amplificationFactor_laxWendroff_le_one_iff hN a lam⟩

/-- **Lax–Wendroff is stable under the CFL condition** (the book cites [QV94]): on the periodic
grid `|γ_k| ≤ 1` for every `k` when `|λ a| ≤ 1`, so Theorem 13.1 gives
`‖u^n‖_{Δ,2} ≤ ‖u^0‖_{Δ,2}`. -/
theorem laxWendroff_stable {N : ℕ} [NeZero N] (hN : 2 ≤ N) {a lam : ℝ} (h : |lam * a| ≤ 1)
    (n : ℕ) (u : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanLin
        (FiniteDifference.periodicScheme (Stencil.toPeriodic N (equation_13_40 a lam)) ^ n) u‖
      ≤ ‖u‖ :=
  theorem_13_1 _ ((Hyperbolic.norm_amplificationFactor_laxWendroff_le_one_iff hN a lam).2 h) n u

/-- **The backward Euler/centred amplification factor** `γ_k = 1/(1 + i λ a sin φ_k)`, of modulus
at most `1` for every `λ`, `a` and `k`: the periodic counterpart of Exercise 7
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.8.2 and Figure 13.7). -/
theorem amplificationFactor_backwardEulerCentred {N : ℕ} [NeZero N] (a lam : ℝ) (k : Fin N) :
    FiniteDifference.amplificationFactor₂
        (Stencil.toPeriodic N (Stencil.threePoint (-(lam * a / 2)) 1 (lam * a / 2)))
        (Stencil.toPeriodic N (Stencil.threePoint 0 1 0)) k
        = 1 / (1 + Complex.I * (lam * a) * (Real.sin (Hyperbolic.gridPhase N k) : ℂ)) ∧
      ‖FiniteDifference.amplificationFactor₂
        (Stencil.toPeriodic N (Stencil.threePoint (-(lam * a / 2)) 1 (lam * a / 2)))
        (Stencil.toPeriodic N (Stencil.threePoint 0 1 0)) k‖ ≤ 1 :=
  ⟨Hyperbolic.amplificationFactor₂_backwardEulerCentred a lam k,
    Hyperbolic.norm_amplificationFactor₂_backwardEulerCentred_le_one a lam k⟩

/-- **(13.53)**, the discrete maximum principle: under the CFL condition the upwind iterates stay
between the infimum and the supremum of the datum, so `‖u^n‖_{Δ,∞} ≤ ‖u^0‖_{Δ,∞}`
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, equation (13.53)). -/
theorem equation_13_53 {a lam : ℝ} (h0 : 0 ≤ lam * |a|) (h1 : lam * |a| ≤ 1) {u : ℤ → ℝ}
    (hba : BddAbove (range u)) (hbb : BddBelow (range u)) (n : ℕ) (j : ℤ) :
    ⨅ i, u i ≤ (Stencil.apply (equation_13_41 a lam))^[n] u j ∧
      (Stencil.apply (equation_13_41 a lam))^[n] u j ≤ ⨆ i, u i :=
  ⟨(Hyperbolic.upwind_isMonotone h0 h1).iInf_le_iterate_apply hbb n j,
    (Hyperbolic.upwind_isMonotone h0 h1).iterate_apply_le_iSup hba n j⟩

end QuarteroniSaccoSaleri.Chapter13
