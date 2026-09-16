import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz
import Numlib.Variational.EllipticInterval
import Numlib.Variational.FiniteElementInterval

/-!
# Advection–diffusion in one dimension, and its stabilized discretizations

The model problem `-ε u'' + β u' = 0` on `(0, 1)` with `u(0) = 0`, `u(1) = 1` and `ε, β > 0`
([quarteroni2000numerical] §12.5), in the regime `ε/β ≪ 1` where advection dominates diffusion,
together with the discretizations that cure the oscillations of the centred scheme.

## Main definitions

* `AdvectionDiffusion.globalPeclet β L ε = |β| L / (2 ε)` and
  `AdvectionDiffusion.localPeclet β h ε = |β| h / (2 ε)`, the global and local Péclet numbers
  ([quarteroni2000numerical] (12.71) and §12.5.1);
* `AdvectionDiffusion.exactSolution ε β x = (e^{βx/ε} - 1)/(e^{β/ε} - 1)`, the solution of the
  model problem;
* `AdvectionDiffusion.centredSolution n Pe i = (1 - ρ^i)/(1 - ρ^n)` with
  `ρ = AdvectionDiffusion.centredRatio Pe = (1 + Pe)/(1 - Pe)`, the solution of the centred
  difference equation (12.76);
* `AdvectionDiffusion.viscosityScheme ε β n φ u`, the centred scheme (12.79) with the numerical
  viscosity `ε_h = AdvectionDiffusion.viscosity ε β h φ = ε (1 + φ(Pe))` of (12.82), and
  `AdvectionDiffusion.upwindScheme`, the upwind scheme (12.78);
* `AdvectionDiffusion.bernoulliFn t = t/(e^t - 1)` (value `1` at `0`), the Bernoulli function, and
  the viscosity functions `AdvectionDiffusion.phiUpwind t = t` and
  `AdvectionDiffusion.phiSG t = t - 1 + B(2t)` of (12.83), the latter being the
  Scharfetter–Gummel (exponential fitting) choice;
* `AdvectionDiffusion.stabilizedPeclet φ Pe = Pe/(1 + φ(Pe))`, the Péclet number `Pe*` of the
  stabilized scheme (§12.5.2);
* `AdvectionDiffusion.stabilizedForm a b ε β h φ`, the stabilized bilinear form (12.84)
  `a_h(u, v) = ∫ (ε_h u' v' + β u' v)` on `H^1(a, b)`, an instance of
  `EllipticInterval.form` with the constant `L^∞` coefficients `ε_h`, `β`, `0`.

## Main statements

* `AdvectionDiffusion.exactSolution_solves` and `AdvectionDiffusion.exactSolution_unique`: the
  exact solution and its uniqueness among `C²` solutions.
* `AdvectionDiffusion.centredSolution_solves`, `centredSolution_unique`: the centred difference
  equation (12.76) has exactly one solution with the two boundary values, and it is the explicit
  one; `AdvectionDiffusion.centredSolution_oscillates`: **for `Pe > 1` its increments alternate
  in sign**, while `centredSolution_strictMono` gives monotonicity for `Pe < 1`.
* `AdvectionDiffusion.upwindScheme_iff_viscosityScheme`: **upwinding is centred differencing
  with the artificial viscosity** `ε (1 + Pe)` (12.78)–(12.81), and
  `viscosityScheme_eq_centredSolution` identifies the solution of the scheme with viscosity as
  the centred solution at the stabilized Péclet number `Pe*`.
* `AdvectionDiffusion.stabilizedPeclet_phiUpwind_lt_one` and
  `stabilizedPeclet_phiSG_eq_tanh`: `Pe* < 1` for the upwind and the Scharfetter–Gummel
  viscosities, for every mesh size; `AdvectionDiffusion.viscosityScheme_isMMatrix`: the matrix of
  the scheme is then an M-matrix, so the discrete maximum principle holds.
* `AdvectionDiffusion.sg_nodal_exact`: **the Scharfetter–Gummel scheme is nodally exact** for the
  model problem, for every mesh size.
* `AdvectionDiffusion.phiSG_asymptotics` and `phiSG_le_sq`: `φ^SG - φ^UP → -1` (so the two are
  asymptotically equal, `phiSG_div_phiUpwind_tendsto`) and `0 ≤ φ^SG(t) ≤ t²/3`, which is why the
  Scharfetter–Gummel viscosity is `O(h²)` where the upwind one is `O(h)`.
* `AdvectionDiffusion.stabilizedForm_self`, `stabilizedForm_isBoundedWith_seminorm` and
  `seminorm_sub_stabilized_le`: `a_h(v, v) = ε_h |v|²_{H^1}` on `H^1_0(a, b)`, the continuity
  constant `M_h = ε_h + |β| C_P`, and the error bound of [quarteroni2000numerical] (12.87)–(12.89)
  in Strang form.
* `AdvectionDiffusion.rep_eq_exactSolution_of_galerkin_sg` and
  `seminorm_sub_stabilized_le_sg`: **the `P_1` Scharfetter–Gummel finite element solution of the
  model problem is nodally exact**, hence equal to the piecewise linear interpolant of the exact
  solution, so its error is the interpolation error and (12.85) holds with the constant `1`.
* `AdvectionDiffusion.seminorm_sub_stabilized_le_upwind` and
  `seminorm_sub_stabilized_le_sg_quadratic`: Theorem 12.4's two general clauses, the first-order
  rate (12.85) of the upwind method with `P_1` elements and the second-order rate (12.86) of the
  Scharfetter–Gummel method with `P_2` elements, both with an explicit constant.

## Implementation notes

Grid functions are indexed by `ℕ`, not by `Fin (n + 1)`: the schemes are three-term relations
whose index arithmetic is painless on `ℕ` and painful on `Fin`, and a grid function is only ever
constrained at the indices `0, …, n`. The difference equations are stated in the shifted form
`i, i + 1, i + 2` for the same reason (no truncated subtraction).

The bilinear form is not defined again here: `EllipticInterval.form` already takes `L^∞`
coefficients, and the stabilized form is that form at the constant coefficients `ε_h`, `β`, `0`
(`EllipticInterval.constLinf` packages a constant as an element of `L^∞(a, b)`). Everything
about it therefore inherits the conventions of `Numlib/Variational/EllipticInterval.lean`: the
space is `SobolevInterval 1 a b`, the Dirichlet test space is `SobolevIntervalZero a b`, and the
discrete problem is `IsGalerkinSolution` in a subspace `K ≤ H^1_0(a, b)` — no finite element
space is needed to state or to prove the error bound.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Matrix Topology

noncomputable section

namespace AdvectionDiffusion

/-! ### The Péclet numbers -/

/-- **The global Péclet number** `Pe_gl = |β| L / (2 ε)` of [quarteroni2000numerical] (12.71),
measuring the dominance of the advective term `β u'` over the diffusive term `-ε u''` on a domain
of size `L`. -/
def globalPeclet (β L ε : ℝ) : ℝ := |β| * L / (2 * ε)

/-- **The local (mesh) Péclet number** `Pe = |β| h / (2 ε)` of [quarteroni2000numerical] §12.5.1:
the global Péclet number of a single mesh panel of width `h`. -/
def localPeclet (β h ε : ℝ) : ℝ := |β| * h / (2 * ε)

/-- On the unit interval the local Péclet number is `h` times the global one. -/
theorem localPeclet_eq_globalPeclet_mul (β h ε : ℝ) :
    localPeclet β h ε = globalPeclet β 1 ε * h := by
  rw [localPeclet, globalPeclet]
  ring

/-- The local Péclet number is nonnegative for a nonnegative mesh size and a positive
diffusion. -/
theorem localPeclet_nonneg {β h ε : ℝ} (hh : 0 ≤ h) (hε : 0 ≤ ε) : 0 ≤ localPeclet β h ε := by
  unfold localPeclet
  positivity

/-- The local Péclet number is positive when the advection is nonzero. -/
theorem localPeclet_pos {β h ε : ℝ} (hβ : β ≠ 0) (hh : 0 < h) (hε : 0 < ε) :
    0 < localPeclet β h ε := by
  unfold localPeclet
  have : 0 < |β| := abs_pos.2 hβ
  positivity

/-- For a positive advection coefficient, `|β| h = 2 ε Pe`. -/
theorem mul_localPeclet {β h ε : ℝ} (hε : ε ≠ 0) : 2 * ε * localPeclet β h ε = |β| * h := by
  rw [localPeclet]
  field_simp

/-! ### The exact solution and its boundary layer -/

/-- **The exact solution of the model problem** `-ε u'' + β u' = 0`, `u(0) = 0`, `u(1) = 1`
([quarteroni2000numerical] §12.5): `u(x) = (e^{βx/ε} - 1)/(e^{β/ε} - 1)`.  For `β/ε = 0` the
denominator vanishes and the definition returns the junk value `0`; every statement about it
assumes `ε, β > 0`. -/
def exactSolution (ε β x : ℝ) : ℝ := (Real.exp (β * x / ε) - 1) / (Real.exp (β / ε) - 1)

/-- The exact solution is differentiable, with `u'(x) = (β/ε) e^{βx/ε}/(e^{β/ε} - 1)`. -/
theorem hasDerivAt_exactSolution (ε β x : ℝ) :
    HasDerivAt (exactSolution ε β)
      (β / ε * Real.exp (β * x / ε) / (Real.exp (β / ε) - 1)) x := by
  have h1 : HasDerivAt (fun t : ℝ => β * t / ε) (β / ε) x := by
    simpa using ((hasDerivAt_id x).const_mul β).div_const ε
  have h2 := (((Real.hasDerivAt_exp (β * x / ε)).comp x h1).sub_const 1).div_const
    (Real.exp (β / ε) - 1)
  refine h2.congr_deriv ?_
  ring

/-- The derivative of the exact solution. -/
theorem deriv_exactSolution (ε β x : ℝ) :
    deriv (exactSolution ε β) x = β / ε * Real.exp (β * x / ε) / (Real.exp (β / ε) - 1) :=
  (hasDerivAt_exactSolution ε β x).deriv

/-- The second derivative of the exact solution. -/
theorem deriv_deriv_exactSolution (ε β x : ℝ) :
    deriv (deriv (exactSolution ε β)) x
      = (β / ε) ^ 2 * Real.exp (β * x / ε) / (Real.exp (β / ε) - 1) := by
  have he : deriv (exactSolution ε β)
      = fun t => β / ε * Real.exp (β * t / ε) / (Real.exp (β / ε) - 1) :=
    funext (deriv_exactSolution ε β)
  rw [he]
  have h1 : HasDerivAt (fun t : ℝ => β * t / ε) (β / ε) x := by
    simpa using ((hasDerivAt_id x).const_mul β).div_const ε
  have h2 := ((((Real.hasDerivAt_exp (β * x / ε)).comp x h1).const_mul (β / ε)).div_const
    (Real.exp (β / ε) - 1))
  refine h2.deriv.trans ?_
  ring

/-- The exact solution vanishes at the left endpoint. -/
@[simp]
theorem exactSolution_zero (ε β : ℝ) : exactSolution ε β 0 = 0 := by
  simp [exactSolution]

/-- The exact solution takes the value `1` at the right endpoint, provided `β/ε ≠ 0`. -/
@[simp]
theorem exactSolution_one {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) : exactSolution ε β 1 = 1 := by
  have hk : (0 : ℝ) < β / ε := div_pos hβ hε
  have hne : Real.exp (β / ε) - 1 ≠ 0 := by
    have : (1 : ℝ) < Real.exp (β / ε) := Real.one_lt_exp_iff.2 hk
    linarith
  rw [exactSolution, mul_one]
  field_simp

/-- **The exact solution solves the model problem** `-ε u'' + β u' = 0`
([quarteroni2000numerical] §12.5): the characteristic roots are `0` and `β/ε`. -/
theorem exactSolution_solves {ε : ℝ} (hε : ε ≠ 0) (β x : ℝ) :
    -ε * deriv (deriv (exactSolution ε β)) x + β * deriv (exactSolution ε β) x = 0 := by
  rw [deriv_deriv_exactSolution, deriv_exactSolution]
  field_simp
  ring

/-- **Uniqueness of the solution of the model problem**: a twice continuously differentiable
`u : ℝ → ℝ` with `-ε u'' + β u' = 0`, `u(0) = 0` and `u(1) = 1` is the exact solution.  Writing
`k = β/ε`, the equation says `u'' = k u'`, so `u' - k u` is constant, say `c`, and then
`(u + c/k) e^{-kx}` is constant as well; the two boundary values fix the two constants.  The
book states the uniqueness on `[0, 1]`; the statement here is on `ℝ`, which is where the
hypotheses of Mathlib's `is_const_of_deriv_eq_zero` live. -/
theorem exactSolution_unique {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (hode : ∀ x, -ε * deriv (deriv u) x + β * deriv u x = 0)
    (h0 : u 0 = 0) (h1 : u 1 = 1) : u = exactSolution ε β := by
  set k : ℝ := β / ε with hkdef
  have hk : 0 < k := div_pos hβ hε
  have hkne : k ≠ 0 := hk.ne'
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hu'd : Differentiable ℝ (deriv u) := hu.differentiable_deriv_two
  -- `u'' = k u'`
  have hode' : ∀ x, deriv (deriv u) x = k * deriv u x := fun x => by
    have := hode x
    rw [hkdef]
    field_simp at this ⊢
    linarith
  -- `u' - k u` is constant
  have hconst : ∀ x, deriv u x - k * u x = deriv u 0 := by
    have hd : Differentiable ℝ fun t => deriv u t - k * u t := hu'd.sub (hud.const_mul k)
    have hzero : ∀ x, deriv (fun t => deriv u t - k * u t) x = 0 := fun x => by
      rw [deriv_fun_sub (hu'd x) ((hud x).const_mul k), deriv_const_mul k (hud x), hode' x]
      ring
    intro x
    have := is_const_of_deriv_eq_zero hd hzero x 0
    rw [h0, mul_zero, sub_zero] at this
    exact this
  set d : ℝ := deriv u 0 / k with hddef
  have hcd : ∀ x, deriv u x - k * u x = k * d := fun x => by
    rw [hddef]
    field_simp
    exact hconst x
  -- `(u + d) e^{-kx}` is constant
  have hψd : ∀ x, HasDerivAt (fun t => (u t + d) * Real.exp (-k * t)) 0 x := fun x => by
    have hx1 : HasDerivAt (fun t : ℝ => u t + d) (deriv u x) x := ((hud x).hasDerivAt).add_const _
    have hmul : HasDerivAt (fun t : ℝ => -k * t) (-k) x := by
      simpa using (hasDerivAt_id x).const_mul (-k)
    have hx2 : HasDerivAt (fun t : ℝ => Real.exp (-k * t)) (Real.exp (-k * x) * -k) x := hmul.exp
    have h := hx1.mul hx2
    have hcancel : deriv u x * Real.exp (-k * x) + (u x + d) * (Real.exp (-k * x) * -k) = 0 := by
      have := hcd x
      nlinarith [Real.exp_pos (-k * x)]
    rwa [hcancel] at h
  have hψ : ∀ x, (u x + d) * Real.exp (-k * x) = d := fun x => by
    have := is_const_of_deriv_eq_zero (fun t => (hψd t).differentiableAt)
      (fun t => (hψd t).deriv) x 0
    simpa [h0] using this
  -- solve for `u`
  have hform : ∀ x, u x = d * (Real.exp (k * x) - 1) := fun x => by
    have h2 : Real.exp (-k * x) * Real.exp (k * x) = 1 := by
      rw [← Real.exp_add]
      norm_num
    have h3 : u x + d = d * Real.exp (k * x) :=
      calc u x + d = (u x + d) * (Real.exp (-k * x) * Real.exp (k * x)) := by rw [h2, mul_one]
        _ = (u x + d) * Real.exp (-k * x) * Real.exp (k * x) := by ring
        _ = d * Real.exp (k * x) := by rw [hψ x]
    linarith
  have hden : Real.exp k - 1 ≠ 0 := by
    have : (1 : ℝ) < Real.exp k := Real.one_lt_exp_iff.2 hk
    linarith
  have hd : d = 1 / (Real.exp k - 1) := by
    have h4 := hform 1
    rw [h1, mul_one] at h4
    field_simp
    linarith
  funext x
  have hkx : β * x / ε = k * x := by rw [hkdef]; ring
  rw [hform x, hd, exactSolution, hkx, hkdef]
  field_simp

/-! ### The centred difference equation and its explicit solution -/

/-- The amplification ratio `ρ = (1 + Pe)/(1 - Pe)` of the centred difference equation (12.76):
the nontrivial root of its characteristic equation `(Pe - 1) ρ² + 2 ρ - (Pe + 1) = 0`, the other
root being `1` ([quarteroni2000numerical] §12.5.1). -/
def centredRatio (Pe : ℝ) : ℝ := (1 + Pe) / (1 - Pe)

/-- The defining relation `(1 - Pe) ρ = 1 + Pe` of the amplification ratio. -/
theorem one_sub_mul_centredRatio {Pe : ℝ} (hPe : Pe ≠ 1) :
    (1 - Pe) * centredRatio Pe = 1 + Pe := by
  rw [centredRatio]
  field_simp

/-- The amplification ratio is a root of the characteristic equation of (12.76). -/
theorem centredRatio_root {Pe : ℝ} (hPe : Pe ≠ 1) :
    (Pe - 1) * centredRatio Pe ^ 2 + 2 * centredRatio Pe - (Pe + 1) = 0 := by
  have h := one_sub_mul_centredRatio hPe
  linear_combination (1 - centredRatio Pe) * h

/-- For a positive local Péclet number other than `1` the amplification ratio has modulus greater
than `1`: below `1` it is `(1 + Pe)/(1 - Pe) > 1`, above `1` it is negative of modulus
`(1 + Pe)/(Pe - 1) > 1`. -/
theorem one_lt_abs_centredRatio {Pe : ℝ} (hPe : 0 < Pe) (hPe1 : Pe ≠ 1) :
    1 < |centredRatio Pe| := by
  have hne : (1 : ℝ) - Pe ≠ 0 := sub_ne_zero.2 fun h => hPe1 h.symm
  rw [centredRatio, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + Pe),
    lt_div_iff₀ (abs_pos.2 hne)]
  rcases lt_or_gt_of_ne hPe1 with h | h
  · rw [abs_of_pos (by linarith)]; linarith
  · rw [abs_of_neg (by linarith)]; linarith

/-- The amplification ratio is negative when the local Péclet number exceeds `1`: this is the
negative base whose powers make the discrete solution oscillate. -/
theorem centredRatio_neg {Pe : ℝ} (hPe : 1 < Pe) : centredRatio Pe < 0 :=
  div_neg_of_pos_of_neg (by linarith) (by linarith)

/-- The amplification ratio exceeds `1` when the local Péclet number is below `1`. -/
theorem one_lt_centredRatio {Pe : ℝ} (hPe : 0 < Pe) (hPe1 : Pe < 1) : 1 < centredRatio Pe := by
  rw [centredRatio, lt_div_iff₀ (by linarith)]
  linarith

/-- No positive power of the amplification ratio is `1`, so the denominator of the explicit
solution of (12.76) never vanishes. -/
theorem centredRatio_pow_ne_one {Pe : ℝ} (hPe : 0 < Pe) (hPe1 : Pe ≠ 1) {n : ℕ} (hn : n ≠ 0) :
    centredRatio Pe ^ n ≠ 1 := by
  intro h
  have h1 : (1 : ℝ) < |centredRatio Pe| ^ n := one_lt_pow₀ (one_lt_abs_centredRatio hPe hPe1) hn
  rw [← abs_pow, h, abs_one] at h1
  exact lt_irrefl 1 h1

/-- **The explicit solution of the centred difference equation** (12.76) on `n` panels with the
boundary values `u_0 = 0`, `u_n = 1` ([quarteroni2000numerical] §12.5.1):
`u_i = (1 - ρ^i)/(1 - ρ^n)` with `ρ = AdvectionDiffusion.centredRatio Pe`. -/
def centredSolution (n : ℕ) (Pe : ℝ) (i : ℕ) : ℝ :=
  (1 - centredRatio Pe ^ i) / (1 - centredRatio Pe ^ n)

/-- The discrete solution vanishes at the left endpoint. -/
@[simp]
theorem centredSolution_zero (n : ℕ) (Pe : ℝ) : centredSolution n Pe 0 = 0 := by
  simp [centredSolution]

/-- The discrete solution takes the value `1` at the right endpoint. -/
@[simp]
theorem centredSolution_self {Pe : ℝ} (hPe : 0 < Pe) (hPe1 : Pe ≠ 1) {n : ℕ} (hn : n ≠ 0) :
    centredSolution n Pe n = 1 :=
  div_self (sub_ne_zero.2 fun h => centredRatio_pow_ne_one hPe hPe1 hn h.symm)

/-- **The explicit solution solves the centred difference equation** (12.76),
`(Pe - 1) u_{i+1} + 2 u_i - (Pe + 1) u_{i-1} = 0`, written here in the shifted form at the indices
`i`, `i + 1`, `i + 2`. -/
theorem centredSolution_solves {Pe : ℝ} (hPe : Pe ≠ 1) (n i : ℕ) :
    (Pe - 1) * centredSolution n Pe (i + 2) + 2 * centredSolution n Pe (i + 1)
      - (Pe + 1) * centredSolution n Pe i = 0 := by
  set ρ := centredRatio Pe with hρ
  set D := 1 - ρ ^ n with hD
  have key : (Pe - 1) * (1 - ρ ^ (i + 2)) + 2 * (1 - ρ ^ (i + 1)) - (Pe + 1) * (1 - ρ ^ i) = 0 := by
    linear_combination (-(ρ ^ i)) * centredRatio_root hPe
  have e : (Pe - 1) * ((1 - ρ ^ (i + 2)) / D) + 2 * ((1 - ρ ^ (i + 1)) / D)
      - (Pe + 1) * ((1 - ρ ^ i) / D)
      = ((Pe - 1) * (1 - ρ ^ (i + 2)) + 2 * (1 - ρ ^ (i + 1)) - (Pe + 1) * (1 - ρ ^ i)) / D := by
    ring
  simp only [centredSolution, ← hρ, ← hD]
  rw [e, key, zero_div]

/-- The increments of the discrete solution are the powers of the amplification ratio times the
first one: `u_{i+1} - u_i = ρ^i (u_1 - u_0)`. -/
theorem centredSolution_sub_eq (n : ℕ) (Pe : ℝ) (i : ℕ) :
    centredSolution n Pe (i + 1) - centredSolution n Pe i
      = centredRatio Pe ^ i * (centredSolution n Pe 1 - centredSolution n Pe 0) := by
  simp only [centredSolution]
  ring

/-- **The centred scheme oscillates when the local Péclet number exceeds `1`**
([quarteroni2000numerical] §12.5.1): the increments of the discrete solution alternate in sign,
because `ρ^i` does. -/
theorem centredSolution_oscillates {Pe : ℝ} (hPe : 1 < Pe) {n : ℕ} (hn : n ≠ 0) (i : ℕ) :
    0 < (-1) ^ i * (centredSolution n Pe (i + 1) - centredSolution n Pe i)
      * (centredSolution n Pe 1 - centredSolution n Pe 0) := by
  have hρ : centredRatio Pe < 0 := centredRatio_neg hPe
  have hne : centredSolution n Pe 1 - centredSolution n Pe 0 ≠ 0 := by
    rw [centredSolution_zero, sub_zero, centredSolution, pow_one]
    refine div_ne_zero (sub_ne_zero.2 fun h => ?_)
      (sub_ne_zero.2 fun h => centredRatio_pow_ne_one (by linarith) (by linarith) hn h.symm)
    linarith
  have e : (-1 : ℝ) ^ i * (centredSolution n Pe (i + 1) - centredSolution n Pe i)
      * (centredSolution n Pe 1 - centredSolution n Pe 0)
      = (-centredRatio Pe) ^ i * (centredSolution n Pe 1 - centredSolution n Pe 0) ^ 2 := by
    rw [centredSolution_sub_eq, neg_pow]
    ring
  rw [e]
  have h1 : 0 < (-centredRatio Pe) ^ i := pow_pos (by linarith) i
  have h2 : 0 < (centredSolution n Pe 1 - centredSolution n Pe 0) ^ 2 := by positivity
  positivity

/-- **The centred scheme is monotone when the local Péclet number is below `1`**, matching the
monotonicity of the exact solution. -/
theorem centredSolution_strictMono {Pe : ℝ} (hPe : 0 < Pe) (hPe1 : Pe < 1) {n : ℕ} (hn : n ≠ 0) :
    StrictMono (centredSolution n Pe) := by
  have hρ : 1 < centredRatio Pe := one_lt_centredRatio hPe hPe1
  refine strictMono_nat_of_lt_succ fun i => ?_
  have hfirst : 0 < centredSolution n Pe 1 - centredSolution n Pe 0 := by
    rw [centredSolution_zero, sub_zero, centredSolution, pow_one]
    refine div_pos_of_neg_of_neg (by linarith) (sub_neg.2 ?_)
    exact one_lt_pow₀ hρ hn
  have := centredSolution_sub_eq n Pe i
  nlinarith [pow_pos (show (0 : ℝ) < centredRatio Pe by linarith) i]

/-- A solution of the centred difference equation (12.76) with `u_0 = 0` is determined by `u_1`:
it is `u_1 ∑_{j < i} ρ^j`.  This is the uniqueness half of [quarteroni2000numerical] §12.5.1, and
the only place where `Pe ≠ 1` — so that the recurrence can be solved for `u_{i+2}` — is used. -/
theorem eq_mul_geom_sum_of_centredRecurrence {Pe : ℝ} (hPe : Pe ≠ 1) {n : ℕ} {u : ℕ → ℝ}
    (h0 : u 0 = 0)
    (hrec : ∀ i, i + 2 ≤ n → (Pe - 1) * u (i + 2) + 2 * u (i + 1) - (Pe + 1) * u i = 0) :
    ∀ i ≤ n, u i = u 1 * ∑ j ∈ Finset.range i, centredRatio Pe ^ j := by
  have hPe' : Pe - 1 ≠ 0 := sub_ne_zero.2 hPe
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i with
    | 0 => intro _; simpa using h0
    | 1 => intro _; simp
    | (k + 2) =>
      intro hk
      have h1 := ih k (by omega) (by omega)
      have h2 := ih (k + 1) (by omega) (by omega)
      have h3 := hrec k (by omega)
      have hlin := one_sub_mul_centredRatio hPe
      rw [h1, h2, Finset.sum_range_succ] at h3
      have key : (Pe - 1) * (u (k + 2)
          - u 1 * ((∑ j ∈ Finset.range k, centredRatio Pe ^ j) + centredRatio Pe ^ k
            + centredRatio Pe ^ (k + 1))) = 0 := by
        linear_combination h3 + (u 1 * centredRatio Pe ^ k) * hlin
      have hX := (mul_eq_zero.1 key).resolve_left hPe'
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linear_combination hX

/-- **The centred difference equation has exactly one solution with the two boundary values**, and
it is `AdvectionDiffusion.centredSolution` ([quarteroni2000numerical] §12.5.1). -/
theorem centredSolution_unique {Pe : ℝ} (hPe : 0 < Pe) (hPe1 : Pe ≠ 1) {n : ℕ} (hn : n ≠ 0)
    {u : ℕ → ℝ} (h0 : u 0 = 0) (hlast : u n = 1)
    (hrec : ∀ i, i + 2 ≤ n → (Pe - 1) * u (i + 2) + 2 * u (i + 1) - (Pe + 1) * u i = 0)
    {i : ℕ} (hi : i ≤ n) : u i = centredSolution n Pe i := by
  set v : ℕ → ℝ := fun j => u j - centredSolution n Pe j with hv
  have hv0 : v 0 = 0 := by simp [hv, h0]
  have hvrec : ∀ j, j + 2 ≤ n → (Pe - 1) * v (j + 2) + 2 * v (j + 1) - (Pe + 1) * v j = 0 := by
    intro j hj
    simp only [hv]
    linarith [centredSolution_solves hPe1 n j, hrec j hj]
  have hgeom := eq_mul_geom_sum_of_centredRecurrence hPe1 hv0 hvrec
  have hvn : v n = 0 := by simp [hv, hlast, centredSolution_self hPe hPe1 hn]
  have hne : centredRatio Pe - 1 ≠ 0 := by
    intro h
    exact centredRatio_pow_ne_one hPe hPe1 hn (by rw [show centredRatio Pe = 1 by linarith,
      one_pow])
  have hsum : ∑ j ∈ Finset.range n, centredRatio Pe ^ j ≠ 0 := by
    rw [geom_sum_eq (fun h => hne (by rw [h]; ring))]
    exact div_ne_zero (sub_ne_zero.2 fun h => centredRatio_pow_ne_one hPe hPe1 hn h) hne
  have hv1 : v 1 = 0 := by
    have hvv := hgeom n le_rfl
    rw [hvn] at hvv
    exact (mul_eq_zero.1 hvv.symm).resolve_right hsum
  have hfin := hgeom i hi
  rw [hv1, zero_mul] at hfin
  simp only [hv] at hfin
  linarith

/-! ### The Bernoulli function and the viscosity functions -/

/-- **The Bernoulli function** `B(t) = t/(e^t - 1)`, extended by `B(0) = 1`
([quarteroni2000numerical] (12.83)).  Mathlib carries the Bernoulli *numbers*, not this
function. -/
def bernoulliFn (t : ℝ) : ℝ := if t = 0 then 1 else t / (Real.exp t - 1)

/-- The Bernoulli function takes the value `1` at the origin, the limit of `t/(e^t - 1)`. -/
@[simp]
theorem bernoulliFn_zero : bernoulliFn 0 = 1 := by simp [bernoulliFn]

/-- Away from the origin the Bernoulli function is the quotient it is named for. -/
theorem bernoulliFn_of_ne_zero {t : ℝ} (ht : t ≠ 0) : bernoulliFn t = t / (Real.exp t - 1) := by
  simp [bernoulliFn, ht]

/-- `e^t - 1` vanishes only at the origin. -/
theorem exp_sub_one_ne_zero {t : ℝ} (ht : t ≠ 0) : Real.exp t - 1 ≠ 0 :=
  sub_ne_zero.2 fun h => ht ((Real.exp_eq_one_iff t).1 h)

/-- The reflection formula `B(-t) = t + B(t)`, the identity behind
[quarteroni2000numerical] Exercise 12.13. -/
theorem bernoulliFn_neg (t : ℝ) : bernoulliFn (-t) = t + bernoulliFn t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · have h1 : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
    have h2 := exp_sub_one_ne_zero ht
    have h3 : (1 : ℝ) - Real.exp t ≠ 0 := fun h => h2 (by linarith)
    rw [bernoulliFn_of_ne_zero (neg_ne_zero.2 ht), bernoulliFn_of_ne_zero ht, Real.exp_neg]
    field_simp
    ring

/-- The Bernoulli function is positive. -/
theorem bernoulliFn_pos (t : ℝ) : 0 < bernoulliFn t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [bernoulliFn_of_ne_zero ht.ne]
    exact div_pos_of_neg_of_neg ht (by
      have : Real.exp t < 1 := Real.exp_lt_one_iff.2 ht
      linarith)
  · simp
  · rw [bernoulliFn_of_ne_zero ht.ne']
    exact div_pos ht (by have : (1 : ℝ) < Real.exp t := Real.one_lt_exp_iff.2 ht; linarith)

/-- The Bernoulli function is at most `1` on `[0, ∞)`, since `t + 1 ≤ e^t`. -/
theorem bernoulliFn_le_one {t : ℝ} (ht : 0 ≤ t) : bernoulliFn t ≤ 1 := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · simp
  · rw [bernoulliFn_of_ne_zero ht'.ne', div_le_one (by
      have : (1 : ℝ) < Real.exp t := Real.one_lt_exp_iff.2 ht'; linarith)]
    linarith [Real.add_one_le_exp t]

/-- The Bernoulli function is continuous, the value `1` at the origin being the limit of
`t/(e^t - 1)`: the reciprocal of the difference quotient of `exp` at `0`. -/
theorem continuous_bernoulliFn : Continuous bernoulliFn := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  rcases eq_or_ne t 0 with rfl | ht
  · have hslope : Tendsto (slope Real.exp 0) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
      simpa using hasDerivAt_iff_tendsto_slope.1 (Real.hasDerivAt_exp 0)
    have hinv : Tendsto (fun t : ℝ => (slope Real.exp 0 t)⁻¹) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
      simpa using hslope.inv₀ one_ne_zero
    have heq : ∀ t : ℝ, t ≠ 0 → (slope Real.exp 0 t)⁻¹ = bernoulliFn t := by
      intro t ht
      rw [slope_def_field, Real.exp_zero, sub_zero, inv_div, bernoulliFn_of_ne_zero ht]
    have hpunct : Tendsto bernoulliFn (𝓝[≠] (0 : ℝ)) (𝓝 (bernoulliFn 0)) := by
      rw [bernoulliFn_zero]
      exact hinv.congr' (eventually_nhdsWithin_of_forall fun t ht => heq t ht)
    exact continuousAt_iff_punctured_nhds.2 hpunct
  · have hc : ContinuousAt (fun s : ℝ => s / (Real.exp s - 1)) t :=
      (continuousAt_id).div (Real.continuous_exp.continuousAt.sub continuousAt_const)
        (exp_sub_one_ne_zero ht)
    refine hc.congr ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using ht)] with s hs
    exact (bernoulliFn_of_ne_zero (by simpa using hs)).symm

/-- **The upwind viscosity function** `φ^UP(t) = t` ([quarteroni2000numerical] §12.5.2). -/
def phiUpwind (t : ℝ) : ℝ := t

/-- **The Scharfetter–Gummel (exponential fitting) viscosity function**
`φ^SG(t) = t - 1 + B(2t)` ([quarteroni2000numerical] (12.83), [SG69]). -/
def phiSG (t : ℝ) : ℝ := t - 1 + bernoulliFn (2 * t)

/-- The Scharfetter–Gummel viscosity function vanishes at the origin, as (12.82) requires of
every viscosity function. -/
@[simp]
theorem phiSG_zero : phiSG 0 = 0 := by simp [phiSG]

/-- The relation `(1 + φ^SG(t))(e^{2t} - 1) = t (e^{2t} + 1)`, from which the closed forms of
`1 + φ^SG` and of the stabilized Péclet number follow. -/
theorem one_add_phiSG_mul {t : ℝ} (ht : t ≠ 0) :
    (1 + phiSG t) * (Real.exp (2 * t) - 1) = t * (Real.exp (2 * t) + 1) := by
  have h2 : (2 : ℝ) * t ≠ 0 := by simpa using ht
  have hE : Real.exp (2 * t) - 1 ≠ 0 := exp_sub_one_ne_zero h2
  have e : (1 + (t - 1 + 2 * t / (Real.exp (2 * t) - 1))) * (Real.exp (2 * t) - 1)
      = t * (Real.exp (2 * t) - 1) + 2 * t / (Real.exp (2 * t) - 1) * (Real.exp (2 * t) - 1) := by
    ring
  rw [phiSG, bernoulliFn_of_ne_zero h2, e, div_mul_cancel₀ _ hE]
  ring

/-- `1 + φ^SG(t) = t coth t`, the closed form of the Scharfetter–Gummel viscosity. -/
theorem one_add_phiSG {t : ℝ} (ht : t ≠ 0) :
    1 + phiSG t = t * Real.cosh t / Real.sinh t := by
  have h2 : (2 : ℝ) * t ≠ 0 := by simpa using ht
  have hE : Real.exp (2 * t) - 1 ≠ 0 := exp_sub_one_ne_zero h2
  have hs : Real.sinh t ≠ 0 := Real.sinh_ne_zero.2 ht
  have hexp : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hEE : Real.exp (2 * t) = Real.exp t * Real.exp t := by
    rw [← Real.exp_add]
    ring_nf
  have hcs : t * Real.cosh t / Real.sinh t
      = t * (Real.exp (2 * t) + 1) / (Real.exp (2 * t) - 1) := by
    rw [div_eq_div_iff hs hE, Real.sinh_eq, Real.cosh_eq, Real.exp_neg, hEE]
    field_simp
  rw [hcs, eq_div_iff hE]
  exact one_add_phiSG_mul ht

/-- `φ^SG(t) = t coth t - 1` ([quarteroni2000numerical] Remark 12.6). -/
theorem phiSG_eq {t : ℝ} (ht : t ≠ 0) : phiSG t = t * Real.cosh t / Real.sinh t - 1 := by
  have := one_add_phiSG ht
  linarith

/-- `t cosh t - sinh t` is nondecreasing: its derivative is `t sinh t ≥ 0`. -/
theorem monotone_mul_cosh_sub_sinh :
    Monotone fun t : ℝ => t * Real.cosh t - Real.sinh t := by
  refine monotone_of_deriv_nonneg
    ((differentiable_id.mul Real.differentiable_cosh).sub Real.differentiable_sinh) fun x => ?_
  have h : HasDerivAt (fun t : ℝ => t * Real.cosh t - Real.sinh t) (x * Real.sinh x) x := by
    have h1 : HasDerivAt (fun t : ℝ => t * Real.cosh t) (1 * Real.cosh x + x * Real.sinh x) x :=
      (hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)
    have h2 := h1.sub (Real.hasDerivAt_sinh x)
    refine h2.congr_deriv ?_
    ring
  rw [h.deriv]
  rcases le_total 0 x with hx | hx
  · exact mul_nonneg hx (Real.sinh_nonneg_iff.2 hx)
  · have := Real.sinh_nonpos_iff.2 hx
    nlinarith

/-- `sinh t ≤ t cosh t` for `t ≥ 0`, with the reverse inequality for `t ≤ 0`. -/
theorem sinh_le_mul_cosh {t : ℝ} (ht : 0 ≤ t) : Real.sinh t ≤ t * Real.cosh t := by
  have := monotone_mul_cosh_sub_sinh ht
  simpa using this

/-- `(t²/3 + 1) sinh t - t cosh t` is nondecreasing: its derivative is
`(t/3)(t cosh t - sinh t) ≥ 0`. -/
theorem monotone_sq_mul_sinh_sub :
    Monotone fun t : ℝ => (t ^ 2 / 3 + 1) * Real.sinh t - t * Real.cosh t := by
  refine monotone_of_deriv_nonneg ((((differentiable_id.pow 2).div_const 3).add_const
    1).mul Real.differentiable_sinh |>.sub (differentiable_id.mul Real.differentiable_cosh))
    fun x => ?_
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 / 3 + 1) (2 * x / 3) x := by
    simpa using ((hasDerivAt_pow 2 x).div_const 3).add_const 1
  have ha : HasDerivAt (fun t : ℝ => (t ^ 2 / 3 + 1) * Real.sinh t)
      (2 * x / 3 * Real.sinh x + (x ^ 2 / 3 + 1) * Real.cosh x) x :=
    h1.mul (Real.hasDerivAt_sinh x)
  have hb : HasDerivAt (fun t : ℝ => t * Real.cosh t) (1 * Real.cosh x + x * Real.sinh x) x :=
    (hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)
  have h : HasDerivAt (fun t : ℝ => (t ^ 2 / 3 + 1) * Real.sinh t - t * Real.cosh t)
      (x / 3 * (x * Real.cosh x - Real.sinh x)) x := by
    refine (ha.sub hb).congr_deriv ?_
    ring
  rw [h.deriv]
  rcases le_total 0 x with hx | hx
  · have hk : (0 : ℝ) ≤ x * Real.cosh x - Real.sinh x := by
      simpa using monotone_mul_cosh_sub_sinh hx
    positivity
  · have hk : x * Real.cosh x - Real.sinh x ≤ 0 := by
      simpa using monotone_mul_cosh_sub_sinh hx
    nlinarith

/-- The Scharfetter–Gummel viscosity function is nonnegative on `[0, ∞)`. -/
theorem phiSG_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ phiSG t := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · simp
  · rw [phiSG_eq ht'.ne', sub_nonneg, le_div_iff₀ (Real.sinh_pos_iff.2 ht')]
    simpa using sinh_le_mul_cosh ht

/-- **The Scharfetter–Gummel viscosity is quadratic in the Péclet number**:
`0 ≤ φ^SG(t) ≤ t²/3` for `t ≥ 0`, which is [quarteroni2000numerical] Remark 12.6's
`φ^SG = O(h²)` (against `φ^UP(Pe) = Pe = O(h)`), with the explicit constant.  The inequality is
`t cosh t ≤ (t²/3 + 1) sinh t`, a consequence of `AdvectionDiffusion.monotone_sq_mul_sinh_sub`. -/
theorem phiSG_le_sq {t : ℝ} (ht : 0 ≤ t) : phiSG t ≤ t ^ 2 / 3 := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · simp
  · rw [phiSG_eq ht'.ne', sub_le_iff_le_add, div_le_iff₀ (Real.sinh_pos_iff.2 ht')]
    have := monotone_sq_mul_sinh_sub ht
    simp only [Real.sinh_zero, Real.cosh_zero] at this
    nlinarith [this]

/-- **`φ^SG` and `φ^UP` are asymptotically equal as the Péclet number grows**
([quarteroni2000numerical] Remark 12.6): their difference tends to `-1`, because
`B(2t) = 2t/(e^{2t} - 1) → 0`.  The book writes `φ^SG ≃ φ^UP`, which is the ratio statement
`AdvectionDiffusion.phiSG_div_phiUpwind_tendsto` below; the difference does **not** tend to
`0`. -/
theorem phiSG_asymptotics : Tendsto (fun t => phiSG t - phiUpwind t) atTop (𝓝 (-1)) := by
  have hexp : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hmul : Tendsto (fun x : ℝ => x * Real.exp (-x)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hden : Tendsto (fun x : ℝ => (1 - Real.exp (-x))⁻¹) atTop (𝓝 1) := by
    have : Tendsto (fun x : ℝ => 1 - Real.exp (-x)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub hexp
    simpa using this.inv₀ one_ne_zero
  have hB : Tendsto (fun x : ℝ => bernoulliFn x) atTop (𝓝 0) := by
    have hprod : Tendsto (fun x : ℝ => x * Real.exp (-x) * (1 - Real.exp (-x))⁻¹) atTop (𝓝 0) := by
      simpa using hmul.mul hden
    refine hprod.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have h1 : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
    have h2 : Real.exp x - 1 ≠ 0 := exp_sub_one_ne_zero hx.ne'
    rw [bernoulliFn_of_ne_zero hx.ne', Real.exp_neg]
    field_simp
  have h2t : Tendsto (fun t : ℝ => 2 * t) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_id
  have hcomp : Tendsto (fun t : ℝ => bernoulliFn (2 * t)) atTop (𝓝 0) := hB.comp h2t
  have he : ∀ t : ℝ, phiSG t - phiUpwind t = bernoulliFn (2 * t) - 1 := fun t => by
    simp [phiSG, phiUpwind]
    ring
  simpa [he] using hcomp.sub_const 1

/-- The ratio form of [quarteroni2000numerical] Remark 12.6's `φ^SG ≃ φ^UP`. -/
theorem phiSG_div_phiUpwind_tendsto : Tendsto (fun t => phiSG t / phiUpwind t) atTop (𝓝 1) := by
  have h1 : Tendsto (fun t : ℝ => (phiSG t - phiUpwind t) / t) atTop (𝓝 0) :=
    phiSG_asymptotics.div_atTop tendsto_id
  have he : ∀ᶠ t : ℝ in atTop, (phiSG t - phiUpwind t) / t + 1 = phiSG t / phiUpwind t := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [phiUpwind]
    field_simp
    ring
  simpa using (h1.add_const 1).congr' he

/-- **The stabilized local Péclet number** `Pe* = Pe/(1 + φ(Pe))` of
[quarteroni2000numerical] §12.5.2: the local Péclet number of the scheme with viscosity
`ε_h = ε (1 + φ(Pe))`. -/
def stabilizedPeclet (φ : ℝ → ℝ) (Pe : ℝ) : ℝ := Pe / (1 + φ Pe)

/-- For the upwind viscosity, `Pe* = Pe/(1 + Pe)`. -/
theorem stabilizedPeclet_phiUpwind (Pe : ℝ) : stabilizedPeclet phiUpwind Pe = Pe / (1 + Pe) := rfl

/-- **`Pe* < 1` for the upwind scheme, for every mesh size** ([quarteroni2000numerical]
§12.5.2). -/
theorem stabilizedPeclet_phiUpwind_lt_one {Pe : ℝ} (hPe : 0 < Pe) :
    stabilizedPeclet phiUpwind Pe < 1 := by
  rw [stabilizedPeclet_phiUpwind, div_lt_one (by linarith)]
  linarith

/-- The stabilized Péclet number of the upwind scheme is positive. -/
theorem stabilizedPeclet_phiUpwind_pos {Pe : ℝ} (hPe : 0 < Pe) :
    0 < stabilizedPeclet phiUpwind Pe := by
  rw [stabilizedPeclet_phiUpwind]
  positivity

/-- **The stabilized Péclet number of the Scharfetter–Gummel scheme is `tanh Pe`**
([quarteroni2000numerical] §12.5.2), since `1 + φ^SG(Pe) = Pe coth Pe`. -/
theorem stabilizedPeclet_phiSG_eq_tanh {Pe : ℝ} (hPe : 0 < Pe) :
    stabilizedPeclet phiSG Pe = Real.tanh Pe := by
  have hsinh : 0 < Real.sinh Pe := Real.sinh_pos_iff.2 hPe
  rw [stabilizedPeclet, one_add_phiSG hPe.ne', Real.tanh_eq_sinh_div_cosh, div_div_eq_mul_div,
    div_eq_div_iff (by positivity) (Real.cosh_pos Pe).ne']
  ring

/-- **`Pe* < 1` for the Scharfetter–Gummel scheme, for every mesh size**. -/
theorem stabilizedPeclet_phiSG_lt_one {Pe : ℝ} (hPe : 0 < Pe) :
    stabilizedPeclet phiSG Pe < 1 := by
  rw [stabilizedPeclet_phiSG_eq_tanh hPe]
  exact Real.tanh_lt_one Pe

/-- The stabilized Péclet number of the Scharfetter–Gummel scheme is positive. -/
theorem stabilizedPeclet_phiSG_pos {Pe : ℝ} (hPe : 0 < Pe) : 0 < stabilizedPeclet phiSG Pe := by
  rw [stabilizedPeclet_phiSG_eq_tanh hPe, Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.2 hPe) (Real.cosh_pos Pe)

/-! ### The difference schemes: centred, upwind, and with artificial viscosity -/

/-- The uniform mesh width `h = 1/n` of a partition of `(0, 1)` into `n` panels. -/
def meshWidth (n : ℕ) : ℝ := 1 / n

/-- The mesh width is positive. -/
theorem meshWidth_pos {n : ℕ} (hn : n ≠ 0) : 0 < meshWidth n := by
  rw [meshWidth]
  positivity

/-- **The numerical viscosity** `ε_h = ε (1 + φ(Pe))` of [quarteroni2000numerical] (12.82), the
diffusion coefficient of the stabilized centred scheme. -/
def viscosity (ε β h : ℝ) (φ : ℝ → ℝ) : ℝ := ε * (1 + φ (localPeclet β h ε))

/-- The viscosity function `φ = 0` gives back the physical diffusion: the centred scheme
(12.77). -/
@[simp]
theorem viscosity_zero (ε β h : ℝ) : viscosity ε β h 0 = ε := by
  simp [viscosity]

/-- **The upwind viscosity is the artificial diffusion `|β| h / 2`** of
[quarteroni2000numerical] (12.81): `ε_h = ε (1 + Pe) = ε + |β| h / 2`. -/
theorem viscosity_phiUpwind {ε : ℝ} (hε : ε ≠ 0) (β h : ℝ) :
    viscosity ε β h phiUpwind = ε + |β| * h / 2 := by
  rw [viscosity, phiUpwind, localPeclet]
  field_simp

/-- The viscosity is positive when `φ(Pe) ≥ 0`, as it is for the upwind and Scharfetter–Gummel
choices. -/
theorem viscosity_pos {ε β h : ℝ} {φ : ℝ → ℝ} (hε : 0 < ε)
    (hφ : 0 ≤ φ (localPeclet β h ε)) : 0 < viscosity ε β h φ := by
  rw [viscosity]
  have : (0 : ℝ) < 1 + φ (localPeclet β h ε) := by linarith
  positivity

/-- **The centred scheme with numerical viscosity**, [quarteroni2000numerical] (12.79) with
(12.82): the grid function `u` on the uniform mesh of `n` panels satisfies `u_0 = 0`, `u_n = 1`
and `-ε_h (u_{i+1} - 2 u_i + u_{i-1})/h² + β (u_{i+1} - u_{i-1})/(2h) = 0` at the interior nodes,
written here at the indices `i`, `i + 1`, `i + 2`.  `φ = 0` is the centred scheme (12.77) and
`φ = AdvectionDiffusion.phiUpwind` the upwind scheme (12.78). -/
def viscosityScheme (ε β : ℝ) (n : ℕ) (φ : ℝ → ℝ) (u : ℕ → ℝ) : Prop :=
  u 0 = 0 ∧ u n = 1 ∧ ∀ i, i + 2 ≤ n →
    -viscosity ε β (meshWidth n) φ * ((u (i + 2) - 2 * u (i + 1) + u i) / meshWidth n ^ 2)
      + β * ((u (i + 2) - u i) / (2 * meshWidth n)) = 0

/-- **The upwind scheme**, [quarteroni2000numerical] (12.78): the centred second difference for
`u''` and the backward difference for `u'` (the case `β > 0`). -/
def upwindScheme (ε β : ℝ) (n : ℕ) (u : ℕ → ℝ) : Prop :=
  u 0 = 0 ∧ u n = 1 ∧ ∀ i, i + 2 ≤ n →
    -ε * ((u (i + 2) - 2 * u (i + 1) + u i) / meshWidth n ^ 2)
      + β * ((u (i + 1) - u i) / meshWidth n) = 0

/-- **The centred scheme is the `P_1` difference equation (12.75)**: multiplying (12.77) by `h`
gives `(ε/h)(-u_{i-1} + 2 u_i - u_{i+1}) + (β/2)(u_{i+1} - u_{i-1}) = 0`, the equation the
piecewise linear Galerkin method produces ([quarteroni2000numerical] §12.5.2). -/
theorem viscosityScheme_zero_iff {ε β : ℝ} {n : ℕ} (hn : n ≠ 0) (u : ℕ → ℝ) :
    viscosityScheme ε β n 0 u ↔ u 0 = 0 ∧ u n = 1 ∧ ∀ i, i + 2 ≤ n →
      ε / meshWidth n * (-u i + 2 * u (i + 1) - u (i + 2)) + β / 2 * (u (i + 2) - u i) = 0 := by
  have hh := meshWidth_pos hn
  rw [viscosityScheme, viscosity_zero]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun i => imp_congr_right fun _ => ?_))
  rw [show ε / meshWidth n * (-u i + 2 * u (i + 1) - u (i + 2)) + β / 2 * (u (i + 2) - u i)
      = meshWidth n * (-ε * ((u (i + 2) - 2 * u (i + 1) + u i) / meshWidth n ^ 2)
        + β * ((u (i + 2) - u i) / (2 * meshWidth n))) by field_simp; ring]
  exact ⟨fun h => by rw [h, mul_zero], fun h => by
    simpa [hh.ne'] using (mul_eq_zero.1 h).resolve_left hh.ne'⟩

/-- **Upwinding is centred differencing with the artificial viscosity `ε (1 + Pe)`**
([quarteroni2000numerical] (12.78)–(12.81)): the two schemes have the same equations, by the
identity `(u_i - u_{i-1})/h = (u_{i+1} - u_{i-1})/(2h) - (h/2)(u_{i+1} - 2u_i + u_{i-1})/h²`. -/
theorem upwindScheme_iff_viscosityScheme {ε β : ℝ} {n : ℕ} (hε : ε ≠ 0) (hβ : 0 < β) (hn : n ≠ 0)
    (u : ℕ → ℝ) : upwindScheme ε β n u ↔ viscosityScheme ε β n phiUpwind u := by
  have hh := meshWidth_pos hn
  rw [upwindScheme, viscosityScheme]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun i => imp_congr_right fun _ => ?_))
  rw [viscosity_phiUpwind hε, abs_of_pos hβ,
    show -ε * ((u (i + 2) - 2 * u (i + 1) + u i) / meshWidth n ^ 2)
        + β * ((u (i + 1) - u i) / meshWidth n)
      = -(ε + β * meshWidth n / 2) * ((u (i + 2) - 2 * u (i + 1) + u i) / meshWidth n ^ 2)
        + β * ((u (i + 2) - u i) / (2 * meshWidth n)) by field_simp; ring]

/-- **With no diffusion the upwind scheme transports the boundary value**
([quarteroni2000numerical] §12.5.2): for `ε = 0` it reduces to `u_i = u_{i-1}`, the solution of
the limit problem `β u' = 0`. -/
theorem upwindScheme_zero_diffusion {β : ℝ} {n : ℕ} (hβ : β ≠ 0) (hn : n ≠ 0) {u : ℕ → ℝ}
    (hu : upwindScheme 0 β n u) {i : ℕ} (hi : i + 2 ≤ n) : u (i + 1) = u i := by
  have hh := meshWidth_pos hn
  have h := hu.2.2 i hi
  rw [neg_zero, zero_mul, zero_add] at h
  have := (mul_eq_zero.1 h).resolve_left hβ
  rw [div_eq_zero_iff] at this
  rcases this with h1 | h1
  · linarith
  · exact absurd h1 hh.ne'

/-- The local Péclet number of the scheme with viscosity `ε_h` is the stabilized Péclet number
`Pe* = Pe/(1 + φ(Pe))` of [quarteroni2000numerical] §12.5.2. -/
theorem localPeclet_viscosity {ε β h : ℝ} {φ : ℝ → ℝ} (hε : ε ≠ 0) :
    localPeclet β h (viscosity ε β h φ) = stabilizedPeclet φ (localPeclet β h ε) := by
  rw [viscosity, localPeclet, localPeclet, stabilizedPeclet]
  field_simp

/-- **The scheme with viscosity is the centred difference equation (12.76) at the stabilized
Péclet number**: dividing (12.79) by `ε_h/h²` turns it into `(Pe* - 1) u_{i+1} + 2 u_i -
(Pe* + 1) u_{i-1} = 0` ([quarteroni2000numerical] §12.5.2). -/
theorem viscosityScheme_iff_centredRecurrence {ε β : ℝ} {n : ℕ} {φ : ℝ → ℝ} (hβ : 0 < β)
    (hn : n ≠ 0) (hε : ε ≠ 0) (hεh : viscosity ε β (meshWidth n) φ ≠ 0) (u : ℕ → ℝ) :
    viscosityScheme ε β n φ u ↔ u 0 = 0 ∧ u n = 1 ∧ ∀ i, i + 2 ≤ n →
      (stabilizedPeclet φ (localPeclet β (meshWidth n) ε) - 1) * u (i + 2) + 2 * u (i + 1)
        - (stabilizedPeclet φ (localPeclet β (meshWidth n) ε) + 1) * u i = 0 := by
  have hh := meshWidth_pos hn
  set Pe := stabilizedPeclet φ (localPeclet β (meshWidth n) ε) with hPe
  have hPeval : Pe * (2 * viscosity ε β (meshWidth n) φ) = β * meshWidth n := by
    rw [hPe, ← localPeclet_viscosity hε, localPeclet, abs_of_pos hβ]
    field_simp
  rw [viscosityScheme]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun i => imp_congr_right fun _ => ?_))
  have key : (Pe - 1) * u (i + 2) + 2 * u (i + 1) - (Pe + 1) * u i
      = meshWidth n ^ 2 / viscosity ε β (meshWidth n) φ
        * (-viscosity ε β (meshWidth n) φ * ((u (i + 2) - 2 * u (i + 1) + u i) / meshWidth n ^ 2)
          + β * ((u (i + 2) - u i) / (2 * meshWidth n))) := by
    field_simp
    linear_combination (u (i + 2) - u i) * hPeval
  rw [key]
  refine ⟨fun h => by rw [h, mul_zero], fun h => ?_⟩
  have hne : meshWidth n ^ 2 / viscosity ε β (meshWidth n) φ ≠ 0 := by
    exact div_ne_zero (by positivity) hεh
  exact (mul_eq_zero.1 h).resolve_left hne

/-- **The solution of the scheme with viscosity is the explicit oscillating solution (12.76) at
the stabilized Péclet number** ([quarteroni2000numerical] §12.5.1–12.5.2).  In particular it
oscillates exactly when `Pe* > 1`, which is why the upwind and Scharfetter–Gummel viscosities —
for which `Pe* < 1` for every `h` — cure the oscillations. -/
theorem viscosityScheme_eq_centredSolution {ε β : ℝ} {n : ℕ} {φ : ℝ → ℝ} (hβ : 0 < β) (hn : n ≠ 0)
    (hε : ε ≠ 0) (hεh : viscosity ε β (meshWidth n) φ ≠ 0)
    (hpos : 0 < stabilizedPeclet φ (localPeclet β (meshWidth n) ε))
    (hne : stabilizedPeclet φ (localPeclet β (meshWidth n) ε) ≠ 1) {u : ℕ → ℝ}
    (hu : viscosityScheme ε β n φ u) {i : ℕ} (hi : i ≤ n) :
    u i = centredSolution n (stabilizedPeclet φ (localPeclet β (meshWidth n) ε)) i := by
  obtain ⟨h0, hlast, hrec⟩ := (viscosityScheme_iff_centredRecurrence hβ hn hε hεh u).1 hu
  exact centredSolution_unique hpos hne hn h0 hlast hrec hi

/-! ### Nodal exactness of the Scharfetter–Gummel scheme -/

/-- **The amplification ratio of the Scharfetter–Gummel scheme is the exact one**:
`(1 + Pe*)/(1 - Pe*) = e^{2 Pe}` because `Pe* = tanh Pe`.  This is the whole content of the nodal
exactness of the exponential fitting scheme ([quarteroni2000numerical] Remark 12.6). -/
theorem centredRatio_stabilizedPeclet_phiSG {Pe : ℝ} (hPe : 0 < Pe) :
    centredRatio (stabilizedPeclet phiSG Pe) = Real.exp (2 * Pe) := by
  have h1 : 1 - Real.tanh Pe ≠ 0 := sub_ne_zero.2 (Real.tanh_lt_one Pe).ne'
  have hE : Real.exp Pe ≠ 0 := (Real.exp_pos Pe).ne'
  have hEE : Real.exp (2 * Pe) = Real.exp Pe * Real.exp Pe := by
    rw [← Real.exp_add]
    ring_nf
  have hs : Real.exp Pe + (Real.exp Pe)⁻¹ ≠ 0 := by positivity
  rw [stabilizedPeclet_phiSG_eq_tanh hPe, centredRatio, div_eq_iff h1, Real.tanh_eq, Real.exp_neg,
    hEE]
  field_simp
  ring

/-- **The Scharfetter–Gummel scheme is nodally exact** ([quarteroni2000numerical] Remark 12.6):
for the model problem (12.70) its solution agrees with the exact solution at every node, whatever
the mesh size — and hence whatever the local Péclet number.  The reason is
`AdvectionDiffusion.centredRatio_stabilizedPeclet_phiSG`: the discrete amplification ratio
`(1 + Pe*)/(1 - Pe*)` is exactly `e^{βh/ε}`, the ratio of the exact solution's exponential
between consecutive nodes. -/
theorem sg_nodal_exact {ε β : ℝ} {n : ℕ} (hε : 0 < ε) (hβ : 0 < β) (hn : n ≠ 0) {u : ℕ → ℝ}
    (hu : viscosityScheme ε β n phiSG u) {i : ℕ} (hi : i ≤ n) :
    u i = exactSolution ε β (i * meshWidth n) := by
  have hh : 0 < meshWidth n := meshWidth_pos hn
  set Pe := localPeclet β (meshWidth n) ε with hPedef
  have hPe : 0 < Pe := localPeclet_pos hβ.ne' hh hε
  have hφ : 0 ≤ phiSG Pe := phiSG_nonneg hPe.le
  have hεh : 0 < viscosity ε β (meshWidth n) phiSG := viscosity_pos hε hφ
  have hpos : 0 < stabilizedPeclet phiSG Pe := stabilizedPeclet_phiSG_pos hPe
  have hlt : stabilizedPeclet phiSG Pe < 1 := stabilizedPeclet_phiSG_lt_one hPe
  have hstep := viscosityScheme_eq_centredSolution hβ hn hε.ne' hεh.ne' hpos hlt.ne hu hi
  rw [hstep, centredSolution, centredRatio_stabilizedPeclet_phiSG hPe]
  -- `2 Pe = β h / ε`
  have h2Pe : 2 * Pe = β * meshWidth n / ε := by
    rw [hPedef, localPeclet, abs_of_pos hβ]
    field_simp
  have hpow : ∀ m : ℕ, Real.exp (2 * Pe) ^ m = Real.exp (β * (m * meshWidth n) / ε) := fun m => by
    rw [← Real.exp_nat_mul, h2Pe]
    congr 1
    ring
  have hn1 : (n : ℝ) * meshWidth n = 1 := by
    rw [meshWidth]
    field_simp
  rw [hpow i, hpow n, hn1, mul_one, exactSolution,
    show (1 : ℝ) - Real.exp (β * (i * meshWidth n) / ε)
      = -(Real.exp (β * (i * meshWidth n) / ε) - 1) by ring,
    show (1 : ℝ) - Real.exp (β / ε) = -(Real.exp (β / ε) - 1) by ring, neg_div_neg_eq]

/-! ### The matrix of the stabilized scheme is an M-matrix -/

/-- Negating a tridiagonal Toeplitz matrix negates its three bands. -/
theorem neg_tridiagonalToeplitz (m : ℕ) (x y z : ℝ) :
    -Matrix.tridiagonalToeplitz m x y z = Matrix.tridiagonalToeplitz m (-x) (-y) (-z) := by
  ext i j
  rw [Matrix.neg_apply, Matrix.tridiagonalToeplitz_apply, Matrix.tridiagonalToeplitz_apply]
  split_ifs <;> simp

/-- The matrix of the stabilized centred scheme splits into the symmetric model Laplacian and the
antisymmetric centred advection matrix:
`tridiag(-(1 + p), 2, -(1 - p)) = tridiag(-1, 2, -1) + p tridiag(-1, 0, 1)`. -/
theorem tridiagonalToeplitz_eq_add_smul (m : ℕ) (p : ℝ) :
    Matrix.tridiagonalToeplitz m (-(1 + p)) 2 (-(1 - p))
      = Matrix.symmTridiagonalToeplitz m (-1) 2 + p • Matrix.tridiagonalToeplitz m (-1) 0 1 := by
  rw [Matrix.symmTridiagonalToeplitz_eq_tridiagonalToeplitz]
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.tridiagonalToeplitz_apply,
    Matrix.tridiagonalToeplitz_apply, Matrix.tridiagonalToeplitz_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The centred advection matrix `tridiag(-1, 0, 1)` is antisymmetric, so its quadratic form
vanishes: the advective term contributes nothing to the energy of the discrete operator. -/
theorem dotProduct_mulVec_tridiagonalToeplitz_antisymm {m : ℕ} (x : Fin m → ℝ) :
    x ⬝ᵥ (Matrix.tridiagonalToeplitz m (-1) 0 1 *ᵥ x) = 0 := by
  have htr : (Matrix.tridiagonalToeplitz m (-1) 0 1)ᵀ = -Matrix.tridiagonalToeplitz m (-1) 0 1 := by
    rw [Matrix.tridiagonalToeplitz_transpose, neg_tridiagonalToeplitz]
    norm_num
  have h1 : x ⬝ᵥ (Matrix.tridiagonalToeplitz m (-1) 0 1 *ᵥ x)
      = x ⬝ᵥ ((Matrix.tridiagonalToeplitz m (-1) 0 1)ᵀ *ᵥ x) := by
    rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, dotProduct_comm]
  rw [htr, Matrix.neg_mulVec, dotProduct_neg] at h1
  linarith

/-- The quadratic form of the stabilized scheme's matrix is that of the model Laplacian, hence
positive: `xᵀ tridiag(-(1 + p), 2, -(1 - p)) x = xᵀ tridiag(-1, 2, -1) x > 0` for `x ≠ 0`,
whatever `p`. -/
theorem dotProduct_mulVec_tridiagonalToeplitz_pos {m : ℕ} (p : ℝ) {x : Fin m → ℝ} (hx : x ≠ 0) :
    0 < x ⬝ᵥ (Matrix.tridiagonalToeplitz m (-(1 + p)) 2 (-(1 - p)) *ᵥ x) := by
  rw [tridiagonalToeplitz_eq_add_smul, Matrix.add_mulVec, dotProduct_add,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    dotProduct_mulVec_tridiagonalToeplitz_antisymm, mul_zero, add_zero]
  simpa using (Matrix.posDef_symmTridiagonalToeplitz_neg_one_two m).dotProduct_mulVec_pos hx

/-- **The matrix of the stabilized scheme is an M-matrix** whenever `|Pe*| ≤ 1`
([quarteroni2000numerical] Exercise 12.13): its off-diagonal entries `-(1 ± Pe*)` are
nonpositive, and its quadratic form is that of the model Laplacian, which is positive definite.
Belongs beside `Matrix.tridiagonalToeplitz` in
`Numlib/LinearAlgebra/Matrix/TridiagonalToeplitz.lean`. -/
theorem isMMatrix_smul_tridiagonalToeplitz {m : ℕ} {c p : ℝ} (hc : 0 < c) (hp : |p| ≤ 1) :
    (c • Matrix.tridiagonalToeplitz m (-(1 + p)) 2 (-(1 - p))).IsMMatrix := by
  obtain ⟨hp1, hp2⟩ := abs_le.1 hp
  refine Matrix.isMMatrix_of_forall_dotProduct_mulVec_pos (fun x hx => ?_) fun i j hij => ?_
  · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_pos hc (dotProduct_mulVec_tridiagonalToeplitz_pos p hx)
  · rw [Matrix.smul_apply, smul_eq_mul, Matrix.tridiagonalToeplitz_apply]
    split_ifs with h1 h2 h3
    · exact absurd (Fin.val_injective h1) hij
    · nlinarith
    · nlinarith
    · simp

/-- **The matrix of the stabilized difference scheme is an M-matrix**
([quarteroni2000numerical] §12.5.2 and Exercise 12.13): the `(n - 1) × (n - 1)` matrix of the
interior equations of `AdvectionDiffusion.viscosityScheme` is
`(ε_h/h²) tridiag(-(1 + Pe*), 2, -(1 - Pe*))`, and it is an M-matrix as soon as `|Pe*| ≤ 1` —
which `AdvectionDiffusion.stabilizedPeclet_phiUpwind_lt_one` and
`stabilizedPeclet_phiSG_lt_one` give for the upwind and the Scharfetter–Gummel viscosities, for
every mesh size.  The discrete maximum principle then follows from
`Matrix.IsMMatrix.nonneg_of_mulVec_nonneg`. -/
theorem viscosityScheme_isMMatrix {ε β : ℝ} {n : ℕ} {φ : ℝ → ℝ} (m : ℕ)
    (hεh : 0 < viscosity ε β (meshWidth n) φ) (hn : n ≠ 0)
    (hPe : |stabilizedPeclet φ (localPeclet β (meshWidth n) ε)| ≤ 1) :
    ((viscosity ε β (meshWidth n) φ / meshWidth n ^ 2) •
        Matrix.tridiagonalToeplitz m
          (-(1 + stabilizedPeclet φ (localPeclet β (meshWidth n) ε))) 2
          (-(1 - stabilizedPeclet φ (localPeclet β (meshWidth n) ε)))).IsMMatrix :=
  isMMatrix_smul_tridiagonalToeplitz (by
    have := meshWidth_pos hn
    positivity) hPe

/-! ### The stabilized finite element form -/

section Form

open EllipticInterval (constLinf coeFn_constLinf norm_constLinf mulL_constLinf)

variable {a b : ℝ}

/-- **The stabilized bilinear form** of [quarteroni2000numerical] (12.84),
`a_h(u, v) = ∫_a^b (ε_h u' v' + β u' v)` with the numerical viscosity
`ε_h = AdvectionDiffusion.viscosity ε β h φ`: the elliptic form of
`Numlib/Variational/EllipticInterval.lean` at the constant coefficients `ε_h`, `β`, `0`.  The
unstabilized Galerkin form (12.73) is the case `φ = 0`. -/
def stabilizedForm (a b : ℝ) (ε β h : ℝ) (φ : ℝ → ℝ) : SesqForm ℝ (SobolevInterval 1 a b) :=
  EllipticInterval.form a b (constLinf a b (viscosity ε β h φ)) (constLinf a b β) 0

/-- **The stabilization term** `b(u, v) = ε φ(Pe) ∫ u' v'` of [quarteroni2000numerical] (12.84)
is the difference between the stabilized form and the Galerkin form. -/
theorem stabilizedForm_sub_form (a b : ℝ) (ε β h : ℝ) (φ : ℝ → ℝ)
    (u v : SobolevInterval 1 a b) :
    stabilizedForm a b ε β h φ u v
        - EllipticInterval.form a b (constLinf a b ε) (constLinf a b β) 0 u v
      = ε * φ (localPeclet β h ε)
        * ⟪SobolevInterval.deriv u 1, SobolevInterval.deriv v 1⟫_ℝ := by
  simp only [stabilizedForm, EllipticInterval.form_apply_inner, mulL_constLinf,
    real_inner_smul_left, viscosity]
  ring

/-- **The energy identity `a_h(v, v) = ε_h |v|²_{H^1}`** on `H^1_0(a, b)`
([quarteroni2000numerical] §12.5.3): the advective term contributes nothing, because
`∫ β v' v = -½ ∫ β' v² = 0` for a constant `β` and `v` vanishing at both endpoints. -/
theorem stabilizedForm_self (hab : a < b) {ε β h : ℝ} (φ : ℝ → ℝ)
    {v : SobolevInterval 1 a b} (hv : v ∈ SobolevIntervalZero a b) :
    stabilizedForm a b ε β h φ v v
      = viscosity ε β h φ * SobolevInterval.seminorm 1 a b v ^ 2 := by
  have hβAC : AbsolutelyContinuousOnInterval (fun _ : ℝ => β) a b :=
    (contDiffOn_const (c := β) (n := 1) (s := uIcc a b)).absolutelyContinuousOnInterval
  have hc := coeFn_constLinf a b (viscosity ε β h φ)
  have hcb := coeFn_constLinf a b β
  have hrep := SobolevInterval.fn_ae_eq_rep hab v
  have i1 : IntegrableOn (fun x => viscosity ε β h φ
      * (SobolevInterval.deriv v 1 x * SobolevInterval.deriv v 1 x)) (Ioo a b) := by
    refine (EllipticInterval.integrable_mul_mul (constLinf a b (viscosity ε β h φ))
      (SobolevInterval.deriv v 1) (SobolevInterval.deriv v 1)).congr ?_
    filter_upwards [hc] with x hx
    rw [hx]
    ring
  have i2 : IntegrableOn (fun x => β * (SobolevInterval.deriv v 1 x
      * SobolevInterval.rep v x)) (Ioo a b) := by
    refine (EllipticInterval.integrable_mul_mul (constLinf a b β) (SobolevInterval.deriv v 1)
      (SobolevInterval.deriv v 0)).congr ?_
    filter_upwards [hcb, hrep] with x h1 h2
    rw [h1, SobolevInterval.deriv_zero, h2]
    ring
  have e1 : stabilizedForm a b ε β h φ v v
      = (∫ x in Ioo a b, viscosity ε β h φ
          * (SobolevInterval.deriv v 1 x * SobolevInterval.deriv v 1 x))
        + ∫ x in Ioo a b, β * (SobolevInterval.deriv v 1 x * SobolevInterval.rep v x) := by
    rw [stabilizedForm, EllipticInterval.form_apply, ← integral_add i1 i2]
    refine integral_congr_ae ?_
    filter_upwards [hc, hcb, hrep, Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ioo a b))]
      with x h1 h2 h3 h4
    rw [h1, h2, h4, SobolevInterval.deriv_zero, h3]
    simp only [Pi.zero_apply]
    ring
  rw [e1, EllipticInterval.integral_mul_deriv_mul_rep_eq hab hβAC hv, integral_const_mul]
  simp only [deriv_const', zero_mul, integral_zero, mul_zero, add_zero]
  rw [SobolevInterval.seminorm_apply, show SobolevInterval.deriv v (Fin.last 1)
    = SobolevInterval.deriv v 1 from rfl, norm_sq_eq_integral_sq]
  refine congrArg _ (integral_congr_ae (Eventually.of_forall fun x => ?_))
  dsimp only
  rw [sq_abs, sq]

/-- **The continuity constant `M_h = ε_h + |β| C_P` of the stabilized form** in the `H^1`
seminorm on `H^1_0(a, b)`, the constant of the proof of [quarteroni2000numerical] Theorem 12.4,
with `C_P = (b - a)/√2`. -/
theorem stabilizedForm_isBoundedWith_seminorm (hab : a < b) {ε β h : ℝ} {φ : ℝ → ℝ}
    (hεh : 0 ≤ viscosity ε β h φ) {u v : SobolevInterval 1 a b}
    (hu : u ∈ SobolevIntervalZero a b) (hv : v ∈ SobolevIntervalZero a b) :
    |stabilizedForm a b ε β h φ u v|
      ≤ (viscosity ε β h φ + (b - a) / Real.sqrt 2 * |β|)
        * SobolevInterval.seminorm 1 a b u * SobolevInterval.seminorm 1 a b v := by
  have h := EllipticInterval.abs_form_le_seminorm hab (constLinf a b (viscosity ε β h φ))
    (constLinf a b β) 0 hu hv
  rw [norm_constLinf hab, norm_constLinf hab, norm_zero, abs_of_nonneg hεh, mul_zero,
    add_zero] at h
  exact h

/-- **Strang's first lemma in a seminorm**: if the perturbed form `B` is bounded by `M` and
coercive with constant `c` for the seminorm `q` relative to a subspace `W`, `uN ∈ K ≤ W` and the
consistency defect satisfies `|B (u - uN) z| ≤ δ q z` for every `z ∈ K`
([quarteroni2000numerical] (12.87) is such a defect), then
`q (u - uN) ≤ (1 + M/c) q (u - w) + δ/c` for every `w ∈ K`.  Only additivity of `B` in each slot
is used.  Belongs in `Numlib/Variational/Galerkin.lean`, as the seminorm companion of
`strang_first`. -/
theorem seminorm_sub_le_of_consistencyDefect {V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : Seminorm ℝ V) (B : V → V → ℝ) (hadd : ∀ x y z, B (x + y) z = B x z + B y z)
    {W : Submodule ℝ V} {M c δ : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ)
    (hM : ∀ x ∈ W, ∀ y ∈ W, |B x y| ≤ M * q x * q y) (hcoer : ∀ x ∈ W, c * q x ^ 2 ≤ B x x)
    {K : Submodule ℝ V} (hK : K ≤ W) {u uN : V} (hu : u ∈ W) (huN : uN ∈ K)
    (hdefect : ∀ z ∈ K, |B (u - uN) z| ≤ δ * q z) {w : V} (hw : w ∈ K) :
    q (u - uN) ≤ (1 + M / c) * q (u - w) + δ / c := by
  set z : V := w - uN with hz
  have hzK : z ∈ K := K.sub_mem hw huN
  have hzW : z ∈ W := hK hzK
  have hwW : w ∈ W := hK hw
  have hsplit : B z z = B (w - u) z + B (u - uN) z := by
    nth_rewrite 1 [show z = (w - u) + (u - uN) by rw [hz]; abel]
    rw [hadd]
  have hkey : c * q z ^ 2 ≤ (M * q (u - w) + δ) * q z := by
    calc c * q z ^ 2 ≤ B z z := hcoer z hzW
      _ = B (w - u) z + B (u - uN) z := hsplit
      _ ≤ |B (w - u) z| + |B (u - uN) z| := by
          exact add_le_add (le_abs_self _) (le_abs_self _)
      _ ≤ M * q (w - u) * q z + δ * q z :=
          add_le_add (hM _ (W.sub_mem hwW hu) _ hzW) (hdefect z hzK)
      _ = (M * q (u - w) + δ) * q z := by
          rw [show q (w - u) = q (u - w) from by rw [← neg_sub u w, map_neg_eq_map]]
          ring
  have hqz : c * q z ≤ M * q (u - w) + δ := by
    rcases eq_or_lt_of_le (apply_nonneg q z) with h0 | h0
    · rw [← h0, mul_zero]
      have hMq : 0 ≤ M * q (u - w) := by
        rcases eq_or_lt_of_le (apply_nonneg q (u - w)) with h | h
        · rw [← h, mul_zero]
        · have hw' : u - w ∈ W := W.sub_mem hu hwW
          have h1 : c * q (u - w) ^ 2 ≤ M * q (u - w) ^ 2 :=
            (hcoer _ hw').trans ((le_abs_self _).trans
              (by have := hM _ hw' _ hw'; rwa [mul_assoc, ← sq] at this))
          exact mul_nonneg (hc.le.trans (le_of_mul_le_mul_right h1 (by positivity))) h.le
      linarith
    · refine le_of_mul_le_mul_right ?_ h0
      calc c * q z * q z = c * q z ^ 2 := by ring
        _ ≤ (M * q (u - w) + δ) * q z := hkey
  have htri : q (u - uN) ≤ q (u - w) + q z := by
    have : u - uN = (u - w) + z := by rw [hz]; abel
    rw [this]
    exact q.add_le' _ _
  have hqz' : q z ≤ (M * q (u - w) + δ) / c := by rwa [le_div_iff₀ hc, mul_comm]
  calc q (u - uN) ≤ q (u - w) + q z := htri
    _ ≤ q (u - w) + (M * q (u - w) + δ) / c := by linarith
    _ = (1 + M / c) * q (u - w) + δ / c := by field_simp; ring

/-- **The error bound of the stabilized finite element method**, the content of
[quarteroni2000numerical] (12.87)–(12.89) in Strang form: if `u ∈ H^1_0(a, b)` solves the
Galerkin problem `a(u, v) = ℓ(v)` on the subspace `K ≤ H^1_0(a, b)` and `u_h ∈ K` solves the
stabilized problem `a_h(u_h, v) = ℓ(v)` on `K`, then for every `w ∈ K`

`|u - u_h|_{H^1} ≤ (1 + M_h/ε_h) |u - w|_{H^1} + (ε φ(Pe)/ε_h) |u|_{H^1}`,

with `M_h = ε_h + |β| C_P`.  This is sharper than the book's (12.89), which applies Young's
inequality to the same two terms; the interpolation estimates of Theorem 8.3 turn it into the
convergence rates of Theorem 12.4 once the trial space `K` is a finite element space. -/
theorem seminorm_sub_stabilized_le (hab : a < b) {ε β h : ℝ} {φ : ℝ → ℝ} (hε : 0 < ε)
    (hφ : 0 ≤ φ (localPeclet β h ε)) {ℓ : SobolevInterval 1 a b →L[ℝ] ℝ}
    {K : Submodule ℝ (SobolevInterval 1 a b)} (hK : K ≤ SobolevIntervalZero a b)
    {u uh : SobolevInterval 1 a b} (hu : u ∈ SobolevIntervalZero a b)
    (hexact : ∀ v ∈ K, EllipticInterval.form a b (constLinf a b ε) (constLinf a b β) 0 u v = ℓ v)
    (hdisc : IsGalerkinSolution (stabilizedForm a b ε β h φ) ℓ K uh)
    {w : SobolevInterval 1 a b} (hw : w ∈ K) :
    SobolevInterval.seminorm 1 a b (u - uh)
      ≤ (1 + (viscosity ε β h φ + (b - a) / Real.sqrt 2 * |β|) / viscosity ε β h φ)
          * SobolevInterval.seminorm 1 a b (u - w)
        + ε * φ (localPeclet β h ε) / viscosity ε β h φ
          * SobolevInterval.seminorm 1 a b u := by
  have hεh : 0 < viscosity ε β h φ := viscosity_pos hε hφ
  have hδ : 0 ≤ ε * φ (localPeclet β h ε) * SobolevInterval.seminorm 1 a b u := by positivity
  have hdef : ∀ z ∈ K, |stabilizedForm a b ε β h φ (u - uh) z|
      ≤ ε * φ (localPeclet β h ε) * SobolevInterval.seminorm 1 a b u
        * SobolevInterval.seminorm 1 a b z := by
    intro z hz
    -- the consistency defect is the stabilization term, `(12.87)`
    have hsub : stabilizedForm a b ε β h φ (u - uh) z
        = ε * φ (localPeclet β h ε)
          * ⟪ SobolevInterval.deriv u 1, SobolevInterval.deriv z 1⟫_ℝ := by
      have h1 : stabilizedForm a b ε β h φ (u - uh) z
          = stabilizedForm a b ε β h φ u z - stabilizedForm a b ε β h φ uh z := by
        simp
      rw [h1, hdisc.2 z hz, ← hexact z hz, ← stabilizedForm_sub_form]
    rw [hsub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε * φ (localPeclet β h ε))]
    calc ε * φ (localPeclet β h ε)
          * |⟪ SobolevInterval.deriv u 1, SobolevInterval.deriv z 1⟫_ℝ|
        ≤ ε * φ (localPeclet β h ε)
          * (‖SobolevInterval.deriv u 1‖ * ‖SobolevInterval.deriv z 1‖) := by
          gcongr
          exact abs_real_inner_le_norm _ _
      _ = ε * φ (localPeclet β h ε) * SobolevInterval.seminorm 1 a b u
          * SobolevInterval.seminorm 1 a b z := by
          rw [SobolevInterval.seminorm_apply, SobolevInterval.seminorm_apply,
            show SobolevInterval.deriv u (Fin.last 1) = SobolevInterval.deriv u 1 from rfl,
            show SobolevInterval.deriv z (Fin.last 1) = SobolevInterval.deriv z 1 from rfl]
          ring
  have key := seminorm_sub_le_of_consistencyDefect (SobolevInterval.seminorm 1 a b)
    (fun x y => stabilizedForm a b ε β h φ x y) (fun x y z => by simp) hεh hδ
    (fun x hx y hy => stabilizedForm_isBoundedWith_seminorm hab hεh.le hx hy)
    (fun x hx => (stabilizedForm_self hab φ hx).ge) hK hu hdisc.1 hdef hw
  refine key.trans_eq ?_
  ring

/-- **Theorem 12.4 for the upwind method with `k = 1`** ([quarteroni2000numerical] (12.85)): on
a partition of mesh at most `h` with the `P_1` finite element space `X_h^{1,0}` as trial space,
the upwind-stabilized Galerkin error satisfies
`|ů - ů_h|_{H¹} ≤ C h (|ů|_{H¹} + |ů|_{H²})` with `C = 2 + C_P |β|/ε + |β|/(2ε)` independent of
`h` and of `ů`. This is `AdvectionDiffusion.seminorm_sub_stabilized_le` with
`w = Π_h^1 ů` (`FiniteElement.lagrangeInterp`), the interpolation estimate (8.27)
`FiniteElement.seminorm_sub_lagrangeInterp_le`, and `ε φ^{UP}(Pe)/ε_h ≤ Pe = |β| h/(2ε)`. -/
theorem seminorm_sub_stabilized_le_upwind (hab : a < b) {n : ℕ} {x : ℕ → ℝ}
    (hx : Spline.IsPartition a b n x) (hn : 1 ≤ n) {ε β h : ℝ} (hε : 0 < ε)
    (hmesh : ∀ k < n, x (k + 1) - x k ≤ h) {ℓ : SobolevInterval 1 a b →L[ℝ] ℝ}
    {u uh : SobolevInterval 1 a b} (U : SobolevInterval 2 a b)
    (hU : SobolevInterval.inclusionCLM 1 a b U = u) (hu : u ∈ SobolevIntervalZero a b)
    (hexact : ∀ v ∈ FiniteElement.lagrangeSpaceZero hab n x 1,
      EllipticInterval.form a b (constLinf a b ε) (constLinf a b β) 0 u v = ℓ v)
    (hdisc : IsGalerkinSolution (stabilizedForm a b ε β h phiUpwind) ℓ
      (FiniteElement.lagrangeSpaceZero hab n x 1) uh) :
    SobolevInterval.seminorm 1 a b (u - uh)
      ≤ (2 + (b - a) / Real.sqrt 2 * |β| / ε + |β| / (2 * ε)) * h
        * (SobolevInterval.seminorm 1 a b u + SobolevInterval.seminorm 2 a b U) := by
  have hh : 0 ≤ h := by
    have e1 := hx.step 0 hn
    have e2 := hmesh 0 hn
    linarith
  have hPe : 0 ≤ localPeclet β h ε := localPeclet_nonneg hh hε.le
  have hφ : 0 ≤ phiUpwind (localPeclet β h ε) := hPe
  have hεh : 0 < viscosity ε β h phiUpwind := viscosity_pos hε hφ
  have hεle : ε ≤ viscosity ε β h phiUpwind := by
    rw [viscosity]
    nlinarith
  have key := seminorm_sub_stabilized_le hab hε hφ
    (FiniteElement.lagrangeSpaceZero_le_sobolevIntervalZero hab n x 1) hu hexact hdisc
    (FiniteElement.lagrangeInterp_mem_lagrangeSpaceZero hab hx hn hu)
  -- the interpolation error
  have hinterp : SobolevInterval.seminorm 1 a b (u - FiniteElement.lagrangeInterp hx hn u)
      ≤ h * SobolevInterval.seminorm 2 a b U := by
    have h1 := FiniteElement.seminorm_sub_lagrangeInterp_le hab hx hn hmesh U
    rwa [hU] at h1
  -- the two constants
  have hCP : 0 ≤ (b - a) / Real.sqrt 2 := by
    have := hab.le
    positivity
  have hc1 : 1 + (viscosity ε β h phiUpwind + (b - a) / Real.sqrt 2 * |β|)
        / viscosity ε β h phiUpwind ≤ 2 + (b - a) / Real.sqrt 2 * |β| / ε := by
    rw [add_div, div_self hεh.ne', ← add_assoc]
    have : (b - a) / Real.sqrt 2 * |β| / viscosity ε β h phiUpwind
        ≤ (b - a) / Real.sqrt 2 * |β| / ε :=
      div_le_div_of_nonneg_left (by positivity) hε hεle
    linarith
  have hc2 : ε * phiUpwind (localPeclet β h ε) / viscosity ε β h phiUpwind
      ≤ |β| / (2 * ε) * h := by
    have hle : ε * phiUpwind (localPeclet β h ε) / viscosity ε β h phiUpwind
        ≤ ε * phiUpwind (localPeclet β h ε) / ε :=
      div_le_div_of_nonneg_left (by positivity) hε hεle
    refine hle.trans (le_of_eq ?_)
    simp only [phiUpwind, localPeclet]
    field_simp
  -- assembling
  have h1 : 0 ≤ SobolevInterval.seminorm 1 a b u := apply_nonneg _ _
  have h2 : 0 ≤ SobolevInterval.seminorm 2 a b U := apply_nonneg _ _
  have h3 : 0 ≤ SobolevInterval.seminorm 1 a b (u - FiniteElement.lagrangeInterp hx hn u) :=
    apply_nonneg _ _
  have h4 : 0 ≤ 1 + (viscosity ε β h phiUpwind + (b - a) / Real.sqrt 2 * |β|)
      / viscosity ε β h phiUpwind := by positivity
  have h5 : 0 ≤ ε * phiUpwind (localPeclet β h ε) / viscosity ε β h phiUpwind := by positivity
  refine key.trans ?_
  have hA : (1 + (viscosity ε β h phiUpwind + (b - a) / Real.sqrt 2 * |β|)
        / viscosity ε β h phiUpwind)
      * SobolevInterval.seminorm 1 a b (u - FiniteElement.lagrangeInterp hx hn u)
      ≤ (2 + (b - a) / Real.sqrt 2 * |β| / ε) * (h * SobolevInterval.seminorm 2 a b U) := by
    refine mul_le_mul hc1 hinterp h3 (by linarith)
  have hB : ε * phiUpwind (localPeclet β h ε) / viscosity ε β h phiUpwind
      * SobolevInterval.seminorm 1 a b u
      ≤ |β| / (2 * ε) * h * SobolevInterval.seminorm 1 a b u :=
    mul_le_mul_of_nonneg_right hc2 h1
  have hbeta : 0 ≤ |β| / (2 * ε) := by positivity
  have hba : (0 : ℝ) ≤ b - a := by linarith
  have ha0 : 0 ≤ 2 + (b - a) / Real.sqrt 2 * |β| / ε := by positivity
  calc (1 + (viscosity ε β h phiUpwind + (b - a) / Real.sqrt 2 * |β|)
          / viscosity ε β h phiUpwind)
        * SobolevInterval.seminorm 1 a b (u - FiniteElement.lagrangeInterp hx hn u)
        + ε * phiUpwind (localPeclet β h ε) / viscosity ε β h phiUpwind
          * SobolevInterval.seminorm 1 a b u
      ≤ (2 + (b - a) / Real.sqrt 2 * |β| / ε) * (h * SobolevInterval.seminorm 2 a b U)
        + |β| / (2 * ε) * h * SobolevInterval.seminorm 1 a b u := add_le_add hA hB
    _ ≤ (2 + (b - a) / Real.sqrt 2 * |β| / ε + |β| / (2 * ε)) * h
          * (SobolevInterval.seminorm 1 a b u + SobolevInterval.seminorm 2 a b U) := by
        nlinarith [mul_nonneg (mul_nonneg ha0 hh) h1, mul_nonneg (mul_nonneg hbeta hh) h2]

/-! ### Theorem 12.4 for the Scharfetter-Gummel method -/

section ScharfetterGummelFEM

variable {n : ℕ} {x : ℕ → ℝ}

/-- **The scheme with viscosity in the stencil form of the `P_1` Galerkin method**: multiplying
(12.79) by `h` gives `(ε_h/h)(-u_{i-1} + 2 u_i - u_{i+1}) + (β/2)(u_{i+1} - u_{i-1}) = 0`, the
equation the piecewise linear Galerkin method produces ([quarteroni2000numerical] §12.5.2).
This is `AdvectionDiffusion.viscosityScheme_zero_iff` for a general viscosity function. -/
theorem viscosityScheme_iff_galerkinStencil {ε β : ℝ} {n : ℕ} {φ : ℝ → ℝ} (hn : n ≠ 0)
    (u : ℕ → ℝ) :
    viscosityScheme ε β n φ u ↔ u 0 = 0 ∧ u n = 1 ∧ ∀ i, i + 2 ≤ n →
      viscosity ε β (meshWidth n) φ / meshWidth n * (-u i + 2 * u (i + 1) - u (i + 2))
        + β / 2 * (u (i + 2) - u i) = 0 := by
  have hh := meshWidth_pos hn
  rw [viscosityScheme]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun i => imp_congr_right fun _ => ?_))
  rw [show viscosity ε β (meshWidth n) φ / meshWidth n * (-u i + 2 * u (i + 1) - u (i + 2))
        + β / 2 * (u (i + 2) - u i)
      = meshWidth n * (-viscosity ε β (meshWidth n) φ
          * ((u (i + 2) - 2 * u (i + 1) + u i) / meshWidth n ^ 2)
        + β * ((u (i + 2) - u i) / (2 * meshWidth n))) by field_simp; ring]
  exact ⟨fun h => by rw [h, mul_zero], fun h => by
    simpa [hh.ne'] using (mul_eq_zero.1 h).resolve_left hh.ne'⟩

/-- The stabilized form (12.84) in the spelling of `FiniteElement.galerkin_iff_centredScheme`. -/
theorem stabilizedForm_eq_form_constLinf (a b : ℝ) (ε β h : ℝ) (φ : ℝ → ℝ) :
    stabilizedForm a b ε β h φ
      = EllipticInterval.form a b (EllipticInterval.constLinf a b (viscosity ε β h φ))
          (EllipticInterval.constLinf a b β) (EllipticInterval.constLinf a b 0) := by
  rw [stabilizedForm, EllipticInterval.constLinf_zero]

variable {n : ℕ} {x : ℕ → ℝ}

/-- **The `P_1` Scharfetter–Gummel approximation of the model problem is nodally exact**
([quarteroni2000numerical] Remark 12.6): on the uniform mesh of `n` panels of `[0, 1]`, a
continuous piecewise linear `u_h` with `u_h(0) = 0`, `u_h(1) = 1` that solves the stabilized
Galerkin problem (12.84) with the Scharfetter–Gummel viscosity takes the values of the exact
solution (12.70) at every node.  The proof is the chain
`FiniteElement.galerkin_iff_centredScheme` (the Galerkin system is the centred difference scheme
at the viscosity `ε_h`), `AdvectionDiffusion.viscosityScheme_iff_galerkinStencil` and
`AdvectionDiffusion.sg_nodal_exact`. -/
theorem rep_eq_exactSolution_of_galerkin_sg (hx : Spline.IsPartition 0 1 n x) (hn : 1 ≤ n)
    (huni : ∀ k < n, x (k + 1) - x k = meshWidth n) {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β)
    {uh : SobolevInterval 1 0 1} (huh : uh ∈ FiniteElement.lagrangeSpace zero_lt_one n x 1)
    (huh0 : SobolevInterval.rep uh 0 = 0) (huh1 : SobolevInterval.rep uh 1 = 1)
    (hdisc : ∀ v ∈ FiniteElement.lagrangeSpaceZero zero_lt_one n x 1,
      stabilizedForm 0 1 ε β (meshWidth n) phiSG uh v = 0) {i : ℕ} (hi : i ≤ n) :
    SobolevInterval.rep uh (x i) = exactSolution ε β (x i) := by
  have hn0 : n ≠ 0 := by omega
  have hh : 0 < meshWidth n := meshWidth_pos hn0
  set c : ℕ → ℝ := fun j ↦ SobolevInterval.rep uh (x j)
  -- `u_h` is the combination of the hat functions with its nodal values
  have hexp : uh = ∑ j ∈ Finset.range (n + 1), c j • FiniteElement.hatFunction hx hn j :=
    FiniteElement.eq_of_rep_node_eq zero_lt_one hx hn huh
      (FiniteElement.sum_hatFunction_mem_lagrangeSpace zero_lt_one hx hn c)
      fun j hj ↦ (FiniteElement.rep_sum_hatFunction zero_lt_one hx hn c hj).symm
  -- the Galerkin system is the centred stencil at the viscosity `ε_h`
  have hstencil : ∀ j, 1 ≤ j → j < n →
      viscosity ε β (meshWidth n) phiSG / meshWidth n * (-c (j - 1) + 2 * c j - c (j + 1))
        + β / 2 * (c (j + 1) - c (j - 1)) = 0 := by
    refine (FiniteElement.galerkin_iff_centredScheme zero_lt_one hx hn hh huni _ β c).1 ?_
    intro v hv
    have := hdisc v hv
    rwa [stabilizedForm_eq_form_constLinf, hexp] at this
  -- hence the nodal values solve the scheme with viscosity
  have hscheme : viscosityScheme ε β n phiSG c := by
    refine (viscosityScheme_iff_galerkinStencil hn0 c).2 ⟨?_, ?_, fun j hj ↦ ?_⟩
    · change SobolevInterval.rep uh (x 0) = 0
      rw [hx.first]; exact huh0
    · change SobolevInterval.rep uh (x n) = 1
      rw [hx.last]; exact huh1
    · simpa using hstencil (j + 1) (by omega) (by omega)
  have hnodal : SobolevInterval.rep uh (x i) = exactSolution ε β ((i : ℝ) * meshWidth n) :=
    sg_nodal_exact hε hβ hn0 hscheme hi
  rw [hnodal, FiniteElement.node_eq_of_uniform hx huni hi, zero_add]

/-- **Theorem 12.4 for the Scharfetter-Gummel method with `k = 1`**
([quarteroni2000numerical] (12.85)): on the uniform mesh of `n` panels of `[0, 1]` the
`P_1` Scharfetter-Gummel approximation of the model problem (12.70) satisfies

`|ů - ů_h|_{H¹(0,1)} ≤ h |ů|_{H²(0,1)}`,

which is the book's `C h G(ů)` with `G(ů) = |ů|_{H²}` and the constant `C = 1`: the book's
factor `(1 + 2 Pe_gl C_P)` is absent, because by `AdvectionDiffusion.sg_nodal_exact` the
discrete solution is *nodally exact*, so `ů_h = Π_h^1 ů` and the Galerkin error **is** the
interpolation error of (8.27).  The statement is written for the unlifted pair `u`, `u_h` —
`u` the exact solution (12.70) with `u(0) = 0`, `u(1) = 1`, and `u_h ∈ X_h^1` the stabilized
Galerkin solution with the same boundary values — which is the same inequality: the lifting
`ū(x) = x` cancels in `ů - ů_h = u - u_h`, and `|ů|_{H²} = |u|_{H²}` because `ū` is affine. -/
theorem seminorm_sub_stabilized_le_sg (hx : Spline.IsPartition 0 1 n x) (hn : 1 ≤ n)
    (huni : ∀ k < n, x (k + 1) - x k = meshWidth n) {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β)
    {u uh : SobolevInterval 1 0 1} (U : SobolevInterval 2 0 1)
    (hU : SobolevInterval.inclusionCLM 1 0 1 U = u)
    (hunode : ∀ i ≤ n, SobolevInterval.rep u (x i) = exactSolution ε β (x i))
    (huh : uh ∈ FiniteElement.lagrangeSpace zero_lt_one n x 1)
    (huh0 : SobolevInterval.rep uh 0 = 0) (huh1 : SobolevInterval.rep uh 1 = 1)
    (hdisc : ∀ v ∈ FiniteElement.lagrangeSpaceZero zero_lt_one n x 1,
      stabilizedForm 0 1 ε β (meshWidth n) phiSG uh v = 0) :
    SobolevInterval.seminorm 1 0 1 (u - uh)
      ≤ meshWidth n * SobolevInterval.seminorm 2 0 1 U := by
  have heq : uh = FiniteElement.lagrangeInterp hx hn u :=
    FiniteElement.eq_of_rep_node_eq zero_lt_one hx hn huh
      (FiniteElement.lagrangeInterp_mem_lagrangeSpace zero_lt_one hx hn u)
      fun i hi ↦ by
        rw [rep_eq_exactSolution_of_galerkin_sg hx hn huni hε hβ huh huh0 huh1 hdisc hi,
          FiniteElement.rep_lagrangeInterp_node zero_lt_one hx hn u hi, hunode i hi]
  rw [heq, ← hU]
  exact FiniteElement.seminorm_sub_lagrangeInterp_le zero_lt_one hx hn
    (fun k hk ↦ le_of_eq (huni k hk)) U

/-- **Theorem 12.4 for the Scharfetter-Gummel method with `k = 2`**
([quarteroni2000numerical] (12.86)): on a quadratic mesh `x_0 < x_1 < ⋯ < x_{2n}` whose `n`
elements `[x_{2m}, x_{2m+2}]` have length at most `h`, with the `P_2` finite element space
`X_h^{2,0}` as trial space, the Scharfetter–Gummel-stabilized Galerkin error satisfies
`|ů - ů_h|_{H¹} ≤ C h² (|ů|_{H¹} + |ů|_{H³})` with `C = 2 + C_P |β|/ε + β²/(12 ε²)`
independent of `h` and of `ů`.  This is `AdvectionDiffusion.seminorm_sub_stabilized_le` with
`w = Π_h^2 ů` (`FiniteElement.quadraticInterp`), the interpolation estimate (8.26) at `k = 2`,
`m = 1` (`FiniteElement.seminorm_sub_quadraticInterp_le`), and
`ε φ^{SG}(Pe)/ε_h ≤ φ^{SG}(Pe) ≤ Pe²/3 = β² h²/(12 ε²)` (`AdvectionDiffusion.phiSG_le_sq`): the
Scharfetter–Gummel consistency defect is second order in `h` where the upwind one
(`seminorm_sub_stabilized_le_upwind`) is only first order, which is what upgrades the rate of
(12.85) to that of (12.86). -/
theorem seminorm_sub_stabilized_le_sg_quadratic (hab : a < b)
    (hx : Spline.IsPartition a b (2 * n) x) (hn : 1 ≤ n) {ε β h : ℝ} (hε : 0 < ε)
    (hmesh : ∀ m < n, x (2 * m + 2) - x (2 * m) ≤ h)
    {ℓ : SobolevInterval 1 a b →L[ℝ] ℝ} {u uh : SobolevInterval 1 a b}
    (U : SobolevInterval 3 a b)
    (hU : SobolevInterval.inclusionCLM 1 a b (SobolevInterval.inclusionCLM 2 a b U) = u)
    (hu : u ∈ SobolevIntervalZero a b)
    (hexact : ∀ v ∈ FiniteElement.lagrangeSpaceZero hab n (FiniteElement.evenNodes x) 2,
      EllipticInterval.form a b (constLinf a b ε) (constLinf a b β) 0 u v = ℓ v)
    (hdisc : IsGalerkinSolution (stabilizedForm a b ε β h phiSG) ℓ
      (FiniteElement.lagrangeSpaceZero hab n (FiniteElement.evenNodes x) 2) uh) :
    SobolevInterval.seminorm 1 a b (u - uh)
      ≤ (2 + (b - a) / Real.sqrt 2 * |β| / ε + β ^ 2 / (12 * ε ^ 2)) * h ^ 2
        * (SobolevInterval.seminorm 1 a b u + SobolevInterval.seminorm 3 a b U) := by
  have hh : 0 ≤ h := by
    have e1 : x (2 * 0) < x (2 * 0 + 2) := hx.lt (by omega) (by omega)
    have e2 := hmesh 0 hn
    linarith
  have hPe : 0 ≤ localPeclet β h ε := localPeclet_nonneg hh hε.le
  have hφ : 0 ≤ phiSG (localPeclet β h ε) := phiSG_nonneg hPe
  have hεh : 0 < viscosity ε β h phiSG := viscosity_pos hε hφ
  have hεle : ε ≤ viscosity ε β h phiSG := by
    rw [viscosity]
    nlinarith
  have key := seminorm_sub_stabilized_le hab hε hφ
    (FiniteElement.lagrangeSpaceZero_le_sobolevIntervalZero hab n (FiniteElement.evenNodes x) 2)
    hu hexact hdisc (FiniteElement.quadraticInterp_mem_lagrangeSpaceZero hab hx hn hu)
  -- the interpolation error, (8.26) with `k = 2`, `m = 1`
  have hinterp : SobolevInterval.seminorm 1 a b (u - FiniteElement.quadraticInterp hab hx hn u)
      ≤ h ^ 2 * SobolevInterval.seminorm 3 a b U := by
    have h1 := FiniteElement.seminorm_sub_quadraticInterp_le hab hx hn hmesh U
    rwa [hU] at h1
  -- the two constants
  have hCP : 0 ≤ (b - a) / Real.sqrt 2 := by
    have := hab.le
    positivity
  have hc1 : 1 + (viscosity ε β h phiSG + (b - a) / Real.sqrt 2 * |β|)
        / viscosity ε β h phiSG ≤ 2 + (b - a) / Real.sqrt 2 * |β| / ε := by
    rw [add_div, div_self hεh.ne', ← add_assoc]
    have : (b - a) / Real.sqrt 2 * |β| / viscosity ε β h phiSG
        ≤ (b - a) / Real.sqrt 2 * |β| / ε :=
      div_le_div_of_nonneg_left (by positivity) hε hεle
    linarith
  have hc2 : ε * phiSG (localPeclet β h ε) / viscosity ε β h phiSG
      ≤ β ^ 2 / (12 * ε ^ 2) * h ^ 2 := by
    have hle : ε * phiSG (localPeclet β h ε) / viscosity ε β h phiSG
        ≤ ε * phiSG (localPeclet β h ε) / ε :=
      div_le_div_of_nonneg_left (by positivity) hε hεle
    refine hle.trans ?_
    rw [mul_div_cancel_left₀ _ hε.ne']
    refine (phiSG_le_sq hPe).trans (le_of_eq ?_)
    rw [localPeclet, div_pow, mul_pow, sq_abs]
    field_simp
    ring
  -- assembling
  have h1 : 0 ≤ SobolevInterval.seminorm 1 a b u := apply_nonneg _ _
  have h2 : 0 ≤ SobolevInterval.seminorm 3 a b U := apply_nonneg _ _
  have h3 : 0 ≤ SobolevInterval.seminorm 1 a b
      (u - FiniteElement.quadraticInterp hab hx hn u) := apply_nonneg _ _
  have hbeta : 0 ≤ β ^ 2 / (12 * ε ^ 2) := by positivity
  have ha0 : 0 ≤ 2 + (b - a) / Real.sqrt 2 * |β| / ε := by positivity
  have hh2 : 0 ≤ h ^ 2 := sq_nonneg h
  refine key.trans ?_
  have hA : (1 + (viscosity ε β h phiSG + (b - a) / Real.sqrt 2 * |β|)
        / viscosity ε β h phiSG)
      * SobolevInterval.seminorm 1 a b (u - FiniteElement.quadraticInterp hab hx hn u)
      ≤ (2 + (b - a) / Real.sqrt 2 * |β| / ε)
        * (h ^ 2 * SobolevInterval.seminorm 3 a b U) :=
    mul_le_mul hc1 hinterp h3 ha0
  have hB : ε * phiSG (localPeclet β h ε) / viscosity ε β h phiSG
        * SobolevInterval.seminorm 1 a b u
      ≤ β ^ 2 / (12 * ε ^ 2) * h ^ 2 * SobolevInterval.seminorm 1 a b u :=
    mul_le_mul_of_nonneg_right hc2 h1
  calc (1 + (viscosity ε β h phiSG + (b - a) / Real.sqrt 2 * |β|)
          / viscosity ε β h phiSG)
        * SobolevInterval.seminorm 1 a b (u - FiniteElement.quadraticInterp hab hx hn u)
        + ε * phiSG (localPeclet β h ε) / viscosity ε β h phiSG
          * SobolevInterval.seminorm 1 a b u
      ≤ (2 + (b - a) / Real.sqrt 2 * |β| / ε) * (h ^ 2 * SobolevInterval.seminorm 3 a b U)
        + β ^ 2 / (12 * ε ^ 2) * h ^ 2 * SobolevInterval.seminorm 1 a b u := add_le_add hA hB
    _ ≤ (2 + (b - a) / Real.sqrt 2 * |β| / ε + β ^ 2 / (12 * ε ^ 2)) * h ^ 2
          * (SobolevInterval.seminorm 1 a b u + SobolevInterval.seminorm 3 a b U) := by
        nlinarith [mul_nonneg (mul_nonneg ha0 hh2) h1, mul_nonneg (mul_nonneg hbeta hh2) h2]

end ScharfetterGummelFEM

end Form

end AdvectionDiffusion
