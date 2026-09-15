import NumlibSurface.QuarteroniSaccoSaleri.Chapter13.Section08

/-!
# Quarteroni–Sacco–Saleri §13.9: dissipation and dispersion

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §13.9 and §13.9.1.

The exact solution of (13.26) multiplies the `k`-th harmonic by `g_k = e^{-i a k Δt}` per time
step (13.54), which with the phase angle `φ_k = k Δx` is `e^{-i a λ φ_k}` (13.55); its modulus is
`1`. A numerical scheme multiplies it by `γ_k` instead, and the two comparisons are the
*amplification error* `ε_a(k) = |γ_k|/|g_k| = |γ_k|` (dissipation) and the *dispersion error*
`ε_d(k) = ω/(k a) = -arg γ_k/(a λ φ_k)`, the ratio of the numerical phase speed to `a`.

§13.9.1 associates with each scheme an *equivalent* (modified) equation
`v_t + a v_x = μ v_xx + ν v_xxx` (13.56), whose second-order term is dissipative and whose
third-order term is dispersive. That reading is justified by (13.61)–(13.63): the Fourier mode
solution is `v(x, t) = e^{-μk²t} e^{ik[x - (a + νk²)t]}`, so `μ` damps the amplitude (the more so at
high `k`) and `ν` shifts the phase speed to `a + νk²`. The coefficients of Table 13.2 for upwind,
Lax–Friedrichs and Lax–Wendroff are the content of (13.59)–(13.60) and Exercise 8; they are
stated in the backbone as *higher-order consistency with the modified equation* and are not yet
proved (see the plan).

Erratum: the text's `ν = (a/6)(a²Δt² - Δx²)` for upwind after (13.60) disagrees with Table 13.2's
`-(a/6)(Δx² - 3aΔxΔt + 2a²Δt²)`; the table is the correct (Warming–Hyett) value.

Figures 13.7–13.9 are plots and are not formalized.
-/

open FiniteDifference

namespace QuarteroniSaccoSaleri.Chapter13

/-! ### The exact amplification and the two errors -/

/-- **(13.54)–(13.55)**: the exact solution multiplies the `k`-th harmonic by
`g_k = e^{-i a k Δt}` per time step, `g_k^n = e^{-i a k n Δt}`, and with the phase angle
`φ_k = k Δx` this is `e^{-i a λ φ_k}` (Quarteroni–Sacco–Saleri, *Numerical Mathematics*,
equations (13.54)–(13.55)). -/
theorem equation_13_54 {Δt Δx lam : ℝ} (hΔx : Δx ≠ 0) (hlam : lam = Δt / Δx) (a : ℝ) (k : ℤ) :
    Hyperbolic.exactAmplification a Δt k = Complex.exp (-(Complex.I * a * k * Δt)) ∧
      (∀ n : ℕ, Hyperbolic.exactAmplification a Δt k ^ n
          = Complex.exp (-(Complex.I * a * k * ((n : ℝ) * Δt)))) ∧
        Hyperbolic.exactAmplification a Δt k
          = Complex.exp (-(Complex.I * ((a * lam * Hyperbolic.phaseAngle k Δx : ℝ) : ℂ))) :=
  ⟨rfl, Hyperbolic.exactAmplification_pow a Δt k,
    Hyperbolic.exactAmplification_eq_phaseAngle hΔx hlam a k⟩

/-- **The amplification (dissipation) error** of the `k`-th harmonic, `ε_a(k) = |γ_k|/|g_k|`,
which is `|γ_k|` because `|g_k| = 1`. -/
noncomputable def amplificationError (γ : ℂ) : ℝ := Hyperbolic.amplificationError γ

/-- **The dispersion error** of the `k`-th harmonic: writing `γ_k = |γ_k| e^{-iωΔt}`, the ratio
`ω/(k a)` of the numerical phase speed to the exact one is `-arg γ_k / (a λ φ_k)`. -/
noncomputable def dispersionError (a lam phi : ℝ) (γ : ℂ) : ℝ :=
  Hyperbolic.dispersionError a lam phi γ

/-- **The exact factor has no dissipation and no dispersion**: `|g_k| = 1`, so `ε_a = 1`, and
`ε_d = 1` as long as the phase is unambiguous (Quarteroni–Sacco–Saleri, *Numerical Mathematics*,
§13.9). -/
theorem amplificationError_exact {a lam Δt Δx : ℝ} {k : ℤ} (hΔx : Δx ≠ 0)
    (hlam : lam = Δt / Δx) (h0 : a * lam * Hyperbolic.phaseAngle k Δx ≠ 0)
    (hpi : |a * lam * Hyperbolic.phaseAngle k Δx| < Real.pi) :
    ‖Hyperbolic.exactAmplification a Δt k‖ = 1 ∧
      amplificationError (Hyperbolic.exactAmplification a Δt k) = 1 ∧
        dispersionError a lam (Hyperbolic.phaseAngle k Δx)
          (Hyperbolic.exactAmplification a Δt k) = 1 :=
  ⟨Hyperbolic.norm_exactAmplification a Δt k,
    Hyperbolic.amplificationError_exactAmplification a Δt k,
    Hyperbolic.dispersionError_exactAmplification hΔx hlam h0 hpi⟩

/-! ### §13.9.1, the equivalent equations -/

/-- **(13.56)**, the equivalent (modified) equation `v_t + a v_x = μ v_xx + ν v_xxx`: `v` is a
classical solution when it has partial derivatives up to the third order in `x` and satisfies the
identity everywhere. -/
def equation_13_56 (a mu nu : ℝ) (v : ℝ → ℝ → ℝ) : Prop :=
  Hyperbolic.IsModifiedSolution a mu nu v

/-- **(13.61)–(13.63)**: the Fourier-mode solution of the equivalent equation. The exponential
ansatz `v(x, t) = e^{ikx + σt}` satisfies `v_t + a v_x = μ v_xx + ν v_xxx` exactly when
`σ + a(ik) = μ(ik)² + ν(ik)³`, which holds for `σ = -μk² - ik(a + νk²)` (the first clause); that
`v` factors as `e^{-μk²t} e^{ik[x - (a + νk²)t]}` (13.63) (the second clause), starts from
`e^{ikx}` (the third) and has modulus `e^{-μk²t}` (the fourth). So `μ` damps the amplitude, the
more strongly the higher the frequency, and `ν` changes the propagation speed from `a` to
`a + νk²`; for `μ = ν = 0` one recovers `e^{ik(x - at)}` (13.62)
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, equations (13.61)–(13.63)). -/
theorem equation_13_63 (a mu nu : ℝ) (k : ℤ) :
    -(mu * (k : ℂ) ^ 2) - Complex.I * k * (a + nu * (k : ℂ) ^ 2)
          + a * (Complex.I * k)
        = mu * (Complex.I * (k : ℂ)) ^ 2 + nu * (Complex.I * (k : ℂ)) ^ 3 ∧
      (∀ x t : ℝ, Complex.exp (Complex.I * k * x
            + (-(mu * (k : ℂ) ^ 2) - Complex.I * k * (a + nu * (k : ℂ) ^ 2)) * t)
          = (Real.exp (-(mu * (k : ℝ) ^ 2) * t) : ℂ)
            * Complex.exp (Complex.I * k * ((x : ℂ) - (a + nu * (k : ℝ) ^ 2) * t))) ∧
        (∀ x : ℝ, Complex.exp (Complex.I * k * x
            + (-(mu * (k : ℂ) ^ 2) - Complex.I * k * (a + nu * (k : ℂ) ^ 2)) * (0 : ℝ))
          = Complex.exp (Complex.I * k * x)) ∧
          ∀ x t : ℝ, ‖Complex.exp (Complex.I * k * x
              + (-(mu * (k : ℂ) ^ 2) - Complex.I * k * (a + nu * (k : ℂ) ^ 2)) * t)‖
            = Real.exp (-(mu * (k : ℝ) ^ 2) * t) := by
  have hI2 : (Complex.I * (k : ℂ)) ^ 2 = -((k : ℂ) ^ 2) := by
    rw [mul_pow, Complex.I_sq]; ring
  have hI3 : (Complex.I * (k : ℂ)) ^ 3 = -(Complex.I * (k : ℂ) ^ 3) := by
    rw [mul_pow, show Complex.I ^ 3 = -Complex.I by rw [pow_succ, Complex.I_sq]; ring]; ring
  refine ⟨by rw [hI2, hI3]; ring, fun x t => ?_, fun x => by norm_num, fun x t => ?_⟩
  · rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · rw [Complex.norm_exp]
    congr 1
    have hre : ((k : ℂ) ^ 2).re = (k : ℝ) ^ 2 := by
      rw [show ((k : ℂ) ^ 2) = ((k ^ 2 : ℤ) : ℂ) from by push_cast; ring, Complex.intCast_re]
      push_cast
      ring
    have him : ((k : ℂ) ^ 2).im = 0 := by
      rw [show ((k : ℂ) ^ 2) = ((k ^ 2 : ℤ) : ℂ) from by push_cast; ring, Complex.intCast_im]
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im, hre, him]
    try ring

end QuarteroniSaccoSaleri.Chapter13
