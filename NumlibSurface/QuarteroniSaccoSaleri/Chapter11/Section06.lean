import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section03
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section05

/-!
# Quarteroni–Sacco–Saleri §11.6: analysis of multistep methods

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §11.6.

The consistency and order conditions (Theorem 11.3, (11.52)–(11.53)); the method on the test
problem (11.54) and the characteristic polynomials `ρ`, `σ`, `Π` (11.55) with the consistency
root; the root condition (Definition 11.10, (11.56)), the strong root condition (Definition
11.11, (11.57)) and the absolute root condition (Definition 11.12); zero-stability (Definition
11.13, (11.58)–(11.60)), its equivalence with the root condition (Theorem 11.4), Lemma 11.3 and
the estimate (11.65); the zero-stability of the one-step, Adams, midpoint, Simpson and BDF
methods (§11.6.3); convergence (Theorem 11.5) and the equivalence theorem (Corollary 11.1);
absolute stability of multistep methods, A- and ϑ-stability, the explicit clause of the second
Dahlquist barrier (Property 11.2), the region `𝒜*` of Remark 11.3 and relative stability
(11.66).

Everything is the scalar case `E = ℝ` of `Numlib/ODE/Multistep` — the test problem on `ℂ` — with
`Numlib/ODE/DifferenceEquation` for Lemma 11.3. The Dahlquist barriers (Property 11.1 and the
order and ϑ-stability clauses of Property 11.2) and the zero-stability of the BDF methods with
`p ≥ 3` are not formalized; see `## Not formalized here` below.

## Main definitions

* `characteristicPolynomials M`, `equation_11_55 M z` — `(ρ, σ)` and `Π = ρ - z σ`.
* `definition_11_10 M`, `definition_11_11 M`, `definition_11_12 M λ` — the root conditions.
* `equation_11_59 M f h t₀ δ z`, `definition_11_13 M f t₀ T` — the perturbed recursion and
  zero-stability.
* `absolutelyStable M λ h`, `equation_11_26_multistep M`, `aStableMultistep M`,
  `thetaStable M ϑ`, `remark_11_3 M`, `equation_11_66 M λ h₀ T` — absolute stability.

## Main results

* `theorem_11_3`, `theorem_11_3_order` — consistency and order through the coefficients.
* `equation_11_54` — the method on the test problem is a linear difference equation.
* `theorem_11_4`, `lemma_11_3`, `equation_11_65` — zero-stability and the root condition.
* `oneStep_zeroStable`, `adams_zeroStable`, `midpoint_zeroStable`, `simpson_zeroStable`,
  `bdf_zeroStable_of_le_two`, `bdf_zeroStable` — the classical methods.
* `theorem_11_5`, `theorem_11_5_mpr`, `theorem_11_5_order`, `theorem_11_5_mp`,
  `corollary_11_1` — convergence.
* `absoluteStability`, `property_11_2_explicit`, `remark_11_3_midpoint`,
  `remark_11_3_zeroStable` — absolute stability.

## Not formalized here

* **Property 11.1, the first Dahlquist barrier**: no zero-stable `p`-step linear multistep method
  has order greater than `p + 1` when `p` is odd, or `p + 2` when `p` is even. The vocabulary is
  complete, so the statement can be written down —
  `M.p + 1 = p → M.SatisfiesRootCondition → M.HasOrder q → q ≤ p + (if Even p then 2 else 1)`,
  in the backbone's `ODE.LinearMultistep` and `HasOrder`, the algebraic order conditions
  `orderCondition` with `orderCondition_iff_taylorCoeff_eq_zero` (Theorem 11.3), the
  characteristic polynomials `characteristicPolynomials` and `Polynomial.SatisfiesRootCondition`
  (Definition 11.10) — and it is the *proof* that is missing. Dahlquist's argument (Dahlquist
  1956; Hairer–Nørsett–Wanner I, III.3, Theorem 3.5) runs through the Möbius transform
  `z ↦ (1+z)/(1-z)`, which carries the closed unit disc onto a half-plane, the expansion of
  `(ρ/σ)(ζ) - log ζ` in `z`, and the positivity of the coefficients of power series of the type
  `z/log((1+z)/(1-z))` together with a count of sign changes forced by the root condition.
  Nothing named Dahlquist, Herglotz or "positive real" is in Mathlib or in `Numlib/` — the
  Dahlquist–Golub–Nash identity of `Numlib/Krylov` is unrelated — and the book quotes the result
  from [Dah63] without proof. Estimate: 1500–2500 lines of complex analysis on power series with
  real coefficients, a module of its own (`ODE/Multistep/Dahlquist`).
* **Property 11.2, the second Dahlquist barrier**, except its explicit clause. The property has
  three clauses: an explicit linear multistep method is neither A-stable nor ϑ-stable; no
  A-stable linear multistep method has order greater than `2`; and for every `ϑ ∈ (0, π/2)` there
  are ϑ-stable `p`-step methods of order `p` only for `p = 3` and `p = 4` (as printed; the
  standard statement, Widlund 1967, is that such methods *exist* for `p = 3, 4`, the trapezoidal
  rule having the smallest error constant among A-stable methods). The **explicit clause is
  proved** here, as `property_11_2_explicit`: `Π` is then a polynomial of degree `p + 1` in `r`
  whose roots cannot all stay in the disc as `|z| → ∞`. The order-two barrier is statable —
  `absoluteStability` and `thetaStable` (Definitions 11.11–11.13) exist, so it reads
  `M.IsAStable → M.HasOrder q → q ≤ 2` — but its proof (Dahlquist 1963; Hairer–Wanner II, V.1,
  Theorem 1.4) needs, beyond the first barrier's Möbius transform, a Riesz–Herglotz positivity
  argument: a function with nonnegative real part on the disc has a nonnegative error constant.
  The ϑ-stability clause is Widlund's theorem and is existential — a construction plus a
  stability-region computation for two specific methods. The book quotes all of it without proof
  ([Wid67]). Estimate: ~500 lines for the order-two barrier once the Möbius transform of
  Property 11.1 exists, inside the same 1500–2500 line module.

## Conventions

As in §11.5: a method is `M : ODE.LinearMultistep` with `a_j = M.a j`, `b_j = M.b j`,
`b_{-1} = M.bm1` and `M.p + 1` steps. The book's Lipschitz hypothesis "`f` Lipschitz in `y`
uniformly on `[t₀, t₀ + T]`" is `∀ t ∈ [t₀, t₀ + T], ∀ y₁ y₂, |f(t, y₁) - f(t, y₂)| ≤ L |y₁ - y₂|`.
A solution of the Cauchy problem enters Theorem 11.5 through `HasDerivAt y (f t (y t)) t` on
the closed horizon, the two-sided derivative the local truncation error (Definition 11.8) is
built from.
-/

open Set Filter Topology Asymptotics ODE Polynomial
open Finset (range)

namespace QuarteroniSaccoSaleri.Chapter11

variable {f : ℝ → ℝ → ℝ} {t₀ T h t : ℝ} {y : ℝ → ℝ} {n : ℕ}

/-! ### Theorem 11.3: consistency and order through the coefficients -/

/-- **Theorem 11.3 (consistency)**: the multistep method (11.45) is consistent iff
`∑_{j=0}^p a_j = 1` and `-∑_{j=0}^p j a_j + ∑_{j=-1}^p b_j = 1` (11.52);
`ODE.LinearMultistep.isConsistent_iff`. -/
theorem theorem_11_3 (M : LinearMultistep) :
    definition_11_9_method M ↔
      ∑ j, M.a j = 1 ∧ -∑ j : Fin (M.p + 1), (j : ℝ) * M.a j + (M.bm1 + ∑ j, M.b j) = 1 := by
  rw [definition_11_9_method, LinearMultistep.isConsistent_iff, LinearMultistep.orderCondition_zero,
    LinearMultistep.orderCondition_one]

/-- **Theorem 11.3 (order)**: for `q ≥ 1`, the method has order `q` iff it is consistent and
`∑_{j=0}^p (-j)^i a_j + i ∑_{j=-1}^p (-j)^{i-1} b_j = 1` for `i = 2, …, q` (11.53);
`ODE.LinearMultistep.hasOrder_iff`. -/
theorem theorem_11_3_order (M : LinearMultistep) {q : ℕ} (hq : 1 ≤ q) :
    definition_11_9_order_method M q ↔
      (∑ j, M.a j = 1 ∧ -∑ j : Fin (M.p + 1), (j : ℝ) * M.a j + (M.bm1 + ∑ j, M.b j) = 1) ∧
        ∀ i, 2 ≤ i → i ≤ q → ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ i * M.a j +
          i * (M.bm1 + ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ (i - 1) * M.b j) = 1 := by
  rw [definition_11_9_order_method, LinearMultistep.hasOrder_iff]
  constructor
  · intro H
    exact ⟨⟨(LinearMultistep.orderCondition_zero M).1 (H 0 (Nat.zero_le q)),
      (LinearMultistep.orderCondition_one M).1 (H 1 hq)⟩, fun i _ hiq => H i hiq⟩
  · rintro ⟨⟨h0, h1⟩, H⟩ i hi
    match i with
    | 0 => exact (LinearMultistep.orderCondition_zero M).2 h0
    | 1 => exact (LinearMultistep.orderCondition_one M).2 h1
    | i + 2 => exact H (i + 2) (by omega) hi

/-! ### (11.54)–(11.55): the test problem and the characteristic polynomials -/

/-- **The first and second characteristic polynomials (§11.6.2)**
`ρ(r) = r^{p+1} - ∑_{j=0}^p a_j r^{p-j}` and `σ(r) = b_{-1} r^{p+1} + ∑_{j=0}^p b_j r^{p-j}`;
`ODE.LinearMultistep.rho`, `ODE.LinearMultistep.sigma`. -/
noncomputable def characteristicPolynomials (M : LinearMultistep) : ℝ[X] × ℝ[X] :=
  (M.rho, M.sigma)

/-- `ρ` and `σ`, evaluated. -/
theorem characteristicPolynomials_eval (M : LinearMultistep) (r : ℝ) :
    (characteristicPolynomials M).1.eval r =
        r ^ (M.p + 1) - ∑ j : Fin (M.p + 1), M.a j * r ^ (M.p - j) ∧
      (characteristicPolynomials M).2.eval r =
        M.bm1 * r ^ (M.p + 1) + ∑ j : Fin (M.p + 1), M.b j * r ^ (M.p - j) :=
  ⟨M.eval_rho r, M.eval_sigma r⟩

/-- `ρ` is monic of degree `p + 1`. -/
theorem characteristicPolynomials_degree (M : LinearMultistep) :
    (characteristicPolynomials M).1.Monic ∧ (characteristicPolynomials M).1.degree = M.p + 1 :=
  ⟨M.rho_monic, M.degree_rho⟩

/-- **The characteristic polynomial (11.55)** `Π(r) = ρ(r) - hλ σ(r)` of the method on the test
problem, at `z = hλ ∈ ℂ`; `ODE.LinearMultistep.charPoly`. -/
noncomputable def equation_11_55 (M : LinearMultistep) (z : ℂ) : ℂ[X] :=
  M.charPoly z

/-- (11.55), unfolded: `Π = ρ - z σ` in `ℂ[X]`, and `Π(0) = ρ`. -/
theorem equation_11_55_eq (M : LinearMultistep) (z : ℂ) :
    equation_11_55 M z = (characteristicPolynomials M).1.map (algebraMap ℝ ℂ) -
        C z * (characteristicPolynomials M).2.map (algebraMap ℝ ℂ) ∧
      equation_11_55 M 0 = (characteristicPolynomials M).1.map (algebraMap ℝ ℂ) :=
  ⟨rfl, M.charPoly_zero⟩

/-- **The consistency root** (§11.6.2): a consistent method has `ρ(1) = 0` — `r_0 = 1` is a root
of `ρ` — and moreover `ρ'(1) = σ(1)`; `ODE.LinearMultistep.rho_isRoot_one`,
`ODE.LinearMultistep.derivative_rho_eval_one_eq_sigma`. -/
theorem consistencyRoot (M : LinearMultistep) (hM : definition_11_9_method M) :
    (characteristicPolynomials M).1.IsRoot 1 ∧
      (derivative (characteristicPolynomials M).1).eval 1 =
        (characteristicPolynomials M).2.eval 1 := by
  rw [definition_11_9_method, LinearMultistep.isConsistent_iff] at hM
  exact ⟨M.rho_isRoot_one hM.1, M.derivative_rho_eval_one_eq_sigma hM.1 hM.2⟩

/-- **(11.54), the method on the test problem**: applied to `y' = λy`, `y(0) = 1` (11.24) the
method (11.45) gives the linear difference equation
`u_{n+1} = ∑_{j=0}^p a_j u_{n-j} + hλ ∑_{j=-1}^p b_j u_{n-j}`, `n ≥ p`, and for `1 - hλ b_{-1} ≠ 0`
its solutions are those of the homogeneous linear recurrence
`ODE.LinearMultistep.toLinearRecurrence M (hλ)` of order `p + 1`, whose characteristic polynomial
is `Π(hλ)` up to the factor `(1 - hλ b_{-1})⁻¹`; `ODE.LinearMultistep.isOrbit_testField_iff`,
`ODE.LinearMultistep.charPoly_toLinearRecurrence`. -/
theorem equation_11_54 (M : LinearMultistep) (lam : ℂ) (u : ℕ → ℂ) :
    (M.IsOrbit (testProblem lam) h 0 u ↔ ∀ n, M.p ≤ n → u (n + 1) =
      ∑ j : Fin (M.p + 1), (M.a j : ℂ) * u (n - j) +
        h * lam * (∑ j : Fin (M.p + 1), (M.b j : ℂ) * u (n - j) + M.bm1 * u (n + 1))) ∧
    (1 - (h : ℂ) * lam * M.bm1 ≠ 0 →
      (M.IsOrbit (testProblem lam) h 0 u ↔ (M.toLinearRecurrence (h * lam)).IsSolution u) ∧
      (M.toLinearRecurrence (h * lam)).charPoly =
        C (1 - (h : ℂ) * lam * M.bm1)⁻¹ * equation_11_55 M (h * lam)) := by
  refine ⟨?_, fun hz => ⟨M.isOrbit_testField_iff hz, M.charPoly_toLinearRecurrence hz⟩⟩
  rw [LinearMultistep.isOrbit_iff]
  simp only [testProblem, testField, Complex.real_smul, Complex.ofReal_mul]
  have key : ∀ m, ∑ j : Fin (M.p + 1), (M.a j : ℂ) * u (m + M.p - j) +
      h * ∑ j : Fin (M.p + 1), (M.b j : ℂ) * (lam * u (m + M.p - j)) +
      h * M.bm1 * (lam * u (m + M.p + 1)) =
      ∑ j : Fin (M.p + 1), (M.a j : ℂ) * u (m + M.p - j) +
      h * lam * (∑ j : Fin (M.p + 1), (M.b j : ℂ) * u (m + M.p - j) + M.bm1 * u (m + M.p + 1)) := by
    intro m
    have hS : ∑ j : Fin (M.p + 1), (M.b j : ℂ) * (lam * u (m + M.p - j)) =
        lam * ∑ j : Fin (M.p + 1), (M.b j : ℂ) * u (m + M.p - j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hS]
    ring
  constructor
  · intro H n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact (H m).trans (key m)
  · intro H n
    exact (H (n + M.p) (Nat.le_add_left _ _)).trans (key n).symm

/-! ### Definitions 11.10–11.12: the root conditions -/

/-- **Definition 11.10 (the root condition, (11.56))**: the roots `r_j` of `ρ` (in `ℂ`) satisfy
`|r_j| ≤ 1`, and those with `|r_j| = 1` are simple; `ODE.LinearMultistep.SatisfiesRootCondition`.
-/
def definition_11_10 (M : LinearMultistep) : Prop :=
  M.SatisfiesRootCondition

/-- (11.56), in the book's terms: `|r_j| ≤ 1` for every root, and `ρ'(r_j) ≠ 0` when `|r_j| = 1`;
`Polynomial.satisfiesRootCondition_iff_derivative`. -/
theorem definition_11_10_iff (M : LinearMultistep) :
    definition_11_10 M ↔ ∀ r : ℂ, ((characteristicPolynomials M).1.map (algebraMap ℝ ℂ)).IsRoot r →
      ‖r‖ ≤ 1 ∧ (‖r‖ = 1 →
        ¬ (derivative ((characteristicPolynomials M).1.map (algebraMap ℝ ℂ))).IsRoot r) :=
  Polynomial.satisfiesRootCondition_iff_derivative (M.rho_monic.map _).ne_zero

/-- **Definition 11.11 (the strong root condition, (11.57))**: the root condition holds and
`r_0 = 1` is the only root of modulus one, i.e. `|r_j| < 1` for `j = 1, …, p`;
`ODE.LinearMultistep.SatisfiesStrongRootCondition`. -/
def definition_11_11 (M : LinearMultistep) : Prop :=
  M.SatisfiesStrongRootCondition

/-- (11.57), unfolded. -/
theorem definition_11_11_iff (M : LinearMultistep) :
    definition_11_11 M ↔ definition_11_10 M ∧
      ∀ r : ℂ, ((characteristicPolynomials M).1.map (algebraMap ℝ ℂ)).IsRoot r → r ≠ 1 → ‖r‖ < 1 :=
  Iff.rfl

/-- **Definition 11.12 (the absolute root condition)**: for a given `λ`, there is `h₀ > 0` such
that the roots `r_j(hλ)` of `Π` satisfy `|r_j(hλ)| < 1` for all `j` and all `h ∈ (0, h₀]`;
`ODE.LinearMultistep.SatisfiesAbsRootCondition`. -/
def definition_11_12 (M : LinearMultistep) (lam : ℂ) : Prop :=
  M.SatisfiesAbsRootCondition lam

/-- Definition 11.12, unfolded. -/
theorem definition_11_12_iff (M : LinearMultistep) (lam : ℂ) :
    definition_11_12 M lam ↔ ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Ioc 0 h₀,
      ∀ r : ℂ, (equation_11_55 M (h * lam)).IsRoot r → ‖r‖ < 1 :=
  Iff.rfl

/-! ### Definition 11.13 and Theorem 11.4: zero-stability -/

/-- **The perturbed method (11.59)**: `z` satisfies
`z_{n+1} = ∑_{j=0}^p a_j z_{n-j}
  + h [∑_{j=0}^p b_j f(t_{n-j}, z_{n-j}) + b_{-1} f(t_{n+1}, z_{n+1}) + δ_{n+1}]`
for `n ≥ p`; `ODE.LinearMultistep.IsOrbitWith`. -/
def equation_11_59 (M : LinearMultistep) (f : ℝ → ℝ → ℝ) (h t₀ : ℝ) (δ z : ℕ → ℝ) : Prop :=
  M.IsOrbitWith f h t₀ δ z

/-- (11.59), unfolded, for every `n ≥ p`. -/
theorem equation_11_59_iff (M : LinearMultistep) (δ z : ℕ → ℝ) :
    equation_11_59 M f h t₀ δ z ↔ ∀ n, M.p ≤ n → z (n + 1) =
      ∑ j : Fin (M.p + 1), M.a j * z (n - j) +
        h * (∑ j : Fin (M.p + 1), M.b j * f (grid t₀ h (n - j)) (z (n - j)) +
          M.bm1 * f (grid t₀ h (n + 1)) (z (n + 1)) + δ (n + 1)) := by
  rw [equation_11_59, LinearMultistep.isOrbitWith_iff]
  simp only [smul_eq_mul, grid]
  constructor
  · intro H n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    refine (H m).trans ?_
    ring
  · intro H n
    refine (H (n + M.p) (Nat.le_add_left _ _)).trans ?_
    ring

/-- **Definition 11.13 (zero-stability of multistep methods)**: the method (11.45) is zero-stable
for the Cauchy problem with field `f` on `[t₀, t₀ + T]` if there are `h₀ > 0` and `C > 0` such
that for all `h ∈ (0, h₀]`, `|z_n^{(h)} - u_n^{(h)}| ≤ C ε` for `0 ≤ n ≤ N_h` (11.58), whenever
`|δ_k| ≤ ε` for `0 ≤ k ≤ N_h`, `z` solves the perturbed recursion (11.59) from the starting values
`w_k + δ_k` and `u` solves (11.60) from the starting values `w_k`, `k = 0, …, p`;
`ODE.LinearMultistep.IsZeroStable`. -/
def definition_11_13 (M : LinearMultistep) (f : ℝ → ℝ → ℝ) (t₀ T : ℝ) : Prop :=
  M.IsZeroStable f t₀ T

/-- Definition 11.13, unfolded. -/
theorem definition_11_13_iff (M : LinearMultistep) :
    definition_11_13 M f t₀ T ↔
      ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ C : ℝ, 0 < C ∧ ∀ h ∈ Ioc 0 h₀, ∀ ε : ℝ, 0 ≤ ε → ∀ δ : ℕ → ℝ,
        (∀ k ≤ gridCount T h, |δ k| ≤ ε) → ∀ u z : ℕ → ℝ, equation_11_45 M f h t₀ u →
          equation_11_59 M f h t₀ δ z → (∀ k ≤ M.p, z k = u k + δ k) →
            ∀ n ≤ gridCount T h, |z n - u n| ≤ C * ε := by
  unfold definition_11_13 LinearMultistep.IsZeroStable equation_11_45 equation_11_59 gridCount
  simp only [Real.norm_eq_abs]

/-- **Theorem 11.4 (zero-stability and the root condition)**: on a horizon `T > 0`, the multistep
method is zero-stable for every Cauchy problem whose field is Lipschitz continuous in `y`
uniformly on `[t₀, t₀ + T]` iff it satisfies the root condition;
`ODE.LinearMultistep.isZeroStable_iff_satisfiesRootCondition`. The book states the theorem for
consistent methods; consistency is not needed. -/
theorem theorem_11_4 (M : LinearMultistep) (hT : 0 < T) :
    (∀ (f : ℝ → ℝ → ℝ) (L : ℝ),
      (∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) →
        definition_11_13 M f t₀ T) ↔ definition_11_10 M := by
  unfold definition_11_13 definition_11_10
  rw [← M.isZeroStable_iff_satisfiesRootCondition hT]
  constructor
  · intro H f L hf
    exact H f L fun t ht y₁ y₂ => by
      have := (hf t ht).dist_le_mul y₁ y₂
      rwa [Real.dist_eq, Real.dist_eq] at this
  · intro H f L hf
    exact H f (Real.toNNReal L) fun t ht => LipschitzWith.of_dist_le_mul fun y₁ y₂ => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
      exact (hf t ht y₁ y₂).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

/-- **Theorem 11.4, sufficiency**: a method satisfying the root condition is zero-stable for
every Cauchy problem with `f` Lipschitz in `y` uniformly on `[t₀, t₀ + T]`, `T ≥ 0`;
`ODE.LinearMultistep.isZeroStable_of_satisfiesRootCondition`. -/
theorem theorem_11_4_mpr (M : LinearMultistep) (hroot : definition_11_10 M) (hT : 0 ≤ T) {L : ℝ}
    (hf : ∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) :
    definition_11_13 M f t₀ T :=
  M.isZeroStable_of_satisfiesRootCondition (L := Real.toNNReal L) hroot hT fun t ht =>
    LipschitzWith.of_dist_le_mul fun y₁ y₂ => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
      exact (hf t ht y₁ y₂).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

/-- **Theorem 11.4, necessity**: a method zero-stable for the problem `y' = 0` on a horizon
`T > 0` satisfies the root condition;
`ODE.LinearMultistep.satisfiesRootCondition_of_isZeroStable`. -/
theorem theorem_11_4_mp (M : LinearMultistep) (hT : 0 < T)
    (hzs : definition_11_13 M (fun _ _ => 0) t₀ T) : definition_11_10 M :=
  M.satisfiesRootCondition_of_isZeroStable hT hzs

/-- **Lemma 11.3, over `ℂ`**: for the difference equation (11.28) of order `k ≥ 1` with complex
coefficients, there is `M > 0` such that every solution `u` of (11.28) satisfies
`|u_n| ≤ M (max_{j<k} |u_j| + ∑_{l=k}^n |φ_l|)` for all `n` (11.63), iff the polynomial (11.30)
satisfies the root condition; `LinearRecurrence.exists_forall_norm_le_iff_satisfiesRootCondition`.
The book cites [Gau97] without proof. -/
theorem lemma_11_3_complex {k : ℕ} (hk : 0 < k) (α : Fin k → ℂ) :
    (∃ M : ℝ, 0 < M ∧ ∀ φ u : ℕ → ℂ, (equation_11_28 α).IsSolutionWith φ u → ∀ n,
      ‖u n‖ ≤ M * ((⨆ j : Fin k, ‖u j‖) + ∑ l ∈ Finset.Icc k n, ‖φ l‖)) ↔
      (equation_11_30 α).SatisfiesRootCondition := by
  rw [equation_11_30_eq]
  exact (equation_11_28 α).exists_forall_norm_le_iff_satisfiesRootCondition hk

/-- **Lemma 11.3**: for the real difference equation (11.28) of order `k ≥ 1`, there is `M > 0`
such that every real solution `u` satisfies `|u_n| ≤ M (max_{j<k} |u_j| + ∑_{l=k}^n |φ_l|)` for
all `n` (11.63), iff the polynomial (11.30) satisfies the root condition (over `ℂ`). The bound
follows from the complex case applied to the complexified sequences; the converse from the real
unbounded solution
`LinearRecurrence.exists_isSolution_real_not_bddAbove_of_not_satisfiesRootCondition`. -/
theorem lemma_11_3 {k : ℕ} (hk : 0 < k) (α : Fin k → ℝ) :
    (∃ M : ℝ, 0 < M ∧ ∀ φ u : ℕ → ℝ, (equation_11_28 α).IsSolutionWith φ u → ∀ n,
      |u n| ≤ M * ((⨆ j : Fin k, |u j|) + ∑ l ∈ Finset.Icc k n, |φ l|)) ↔
      ((equation_11_30 α).map (algebraMap ℝ ℂ)).SatisfiesRootCondition := by
  have hchar : ((equation_11_28 α).map (algebraMap ℝ ℂ)).charPoly =
      (equation_11_30 α).map (algebraMap ℝ ℂ) := by
    rw [LinearRecurrence.charPoly_map, equation_11_30_eq]
  constructor
  · rintro ⟨M, hM0, hM⟩
    by_contra hroot
    rw [← hchar] at hroot
    obtain ⟨u, hu, hu'⟩ :=
      (equation_11_28 α).exists_isSolution_real_not_bddAbove_of_not_satisfiesRootCondition hroot
    refine hu' ⟨M * ((⨆ j : Fin k, |u j|) + ∑ l ∈ Finset.Icc k 0, |(0 : ℝ)|), ?_⟩
    rintro _ ⟨n, rfl⟩
    have := hM 0 u (((equation_11_28 α).isSolutionWith_zero_iff u).2 hu) n
    simp only [Pi.zero_apply, abs_zero, Finset.sum_const_zero, add_zero] at this ⊢
    exact this
  · intro hroot
    rw [← hchar] at hroot
    obtain ⟨M, hM0, hM⟩ :=
      ((equation_11_28 α).map (algebraMap ℝ ℂ)).exists_forall_norm_le_iff_satisfiesRootCondition
        hk |>.2 hroot
    refine ⟨M, hM0, fun φ u hu n => ?_⟩
    have := hM _ _ ((equation_11_28 α).isSolutionWith_map (algebraMap ℝ ℂ) hu) n
    simpa only [Function.comp_apply, Complex.coe_algebraMap, Complex.norm_real,
      Real.norm_eq_abs, LinearRecurrence.map_order, equation_11_28_order] using this

/-- **The zero-stability estimate (11.65)**: under the root condition and the Lipschitz
condition, there are `h₀ > 0` and `K > 0` such that for `h ∈ (0, h₀]`, a solution `u` of (11.60),
a solution `z` of the perturbed recursion (11.59) with starting errors `|z_k - u_k| ≤ ε₀`,
`k ≤ p`, and perturbations `|δ_k| ≤ ε₁` for `p + 1 ≤ k ≤ N_h`,
`|z_n^{(h)} - u_n^{(h)}| ≤ K (ε₀ + T ε₁)` for `n ≤ N_h` — the book's
`2 M e^{TQ} {(p + 1) Δ_{[0,p]} + T Δ_{[p+1,n]}}` with `h₀ = 1/Q`;
`ODE.LinearMultistep.norm_sub_le_of_satisfiesRootCondition`. -/
theorem equation_11_65 (M : LinearMultistep) (hroot : definition_11_10 M) (hT : 0 ≤ T) {L : ℝ}
    (hf : ∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ K : ℝ, 0 < K ∧ ∀ h ∈ Ioc 0 h₀, ∀ ε₀ ε₁ : ℝ, 0 ≤ ε₀ → 0 ≤ ε₁ →
      ∀ δ u z : ℕ → ℝ, equation_11_45 M f h t₀ u → equation_11_59 M f h t₀ δ z →
        (∀ k ≤ M.p, |z k - u k| ≤ ε₀) → (∀ k, M.p + 1 ≤ k → k ≤ gridCount T h → |δ k| ≤ ε₁) →
          ∀ n ≤ gridCount T h, |z n - u n| ≤ K * (ε₀ + T * ε₁) := by
  have hf' : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith (Real.toNNReal L) (f t) := fun t ht =>
    LipschitzWith.of_dist_le_mul fun y₁ y₂ => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
      exact (hf t ht y₁ y₂).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  obtain ⟨h₀, hh₀, K, hK, hest⟩ := M.norm_sub_le_of_satisfiesRootCondition hroot hT hf'
  refine ⟨h₀, hh₀, K, hK, fun h hh ε₀ ε₁ hε₀ hε₁ δ u z hu hz hzu hδ n hn => ?_⟩
  exact hest h hh hε₀ hε₁ (fun m _ => (M.isOrbit_iff_rhs.1 hu) m) (fun m _ => hz m)
    (fun k hk => hzu k hk) (fun k hk hk' => hδ k hk hk') n hn

/-! ### §11.6.3: zero-stability of the classical methods -/

/-- **Consistent one-step methods are zero-stable** (§11.6.3): a method with `p = 0` and
`a_0 = 1` has `ρ(r) = r - 1`, satisfies the root condition, and is zero-stable for every
Lipschitz problem; `ODE.LinearMultistep.satisfiesRootCondition_of_p_eq_zero`,
`ODE.LinearMultistep.rho_ofOneStep`. -/
theorem oneStep_zeroStable :
    (∀ M : LinearMultistep, M.p = 0 → ∑ j, M.a j = 1 → definition_11_10 M ∧
      ∀ (t₀ T : ℝ) (f : ℝ → ℝ → ℝ) (L : ℝ), 0 ≤ T →
        (∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) →
          definition_11_13 M f t₀ T) ∧
    ∀ b₀ bm1 : ℝ, (characteristicPolynomials (LinearMultistep.ofOneStep 1 b₀ bm1)).1 = X - 1 := by
  refine ⟨fun M hp h0 => ?_, fun b₀ bm1 => ?_⟩
  · have hroot : definition_11_10 M :=
      M.satisfiesRootCondition_of_p_eq_zero hp ((LinearMultistep.orderCondition_zero M).2 h0)
    exact ⟨hroot, fun t₀ T f L hT hf => theorem_11_4_mpr M hroot hT hf⟩
  · rw [characteristicPolynomials, LinearMultistep.rho_ofOneStep, C_1]

/-- **Adams methods are zero-stable** (§11.6.3): `ρ(r) = r^{p+1} - r^p = r^p (r - 1)` has the
roots `1` and `0` (of multiplicity `p`), so every Adams method satisfies the root condition and is
zero-stable for every Lipschitz problem; `ODE.LinearMultistep.rho_of_a_single`,
`ODE.LinearMultistep.satisfiesRootCondition_of_a_single`,
`ODE.LinearMultistep.adams_satisfiesRootCondition`. -/
theorem adams_zeroStable :
    (∀ M : LinearMultistep, equation_11_49 M →
      (characteristicPolynomials M).1 = X ^ M.p * (X - 1) ∧ definition_11_10 M ∧
      ∀ (t₀ T : ℝ) (f : ℝ → ℝ → ℝ) (L : ℝ), 0 ≤ T →
        (∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) →
          definition_11_13 M f t₀ T) ∧
    ∀ p : ℕ, definition_11_10 (LinearMultistep.adamsBashforth p) ∧
      definition_11_10 (LinearMultistep.adamsMoulton p) := by
  refine ⟨fun M hM => ?_, fun p => LinearMultistep.adams_satisfiesRootCondition p⟩
  have hroot : definition_11_10 M := M.satisfiesRootCondition_of_a_single hM
  refine ⟨?_, hroot, fun t₀ T f L hT hf => theorem_11_4_mpr M hroot hT hf⟩
  rw [characteristicPolynomials, M.rho_of_a_single hM, C_1]

/-- **The midpoint method is zero-stable** (§11.6.3): `ρ(r) = r² - 1` has the simple roots `±1`;
`ODE.LinearMultistep.midpoint_satisfiesRootCondition`. -/
theorem midpoint_zeroStable :
    (characteristicPolynomials equation_11_43).1 = X ^ 2 - 1 ∧ definition_11_10 equation_11_43 ∧
      ∀ (t₀ T : ℝ) (f : ℝ → ℝ → ℝ) (L : ℝ), 0 ≤ T →
        (∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) →
          definition_11_13 equation_11_43 f t₀ T :=
  ⟨LinearMultistep.rho_midpoint, LinearMultistep.midpoint_satisfiesRootCondition,
    fun _ _ _ _ hT hf => theorem_11_4_mpr _ LinearMultistep.midpoint_satisfiesRootCondition hT hf⟩

/-- **The Simpson method is zero-stable** (§11.6.3): `ρ(r) = r² - 1` has the simple roots `±1`;
`ODE.LinearMultistep.simpson_satisfiesRootCondition`. -/
theorem simpson_zeroStable :
    (characteristicPolynomials equation_11_44).1 = X ^ 2 - 1 ∧ definition_11_10 equation_11_44 ∧
      ∀ (t₀ T : ℝ) (f : ℝ → ℝ → ℝ) (L : ℝ), 0 ≤ T →
        (∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) →
          definition_11_13 equation_11_44 f t₀ T :=
  ⟨LinearMultistep.rho_simpson, LinearMultistep.simpson_satisfiesRootCondition,
    fun _ _ _ _ hT hf => theorem_11_4_mpr _ LinearMultistep.simpson_satisfiesRootCondition hT hf⟩

/-- **The BDF methods with `p ≤ 2` are zero-stable** (§11.6.3, the rows `p = 0, 1, 2` of Table
11.2): `ρ` has the roots `1`, `1/3` (`p = 1`) and `1`, `(7 ± i√39)/22` (`p = 2`);
`ODE.LinearMultistep.bdf_satisfiesRootCondition`. The rows `p = 3, 4, 5` are `bdf_zeroStable`. -/
theorem bdf_zeroStable_of_le_two (k : Fin 6) (hk : k ≤ 2) : definition_11_10 (bdf k) :=
  LinearMultistep.bdf_satisfiesRootCondition k hk

/-- **The BDF methods of Table 11.2 are zero-stable** (§11.6.3, "BDF methods are zero-stable for
`p ≤ 5`", quoted in the book from Cryer without proof): every one of the six rows of Table 11.2
satisfies the root condition. For `p ≤ 2` this is `bdf_zeroStable_of_le_two`; for `p = 3, 4, 5`
the spurious factor of `ρ` is located inside the unit disc by the Schur–Cohn recursion,
`ODE.LinearMultistep.bdf_satisfiesRootCondition_all`. -/
theorem bdf_zeroStable (k : Fin 6) : definition_11_10 (bdf k) :=
  LinearMultistep.bdf_satisfiesRootCondition_all k

/-! ### Theorem 11.5 and Corollary 11.1: convergence -/

/-- **Theorem 11.5, sufficiency**: a method satisfying the root condition, consistent along the
solution `y` of a Cauchy problem whose field is Lipschitz in `y` uniformly on `[t₀, t₀ + T]`, is
convergent: there are `h₀ > 0` and `C(ε, h) → 0` as `(ε, h) → (0, 0)` such that every sequence
`u` produced by the method with step `h ∈ (0, h₀]` satisfies
`|u_n - y_n| ≤ C(max_{k ≤ p} |u_k - y_k|, h)` for `n ≤ N_h` — the error tends to zero when the
error on the starting values does; `ODE.LinearMultistep.isConvergentFor_of_satisfiesRootCondition`.
-/
theorem theorem_11_5_mpr (M : LinearMultistep) (hroot : definition_11_10 M) (hT : 0 ≤ T) {L : ℝ}
    (hf : ∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|)
    (hy : ∀ t ∈ Icc t₀ (t₀ + T), HasDerivAt y (f t (y t)) t) (hcons : definition_11_9 M t₀ T y) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ C : ℝ → ℝ → ℝ,
      Tendsto (fun p : ℝ × ℝ => C p.1 p.2) (𝓝[≥] 0 ×ˢ 𝓝[>] 0) (𝓝 0) ∧
      ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → ℝ, equation_11_45 M f h t₀ u → ∀ n ≤ gridCount T h,
        |u n - y (grid t₀ h n)| ≤ C (⨆ k : Fin (M.p + 1), |u k - y (grid t₀ h k)|) h := by
  have hf' : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith (Real.toNNReal L) (f t) := fun t ht =>
    LipschitzWith.of_dist_le_mul fun y₁ y₂ => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
      exact (hf t ht y₁ y₂).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  exact M.isConvergentFor_of_satisfiesRootCondition hroot hT hf' hy hcons

/-- **Theorem 11.5, the order of convergence**: a method satisfying the root condition, of order
`q` along the solution `y` of a Lipschitz Cauchy problem, converges with order `q`:
`|u_n - y_n| ≤ K (max_{k ≤ p} |u_k - y_k| + h^q)` for `n ≤ N_h`, so that starting errors `O(h^q)`
give a global error `O(h^q)`;
`ODE.LinearMultistep.isConvergentWithOrderFor_of_satisfiesRootCondition`. -/
theorem theorem_11_5_order (M : LinearMultistep) (hroot : definition_11_10 M) (hT : 0 ≤ T) {L : ℝ}
    (hf : ∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|)
    (hy : ∀ t ∈ Icc t₀ (t₀ + T), HasDerivAt y (f t (y t)) t) {q : ℕ}
    (hord : definition_11_9_order M t₀ T y q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ K : ℝ, 0 < K ∧ ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → ℝ, equation_11_45 M f h t₀ u →
      ∀ n ≤ gridCount T h,
        |u n - y (grid t₀ h n)| ≤ K * ((⨆ k : Fin (M.p + 1), |u k - y (grid t₀ h k)|) + h ^ q) := by
  have hf' : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith (Real.toNNReal L) (f t) := fun t ht =>
    LipschitzWith.of_dist_le_mul fun y₁ y₂ => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
      exact (hf t ht y₁ y₂).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  exact M.isConvergentWithOrderFor_of_satisfiesRootCondition hroot hT hf' hy hord

/-- **Theorem 11.5, necessity**: a method convergent (in the sense of `theorem_11_5_mpr`) for the
problem `y' = 0`, `y = 0` on a horizon `T > 0` satisfies the root condition;
`ODE.LinearMultistep.satisfiesRootCondition_of_isConvergentFor`. -/
theorem theorem_11_5_mp (M : LinearMultistep) (hT : 0 < T)
    (hconv : ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ C : ℝ → ℝ → ℝ,
      Tendsto (fun p : ℝ × ℝ => C p.1 p.2) (𝓝[≥] 0 ×ˢ 𝓝[>] 0) (𝓝 0) ∧
      ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → ℝ, equation_11_45 M (fun _ _ => 0) h t₀ u →
        ∀ n ≤ gridCount T h, |u n| ≤ C (⨆ k : Fin (M.p + 1), |u k|) h) :
    definition_11_10 M := by
  refine M.satisfiesRootCondition_of_isConvergentFor (t₀ := t₀) hT ?_
  simpa only [LinearMultistep.IsConvergentFor, Real.norm_eq_abs, sub_zero, equation_11_45,
    gridCount, grid] using hconv

/-- **Theorem 11.5 (convergence)**: on a horizon `T > 0`, a consistent multistep method is
convergent for every Cauchy problem with `f` Lipschitz in `y` uniformly on `[t₀, t₀ + T]` (and a
solution `y` along which the method is consistent) iff it satisfies the root condition. -/
theorem theorem_11_5 (M : LinearMultistep) (hcons : definition_11_9_method M) (hT : 0 < T) :
    (∀ (f : ℝ → ℝ → ℝ) (L : ℝ) (y : ℝ → ℝ),
      (∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) →
      (∀ t ∈ Icc t₀ (t₀ + T), HasDerivAt y (f t (y t)) t) → definition_11_9 M t₀ T y →
      ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ C : ℝ → ℝ → ℝ,
        Tendsto (fun p : ℝ × ℝ => C p.1 p.2) (𝓝[≥] 0 ×ˢ 𝓝[>] 0) (𝓝 0) ∧
        ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → ℝ, equation_11_45 M f h t₀ u → ∀ n ≤ gridCount T h,
          |u n - y (grid t₀ h n)| ≤ C (⨆ k : Fin (M.p + 1), |u k - y (grid t₀ h k)|) h) ↔
      definition_11_10 M := by
  constructor
  · intro H
    refine theorem_11_5_mp (t₀ := t₀) M hT ?_
    have := H (fun _ _ => 0) 0 (fun _ => 0) (fun _ _ _ _ => by simp)
      (fun _ _ => hasDerivAt_const _ _) (hcons t₀ T hT _ contDiff_const)
    simpa only [sub_zero] using this
  · intro hroot f L y hf hy hc
    exact theorem_11_5_mpr M hroot hT.le hf hy hc

/-- **Corollary 11.1 (the equivalence theorem)**: on a horizon `T > 0`, a consistent multistep
method is convergent for every Lipschitz Cauchy problem with a `C¹` solution iff it is zero-stable
for every Lipschitz problem — both being the root condition, by Theorems 11.4 and 11.5;
`ODE.LinearMultistep.isConvergentFor_iff_isZeroStable`. -/
theorem corollary_11_1 (M : LinearMultistep) (hcons : definition_11_9_method M) (hT : 0 < T) :
    (∀ (f : ℝ → ℝ → ℝ) (L : ℝ) (y : ℝ → ℝ),
      (∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) →
      (∀ t ∈ Icc t₀ (t₀ + T), HasDerivAt y (f t (y t)) t) →
      ContinuousOn (fun t => f t (y t)) (Icc t₀ (t₀ + T)) →
      ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ C : ℝ → ℝ → ℝ,
        Tendsto (fun p : ℝ × ℝ => C p.1 p.2) (𝓝[≥] 0 ×ˢ 𝓝[>] 0) (𝓝 0) ∧
        ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → ℝ, equation_11_45 M f h t₀ u → ∀ n ≤ gridCount T h,
          |u n - y (grid t₀ h n)| ≤ C (⨆ k : Fin (M.p + 1), |u k - y (grid t₀ h k)|) h) ↔
    (∀ (f : ℝ → ℝ → ℝ) (L : ℝ),
      (∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) →
        definition_11_13 M f t₀ T) := by
  rw [theorem_11_4 M hT]
  have key := M.isConvergentFor_iff_isZeroStable (t₀ := t₀) hcons hT
  rw [M.isZeroStable_iff_satisfiesRootCondition hT] at key
  change _ ↔ M.SatisfiesRootCondition
  rw [← key]
  constructor
  · intro H f L y hf hy hcont
    exact H f L y (fun t ht y₁ y₂ => by
      have := (hf t ht).dist_le_mul y₁ y₂
      rwa [Real.dist_eq, Real.dist_eq] at this) hy hcont
  · intro H f L y hf hy hcont
    exact H f (Real.toNNReal L) y (fun t ht => LipschitzWith.of_dist_le_mul fun y₁ y₂ => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
      exact (hf t ht y₁ y₂).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)))
      hy hcont

/-! ### §11.6.4: absolute stability of multistep methods -/

/-- **Absolute stability of a multistep method** (Definition 11.6 for (11.45)): the method with
step `h > 0` applied to the test problem (11.24) is absolutely stable if it is determined
(`1 - hλ b_{-1} ≠ 0`) and every sequence it produces tends to zero. -/
def absolutelyStable (M : LinearMultistep) (lam : ℂ) (h : ℝ) : Prop :=
  1 - (h : ℂ) * lam * M.bm1 ≠ 0 ∧
    ∀ u : ℕ → ℂ, M.IsOrbit (testProblem lam) h 0 u → Tendsto u atTop (𝓝 0)

/-- **The region of absolute stability (11.26) of a multistep method**;
`ODE.LinearMultistep.absStabilityRegion`. -/
def equation_11_26_multistep (M : LinearMultistep) : Set ℂ :=
  M.absStabilityRegion

/-- **Absolute stability of multistep methods (§11.6.4)**: the method is absolutely stable at
`(λ, h)` iff `hλ ∈ 𝒜`; `z ∈ 𝒜` iff `1 - z b_{-1} ≠ 0` and all the roots of `Π(z)` lie in the open
unit disc; hence the absolute root condition (Definition 11.12) at `λ` is necessary and
sufficient for the method to be absolutely stable at `(λ, h)` for all `h ≤ h₀`, for some `h₀ > 0`;
`ODE.LinearMultistep.isAbsStable_iff_mem`, `ODE.LinearMultistep.mem_absStabilityRegion_iff`,
`ODE.LinearMultistep.satisfiesAbsRootCondition_iff`. -/
theorem absoluteStability (M : LinearMultistep) :
    (∀ (lam : ℂ) (h : ℝ), absolutelyStable M lam h ↔ (h : ℂ) * lam ∈ equation_11_26_multistep M) ∧
    (∀ z : ℂ, z ∈ equation_11_26_multistep M ↔
      1 - z * M.bm1 ≠ 0 ∧ ∀ r : ℂ, (equation_11_55 M z).IsRoot r → ‖r‖ < 1) ∧
    ∀ lam : ℂ, definition_11_12 M lam ↔
      ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Ioc 0 h₀, absolutelyStable M lam h := by
  refine ⟨fun lam h => M.isAbsStable_iff_mem lam, fun z => M.mem_absStabilityRegion_iff z,
    fun lam => ?_⟩
  rw [definition_11_12, M.satisfiesAbsRootCondition_iff]
  exact exists_congr fun h₀ => and_congr_right fun _ => forall₂_congr fun h _ =>
    (M.isAbsStable_iff_mem lam).symm

/-- **A-stability of a multistep method** (§11.6.4): `𝒜 ⊇ ℂ⁻`; `ODE.LinearMultistep.IsAStable`.
-/
def aStableMultistep (M : LinearMultistep) : Prop :=
  M.IsAStable

/-- **ϑ-stability** (§11.6.4): for `ϑ ∈ (0, π/2)`, the method is ϑ-stable if `𝒜` contains the
sector `{z ∈ ℂ : -ϑ < π - arg z < ϑ}`, written `|arg(-z)| < ϑ`; `ODE.LinearMultistep.IsThetaStable`.
-/
def thetaStable (M : LinearMultistep) (ϑ : ℝ) : Prop :=
  M.IsThetaStable ϑ

/-- A- and ϑ-stability, unfolded, and A-stability implies ϑ-stability for `ϑ ≤ π/2`. -/
theorem thetaStable_iff (M : LinearMultistep) (ϑ : ℝ) :
    (aStableMultistep M ↔ ∀ z : ℂ, z.re < 0 → z ∈ equation_11_26_multistep M) ∧
    (thetaStable M ϑ ↔
      ∀ z : ℂ, z ≠ 0 → |Complex.arg (-z)| < ϑ → z ∈ equation_11_26_multistep M) ∧
    (aStableMultistep M → ϑ ≤ Real.pi / 2 → thetaStable M ϑ) :=
  ⟨Iff.rfl, Iff.rfl, fun hA hϑ => LinearMultistep.IsAStable.isThetaStable M hA hϑ⟩

/-- **Backward Euler and Crank–Nicolson are A-stable as multistep methods** (`bdf 0` and
`adamsMoulton 1`), and the regions of forward Euler, backward Euler and Crank–Nicolson as
multistep methods are their regions as one-step methods (§11.3);
`ODE.LinearMultistep.absStabilityRegion_ofOneStep`. -/
theorem backwardEuler_aStable :
    aStableMultistep (bdf 0) ∧ aStableMultistep (LinearMultistep.adamsMoulton 1) ∧
    equation_11_26_multistep (LinearMultistep.adamsBashforth 0) =
      equation_11_26 (fun f => OneStep.ofIncrement (OneStep.forwardEuler f)) ∧
    equation_11_26_multistep (bdf 0) =
      equation_11_26 (fun f => OneStep.ofIncrement (OneStep.backwardEuler f)) ∧
    equation_11_26_multistep (LinearMultistep.adamsMoulton 1) =
      equation_11_26 (fun f => OneStep.ofIncrement (OneStep.crankNicolson f)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := LinearMultistep.absStabilityRegion_ofOneStep
  refine ⟨h4, h5, ?_, ?_, ?_⟩
  · rw [equation_11_26_multistep, LinearMultistep.adamsBashforth_zero_eq]
    exact h1
  · exact h2
  · rw [equation_11_26_multistep, LinearMultistep.adamsMoulton_one_eq]
    exact h3

/-- Crank–Nicolson is A-stable as a multistep method. -/
theorem crankNicolson_aStable : aStableMultistep (LinearMultistep.adamsMoulton 1) :=
  backwardEuler_aStable.2.1

/-- **Property 11.2, the explicit clause**: an explicit consistent linear multistep method is
neither A-stable nor ϑ-stable for any `ϑ > 0` — its region of absolute stability misses points
`-t`, `t > 0` arbitrarily large, since `Π(-t)` is monic of degree `p + 1` and a monic polynomial
with all its roots in the open unit disc is bounded by `2^{p+1}` on the closed disc, while
`|Π(-t)(x₀)| ≥ t |σ(x₀)| - |ρ(x₀)|` at a point `x₀ ∈ [0, 1]` with `σ(x₀) ≠ 0`;
`ODE.LinearMultistep.not_isAStable_of_bm1_eq_zero`,
`ODE.LinearMultistep.not_isThetaStable_of_bm1_eq_zero`. The order-2 barrier for A-stable methods
and Widlund's statement on ϑ-stable methods are not formalized; see `## Not formalized here` in
the module doc. -/
theorem property_11_2_explicit (M : LinearMultistep) (hex : ¬ M.IsImplicit)
    (h0 : ∑ j, M.a j = 1) :
    ¬ aStableMultistep M ∧ ∀ ϑ : ℝ, 0 < ϑ → ¬ thetaStable M ϑ := by
  have hb : M.bm1 = 0 := not_not.1 hex
  have h0' : M.orderCondition 0 := (LinearMultistep.orderCondition_zero M).2 h0
  exact ⟨M.not_isAStable_of_bm1_eq_zero hb h0',
    fun ϑ hϑ => M.not_isThetaStable_of_bm1_eq_zero hb h0' hϑ⟩

/-- **Remark 11.3, the region `𝒜*`** of [BD74]: the set of `z = hλ` for which the method is
determined and every sequence it produces on the test problem is bounded,
`∃ C > 0, |u_n| ≤ C` for all `n ≥ 0`; `ODE.LinearMultistep.absStabilityRegionStar`. -/
def remark_11_3 (M : LinearMultistep) : Set ℂ :=
  M.absStabilityRegionStar

/-- `𝒜*`, unfolded (through the recurrence (11.54) and through the sequences the method
produces on the test problem), `𝒜 ⊆ 𝒜*`, and `z ∈ 𝒜*` iff `Π(z)` satisfies the root condition
(Lemma 11.3); `ODE.LinearMultistep.mem_absStabilityRegionStar_iff`. -/
theorem remark_11_3_iff (M : LinearMultistep) :
    (∀ z : ℂ, z ∈ remark_11_3 M ↔ 1 - z * M.bm1 ≠ 0 ∧ ∀ u : ℕ → ℂ,
      (M.toLinearRecurrence z).IsSolution u → BddAbove (Set.range fun n => ‖u n‖)) ∧
    (∀ (lam : ℂ) (h : ℝ), (h : ℂ) * lam ∈ remark_11_3 M ↔
      1 - (h : ℂ) * lam * M.bm1 ≠ 0 ∧
      ∀ u : ℕ → ℂ, M.IsOrbit (testProblem lam) h 0 u → BddAbove (Set.range fun n => ‖u n‖)) ∧
    equation_11_26_multistep M ⊆ remark_11_3 M ∧
    ∀ z : ℂ, z ∈ remark_11_3 M ↔
      1 - z * M.bm1 ≠ 0 ∧ (equation_11_55 M z).SatisfiesRootCondition := by
  refine ⟨fun z => Iff.rfl, fun lam h => ?_, M.absStabilityRegion_subset_star,
    fun z => M.mem_absStabilityRegionStar_iff z⟩
  change (1 - (h : ℂ) * lam * M.bm1 ≠ 0 ∧ ∀ u : ℕ → ℂ,
    (M.toLinearRecurrence (h * lam)).IsSolution u → BddAbove (Set.range fun n => ‖u n‖)) ↔ _
  exact and_congr_right fun hz => forall_congr' fun u =>
    imp_congr_left (M.isOrbit_testField_iff hz).symm

/-- **Remark 11.3, the midpoint method**: `𝒜 = ∅` while `𝒜* = {iα : |α| < 1}` — the book prints
`α ∈ [-1, 1]`, but at `α = ±1` the root `±i` of `r² ∓ 2ir - 1` is double and `n (±i)^n` is
unbounded (see the errata); `ODE.LinearMultistep.absStabilityRegion_midpoint`. -/
theorem remark_11_3_midpoint :
    equation_11_26_multistep equation_11_43 = ∅ ∧
      remark_11_3 equation_11_43 = {z | ∃ α : ℝ, |α| < 1 ∧ z = α * Complex.I} :=
  LinearMultistep.absStabilityRegion_midpoint

/-- **Remark 11.3, zero-stability**: zero-stable methods are those with `0 ∈ 𝒜*` — `Π(0) = ρ`,
so `0 ∈ 𝒜*` is the root condition, which with Theorem 11.4 is zero-stability for every Lipschitz
problem; `ODE.LinearMultistep.zero_mem_absStabilityRegionStar_iff`. -/
theorem remark_11_3_zeroStable (M : LinearMultistep) (hT : 0 < T) :
    (0 : ℂ) ∈ remark_11_3 M ↔ ∀ (f : ℝ → ℝ → ℝ) (L : ℝ),
      (∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) →
        definition_11_13 M f t₀ T := by
  rw [theorem_11_4 M hT, remark_11_3, LinearMultistep.zero_mem_absStabilityRegionStar_iff]
  rfl

/-- **Relative stability (11.66)**: the method on the test problem (11.24) with a given `λ` is
relatively stable with threshold `h₀` on the horizon `T` if for every `h ≤ h₀` there is `C > 0`
with `|u_n| ≤ C (|u_0| + ⋯ + |u_p|)` for `p + 1 ≤ n ≤ N_h`. The bound is read over the grid of the
fixed bounded interval `[0, T]`: as printed, over all `n`, it fails for every method with a
principal root of modulus `> 1` (e.g. `Re λ > 0`). The claim that the strong root condition
implies (11.66) is not formalized. -/
def equation_11_66 (M : LinearMultistep) (lam : ℂ) (h₀ T : ℝ) : Prop :=
  ∀ h ∈ Ioc 0 h₀, ∃ C : ℝ, 0 < C ∧ ∀ u : ℕ → ℂ, M.IsOrbit (testProblem lam) h 0 u →
    ∀ n, M.p + 1 ≤ n → n ≤ gridCount T h → ‖u n‖ ≤ C * ∑ k : Fin (M.p + 1), ‖u k‖

end QuarteroniSaccoSaleri.Chapter11
