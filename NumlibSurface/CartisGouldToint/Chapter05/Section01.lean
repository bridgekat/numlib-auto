import Numlib.Optimization.LeastSquares.LowerComplexity
import Numlib.Optimization.LeastSquares.Complexity
import Numlib.Optimization.LeastSquares.Run
import Numlib.Optimization.LeastSquares.EmptyDirections
import Numlib.Optimization.LeastSquares.Exponents
import Numlib.Optimization.LeastSquares.Cascading
import Numlib.Optimization.LeastSquares.Decrease
import Numlib.Analysis.SpecialFunctions.Pow.Differences
import Numlib.Data.Nat.Factorization
import Numlib.Optimization.LeastSquares.Powers

/-!
# Cartis–Gould–Toint, Section 5.1: residual powers

The residual-power analysis uses increments of cascading dyadic powers and the unique
odd factorization of a positive integer. Lemma 5.1.3 retains the quotient form and all
integer exponents from the source, with the zero case interpreted by real division.
-/

namespace CartisGouldToint

/-- Cartis–Gould–Toint, Lemma 5.1.3: cascading differences of nonnegative
ordered numbers, with all dyadic and integer powers written explicitly.
When `a = b = 0`, the quotient is interpreted by real division. -/
theorem lemma_5_1_3 {a b : ℝ} (hba : b ≤ a) (hb : 0 ≤ b)
    (i ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (a ^ ℓ - b ^ ℓ) /
        ((2 : ℝ) ^ i * (ℓ : ℝ) *
          a ^ (((2 : ℝ) ^ i - 1) / (2 : ℝ) ^ i + (ℓ : ℝ) - 1)) ≤
      a ^ (1 / (2 : ℝ) ^ i) - b ^ (1 / (2 : ℝ) ^ i) := by
  have hpow : (0 : ℝ) < 2 ^ i := pow_pos (by norm_num) i
  have hpow1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  have hq : (0 : ℝ) < 1 / 2 ^ i := one_div_pos.mpr hpow
  have hqp : (1 : ℝ) / 2 ^ i ≤ (ℓ : ℝ) := by
    calc
      (1 : ℝ) / 2 ^ i ≤ 1 := (div_le_one hpow).mpr hpow1
      _ ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have h := Real.rpow_sub_div_le_rpow_sub hb hba hq hqp
  rw [Real.rpow_natCast, Real.rpow_natCast] at h
  have he : (ℓ : ℝ) - 1 / (2 : ℝ) ^ i =
      ((2 : ℝ) ^ i - 1) / (2 : ℝ) ^ i + (ℓ : ℝ) - 1 := by
    field_simp
    ring
  rw [he] at h
  simpa [div_div, mul_comm] using h

/-- **Lemma 5.1.5 (odd factorization).** Each positive natural number has a
unique representation as an odd positive integer times a power of two. The book's
`ℕ` excludes zero; the hypothesis `0 < p` makes that convention explicit. -/
theorem lemma_5_1_5 {p : ℕ} (hp : 0 < p) :
    ∃! z : ℕ × ℕ, Odd z.1 ∧ 0 < z.1 ∧ p = z.1 * 2 ^ z.2 :=
  Nat.existsUnique_odd_mul_two_pow hp

/-- The residual-power objective (5.1.3), with real exponent `ℓ`:
`Φ_ℓ(x) = ‖r(x)‖^ℓ / ℓ`. The optimization model uses positive exponents. -/
noncomputable def residualPowerObjective {E F : Type*} [NormedAddCommGroup F]
    (r : E → F) (ℓ : ℝ) (x : E) : ℝ := LeastSquares.powerObjective r ℓ x

/-- Evaluation of the residual-power objective. -/
@[simp]
theorem residualPowerObjective_apply {E F : Type*} [NormedAddCommGroup F]
    (r : E → F) (ℓ : ℝ) (x : E) :
    residualPowerObjective r ℓ x = ‖r x‖ ^ ℓ / ℓ := rfl

/-- The exponent-one residual objective is the residual norm. -/
@[simp]
theorem residualPowerObjective_one {E F : Type*} [NormedAddCommGroup F]
    (r : E → F) (x : E) : residualPowerObjective r 1 x = ‖r x‖ :=
  LeastSquares.powerObjective_one r x

/-- The exponent-two residual objective is the least-squares objective. -/
@[simp]
theorem residualPowerObjective_two {E F : Type*} [NormedAddCommGroup F]
    (r : E → F) (x : E) : residualPowerObjective r 2 x = ‖r x‖ ^ 2 / 2 :=
  LeastSquares.powerObjective_two r x

/-- **Lemma 5.1.1 (smoothness of residual powers).** A `C^p` residual has a `C^p`
residual-power objective whenever the positive exponent is an even integer or
is a real number strictly larger than `2p`. Both cases include residual zeros. -/
theorem lemma_5_1_1 {n m p : ℕ}
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {ℓ : ℝ}
    (hr : ContDiff ℝ p r) (_hℓ : 0 < ℓ)
    (hcase : (∃ q : ℕ, ℓ = 2 * (q : ℝ)) ∨ 2 * (p : ℝ) < ℓ) :
    ContDiff ℝ p (residualPowerObjective r ℓ) := by
  rcases hcase with ⟨q,rfl⟩ | hlarge
  · exact LeastSquares.contDiff_powerObjective_even hr q
  · exact LeastSquares.contDiff_powerObjective_of_two_mul_le hr hlarge.le

end CartisGouldToint

namespace CartisGouldToint
open HighOrderRegularization

/-- The actual model/ratio/update components of ARpLE, without its stopping rule. -/
abbrev arpLeastEuclideanModelTrace {n m : ℕ}
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (ℓ : ℝ) (p : ℕ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ) (N : ℕ) : Prop :=
  LeastSquares.RegularizationTrace r ℓ p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N

/-- The normalized actual first derivative measure `ψℓ,1`. -/
noncomputable abbrev residualFirstMeasure {n m : ℕ}
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (ℓ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := LeastSquares.firstMeasure r ℓ x

/-- The normalized actual least Hessian value `ψℓ,2`, used with its true eigenpair
certificate. -/
noncomputable abbrev residualSecondMeasure {n m : ℕ}
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (ℓ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (μ : ℝ) : ℝ := LeastSquares.secondMeasure r ℓ x μ

/-- The normalized absolute actual directional Hessian in (5.1.7). -/
noncomputable abbrev residualDirectionalSecondMeasure {n m : ℕ}
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (ℓ : ℝ)
    (x v : EuclideanSpace ℝ (Fin n)) : ℝ := LeastSquares.directionalSecondMeasure r ℓ x v

/-- The normalized absolute actual third derivative `ψℓ,3` in (5.1.6). -/
noncomputable abbrev residualThirdMeasure {n m : ℕ}
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (ℓ : ℝ)
    (x v : EuclideanSpace ℝ (Fin n)) : ℝ := LeastSquares.thirdMeasure r ℓ x v

/-- **Lemma 5.1.2.** All three successful residual-power decrease bounds
(5.1.15)–(5.1.17) and the normalized small-Hessian bound (5.1.18).
The measures use actual objective derivatives, and the least Hessian value has
its actual eigenpair certificate. Only enabled higher-order model tests are
required. Zero endpoint residuals are included by real division. -/
theorem lemma_5_1_2 {n m p N i : ℕ}
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {ℓ η₁ η₂ γ₁ γ₂ γ₃ σmin L θ₁ θ₂ θ₃ : ℝ} {ε₂ ε₃ : WithTop ℝ}
    (h : arpLeastEuclideanModelTrace r ℓ p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hp₂ : ε₂ ≠ ⊤ → 2 ≤ p) (hp₃ : ε₃ ≠ ⊤ → 3 ≤ p)
    (hℓ : 2 ≤ ℓ) (hf : ContDiff ℝ p (residualPowerObjective r ℓ)) (hL : 1 ≤ L)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hθ₃ : 0 < θ₃)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p (residualPowerObjective r ℓ) y -
      iteratedFDeriv ℝ p (residualPowerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hi : i < N) (hs : η₁ ≤ ρ i)
    (hfirst : ‖fderiv ℝ (model (residualPowerObjective r ℓ) p (x i) (σ i)) (s i)‖ ≤
      θ₁ * ‖s i‖ ^ p)
    (hsecond : ε₂ ≠ ⊤ → ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 →
      -θ₂ * ‖s i‖ ^ (p - 1) ≤ iteratedFDeriv ℝ 2
        (model (residualPowerObjective r ℓ) p (x i) (σ i)) (s i) (fun _ => v))
    (hthird : ε₃ ≠ ⊤ → ∀ v ∈ smallModelDirections
      (residualPowerObjective r ℓ) p (x i) (s i) (σ i) θ₂,
      |iteratedFDeriv ℝ 3 (model (residualPowerObjective r ℓ) p (x i) (σ i)) (s i)
        (fun _ => v)| ≤ θ₃ * ‖s i‖ ^ (p - 2)) :
    ∃ κ₁ > 0, ∃ κ₂ > 0, ∃ κ₃ > 0,
      κ₁ = decreaseConstant p p η₁ σmin L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₁ ∧
      κ₂ = decreaseConstant p (p - 1) η₁ σmin L
        (max (σ 0) (γ₃ * L / (1 - η₂))) θ₂ ∧
      κ₃ = decreaseConstant p (p - 2) η₁ σmin L
        (max (σ 0) (γ₃ * L / (1 - η₂))) θ₃ ∧
      κ₁ * ℓ * residualFirstMeasure r ℓ (x (i + 1)) ^ (((p + 1 : ℕ) : ℝ) / p) *
        ‖r (x (i + 1))‖ ^ ((ℓ - 1) * ((p + 1 : ℕ) : ℝ) / p) ≤
          ‖r (x i)‖ ^ ℓ - ‖r (x (i + 1))‖ ^ ℓ ∧
      (ε₂ ≠ ⊤ → ∀ (μ : ℝ) (u : EuclideanSpace ℝ (Fin n)),
        SecondOrderTrustRegion.IsLeastEigenpair (residualPowerObjective r ℓ) (x (i + 1)) μ u →
        κ₂ * ℓ * max 0 (-residualSecondMeasure r ℓ (x (i + 1)) μ) ^
          (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)) *
          ‖r (x (i + 1))‖ ^ ((ℓ - 1) * ((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)) ≤
            ‖r (x i)‖ ^ ℓ - ‖r (x (i + 1))‖ ^ ℓ) ∧
      (ε₃ ≠ ⊤ → ∀ v ∈ smallModelDirections
        (residualPowerObjective r ℓ) p (x i) (s i) (σ i) θ₂,
        κ₃ * ℓ * residualThirdMeasure r ℓ (x (i + 1)) v ^
          (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)) *
          ‖r (x (i + 1))‖ ^ ((ℓ - 1) * ((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)) ≤
            ‖r (x i)‖ ^ ℓ - ‖r (x (i + 1))‖ ^ ℓ ∧
        residualDirectionalSecondMeasure r ℓ (x (i + 1)) v *
          ‖r (x (i + 1))‖ ^ (ℓ - 1) ≤
          1 / stepConstant (p - 1) L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₂ *
            ‖s i‖ ^ (p - 1)) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hℓp : 0 < ℓ := by linarith
  have hm : 0 ≤ max (σ 0) (γ₃ * L / (1 - η₂)) :=
    (h.updates.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  refine ⟨_, decreaseConstant_pos p p h.updates.eta1_pos h.updates.min_pos hLp hm hθ₁.le,
    _, decreaseConstant_pos p (p - 1) h.updates.eta1_pos h.updates.min_pos hLp hm hθ₂.le,
    _, decreaseConstant_pos p (p - 2) h.updates.eta1_pos h.updates.min_pos hLp hm hθ₃.le,
    rfl, rfl, rfl, ?_,?_,?_⟩
  · exact LeastSquares.RegularizationTrace.decrease_first h hℓp hf hLp hθ₁.le
      hlip hi hs hfirst
  · intro hε μ u hu
    exact LeastSquares.RegularizationTrace.decrease_second h (hp₂ hε) hℓp hf hLp hθ₂.le
      hlip hi hs (hsecond hε) hu
  · intro hε v hv
    exact ⟨LeastSquares.RegularizationTrace.decrease_third h (hp₃ hε) hℓp hf hLp hθ₃.le
        hlip hi hs (hthird hε) hv,
      LeastSquares.RegularizationTrace.small_curvature_le h (by have := hp₃ hε; omega)
        hf hLp.le hlip hi hs hv⟩

end CartisGouldToint

namespace CartisGouldToint
open HighOrderRegularization

/-- The exact residual exponent for branch `j`: `(2^a-1)/2^a-j*(ℓ-1)/(p+1-j)`. -/
noncomputable abbrev residualCascadingExponent := LeastSquares.cascadingExponent

/-- The exact dyadic-root coefficient `κ*β^((ℓ-1)*(p+1)/(p+1-j))/2^a`. -/
noncomputable abbrev residualCascadingConstant := LeastSquares.cascadingConstant

/-- **Lemma 5.1.4.** All three enabled dyadic-root decrease bounds (5.1.20),
(5.1.22), (5.1.24) with the exact coefficients and exponents (5.1.21), (5.1.23),
(5.1.25), together with both relative-decrease inequalities (5.1.27) and their
strictly positive coefficient (5.1.28). Actual accepted trial rules derive
residual monotonicity; no residual decrease is assumed. -/
theorem lemma_5_1_4 {n m p N i : ℕ}
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {ℓ η₁ η₂ γ₁ γ₂ γ₃ σmin L θ₁ θ₂ θ₃ β : ℝ}
    {ε₂ ε₃ : WithTop ℝ}
    (h : arpLeastEuclideanModelTrace r ℓ p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hp₂ : ε₂ ≠ ⊤ → 2 ≤ p) (hp₃ : ε₃ ≠ ⊤ → 3 ≤ p)
    (hℓ : 2 ≤ ℓ) (hf : ContDiff ℝ p (residualPowerObjective r ℓ)) (hL : 1 ≤ L)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hθ₃ : 0 < θ₃)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p (residualPowerObjective r ℓ) y -
      iteratedFDeriv ℝ p (residualPowerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hβ : 0 < β) (hβ1 : β < 1)
    (hi : i < N) (hs : η₁ ≤ ρ i)
    (hfirst : ‖fderiv ℝ (model (residualPowerObjective r ℓ) p (x i) (σ i)) (s i)‖ ≤
      θ₁ * ‖s i‖ ^ p)
    (hsecond : ε₂ ≠ ⊤ → ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 →
      -θ₂ * ‖s i‖ ^ (p - 1) ≤ iteratedFDeriv ℝ 2
        (model (residualPowerObjective r ℓ) p (x i) (σ i)) (s i) (fun _ => v))
    (hthird : ε₃ ≠ ⊤ → ∀ v ∈ smallModelDirections
      (residualPowerObjective r ℓ) p (x i) (s i) (σ i) θ₂,
      |iteratedFDeriv ℝ 3 (model (residualPowerObjective r ℓ) p (x i) (σ i)) (s i)
        (fun _ => v)| ≤ θ₃ * ‖s i‖ ^ (p - 2)) :
    ∃ κ₁ > 0, ∃ κ₂ > 0, ∃ κ₃ > 0,
      κ₁ = decreaseConstant p p η₁ σmin L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₁ ∧
      κ₂ = decreaseConstant p (p - 1) η₁ σmin L
        (max (σ 0) (γ₃ * L / (1 - η₂))) θ₂ ∧
      κ₃ = decreaseConstant p (p - 2) η₁ σmin L
        (max (σ 0) (γ₃ * L / (1 - η₂))) θ₃ ∧
      ∀ a : ℕ,
        0 < residualCascadingConstant κ₁ β ℓ p a 1 ∧
        0 < residualCascadingConstant κ₂ β ℓ p a 2 ∧
        0 < residualCascadingConstant κ₃ β ℓ p a 3 ∧
        (β * ‖r (x i)‖ < ‖r (x (i + 1))‖ →
          residualCascadingConstant κ₁ β ℓ p a 1 *
            residualFirstMeasure r ℓ (x (i + 1)) ^ (((p + 1 : ℕ) : ℝ) / p) /
            ‖r (x i)‖ ^ residualCascadingExponent p ℓ a 1 ≤
              ‖r (x i)‖ ^ (1 / (2 : ℝ) ^ a) -
                ‖r (x (i + 1))‖ ^ (1 / (2 : ℝ) ^ a) ∧
          (ε₂ ≠ ⊤ → ∀ (μ : ℝ) (u : EuclideanSpace ℝ (Fin n)),
            SecondOrderTrustRegion.IsLeastEigenpair
              (residualPowerObjective r ℓ) (x (i + 1)) μ u →
            residualCascadingConstant κ₂ β ℓ p a 2 *
              max 0 (-residualSecondMeasure r ℓ (x (i + 1)) μ) ^
                (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)) /
              ‖r (x i)‖ ^ residualCascadingExponent p ℓ a 2 ≤
                ‖r (x i)‖ ^ (1 / (2 : ℝ) ^ a) -
                  ‖r (x (i + 1))‖ ^ (1 / (2 : ℝ) ^ a)) ∧
          (ε₃ ≠ ⊤ → ∀ v ∈ smallModelDirections
            (residualPowerObjective r ℓ) p (x i) (s i) (σ i) θ₂,
            residualCascadingConstant κ₃ β ℓ p a 3 *
              residualThirdMeasure r ℓ (x (i + 1)) v ^
                (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)) /
              ‖r (x i)‖ ^ residualCascadingExponent p ℓ a 3 ≤
                ‖r (x i)‖ ^ (1 / (2 : ℝ) ^ a) -
                  ‖r (x (i + 1))‖ ^ (1 / (2 : ℝ) ^ a))) ∧
        (‖r (x (i + 1))‖ ≤ β * ‖r (x i)‖ →
          0 < 1 - β ^ (1 / (2 : ℝ) ^ a) ∧
          (1 - β ^ (1 / (2 : ℝ) ^ a)) * ‖r (x i)‖ ^ (1 / (2 : ℝ) ^ a) ≤
            ‖r (x i)‖ ^ (1 / (2 : ℝ) ^ a) -
              ‖r (x (i + 1))‖ ^ (1 / (2 : ℝ) ^ a) ∧
          (1 - β ^ (1 / (2 : ℝ) ^ a)) * ‖r (x (i + 1))‖ ^ (1 / (2 : ℝ) ^ a) ≤
            (1 - β ^ (1 / (2 : ℝ) ^ a)) * ‖r (x i)‖ ^ (1 / (2 : ℝ) ^ a)) := by
  obtain ⟨κ₁, hκ₁, κ₂, hκ₂, κ₃, hκ₃, h₁, h₂, h₃, hd₁, hd₂, hd₃⟩ :=
    lemma_5_1_2 h hp₂ hp₃ hℓ hf hL hθ₁ hθ₂ hθ₃ hlip hi hs hfirst hsecond hthird
  refine ⟨κ₁, hκ₁, κ₂, hκ₂, κ₃, hκ₃, h₁, h₂, h₃, ?_⟩
  have hres := LeastSquares.RegularizationTrace.residual_lt h (by linarith) hi hs
  have ha : 0 < ‖r (x i)‖ := (norm_nonneg _).trans_lt hres
  have hℓ1 : 1 ≤ ℓ := by linarith
  intro a
  refine ⟨LeastSquares.cascadingConstant_pos hκ₁ hβ p a 1,
    LeastSquares.cascadingConstant_pos hκ₂ hβ p a 2,
    LeastSquares.cascadingConstant_pos hκ₃ hβ p a 3, ?_, ?_⟩
  · intro hrel
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Nat.add_sub_cancel] using
        LeastSquares.cascading_decrease_of_power (p := p) (i := a) (j := 1)
          (u := residualFirstMeasure r ℓ (x (i + 1)))
          ha (norm_nonneg _) hres.le hβ hrel.le hℓ1 hκ₁.le
          (div_nonneg (norm_nonneg _) (LeastSquares.derivativeWeight_nonneg _ _ _))
          h.order_pos hd₁
    · intro hε μ u hu
      have hd := hd₂ hε μ u hu
      have hm : p + 1 - 2 = p - 1 := by omega
      simpa only [hm] using
        LeastSquares.cascading_decrease_of_power (p := p) (i := a) (j := 2)
          ha (norm_nonneg _) hres.le hβ hrel.le hℓ1 hκ₂.le
          (le_max_left 0 _) (hp₂ hε) (by simpa only [hm] using hd)
    · intro hε v hv
      have hd := (hd₃ hε v hv).1
      have hm : p + 1 - 3 = p - 2 := by omega
      simpa only [hm] using
        LeastSquares.cascading_decrease_of_power (p := p) (i := a) (j := 3)
          (u := residualThirdMeasure r ℓ (x (i + 1)) v)
          ha (norm_nonneg _) hres.le hβ hrel.le hℓ1 hκ₃.le
          (div_nonneg (abs_nonneg _) (LeastSquares.derivativeWeight_nonneg _ _ _))
          (hp₃ hε) (by simpa only [hm] using hd)
  · intro hrel
    exact Real.relative_cascading_decrease (norm_nonneg _) hres.le hβ.le hβ1 hrel
      (by positivity)

end CartisGouldToint

namespace CartisGouldToint

/-- **Lemma 5.1.6.** All six good-exponent choices (5.1.38)–(5.1.43),
including every strict-positivity, exact-zero and `ℓ>1` conclusion. The odd
factors from Lemma 5.1.5 and the positive even valuation in (5.1.43) are
explicit. The source convention that natural model orders are positive is
recorded by `hp`. -/
theorem lemma_5_1_6 {p : ℕ} (hp : 0 < p) :
    (∀ i : ℕ, Real.logb 2 (p : ℝ) < i →
      0 < residualCascadingExponent p p i 1) ∧
    (∀ o i : ℕ, Odd o → Even p → p = o * 2 ^ i →
      residualCascadingExponent p (1 + (o : ℝ) * ((2 : ℝ)^i - 1)) i 1 = 0 ∧
        1 < 1 + (o : ℝ) * ((2 : ℝ)^i - 1)) ∧
    (∀ i : ℕ, Even p → Real.logb 2 (p - 1 : ℕ) < i →
      0 < residualCascadingExponent p ((p : ℝ) / 2) i 1 ∧
      0 < residualCascadingExponent p ((p : ℝ) / 2) i 2) ∧
    (∀ o i : ℕ, Odd o → 4 ∣ p - 1 → p - 1 = o * 2 ^ (i + 1) →
      residualCascadingExponent p (1 + (o : ℝ) * ((2 : ℝ)^i - 1)) i 2 = 0 ∧
      0 < residualCascadingExponent p (1 + (o : ℝ) * ((2 : ℝ)^i - 1)) i 1 ∧
      1 < 1 + (o : ℝ) * ((2 : ℝ)^i - 1)) ∧
    (∀ i : ℕ, 3 ∣ p → Real.logb 2 (p - 2 : ℕ) < i →
      0 < residualCascadingExponent p ((p : ℝ) / 3) i 1 ∧
      0 < residualCascadingExponent p ((p : ℝ) / 3) i 2 ∧
      0 < residualCascadingExponent p ((p : ℝ) / 3) i 3) ∧
    (∀ o i : ℕ, Odd o → 0 < i → Even i → p - 2 = o * 2 ^ i →
      let ℓ := 1 + (o : ℝ) * ∑ k ∈ Finset.range (i / 2), (2 : ℝ)^(2 * k)
      residualCascadingExponent p ℓ i 3 = 0 ∧
      0 < residualCascadingExponent p ℓ i 1 ∧
      0 < residualCascadingExponent p ℓ i 2 ∧ 1 < ℓ) :=
  LeastSquares.cascadingExponent_choices hp

end CartisGouldToint

namespace CartisGouldToint

/-- The literal finite-third-order ARpLE test, including its printed direction guard. -/
abbrev arpLeastEuclideanLiteralFiniteStop := @LeastSquares.literalFiniteStop

/-- The repaired finite-third-order ARpLE test removes only the direction nonemptiness guard. -/
abbrev arpLeastEuclideanFiniteStop := @LeastSquares.finiteStop

/-- **Counterexample to the literal third-order claim of Theorem 5.1.7.**
The legal choice `p=6,ℓ=2,i=3` satisfies (5.1.42). The actual positive C6 residual
never passes the global tolerance one, and a genuine accepted AR6 trial with
actual ratio two creates an empty inherited set at a flat terminal jet. The
literal stopping test fails there and every positive-parameter model admits no
strictly improving step. The repaired test accepts that same actual endpoint. -/
theorem theorem_5_1_7_nonempty_guard_counterexample :
    (1 < (2 : ℝ) ∧ (2 : ℝ) = (6 : ℝ) / 3 ∧ Real.logb 2 (6 - 2 : ℝ) < 3) ∧
    ∃ (r : ℝ → ℝ) (L ε₁ : ℝ), 1 ≤ L ∧ 0 < ε₁ ∧ ε₁ ≤ 1 ∧
      ContDiff ℝ 6 r ∧ ContDiff ℝ 6 (LeastSquares.powerObjective r 2) ∧
      (∀ x, 1 < ‖r x‖) ∧
      (∀ x y, ‖iteratedFDeriv ℝ 6 (LeastSquares.powerObjective r 2) x -
        iteratedFDeriv ℝ 6 (LeastSquares.powerObjective r 2) y‖ ≤ L * ‖x - y‖) ∧
      HighOrderRegularization.ModelTrace (LeastSquares.powerObjective r 2) 6
        HighOrderRegularization.EmptyDirections.point (fun _ => 1) (fun _ => 1440) (fun _ => 2)
        (1 / 4) (3 / 4) (1 / 2) 2 3 1440 1 ∧
      HighOrderRegularization.StepConditions (LeastSquares.powerObjective r 2) 6 0 1 1440 1 1 1 ∧
      HighOrderRegularization.smallModelDirections
        (LeastSquares.powerObjective r 2) 6 0 1 1440 1 = ∅ ∧
      (∀ (μ : ℝ) (M : Set ℝ), ¬ LeastSquares.literalFiniteStop r 2 0 μ M 1 ε₁ 1 1) ∧
      ¬ LeastSquares.literalFiniteStop r 2 1 0 ∅ 1 ε₁ 1 1 ∧
      LeastSquares.finiteStop r 2 1 0 ∅ 1 ε₁ 1 1 ∧
      SecondOrderTrustRegion.IsLeastEigenpair (LeastSquares.powerObjective r 2) 1 0 1 ∧
      (∀ σ : ℝ, 0 ≤ σ → ¬ ∃ s : ℝ,
        HighOrderRegularization.model (LeastSquares.powerObjective r 2) 6 1 σ s <
          HighOrderRegularization.model (LeastSquares.powerObjective r 2) 6 1 σ 0) :=
  ⟨LeastSquares.EmptyDirections.source_exponent_choice,
    LeastSquares.EmptyDirections.exists_stuck_execution⟩

end CartisGouldToint

namespace CartisGouldToint

/-- Algorithm 5.1.1 in all enabled orders, retaining the literal stopping guard.
Every trace field is an actual objective/model rule, never a decrease or complexity conclusion. -/
abbrev arpLeastEuclideanRun {n m : ℕ}
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (ℓ : ℝ) (p : ℕ)
    (x s u : ℕ → EuclideanSpace ℝ (Fin n)) (μ σ ρ : ℕ → ℝ)
    (M : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₀ ε₁ : ℝ)
    (ε₂ ε₃ : WithTop ℝ) (N : ℕ) : Prop :=
  LeastSquares.Run true r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
    θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ N

/-- The same complete ARpLE program after removing only the false nonempty-direction guard. -/
abbrev arpLeastEuclideanCorrectedRun {n m : ℕ}
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (ℓ : ℝ) (p : ℕ)
    (x s u : ℕ → EuclideanSpace ℝ (Fin n)) (μ σ ρ : ℕ → ℝ)
    (M : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₀ ε₁ : ℝ)
    (ε₂ ε₃ : WithTop ℝ) (N : ℕ) : Prop :=
  LeastSquares.Run false r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
    θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ N

end CartisGouldToint

namespace CartisGouldToint

/-- The minimum of the four exact accuracy powers in (5.1.44)–(5.1.45). -/
noncomputable abbrev residualAccuracyFactor := LeastSquares.rootAccuracyFactor

/-- The maximum of the four printed initial-residual powers in the complexity numerator. -/
noncomputable abbrev residualInitialBudget := LeastSquares.rootBudget

/-- The exact maximum reciprocal decrease coefficient `κS`, fixed before all accuracies. -/
noncomputable abbrev arpLeastEuclideanSuccessfulIterationConstant :=
  LeastSquares.rootSuccessfulIterationConstant

/-- The actual true normalized small-curvature unit directions (5.1.7). -/
abbrev residualSmallCurvatureDirections := @LeastSquares.smallResidualCurvatureDirections

/-- Residual calls include initialization and every actual acceptance trial. -/
abbrev arpLeastEuclideanResidualEvaluations := HighOrderRegularization.functionEvaluations

/-- Every requested residual derivative order is evaluated initially and at accepted endpoints. -/
noncomputable abbrev arpLeastEuclideanDerivativeEvaluations := LeastSquares.derivativeEvaluations

/-- The inverse accuracy factor is exactly the maximum of the four source inverse powers. -/
theorem residualAccuracyFactor_inverse (p a : ℕ) {ε₀ ε₁ ε₂ ε₃ : ℝ}
    (h₀ : 0 < ε₀) (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃) :
    1 / residualAccuracyFactor p a ε₀ ε₁ ε₂ ε₃ =
      max (ε₀ ^ (-(1 / (2 : ℝ) ^ a)))
        (max (ε₁ ^ (-((p + 1 : ℕ) : ℝ) / p))
          (max (ε₂ ^ (-((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)))
            (ε₃ ^ (-((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ))))) :=
  LeastSquares.inv_rootAccuracyFactor_eq p a h₀ h₁ h₂ h₃

/-- **Theorem 5.1.7, corrected finite-third-order statement.** Only the false
nonempty-direction guard is removed. The exact source constants are fixed before
all four accuracies and all actual executions; all true optimality clauses,
returned-direction containment, first-stop termination, and initialized counts
are included. The source exponent choices use their preceding divisibility and
odd-factorization context. OCR dyadic indices are `a`, and the function budget
uses `κA` as derived in the proof, correcting its duplicated printed `κC`. -/
theorem theorem_5_1_7_corrected {n m p a : ℕ}
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} (ℓ : ℝ)
    {σinit σmin η₁ η₂ γ₁ γ₂ γ₃ L θ₁ θ₂ θ₃ β : ℝ}
    (hp : 0 < p) (_hℓ : 1 < ℓ)
    (hchoice : (3 ∣ p ∧ ℓ = (p : ℝ) / 3 ∧ Real.logb 2 (p - 2 : ℕ) < a) ∨
      ∃ o : ℕ, Odd o ∧ 0 < a ∧ Even a ∧ p - 2 = o * 2 ^ a ∧
        ℓ = 1 + (o : ℝ) * ∑ k ∈ Finset.range (a / 2), (2 : ℝ) ^ (2 * k))
    (hf : ContDiff ℝ p (residualPowerObjective r ℓ)) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p (residualPowerObjective r ℓ) y -
      iteratedFDeriv ℝ p (residualPowerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hσ : 0 < σinit) (hmin : 0 < σmin) (hη : 0 < η₁) (hγ₂ : 1 < γ₂)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hθ₃ : 0 < θ₃) (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ κS > 0, ∃ κA > 0, ∃ κC > 0,
      κS = arpLeastEuclideanSuccessfulIterationConstant p ℓ a σinit σmin η₁ η₂
        γ₃ L θ₁ θ₂ θ₃ β ∧
      κA = κS * (1 + |Real.log γ₁| / Real.log γ₂) ∧
      κC = |Real.log γ₁| / Real.log γ₂ +
        Real.log (max σinit (γ₃ * L / (1 - η₂)) / σinit) / Real.log γ₂ + 2 ∧
      ∀ ε₀ ε₁ ε₂ ε₃ : ℝ, ∀ x s u : ℕ → EuclideanSpace ℝ (Fin n),
      ∀ μ σ ρ : ℕ → ℝ, ∀ M : ℕ → Set (EuclideanSpace ℝ (Fin n)), σ 0 =
        σinit →
      (∀ N, (∀ i < N, ¬arpLeastEuclideanFiniteStop r ℓ (x i) (μ i) (M i) ε₀
        ε₁ ε₂ ε₃) →
        arpLeastEuclideanCorrectedRun r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
          θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ N) →
      ∃ K, arpLeastEuclideanFiniteStop r ℓ (x K) (μ K) (M K) ε₀ ε₁ ε₂ ε₃ ∧
        arpLeastEuclideanCorrectedRun r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
          θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ K ∧
        (∀ i < K, ¬arpLeastEuclideanFiniteStop r ℓ (x i) (μ i) (M i) ε₀ ε₁
          ε₂ ε₃) ∧
        (‖r (x K)‖ ≤ ε₀ ∨
          residualFirstMeasure r ℓ (x K) ≤ ε₁ ∧ -ε₂ ≤ residualSecondMeasure
            r ℓ (x K) (μ K) ∧
          HighOrderRegularization.returnedDirections (residualSecondMeasure r ℓ (x K)
            (μ K)) ε₂ (M K) ⊆
            residualSmallCurvatureDirections r ℓ (x K) ε₂ ∧
          ∀ v ∈ HighOrderRegularization.returnedDirections (residualSecondMeasure r
            ℓ (x K) (μ K)) ε₂ (M K),
            residualThirdMeasure r ℓ (x K) v ≤ ε₃) ∧
        (arpLeastEuclideanResidualEvaluations K : ℝ) ≤
          κA * residualInitialBudget p ℓ a ‖r (x 0)‖ / residualAccuracyFactor p a
            ε₀ ε₁ ε₂ ε₃ + κC ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ p → (arpLeastEuclideanDerivativeEvaluations ρ
          η₁ p j K : ℝ) ≤
          κS * residualInitialBudget p ℓ a ‖r (x 0)‖ / residualAccuracyFactor p a
            ε₀ ε₁ ε₂ ε₃ + 2 := by
  have H := LeastSquares.cascadingExponent_choices hp
  have hg : 0 ≤ residualCascadingExponent p ℓ a 1 ∧
      0 ≤ residualCascadingExponent p ℓ a 2 ∧
      0 ≤ residualCascadingExponent p ℓ a 3 := by
    rcases hchoice with ⟨hdiv, rfl, hlog⟩ | ⟨o, ho, ha, heven, hfac, rfl⟩
    · have ht := H.2.2.2.2.1 a hdiv hlog
      exact ⟨ht.1.le, ht.2.1.le, ht.2.2.le⟩
    · have ht := H.2.2.2.2.2 o a ho ha heven hfac
      exact ⟨ht.2.1.le, ht.2.2.1.le, ht.1.symm.le⟩
  exact LeastSquares.exists_uniform_finite_complexity p a ℓ hf (zero_lt_one.trans_le hL)
    hlip hσ hmin hη hγ₂ hθ₁ hθ₂ hθ₃ hβ hβ1 hg.1 hg.2.1 hg.2.2

end CartisGouldToint

namespace CartisGouldToint

/-- The normalized stop with third order disabled, and optionally second order disabled. -/
abbrev arpLeastEuclideanLowerStop := @LeastSquares.lowerStop

/-- A genuine literal ARpLE execution with only first or first-and-second tests enabled. -/
abbrev arpLeastEuclideanLowerRun {n m : ℕ} (second : Bool)
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (ℓ : ℝ) (p : ℕ)
    (x s u : ℕ → EuclideanSpace ℝ (Fin n)) (μ σ ρ : ℕ → ℝ)
    (M : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ : ℝ) (N :
      ℕ) : Prop :=
  LeastSquares.LowerRun true second r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
    θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ N

/-- The exact minimum of enabled lower-order accuracy powers. -/
noncomputable abbrev residualLowerAccuracyFactor := LeastSquares.lowerAccuracyFactor

/-- The exact maximum of enabled initial residual powers. -/
noncomputable abbrev residualLowerInitialBudget := LeastSquares.lowerBudget

/-- The maximum of enabled reciprocal decrease coefficients, before all accuracies. -/
noncomputable abbrev arpLeastEuclideanLowerSuccessfulIterationConstant :=
  LeastSquares.lowerSuccessfulIterationConstant

/-- Lower-order complexity has precisely the maximum of the enabled inverse accuracy powers. -/
theorem residualLowerAccuracyFactor_inverse (second : Bool) (p a : ℕ) {ε₀ ε₁ ε₂ : ℝ}
    (h₀ : 0 < ε₀) (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) :
    1 / residualLowerAccuracyFactor second p a ε₀ ε₁ ε₂ =
      if second then max (ε₀ ^ (-(1 / (2 : ℝ) ^ a)))
        (max (ε₁ ^ (-((p + 1 : ℕ) : ℝ) / p))
          (ε₂ ^ (-((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ))))
      else max (ε₀ ^ (-(1 / (2 : ℝ) ^ a)))
        (ε₁ ^ (-((p + 1 : ℕ) : ℝ) / p)) :=
  LeastSquares.inv_lowerAccuracyFactor_eq second p a h₀ h₁ h₂

/-- Theorem 5.1.7 with both higher tests disabled: choices (5.1.38)–(5.1.39),
exact first-order powers and constants, the first actual stop and every initialized count.
The literal program is valid in this mode; its third-order guard is irrelevant. -/
theorem theorem_5_1_7_corrected_first_order {n m p a : ℕ}
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} (ℓ : ℝ)
    {σinit σmin η₁ η₂ γ₁ γ₂ γ₃ L θ₁ θ₂ θ₃ β : ℝ}
    (hp : 0 < p) (_hℓ : 1 < ℓ)
    (hchoice : (ℓ = (p : ℝ) ∧ Real.logb 2 (p : ℝ) < a) ∨
      ∃ o : ℕ, Odd o ∧ Even p ∧ p = o * 2 ^ a ∧
        ℓ = 1 + (o : ℝ) * ((2 : ℝ) ^ a - 1))
    (hf : ContDiff ℝ p (residualPowerObjective r ℓ)) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p (residualPowerObjective r ℓ) y -
      iteratedFDeriv ℝ p (residualPowerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hσ : 0 < σinit) (hmin : 0 < σmin) (hη : 0 < η₁) (hγ₂ : 1 < γ₂)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ κS > 0, ∃ κA > 0, ∃ κC > 0,
      κS = arpLeastEuclideanLowerSuccessfulIterationConstant false p ℓ a σinit σmin
        η₁ η₂ γ₃ L θ₁ θ₂ β ∧
      κA = κS * (1 + |Real.log γ₁| / Real.log γ₂) ∧
      κC = |Real.log γ₁| / Real.log γ₂ +
        Real.log (max σinit (γ₃ * L / (1 - η₂)) / σinit) / Real.log γ₂ + 2 ∧
      ∀ ε₀ ε₁ : ℝ, ∀ x s u : ℕ → EuclideanSpace ℝ (Fin n),
      ∀ μ σ ρ : ℕ → ℝ, ∀ M : ℕ → Set (EuclideanSpace ℝ (Fin n)), σ 0 =
        σinit →
      (∀ N, (∀ i < N, ¬arpLeastEuclideanLowerStop false r ℓ (x i) (μ i) ε₀ ε₁ 1) →
        arpLeastEuclideanLowerRun false r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
          θ₁ θ₂ θ₃ ε₀ ε₁ 1 N) →
      ∃ K, arpLeastEuclideanLowerStop false r ℓ (x K) (μ K) ε₀ ε₁ 1 ∧
        arpLeastEuclideanLowerRun false r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
          θ₁ θ₂ θ₃ ε₀ ε₁ 1 K ∧
        (∀ i < K, ¬arpLeastEuclideanLowerStop false r ℓ (x i) (μ i) ε₀ ε₁ 1) ∧
        (arpLeastEuclideanResidualEvaluations K : ℝ) ≤
          κA * residualLowerInitialBudget false p ℓ a ‖r (x 0)‖ /
            residualLowerAccuracyFactor false p a ε₀ ε₁ 1 + κC ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ p → (arpLeastEuclideanDerivativeEvaluations ρ
          η₁ p j K : ℝ) ≤
          κS * residualLowerInitialBudget false p ℓ a ‖r (x 0)‖ /
            residualLowerAccuracyFactor false p a ε₀ ε₁ 1 + 2 := by
  have H := LeastSquares.cascadingExponent_choices hp
  have hg : 0 ≤ residualCascadingExponent p ℓ a 1 := by
    rcases hchoice with ⟨rfl, hlog⟩ | ⟨o, ho, heven, hfac, rfl⟩
    · exact (H.1 a hlog).le
    · exact (H.2.1 o a ho heven hfac).1.symm.le
  obtain ⟨κS, hS, κA, hA, κC, hC, hKS, hKA, hKC, h⟩ :=
    LeastSquares.exists_uniform_lower_complexity true false p a ℓ hf
      (zero_lt_one.trans_le hL) hlip hσ hmin hη hγ₂ hθ₁ hθ₂ hβ hβ1 hg (by simp)
  refine ⟨κS, hS, κA, hA, κC, hC, hKS, hKA, hKC, ?_⟩
  intro ε₀ ε₁
  exact h ε₀ ε₁ 1 zero_lt_one

/-- Theorem 5.1.7 with third order disabled: choices (5.1.40)–(5.1.41),
exact first/second-order powers and constants, the first actual stop and initialized counts.
The literal program is valid in this mode; its third-order guard is irrelevant. -/
theorem theorem_5_1_7_corrected_second_order {n m p a : ℕ}
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} (ℓ : ℝ)
    {σinit σmin η₁ η₂ γ₁ γ₂ γ₃ L θ₁ θ₂ θ₃ β : ℝ}
    (hp : 0 < p) (_hℓ : 1 < ℓ)
    (hchoice : (Even p ∧ ℓ = (p : ℝ) / 2 ∧ Real.logb 2 (p - 1 : ℕ) < a) ∨
      ∃ o : ℕ, Odd o ∧ 4 ∣ p - 1 ∧ p - 1 = o * 2 ^ (a + 1) ∧
        ℓ = 1 + (o : ℝ) * ((2 : ℝ) ^ a - 1))
    (hf : ContDiff ℝ p (residualPowerObjective r ℓ)) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p (residualPowerObjective r ℓ) y -
      iteratedFDeriv ℝ p (residualPowerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hσ : 0 < σinit) (hmin : 0 < σmin) (hη : 0 < η₁) (hγ₂ : 1 < γ₂)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ κS > 0, ∃ κA > 0, ∃ κC > 0,
      κS = arpLeastEuclideanLowerSuccessfulIterationConstant true p ℓ a σinit σmin
        η₁ η₂ γ₃ L θ₁ θ₂ β ∧
      κA = κS * (1 + |Real.log γ₁| / Real.log γ₂) ∧
      κC = |Real.log γ₁| / Real.log γ₂ +
        Real.log (max σinit (γ₃ * L / (1 - η₂)) / σinit) / Real.log γ₂ + 2 ∧
      ∀ ε₀ ε₁ ε₂ : ℝ, 0 < ε₂ → ∀ x s u : ℕ → EuclideanSpace ℝ (Fin n),
      ∀ μ σ ρ : ℕ → ℝ, ∀ M : ℕ → Set (EuclideanSpace ℝ (Fin n)), σ 0 =
        σinit →
      (∀ N, (∀ i < N, ¬arpLeastEuclideanLowerStop true r ℓ (x i) (μ i) ε₀ ε₁
        ε₂) →
        arpLeastEuclideanLowerRun true r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
          θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ N) →
      ∃ K, arpLeastEuclideanLowerStop true r ℓ (x K) (μ K) ε₀ ε₁ ε₂ ∧
        arpLeastEuclideanLowerRun true r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
          θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ K ∧
        (∀ i < K, ¬arpLeastEuclideanLowerStop true r ℓ (x i) (μ i) ε₀ ε₁ ε₂) ∧
        (arpLeastEuclideanResidualEvaluations K : ℝ) ≤
          κA * residualLowerInitialBudget true p ℓ a ‖r (x 0)‖ /
            residualLowerAccuracyFactor true p a ε₀ ε₁ ε₂ + κC ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ p → (arpLeastEuclideanDerivativeEvaluations ρ
          η₁ p j K : ℝ) ≤
          κS * residualLowerInitialBudget true p ℓ a ‖r (x 0)‖ /
            residualLowerAccuracyFactor true p a ε₀ ε₁ ε₂ + 2 := by
  have H := LeastSquares.cascadingExponent_choices hp
  have hg : 0 ≤ residualCascadingExponent p ℓ a 1 ∧
      0 ≤ residualCascadingExponent p ℓ a 2 := by
    rcases hchoice with ⟨heven, rfl, hlog⟩ | ⟨o, ho, hdiv, hfac, rfl⟩
    · have ht := H.2.2.1 a heven hlog
      exact ⟨ht.1.le, ht.2.le⟩
    · have ht := H.2.2.2.1 o a ho hdiv hfac
      exact ⟨ht.2.1.le, ht.1.symm.le⟩
  exact LeastSquares.exists_uniform_lower_complexity true true p a ℓ hf
    (zero_lt_one.trans_le hL) hlip hσ hmin hη hγ₂ hθ₁ hθ₂ hβ hβ1 hg.1 (fun _ => hg.2)

end CartisGouldToint
