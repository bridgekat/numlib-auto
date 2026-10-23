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
