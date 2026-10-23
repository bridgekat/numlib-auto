import Numlib.Optimization.Regularization.HighOrder.Parameter
import Numlib.Analysis.InnerProductSpace.NormPow.Derivatives
import Numlib.Analysis.Calculus.TaylorModel.PolynomialDerivative
import Numlib.Analysis.Calculus.TaylorModel.Smooth
import Numlib.Optimization.TrustRegion.SecondOrder.Finite


/-!
# Actual high-order regularization derivative and step bounds

The actual regularized Taylor model is differentiated to orders one, two and
three. Sharp Taylor derivative remainders and genuine norm-power derivatives
control the objective derivatives at each accepted trial. The operational model
stationarity tests yield the exact factorial step coefficients and successful
objective decrease constants, including the source's small-model-curvature set.
-/

namespace HighOrderRegularization
open TaylorModel Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- At a nonzero displacement the actual norm-power penalty is smooth to every order. -/
theorem contDiffAt_normPower (p j : ℕ) {s : E} (hs : s ≠ 0) :
    ContDiffAt ℝ j (fun z : E => ‖z‖ ^ (p + 1)) s := by
  have hh := (contDiffOn_normRpow (p + 1 : ℝ) j).contDiffAt
    (isOpen_compl_singleton.mem_nhds hs)
  simpa only [show (p + 1 : ℝ) = ((p + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast] using hh

/-- Every actual derivative of the regularized model splits into its genuine
Taylor derivative and its norm-power penalty derivative. -/
theorem iteratedFDeriv_model (f : E → ℝ) (p j : ℕ) (x : E) (σ : ℝ)
    {s : E} (hs : s ≠ 0) :
    iteratedFDeriv ℝ j (model f p x σ) s =
      iteratedFDeriv ℝ j (eval f p x) s +
        (σ / (p + 1).factorial) •
          iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ (p + 1)) s := by
  have hT := (contDiff_eval f p x j).contDiffAt (x := s)
  have hN := contDiffAt_normPower p j hs
  have heq : model f p x σ = eval f p x +
      (σ / (p + 1).factorial) • (fun z : E => ‖z‖ ^ (p + 1)) := by
    funext z
    rfl
  have hNp : ContDiffAt ℝ j
      ((σ / (p + 1).factorial) • (fun z : E => ‖z‖ ^ (p + 1))) s :=
    hN.const_smul (σ / (p + 1).factorial)
  rw [heq, iteratedFDeriv_add_apply hT hNp,
    iteratedFDeriv_const_smul_apply (a := σ / (p + 1).factorial) hN]

/-- The corresponding actual first derivative splits at every nonzero trial. -/
theorem fderiv_model (f : E → ℝ) (p : ℕ) (x : E) (σ : ℝ)
    {s : E} (hs : s ≠ 0) :
    fderiv ℝ (model f p x σ) s = fderiv ℝ (eval f p x) s +
      (σ / (p + 1).factorial) • fderiv ℝ (fun z : E => ‖z‖ ^ (p + 1)) s := by
  have hT := ((contDiff_eval f p x 1).contDiffAt (x := s)).differentiableAt one_ne_zero
  have hN := (contDiffAt_normPower p 1 hs).differentiableAt one_ne_zero
  have hh := hT.hasFDerivAt.add (hN.hasFDerivAt.const_smul (σ / (p + 1).factorial))
  have heq : model f p x σ = eval f p x +
      (σ / (p + 1).factorial) • (fun z : E => ‖z‖ ^ (p + 1)) := by
    funext z
    rfl
  exact heq.symm ▸ hh.fderiv

/-- The norm of the first derivative penalty has exactly the source factorial coefficient. -/
theorem norm_first_penalty {p : ℕ} (hp : 1 ≤ p) {σ : ℝ} (hσ : 0 ≤ σ) (s : E) :
    ‖(σ / (p + 1).factorial) • fderiv ℝ (fun z : E => ‖z‖ ^ (p + 1)) s‖ =
      σ / p.factorial * ‖s‖ ^ p := by
  rw [norm_smul, Real.norm_of_nonneg (by positivity), NormPower.norm_fderiv_norm_pow hp]
  rw [Nat.factorial_succ, Nat.cast_mul]
  push_cast
  field_simp

/-- The sharp Taylor gradient remainder is an actual continuous-linear-map norm bound. -/
theorem norm_first_error_le {p : ℕ} (hp : 1 ≤ p) {f : E → ℝ} (hf : ContDiff ℝ p f)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (x s : E) :
    ‖fderiv ℝ f (x + s) - fderiv ℝ (eval f p x) s‖ ≤
      L / p.factorial * ‖s‖ ^ p := by
  have hh := norm_iteratedFDeriv_sub_eval_le_lipschitz (j := 1)
    (C := univ) (D := univ) isOpen_univ (Subset.refl _) convex_univ
    hf.contDiffOn hL (fun y _ z _ => hlip y z) hp (mem_univ x) (mem_univ (x + s))
  have hq : p - 1 + 1 = p := by omega
  rw [hq] at hh
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have ht := (iteratedFDeriv ℝ 1 f (x + s) -
    iteratedFDeriv ℝ 1 (eval f p x) s).le_opNorm (fun _ => v)
  simp only [sub_apply, iteratedFDeriv_one_apply, Fin.prod_const, pow_one] at ht
  have hmul := mul_le_mul_of_nonneg_right hh (norm_nonneg v)
  convert ht.trans hmul using 1
  ring

private theorem factorial_weight_mul_descFactorial {p j : ℕ} (hj : j ≤ p + 1) (σ : ℝ) :
    σ / (p + 1).factorial * ((p + 1).descFactorial j : ℝ) =
      σ / (p + 1 - j).factorial := by
  rw [div_mul_eq_mul_div]
  apply (div_eq_div_iff (by positivity : ((p + 1).factorial : ℝ) ≠ 0)
    (by positivity : ((p + 1 - j).factorial : ℝ) ≠ 0)).mpr
  have hh : ((p + 1 - j).factorial : ℝ) * (p + 1).descFactorial j = (p + 1).factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial hj
  rw [←hh]
  ring

private theorem factorial_weight_two {p : ℕ} (hp : 3 ≤ p) (σ : ℝ) :
    σ / (p + 1).factorial * ((p + 1 : ℝ) * p) = σ / (p - 1).factorial := by
  have hh := factorial_weight_mul_descFactorial (p := p) (j := 2) (by omega) σ
  have he : (p + 1).descFactorial 2 = (p + 1) * p := by
    simp [Nat.descFactorial_succ, Nat.mul_comm]
  rw [he, show p + 1 - 2 = p - 1 by omega, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hh
  exact hh

private theorem factorial_weight_three {p : ℕ} (hp : 3 ≤ p) (σ : ℝ) :
    σ / (p + 1).factorial * ((p + 1 : ℝ) * p * (p - 1 : ℕ)) =
      σ / (p - 2).factorial := by
  have hh := factorial_weight_mul_descFactorial (p := p) (j := 3) (by omega) σ
  have he : (p + 1).descFactorial 3 = (p + 1) * p * (p - 1) := by
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, mul_one]
    rw [show p + 1 - 2 = p - 1 by omega, Nat.add_sub_cancel]
    ring
  rw [he, show p + 1 - 3 = p - 2 by omega] at hh
  push_cast at hh
  exact hh

/-- The actual second or third penalty derivative has the exact factorial directional bound. -/
theorem penalty_direction_le {p j : ℕ} (hp : 3 ≤ p) (hj : j = 2 ∨ j = 3)
    {σ : ℝ} (hσ : 0 ≤ σ) (s v : E) (hv : ‖v‖ = 1) :
    |σ / (p + 1).factorial *
      iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ (p + 1)) s (fun _ => v)| ≤
        σ / (p - j + 1).factorial * ‖s‖ ^ (p - j + 1) := by
  have hc : 0 ≤ σ / (p + 1).factorial := by positivity
  rw [abs_mul, abs_of_nonneg hc]
  rcases hj with rfl | rfl
  · have hh := mul_le_mul_of_nonneg_left
      (NormPower.abs_iteratedFDeriv_two_norm_pow_le hp s v hv) hc
    have he : σ / (p + 1).factorial * ((p + 1 : ℝ) * p * ‖s‖ ^ (p - 1)) =
        σ / (p - 1).factorial * ‖s‖ ^ (p - 1) := by
      rw [←mul_assoc, factorial_weight_two hp]
    rw [he] at hh
    simpa only [show p - 2 + 1 = p - 1 by omega] using hh
  · have hh := mul_le_mul_of_nonneg_left
      (NormPower.abs_iteratedFDeriv_three_norm_pow_le hp s v hv) hc
    have he : σ / (p + 1).factorial *
        ((p + 1 : ℝ) * p * (p - 1 : ℕ) * ‖s‖ ^ (p - 2)) =
        σ / (p - 2).factorial * ‖s‖ ^ (p - 2) := by
      rw [←mul_assoc, factorial_weight_three hp]
    rw [he] at hh
    simpa only [show p - 3 + 1 = p - 2 by omega] using hh

/-- The genuine model's second and third directional errors combine the sharp
Taylor derivative remainder and the actual regularization derivative. -/
theorem directional_error_le {p j : ℕ} (hp : 3 ≤ p) (hj : j = 2 ∨ j = 3)
    {f : E → ℝ} (hf : ContDiff ℝ p f) {L σ : ℝ} (hL : 0 ≤ L) (hσ : 0 ≤ σ)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (x : E) {s : E} (hs : s ≠ 0) (v : E) (hv : ‖v‖ = 1) :
    |iteratedFDeriv ℝ j f (x + s) (fun _ => v) -
      iteratedFDeriv ℝ j (model f p x σ) s (fun _ => v)| ≤
        (L + σ) / (p - j + 1).factorial * ‖s‖ ^ (p - j + 1) := by
  have hjp : j ≤ p := by rcases hj with rfl | rfl <;> omega
  have herr := norm_iteratedFDeriv_sub_eval_le_lipschitz
    (C := univ) (D := univ) isOpen_univ (Subset.refl _) convex_univ
    hf.contDiffOn hL (fun y _ z _ => hlip y z) hjp (mem_univ x) (mem_univ (x + s))
  have he := (iteratedFDeriv ℝ j f (x + s) - iteratedFDeriv ℝ j (eval f p x) s).le_opNorm
    (fun _ => v)
  simp only [sub_apply, Fin.prod_const, hv, one_pow, mul_one, Real.norm_eq_abs] at he
  have hTaylor := he.trans herr
  have hpen := penalty_direction_le hp hj hσ s v hv
  rw [iteratedFDeriv_model f p j x σ hs, add_apply, smul_apply, smul_eq_mul]
  calc _ = |(iteratedFDeriv ℝ j f (x + s) (fun _ => v) -
        iteratedFDeriv ℝ j (eval f p x) s (fun _ => v)) -
        σ / (p + 1).factorial *
          iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ (p + 1)) s (fun _ => v)| := by congr 1; ring
       _ ≤ _ := (abs_sub _ _).trans (add_le_add hTaylor hpen) |>.trans_eq (by ring)

/-- The source's small-curvature directions for the actual regularized model (4.1.14). -/
def smallModelDirections (f : E → ℝ) (p : ℕ) (x s : E) (σ θ₂ : ℝ) : Set E :=
  {v | ‖v‖ = 1 ∧
    |iteratedFDeriv ℝ 2 (model f p x σ) s (fun _ => v)| ≤ θ₂ * ‖s‖ ^ (p - 1)}

/-- Membership records precisely a unit direction and the actual model-curvature bound. -/
theorem mem_smallModelDirections_iff (f : E → ℝ) (p : ℕ) (x s : E) (σ θ₂ : ℝ) (v : E) :
    v ∈ smallModelDirections f p x s σ θ₂ ↔ ‖v‖ = 1 ∧
      |iteratedFDeriv ℝ 2 (model f p x σ) s (fun _ => v)| ≤
        θ₂ * ‖s‖ ^ (p - 1) := Iff.rfl

/-- The three actual derivative termination tests for an ARp model step.
The second condition is the equivalent unit-direction least-curvature test. -/
structure StepConditions (f : E → ℝ) (p : ℕ) (x s : E)
    (σ θ₁ θ₂ θ₃ : ℝ) : Prop where
  first : ‖fderiv ℝ (model f p x σ) s‖ ≤ θ₁ * ‖s‖ ^ p
  second : ∀ v : E, ‖v‖ = 1 →
    -θ₂ * ‖s‖ ^ (p - 1) ≤ iteratedFDeriv ℝ 2 (model f p x σ) s (fun _ => v)
  third : ∀ v ∈ smallModelDirections f p x s σ θ₂,
    |iteratedFDeriv ℝ 3 (model f p x σ) s (fun _ => v)| ≤ θ₃ * ‖s‖ ^ (p - 2)

/-- The actual Taylor gradient error, model gradient and penalty gradient control
the genuine objective gradient at the trial point. -/
theorem trial_gradient_le {p : ℕ} (hp : 1 ≤ p) {f : E → ℝ} (hf : ContDiff ℝ p f)
    {L σ θ₁ : ℝ} (hL : 0 ≤ L) (hσ : 0 ≤ σ)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (x : E) {s : E} (hs : s ≠ 0)
    (hfirst : ‖fderiv ℝ (model f p x σ) s‖ ≤ θ₁ * ‖s‖ ^ p) :
    ‖fderiv ℝ f (x + s)‖ ≤ ((L + σ) / p.factorial + θ₁) * ‖s‖ ^ p := by
  have heq : fderiv ℝ (eval f p x) s = fderiv ℝ (model f p x σ) s -
      (σ / (p + 1).factorial) • fderiv ℝ (fun z : E => ‖z‖ ^ (p + 1)) s := by
    rw [fderiv_model f p x σ hs]
    abel
  have ht := norm_add_le (fderiv ℝ f (x + s) - fderiv ℝ (eval f p x) s)
    (fderiv ℝ (eval f p x) s)
  rw [sub_add_cancel] at ht
  have hT : ‖fderiv ℝ (eval f p x) s‖ ≤ ‖fderiv ℝ (model f p x σ) s‖ +
      ‖(σ / (p + 1).factorial) • fderiv ℝ (fun z : E => ‖z‖ ^ (p + 1)) s‖ := by
    rw [heq]
    exact norm_sub_le _ _
  have hh := ht.trans (add_le_add (norm_first_error_le hp hf hL hlip x s) hT)
  have hp' := norm_first_penalty hp hσ s
  rw [hp'] at hh
  have hc := hh.trans (add_le_add le_rfl (add_le_add hfirst le_rfl))
  convert hc using 1
  ring

/-- The actual model's curvature test controls the genuine trial Hessian in every unit direction. -/
theorem trial_curvature_lower {p : ℕ} (hp : 3 ≤ p) {f : E → ℝ} (hf : ContDiff ℝ p f)
    {L σ θ₂ : ℝ} (hL : 0 ≤ L) (hσ : 0 ≤ σ)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (x : E) {s : E} (hs : s ≠ 0) (v : E) (hv : ‖v‖ = 1)
    (hsecond : -θ₂ * ‖s‖ ^ (p - 1) ≤
      iteratedFDeriv ℝ 2 (model f p x σ) s (fun _ => v)) :
    -((L + σ) / (p - 1).factorial + θ₂) * ‖s‖ ^ (p - 1) ≤
      iteratedFDeriv ℝ 2 f (x + s) (fun _ => v) := by
  have hh := directional_error_le hp (Or.inl rfl) hf hL hσ hlip x hs v hv
  rw [show p - 2 + 1 = p - 1 by omega] at hh
  linarith [(abs_le.mp hh).1]

/-- Every small-model-curvature direction has the source's absolute trial Hessian bound. -/
theorem trial_small_curvature_le {p : ℕ} (hp : 3 ≤ p) {f : E → ℝ} (hf : ContDiff ℝ p f)
    {L σ θ₂ : ℝ} (hL : 0 ≤ L) (hσ : 0 ≤ σ)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (x : E) {s : E} (hs : s ≠ 0) {v : E}
    (hv : v ∈ smallModelDirections f p x s σ θ₂) :
    |iteratedFDeriv ℝ 2 f (x + s) (fun _ => v)| ≤
      ((L + σ) / (p - 1).factorial + θ₂) * ‖s‖ ^ (p - 1) := by
  have hh := directional_error_le hp (Or.inl rfl) hf hL hσ hlip x hs v hv.1
  rw [show p - 2 + 1 = p - 1 by omega] at hh
  have htri := abs_add_le
    (iteratedFDeriv ℝ 2 f (x + s) (fun _ => v) -
      iteratedFDeriv ℝ 2 (model f p x σ) s (fun _ => v))
    (iteratedFDeriv ℝ 2 (model f p x σ) s (fun _ => v))
  rw [sub_add_cancel] at htri
  have hb := htri.trans (add_le_add hh hv.2)
  convert hb using 1
  ring

/-- The actual third-order model test controls the genuine third derivative in
all of the source's small-model-curvature directions. -/
theorem trial_third_le {p : ℕ} (hp : 3 ≤ p) {f : E → ℝ} (hf : ContDiff ℝ p f)
    {L σ θ₁ θ₂ θ₃ : ℝ} (hL : 0 ≤ L) (hσ : 0 ≤ σ)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (x : E) {s : E} (hs : s ≠ 0) (hstep : StepConditions f p x s σ θ₁ θ₂ θ₃)
    {v : E} (hv : v ∈ smallModelDirections f p x s σ θ₂) :
    |iteratedFDeriv ℝ 3 f (x + s) (fun _ => v)| ≤
      ((L + σ) / (p - 2).factorial + θ₃) * ‖s‖ ^ (p - 2) := by
  have hh := directional_error_le hp (Or.inr rfl) hf hL hσ hlip x hs v hv.1
  rw [show p - 3 + 1 = p - 2 by omega] at hh
  have htri := abs_add_le
    (iteratedFDeriv ℝ 3 f (x + s) (fun _ => v) -
      iteratedFDeriv ℝ 3 (model f p x σ) s (fun _ => v))
    (iteratedFDeriv ℝ 3 (model f p x σ) s (fun _ => v))
  rw [sub_add_cancel] at htri
  have hb := htri.trans (add_le_add hh (hstep.third v hv))
  convert hb using 1
  ring

end HighOrderRegularization

namespace HighOrderRegularization
open TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The factorial-normalized step coefficient for a derivative whose remainder has degree `m`. -/
noncomputable def stepConstant (m : ℕ) (L σmax θ : ℝ) : ℝ :=
  m.factorial / (L + σmax + θ * m.factorial)

/-- The step coefficient is positive for the source's positive data. -/
theorem stepConstant_pos (m : ℕ) {L σmax θ : ℝ} (hL : 0 < L)
    (hσ : 0 ≤ σmax) (hθ : 0 ≤ θ) : 0 < stepConstant m L σmax θ := by
  unfold stepConstant
  positivity

/-- A bound on a trial derivative inverts to the exact printed step coefficient. -/
theorem stepConstant_mul_le {m : ℕ} {L σ σmax θ r u : ℝ}
    (hL : 0 < L) (hσmax : 0 ≤ σmax) (hθ : 0 ≤ θ) (hσ : σ ≤ σmax)
    (hr : 0 ≤ r) (hu : u ≤ ((L + σ) / m.factorial + θ) * r) :
    stepConstant m L σmax θ * u ≤ r := by
  have hd : 0 < L + σmax + θ * m.factorial := by positivity
  have hf : (0 : ℝ) < m.factorial := by positivity
  have hlarge : u ≤ ((L + σmax) / m.factorial + θ) * r := by
    apply hu.trans
    gcongr
  unfold stepConstant
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).mpr
  have hm := mul_le_mul_of_nonneg_left hlarge hf.le
  convert hm using 1
  field_simp

/-- The reciprocal coefficient is exactly the upper derivative multiplier. -/
theorem inv_stepConstant (m : ℕ) (L σmax θ : ℝ) :
    1 / stepConstant m L σmax θ = (L + σmax) / m.factorial + θ := by
  unfold stepConstant
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  field_simp

namespace ModelTrace
variable {f : E → ℝ} {p : ℕ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ σmin L θ₁ θ₂ θ₃ : ℝ} {N : ℕ}

/-- Strict improvement of the actual model excludes the zero step. -/
theorem step_ne_zero (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    {i : ℕ} (hi : i < N) : s i ≠ 0 := by
  intro hz
  have hh := h.improvement i hi
  rw [hz] at hh
  exact lt_irrefl _ hh

/-- The accepted endpoint is the actual trial point. -/
theorem successful_point (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i) : x (i + 1) = x i + s i := by
  rw [h.point_update i hi, ite_eq_left hs]

/-- The first-order step lower bound, with the exact source coefficient. -/
theorem step_lower_first (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ p f) (hL : 0 < L) (hθ : 0 ≤ θ₁)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i)
    (hfirst : ‖fderiv ℝ (model f p (x i) (σ i)) (s i)‖ ≤ θ₁ * ‖s i‖ ^ p) :
    stepConstant p L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₁ *
      ‖fderiv ℝ f (x (i + 1))‖ ≤ ‖s i‖ ^ p := by
  rw [h.successful_point hi hs]
  apply stepConstant_mul_le hL
    ((h.updates.pos (Nat.zero_le N)).le.trans (le_max_left _ _)) hθ
    (h.parameter_le hf hL.le hlip hi.le) (pow_nonneg (norm_nonneg _) _)
  exact trial_gradient_le h.order_pos hf hL.le (h.updates.pos hi.le).le hlip
    (x i) (h.step_ne_zero hi) hfirst

/-- The second-order step bound uses a least eigenpair of the actual endpoint Hessian. -/
theorem step_lower_second [CompleteSpace E]
    (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hp : 3 ≤ p) (hf : ContDiff ℝ p f) (hL : 0 < L) (hθ : 0 ≤ θ₂)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i)
    (hsecond : ∀ v : E, ‖v‖ = 1 → -θ₂ * ‖s i‖ ^ (p - 1) ≤
      iteratedFDeriv ℝ 2 (model f p (x i) (σ i)) (s i) (fun _ => v))
    {μ : ℝ} {u : E} (heigen : SecondOrderTrustRegion.IsLeastEigenpair f (x (i + 1)) μ u) :
    stepConstant (p - 1) L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₂ * max 0 (-μ) ≤
      ‖s i‖ ^ (p - 1) := by
  have hb := trial_curvature_lower hp hf hL.le (h.updates.pos hi.le).le hlip
    (x i) (h.step_ne_zero hi) u heigen.unit (hsecond u heigen.unit)
  rw [←h.successful_point hi hs, TaylorModel.tensor_curvature_of_eigenvector f _ u
    heigen.unit heigen.eigenvector] at hb
  apply stepConstant_mul_le hL
    ((h.updates.pos (Nat.zero_le N)).le.trans (le_max_left _ _)) hθ
    (h.parameter_le hf hL.le hlip hi.le) (pow_nonneg (norm_nonneg _) _)
  apply max_le
  · have hσi := (h.updates.pos hi.le).le
    positivity
  · linarith

/-- The third-order bound holds for every actual small-model-curvature direction. -/
theorem step_lower_third (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hp : 3 ≤ p) (hf : ContDiff ℝ p f) (hL : 0 < L) (hθ : 0 ≤ θ₃)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i)
    (hthird : ∀ v ∈ smallModelDirections f p (x i) (s i) (σ i) θ₂,
      |iteratedFDeriv ℝ 3 (model f p (x i) (σ i)) (s i) (fun _ => v)| ≤
        θ₃ * ‖s i‖ ^ (p - 2))
    {v : E} (hv : v ∈ smallModelDirections f p (x i) (s i) (σ i) θ₂) :
    stepConstant (p - 2) L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₃ *
      |iteratedFDeriv ℝ 3 f (x (i + 1)) (fun _ => v)| ≤ ‖s i‖ ^ (p - 2) := by
  rw [h.successful_point hi hs]
  apply stepConstant_mul_le hL
    ((h.updates.pos (Nat.zero_le N)).le.trans (le_max_left _ _)) hθ
    (h.parameter_le hf hL.le hlip hi.le) (pow_nonneg (norm_nonneg _) _)
  have hh := directional_error_le hp (Or.inr rfl) hf hL.le (h.updates.pos hi.le).le
    hlip (x i) (h.step_ne_zero hi) v hv.1
  have ht := (abs_add_le
    (iteratedFDeriv ℝ 3 f (x i + s i) (fun _ => v) -
      iteratedFDeriv ℝ 3 (model f p (x i) (σ i)) (s i) (fun _ => v))
    (iteratedFDeriv ℝ 3 (model f p (x i) (σ i)) (s i) (fun _ => v)))
  rw [sub_add_cancel] at ht
  have hb := ht.trans (add_le_add hh (hthird v hv))
  convert hb using 1
  rw [show p - 3 + 1 = p - 2 by omega]
  ring

/-- Small model curvature implies the endpoint's absolute Hessian bound (4.1.23). -/
theorem small_curvature_le (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hp : 3 ≤ p) (hf : ContDiff ℝ p f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i)
    {v : E} (hv : v ∈ smallModelDirections f p (x i) (s i) (σ i) θ₂) :
    |iteratedFDeriv ℝ 2 f (x (i + 1)) (fun _ => v)| ≤
      1 / stepConstant (p - 1) L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₂ *
        ‖s i‖ ^ (p - 1) := by
  rw [h.successful_point hi hs, inv_stepConstant]
  have hh := trial_small_curvature_le hp hf hL (h.updates.pos hi.le).le hlip
    (x i) (h.step_ne_zero hi) hv
  apply hh.trans
  gcongr
  exact h.parameter_le hf hL hlip hi.le

end ModelTrace
end HighOrderRegularization

namespace HighOrderRegularization
/-- Raising a natural-power step bound yields the exact fractional-power derivative budget. -/
theorem rpow_step_lower {m n : ℕ} (hm : 0 < m) {κ u r : ℝ}
    (hκ : 0 ≤ κ) (hu : 0 ≤ u) (hr : 0 ≤ r) (hb : κ * u ≤ r ^ m) :
    κ ^ ((n : ℝ) / m) * u ^ ((n : ℝ) / m) ≤ r ^ n := by
  have hpow := Real.rpow_le_rpow (mul_nonneg hκ hu) hb
    (show 0 ≤ (n : ℝ) / m by positivity)
  rw [Real.mul_rpow hκ hu] at hpow
  have he : (r ^ m) ^ ((n : ℝ) / m) = r ^ n := by
    rw [←Real.rpow_natCast, ←Real.rpow_mul hr]
    have hm' : (m : ℝ) ≠ 0 := by positivity
    rw [mul_div_cancel₀ _ hm', Real.rpow_natCast]
  rwa [he] at hpow

/-- The successful-decrease constant multiplying an order-`j` endpoint measure. -/
noncomputable def decreaseConstant (p m : ℕ) (η₁ σmin L σmax θ : ℝ) : ℝ :=
  η₁ * σmin / (p + 1).factorial *
    stepConstant m L σmax θ ^ (((p + 1 : ℕ) : ℝ) / m)

/-- All successful-decrease constants are positive for the source data. -/
theorem decreaseConstant_pos (p m : ℕ) {η₁ σmin L σmax θ : ℝ}
    (hη : 0 < η₁) (hmin : 0 < σmin) (hL : 0 < L) (hσ : 0 ≤ σmax) (hθ : 0 ≤ θ) :
    0 < decreaseConstant p m η₁ σmin L σmax θ := by
  have hk := stepConstant_pos m hL hσ hθ
  unfold decreaseConstant
  positivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace ModelTrace
variable {f : E → ℝ} {p : ℕ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ σmin L : ℝ} {N : ℕ}

/-- A natural-power step bound transfers through the actual accepted objective decrease. -/
theorem decrease_of_step_lower (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    {i m : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i) (hm : 0 < m)
    {κ u : ℝ} (hκ : 0 ≤ κ) (hu : 0 ≤ u) (hb : κ * u ≤ ‖s i‖ ^ m) :
    η₁ * σmin / (p + 1).factorial * κ ^ (((p + 1 : ℕ) : ℝ) / m) *
      u ^ (((p + 1 : ℕ) : ℝ) / m) ≤ f (x i) - f (x (i + 1)) := by
  have hh := mul_le_mul_of_nonneg_left
    (rpow_step_lower (n := p + 1) hm hκ hu (norm_nonneg _) hb)
    (show 0 ≤ η₁ * σmin / (p + 1).factorial from
      div_nonneg (mul_nonneg h.updates.eta1_pos.le h.updates.min_pos.le) (Nat.cast_nonneg _))
  calc _ = η₁ * σmin / (p + 1).factorial *
        (κ ^ (((p + 1 : ℕ) : ℝ) / m) * u ^ (((p + 1 : ℕ) : ℝ) / m)) := by ring
       _ ≤ η₁ * σmin / (p + 1).factorial * ‖s i‖ ^ (p + 1) := hh
       _ ≤ _ := (h.successful_decrease hi hs).le

/-- The full first-order successful objective decrease with its exact source constant. -/
theorem decrease_first (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ p f) (hL : 0 < L) {θ₁ : ℝ} (hθ : 0 ≤ θ₁)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i)
    (hfirst : ‖fderiv ℝ (model f p (x i) (σ i)) (s i)‖ ≤ θ₁ * ‖s i‖ ^ p) :
    decreaseConstant p p η₁ σmin L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₁ *
      ‖fderiv ℝ f (x (i + 1))‖ ^ (((p + 1 : ℕ) : ℝ) / p) ≤
        f (x i) - f (x (i + 1)) := by
  exact h.decrease_of_step_lower hi hs h.order_pos
    (stepConstant_pos p hL
      ((h.updates.pos (Nat.zero_le N)).le.trans (le_max_left _ _)) hθ).le
    (norm_nonneg _) (h.step_lower_first hf hL hθ hlip hi hs hfirst)

/-- The full second-order successful objective decrease for the actual least Hessian pair. -/
theorem decrease_second [CompleteSpace E]
    (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hp : 3 ≤ p) (hf : ContDiff ℝ p f) (hL : 0 < L) {θ₂ : ℝ} (hθ : 0 ≤ θ₂)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i)
    (hsecond : ∀ v : E, ‖v‖ = 1 → -θ₂ * ‖s i‖ ^ (p - 1) ≤
      iteratedFDeriv ℝ 2 (model f p (x i) (σ i)) (s i) (fun _ => v))
    {μ : ℝ} {u : E} (heigen : SecondOrderTrustRegion.IsLeastEigenpair f (x (i + 1)) μ u) :
    decreaseConstant p (p - 1) η₁ σmin L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₂ *
      (max 0 (-μ)) ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)) ≤
        f (x i) - f (x (i + 1)) := by
  exact h.decrease_of_step_lower hi hs (by omega : 0 < p - 1)
    (stepConstant_pos (p - 1) hL
      ((h.updates.pos (Nat.zero_le N)).le.trans (le_max_left _ _)) hθ).le
    (le_max_left _ _) (h.step_lower_second hp hf hL hθ hlip hi hs hsecond heigen)

/-- The full third-order successful decrease in every actual small-model-curvature direction. -/
theorem decrease_third (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hp : 3 ≤ p) (hf : ContDiff ℝ p f) (hL : 0 < L) {θ₂ θ₃ : ℝ} (hθ : 0 ≤ θ₃)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i)
    (hthird : ∀ v ∈ smallModelDirections f p (x i) (s i) (σ i) θ₂,
      |iteratedFDeriv ℝ 3 (model f p (x i) (σ i)) (s i) (fun _ => v)| ≤
        θ₃ * ‖s i‖ ^ (p - 2))
    {v : E} (hv : v ∈ smallModelDirections f p (x i) (s i) (σ i) θ₂) :
    decreaseConstant p (p - 2) η₁ σmin L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₃ *
      |iteratedFDeriv ℝ 3 f (x (i + 1)) (fun _ => v)| ^
        (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)) ≤ f (x i) - f (x (i + 1)) := by
  exact h.decrease_of_step_lower hi hs (by omega : 0 < p - 2)
    (stepConstant_pos (p - 2) hL
      ((h.updates.pos (Nat.zero_le N)).le.trans (le_max_left _ _)) hθ).le
    (abs_nonneg _) (h.step_lower_third hp hf hL hθ hlip hi hs hthird hv)

end ModelTrace
end HighOrderRegularization
