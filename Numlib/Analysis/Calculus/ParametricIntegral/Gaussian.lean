import Numlib.Probability.Distributions.Gaussian.Moments
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Differentiation of Gaussian projection jets

A scalar jet evaluated on a Gaussian projection and multiplied by fixed
projection directions has a genuine Fréchet derivative. Polynomial growth of
the actual scalar jets supplies Gaussian moment domination uniformly on a
neighborhood. This gives the actual derivative of its integral, with no
interchange or norm-power derivative identity assumed.
-/

open MeasureTheory
open scoped Topology
namespace ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuine scalar iterated derivative on a linear projection, multiplied
by the projections of fixed directions. -/
noncomputable def projectionJet (f : ℝ → ℝ) (j : ℕ) (x : E)
    (v : Fin j → E) (g : E) : ℝ :=
  iteratedDeriv j f (inner ℝ g x) * ∏ i, inner ℝ g (v i)

/-- The continuous linear map obtained by differentiating a projection jet
in its base point. -/
noncomputable def projectionJetDeriv (f : ℝ → ℝ) (j : ℕ) (x : E)
    (v : Fin j → E) (g : E) : E →L[ℝ] ℝ :=
  (iteratedDeriv (j + 1) f (inner ℝ g x) * ∏ i, inner ℝ g (v i)) • innerSL ℝ g

/-- The projection jet is the actual scalar jet times the product of its
fixed direction projections. -/
theorem projectionJet_eq (f : ℝ → ℝ) (j : ℕ) (x : E) (v : Fin j → E) (g : E) :
    projectionJet f j x v g = iteratedDeriv j f (inner ℝ g x) * ∏ i, inner ℝ g (v i) := rfl

/-- Evaluation of the projection-jet derivative on a direction. -/
theorem projectionJetDeriv_apply (f : ℝ → ℝ) (j : ℕ) (x : E)
    (v : Fin j → E) (g w : E) : projectionJetDeriv f j x v g w =
      iteratedDeriv (j + 1) f (inner ℝ g x) * (∏ i, inner ℝ g (v i)) * inner ℝ g w := by
  simp only [projectionJetDeriv, smul_apply, smul_eq_mul, innerSL_apply_apply]

/-- Appending a first direction to a next-order projection jet evaluates
the preceding projection-jet derivative on that direction. -/
theorem projectionJet_cons (f : ℝ → ℝ) (j : ℕ) (x : E)
    (v : Fin j → E) (g w : E) :
    projectionJet f (j + 1) x (Fin.cons w v) g = projectionJetDeriv f j x v g w := by
  simp only [projectionJet_eq, projectionJetDeriv_apply, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  ring

/-- The actual derivative of a projection jet follows from finite scalar
smoothness and the chain and product rules. -/
theorem hasFDerivAt_projectionJet {f : ℝ → ℝ} {j : ℕ}
    (hf : ContDiff ℝ (j + 1 : ℕ) f) (x : E) (v : Fin j → E) (g : E) :
    HasFDerivAt (fun y => projectionJet f j y v g) (projectionJetDeriv f j x v g) x := by
  have hd := (hf.differentiable_iteratedDeriv' j (inner ℝ g x)).hasDerivAt
  rw [← iteratedDeriv_succ] at hd
  have hh := (hd.comp_hasFDerivAt x (innerSL ℝ g).hasFDerivAt).mul_const
    (∏ i, inner ℝ g (v i))
  simpa only [projectionJet, projectionJetDeriv, Function.comp_apply, smul_smul, mul_comm] using hh

private theorem prod_abs_inner_le (j : ℕ) (g : E) (v : Fin j → E) :
    (∏ i, |inner ℝ g (v i)|) ≤ ‖g‖ ^ j * ∏ i, ‖v i‖ := by
  calc _ ≤ ∏ i, ‖g‖ * ‖v i‖ := Finset.prod_le_prod₀
        (fun i _ => abs_nonneg _) (fun i _ => abs_real_inner_le_norm g (v i))
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

/-- A homogeneous polynomial growth bound on the actual scalar jet gives
a Gaussian norm-growth bound on the projection jet. -/
theorem norm_projectionJet_le {f : ℝ → ℝ} {m j : ℕ} {A : ℝ}
    (hj : j ≤ m) (hA : 0 ≤ A)
    (hf : ∀ t, |iteratedDeriv j f t| ≤ A * |t| ^ (m - j))
    (x : E) (v : Fin j → E) (g : E) :
    ‖projectionJet f j x v g‖ ≤ A * ‖x‖ ^ (m - j) *
      (∏ i, ‖v i‖) * ‖g‖ ^ m := by
  have ha := (hf (inner ℝ g x)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm g x) _)
      hA)
  have hb := prod_abs_inner_le j g v
  have he : ‖g‖ ^ (m - j) * ‖g‖ ^ j = ‖g‖ ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hj]
  calc
    ‖projectionJet f j x v g‖ = |iteratedDeriv j f (inner ℝ g x)| *
        ∏ i, |inner ℝ g (v i)| := by simp only [projectionJet, Real.norm_eq_abs, abs_mul,
          Finset.abs_prod]
    _ ≤ (A * (‖g‖ * ‖x‖) ^ (m - j)) * (‖g‖ ^ j * ∏ i, ‖v i‖) := by
      exact mul_le_mul ha hb (Finset.prod_nonneg fun i _ => abs_nonneg _)
        (by positivity)
    _ = A * ‖x‖ ^ (m - j) * (∏ i, ‖v i‖) *
        (‖g‖ ^ (m - j) * ‖g‖ ^ j) := by rw [mul_pow]; ring
    _ = _ := by rw [he]

/-- The corresponding growth bound on the next scalar jet controls the
full operator norm of the projection-jet derivative. -/
theorem norm_projectionJetDeriv_le {f : ℝ → ℝ} {m j : ℕ} {B : ℝ}
    (hj : j + 1 ≤ m) (hB : 0 ≤ B)
    (hf : ∀ t, |iteratedDeriv (j + 1) f t| ≤ B * |t| ^ (m - (j + 1)))
    (x : E) (v : Fin j → E) (g : E) :
    ‖projectionJetDeriv f j x v g‖ ≤ B * ‖x‖ ^ (m - (j + 1)) *
      (∏ i, ‖v i‖) * ‖g‖ ^ m := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  have hh := norm_projectionJet_le hj hB hf x (Fin.cons w v) g
  rw [projectionJet_cons] at hh
  simpa only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_assoc,
    mul_left_comm ‖w‖, mul_comm ‖w‖] using hh



/-- A continuous actual scalar jet makes the Gaussian projection kernel
continuous in its Gaussian argument. -/
theorem continuous_projectionJet {f : ℝ → ℝ} {j : ℕ}
    (hf : Continuous (iteratedDeriv j f)) (x : E) (v : Fin j → E) :
    Continuous (fun g : E => projectionJet f j x v g) := by
  unfold projectionJet
  exact (hf.comp (by fun_prop)).mul (by fun_prop)

/-- Continuity of the next scalar jet makes the derivative kernel
continuous in its Gaussian argument. -/
theorem continuous_projectionJetDeriv {f : ℝ → ℝ} {j : ℕ}
    (hf : Continuous (iteratedDeriv (j + 1) f)) (x : E) (v : Fin j → E) :
    Continuous (fun g : E => projectionJetDeriv f j x v g) := by
  unfold projectionJetDeriv
  exact ((hf.comp (by fun_prop)).mul (by fun_prop)).smul (innerSL ℝ).continuous

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Every natural norm moment of a finite-dimensional standard Gaussian
is integrable. -/
theorem integrable_norm_pow_stdGaussian (m : ℕ) :
    Integrable (fun g : E => ‖g‖ ^ m) (stdGaussian E) := by
  have hg : MemLp (id : E → E) m (stdGaussian E) :=
    IsGaussian.memLp_id (stdGaussian E) m (by simp)
  simpa only [id_eq] using hg.integrable_norm_pow'

/-- A continuous scalar jet with the stated homogeneous growth bound
gives an integrable Gaussian projection kernel. -/
theorem integrable_projectionJet {f : ℝ → ℝ} {m j : ℕ} {A : ℝ}
    (hj : j ≤ m) (hA : 0 ≤ A) (hcont : Continuous (iteratedDeriv j f))
    (hf : ∀ t, |iteratedDeriv j f t| ≤ A * |t| ^ (m - j))
    (x : E) (v : Fin j → E) :
    Integrable (fun g : E => projectionJet f j x v g) (stdGaussian E) := by
  apply ((integrable_norm_pow_stdGaussian (E := E) m).const_mul
    (A * ‖x‖ ^ (m - j) * ∏ i, ‖v i‖)).mono'
      (continuous_projectionJet hcont x v).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_projectionJet_le hj hA hf x v)

/-- Polynomial growth bounds on two consecutive actual scalar jets and
finite scalar smoothness justify differentiation of the Gaussian integral.
The derivative kernel is integrable and is the actual Fréchet derivative. -/
theorem integral_projectionJet_hasFDerivAt {f : ℝ → ℝ} {m j : ℕ} {A B : ℝ}
    (hj : j + 1 ≤ m) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcont : ContDiff ℝ (j + 1 : ℕ) f)
    (hf : ∀ t, |iteratedDeriv j f t| ≤ A * |t| ^ (m - j))
    (hf' : ∀ t, |iteratedDeriv (j + 1) f t| ≤ B * |t| ^ (m - (j + 1)))
    (x₀ : E) (v : Fin j → E) :
    Integrable (fun g : E => projectionJetDeriv f j x₀ v g) (stdGaussian E) ∧
      HasFDerivAt (fun x : E => ∫ g : E, projectionJet f j x v g ∂(stdGaussian E))
        (∫ g : E, projectionJetDeriv f j x₀ v g ∂(stdGaussian E)) x₀ := by
  have hc : Continuous (iteratedDeriv j f) :=
    hcont.continuous_iteratedDeriv j (by exact_mod_cast Nat.le_succ j)
  have hc' : Continuous (iteratedDeriv (j + 1) f) :=
    hcont.continuous_iteratedDeriv (j + 1) le_rfl
  let bound : E → ℝ := fun g => B * (‖x₀‖ + 1) ^ (m - (j + 1)) *
    (∏ i, ‖v i‖) * ‖g‖ ^ m
  have hbint : Integrable bound (stdGaussian E) :=
    (integrable_norm_pow_stdGaussian (E := E) m).const_mul _
  have hbloc (g x : E) (hx : x ∈ Metric.ball x₀ 1) :
      ‖projectionJetDeriv f j x v g‖ ≤ bound g := by
    have hxnorm : ‖x‖ ≤ ‖x₀‖ + 1 := by
      have hsub : ‖x - x₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
      have htri : ‖x‖ ≤ ‖x₀‖ + ‖x - x₀‖ := by
        have he : x₀ + (x - x₀) = x := by abel
        simpa only [he] using norm_add_le x₀ (x - x₀)
      linarith
    exact (norm_projectionJetDeriv_le hj hB hf' x v g).trans (by
      dsimp [bound]
      gcongr)
  have hderivint : Integrable (fun g : E => projectionJetDeriv f j x₀ v g)
      (stdGaussian E) := by
    exact hbint.mono' (continuous_projectionJetDeriv hc' x₀ v).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => hbloc g x₀ (Metric.mem_ball_self zero_lt_one))
  refine ⟨hderivint, ?_⟩
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun x g =>
    projectionJetDeriv f j x v g) (bound := bound) (Metric.ball_mem_nhds x₀ zero_lt_one)
  · exact Filter.Eventually.of_forall fun x =>
      (continuous_projectionJet hc x v).aestronglyMeasurable
  · exact integrable_projectionJet (by omega) hA hc hf x₀ v
  · exact (continuous_projectionJetDeriv hc' x₀ v).aestronglyMeasurable
  · exact Filter.Eventually.of_forall hbloc
  · exact hbint
  · exact Filter.Eventually.of_forall fun g x _ => hasFDerivAt_projectionJet hcont x v g

end ProbabilityTheory
