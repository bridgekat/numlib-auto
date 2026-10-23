import Numlib.Optimization.Composite.Optimality
import Numlib.Optimization.HighOrder.ModelDecrease
import Numlib.Optimization.EvaluationComplexity.ParameterUpdates
import Numlib.Analysis.Calculus.TaylorModel.Holder
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Composite Taylor errors and regularization parameter bounds

Componentwise smoothness of the residual map produces the exact square-root
of dimension factor in the composite Taylor remainder. No differentiability of
the outer Lipschitz function is used. The model, ratio and parameter components
of a regularization trace suffice for the uniform parameter bound.
-/

open Set TaylorModel ModelDecrease EvaluationComplexity
open scoped BigOperators

namespace Composite

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A common bound on every coordinate gives the square-root dimension bound
on the Euclidean norm, including dimension zero. -/
theorem norm_le_sqrt_dim_mul {m : ℕ} {v : EuclideanSpace ℝ (Fin m)} {B : ℝ}
    (hB : 0 ≤ B) (hv : ∀ i, |v i| ≤ B) : ‖v‖ ≤ Real.sqrt m * B := by
  have hs : ‖v‖ ^ 2 ≤ (m : ℝ) * B ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin m, B ^ 2 := Finset.sum_le_sum (fun i _ => by
        have hi := hv i
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (v i)) hi 2)
      _ = _ := by simp
  have hroot := Real.sq_sqrt (show (0 : ℝ) ≤ m by positivity)
  have hnonneg : 0 ≤ Real.sqrt m * B := mul_nonneg (Real.sqrt_nonneg _) hB
  nlinarith

/-- The residual's genuine Taylor error under componentwise highest-derivative
Lipschitz bounds. This is where the source's `√m` factor is required. -/
theorem norm_sub_eval_le_componentwise {m p : ℕ}
    {c : E → EuclideanSpace ℝ (Fin m)} {Lc : ℝ}
    (hc : ∀ i, ContDiff ℝ (p + 1) (fun z => c z i)) (hLc : 0 ≤ Lc)
    (hlip : ∀ i y z,
      ‖iteratedFDeriv ℝ (p + 1) (fun w => c w i) y -
        iteratedFDeriv ℝ (p + 1) (fun w => c w i) z‖ ≤ Lc * ‖y - z‖)
    (x s : E) :
    ‖c (x + s) - eval c (p + 1) x s‖ ≤
      Real.sqrt m * Lc * ‖s‖ ^ (p + 2) / (p + 2).factorial := by
  have hcv : ContDiff ℝ (p + 1) c := (contDiff_piLp 2).mpr hc
  have hcoord (i : Fin m) :
      |(c (x + s) - eval c (p + 1) x s) i| ≤
        Lc * ‖s‖ ^ (p + 2) / (p + 2).factorial := by
    have heval := map_eval (EuclideanSpace.proj (𝕜 := ℝ) i) (x := x) hcv.contDiffAt s
    have herr := abs_sub_eval_le_lipschitz isOpen_univ (Subset.refl univ)
      convex_univ (hc i).contDiffOn hLc (fun y _ z _ => hlip i y z)
      (mem_univ x) (mem_univ (x + s))
    change |c (x + s) i - _| ≤ _
    convert herr using 1
    congr 2
    exact heval.symm
  convert norm_le_sqrt_dim_mul (by positivity) hcoord using 1
  ring

/-- The actual composite objective differs from its generalized Taylor model
by at most the combined smoothness constant times the factorial-normalized power. -/
theorem abs_sub_taylorModel_le {m p : ℕ}
    {f : E → ℝ} {c : E → EuclideanSpace ℝ (Fin m)} {h : EuclideanSpace ℝ (Fin m) → ℝ}
    {Lf Lc : ℝ} {K : NNReal}
    (hf : ContDiff ℝ (p + 1) f) (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc)
    (hc : ∀ i, ContDiff ℝ (p + 1) (fun z => c z i))
    (hlipf : ∀ y z, ‖iteratedFDeriv ℝ (p + 1) f y - iteratedFDeriv ℝ (p + 1) f z‖ ≤
      Lf * ‖y - z‖)
    (hlipc : ∀ i y z, ‖iteratedFDeriv ℝ (p + 1) (fun w => c w i) y -
      iteratedFDeriv ℝ (p + 1) (fun w => c w i) z‖ ≤ Lc * ‖y - z‖)
    (hh : LipschitzWith K h) (x s : E) :
    |f (x + s) + h (c (x + s)) - taylorModel f c h (p + 1) x s| ≤
      (Lf + Real.sqrt m * (K : ℝ) * Lc) * ‖s‖ ^ (p + 2) / (p + 2).factorial := by
  have hferr := abs_sub_eval_le_lipschitz isOpen_univ (Subset.refl univ)
    convex_univ hf.contDiffOn hLf (fun y _ z _ => hlipf y z)
    (mem_univ x) (mem_univ (x + s))
  have hcerr := norm_sub_eval_le_componentwise hc hLc hlipc x s
  have hherr := hh.dist_le_mul (c (x + s)) (eval c (p + 1) x s)
  rw [Real.dist_eq, dist_eq_norm] at hherr
  have hsum := (abs_add_le (f (x + s) - eval f (p + 1) x s)
    (h (c (x + s)) - h (eval c (p + 1) x s))).trans
      (add_le_add hferr (hherr.trans (mul_le_mul_of_nonneg_left hcerr K.coe_nonneg)))
  convert hsum using 1
  · congr 1
    unfold taylorModel
    ring
  · ring

/-- The actual norm-power regularization of the composite Taylor model. -/
noncomputable def regularizedModel {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → ℝ) (c : E → F) (h : F → ℝ) (p : ℕ) (x : E) (σ : ℝ) (s : E) : ℝ :=
  penalized (taylorModel f c h p x) p σ s

/-- Model-improvement, actual objective ratio and exact three-case parameter
updates. This component trace does not encode step stationarity or termination. -/
structure ModelTrace {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → ℝ) (c : E → F) (h : F → ℝ) (p : ℕ)
    (x s : ℕ → E) (σ ρ : ℕ → ℝ) (η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ) (N : ℕ) : Prop where
  updates : RegularizationParameterUpdates σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N
  improvement : ∀ i < N,
    regularizedModel f c h p (x i) (σ i) (s i) < regularizedModel f c h p (x i) (σ i) 0
  ratio : ∀ i < N, ρ i =
    (f (x i) + h (c (x i)) - (f (x i + s i) + h (c (x i + s i)))) /
      (taylorModel f c h p (x i) 0 - taylorModel f c h p (x i) (s i))

namespace ModelTrace
variable {m p : ℕ} {f : E → ℝ} {c : E → EuclideanSpace ℝ (Fin m)}
  {h : EuclideanSpace ℝ (Fin m) → ℝ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ σmin Lf Lc : ℝ} {K : NNReal} {N : ℕ}

/-- Model improvement supplies the true composite Taylor decrease. -/
theorem model_decrease (ht : ModelTrace f c h p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    {i : ℕ} (hi : i < N) :
    σ i / ((p + 1).factorial : ℝ) * ‖s i‖ ^ (p + 1) <
      taylorModel f c h p (x i) 0 - taylorModel f c h p (x i) (s i) :=
  penalty_lt_decrement _ _ _ _ (ht.improvement i hi)

/-- The actual ratio denominator is strictly positive. -/
theorem denominator_pos (ht : ModelTrace f c h p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    {i : ℕ} (hi : i < N) :
    0 < taylorModel f c h p (x i) 0 - taylorModel f c h p (x i) (s i) :=
by
  have hσ := ht.updates.pos (show i ≤ N by omega)
  exact lt_of_le_of_lt (by positivity : 0 ≤ σ i / ((p + 1).factorial : ℝ) *
    ‖s i‖ ^ (p + 1)) (ht.model_decrease hi)

/-- The sharp composite value error guarantees very successful acceptance
once the parameter reaches the combined Lipschitz threshold. -/
theorem very_successful
    (ht : ModelTrace f c h (p + 1) x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ (p + 1) f) (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc)
    (hc : ∀ i, ContDiff ℝ (p + 1) (fun z => c z i))
    (hlipf : ∀ y z, ‖iteratedFDeriv ℝ (p + 1) f y - iteratedFDeriv ℝ (p + 1) f z‖ ≤
      Lf * ‖y - z‖)
    (hlipc : ∀ i y z, ‖iteratedFDeriv ℝ (p + 1) (fun w => c w i) y -
      iteratedFDeriv ℝ (p + 1) (fun w => c w i) z‖ ≤ Lc * ‖y - z‖)
    (hh : LipschitzWith K h) {i : ℕ} (hi : i < N)
    (hlarge : (Lf + Real.sqrt m * (K : ℝ) * Lc) / (1 - η₂) ≤ σ i) : η₂ ≤ ρ i := by
  have hη : 0 < 1 - η₂ := sub_pos.mpr ht.updates.eta2_lt_one
  have herr := abs_sub_taylorModel_le hf hLf hLc hc hlipf hlipc hh (x i) (s i)
  have hd := mul_le_mul_of_nonneg_left (ht.model_decrease hi).le hη.le
  have hm := mul_le_mul_of_nonneg_right ((div_le_iff₀ hη).mp hlarge)
    (show 0 ≤ ‖s i‖ ^ (p + 2) / ((p + 2).factorial : ℝ) by positivity)
  have he : f (x i + s i) + h (c (x i + s i)) - taylorModel f c h (p + 1) (x i) (s i) ≤
      (1 - η₂) * (taylorModel f c h (p + 1) (x i) 0 -
        taylorModel f c h (p + 1) (x i) (s i)) := by
    have he1 := (abs_le.mp herr).2
    calc
      _ ≤ (Lf + Real.sqrt m * (K : ℝ) * Lc) * ‖s i‖ ^ (p + 2) /
          (p + 2).factorial := he1
      _ ≤ σ i * (1 - η₂) * ‖s i‖ ^ (p + 2) / (p + 2).factorial := by
        convert hm using 1 <;> ring
      _ ≤ _ := by convert hd using 1; ring
  rw [ht.ratio i hi]
  apply (le_div_iff₀ (ht.denominator_pos hi)).mpr
  rw [taylorModel_zero] at he ⊢
  linarith

/-- The exact update rule bounds every regularization parameter uniformly. -/
theorem parameter_le
    (ht : ModelTrace f c h (p + 1) x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ (p + 1) f) (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc)
    (hc : ∀ i, ContDiff ℝ (p + 1) (fun z => c z i))
    (hlipf : ∀ y z, ‖iteratedFDeriv ℝ (p + 1) f y - iteratedFDeriv ℝ (p + 1) f z‖ ≤
      Lf * ‖y - z‖)
    (hlipc : ∀ i y z, ‖iteratedFDeriv ℝ (p + 1) (fun w => c w i) y -
      iteratedFDeriv ℝ (p + 1) (fun w => c w i) z‖ ≤ Lc * ‖y - z‖)
    (hh : LipschitzWith K h) {i : ℕ} (hi : i ≤ N) :
    σ i ≤ max (σ 0) (γ₃ * (Lf + Real.sqrt m * (K : ℝ) * Lc) / (1 - η₂)) := by
  simpa only [mul_div_assoc] using ht.updates.le_max_initial_threshold
    (fun j hj hlarge => ht.very_successful hf hLf hLc hc hlipf hlipc hh hj hlarge) hi

end ModelTrace
end Composite
