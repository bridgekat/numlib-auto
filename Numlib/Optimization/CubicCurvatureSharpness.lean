import Numlib.Analysis.Calculus.FiniteHermiteInterpolation
import Numlib.Optimization.CubicSharpTrace
import Numlib.Optimization.CubicModelMinimizer
import Numlib.Optimization.CubicSecondOrder
import Numlib.Optimization.FiniteChain
import Numlib.Analysis.Calculus.EuclideanOneHigherDeriv

/-!
# Sharp cubic regularization traces driven by negative curvature

Uniform Hermite interpolation realizes a bounded family whose gradients vanish along an
arbitrarily long trace, while negative Hessian curvature forces cubic regularization steps.
The steps globally minimize the actual cubic Taylor model.
-/
noncomputable section
open scoped NNReal InnerProductSpace Nat
namespace Optimization.CubicCurvatureSharpness
open Polynomial CubicRegularization RegularizedTaylorModel

/-- The value, zero gradient, and negative curvature data for a finite chain. -/
def curvatureJet (N : ℕ) (ε : ℝ) (k j : ℕ) : ℝ :=
  if j = 0 then -(k : ℝ) * ε ^ 3 else
  if j = 2 then if k < N then -2 * ε else 0 else 0

/-- At every active knot the quadratic Taylor polynomial is explicit. -/
theorem endpointTaylor_curvatureJet {N k : ℕ} {ε : ℝ} (hk : k < N) :
    Hermite.endpointTaylor 2 (curvatureJet N ε k) =
      C (-(k : ℝ) * ε ^ 3) + C (-ε) * X ^ 2 := by
  norm_num [Hermite.endpointTaylor, Hermite.jetPoly, Finset.sum_range_succ,
    curvatureJet, hk]
  rw [show -(2 * ε) / 2 = -ε by ring, map_neg]
  ring

/-- The curvature chain satisfies uniform scaled Hermite discrepancies. -/
theorem curvatureJet_compatible {N : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∀ k < N, ∀ j ≤ 2,
      |curvatureJet N ε (k + 1) j -
        (derivative^[j] (Hermite.endpointTaylor 2 (curvatureJet N ε k))).eval ε| ≤
        8 * ε ^ (3 - j) := by
  intro k hk j hj
  rw [endpointTaylor_curvatureJet hk]
  interval_cases j
  · simp only [curvatureJet, ↓reduceIte, Function.iterate_zero, id_eq,
      eval_add, eval_C, eval_mul, eval_pow, eval_X, Nat.cast_add, Nat.cast_one]
    have he : -((k : ℝ) + 1) * ε ^ 3 - (-(k : ℝ) * ε ^ 3 + -ε * ε ^ 2) = 0 := by ring
    rw [he, abs_zero]
    positivity
  · norm_num [curvatureJet, derivative_add, derivative_mul, derivative_pow]
    rw [abs_of_pos hε]
    nlinarith [sq_nonneg ε]
  · norm_num [curvatureJet, Function.iterate_succ_apply, derivative_add,
      derivative_mul, derivative_pow]
    split_ifs <;> ring_nf <;> simp [abs_of_pos hε] <;> linarith

/-- Uniform bounded C² interpolants with stationary gradients and prescribed negative Hessian
curvature at all nonterminal knots. -/
theorem exists_scalar_chain :
    ∃ L B : ℝ≥0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (ψ : ℝ → ℝ) (N : ℕ), ContDiff ℝ 2 ψ ∧
        LipschitzWith L (iteratedDeriv 2 ψ) ∧
        (∀ k ≤ N, ∀ j ≤ 2, iteratedDeriv j ψ ((k : ℝ) * ε) = curvatureJet N ε k j) ∧
        (∀ j ≤ 2, ∀ t, |iteratedDeriv j ψ t| ≤ B) ∧ 1 / ε ^ 3 ≤ (N : ℝ) := by
  obtain ⟨L, B, hinterp⟩ :=
    Hermite.exists_contDiff_lipschitz_iteratedDeriv_of_finite_jets 2 8 (by norm_num)
  refine ⟨L, B, ?_⟩
  intro ε hε hεone
  let N : ℕ := ⌈1 / ε ^ 3⌉₊
  have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have hlower : 1 / ε ^ 3 ≤ (N : ℝ) := Nat.le_ceil _
  have hupper : (N : ℝ) < 1 / ε ^ 3 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hdrop : (N : ℝ) * ε ^ 3 ≤ 2 := by
    have hh := (mul_lt_mul_of_pos_right hupper (pow_pos hε 3)).le
    have he : (1 / ε ^ 3 + 1) * ε ^ 3 = 1 + ε ^ 3 := by field_simp
    rw [he] at hh
    have hepspow : ε ^ 3 ≤ 1 := pow_le_one₀ hε.le hεone
    linarith
  have hdiff (k : ℕ) : ((k + 1 : ℕ) : ℝ) * ε - (k : ℝ) * ε = ε := by push_cast; ring
  obtain ⟨ψ, hψ, hLip, hjet, hb⟩ := hinterp N hN (fun k => (k : ℝ) * ε)
    (curvatureJet N ε) (fun k _ => by push_cast; nlinarith)
    (fun k hk j hj => by rw [hdiff]; exact curvatureJet_compatible hε k hk j hj)
  refine ⟨ψ, N, hψ, hLip, hjet, ?_, hlower⟩
  have hbound := hb (fun k hk j hj => ?_) (fun k _ => by rw [hdiff]; linarith)
  · exact hbound
  · by_cases hj0 : j = 0
    · subst j
      simp only [curvatureJet, ↓reduceIte]
      rw [show -(k : ℝ) * ε ^ 3 = -((k : ℝ) * ε ^ 3) by ring,
        abs_neg, abs_of_nonneg (by positivity)]
      have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk.le
      have hh := mul_le_mul_of_nonneg_right hkN (pow_nonneg hε.le 3)
      linarith
    · by_cases hj2 : j = 2
      · subst j
        simp [curvatureJet, hk, abs_mul, abs_of_nonneg hε.le]
        linarith
      · simp [curvatureJet, hj0, hj2]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Zero gradient and a scalar Hessian determine the entire cubic Taylor model. -/
theorem cubicModel_of_scalar_hessian {f : E → ℝ} {x : E} {a σ : ℝ}
    (hg : fderiv ℝ f x = 0)
    (hH : ∀ u, fderiv ℝ (fderiv ℝ f) x u u = a * ‖u‖ ^ 2) (s : E) :
    cubicModel f x σ s = f x + a / 2 * ‖s‖ ^ 2 + σ / 6 * ‖s‖ ^ 3 := by
  simpa [hg] using CubicRegularization.cubicModel_of_scalar_hessian hH s

/-- At negative scalar curvature, a step of norm ε globally minimizes the cubic model
with regularization parameter four. -/
theorem isMinOn_cubicModel_of_negative_curvature {f : E → ℝ} {x s : E} {ε : ℝ}
    (hε : 0 ≤ ε) (hg : fderiv ℝ f x = 0)
    (hH : ∀ u, fderiv ℝ (fderiv ℝ f) x u u = (-2 * ε) * ‖u‖ ^ 2)
    (hs : ‖s‖ = ε) : IsMinOn (cubicModel f x 4) Set.univ s := by
  intro y _
  change cubicModel f x 4 s ≤ cubicModel f x 4 y
  simp only [cubicModel_of_scalar_hessian hg hH, hs]
  have hprod := mul_nonneg (sq_nonneg (‖y‖ - ε))
    (show 0 ≤ 2 * ‖y‖ + ε by positivity)
  nlinarith

/-- Zero gradient and Hessian make the zero step a global cubic-model minimizer. -/
theorem isMinOn_cubicModel_of_zero_hessian {f : E → ℝ} {x : E}
    (hg : fderiv ℝ f x = 0) (hH : ∀ u, fderiv ℝ (fderiv ℝ f) x u u = 0) :
    IsMinOn (cubicModel f x 4) Set.univ 0 := by
  intro y _
  change cubicModel f x 4 0 ≤ cubicModel f x 4 y
  rw [cubicModel_zero, cubicModel_of_scalar_hessian hg (a := 0) (by simpa using hH)]
  simp only [zero_div, zero_mul, add_zero]
  exact le_add_of_nonneg_right (by positivity)

/-- Uniform sharp AR2 runs whose first-order derivatives vanish at every iterate and whose
negative curvature persists for at least ε⁻³ successful steps. The objective and Hessian
Lipschitz bounds are independent of ε. -/
theorem exists_hard_family :
    ∃ L B : ℝ≥0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ) (N : ℕ)
        (x s : ℕ → EuclideanSpace ℝ (Fin 1)),
        ContDiff ℝ 2 f ∧ LipschitzWith L (iteratedFDeriv ℝ 2 f) ∧
        (∀ y, |f y| ≤ B) ∧ f (x 0) = 0 ∧ x 0 = 0 ∧
        SecondOrderRun sharpParameters 1 1 f x s (fun _ => 4) ∧
        (∀ k, fderiv ℝ f (x k) = 0) ∧
        (∀ k < N, ∀ u, fderiv ℝ (fderiv ℝ f) (x k) u u = (-2 * ε) * ‖u‖ ^ 2) ∧
        (∀ u, fderiv ℝ (fderiv ℝ f) (x N) u u = 0) ∧
        ParameterUpdates.successCount
          (fun k => sharpParameters.eta1 ≤ ratio f (x k) (s k) 4) N = N ∧
        1 / ε ^ 3 ≤ (N : ℝ) := by
  obtain ⟨L, B, hfamily⟩ := exists_scalar_chain
  refine ⟨L, B, ?_⟩
  intro ε hε hεone
  obtain ⟨ψ, N, hψ, hLip, hjet, hbound, hNlower⟩ := hfamily ε hε hεone
  let f := EuclideanOne.lift ψ
  let v := EuclideanOne.coord.symm ε
  let x := FiniteChain.point N v
  let s := FiniteChain.step N v
  have hvnorm : ‖v‖ = ε := by
    change ‖EuclideanOne.coord.symm ε‖ = _
    rw [EuclideanOne.coord.symm.norm_map, Real.norm_eq_abs, abs_of_pos hε]
  have hv : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hvnorm]; exact hε.ne')
  have hd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hd' : Differentiable ℝ (deriv ψ) := by
    simpa only [iteratedDeriv_one] using hψ.differentiable_iteratedDeriv 1 (by norm_num)
  have hvalues (k : ℕ) (hk : k ≤ N) : f ((k : ℝ) • v) = -(k : ℝ) * ε ^ 3 := by
    simpa [f, v, EuclideanOne.lift, Function.comp_def, curvatureJet]
      using hjet k hk 0 (by norm_num)
  have hgrad (k : ℕ) (hk : k ≤ N) : fderiv ℝ f ((k : ℝ) • v) = 0 := by
    have hj : deriv ψ ((k : ℝ) * ε) = 0 := by
      simpa [curvatureJet] using hjet k hk 1 (by norm_num)
    rw [EuclideanOne.fderiv_eq hd]
    simp [v, hj]
  have hhess (k : ℕ) (hk : k ≤ N) (u : EuclideanSpace ℝ (Fin 1)) :
      fderiv ℝ (fderiv ℝ f) ((k : ℝ) • v) u u =
        (if k < N then -2 * ε else 0) * ‖u‖ ^ 2 := by
    have hj : deriv (deriv ψ) ((k : ℝ) * ε) = if k < N then -2 * ε else 0 := by
      simpa [iteratedDeriv_succ, iteratedDeriv_zero, curvatureJet]
        using hjet k hk 2 (by norm_num)
    have hh := EuclideanOne.fderiv_fderiv_apply hd
      (x := (k : ℝ) • v) (d₂ := if k < N then -2 * ε else 0)
      (by simpa [v, hj] using (hd' ((k : ℝ) * ε)).hasDerivAt) u u
    have hn : EuclideanOne.coord u ^ 2 = ‖u‖ ^ 2 := by
      rw [← EuclideanOne.coord.norm_map u, Real.norm_eq_abs, sq_abs]
    simpa [mul_assoc, ← pow_two, hn] using hh
  have hgall (k : ℕ) : fderiv ℝ f (x k) = 0 := by
    exact hgrad (min k N) (Nat.min_le_right k N)
  have hHactive (k : ℕ) (hk : k < N) (u) :
      fderiv ℝ (fderiv ℝ f) (x k) u u = (-2 * ε) * ‖u‖ ^ 2 := by
    simpa [x, FiniteChain.point_of_le v hk.le, hk] using hhess k hk.le u
  have hHterminal (k : ℕ) (hk : N ≤ k) (u) :
      fderiv ℝ (fderiv ℝ f) (x k) u u = 0 := by
    simpa [x, FiniteChain.point_of_ge v hk] using hhess N le_rfl u
  have hmin (k : ℕ) : IsMinOn (cubicModel f (x k) 4) Set.univ (s k) := by
    by_cases hk : k < N
    · exact isMinOn_cubicModel_of_negative_curvature hε.le (hgall k)
        (hHactive k hk) (by simpa [s, FiniteChain.step, hk] using hvnorm)
    · simpa [s, FiniteChain.step, hk] using
        isMinOn_cubicModel_of_zero_hessian (hgall k) (hHterminal k (Nat.le_of_not_gt hk))
  have hratio (k : ℕ) : ratio f (x k) (s k) 4 = 1 := by
    by_cases hk : k < N
    · have hsne : s k ≠ 0 := by simpa [s, FiniteChain.step, hk] using hv
      rw [ratio, ite_eq_right hsne]
      have hstep := FiniteChain.point_add_step N v k
      have hx : x k + s k = x (k + 1) := hstep.symm
      rw [hx]
      have hmodel := cubicModel_of_scalar_hessian (hgall k) (hHactive k hk) (σ := 4) (s k)
      rw [cubicModel_eq] at hmodel
      have hsnorm : ‖s k‖ = ε := by simpa [s, FiniteChain.step, hk] using hvnorm
      rw [hsnorm] at hmodel
      have hfk : f (x k) = -(k : ℝ) * ε ^ 3 := by
        simpa [x, FiniteChain.point_of_le v hk.le] using hvalues k hk.le
      have hfk1 : f (x (k + 1)) = -(k + 1 : ℕ) * ε ^ 3 := by
        simpa [x, FiniteChain.point_of_le v hk] using hvalues (k + 1) hk
      rw [taylorModel_zero, hfk, hfk1]
      have htaylor : taylorModel f 2 (x k) (s k) = -(k : ℝ) * ε ^ 3 - ε ^ 3 := by
        rw [hfk] at hmodel
        linarith
      rw [htaylor]
      have he : -(k : ℝ) * ε ^ 3 - (-(k + 1 : ℕ) * ε ^ 3) = ε ^ 3 := by push_cast; ring
      rw [he]
      have he' : -(k : ℝ) * ε ^ 3 - (-(k : ℝ) * ε ^ 3 - ε ^ 3) = ε ^ 3 := by ring
      rw [he', div_self (pow_ne_zero 3 hε.ne')]
    · simp [ratio, s, FiniteChain.step, hk]
  have hrun : SecondOrderRun sharpParameters 1 1 f x s (fun _ => 4) :=
    secondOrderRun_of_global_minimizers sharpParameters (by norm_num) (by norm_num)
      (by norm_num [sharpParameters]) (EuclideanOne.contDiff hψ) hmin
      (fun k => by rw [hratio]; norm_num [sharpParameters])
      (FiniteChain.point_add_step N v)
  have hcount : ParameterUpdates.successCount
      (fun k => sharpParameters.eta1 ≤ ratio f (x k) (s k) 4) N = N := by
    classical
    norm_num [ParameterUpdates.successCount, hratio, sharpParameters]
  refine ⟨f, N, x, s, EuclideanOne.contDiff hψ,
    EuclideanOne.iteratedFDeriv_lipschitz hψ hLip, ?_, ?_, ?_, hrun, hgall,
    hHactive, hHterminal N le_rfl, hcount, hNlower⟩
  · intro y
    simpa [f, EuclideanOne.lift] using hbound 0 (by omega) (EuclideanOne.coord y)
  · simpa [x, FiniteChain.point] using hvalues 0 (Nat.zero_le N)
  · simp [x]

end Optimization.CubicCurvatureSharpness
