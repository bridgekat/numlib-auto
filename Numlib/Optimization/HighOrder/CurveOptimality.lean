import Numlib.Analysis.Calculus.TaylorModel.PolynomialCurve
import Numlib.Analysis.Calculus.IteratedDeriv.LocalMin

/-!
# Necessary optimality conditions from polynomial curves

At a local minimum, if all lower coefficients of the objective along a polynomial
curve vanish, the next coefficient is nonnegative. The coefficients are the
ordered-composition sums of actual Fréchet derivatives. No jet identity or
curve-wise optimality condition is assumed.
-/

namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A local minimum has nonnegative next curve coefficient whenever all lower positive-
degree curve coefficients vanish. -/
theorem curveCoefficient_nonneg_of_isLocalMin {q j : ℕ}
    (hj : 0 < j) (hjq : j ≤ q) {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ q f x) (hmin : IsLocalMin f x) (s : ℕ → E)
    (hzero : ∀ i, 0 < i → i < j → curveCoefficient f x s i = 0) :
    0 ≤ curveCoefficient f x s j := by
  let c : ℝ → E := fun t => x + polynomialCurve s q t
  have hc : ContDiff ℝ q c := contDiff_const.add (polynomialCurve_contDiff s q)
  have hc0 : c 0 = x := by simp [c, polynomialCurve_zero]
  have hg : ContDiffAt ℝ q (f ∘ c) 0 :=
    (show ContDiffAt ℝ q f (c 0) by simpa only [hc0] using hf).comp 0 hc.contDiffAt
  have hmin' : IsLocalMin (f ∘ c) 0 := by
    have hm : ∀ᶠ y in nhds x, f x ≤ f y := hmin
    have he := (hc.continuous.continuousAt (x := 0)).tendsto
    rw [hc0] at he
    change ∀ᶠ t in nhds (0 : ℝ), (f ∘ c) 0 ≤ (f ∘ c) t
    simpa only [Function.comp_apply, hc0] using he.eventually hm
  have hD := ScalarOptimality.iteratedDeriv_nonneg_of_isLocalMin hj
    (hg.of_le (by exact_mod_cast hjq)) hmin' (fun i hi hij => ?_)
  · change 0 ≤ iteratedDeriv j (fun t => f (x + polynomialCurve s q t)) 0 at hD
    rw [iteratedDeriv_polynomialCurve hjq hf] at hD
    have hfact : (0 : ℝ) < j.factorial := by positivity
    nlinarith
  · change iteratedDeriv i (fun t => f (x + polynomialCurve s q t)) 0 = 0
    rw [iteratedDeriv_polynomialCurve (hij.le.trans hjq) hf, hzero i hi hij, mul_zero]
end TaylorModel
