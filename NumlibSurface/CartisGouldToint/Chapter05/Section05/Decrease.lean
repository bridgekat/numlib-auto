import NumlibSurface.CartisGouldToint.Chapter05.Section05.Bounds
import Numlib.Optimization.UniversalRegularizationDecrease

/-!
# Chapter 5, Section 5: decrease on successful universal-regularization iterations

The constants are exactly the one-order and two-order constants of Lemma 5.5.6.
A common tolerance radius proves the mixed-power minimum without a positive parameter floor.
-/

noncomputable section
namespace CartisGouldToint.Chapter05.Section05
open Optimization.UniversalRegularization

/-- The constants `sigma_H,1` and `sigma_H` in Lemma 5.5.6, selected by the active order.
Their definitions read no accuracy tolerances. -/
abbrev universalDecreaseSigma {q p : ℕ} {r : ℝ} (a : universalParameters q p r)
    (H t initial : ℝ) : ℝ := decreaseSigma a H t initial

/-- The constants `kappa_H,1` and `kappa_H,2` of Lemma 5.5.6. The order-`j` factor is
`(alpha_j^r / sigma_H^j)^(1/(r-j))`, multiplied by `eta_1/r!`; two active orders use
their minimum. -/
abbrev universalDecreaseConstant {q p : ℕ} {r : ℝ} (a : universalParameters q p r)
    (H t initial : ℝ) : ℝ := decreaseConstant a H t initial

/-- The source decrease constants are positive. -/
theorem universalDecreaseConstant_pos {q p : ℕ} {r H t initial : ℝ}
    {a : universalParameters q p r} (hi : 0 < initial) :
    0 < universalDecreaseConstant a H t initial := decreaseConstant_pos hi

/-- Fixed nonaccuracy parameters give one decrease constant simultaneously for every
accuracy choice. In particular, epsilon cannot be hidden in the constant's parameter argument. -/
theorem universalDecreaseConstant_eq_of_parameters {q p : ℕ} {r H t initial : ℝ}
    {a b : universalParameters q p r}
    (heta1 : a.eta1 = b.eta1) (heta2 : a.eta2 = b.eta2)
    (hgamma3 : a.gamma3 = b.gamma3) (htheta : a.theta = b.theta)
    (halpha : a.alpha = b.alpha) :
    universalDecreaseConstant a H t initial = universalDecreaseConstant b H t initial :=
  decreaseConstant_eq_of_parameters heta1 heta2 hgamma3 htheta halpha

/-- Lemma 5.5.6, both parts: every successful nonterminal actual iteration pays the first
complexity power, or the minimum of the first and second complexity powers when both are
active. The exact printed constants apply also when `r = p + beta` or `H = 0`. -/
theorem lemma_5_5_6 {n q p N k : ℕ} [NeZero n] {r H beta : ℝ}
    {a : universalParameters q p r} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {sigma : ℕ → ℝ}
    (h : universalPrefix a f x s sigma N) (hf : holderDerivativeAssumption f p H beta)
    (hexp : (q : ℝ) < (p : ℝ) + beta) (htr : (p : ℝ) + beta ≤ r) (hk : k < N)
    (ha : Accepted a f (x k) (sigma k) (s k)) :
    universalDecreaseConstant a H ((p : ℝ) + beta) (sigma 0) *
      (if 2 ≤ q then min (a.epsilon 0 ^ (((p : ℝ) + beta) / ((p : ℝ) + beta - 1)))
        (a.epsilon 1 ^ (((p : ℝ) + beta) / ((p : ℝ) + beta - 2)))
      else a.epsilon 0 ^ (((p : ℝ) + beta) / ((p : ℝ) + beta - 1))) ≤
        f (x k) - f (x (k + 1)) := by
  have ht : 0 ≤ (p : ℝ) + beta := by
    have hp : (0 : ℝ) < q := by exact_mod_cast a.order_pos
    linarith
  rw [← toleranceRadius_power ht]
  exact h.successful_decrease hf.toHolderDerivative hexp htr hk ha

end CartisGouldToint.Chapter05.Section05
