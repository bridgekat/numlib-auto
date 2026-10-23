import Numlib.Optimization.LineSearch.LipschitzGradient
import Numlib.Optimization.LineSearch.ExactGradient
import Numlib.Optimization.LineSearch.ExactQuadraticSharpness
import Numlib.Optimization.LineSearch.Backtracking
import Numlib.Optimization.LineSearch.Sharpness
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Cartis–Gould–Toint, Section 2.2: linesearch steps

The explicit sufficient-decrease interval in Lemma 2.2.1 is obtained from the
sharp quadratic remainder for a Lipschitz gradient. Gradients are identified
with the Fréchet derivative through the Euclidean inner product.

Theorem 2.2.5 uses a positive diagonal quadratic with genuine global line
minimizers. This proves the original lower bound independently of the printed
Appendix B.2 corridor, whose first-local-minimum argument does not establish the
global exact-line-search condition (2.2.26).
-/

namespace CartisGouldToint

/-- A finite nonterminated prefix of Algorithm 2.2.1. The natural number `j i`
is exactly the first halving index passing the actual Armijo test at iteration `i`. -/
def sdbaRun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (j : ℕ → ℕ)
    (α tini ε : ℝ) (N : ℕ) : Prop :=
  BacktrackingGradient.Run f g x j α tini ε N

/-- A finite prefix of exact steepest descent before termination. Its steps
globally minimize the actual objective along each nonnegative negative-gradient
ray, as in (2.2.26). -/
def sdexRun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ) (ε : ℝ) (N : ℕ) : Prop :=
  ExactGradientLineSearch.Run f g x t ε N

/-- **Lemma 2.2.1.** Under the Lipschitz-gradient assumption, every step length
`0 ≤ t ≤ 2(1 - α)/L` satisfies the Armijo decrease inequality (2.2.3). -/
theorem lemma_2_2_1 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {L α t : ℝ}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hL : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hL1 : 1 ≤ L) (hα0 : 0 < α) (hα1 : α < 1)
    (ht : t ∈ Set.Icc 0 (2 * (1 - α) / L)) (x : EuclideanSpace ℝ (Fin n)) :
    f (x - t • g x) ≤ f x - α * t * ‖g x‖ ^ 2 := by
  have h := LineSearch.armijo_neg_gradient_of_lipschitz hf hL ht.1
    (by have hpos : 0 < L := by linarith
        have hh := (le_div_iff₀ hpos).mp ht.2
        nlinarith) x
  simpa [LineSearch.Armijo, smul_neg, sub_eq_add_neg, innerSL_apply_apply,
    real_inner_self_eq_norm_sq] using h

/-- **Theorem 2.2.4.** Exact steepest descent reaches the gradient tolerance in
at most `2L (f(x₀) - f_low)/ε²` iterations. The exact line minimizations may require
an unbounded amount of work; this statement counts only outer iterations. -/
theorem theorem_2_2_4 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {t : ℕ → ℝ} {ε L flow : ℝ}
    (hprefix : ∀ N, (∀ i < N, ε < ‖g (x i)‖) → sdexRun f g x t ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hL1 : 1 ≤ L)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ κ > 0, κ = 2 * L ∧ ∃ K, ‖g (x K)‖ ≤ ε ∧ sdexRun f g x t ε K ∧
      (K : ℝ) ≤ κ * (f (x 0) - flow) / ε ^ 2 := by
  have hLpos : 0 < L := by linarith
  obtain ⟨K, hstop, hK, hbound⟩ :=
    ExactGradientLineSearch.exists_termination hprefix hL hLpos hlow
  exact ⟨2 * L, by positivity, rfl, K, hstop, hK, hbound⟩

/-- **Theorem 2.2.2.** Backtracking steepest descent reaches the gradient tolerance
with objective and gradient evaluation bounds of order `ε⁻²`. The constants
are given by an accuracy-independent sufficient halving index and the step bound
`min(tini, (1-α)/L)`. The additive ones count the initial evaluations; these repairs
are necessary when the initial step is already small or the initial point satisfies
the stopping test. -/
theorem theorem_2_2_2 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {j : ℕ → ℕ} {α tini ε L flow : ℝ}
    (hprefix : ∀ N, (∀ i < N, ε < ‖g (x i)‖) → sdbaRun f g x j α tini ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hL1 : 1 ≤ L)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ M : ℕ, BacktrackingGradient.step tini M ≤ BacktrackingGradient.threshold L α ∧
      ∃ κI > 0, ∃ κF > 0,
        κI = (α * min tini ((1 - α) / L))⁻¹ ∧ κF = (M + 1 : ℕ) * κI ∧
        ∃ K, ‖g (x K)‖ ≤ ε ∧ sdbaRun f g x j α tini ε K ∧
          (K : ℝ) ≤ κI * (f (x 0) - flow) / ε ^ 2 ∧
          ((BacktrackingGradient.Run.functionEvaluations j K : ℕ) : ℝ) ≤
            κF * (f (x 0) - flow) / ε ^ 2 + 1 ∧
          ((K + 1 : ℕ) : ℝ) ≤ κI * (f (x 0) - flow) / ε ^ 2 + 1 := by
  have h0 := hprefix 0 (by simp)
  have hLpos : 0 < L := by linarith
  have hmin : 0 < min tini ((1 - α) / L) := lt_min h0.initial_pos
    (div_pos (by linarith [h0.alpha_lt_one]) hLpos)
  obtain ⟨M, hM⟩ := BacktrackingGradient.exists_step_le tini
    (show 0 < BacktrackingGradient.threshold L α from by
      exact div_pos (mul_pos (by norm_num) (sub_pos.mpr h0.alpha_lt_one)) hLpos)
  let κI := (α * min tini ((1 - α) / L))⁻¹
  have hI : 0 < κI := inv_pos.mpr (mul_pos h0.alpha_pos hmin)
  obtain ⟨K, hstop, hK, hbound⟩ :=
    BacktrackingGradient.exists_termination hprefix hL hLpos hlow
  have hiter : (K : ℝ) ≤ κI * (f (x 0) - flow) / ε ^ 2 := by
    convert hbound using 1
    dsimp [κI]
    field_simp
  refine ⟨M, hM, κI, hI, (M + 1 : ℕ) * κI, by positivity,
    rfl, rfl, K, hstop, hK, hiter, ?_, ?_⟩
  · have hc : (BacktrackingGradient.Run.functionEvaluations j K : ℝ) ≤
        1 + (M + 1 : ℕ) * (K : ℝ) := by
      exact_mod_cast hK.functionEvaluations_le hL hLpos hM
    have hm : (0 : ℝ) ≤ (M + 1 : ℕ) := by positivity
    have hp := mul_le_mul_of_nonneg_left hiter hm
    calc
      (BacktrackingGradient.Run.functionEvaluations j K : ℝ) ≤ 1 + (M + 1 : ℕ) * (K : ℝ) := hc
      _ ≤ 1 + (M + 1 : ℕ) * (κI * (f (x 0) - flow) / ε ^ 2) := add_le_add le_rfl hp
      _ = _ := by ring
  · push_cast
    linarith

/-- **Theorem 2.2.3 (slow steepest descent).** For every Armijo parameter and
positive initial step, a one-dimensional bounded-below `C¹` objective can require
at least `ε⁻²` function and gradient evaluations. The gradient Lipschitz constant
and initial objective gap are uniform over `0 < ε < 1`.

The explicit witness is a linear descent plateau with a quadratic terminal ramp.
It yields an actual SDBA run with zero halvings at every iteration. The iteration
count is rounded upward to `ceil(ε⁻²)`, since counts must be integers. Evaluation
counts include the initial values and the terminal gradient stopping test. -/
theorem theorem_2_2_3 {α tini : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (htini : 0 < tini) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ (f g : ℝ → ℝ) (x : ℕ → ℝ) (N : ℕ),
        ContDiff ℝ 1 f ∧ (∀ y, HasFDerivAt f (innerSL ℝ (g y)) y) ∧
        (∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) ∧
        (∀ y, 0 ≤ f y) ∧ f (x 0) ≤ 8 * tini ∧ x 0 = 0 ∧
        N = ⌈1 / ε ^ 2⌉₊ ∧ BacktrackingGradient.Run f g x (fun _ => 0) α tini ε N ∧
        ‖g (x N)‖ = ε ∧ (1 / ε ^ 2 : ℝ) ≤ N ∧
        BacktrackingGradient.Run.functionEvaluations (fun _ => 0) N = N + 1 ∧
        (1 / ε ^ 2 : ℝ) ≤ BacktrackingGradient.Run.functionEvaluations (fun _ => 0) N ∧
        (1 / ε ^ 2 : ℝ) ≤ BacktrackingGradient.Run.gradientEvaluations N :=
  BacktrackingGradient.exists_slow_run hα0 hα1 htini

/-- **Theorem 2.2.5.** Genuine global exact steepest descent may require at least
ε⁻² outer iterations. The infinitely smooth nonnegative quadratic witnesses
have gradient Lipschitz constants and initial objective gaps bounded uniformly
before the requested accuracy is chosen. The returned index is the actual first
stopping index of the primitive SDEX execution.

The explicit family has eigenvalues ε²/16 and 1, the exact global line step
2/(1+ε²/16), gradient Lipschitz constant 1 and initial gap at most 17/2. Its
selected line minimizers are unique. This proof does not rely on the incorrect
global-line-minimum assertion for the printed Appendix B.2 corridor. -/
theorem theorem_2_2_5 : ∃ L > 0, ∃ B > 0,
    ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∃ (f : EuclideanSpace ℝ (Fin 2) → ℝ)
      (x : ℕ → EuclideanSpace ℝ (Fin 2)) (t : ℕ → ℝ) (K : ℕ),
      ContDiff ℝ (⊤ : ℕ∞) f ∧ (∀ z, 0 ≤ f z) ∧ f (x 0) ≤ B ∧
      (∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y-z‖) ∧
      sdexRun f (gradient f) x t ε K ∧ ‖gradient f (x K)‖ ≤ ε ∧
      ⌊ε^(-(2 : ℝ))⌋₊ ≤ K ∧ ε^(-(2 : ℝ)) ≤ (K : ℝ) :=
  ExactGradientLineSearch.QuadraticSharpness.exists_uniform_global_witness

end CartisGouldToint
