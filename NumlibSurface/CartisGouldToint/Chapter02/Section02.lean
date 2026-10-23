import Numlib.Optimization.LineSearch.LipschitzGradient
import Numlib.Optimization.LineSearch.ExactGradient
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Cartis–Gould–Toint, Section 2.2: linesearch steps

The explicit sufficient-decrease interval in Lemma 2.2.1 is obtained from the
sharp quadratic remainder for a Lipschitz gradient. Gradients are identified
with the Fréchet derivative through the Euclidean inner product.
-/

namespace CartisGouldToint

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

end CartisGouldToint
