import Numlib.Analysis.Calculus.QuinticHermite
import Numlib.Analysis.Calculus.FiniteHermiteInterpolation

/-!
# Canonical finite quintic interpolation

The cell on every interval is the explicit six-coefficient Hermite polynomial, rescaled
from the unit interval. Ordered finite joining retains its actual cell formulas and all
endpoint jets through order two. The exterior branches are the endpoint Taylor polynomials.
-/

noncomputable section
open Polynomial Set

namespace Hermite

/-- Rescale endpoint derivative data to the unit interval. -/
def scaledJet (s : ℝ) (a : ℕ → ℝ) (j : ℕ) : ℝ := s ^ j * a j

/-- The explicit quintic on an interval of length `s`, in the local coordinate. -/
def intervalQuinticPolynomial (s : ℝ) (a b : ℕ → ℝ) : ℝ[X] :=
  (quinticPolynomial (scaledJet s a) (scaledJet s b)).comp (C s⁻¹ * X)

/-- The actual translated and rescaled six-coefficient interpolation cell. -/
def quinticCell (x s : ℝ) (a b : ℕ → ℝ) : ℝ → ℝ :=
  shiftedPolynomial (intervalQuinticPolynomial s a b) x

/-- Every interpolation cell is smooth, including degenerate endpoint data. -/
theorem contDiff_quinticCell (x s : ℝ) (a b : ℕ → ℝ) (p : ℕ) :
    ContDiff ℝ p (quinticCell x s a b) :=
  contDiff_shiftedPolynomial _ _ p

/-- Actual derivatives of a rescaled cell are the derivatives of its unit polynomial. -/
theorem iteratedDeriv_quinticCell (x s : ℝ) (a b : ℕ → ℝ) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (quinticCell x s a b) t =
      (s⁻¹) ^ j * (derivative^[j] (quinticPolynomial (scaledJet s a) (scaledJet s b))).eval
        ((t - x) / s) := by
  rw [quinticCell, iteratedDeriv_shiftedPolynomial]
  simp only [intervalQuinticPolynomial, iterate_derivative_comp_C_mul_X,
    eval_mul, eval_C, eval_comp, eval_X]
  rw [div_eq_mul_inv, mul_comm (t - x) s⁻¹]

/-- All six endpoint derivatives of the actual rescaled polynomial have the prescribed values. -/
theorem quinticCell_endpoint_jets (x : ℝ) {s : ℝ} (hs : s ≠ 0)
    (a b : ℕ → ℝ) {j : ℕ} (hj : j ≤ 2) :
    iteratedDeriv j (quinticCell x s a b) x = a j ∧
      iteratedDeriv j (quinticCell x s a b) (x + s) = b j := by
  have h := iteratedDeriv_quinticPolynomial_endpoints (scaledJet s a) (scaledJet s b) hj
  simp only [Polynomial.iteratedDeriv_eval] at h
  simp only [iteratedDeriv_quinticCell, sub_self, zero_div, add_sub_cancel_left,
    div_self hs, h.1, h.2, scaledJet]
  constructor <;> simp [hs]

/-- Evaluate an actual interpolation cell using the explicit unit quintic. -/
theorem quinticCell_eq (x s : ℝ) (a b : ℕ → ℝ) (t : ℝ) :
    quinticCell x s a b t =
      (quinticPolynomial (scaledJet s a) (scaledJet s b)).eval ((t - x) / s) := by
  simp only [quinticCell, shiftedPolynomial, intervalQuinticPolynomial, eval_comp,
    eval_mul, eval_C, eval_X]
  rw [div_eq_mul_inv, mul_comm (t - x) s⁻¹]

/-- The pieces of the canonical finite interpolant, including both Taylor exterior branches. -/
def quinticPieces (N : ℕ) (x : ℕ → ℝ) (a : ℕ → ℕ → ℝ) (i : ℕ) : ℝ → ℝ :=
  if i = 0 then shiftedPolynomial (endpointTaylor 2 (a 0)) (x 0)
  else if i ≤ N then quinticCell (x (i - 1)) (x i - x (i - 1)) (a (i - 1)) (a i)
  else shiftedPolynomial (endpointTaylor 2 (a N)) (x N)

/-- Join the actual explicit quintic cells, with endpoint Taylor tails. -/
def finiteQuintic (N : ℕ) (x : ℕ → ℝ) (a : ℕ → ℕ → ℝ) : ℝ → ℝ :=
  joinFin x (quinticPieces N x a) (N + 1)

/-- The first branch is the Taylor polynomial at the initial node. -/
@[simp] theorem quinticPieces_zero (N : ℕ) (x : ℕ → ℝ) (a : ℕ → ℕ → ℝ) :
    quinticPieces N x a 0 = shiftedPolynomial (endpointTaylor 2 (a 0)) (x 0) := by
  simp [quinticPieces]

/-- Every interior branch is its explicit adjacent-node interpolation cell. -/
theorem quinticPieces_succ (N : ℕ) (x : ℕ → ℝ) (a : ℕ → ℕ → ℝ)
    {i : ℕ} (hi : i < N) :
    quinticPieces N x a (i + 1) = quinticCell (x i) (x (i + 1) - x i) (a i) (a (i + 1)) := by
  simp [quinticPieces, Nat.succ_le_iff.mpr hi]

/-- The final branch is the Taylor polynomial at the terminal node. -/
@[simp] theorem quinticPieces_last (N : ℕ) (x : ℕ → ℝ) (a : ℕ → ℕ → ℝ) :
    quinticPieces N x a (N + 1) = shiftedPolynomial (endpointTaylor 2 (a N)) (x N) := by
  simp [quinticPieces]

/-- Every piece of the actual construction is smooth. -/
theorem contDiff_quinticPieces (N : ℕ) (x : ℕ → ℝ) (a : ℕ → ℕ → ℝ) (i p : ℕ) :
    ContDiff ℝ p (quinticPieces N x a i) := by
  unfold quinticPieces
  split_ifs
  · exact contDiff_shiftedPolynomial _ _ p
  · exact contDiff_quinticCell _ _ _ _ p
  · exact contDiff_shiftedPolynomial _ _ p

/-- The preceding piece has the prescribed jet at every node. -/
theorem quinticPieces_left_jets {N : ℕ} {x : ℕ → ℝ} (a : ℕ → ℕ → ℝ)
    (hx : ∀ i < N, x i < x (i + 1)) {i j : ℕ} (hi : i ≤ N) (hj : j ≤ 2) :
    iteratedDeriv j (quinticPieces N x a i) (x i) = a i j := by
  by_cases hi0 : i = 0
  · subst i
    simp only [quinticPieces_zero, iteratedDeriv_shiftedPolynomial, sub_self]
    exact eval_iterate_derivative_endpointTaylor 2 j (a 0) hj
  · have him : i - 1 < N := by omega
    have hieq : i - 1 + 1 = i := Nat.sub_add_cancel (by omega)
    rw [← hieq, quinticPieces_succ N x a him]
    have h := (quinticCell_endpoint_jets (x (i - 1))
      (sub_ne_zero.mpr (ne_of_gt (hx (i - 1) him))) (a (i - 1)) (a (i - 1 + 1)) hj).2
    simpa only [add_sub_cancel] using h

/-- The following piece has the same prescribed jet at every node. -/
theorem quinticPieces_right_jets {N : ℕ} {x : ℕ → ℝ} (a : ℕ → ℕ → ℝ)
    (hx : ∀ i < N, x i < x (i + 1)) {i j : ℕ} (hi : i ≤ N) (hj : j ≤ 2) :
    iteratedDeriv j (quinticPieces N x a (i + 1)) (x i) = a i j := by
  rcases hi.eq_or_lt with rfl | hi
  · simp only [quinticPieces_last, iteratedDeriv_shiftedPolynomial, sub_self]
    exact eval_iterate_derivative_endpointTaylor 2 j (a i) hj
  · rw [quinticPieces_succ N x a hi]
    exact (quinticCell_endpoint_jets (x i) (sub_ne_zero.mpr (ne_of_gt (hx i hi)))
      (a i) (a (i + 1)) hj).1

/-- The finite explicit construction is globally twice continuously differentiable;
its genuine iterated derivatives are joined from the corresponding piece derivatives. -/
theorem contDiff_finiteQuintic {N : ℕ} {x : ℕ → ℝ} (a : ℕ → ℕ → ℝ)
    (hx : ∀ i < N, x i < x (i + 1)) :
    ContDiff ℝ 2 (finiteQuintic N x a) ∧ ∀ j ≤ 2,
      iteratedDeriv j (finiteQuintic N x a) =
        joinFin x (fun i => iteratedDeriv j (quinticPieces N x a i)) (N + 1) := by
  have hprefix := contDiff_joinFin_of_matching_jets hx
    (fun i _ => contDiff_quinticPieces N x a i 2)
    (fun i hi j hj => (quinticPieces_left_jets a hx hi.le hj).trans
      (quinticPieces_right_jets a hx hi.le hj).symm)
  have hseam : ∀ j ≤ 2, iteratedDeriv j (joinFin x (quinticPieces N x a) N) (x N) =
      iteratedDeriv j (quinticPieces N x a (N + 1)) (x N) := by
    intro j hj
    rw [hprefix.2 j hj, joinFin_eq_last x _ N hx le_rfl]
    exact (quinticPieces_left_jets a hx le_rfl hj).trans
      (quinticPieces_right_jets a hx le_rfl hj).symm
  have hfinal := contDiff_joinAt_of_matching_jets hprefix.1
    (contDiff_quinticPieces N x a (N + 1) 2) hseam
  refine ⟨hfinal.1, fun j hj => ?_⟩
  simpa only [finiteQuintic, joinFin, hprefix.2 j hj] using hfinal.2 j hj

/-- The actual finite interpolant realizes every prescribed nodal jet. -/
theorem finiteQuintic_node_jets {N : ℕ} {x : ℕ → ℝ} (a : ℕ → ℕ → ℝ)
    (hx : ∀ i < N, x i < x (i + 1)) {i j : ℕ} (hi : i ≤ N) (hj : j ≤ 2) :
    iteratedDeriv j (finiteQuintic N x a) (x i) = a i j := by
  rw [(contDiff_finiteQuintic a hx).2 j hj]
  rw [joinFin_succ_of_le x _ N (le_of_adjacent_le (fun k hk => (hx k hk).le) hi le_rfl),
    joinFin_at_knot hx hi]
  exact quinticPieces_left_jets a hx hi hj

/-- Finite ordered joining selects the prescribed cell on each closed interval when its
left endpoint values match. This includes both interval endpoints. -/
theorem joinFin_cell {E : Type*} {n i : ℕ} {x : ℕ → ℝ} {f : ℕ → ℝ → E}
    (hx : ∀ k < n, x k < x (k + 1)) (hi : i < n)
    (hm : f i (x i) = f (i + 1) (x i)) {t : ℝ} (ht : t ∈ Icc (x i) (x (i + 1))) :
    joinFin x f (n + 1) t = f (i + 1) t := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [joinFin_succ_of_le x f (n + 1) (ht.2.trans
      (le_of_adjacent_le (fun k hk => (hx k hk).le) (by omega) le_rfl))]
    by_cases hin : i < n
    · exact ih (fun k hk => hx k (by omega)) hin
    · have he : i = n := by omega
      subst i
      change joinAt (x n) (joinFin x f n) (f (n + 1)) t = _
      apply joinAt_of_ge _ ht.1
      rw [joinFin_eq_last x f n (fun k hk => hx k (by omega)) le_rfl]
      exact hm

/-- On each closed cell, every actual derivative through order two is the derivative of
its specific explicit quintic, rather than an unspecified interpolant. -/
theorem finiteQuintic_cell_jets {N : ℕ} {x : ℕ → ℝ} (a : ℕ → ℕ → ℝ)
    (hx : ∀ i < N, x i < x (i + 1)) {i j : ℕ} (hi : i < N) (hj : j ≤ 2)
    {t : ℝ} (ht : t ∈ Icc (x i) (x (i + 1))) :
    iteratedDeriv j (finiteQuintic N x a) t =
      iteratedDeriv j (quinticCell (x i) (x (i + 1) - x i) (a i) (a (i + 1))) t := by
  rw [(contDiff_finiteQuintic a hx).2 j hj]
  rw [joinFin_cell hx hi ((quinticPieces_left_jets a hx hi.le hj).trans
    (quinticPieces_right_jets a hx hi.le hj).symm) ht, quinticPieces_succ N x a hi]

/-- The initial Taylor branch is retained on the entire left half-line, with all its jets. -/
theorem finiteQuintic_left_jets {N : ℕ} {x : ℕ → ℝ} (a : ℕ → ℕ → ℝ)
    (hx : ∀ i < N, x i < x (i + 1)) {j : ℕ} (hj : j ≤ 2) {t : ℝ} (ht : t ≤ x 0) :
    iteratedDeriv j (finiteQuintic N x a) t =
      (derivative^[j] (endpointTaylor 2 (a 0))).eval (t - x 0) := by
  rw [(contDiff_finiteQuintic a hx).2 j hj,
    joinFin_eq_first (fun i hi => le_of_adjacent_le (fun k hk => (hx k hk).le)
      (Nat.zero_le i) (by omega)) ht, quinticPieces_zero,
    iteratedDeriv_shiftedPolynomial]

/-- The terminal Taylor branch is retained on the right half-line, with all its jets. -/
theorem finiteQuintic_right_jets {N : ℕ} {x : ℕ → ℝ} (a : ℕ → ℕ → ℝ)
    (hx : ∀ i < N, x i < x (i + 1)) {j : ℕ} (hj : j ≤ 2) {t : ℝ} (ht : x N ≤ t) :
    iteratedDeriv j (finiteQuintic N x a) t =
      (derivative^[j] (endpointTaylor 2 (a N))).eval (t - x N) := by
  rw [(contDiff_finiteQuintic a hx).2 j hj]
  change joinAt (x N) (joinFin x (fun i => iteratedDeriv j (quinticPieces N x a i)) N)
    (iteratedDeriv j (quinticPieces N x a (N + 1))) t = _
  rw [joinAt_of_ge (by
    rw [joinFin_eq_last x _ N hx le_rfl]
    exact (quinticPieces_left_jets a hx le_rfl hj).trans
      (quinticPieces_right_jets a hx le_rfl hj).symm) ht,
    quinticPieces_last, iteratedDeriv_shiftedPolynomial]

/-- Any point between the first and last nodes lies in an adjacent closed cell.
The assertion needs no spacing bound or monotonicity hypothesis. -/
theorem exists_adjacent_cell {N : ℕ} (hN : 0 < N) (x : ℕ → ℝ) {t : ℝ}
    (ht : t ∈ Icc (x 0) (x N)) : ∃ k < N, t ∈ Icc (x k) (x (k + 1)) := by
  induction N with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      exact ⟨0, by omega, ht⟩
    by_cases h : t ≤ x n
    · obtain ⟨k, hk, hkt⟩ := ih (by omega) ⟨ht.1, h⟩
      exact ⟨k, by omega, hkt⟩
    · exact ⟨n, by omega, le_of_not_ge h, ht.2⟩

end Hermite
