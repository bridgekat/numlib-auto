import Numlib.Optimization.SteepestDescent.Exact.CorridorPolynomials

/-!
# Genuine global source corridor curves

The three explicit finite polynomial chains realize the prescribed width,
center and scalar objective jets. Every actual interval and both exterior
Taylor continuations are identified. The first two terminal jets are flat,
so the width and center have constant tails rather than an indefinite linear
continuation of the finite excess sequence.
-/

open Polynomial Set
noncomputable section
namespace ExactSteepestDescent.Corridor

/-- The indexed source polynomial interval family: width, center and scalar value. -/
def curvePolynomial (P : Parameters) (i : Fin 3) (k : ℕ) : ℝ[X] :=
  ![widthPolynomial P k, centerPolynomial P k, scalarPolynomial P k] i

/-- The indexed source endpoint jets corresponding to the three polynomial families. -/
def curveJet (P : Parameters) (i : Fin 3) (k j : ℕ) : ℝ :=
  ![widthJet P k j, centerJet P k j, scalarJet P k j] i

/-- Initial Taylor seeds give a constant width and center, and a linear scalar tail. -/
def curveSeed (P : Parameters) (i : Fin 3) : ℝ → ℝ :=
  Hermite.taylorTail 2 (curveJet P i 0) 0

/-- The actual global finite source curve with its endpoint Taylor continuations. -/
def curve (P : Parameters) (i : Fin 3) : ℝ → ℝ :=
  Hermite.polynomialPrefix 2 (horizontal P) (curvePolynomial P i) (curveSeed P i) P.horizon

/-- The horizontal source grid starts at zero. -/
theorem horizontal_zero (P : Parameters) : horizontal P 0 = 0 := by simp [horizontal]

/-- All actual interval polynomials match their designated left jets. -/
theorem curvePolynomial_left (P : Parameters) (i : Fin 3) (k j : ℕ) (hj : j ≤ 2) :
    iteratedDeriv j (curvePolynomial P i k).eval 0 = curveJet P i k j := by
  fin_cases i
  · exact widthPolynomial_left P k j hj
  · exact centerPolynomial_left P k j hj
  · exact scalarPolynomial_left P k j hj

/-- All actual interval polynomials match the next designated jets at the true grid step. -/
theorem curvePolynomial_right (P : Parameters) (i : Fin 3) {k : ℕ}
    (hk : k < P.horizon) (j : ℕ) (hj : j ≤ 2) :
    iteratedDeriv j (curvePolynomial P i k).eval
      (horizontal P (k + 1) - horizontal P k) = curveJet P i (k + 1) j := by
  rw [horizontal_succ, add_sub_cancel_left]
  fin_cases i
  · exact widthPolynomial_right P hk j hj
  · exact centerPolynomial_right P hk j hj
  · exact scalarPolynomial_right P hk j hj

/-- The genuine source seeds recover every initial jet. -/
theorem curveSeed_jets (P : Parameters) (i : Fin 3) (j : ℕ) (hj : j ≤ 2) :
    iteratedDeriv j (curveSeed P i) (horizontal P 0) = curveJet P i 0 j := by
  rw [horizontal_zero]
  exact Hermite.taylorTail_jet 2 _ 0 hj

/-- Actual global twice differentiable source curves realize every node and
retain the exact source polynomial, including derivatives at every join. -/
theorem curve_spec (P : Parameters) (i : Fin 3) : ContDiff ℝ 2 (curve P i) ∧
    (∀ k ≤ P.horizon, ∀ j ≤ 2, iteratedDeriv j (curve P i) (horizontal P k) =
      curveJet P i k j) ∧
    ∀ k < P.horizon, ∀ j ≤ 2, ∀ t ∈ Icc (horizontal P k) (horizontal P (k + 1)),
      iteratedDeriv j (curve P i) t =
        iteratedDeriv j (curvePolynomial P i k).eval (t - horizontal P k) := by
  exact Hermite.polynomialPrefix_spec (horizontal_increasing P)
    (fun k _ j hj => curvePolynomial_left P i k j hj)
    (fun k hk j hj => curvePolynomial_right P i hk j hj)
    (Hermite.taylorTail_contDiff 2 _ 0) (curveSeed_jets P i)

/-- The entire left continuation is the actual initial Taylor seed. -/
theorem curve_left (P : Parameters) (i : Fin 3) {j : ℕ} (hj : j ≤ 2)
    {t : ℝ} (ht : t ≤ 0) :
    iteratedDeriv j (curve P i) t = iteratedDeriv j (curveSeed P i) t := by
  exact Hermite.polynomialPrefix_left (horizontal_increasing P)
    (fun k _ j hj => curvePolynomial_left P i k j hj)
    (fun k hk j hj => curvePolynomial_right P i hk j hj)
    (Hermite.taylorTail_contDiff 2 _ 0) (curveSeed_jets P i) hj
    (by rwa [horizontal_zero])

/-- The entire right continuation is the actual final Taylor polynomial. -/
theorem curve_right (P : Parameters) (i : Fin 3) {j : ℕ} (hj : j ≤ 2)
    {t : ℝ} (ht : horizontal P P.horizon ≤ t) :
    iteratedDeriv j (curve P i) t =
      iteratedDeriv j (Hermite.taylorTail 2 (curveJet P i P.horizon)
        (horizontal P P.horizon)) t := by
  exact Hermite.polynomialPrefix_tail P.horizon_pos (horizontal_increasing P)
    (fun k _ j hj => curvePolynomial_left P i k j hj)
    (fun k hk j hj => curvePolynomial_right P i hk j hj)
    (Hermite.taylorTail_contDiff 2 _ 0) (curveSeed_jets P i) hj ht

/-- Width and center positive-order jets are genuinely flat at every node. -/
theorem curveJet_flat (P : Parameters) {i : Fin 3} (hi : i ≠ 2)
    (k j : ℕ) (hj : 1 ≤ j) : curveJet P i k j = 0 := by
  fin_cases i
  · simp [curveJet, widthJet, show j ≠ 0 by omega]
  · simp [curveJet, centerJet, show j ≠ 0 by omega]
  · exact (hi rfl).elim

/-- The finite width and center chains have exactly constant terminal tails. -/
theorem curve_right_flat (P : Parameters) {i : Fin 3} (hi : i ≠ 2)
    {j : ℕ} (hj : j ≤ 2) {t : ℝ} (ht : horizontal P P.horizon ≤ t) :
    iteratedDeriv j (curve P i) t =
      if j = 0 then curveJet P i P.horizon 0 else 0 := by
  rw [curve_right P i hj ht,
    Hermite.taylorTail_of_flat (fun a ha _ => curveJet_flat P hi P.horizon a ha),
    iteratedDeriv_const]

/-- The actual two-dimensional source corridor function uses the genuine curves. -/
def residualCorridor (P : Parameters) : ℝ × ℝ → ℝ :=
  corridorFunction (curve P 0) (curve P 1)

/-- The genuine global source corridor function is twice continuously differentiable. -/
theorem contDiff_residualCorridor (P : Parameters) : ContDiff ℝ 2 (residualCorridor P) :=
  contDiff_corridorFunction (curve_spec P 0).1 (curve_spec P 1).1

end ExactSteepestDescent.Corridor
