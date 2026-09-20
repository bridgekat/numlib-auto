import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Numlib.Analysis.PDE.Heat.SineSeries
import Numlib.FiniteDifference.TwoLevel
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz
import NumlibSurface.AtkinsonHan.Chapter06.Section02

/-!
# Atkinson–Han §6.3: two-level difference schemes

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §6.3.

The section studies the two-level recursion (6.3.4)–(6.3.5)

  `v^{m+1} = Q v^m + h_t g^m`,  `v^0 = u^0`,

whose exact values satisfy the same recursion with an extra local truncation error `h_t τ^m`
(6.3.6).  Definition 6.3.1 asks for consistency, order, stability and convergence *of a family* of
such schemes as the two mesh parameters `h_x` and `h_t` are refined, so the definitions below are
stated for a family indexed by an arbitrary type with a filter along which the mesh is refined;
that filter is what "as `h_x, h_t → 0`" means.  Theorem 6.3.2 is then one inequality with explicit
constants, `FiniteDifference.norm_sub_le_of_stable`, together with two limits; its two claims are
`theorem_6_3_2` (consistency and stability give convergence) and `theorem_6_3_2'` (order `(p₁, p₂)`
gives the error estimate).

The book works in `ℝ^{N_x - 1}` and leaves the norm on it unspecified, saying that it will be
chosen per example — the two worked examples use the maximum norm and a scaled discrete two-norm
on the same space and get different stability conditions.  The surface therefore takes an
arbitrary real normed space, which is more faithful than fixing `EuclideanSpace ℝ (Fin (N_x - 1))`,
not less.  The truncation error `τ^m` is data of the statement, defined by the relation (6.3.6)
that the exact values satisfy, rather than a derived quantity.

Exercise 6.3.1, the eigenvalues of a tridiagonal Toeplitz matrix, is `exercise_6_3_1`; it is the
one piece of the section's concrete material with independent interest, and its content lives in
the backbone as `Matrix.tridiagonalToeplitz_hasEigenvalue_iff`.

## Examples 6.3.3 and 6.3.4

The forward and backward schemes for the heat equation `u_t = ν u_xx + f` on `(0, π) × (0, T)`,
in the maximum norm and in the discrete weighted `2`-norm `‖v‖_{2, h_x} = √h_x ‖v‖₂`. The book
*assumes* an exact solution with `u_tt` and `u_xxxx` continuous on the closed rectangle; that
hypothesis is the structure `IsRegularHeatSolution`, which carries the solution with its derivative
towers in `x` (to order four) and in `t` (to order two), one-sided at the edges, the two bounds
`M_tt`, `M_xxxx`, the equation and the boundary values. The four nodes `example_6_3_3`,
`example_6_3_3_l2`, `example_6_3_4`, `example_6_3_4_l2` are the error bounds
`max_m ‖u^m - v^m‖ ≤ c (h_x² + h_t)` with the explicit constant
`c = (M_tt / 2 + ν M_xxxx / 12) T` (times `√π` in the weighted `2`-norm), obtained from the
backbone form `FiniteDifference.norm_sub_le_of_stable` of Theorem 6.3.2 with the horizon cut at
`N_t`, the Taylor bounds of `Numlib.Analysis.Calculus.Taylor` for the truncation errors, and the
stability bounds `‖Q‖_∞ ≤ 1`, `‖Q‖₂ ≤ 1` (for `r ≤ 1/2` in the forward case, unconditionally in
the backward one, where `Q = Q₁⁻¹`). The `2`-norm stability reads the spectrum of Exercise 6.3.1
through `Matrix.isSymmetricBoundedBy_symmTridiagonalToeplitz_of_mem_Icc`; the backward scheme's
`‖Q‖_∞ ≤ 1` is the book's diagonal-dominance argument.

The sine-series solutions of Example 6.2.4 (`Heat.sineSeries`) have all the regularity assumed,
with `M_tt = ∑ |b_j| (ν j²)²` and `M_xxxx = ∑ |b_j| j⁴` (`sineSeries_isRegularHeatSolution`), and
`example_6_3_3_sineSeries`, `example_6_3_4_sineSeries` are the two examples for them.

## Not formalized here

Exercises 6.3.2–6.3.3 (Crank–Nicolson and the generalized midpoint scheme).
-/

open Filter Set
open scoped Real

namespace AtkinsonHan.Chapter06

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

/-- **Definition 6.3.1, consistency.**  A family of two-level schemes, indexed by `ι` and refined
along the filter `l`, is *consistent* when the largest local truncation error inside the horizon,
`sup_{m h_t ≤ T} ‖τ^m‖`, tends to `0` as the mesh is refined. -/
def IsConsistentScheme (l : Filter ι) (ht : ι → ℝ) (τ : ι → ℕ → E) (T : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ i in l, ∀ m : ℕ, (m : ℝ) * ht i ≤ T → ‖τ i m‖ ≤ ε

/-- **Definition 6.3.1, order** (6.3.7).  The family is *of order* `(p₁, p₂)` with constant `c`
when the local truncation errors inside the horizon satisfy
`‖τ^m‖ ≤ c (h_x^{p₁} + h_t^{p₂})` for every mesh.  A family of some order is consistent as soon as
`h_x^{p₁} + h_t^{p₂} → 0` along the refinement. -/
def IsSchemeOfOrder (hx ht : ι → ℝ) (τ : ι → ℕ → E) (T c : ℝ) (p₁ p₂ : ℕ) : Prop :=
  ∀ (i : ι) (m : ℕ), (m : ℝ) * ht i ≤ T → ‖τ i m‖ ≤ c * (hx i ^ p₁ + ht i ^ p₂)

/-- **Definition 6.3.1, stability.**  The family is *stable* with constant `M₀` when
`sup_{m h_t ≤ T} ‖Q^m‖ ≤ M₀` for every mesh, the constant being independent of the mesh — which is
what taking a single `M₀` for all indices says. -/
def IsStableScheme (ht : ι → ℝ) (Q : ι → E →L[ℝ] E) (T M₀ : ℝ) : Prop :=
  ∀ (i : ι) (m : ℕ), (m : ℝ) * ht i ≤ T → ‖Q i ^ m‖ ≤ M₀

/-- **Definition 6.3.1, convergence.**  The family is *convergent* when the largest error inside
the horizon, `sup_{m h_t ≤ T} ‖u^m - v^m‖`, tends to `0` as the mesh is refined. -/
def IsConvergentScheme (l : Filter ι) (ht : ι → ℝ) (u v : ι → ℕ → E) (T : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ i in l, ∀ m : ℕ, (m : ℝ) * ht i ≤ T → ‖u i m - v i m‖ ≤ ε

section Theorem632

variable {ht hx : ι → ℝ} {Q : ι → E →L[ℝ] E} {u v g τ : ι → ℕ → E} {T M₀ : ℝ}

/-- The error bound of Theorem 6.3.2 at one mesh: a bound `δ` on the local truncation errors
inside the horizon bounds the error by `M₀ T δ`.  This is
`FiniteDifference.norm_sub_le_of_stable` applied with the horizon cut at the step being estimated,
which is why no separate count of time levels is needed. -/
private theorem error_le (hht : ∀ i, 0 ≤ ht i)
    (hv : ∀ (i : ι) (m : ℕ), v i (m + 1) = Q i (v i m) + ht i • g i m)
    (hu : ∀ (i : ι) (m : ℕ), u i (m + 1) = Q i (u i m) + ht i • g i m + ht i • τ i m)
    (h0 : ∀ i : ι, u i 0 = v i 0) (hstab : IsStableScheme ht Q T M₀) (i : ι) {δ : ℝ} (hδ : 0 ≤ δ)
    (hτ : ∀ m : ℕ, (m : ℝ) * ht i ≤ T → ‖τ i m‖ ≤ δ) {m : ℕ} (hm : (m : ℝ) * ht i ≤ T) :
    ‖u i m - v i m‖ ≤ M₀ * T * δ := by
  have hle : ∀ k : ℕ, k ≤ m → (k : ℝ) * ht i ≤ T := fun k hk =>
    le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (hht i)) hm
  exact FiniteDifference.norm_sub_le_of_stable (hht i) hδ hm (fun k _ => hv i k)
    (fun k _ => hu i k) (h0 i) (fun k hk => hstab i k (hle k hk))
    (fun k hk => hτ k (hle k hk.le)) le_rfl

/-- **Theorem 6.3.2**, first claim.  A consistent and stable family of two-level schemes is
convergent, its error inside the horizon obeying
`sup_{m h_t ≤ T} ‖u^m - v^m‖ ≤ M₀ T sup_{m h_t ≤ T} ‖τ^m‖`.

The exact values `u` and the computed values `v` obey the same two-level recursion, the exact ones
carrying the local truncation error `h_t τ^m` of (6.3.6), and they start from the same value. -/
theorem theorem_6_3_2 {l : Filter ι} (hT : 0 ≤ T) (hht : ∀ i, 0 ≤ ht i)
    (hv : ∀ (i : ι) (m : ℕ), v i (m + 1) = Q i (v i m) + ht i • g i m)
    (hu : ∀ (i : ι) (m : ℕ), u i (m + 1) = Q i (u i m) + ht i • g i m + ht i • τ i m)
    (h0 : ∀ i : ι, u i 0 = v i 0) (hstab : IsStableScheme ht Q T M₀)
    (hcons : IsConsistentScheme l ht τ T) :
    IsConvergentScheme l ht u v T := by
  intro ε hε
  have hM : (0 : ℝ) ≤ max M₀ 0 := le_max_right _ _
  have hMT : (0 : ℝ) ≤ max M₀ 0 * T := mul_nonneg hM hT
  have hden : (0 : ℝ) < max M₀ 0 * T + 1 := by linarith
  have hδpos : (0 : ℝ) < ε / (max M₀ 0 * T + 1) := div_pos hε hden
  filter_upwards [hcons _ hδpos] with i hi
  intro m hm
  calc ‖u i m - v i m‖ ≤ M₀ * T * (ε / (max M₀ 0 * T + 1)) :=
        error_le hht hv hu h0 hstab i hδpos.le hi hm
    _ ≤ max M₀ 0 * T * (ε / (max M₀ 0 * T + 1)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hT) hδpos.le
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ hden]
        nlinarith [hε.le]

/-- **Theorem 6.3.2**, second claim: a stable family of order `(p₁, p₂)` with constant `c` has
error at most `M₀ T c (h_x^{p₁} + h_t^{p₂})` inside the horizon.  Consistency is not needed
separately, being implied by (6.3.7) once the mesh is refined. -/
theorem theorem_6_3_2' (hT : 0 ≤ T) (hht : ∀ i, 0 ≤ ht i)
    (hv : ∀ (i : ι) (m : ℕ), v i (m + 1) = Q i (v i m) + ht i • g i m)
    (hu : ∀ (i : ι) (m : ℕ), u i (m + 1) = Q i (u i m) + ht i • g i m + ht i • τ i m)
    (h0 : ∀ i : ι, u i 0 = v i 0) (hstab : IsStableScheme ht Q T M₀) {c : ℝ} {p₁ p₂ : ℕ}
    (hord : IsSchemeOfOrder hx ht τ T c p₁ p₂) (i : ι) {m : ℕ} (hm : (m : ℝ) * ht i ≤ T) :
    ‖u i m - v i m‖ ≤ M₀ * T * (c * (hx i ^ p₁ + ht i ^ p₂)) := by
  have hδ0 : 0 ≤ c * (hx i ^ p₁ + ht i ^ p₂) :=
    le_trans (norm_nonneg _) (hord i 0 (by simpa using hT))
  exact error_le hht hv hu h0 hstab i hδ0 (fun k hk => hord i k hk) hm

end Theorem632

section Toeplitz

/-- **Exercise 6.3.1**: for `a, b, c ∈ ℝ` with `b c ≥ 0`, the `N × N` tridiagonal Toeplitz matrix
`Q` with `a` on the diagonal, `b` on the subdiagonal and `c` on the superdiagonal has the `N`
eigenvalues

`λ_j = a + 2 √(b c) cos(jπ / (N + 1))`,  `1 ≤ j ≤ N`

(here indexed by `j : Fin N`, so that the book's `j` is `j + 1`).  This is the backbone's
`Matrix.tridiagonalToeplitz_hasEigenvalue_iff`, whose argument order is `tridiag(sub, diag, super)`
rather than the book's `(diag, sub, super)`.

It is the spectral fact behind Examples 6.3.3 and 6.3.4, where the stability of the forward and
backward schemes for the heat equation is read off the eigenvalues of `tridiag(-1, 2, -1)` — the
symmetric case `b = c`, which the backbone treats directly. -/
theorem exercise_6_3_1 (N : ℕ) (a b c : ℝ) (hbc : 0 ≤ b * c) (μ : ℝ) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin (Matrix.tridiagonalToeplitz N b a c)) μ ↔
      ∃ j : Fin N, μ = a + 2 * Real.sqrt (b * c)
        * Real.cos ((((j : ℕ) : ℝ) + 1) * π / ((N : ℝ) + 1)) :=
  Matrix.tridiagonalToeplitz_hasEigenvalue_iff N b a c hbc μ

end Toeplitz

/-! ### Examples 6.3.3 and 6.3.4: the forward and backward schemes for the heat equation -/

section HeatSchemes

open Matrix
open scoped Matrix.Norms.L2Operator

/-- **The regularity assumed in Examples 6.3.3–6.3.4.** A solution `u` of the heat equation
`u_t = ν u_xx + f` on `[0, π] × [0, T]` with the boundary values `u (0, t) = u (π, t) = 0`,
given with its derivatives: `ux m` is `∂ₓ^m u` for `m ≤ 4` and `ut m` is `∂ₜ^m u` for `m ≤ 2`,
each the derivative of the previous one *within* the closed rectangle (one-sided at its edges,
which is what "`u_tt, u_xxxx ∈ C([0, π] × [0, T])`" gives), and the two bounds
`|u_tt| ≤ M_tt`, `|u_xxxx| ≤ M_xxxx` on the rectangle, which are the constants the book's `c`
depends on. The equation is asked for on the closed rectangle, as continuity of the derivatives
gives it there from the open one. -/
structure IsRegularHeatSolution (ν T : ℝ) (f u : ℝ × ℝ → ℝ) (ux ut : ℕ → ℝ × ℝ → ℝ)
    (Mtt Mxxxx : ℝ) : Prop where
  /-- `ux 0 = u`. -/
  ux_zero : ux 0 = u
  /-- `ut 0 = u`. -/
  ut_zero : ut 0 = u
  /-- `ux (m + 1)` is the spatial derivative of `ux m`, within `[0, π]`, for `m < 4`. -/
  hasDerivWithinAt_ux : ∀ m < 4, ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) π,
    HasDerivWithinAt (fun y => ux m (y, t)) (ux (m + 1) (x, t)) (Icc 0 π) x
  /-- `ut (m + 1)` is the time derivative of `ut m`, within `[0, T]`, for `m < 2`. -/
  hasDerivWithinAt_ut : ∀ m < 2, ∀ x ∈ Icc (0 : ℝ) π, ∀ t ∈ Icc (0 : ℝ) T,
    HasDerivWithinAt (fun s => ut m (x, s)) (ut (m + 1) (x, t)) (Icc 0 T) t
  /-- `|u_tt| ≤ M_tt` on the rectangle. -/
  abs_ut_two_le : ∀ x ∈ Icc (0 : ℝ) π, ∀ t ∈ Icc (0 : ℝ) T, |ut 2 (x, t)| ≤ Mtt
  /-- `|u_xxxx| ≤ M_xxxx` on the rectangle. -/
  abs_ux_four_le : ∀ x ∈ Icc (0 : ℝ) π, ∀ t ∈ Icc (0 : ℝ) T, |ux 4 (x, t)| ≤ Mxxxx
  /-- The heat equation `u_t = ν u_xx + f`. -/
  equation : ∀ x ∈ Icc (0 : ℝ) π, ∀ t ∈ Icc (0 : ℝ) T, ut 1 (x, t) = ν * ux 2 (x, t) + f (x, t)
  /-- The boundary value at `x = 0`. -/
  left : ∀ t ∈ Icc (0 : ℝ) T, u (0, t) = 0
  /-- The boundary value at `x = π`. -/
  right : ∀ t ∈ Icc (0 : ℝ) T, u (π, t) = 0

variable {ν T : ℝ} {f u : ℝ × ℝ → ℝ} {ux ut : ℕ → ℝ × ℝ → ℝ} {Mtt Mxxxx : ℝ}

namespace IsRegularHeatSolution

variable (hu : IsRegularHeatSolution ν T f u ux ut Mtt Mxxxx)
include hu

/-- The forward Taylor bound in time: `|u (x, t + k) - u (x, t) - k u_t (x, t)| ≤ M_tt k² / 2`. -/
theorem abs_sub_forward_time_le {x t k : ℝ} (hx : x ∈ Icc (0 : ℝ) π) (ht : t ∈ Icc (0 : ℝ) T)
    (hk : 0 ≤ k) (htk : t + k ≤ T) :
    |u (x, t + k) - u (x, t) - k * ut 1 (x, t)| ≤ Mtt * k ^ 2 / 2 := by
  have hsub : Icc t (t + k) ⊆ Icc 0 T := Icc_subset_Icc ht.1 htk
  have h := norm_sub_sub_smul_le_mul_sq_div_two (y := fun s => u (x, s))
    (y' := fun s => ut 1 (x, s)) (y'' := fun s => ut 2 (x, s)) (M := Mtt) (by linarith)
    (fun s hs => by
      have := hu.hasDerivWithinAt_ut 0 (by norm_num) x hx s (hsub hs)
      rw [hu.ut_zero] at this
      exact this.mono hsub)
    (fun s hs => (hu.hasDerivWithinAt_ut 1 (by norm_num) x hx s (hsub hs)).mono hsub)
    (fun s hs => by rw [Real.norm_eq_abs]; exact hu.abs_ut_two_le x hx s (hsub hs))
  simpa [smul_eq_mul, Real.norm_eq_abs] using h

/-- The backward Taylor bound in time:
`|u (x, t + k) - u (x, t) - k u_t (x, t + k)| ≤ M_tt k² / 2`. -/
theorem abs_sub_backward_time_le {x t k : ℝ} (hx : x ∈ Icc (0 : ℝ) π) (ht : t ∈ Icc (0 : ℝ) T)
    (hk : 0 ≤ k) (htk : t + k ≤ T) :
    |u (x, t + k) - u (x, t) - k * ut 1 (x, t + k)| ≤ Mtt * k ^ 2 / 2 := by
  have hsub : Icc t (t + k) ⊆ Icc 0 T := Icc_subset_Icc ht.1 htk
  have h := norm_sub_sub_smul_le_mul_sq_div_two' (y := fun s => u (x, s))
    (y' := fun s => ut 1 (x, s)) (y'' := fun s => ut 2 (x, s)) (M := Mtt) (by linarith)
    (fun s hs => by
      have := hu.hasDerivWithinAt_ut 0 (by norm_num) x hx s (hsub hs)
      rw [hu.ut_zero] at this
      exact this.mono hsub)
    (fun s hs => (hu.hasDerivWithinAt_ut 1 (by norm_num) x hx s (hsub hs)).mono hsub)
    (fun s hs => by rw [Real.norm_eq_abs]; exact hu.abs_ut_two_le x hx s (hsub hs))
  rw [smul_eq_mul, Real.norm_eq_abs, add_sub_cancel_left] at h
  have e : u (x, t + k) - u (x, t) - k * ut 1 (x, t + k)
      = -(u (x, t) - u (x, t + k) - (t - (t + k)) * ut 1 (x, t + k)) := by ring
  rw [e, abs_neg]
  exact h

/-- The Taylor bound for the centred second difference in space:
`|u (x + h, t) - 2 u (x, t) + u (x - h, t) - h² u_xx (x, t)| ≤ M_xxxx h⁴ / 12`. -/
theorem abs_centred_sub_le {x t h : ℝ} (hxl : x - h ∈ Icc (0 : ℝ) π) (hxr : x + h ∈ Icc (0 : ℝ) π)
    (hh : 0 ≤ h) (ht : t ∈ Icc (0 : ℝ) T) :
    |u (x + h, t) - 2 * u (x, t) + u (x - h, t) - h ^ 2 * ux 2 (x, t)| ≤ Mxxxx * h ^ 4 / 12 := by
  have hx : x ∈ Icc (0 : ℝ) π := ⟨by linarith [hxl.1], by linarith [hxr.2]⟩
  have hy : ∀ m < 4, ∀ s ∈ Icc (0 : ℝ) π,
      HasDerivWithinAt (fun y => ux m (y, t)) (ux (m + 1) (s, t)) (Icc 0 π) s :=
    fun m hm s hs => hu.hasDerivWithinAt_ux m hm t ht s hs
  have hK : ∀ s ∈ Icc (0 : ℝ) π, ‖ux 4 (s, t)‖ ≤ Mxxxx := fun s hs => by
    rw [Real.norm_eq_abs]; exact hu.abs_ux_four_le s hs t ht
  have hr := norm_sub_sum_smul_le (y := fun m y => ux m (y, t)) 4 hy hK hx hxr
  have hl := norm_sub_sum_smul_le (y := fun m y => ux m (y, t)) 4 hy hK hx hxl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, smul_eq_mul,
    Real.norm_eq_abs, hu.ux_zero, add_sub_cancel_left, sub_sub_cancel_left, abs_neg,
    abs_of_nonneg hh] at hr hl
  push_cast at hr hl
  have e : u (x + h, t) - 2 * u (x, t) + u (x - h, t) - h ^ 2 * ux 2 (x, t)
      = (u (x + h, t) - (0 + h ^ 0 / 1 * u (x, t) + h ^ 1 / 1 * ux 1 (x, t)
          + h ^ 2 / 2 * ux 2 (x, t) + h ^ 3 / 6 * ux 3 (x, t)))
        + (u (x - h, t) - (0 + (-h) ^ 0 / 1 * u (x, t) + (-h) ^ 1 / 1 * ux 1 (x, t)
          + (-h) ^ 2 / 2 * ux 2 (x, t) + (-h) ^ 3 / 6 * ux 3 (x, t))) := by
    ring
  rw [e]
  calc _ ≤ Mxxxx * h ^ 4 / 24 + Mxxxx * h ^ 4 / 24 :=
        (abs_add_le _ _).trans (add_le_add hr hl)
    _ = Mxxxx * h ^ 4 / 12 := by ring

end IsRegularHeatSolution

/-! #### The grid and the two matrices -/

/-- The values of a function of `(x, t)` on the interior grid at time level `m`:
`u^m_j = u (x_j, t_m)` with `x_j = (j + 1) h_x` and `t_m = m h_t`, for `j : Fin (N + 1)` — so
the book's `N_x - 1` interior points `x_1, …, x_{N_x - 1}` are indexed from `0`, and
`N_x = N + 2`. -/
def gridValues (N : ℕ) (u : ℝ × ℝ → ℝ) (hx ht : ℝ) (m : ℕ) : Fin (N + 1) → ℝ :=
  fun j => u (((j : ℕ) + 1) * hx, m * ht)

/-- The value of `u^m_j`. -/
theorem gridValues_apply (N : ℕ) (u : ℝ × ℝ → ℝ) (hx ht : ℝ) (m : ℕ) (j : Fin (N + 1)) :
    gridValues N u hx ht m j = u (((j : ℕ) + 1) * hx, m * ht) := rfl

/-- The three-term row of `tridiag(a, b, a)` on `Fin (N + 1)`, the boundary terms absent in the
first and last rows: `Matrix.tridiagonalOf_mulVec` for the constant bands. -/
private theorem symmTridiagonalToeplitz_mulVec_apply' {N : ℕ} (a b : ℝ) (v : Fin (N + 1) → ℝ)
    (i : Fin (N + 1)) :
    (symmTridiagonalToeplitz (N + 1) a b *ᵥ v) i
      = (if h : 0 < (i : ℕ) then a * v ⟨i - 1, by omega⟩ else 0) + b * v i
        + (if h : (i : ℕ) < N then a * v ⟨i + 1, by omega⟩ else 0) := by
  rw [symmTridiagonalToeplitz_eq_tridiagonalToeplitz, tridiagonalToeplitz_eq_tridiagonalOf,
    tridiagonalOf_mulVec]

/-- On the grid values of a function vanishing at `x = 0` and `x = π = (N + 2) h_x`, the row of
`tridiag(a, b, a)` reads uniformly `a u (x_j - h_x) + b u (x_j) + a u (x_j + h_x)`. -/
private theorem symmTridiagonalToeplitz_mulVec_gridValues {N : ℕ} {u : ℝ × ℝ → ℝ} {hx ht : ℝ}
    (hhx : hx = π / (N + 2)) (a b : ℝ) (m : ℕ) (h0 : u (0, m * ht) = 0) (hπ : u (π, m * ht) = 0)
    (i : Fin (N + 1)) :
    (symmTridiagonalToeplitz (N + 1) a b *ᵥ gridValues N u hx ht m) i
      = a * u ((i : ℕ) * hx, m * ht) + b * u (((i : ℕ) + 1) * hx, m * ht)
        + a * u (((i : ℕ) + 2) * hx, m * ht) := by
  have hN2 : ((N : ℝ) + 2) ≠ 0 := by positivity
  rw [symmTridiagonalToeplitz_mulVec_apply']
  congr 1
  · congr 1
    split_ifs with hi
    · rw [gridValues_apply]
      congr 3
      push_cast [Nat.cast_sub hi]
      ring
    · have : (i : ℕ) = 0 := by omega
      rw [this, Nat.cast_zero, zero_mul, h0, mul_zero]
  · split_ifs with hi
    · rw [gridValues_apply]
      push_cast
      ring_nf
    · have : (i : ℕ) = N := by omega
      rw [this, show ((N : ℝ) + 2) * hx = π by rw [hhx]; field_simp, hπ, mul_zero]

/-- The row bound `|(tridiag(a, b, a) v)_i| ≤ (2 |a| + |b|) ‖v‖_∞`. -/
private theorem abs_symmTridiagonalToeplitz_mulVec_le {N : ℕ} (a b : ℝ) (v : Fin (N + 1) → ℝ)
    (i : Fin (N + 1)) :
    |(symmTridiagonalToeplitz (N + 1) a b *ᵥ v) i| ≤ (2 * |a| + |b|) * ‖v‖ := by
  rw [symmTridiagonalToeplitz_mulVec_apply']
  have hv : ∀ j, |v j| ≤ ‖v‖ := fun j => (Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm v j)
  have h1 : |if h : 0 < (i : ℕ) then a * v ⟨i - 1, by omega⟩ else 0| ≤ |a| * ‖v‖ := by
    split_ifs
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hv _) (abs_nonneg a)
    · rw [abs_zero]; positivity
  have h2 : |if h : (i : ℕ) < N then a * v ⟨i + 1, by omega⟩ else 0| ≤ |a| * ‖v‖ := by
    split_ifs
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hv _) (abs_nonneg a)
    · rw [abs_zero]; positivity
  have h3 : |b * v i| ≤ |b| * ‖v‖ := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hv _) (abs_nonneg b)
  calc _ ≤ |if h : 0 < (i : ℕ) then a * v ⟨i - 1, by omega⟩ else 0| + |b * v i|
        + |if h : (i : ℕ) < N then a * v ⟨i + 1, by omega⟩ else 0| := abs_add_three _ _ _
    _ ≤ |a| * ‖v‖ + |b| * ‖v‖ + |a| * ‖v‖ := add_le_add (add_le_add h1 h3) h2
    _ = (2 * |a| + |b|) * ‖v‖ := by ring

/-- A matrix as a bounded operator on `ℝ^{N+1}` with the maximum norm. -/
private noncomputable def toLinfty {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    (Fin (N + 1) → ℝ) →L[ℝ] (Fin (N + 1) → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' A)

private theorem toLinfty_apply {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (v : Fin (N + 1) → ℝ) : toLinfty A v = A *ᵥ v := by
  rw [toLinfty, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply]

/-- The powers of an operator of norm at most `1` have norm at most `1`. -/
private theorem norm_pow_le_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : E →L[ℝ] E} (hQ : ‖Q‖ ≤ 1) (m : ℕ) : ‖Q ^ m‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [pow_zero]
    exact ContinuousLinearMap.norm_id_le
  · exact (norm_pow_le' Q hm).trans (pow_le_one₀ (norm_nonneg _) hQ)

/-- The `ℓ²` operator norm of a symmetric matrix whose quadratic form is enclosed in `[-M, M]` is
at most `M`: one half of `Matrix.IsHermitian.l2_opNorm_eq`, through Rayleigh quotients. -/
private theorem norm_toEuclideanCLM_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hb : (toEuclideanLin A).IsSymmetricBoundedBy (-M) M) :
    ‖toEuclideanCLM (𝕜 := ℝ) A‖ ≤ M := by
  set Tc : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearMap.toContinuousLinearMap (toEuclideanLin A) with hTc
  have hTsymm : (Tc : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric :=
    hb.isSymmetric
  rw [l2_opNorm_toEuclideanCLM, l2_opNorm_eq_norm_toEuclideanLin, ← hTc,
    ContinuousLinearMap.norm_eq_iSup_rayleighQuotient Tc hTsymm]
  refine ciSup_le fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf] using hM
  · have h := hb.rayleigh_mem_Icc hx
    rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf, abs_le]
    exact ⟨h.1, h.2⟩

/-- The Euclidean norm of a vector of `ℝ^{N+1}` is at most `√(N + 1)` times its maximum norm. -/
private theorem norm_toLp_le {N : ℕ} (v : Fin (N + 1) → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hv : ∀ j, |v j| ≤ δ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (N + 1)))‖ ≤ Real.sqrt ((N : ℝ) + 1) * δ := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq hδ, ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (N + 1))) i‖ ^ 2
      ≤ ∑ _i : Fin (N + 1), δ ^ 2 := Finset.sum_le_sum fun i _ => by
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hv i) 2
    _ = ((N : ℝ) + 1) * δ ^ 2 := by simp

/-! #### The forward scheme, Example 6.3.3 -/

section Forward

variable {N Nt : ℕ} {hx ht r : ℝ} (hν : 0 < ν) (hT : 0 < T) (hNt : 0 < Nt)
  (hhx : hx = π / (N + 2)) (hht : ht = T / Nt) (hr : r = ν * ht / hx ^ 2)

/-- The local truncation error of the forward scheme, defined by (6.3.6): `τ^m` is what has to be
added to `Q u^m + h_t f^m` to reach `u^{m+1}`, divided by `h_t`. -/
private noncomputable def forwardTrunc (N : ℕ) (u f : ℝ × ℝ → ℝ) (hx ht r : ℝ) (m : ℕ) :
    Fin (N + 1) → ℝ :=
  ht⁻¹ • (gridValues N u hx ht (m + 1) - symmTridiagonalToeplitz (N + 1) r (1 - 2 * r) *ᵥ
    gridValues N u hx ht m - ht • gridValues N f hx ht m)

include hT hNt hht in
private theorem gridValues_succ_forward (u f : ℝ × ℝ → ℝ) (m : ℕ) :
    gridValues N u hx ht (m + 1)
      = symmTridiagonalToeplitz (N + 1) r (1 - 2 * r) *ᵥ gridValues N u hx ht m
        + ht • gridValues N f hx ht m + ht • forwardTrunc N u f hx ht r m := by
  have hht0 : ht ≠ 0 := by rw [hht]; positivity
  rw [forwardTrunc, smul_smul, mul_inv_cancel₀ hht0, one_smul]
  abel

include hν hT hNt hhx hht hr in
/-- **The truncation error of the forward scheme** (Example 6.3.3): by Taylor expansion,
`|τ^m_j| ≤ (M_tt / 2) h_t + (ν M_xxxx / 12) h_x² ≤ c (h_x² + h_t)` with
`c = M_tt / 2 + ν M_xxxx / 12`, at every time level `m < N_t`. -/
private theorem abs_forwardTrunc_le (hu : IsRegularHeatSolution ν T f u ux ut Mtt Mxxxx)
    {m : ℕ} (hm : m < Nt) (j : Fin (N + 1)) :
    |forwardTrunc N u f hx ht r m j| ≤ (Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht) := by
  have hN2 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hhx0 : 0 < hx := by rw [hhx]; positivity
  have hht0 : 0 < ht := by rw [hht]; positivity
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hMtt : 0 ≤ Mtt := (abs_nonneg _).trans (hu.abs_ut_two_le 0 (left_mem_Icc.2 Real.pi_pos.le)
    0 (left_mem_Icc.2 hT.le))
  have hMx : 0 ≤ Mxxxx := (abs_nonneg _).trans (hu.abs_ux_four_le 0
    (left_mem_Icc.2 Real.pi_pos.le) 0 (left_mem_Icc.2 hT.le))
  -- the grid point and the two time levels
  set x : ℝ := ((j : ℕ) + 1) * hx with hxdef
  set t : ℝ := m * ht with htdef
  have hxmem : x ∈ Icc (0 : ℝ) π := by
    refine ⟨by positivity, ?_⟩
    rw [hxdef, hhx]
    have : ((j : ℕ) : ℝ) + 1 ≤ (N : ℝ) + 2 := by
      have := j.isLt
      exact_mod_cast (by omega : (j : ℕ) + 1 ≤ N + 2)
    calc ((j : ℕ) + 1) * (π / (N + 2)) ≤ ((N : ℝ) + 2) * (π / (N + 2)) :=
        mul_le_mul_of_nonneg_right this (by positivity)
      _ = π := by field_simp
  have hxl : x - hx ∈ Icc (0 : ℝ) π := by
    refine ⟨by rw [hxdef]; nlinarith, by linarith [hxmem.2]⟩
  have hxr : x + hx ∈ Icc (0 : ℝ) π := by
    refine ⟨by linarith [hxmem.1], ?_⟩
    rw [hxdef, hhx]
    have : ((j : ℕ) : ℝ) + 2 ≤ (N : ℝ) + 2 := by
      have := j.isLt
      exact_mod_cast (by omega : (j : ℕ) + 2 ≤ N + 2)
    calc ((j : ℕ) + 1) * (π / (N + 2)) + π / (N + 2) = ((j : ℕ) + 2) * (π / (N + 2)) := by ring
      _ ≤ ((N : ℝ) + 2) * (π / (N + 2)) :=
        mul_le_mul_of_nonneg_right this (by positivity)
      _ = π := by field_simp
  have htmem : t ∈ Icc (0 : ℝ) T := by
    refine ⟨by positivity, ?_⟩
    rw [htdef, hht]
    have : (m : ℝ) ≤ Nt := by exact_mod_cast hm.le
    calc (m : ℝ) * (T / Nt) ≤ Nt * (T / Nt) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = T := by field_simp
  have htk : t + ht ≤ T := by
    rw [htdef, hht]
    have : (m : ℝ) + 1 ≤ Nt := by exact_mod_cast hm
    calc (m : ℝ) * (T / Nt) + T / Nt = ((m : ℝ) + 1) * (T / Nt) := by ring
      _ ≤ Nt * (T / Nt) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = T := by field_simp
  -- the boundary values at the two levels
  have hb0 : u (0, m * ht) = 0 := hu.left _ htmem
  have hbπ : u (π, m * ht) = 0 := hu.right _ htmem
  -- the identity `h_t τ = A - r B`
  have hrow := symmTridiagonalToeplitz_mulVec_gridValues (u := u) (ht := ht) hhx r (1 - 2 * r) m
    hb0 hbπ j
  have hτ : ht * forwardTrunc N u f hx ht r m j
      = (u (x, t + ht) - u (x, t) - ht * ut 1 (x, t))
        - r * (u (x + hx, t) - 2 * u (x, t) + u (x - hx, t) - hx ^ 2 * ux 2 (x, t)) := by
    have heq := hu.equation x hxmem t htmem
    have hrhx : r * hx ^ 2 = ν * ht := by
      rw [hr, div_mul_cancel₀ _ (pow_ne_zero 2 hhx0.ne')]
    simp only [forwardTrunc, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hrow, gridValues_apply]
    rw [mul_inv_cancel_left₀ hht0.ne', heq]
    have e1 : (((j : ℕ) : ℝ) + 1) * hx = x := rfl
    have e2 : (((m + 1 : ℕ) : ℝ)) * ht = t + ht := by push_cast; ring
    have e3 : ((j : ℕ) : ℝ) * hx = x - hx := by rw [hxdef]; ring
    have e4 : (((j : ℕ) : ℝ) + 2) * hx = x + hx := by rw [hxdef]; ring
    rw [e1, e2, e3, e4]
    linear_combination (-(ux 2 (x, t))) * hrhx
  have hA := hu.abs_sub_forward_time_le hxmem htmem hht0.le htk
  have hB := hu.abs_centred_sub_le hxl hxr hhx0.le htmem
  have hbound : |ht * forwardTrunc N u f hx ht r m j|
      ≤ ht * ((Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht)) := by
    rw [hτ]
    have hrhx4 : r * hx ^ 4 = ν * ht * hx ^ 2 := by
      rw [hr]; field_simp
    calc |u (x, t + ht) - u (x, t) - ht * ut 1 (x, t)
          - r * (u (x + hx, t) - 2 * u (x, t) + u (x - hx, t) - hx ^ 2 * ux 2 (x, t))|
        ≤ Mtt * ht ^ 2 / 2 + r * (Mxxxx * hx ^ 4 / 12) := by
          refine (abs_sub _ _).trans (add_le_add hA ?_)
          rw [abs_mul, abs_of_nonneg hr0]
          exact mul_le_mul_of_nonneg_left hB hr0
      _ = ht * (Mtt / 2 * ht + ν * Mxxxx / 12 * hx ^ 2) := by
          rw [show r * (Mxxxx * hx ^ 4 / 12) = (r * hx ^ 4) * Mxxxx / 12 by ring, hrhx4]; ring
      _ ≤ ht * ((Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht)) := by
          refine mul_le_mul_of_nonneg_left ?_ hht0.le
          nlinarith [mul_nonneg hMtt (sq_nonneg hx), mul_nonneg (mul_nonneg hν.le hMx) hht0.le]
  rw [abs_mul, abs_of_pos hht0] at hbound
  exact le_of_mul_le_mul_left hbound hht0

/-- **Example 6.3.3, the maximum norm**: for the forward scheme (6.1.8)–(6.1.10) for
`u_t = ν u_xx + f` on `(0, π) × (0, T)` with `r = ν h_t / h_x² ≤ 1/2`, and an exact solution with
`u_tt, u_xxxx` continuous on `[0, π] × [0, T]` (`IsRegularHeatSolution`, with the bounds
`M_tt`, `M_xxxx`), the error at every time level `m ≤ N_t` satisfies

  `max_j |u (x_j, t_m) - v^m_j| ≤ (M_tt / 2 + ν M_xxxx / 12) T (h_x² + h_t)`,

the order-`(2, 1)` estimate of Theorem 6.3.2. The scheme is written as the two-level recursion
`v^{m+1} = Q v^m + h_t f^m` with the tridiagonal Toeplitz `Q = tridiag(r, 1 - 2r, r)` on the
`N + 1` interior points (`N_x = N + 2`); its iteration matrix has `‖Q‖_∞ ≤ 1` for `r ≤ 1/2`, so
the scheme is stable with `M₀ = 1`, and the truncation error is bounded by Taylor expansion.
The horizon is cut at `N_t`, since the exact solution is only assumed regular on `[0, T]`, so
the estimate is `FiniteDifference.norm_sub_le_of_stable`, the backbone form of Theorem 6.3.2. -/
theorem example_6_3_3 (hν : 0 < ν) (hT : 0 < T) {N Nt : ℕ} (hNt : 0 < Nt) {hx ht r : ℝ}
    (hhx : hx = π / (N + 2)) (hht : ht = T / Nt) (hr : r = ν * ht / hx ^ 2) (hr2 : r ≤ 1 / 2)
    (hu : IsRegularHeatSolution ν T f u ux ut Mtt Mxxxx) {v : ℕ → Fin (N + 1) → ℝ}
    (hv0 : v 0 = gridValues N u hx ht 0)
    (hv : ∀ m, v (m + 1) = symmTridiagonalToeplitz (N + 1) r (1 - 2 * r) *ᵥ v m
      + ht • gridValues N f hx ht m)
    {m : ℕ} (hm : m ≤ Nt) :
    ‖gridValues N u hx ht m - v m‖ ≤ (Mtt / 2 + ν * Mxxxx / 12) * T * (hx ^ 2 + ht) := by
  have hhx0 : 0 < hx := by rw [hhx]; positivity
  have hht0 : 0 < ht := by rw [hht]; positivity
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hMtt : 0 ≤ Mtt := (abs_nonneg _).trans (hu.abs_ut_two_le 0 (left_mem_Icc.2 Real.pi_pos.le)
    0 (left_mem_Icc.2 hT.le))
  have hMx : 0 ≤ Mxxxx := (abs_nonneg _).trans (hu.abs_ux_four_le 0
    (left_mem_Icc.2 Real.pi_pos.le) 0 (left_mem_Icc.2 hT.le))
  set Q := toLinfty (symmTridiagonalToeplitz (N + 1) r (1 - 2 * r)) with hQ
  -- stability: `‖Q‖_∞ ≤ 1`
  have hQ1 : ‖Q‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
    rw [one_mul, hQ, toLinfty_apply]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    refine (abs_symmTridiagonalToeplitz_mulVec_le _ _ _ _).trans ?_
    rw [abs_of_nonneg hr0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * r),
      show 2 * r + (1 - 2 * r) = 1 by ring, one_mul]
  have hδ : 0 ≤ (Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht) := by positivity
  have h := FiniteDifference.norm_sub_le_of_stable (Q := Q) (u := gridValues N u hx ht) (v := v)
    (g := gridValues N f hx ht) (τ := forwardTrunc N u f hx ht r) (h := ht) (T := T) (M₀ := 1)
    (N := Nt) hht0.le hδ (le_of_eq (by rw [hht]; field_simp))
    (fun k _ => by rw [hv k, hQ, toLinfty_apply])
    (fun k _ => by rw [gridValues_succ_forward hT hNt hht u f k, hQ, toLinfty_apply])
    hv0.symm (fun k _ => norm_pow_le_one hQ1 k)
    (fun k hk => (pi_norm_le_iff_of_nonneg hδ).2 fun j => by
      rw [Real.norm_eq_abs]
      exact abs_forwardTrunc_le hν hT hNt hhx hht hr hu hk j) hm
  calc ‖gridValues N u hx ht m - v m‖ ≤ 1 * T * ((Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht)) := h
    _ = (Mtt / 2 + ν * Mxxxx / 12) * T * (hx ^ 2 + ht) := by ring

/-- The eigenvalues `1 - 2r + 2r cos θ_k` of `tridiag(r, 1 - 2r, r)` lie in `[-1, 1]` for
`0 ≤ r ≤ 1/2`: the quadratic-form bound behind `‖Q‖₂ < 1` of Example 6.3.3. -/
private theorem isSymmetricBoundedBy_forward {N : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 1 / 2) :
    (toEuclideanLin (symmTridiagonalToeplitz (N + 1) r (1 - 2 * r))).IsSymmetricBoundedBy
      (-1) 1 := by
  refine isSymmetricBoundedBy_symmTridiagonalToeplitz_of_mem_Icc r (1 - 2 * r) fun k => ?_
  have h1 := Real.neg_one_le_cos ((((k : ℕ) : ℝ) + 1) * π / ((N + 1 : ℕ) + 1))
  have h2 := Real.cos_le_one ((((k : ℕ) : ℝ) + 1) * π / ((N + 1 : ℕ) + 1))
  constructor <;> nlinarith

/-- The `√h_x ‖·‖₂` bound derived from the `ℓ²` bound on `ℝ^{N+1}`: `h_x (N + 1) ≤ π`. -/
private theorem sqrt_mul_sum_sq_le {N : ℕ} {hx : ℝ} (hhx : hx = π / (N + 2)) (w : Fin (N + 1) → ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin (N + 1)))‖ ≤ Real.sqrt ((N : ℝ) + 1) * C) :
    Real.sqrt (hx * ∑ j, w j ^ 2) ≤ Real.sqrt π * C := by
  have hhx0 : 0 ≤ hx := by rw [hhx]; positivity
  have hN : hx * ((N : ℝ) + 1) ≤ π := by
    rw [hhx, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  rw [EuclideanSpace.norm_eq] at h
  simp only [Real.norm_eq_abs, sq_abs] at h
  calc Real.sqrt (hx * ∑ j, w j ^ 2) = Real.sqrt hx * Real.sqrt (∑ j, w j ^ 2) :=
        Real.sqrt_mul hhx0 _
    _ ≤ Real.sqrt hx * (Real.sqrt ((N : ℝ) + 1) * C) :=
        mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
    _ = Real.sqrt (hx * ((N : ℝ) + 1)) * C := by rw [Real.sqrt_mul hhx0]; ring
    _ ≤ Real.sqrt π * C := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hN) hC

/-- **Example 6.3.3, the discrete weighted `2`-norm**: under the hypotheses of `example_6_3_3`,
also `‖u^m - v^m‖_{2, h_x} = √h_x ‖u^m - v^m‖₂ ≤ √π (M_tt / 2 + ν M_xxxx / 12) T (h_x² + h_t)`
for `m ≤ N_t`. In `‖·‖_{2, h_x}` the induced matrix norm is the spectral norm, and the eigenvalues
`1 - 4r sin²(jπ / (2 N_x))` of `Q` (Exercise 6.3.1) lie in `[-1, 1]` for `r ≤ 1/2`, so `‖Q‖₂ ≤ 1`
and the scheme is stable with `M₀ = 1`; the truncation error is the same. The factor `√π`
bounds `√(h_x (N_x - 1))`, which converts the maximum-norm bound on `τ^m` into the weighted
`2`-norm one. -/
theorem example_6_3_3_l2 (hν : 0 < ν) (hT : 0 < T) {N Nt : ℕ} (hNt : 0 < Nt) {hx ht r : ℝ}
    (hhx : hx = π / (N + 2)) (hht : ht = T / Nt) (hr : r = ν * ht / hx ^ 2) (hr2 : r ≤ 1 / 2)
    (hu : IsRegularHeatSolution ν T f u ux ut Mtt Mxxxx) {v : ℕ → Fin (N + 1) → ℝ}
    (hv0 : v 0 = gridValues N u hx ht 0)
    (hv : ∀ m, v (m + 1) = symmTridiagonalToeplitz (N + 1) r (1 - 2 * r) *ᵥ v m
      + ht • gridValues N f hx ht m)
    {m : ℕ} (hm : m ≤ Nt) :
    Real.sqrt (hx * ∑ j, (gridValues N u hx ht m j - v m j) ^ 2)
      ≤ Real.sqrt π * ((Mtt / 2 + ν * Mxxxx / 12) * T * (hx ^ 2 + ht)) := by
  have hhx0 : 0 < hx := by rw [hhx]; positivity
  have hht0 : 0 < ht := by rw [hht]; positivity
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hMtt : 0 ≤ Mtt := (abs_nonneg _).trans (hu.abs_ut_two_le 0 (left_mem_Icc.2 Real.pi_pos.le)
    0 (left_mem_Icc.2 hT.le))
  have hMx : 0 ≤ Mxxxx := (abs_nonneg _).trans (hu.abs_ux_four_le 0
    (left_mem_Icc.2 Real.pi_pos.le) 0 (left_mem_Icc.2 hT.le))
  set Q : EuclideanSpace ℝ (Fin (N + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (N + 1)) :=
    toEuclideanCLM (𝕜 := ℝ) (symmTridiagonalToeplitz (N + 1) r (1 - 2 * r)) with hQ
  have hQ1 : ‖Q‖ ≤ 1 := norm_toEuclideanCLM_le zero_le_one (isSymmetricBoundedBy_forward hr0 hr2)
  set c := (Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht) with hc
  have hc0 : 0 ≤ c := by positivity
  have hδ : 0 ≤ Real.sqrt ((N : ℝ) + 1) * c := by positivity
  have h := FiniteDifference.norm_sub_le_of_stable (Q := Q)
    (u := fun k => WithLp.toLp 2 (gridValues N u hx ht k))
    (v := fun k => WithLp.toLp 2 (v k)) (g := fun k => WithLp.toLp 2 (gridValues N f hx ht k))
    (τ := fun k => WithLp.toLp 2 (forwardTrunc N u f hx ht r k)) (h := ht) (T := T) (M₀ := 1)
    (N := Nt) hht0.le hδ (le_of_eq (by rw [hht]; field_simp))
    (fun k _ => by rw [hv k, WithLp.toLp_add, WithLp.toLp_smul, hQ, toEuclideanCLM_toLp])
    (fun k _ => by
      rw [gridValues_succ_forward hT hNt hht u f k, WithLp.toLp_add, WithLp.toLp_add,
        WithLp.toLp_smul, WithLp.toLp_smul, hQ, toEuclideanCLM_toLp])
    (by rw [hv0]) (fun k _ => norm_pow_le_one hQ1 k)
    (fun k hk => norm_toLp_le _ hc0 fun j => abs_forwardTrunc_le hν hT hNt hhx hht hr hu hk j) hm
  rw [← WithLp.toLp_sub, one_mul, ← mul_assoc] at h
  have key := sqrt_mul_sum_sq_le hhx (gridValues N u hx ht m - v m) (C := T * c) (by positivity)
    (h.trans (le_of_eq (by ring)))
  simp only [Pi.sub_apply] at key
  refine key.trans (le_of_eq ?_)
  rw [hc]; ring

end Forward

/-! #### The backward scheme, Example 6.3.4 -/

section Backward

variable {N Nt : ℕ} {hx ht r : ℝ} (hν : 0 < ν) (hT : 0 < T) (hNt : 0 < Nt)
  (hhx : hx = π / (N + 2)) (hht : ht = T / Nt) (hr : r = ν * ht / hx ^ 2)

/-- The matrix `Q₁ = tridiag(-r, 1 + 2r, -r)` of the backward scheme is positive definite, hence
invertible, for every `r ≥ 0`: it is strictly diagonally dominant. -/
private theorem isUnit_backward {r : ℝ} (hr0 : 0 ≤ r) :
    IsUnit (symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r)) :=
  (posDef_symmTridiagonalToeplitz (N + 1) (by rw [abs_neg, abs_of_nonneg hr0]; linarith)).isUnit

/-- The eigenvalues `1 + 2r - 2r cos θ_k` of `Q₁` lie in `[1, 1 + 4r]` for `r ≥ 0`. -/
private theorem isSymmetricBoundedBy_backward {N : ℕ} {r : ℝ} (hr0 : 0 ≤ r) :
    (toEuclideanLin (symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r))).IsSymmetricBoundedBy
      1 (1 + 4 * r) := by
  refine isSymmetricBoundedBy_symmTridiagonalToeplitz_of_mem_Icc (-r) (1 + 2 * r) fun k => ?_
  have h1 := Real.neg_one_le_cos ((((k : ℕ) : ℝ) + 1) * π / ((N + 1 : ℕ) + 1))
  have h2 := Real.cos_le_one ((((k : ℕ) : ℝ) + 1) * π / ((N + 1 : ℕ) + 1))
  constructor <;> nlinarith

/-- **`‖Q₁⁻¹‖_∞ ≤ 1` by diagonal dominance** (Example 6.3.4): if `Q₁ y = x` then, at every
index, `(1 + 2r) |y_i| ≤ |x_i| + 2r ‖y‖_∞`, so `‖y‖_∞ ≤ ‖x‖_∞`. -/
private theorem norm_mulVec_inv_backward_le {r : ℝ} (hr0 : 0 ≤ r) (x : Fin (N + 1) → ℝ) :
    ‖(symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r))⁻¹ *ᵥ x‖ ≤ ‖x‖ := by
  set y := (symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r))⁻¹ *ᵥ x with hy
  have hQy : symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r) *ᵥ y = x := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_backward hr0)), Matrix.one_mulVec]
  have hyi : ∀ j, |y j| ≤ ‖y‖ := fun j => (Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm y j)
  have hxi : ∀ j, |x j| ≤ ‖x‖ := fun j => (Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm x j)
  have h12 : (0 : ℝ) < 1 + 2 * r := by linarith
  have key : ‖y‖ ≤ (‖x‖ + 2 * r * ‖y‖) / (1 + 2 * r) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Real.norm_eq_abs, le_div_iff₀ h12]
    have hrow := congrFun hQy i
    rw [symmTridiagonalToeplitz_mulVec_apply'] at hrow
    have h1 : |if h : 0 < (i : ℕ) then -r * y ⟨i - 1, by omega⟩ else 0| ≤ r * ‖y‖ := by
      split_ifs
      · rw [abs_mul, abs_neg, abs_of_nonneg hr0]
        exact mul_le_mul_of_nonneg_left (hyi _) hr0
      · rw [abs_zero]; positivity
    have h2 : |if h : (i : ℕ) < N then -r * y ⟨i + 1, by omega⟩ else 0| ≤ r * ‖y‖ := by
      split_ifs
      · rw [abs_mul, abs_neg, abs_of_nonneg hr0]
        exact mul_le_mul_of_nonneg_left (hyi _) hr0
      · rw [abs_zero]; positivity
    have h3 : (1 + 2 * r) * y i = x i - (if h : 0 < (i : ℕ) then -r * y ⟨i - 1, by omega⟩ else 0)
        - (if h : (i : ℕ) < N then -r * y ⟨i + 1, by omega⟩ else 0) := by
      linarith
    calc |y i| * (1 + 2 * r) = |(1 + 2 * r) * y i| := by
          rw [abs_mul, abs_of_pos h12, mul_comm]
      _ ≤ |x i| + |if h : 0 < (i : ℕ) then -r * y ⟨i - 1, by omega⟩ else 0|
          + |if h : (i : ℕ) < N then -r * y ⟨i + 1, by omega⟩ else 0| := by
          rw [h3]
          exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ ‖x‖ + r * ‖y‖ + r * ‖y‖ := add_le_add (add_le_add (hxi i) h1) h2
      _ = ‖x‖ + 2 * r * ‖y‖ := by ring
  rw [le_div_iff₀ h12] at key
  linarith

/-- **`‖Q₁⁻¹‖₂ ≤ 1`** (Example 6.3.4): the eigenvalues of `Q₁` are at least `1`. -/
private theorem norm_toEuclideanCLM_inv_backward_le {r : ℝ} (hr0 : 0 ≤ r) :
    ‖toEuclideanCLM (𝕜 := ℝ) (symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r))⁻¹‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  rw [one_mul]
  have hb := (isSymmetricBoundedBy_backward (N := N) hr0).isCoerciveWith.norm_le_norm_apply
    (toEuclideanLin (symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r))⁻¹ z)
  rw [one_mul, toEuclideanLin_mul_nonsing_inv_apply (isUnit_backward hr0)] at hb
  exact hb

/-- The local truncation error `τ̄^m` of the backward scheme, defined by the implicit relation
`Q₁ u^{m+1} = u^m + h_t f^{m+1} + h_t τ̄^m` (Example 6.3.4). -/
private noncomputable def backwardTrunc (N : ℕ) (u f : ℝ × ℝ → ℝ) (hx ht r : ℝ) (m : ℕ) :
    Fin (N + 1) → ℝ :=
  ht⁻¹ • (symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r) *ᵥ gridValues N u hx ht (m + 1)
    - gridValues N u hx ht m - ht • gridValues N f hx ht (m + 1))

include hT hNt hht in
private theorem mulVec_gridValues_succ_backward (u f : ℝ × ℝ → ℝ) (m : ℕ) :
    symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r) *ᵥ gridValues N u hx ht (m + 1)
      = gridValues N u hx ht m + ht • gridValues N f hx ht (m + 1)
        + ht • backwardTrunc N u f hx ht r m := by
  have hht0 : ht ≠ 0 := by rw [hht]; positivity
  rw [backwardTrunc, smul_smul, mul_inv_cancel₀ hht0, one_smul]
  abel

include hν hT hNt hhx hht hr in
/-- **The truncation error of the backward scheme** (Example 6.3.4): by Taylor expansion at
`(x_j, t_{m+1})`, `|τ̄^m_j| ≤ (M_tt / 2) h_t + (ν M_xxxx / 12) h_x² ≤ c (h_x² + h_t)` with
`c = M_tt / 2 + ν M_xxxx / 12`, for `m < N_t`. -/
private theorem abs_backwardTrunc_le (hu : IsRegularHeatSolution ν T f u ux ut Mtt Mxxxx)
    {m : ℕ} (hm : m < Nt) (j : Fin (N + 1)) :
    |backwardTrunc N u f hx ht r m j| ≤ (Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht) := by
  have hN2 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hhx0 : 0 < hx := by rw [hhx]; positivity
  have hht0 : 0 < ht := by rw [hht]; positivity
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hMtt : 0 ≤ Mtt := (abs_nonneg _).trans (hu.abs_ut_two_le 0 (left_mem_Icc.2 Real.pi_pos.le)
    0 (left_mem_Icc.2 hT.le))
  have hMx : 0 ≤ Mxxxx := (abs_nonneg _).trans (hu.abs_ux_four_le 0
    (left_mem_Icc.2 Real.pi_pos.le) 0 (left_mem_Icc.2 hT.le))
  set x : ℝ := ((j : ℕ) + 1) * hx with hxdef
  set t : ℝ := m * ht with htdef
  have hxmem : x ∈ Icc (0 : ℝ) π := by
    refine ⟨by positivity, ?_⟩
    rw [hxdef, hhx]
    have : ((j : ℕ) : ℝ) + 1 ≤ (N : ℝ) + 2 := by
      have := j.isLt
      exact_mod_cast (by omega : (j : ℕ) + 1 ≤ N + 2)
    calc ((j : ℕ) + 1) * (π / (N + 2)) ≤ ((N : ℝ) + 2) * (π / (N + 2)) :=
        mul_le_mul_of_nonneg_right this (by positivity)
      _ = π := by field_simp
  have hxl : x - hx ∈ Icc (0 : ℝ) π := by
    refine ⟨by rw [hxdef]; nlinarith, by linarith [hxmem.2]⟩
  have hxr : x + hx ∈ Icc (0 : ℝ) π := by
    refine ⟨by linarith [hxmem.1], ?_⟩
    rw [hxdef, hhx]
    have : ((j : ℕ) : ℝ) + 2 ≤ (N : ℝ) + 2 := by
      have := j.isLt
      exact_mod_cast (by omega : (j : ℕ) + 2 ≤ N + 2)
    calc ((j : ℕ) + 1) * (π / (N + 2)) + π / (N + 2) = ((j : ℕ) + 2) * (π / (N + 2)) := by ring
      _ ≤ ((N : ℝ) + 2) * (π / (N + 2)) :=
        mul_le_mul_of_nonneg_right this (by positivity)
      _ = π := by field_simp
  have htmem : t ∈ Icc (0 : ℝ) T := by
    refine ⟨by positivity, ?_⟩
    rw [htdef, hht]
    have : (m : ℝ) ≤ Nt := by exact_mod_cast hm.le
    calc (m : ℝ) * (T / Nt) ≤ Nt * (T / Nt) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = T := by field_simp
  have htk : t + ht ≤ T := by
    rw [htdef, hht]
    have : (m : ℝ) + 1 ≤ Nt := by exact_mod_cast hm
    calc (m : ℝ) * (T / Nt) + T / Nt = ((m : ℝ) + 1) * (T / Nt) := by ring
      _ ≤ Nt * (T / Nt) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = T := by field_simp
  have ht'mem : t + ht ∈ Icc (0 : ℝ) T := ⟨by positivity, htk⟩
  have e2 : (((m + 1 : ℕ) : ℝ)) * ht = t + ht := by push_cast; ring
  -- the boundary values at the level `m + 1`
  have hb0 : u (0, ((m + 1 : ℕ) : ℝ) * ht) = 0 := by rw [e2]; exact hu.left _ ht'mem
  have hbπ : u (π, ((m + 1 : ℕ) : ℝ) * ht) = 0 := by rw [e2]; exact hu.right _ ht'mem
  have hrow := symmTridiagonalToeplitz_mulVec_gridValues (u := u) (ht := ht) hhx (-r) (1 + 2 * r)
    (m + 1) hb0 hbπ j
  -- the identity `h_t τ̄ = A - r B`, at the level `m + 1`
  have hτ : ht * backwardTrunc N u f hx ht r m j
      = (u (x, t + ht) - u (x, t) - ht * ut 1 (x, t + ht))
        - r * (u (x + hx, t + ht) - 2 * u (x, t + ht) + u (x - hx, t + ht)
          - hx ^ 2 * ux 2 (x, t + ht)) := by
    have heq := hu.equation x hxmem (t + ht) ht'mem
    have hrhx : r * hx ^ 2 = ν * ht := by
      rw [hr, div_mul_cancel₀ _ (pow_ne_zero 2 hhx0.ne')]
    simp only [backwardTrunc, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hrow, gridValues_apply]
    rw [mul_inv_cancel_left₀ hht0.ne', heq]
    have e1 : (((j : ℕ) : ℝ) + 1) * hx = x := rfl
    have e3 : ((j : ℕ) : ℝ) * hx = x - hx := by rw [hxdef]; ring
    have e4 : (((j : ℕ) : ℝ) + 2) * hx = x + hx := by rw [hxdef]; ring
    rw [e1, e2, e3, e4]
    linear_combination (-(ux 2 (x, t + ht))) * hrhx
  have hA := hu.abs_sub_backward_time_le hxmem htmem hht0.le htk
  have hB := hu.abs_centred_sub_le hxl hxr hhx0.le ht'mem
  have hbound : |ht * backwardTrunc N u f hx ht r m j|
      ≤ ht * ((Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht)) := by
    rw [hτ]
    have hrhx4 : r * hx ^ 4 = ν * ht * hx ^ 2 := by
      rw [hr]; field_simp
    calc |u (x, t + ht) - u (x, t) - ht * ut 1 (x, t + ht)
          - r * (u (x + hx, t + ht) - 2 * u (x, t + ht) + u (x - hx, t + ht)
            - hx ^ 2 * ux 2 (x, t + ht))|
        ≤ Mtt * ht ^ 2 / 2 + r * (Mxxxx * hx ^ 4 / 12) := by
          refine (abs_sub _ _).trans (add_le_add hA ?_)
          rw [abs_mul, abs_of_nonneg hr0]
          exact mul_le_mul_of_nonneg_left hB hr0
      _ = ht * (Mtt / 2 * ht + ν * Mxxxx / 12 * hx ^ 2) := by
          rw [show r * (Mxxxx * hx ^ 4 / 12) = (r * hx ^ 4) * Mxxxx / 12 by ring, hrhx4]; ring
      _ ≤ ht * ((Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht)) := by
          refine mul_le_mul_of_nonneg_left ?_ hht0.le
          nlinarith [mul_nonneg hMtt (sq_nonneg hx), mul_nonneg (mul_nonneg hν.le hMx) hht0.le]
  rw [abs_mul, abs_of_pos hht0] at hbound
  exact le_of_mul_le_mul_left hbound hht0

/-- **Example 6.3.4, the maximum norm**: for the backward scheme (6.1.12)–(6.1.14) for
`u_t = ν u_xx + f`, with no condition on `r = ν h_t / h_x²`, and an exact solution with `u_tt`,
`u_xxxx` continuous on `[0, π] × [0, T]` (`IsRegularHeatSolution`, with the bounds `M_tt`,
`M_xxxx`), the error at every time level `m ≤ N_t` satisfies

  `max_j |u (x_j, t_m) - v^m_j| ≤ (M_tt / 2 + ν M_xxxx / 12) T (h_x² + h_t)`.

The scheme is the implicit relation `Q₁ v^{m+1} = v^m + h_t f^{m+1}` with
`Q₁ = tridiag(-r, 1 + 2r, -r)`, which is the two-level scheme with `Q = Q₁⁻¹` and
`g^m = Q f^{m+1}`; diagonal dominance gives `‖Q‖_∞ ≤ 1`, so the scheme is unconditionally
stable with `M₀ = 1`, and its truncation error `τ^m = Q τ̄^m` satisfies `‖τ^m‖_∞ ≤ ‖τ̄^m‖_∞`
with `τ̄^m` bounded by Taylor expansion at `(x_j, t_{m+1})`. As in `example_6_3_3` the horizon
is cut at `N_t`. -/
theorem example_6_3_4 (hν : 0 < ν) (hT : 0 < T) {N Nt : ℕ} (hNt : 0 < Nt) {hx ht r : ℝ}
    (hhx : hx = π / (N + 2)) (hht : ht = T / Nt) (hr : r = ν * ht / hx ^ 2)
    (hu : IsRegularHeatSolution ν T f u ux ut Mtt Mxxxx) {v : ℕ → Fin (N + 1) → ℝ}
    (hv0 : v 0 = gridValues N u hx ht 0)
    (hv : ∀ m, symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r) *ᵥ v (m + 1)
      = v m + ht • gridValues N f hx ht (m + 1))
    {m : ℕ} (hm : m ≤ Nt) :
    ‖gridValues N u hx ht m - v m‖ ≤ (Mtt / 2 + ν * Mxxxx / 12) * T * (hx ^ 2 + ht) := by
  have hhx0 : 0 < hx := by rw [hhx]; positivity
  have hht0 : 0 < ht := by rw [hht]; positivity
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hMtt : 0 ≤ Mtt := (abs_nonneg _).trans (hu.abs_ut_two_le 0 (left_mem_Icc.2 Real.pi_pos.le)
    0 (left_mem_Icc.2 hT.le))
  have hMx : 0 ≤ Mxxxx := (abs_nonneg _).trans (hu.abs_ux_four_le 0
    (left_mem_Icc.2 Real.pi_pos.le) 0 (left_mem_Icc.2 hT.le))
  set Q₁ := symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r) with hQ₁
  have hunit := isUnit_backward (N := N) hr0
  have hdet : IsUnit Q₁.det := (Matrix.isUnit_iff_isUnit_det _).1 hunit
  have hinv : ∀ w : Fin (N + 1) → ℝ, Q₁⁻¹ *ᵥ (Q₁ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  set Q := toLinfty Q₁⁻¹ with hQ
  have hQ1 : ‖Q‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
    rw [one_mul, hQ, toLinfty_apply]
    exact norm_mulVec_inv_backward_le hr0 w
  set c := (Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht) with hc
  have hc0 : 0 ≤ c := by positivity
  have h := FiniteDifference.norm_sub_le_of_stable (Q := Q) (u := gridValues N u hx ht) (v := v)
    (g := fun k => Q₁⁻¹ *ᵥ gridValues N f hx ht (k + 1))
    (τ := fun k => Q₁⁻¹ *ᵥ backwardTrunc N u f hx ht r k) (h := ht) (T := T) (M₀ := 1)
    (N := Nt) hht0.le hc0 (le_of_eq (by rw [hht]; field_simp))
    (fun k _ => by
      rw [hQ, toLinfty_apply, ← Matrix.mulVec_smul, ← Matrix.mulVec_add, ← hv k, hinv])
    (fun k _ => by
      rw [hQ, toLinfty_apply, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_add,
        ← Matrix.mulVec_add, ← mulVec_gridValues_succ_backward hT hNt hht u f k, hinv])
    hv0.symm (fun k _ => norm_pow_le_one hQ1 k)
    (fun k hk => (norm_mulVec_inv_backward_le hr0 _).trans
      ((pi_norm_le_iff_of_nonneg hc0).2 fun j => by
        rw [Real.norm_eq_abs]
        exact abs_backwardTrunc_le hν hT hNt hhx hht hr hu hk j)) hm
  calc ‖gridValues N u hx ht m - v m‖ ≤ 1 * T * c := h
    _ = (Mtt / 2 + ν * Mxxxx / 12) * T * (hx ^ 2 + ht) := by rw [hc]; ring

/-- **Example 6.3.4, the discrete weighted `2`-norm**: under the hypotheses of `example_6_3_4`,
also `√h_x ‖u^m - v^m‖₂ ≤ √π (M_tt / 2 + ν M_xxxx / 12) T (h_x² + h_t)` for `m ≤ N_t`. The
eigenvalues `1 + 4r cos²(jπ / (2 N_x))` of `Q₁` (Exercise 6.3.1) are at least `1`, so the
eigenvalues of `Q = Q₁⁻¹` lie in `(0, 1]` and `‖Q‖₂ ≤ 1`: the scheme is unconditionally stable in
`‖·‖_{2, h_x}` too, and `‖τ^m‖₂ ≤ ‖τ̄^m‖₂`. -/
theorem example_6_3_4_l2 (hν : 0 < ν) (hT : 0 < T) {N Nt : ℕ} (hNt : 0 < Nt) {hx ht r : ℝ}
    (hhx : hx = π / (N + 2)) (hht : ht = T / Nt) (hr : r = ν * ht / hx ^ 2)
    (hu : IsRegularHeatSolution ν T f u ux ut Mtt Mxxxx) {v : ℕ → Fin (N + 1) → ℝ}
    (hv0 : v 0 = gridValues N u hx ht 0)
    (hv : ∀ m, symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r) *ᵥ v (m + 1)
      = v m + ht • gridValues N f hx ht (m + 1))
    {m : ℕ} (hm : m ≤ Nt) :
    Real.sqrt (hx * ∑ j, (gridValues N u hx ht m j - v m j) ^ 2)
      ≤ Real.sqrt π * ((Mtt / 2 + ν * Mxxxx / 12) * T * (hx ^ 2 + ht)) := by
  have hhx0 : 0 < hx := by rw [hhx]; positivity
  have hht0 : 0 < ht := by rw [hht]; positivity
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hMtt : 0 ≤ Mtt := (abs_nonneg _).trans (hu.abs_ut_two_le 0 (left_mem_Icc.2 Real.pi_pos.le)
    0 (left_mem_Icc.2 hT.le))
  have hMx : 0 ≤ Mxxxx := (abs_nonneg _).trans (hu.abs_ux_four_le 0
    (left_mem_Icc.2 Real.pi_pos.le) 0 (left_mem_Icc.2 hT.le))
  set Q₁ := symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r) with hQ₁
  have hunit := isUnit_backward (N := N) hr0
  have hdet : IsUnit Q₁.det := (Matrix.isUnit_iff_isUnit_det _).1 hunit
  have hinv : ∀ w : Fin (N + 1) → ℝ, Q₁⁻¹ *ᵥ (Q₁ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  set Q : EuclideanSpace ℝ (Fin (N + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (N + 1)) :=
    toEuclideanCLM (𝕜 := ℝ) Q₁⁻¹ with hQ
  have hQ1 : ‖Q‖ ≤ 1 := norm_toEuclideanCLM_inv_backward_le hr0
  set c := (Mtt / 2 + ν * Mxxxx / 12) * (hx ^ 2 + ht) with hc
  have hc0 : 0 ≤ c := by positivity
  have hδ : 0 ≤ Real.sqrt ((N : ℝ) + 1) * c := by positivity
  have h := FiniteDifference.norm_sub_le_of_stable (Q := Q)
    (u := fun k => WithLp.toLp 2 (gridValues N u hx ht k))
    (v := fun k => WithLp.toLp 2 (v k))
    (g := fun k => WithLp.toLp 2 (Q₁⁻¹ *ᵥ gridValues N f hx ht (k + 1)))
    (τ := fun k => WithLp.toLp 2 (Q₁⁻¹ *ᵥ backwardTrunc N u f hx ht r k)) (h := ht) (T := T)
    (M₀ := 1) (N := Nt) hht0.le hδ (le_of_eq (by rw [hht]; field_simp))
    (fun k _ => by
      rw [hQ, toEuclideanCLM_toLp, ← WithLp.toLp_smul, ← WithLp.toLp_add, ← Matrix.mulVec_smul,
        ← Matrix.mulVec_add, ← hv k, hinv])
    (fun k _ => by
      rw [hQ, toEuclideanCLM_toLp, ← WithLp.toLp_smul, ← WithLp.toLp_smul, ← WithLp.toLp_add,
        ← WithLp.toLp_add, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_add,
        ← Matrix.mulVec_add, ← mulVec_gridValues_succ_backward hT hNt hht u f k, hinv])
    (by rw [hv0]) (fun k _ => norm_pow_le_one hQ1 k)
    (fun k hk => by
      have h1 : ‖(WithLp.toLp 2 (Q₁⁻¹ *ᵥ backwardTrunc N u f hx ht r k) :
          EuclideanSpace ℝ (Fin (N + 1)))‖
          ≤ ‖(WithLp.toLp 2 (backwardTrunc N u f hx ht r k) : EuclideanSpace ℝ (Fin (N + 1)))‖ := by
        have := Q.le_opNorm (WithLp.toLp 2 (backwardTrunc N u f hx ht r k))
        rw [hQ, toEuclideanCLM_toLp] at this
        exact this.trans (by nlinarith [norm_nonneg (WithLp.toLp 2 (backwardTrunc N u f hx ht r k) :
          EuclideanSpace ℝ (Fin (N + 1)))])
      exact h1.trans (norm_toLp_le _ hc0 fun j =>
        abs_backwardTrunc_le hν hT hNt hhx hht hr hu hk j)) hm
  rw [← WithLp.toLp_sub, one_mul, ← mul_assoc] at h
  have key := sqrt_mul_sum_sq_le hhx (gridValues N u hx ht m - v m) (C := T * c) (by positivity)
    (h.trans (le_of_eq (by ring)))
  simp only [Pi.sub_apply] at key
  refine key.trans (le_of_eq ?_)
  rw [hc]; ring

end Backward

/-! #### The sine-series solutions of Example 6.2.4 satisfy the hypotheses -/

section SineSeries

/-- **The sine-series solutions have the regularity of Examples 6.3.3–6.3.4**: for
`u (x, t) = ∑_{j < n} b j exp (-ν (j + 1)² t) sin ((j + 1) x)` (Example 6.2.4, (6.2.7)), which
solves the homogeneous equation `u_t = ν u_xx` with `u (0, t) = u (π, t) = 0`, the derivative
towers are `Heat.sineSeriesDerivX` and `Heat.sineSeriesDerivT`, and
`|u_tt| ≤ ∑ |b j| (ν (j + 1)²)²`, `|u_xxxx| ≤ ∑ |b j| (j + 1)⁴` on `[0, π] × [0, T]`. -/
theorem sineSeries_isRegularHeatSolution (hν : 0 < ν) (T : ℝ) (n : ℕ) (b : ℕ → ℝ) :
    IsRegularHeatSolution ν T 0 (Heat.sineSeries ν n b) (Heat.sineSeriesDerivX ν n b)
      (Heat.sineSeriesDerivT ν n b) (∑ j ∈ Finset.range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2)
      (∑ j ∈ Finset.range n, |b j| * ((j : ℝ) + 1) ^ 4) where
  ux_zero := Heat.sineSeriesDerivX_zero
  ut_zero := Heat.sineSeriesDerivT_zero
  hasDerivWithinAt_ux m _ t _ x _ := (Heat.hasDerivAt_sineSeriesDerivX m x t).hasDerivWithinAt
  hasDerivWithinAt_ut m _ x _ t _ := (Heat.hasDerivAt_sineSeriesDerivT m x t).hasDerivWithinAt
  abs_ut_two_le x _ t ht := Heat.abs_sineSeriesDerivT_le hν.le 2 (p := (x, t)) ht.1
  abs_ux_four_le x _ t ht := Heat.abs_sineSeriesDerivX_le hν.le 4 (p := (x, t)) ht.1
  equation x _ t _ := by rw [Heat.sineSeriesDerivT_one, Pi.zero_apply, add_zero]
  left t _ := Heat.sineSeries_zero_left t
  right t _ := Heat.sineSeries_pi_left t

/-- **Example 6.3.3 for the sine-series solutions** of Example 6.2.4, in both norms: the
hypotheses on `u_tt` and `u_xxxx` are discharged by `sineSeries_isRegularHeatSolution`, with
`M_tt = ∑ |b j| (ν (j + 1)²)²` and `M_xxxx = ∑ |b j| (j + 1)⁴`. -/
theorem example_6_3_3_sineSeries (hν : 0 < ν) (hT : 0 < T) {N Nt : ℕ} (hNt : 0 < Nt)
    {hx ht r : ℝ} (hhx : hx = π / (N + 2)) (hht : ht = T / Nt) (hr : r = ν * ht / hx ^ 2)
    (hr2 : r ≤ 1 / 2) (n : ℕ) (b : ℕ → ℝ) {v : ℕ → Fin (N + 1) → ℝ}
    (hv0 : v 0 = gridValues N (Heat.sineSeries ν n b) hx ht 0)
    (hv : ∀ m, v (m + 1) = symmTridiagonalToeplitz (N + 1) r (1 - 2 * r) *ᵥ v m)
    {m : ℕ} (hm : m ≤ Nt) :
    ‖gridValues N (Heat.sineSeries ν n b) hx ht m - v m‖
        ≤ ((∑ j ∈ Finset.range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2) / 2
          + ν * (∑ j ∈ Finset.range n, |b j| * ((j : ℝ) + 1) ^ 4) / 12) * T * (hx ^ 2 + ht) ∧
      Real.sqrt (hx * ∑ j, (gridValues N (Heat.sineSeries ν n b) hx ht m j - v m j) ^ 2)
        ≤ Real.sqrt π * (((∑ j ∈ Finset.range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2) / 2
          + ν * (∑ j ∈ Finset.range n, |b j| * ((j : ℝ) + 1) ^ 4) / 12) * T * (hx ^ 2 + ht)) := by
  have hv' : ∀ m, v (m + 1) = symmTridiagonalToeplitz (N + 1) r (1 - 2 * r) *ᵥ v m
      + ht • gridValues N (0 : ℝ × ℝ → ℝ) hx ht m := fun m => by
    have : gridValues N (0 : ℝ × ℝ → ℝ) hx ht m = 0 := by funext j; rfl
    rw [hv m, this, smul_zero, add_zero]
  exact ⟨example_6_3_3 hν hT hNt hhx hht hr hr2 (sineSeries_isRegularHeatSolution hν T n b) hv0 hv'
    hm, example_6_3_3_l2 hν hT hNt hhx hht hr hr2 (sineSeries_isRegularHeatSolution hν T n b) hv0
    hv' hm⟩

/-- **Example 6.3.4 for the sine-series solutions** of Example 6.2.4, in both norms. -/
theorem example_6_3_4_sineSeries (hν : 0 < ν) (hT : 0 < T) {N Nt : ℕ} (hNt : 0 < Nt)
    {hx ht r : ℝ} (hhx : hx = π / (N + 2)) (hht : ht = T / Nt) (hr : r = ν * ht / hx ^ 2)
    (n : ℕ) (b : ℕ → ℝ) {v : ℕ → Fin (N + 1) → ℝ}
    (hv0 : v 0 = gridValues N (Heat.sineSeries ν n b) hx ht 0)
    (hv : ∀ m, symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r) *ᵥ v (m + 1) = v m)
    {m : ℕ} (hm : m ≤ Nt) :
    ‖gridValues N (Heat.sineSeries ν n b) hx ht m - v m‖
        ≤ ((∑ j ∈ Finset.range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2) / 2
          + ν * (∑ j ∈ Finset.range n, |b j| * ((j : ℝ) + 1) ^ 4) / 12) * T * (hx ^ 2 + ht) ∧
      Real.sqrt (hx * ∑ j, (gridValues N (Heat.sineSeries ν n b) hx ht m j - v m j) ^ 2)
        ≤ Real.sqrt π * (((∑ j ∈ Finset.range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2) / 2
          + ν * (∑ j ∈ Finset.range n, |b j| * ((j : ℝ) + 1) ^ 4) / 12) * T * (hx ^ 2 + ht)) := by
  have hv' : ∀ m, symmTridiagonalToeplitz (N + 1) (-r) (1 + 2 * r) *ᵥ v (m + 1)
      = v m + ht • gridValues N (0 : ℝ × ℝ → ℝ) hx ht (m + 1) := fun m => by
    have : gridValues N (0 : ℝ × ℝ → ℝ) hx ht (m + 1) = 0 := by funext j; rfl
    rw [hv m, this, smul_zero, add_zero]
  exact ⟨example_6_3_4 hν hT hNt hhx hht hr (sineSeries_isRegularHeatSolution hν T n b) hv0 hv' hm,
    example_6_3_4_l2 hν hT hNt hhx hht hr (sineSeries_isRegularHeatSolution hν T n b) hv0 hv' hm⟩

end SineSeries

end HeatSchemes

end AtkinsonHan.Chapter06
