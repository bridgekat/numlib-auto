import Numlib.FiniteDifference.TwoLevel

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
constants, `FiniteDifference.norm_sub_le_of_stable`, together with two limits.

The book works in `ℝ^{N_x - 1}` and leaves the norm on it unspecified, saying that it will be
chosen per example — the two worked examples use the maximum norm and a scaled discrete two-norm
on the same space and get different stability conditions.  The surface therefore takes an
arbitrary real normed space, which is more faithful than fixing `EuclideanSpace ℝ (Fin (N_x - 1))`,
not less.  The truncation error `τ^m` is data of the statement, defined by the relation (6.3.6)
that the exact values satisfy, rather than a derived quantity.

Examples 6.3.3 and 6.3.4 (the forward and backward schemes for the heat equation, in the maximum
norm and in the discrete two-norm) and Exercises 6.3.1–6.3.3 are not formalized: they are Taylor
expansions of a solution assumed smooth together with the eigenvalues of a tridiagonal Toeplitz
matrix, and they exercise nothing in the theory above.
-/

open Filter Set

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

/-- **Theorem 6.3.2.**  A consistent and stable family of two-level schemes is convergent, and its
error inside the horizon obeys `sup_{m h_t ≤ T} ‖u^m - v^m‖ ≤ M₀ T sup_{m h_t ≤ T} ‖τ^m‖`; if the
family is moreover of order `(p₁, p₂)` with constant `c` then the error is at most
`M₀ T c (h_x^{p₁} + h_t^{p₂})`.

The exact values `u` and the computed values `v` obey the same two-level recursion, the exact ones
carrying the local truncation error `h_t τ^m` of (6.3.6), and they start from the same value. -/
theorem theorem_6_3_2 {l : Filter ι} (hT : 0 ≤ T) (hht : ∀ i, 0 ≤ ht i)
    (hv : ∀ (i : ι) (m : ℕ), v i (m + 1) = Q i (v i m) + ht i • g i m)
    (hu : ∀ (i : ι) (m : ℕ), u i (m + 1) = Q i (u i m) + ht i • g i m + ht i • τ i m)
    (h0 : ∀ i : ι, u i 0 = v i 0) (hstab : IsStableScheme ht Q T M₀)
    (hcons : IsConsistentScheme l ht τ T) :
    IsConvergentScheme l ht u v T ∧
      ∀ (c : ℝ) (p₁ p₂ : ℕ), IsSchemeOfOrder hx ht τ T c p₁ p₂ →
        ∀ (i : ι) (m : ℕ), (m : ℝ) * ht i ≤ T →
          ‖u i m - v i m‖ ≤ M₀ * T * (c * (hx i ^ p₁ + ht i ^ p₂)) := by
  constructor
  · intro ε hε
    have hM : (0 : ℝ) ≤ max M₀ 0 := le_max_right _ _
    have hMT : (0 : ℝ) ≤ max M₀ 0 * T := mul_nonneg hM hT
    have hden : (0 : ℝ) < max M₀ 0 * T + 1 := by linarith
    have hδpos : (0 : ℝ) < ε / (max M₀ 0 * T + 1) := div_pos hε hden
    filter_upwards [hcons _ hδpos] with i hi
    intro m hm
    calc ‖u i m - v i m‖ ≤ M₀ * T * (ε / (max M₀ 0 * T + 1)) :=
          error_le hht hv hu h0 hstab i hδpos.le hi hm
      _ ≤ max M₀ 0 * T * (ε / (max M₀ 0 * T + 1)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hT) hδpos.le
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ hden]
          nlinarith [hε.le]
  · intro c p₁ p₂ hord i m hm
    have hδ0 : 0 ≤ c * (hx i ^ p₁ + ht i ^ p₂) :=
      le_trans (norm_nonneg _) (hord i 0 (by simpa using hT))
    exact error_le hht hv hu h0 hstab i hδ0 (fun k hk => hord i k hk) hm

end Theorem632

end AtkinsonHan.Chapter06
