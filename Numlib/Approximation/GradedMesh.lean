import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Numlib.Approximation.Interpolation

/-!
# Graded meshes for piecewise polynomial interpolation

Piecewise polynomial interpolation of degree `m` on a *uniform* mesh of `n` panels converges at the
rate `n^{-(m+1)}` only for a function whose `(m+1)`-st derivative is bounded.  A function that is
merely Hölder continuous of exponent `γ ∈ (0, 1)` at an endpoint of the interval, smooth inside, and
whose `(m+1)`-st derivative blows up there no faster than `(x - a)^{γ - (m+1)}` — Rice's class
`(γ, m + 1)`, the regularity a weakly singular integral equation produces — loses that rate, and
recovers it on a mesh *graded* towards the endpoint:

`x_j = a + (j/n)^q (b - a)`,   `q ≥ (m + 1)/γ`.

The grading is exactly strong enough: the panel `[x_j, x_{j+1}]` has length `𝒪(j^{q-1} n^{-q})` by
the mean value theorem, the singular factor `(x_j - a)^{γ-(m+1)}` is `(j/n)^{q(γ-m-1)}`, and the
powers of `j` in the product `h_j^{m+1} (x_j - a)^{γ-(m+1)}` combine into `(j/n)^{qγ-(m+1)} ≤ 1`
precisely when `q γ ≥ m + 1`.  The panel touching the singularity, where no derivative bound is
available, is handled by the Hölder condition alone, and `(x_1 - a)^γ = n^{-qγ} ≤ n^{-(m+1)}` is
the same inequality again.

Two meshes are treated: the one-sided mesh on `[0, 1]`, graded towards the origin, and the mesh on
`[a, b]` graded towards *both* endpoints, `x_j = a + (2j/n)^q (b-a)/2` on the left half and
`x_{n-j} = a + b - x_j` on the right, whose bound is stated with an explicit constant so that it
applies uniformly to a family of functions sharing the same Hölder and derivative constants.

## Main statements

* `isPanelNodes_graded` — the graded mesh on `[0, 1]` together with nodes placed at fixed fractions
  `0 = μ_0 < ⋯ < μ_m = 1` of every panel is a panel node system in the sense of
  `IsPanelNodes`.
* `norm_sub_piecewisePolyInterpCLM_le_graded` — **the graded-mesh interpolation error**
  `‖u - P_n u‖_∞ ≤ C n^{-(m+1)}` for a function of Rice's class `(γ, m + 1)` at the origin, with
  `C` independent of `n`.
* `isPanelNodes_gradedSym`, `sub_le_gradedSym` and
  `norm_sub_piecewisePolyInterpCLM_le_gradedSym` — the same two statements for the mesh graded
  towards both endpoints of `[a, b]`, the last with an explicit constant, together with the bound
  `(b - a) q / (2 r)` on the width of a panel of that mesh, which is what makes the interpolants
  converge for a merely continuous function.

## References

The mesh and the error bound are due to John R. Rice, *On the degree of convergence of nonlinear
spline approximation*, in *Approximations with Special Emphasis on Spline Functions*, Academic
Press, 1969, 349–365.  Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A
Functional Analysis Framework*, 3rd edition, Springer, 2009 ([han2009theoretical]) state the
one-sided bound as their Lemma 12.5.5, equations (12.5.30)–(12.5.35), and the two-sided mesh in the
paragraph preceding their Theorem 12.5.6; both without proof.

## Implementation notes

The helper estimates on one panel are private: they are stated in the normalized variable `j/n`
rather than in the mesh points themselves, which is convenient for the proofs and useless outside
them.  So are the two elementary bounds on `A^q - B^q` for `q ≥ 1` that drive them — the mean value
bound, and its weakening which trades the sharp factor for one that survives at `B = 0`, where the
mean value theorem gives nothing.
-/

/-! ### Two bounds on a real power

Both compare `A ^ q - B ^ q` with `A - B` for an exponent `q ≥ 1`.  The first is the mean value
theorem; the second trades the sharp factor `q A^{q-1}` for the cruder `q`, and in exchange holds
also at `B = 0`, where `y ↦ y ^ q` is not differentiable for `q < 1` and where the panel of a
graded mesh that touches the singularity lives. -/

namespace Real

/-- **The mean value bound for a real power**: for `q ≥ 1` and `0 < B < A`,
`A ^ q - B ^ q ≤ q A ^ (q - 1) (A - B)`.

The hypothesis `0 < B` is what makes `y ↦ y ^ q` differentiable on `[B, A]`; see
`Real.rpow_sub_rpow_le_mul_sub` for a cruder bound that survives at `B = 0`. -/
private theorem rpow_sub_rpow_le {A B q : ℝ} (hq : 1 ≤ q) (hB : 0 < B) (hBA : B < A) :
    A ^ q - B ^ q ≤ q * A ^ (q - 1) * (A - B) := by
  have hderiv : ∀ s ∈ Set.Icc B A, HasDerivAt (fun y : ℝ => y ^ q) (q * s ^ (q - 1)) s :=
    fun s _ => hasDerivAt_rpow_const (Or.inr hq)
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun y : ℝ => y ^ q)
    (fun s => q * s ^ (q - 1)) hBA
    (fun s hs => (hderiv s hs).continuousAt.continuousWithinAt)
    (fun s hs => hderiv s (Set.Ioo_subset_Icc_self hs))
  have hsub : (0 : ℝ) < A - B := by linarith
  have hξA : ξ ^ (q - 1) ≤ A ^ (q - 1) :=
    rpow_le_rpow (hB.trans hξ.1).le hξ.2.le (by linarith)
  rw [eq_div_iff (ne_of_gt hsub)] at hξeq
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hkey : 0 ≤ q * (A ^ (q - 1) - ξ ^ (q - 1)) * (A - B) :=
    mul_nonneg (mul_nonneg hq0 (by linarith)) hsub.le
  linarith [hkey, hξeq]

/-- **A bound on `A ^ q - B ^ q` valid down to `B = 0`**: for `q ≥ 1` and `0 ≤ B < A ≤ 1`,
`A ^ q - B ^ q ≤ q (A - B)`.

It is `Real.rpow_sub_rpow_le` with the sharp factor `A ^ (q - 1)` weakened to `1`, which costs
nothing when `A ≤ 1` and buys the degenerate case `B = 0`, where `y ↦ y ^ q` is not
differentiable. -/
private theorem rpow_sub_rpow_le_mul_sub {A B q : ℝ} (hq : 1 ≤ q) (hB : 0 ≤ B) (hBA : B < A)
    (hA1 : A ≤ 1) : A ^ q - B ^ q ≤ q * (A - B) := by
  have hA0 : 0 < A := lt_of_le_of_lt hB hBA
  rcases eq_or_lt_of_le hB with hB0 | hB0
  · have hzero : B ^ q = 0 := by rw [← hB0, zero_rpow (by linarith)]
    have h1 : A ^ q ≤ A := by
      calc A ^ q ≤ A ^ (1 : ℝ) := rpow_le_rpow_of_exponent_ge hA0 hA1 hq
        _ = A := rpow_one A
    rw [hzero, ← hB0]
    nlinarith
  · have h1 := rpow_sub_rpow_le hq hB0 hBA
    have h2 : A ^ (q - 1) ≤ 1 := rpow_le_one hA0.le hA1 (by linarith)
    have h3 : 0 ≤ q * (A - B) * (1 - A ^ (q - 1)) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    linarith [h1, h3]

end Real

/-! ### The graded mesh on `[0, 1]` -/

/-- **The graded-mesh panel estimate**, in the normalized variable.  On the mesh
`x_j = (j/n)^q`, if `q γ ≥ m + 1` then
`(x_{j+1} - x_j)^{m+1} x_j^{γ - (m+1)} ≤ (q 2^{q-1})^{m+1} n^{-(m+1)}` for every panel that does
not touch the origin.

This is where the grading pays for the singularity: the panel length is `𝒪(j^{q-1} n^{-q})` by the
mean value theorem, and the singular factor `x_j^{γ-(m+1)}` is `(j/n)^{q(γ-m-1)}`, so the powers of
`j` combine into `(j/n)^{qγ-(m+1)} ≤ 1` exactly when `q ≥ (m+1)/γ`. -/
private theorem graded_panel_le {m : ℕ} {γ q n A B : ℝ} (hq1 : 1 ≤ q)
    (hqγ : ((m : ℝ) + 1) ≤ q * γ) (hn0 : 0 < n) (hB0 : 0 < B) (hBA : B < A) (hA1 : A ≤ 1)
    (hAB : A - B = 1 / n) (hA2B : A ≤ 2 * B) :
    (A ^ q - B ^ q) ^ (m + 1) * ((B ^ q) ^ (γ - ((m : ℝ) + 1)))
      ≤ (q * 2 ^ (q - 1)) ^ (m + 1) / n ^ (m + 1) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hA0 : (0 : ℝ) < A := hB0.trans hBA
  have hB1 : B ≤ 1 := (hBA.le).trans hA1
  have hh0 : 0 ≤ A ^ q - B ^ q := by
    have := Real.rpow_le_rpow hB0.le hBA.le hq0.le
    linarith
  have hstep : A ^ q - B ^ q ≤ q * 2 ^ (q - 1) * B ^ (q - 1) / n := by
    have h2 : A ^ (q - 1) ≤ 2 ^ (q - 1) * B ^ (q - 1) := by
      rw [← Real.mul_rpow (by norm_num) hB0.le]
      exact Real.rpow_le_rpow hA0.le hA2B (by linarith)
    calc A ^ q - B ^ q ≤ q * A ^ (q - 1) * (A - B) := Real.rpow_sub_rpow_le hq1 hB0 hBA
      _ = q * A ^ (q - 1) / n := by rw [hAB]; ring
      _ ≤ q * (2 ^ (q - 1) * B ^ (q - 1)) / n := by gcongr
      _ = q * 2 ^ (q - 1) * B ^ (q - 1) / n := by ring
  have hpow : (A ^ q - B ^ q) ^ (m + 1)
      ≤ (q * 2 ^ (q - 1)) ^ (m + 1) * (B ^ (q - 1)) ^ (m + 1) / n ^ (m + 1) := by
    calc (A ^ q - B ^ q) ^ (m + 1) ≤ (q * 2 ^ (q - 1) * B ^ (q - 1) / n) ^ (m + 1) := by
          gcongr
      _ = (q * 2 ^ (q - 1)) ^ (m + 1) * (B ^ (q - 1)) ^ (m + 1) / n ^ (m + 1) := by
          rw [div_pow, mul_pow]
  have hBrpow : (B ^ (q - 1)) ^ (m + 1) * ((B ^ q) ^ (γ - ((m : ℝ) + 1)))
      = B ^ (q * γ - ((m : ℝ) + 1)) := by
    rw [← Real.rpow_natCast (B ^ (q - 1)) (m + 1), ← Real.rpow_mul hB0.le,
      ← Real.rpow_mul hB0.le, ← Real.rpow_add hB0]
    congr 1
    push_cast
    ring
  have hBle : B ^ (q * γ - ((m : ℝ) + 1)) ≤ 1 :=
    Real.rpow_le_one hB0.le hB1 (by linarith)
  have hfac0 : (0 : ℝ) ≤ (B ^ q) ^ (γ - ((m : ℝ) + 1)) := Real.rpow_nonneg (by positivity) _
  have hc0 : (0 : ℝ) ≤ (q * 2 ^ (q - 1)) ^ (m + 1) / n ^ (m + 1) := by positivity
  calc (A ^ q - B ^ q) ^ (m + 1) * ((B ^ q) ^ (γ - ((m : ℝ) + 1)))
      ≤ ((q * 2 ^ (q - 1)) ^ (m + 1) * (B ^ (q - 1)) ^ (m + 1) / n ^ (m + 1))
          * ((B ^ q) ^ (γ - ((m : ℝ) + 1))) := by
        exact mul_le_mul_of_nonneg_right hpow hfac0
    _ = (q * 2 ^ (q - 1)) ^ (m + 1) / n ^ (m + 1) * B ^ (q * γ - ((m : ℝ) + 1)) := by
        rw [← hBrpow]
        ring
    _ ≤ (q * 2 ^ (q - 1)) ^ (m + 1) / n ^ (m + 1) * 1 :=
        mul_le_mul_of_nonneg_left hBle hc0
    _ = (q * 2 ^ (q - 1)) ^ (m + 1) / n ^ (m + 1) := mul_one _

/-- **The graded mesh and its nodes form a panel node system.**  The mesh is Rice's
`x_j = (j/n)^q` on `[0, 1]` with `n = N + 1` panels, and the nodes of the panel `[x_j, x_{j+1}]`
are the images `x_{ji} = x_j + μ_i h_j` of a fixed partition `0 = μ_0 < ⋯ < μ_m = 1` of the unit
interval.  [han2009theoretical], §12.5, equations (12.5.30)-(12.5.32). -/
theorem isPanelNodes_graded {m N : ℕ} {q : ℝ} (hq1 : 1 ≤ q) {μ : Fin (m + 1) → ℝ}
    (hμ0 : μ 0 = 0) (hμ1 : μ (Fin.last m) = 1) (hμmono : StrictMono μ)
    {x : ℕ → Set.Icc (0 : ℝ) 1} {node : ℕ → Fin (m + 1) → Set.Icc (0 : ℝ) 1}
    (hx : ∀ j ≤ N + 1, (x j : ℝ) = ((j : ℝ) / ((N : ℝ) + 1)) ^ q)
    (hnode : ∀ j ≤ N, ∀ i, (node j i : ℝ)
      = (x j : ℝ) + μ i * ((x (j + 1) : ℝ) - (x j : ℝ))) :
    IsPanelNodes N m x node := by
  have hn0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
  have hstep : ∀ j ≤ N, (x j : ℝ) < (x (j + 1) : ℝ) := by
    intro j hj
    rw [hx j (by omega), hx (j + 1) (by omega)]
    refine Real.rpow_lt_rpow (by positivity) ?_ hq0
    push_cast
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    gcongr
    linarith
  have hμmem : ∀ i : Fin (m + 1), μ i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    constructor
    · rw [← hμ0]
      exact hμmono.monotone (Fin.zero_le i)
    · rw [← hμ1]
      exact hμmono.monotone (Fin.le_last i)
  refine ⟨hstep, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hx 0 (by omega), Nat.cast_zero, zero_div, Real.zero_rpow (ne_of_gt hq0)]
  · rw [hx (N + 1) (by omega)]
    push_cast
    rw [div_self (ne_of_gt hn0), Real.one_rpow]
  · intro j hj i
    have hd : (0 : ℝ) ≤ (x (j + 1) : ℝ) - (x j : ℝ) := sub_nonneg.mpr (hstep j hj).le
    rw [hnode j hj i]
    constructor <;> nlinarith [(hμmem i).1, (hμmem i).2]
  · intro j hj i i' hii
    simp only at hii
    have hd : (0 : ℝ) < (x (j + 1) : ℝ) - (x j : ℝ) := sub_pos.mpr (hstep j hj)
    rw [hnode j hj i, hnode j hj i'] at hii
    refine hμmono.injective (mul_right_cancel₀ (ne_of_gt hd) ?_)
    linarith
  · intro j hj
    refine Subtype.ext ?_
    rw [hnode j hj 0, hμ0]
    ring
  · intro j hj
    refine Subtype.ext ?_
    rw [hnode j hj (Fin.last m), hμ1]
    ring

/-- **Rice's graded-mesh interpolation error.**  For `0 < γ < 1` let `u` be of Rice's type
`(γ, m + 1)` on `[0, 1]` — Hölder continuous with exponent `γ`, of class `C^{m+1}` on `(0, 1]` and
with `|u^{(m+1)}(s)| ≤ c s^{γ - (m+1)}` — and let `P_n` be piecewise polynomial interpolation of
degree `m` on the graded mesh `x_j = (j/n)^q`, at nodes placed at fixed fractions
`0 = μ_0 < ⋯ < μ_m = 1` of each panel.  Then for `q ≥ (m + 1)/γ`,

`‖u - P_n u‖_∞ ≤ C n^{-(m+1)}`

with `C` independent of `n`.

On the first panel `[0, x_1]` only the Hölder bound is available, and `x_1^γ = n^{-qγ} ≤
n^{-(m+1)}` is exactly what `q γ ≥ m + 1` buys; on every later panel the Lagrange error formula
applies — `u` is smooth there — and the graded-mesh panel estimate makes
`h_j^{m+1} x_j^{γ-(m+1)}` uniformly `𝒪(n^{-(m+1)})`.  The Lebesgue constants of the panels are
bounded uniformly because the nodes sit at fixed fractions of every panel.

This is [han2009theoretical], §12.5, Lemma 12.5.5, equation (12.5.35), stated there without
proof. -/
theorem norm_sub_piecewisePolyInterpCLM_le_graded {m : ℕ} {γ q H c : ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1)
    (hq : ((m : ℝ) + 1) / γ ≤ q) {μ : Fin (m + 1) → ℝ}
    (hμ0 : μ 0 = 0) (hμ1 : μ (Fin.last m) = 1) (hμmono : StrictMono μ)
    {U : ℝ → ℝ} {u : C(Set.Icc (0 : ℝ) 1, ℝ)} (hu : ∀ t : Set.Icc (0 : ℝ) 1, u t = U ((t : ℝ)))
    (hH : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, |U s - U t| ≤ H * |s - t| ^ γ)
    (hUC : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) U (Set.Ioi 0))
    (hUd : ∀ s ∈ Set.Ioc (0 : ℝ) 1, |iteratedDeriv (m + 1) U s| ≤ c * s ^ (γ - ((m : ℝ) + 1)))
    {x : ℕ → ℕ → Set.Icc (0 : ℝ) 1} {node : ℕ → ℕ → Fin (m + 1) → Set.Icc (0 : ℝ) 1}
    (hx : ∀ N, ∀ j ≤ N + 1, (x N j : ℝ) = ((j : ℝ) / ((N : ℝ) + 1)) ^ q)
    (hnode : ∀ N, ∀ j ≤ N, ∀ i, (node N j i : ℝ)
      = (x N j : ℝ) + μ i * ((x N (j + 1) : ℝ) - (x N j : ℝ))) :
    ∃ C : ℝ, ∀ N : ℕ,
      ‖u - piecewisePolyInterpCLM N m (x N) (node N) u‖ ≤ C / ((N : ℝ) + 1) ^ (m + 1) := by
  classical
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hq1 : (1 : ℝ) ≤ q := by
    have h2 : (1 : ℝ) < ((m : ℝ) + 1) / γ := by
      rw [lt_div_iff₀ hγ0]
      linarith
    linarith
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
  have hqγ : ((m : ℝ) + 1) ≤ q * γ := by
    rw [div_le_iff₀ hγ0] at hq
    linarith
  have hH0 : 0 ≤ H := by
    have h := hH 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
    rw [show |(0 : ℝ) - 1| = 1 by norm_num, Real.one_rpow, mul_one] at h
    exact le_trans (abs_nonneg _) h
  have hc0 : 0 ≤ c := by
    have h := hUd 1 ⟨zero_lt_one, le_rfl⟩
    rw [Real.one_rpow, mul_one] at h
    exact le_trans (abs_nonneg _) h
  have hfact0 : (0 : ℝ) < ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (m + 1)
  -- the nodes sit at fixed fractions of every panel, so one Lebesgue bound serves every mesh
  have hnodes : ∀ N : ℕ, IsPanelNodes N m (x N) (node N) := fun N =>
    isPanelNodes_graded hq1 hμ0 hμ1 hμmono (hx N) (hnode N)
  obtain ⟨Λ, hΛfam⟩ := exists_isPanelLebesgueBound_of_affine (ι := Unit) (μ := fun _ => μ)
    fun _ => hμmono.injective
  have hΛb : ∀ N : ℕ, IsPanelLebesgueBound N m (x N) (node N) Λ := fun N =>
    hΛfam (c := fun _ => ()) (hnodes N) fun j hj i => hnode N j hj i
  have hΛ0 : 0 ≤ Λ := (hΛb 0).nonneg (hnodes 0)
  set Cst : ℝ := (1 + Λ) * H + c * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial with hCstdef
  have hCst2 : (0 : ℝ) ≤ c * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial :=
    div_nonneg (mul_nonneg hc0 (pow_nonneg (by positivity) _)) hfact0.le
  have hCst0 : 0 ≤ Cst := by
    rw [hCstdef]
    have h1 : (0 : ℝ) ≤ (1 + Λ) * H := mul_nonneg (by linarith) hH0
    linarith
  refine ⟨Cst, fun N => ?_⟩
  have hn0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hnN : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hnodes := hnodes N
  have hΛb := hΛb N
  rw [ContinuousMap.norm_le _ (div_nonneg hCst0 (by positivity))]
  intro t
  obtain ⟨k, hk, h1, h2⟩ := exists_mem_subinterval hnodes.first hnodes.last t
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs]
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · -- the first panel, where only the Hölder bound is available
    have hx0 : (x N 0 : ℝ) = 0 := hnodes.first
    have hx1 : (x N 1 : ℝ) = (1 / ((N : ℝ) + 1)) ^ q := by
      rw [hx N 1 (by omega)]
      norm_num
    have hosc : ∀ s : Set.Icc (0 : ℝ) 1, (x N 0 : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (x N 1 : ℝ) →
        |u s - u (x N 0)| ≤ H * ((x N 1 : ℝ)) ^ γ := by
      intro s hs1 hs2
      rw [hx0] at hs1
      rw [hu s, hu (x N 0)]
      refine le_trans (hH ((s : ℝ)) s.2 ((x N 0 : ℝ)) (x N 0).2) ?_
      rw [hx0, sub_zero, abs_of_nonneg hs1]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs1 hs2 hγ0.le) hH0
    have hxγ : ((x N 1 : ℝ)) ^ γ ≤ 1 / ((N : ℝ) + 1) ^ (m + 1) := by
      have h1n : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
      have h1n1 : (1 : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
        rw [div_le_one hn0]
        exact hnN
      rw [hx1, ← Real.rpow_mul h1n.le]
      calc (1 / ((N : ℝ) + 1)) ^ (q * γ)
          ≤ (1 / ((N : ℝ) + 1)) ^ (((m + 1 : ℕ) : ℝ)) := by
            refine Real.rpow_le_rpow_of_exponent_ge h1n h1n1 ?_
            push_cast
            linarith
        _ = 1 / ((N : ℝ) + 1) ^ (m + 1) := by rw [Real.rpow_natCast, div_pow, one_pow]
    refine (abs_sub_piecewisePolyInterpCLM_apply_le_of_osc hnodes hΛb u hk h1 h2 hosc).trans ?_
    have hxγ0 : (0 : ℝ) ≤ ((x N 1 : ℝ)) ^ γ := Real.rpow_nonneg (x N 1).2.1 γ
    calc (1 + Λ) * (H * ((x N 1 : ℝ)) ^ γ)
        ≤ (1 + Λ) * (H * (1 / ((N : ℝ) + 1) ^ (m + 1))) := by gcongr
      _ = (1 + Λ) * H / ((N : ℝ) + 1) ^ (m + 1) := by ring
      _ ≤ Cst / ((N : ℝ) + 1) ^ (m + 1) := by
          gcongr
          rw [hCstdef]
          linarith
  · -- a panel that stays away from the origin, where the Lagrange error formula applies
    have hkN : k ≤ N := hk
    have hB0 : (0 : ℝ) < (k : ℝ) / ((N : ℝ) + 1) := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      positivity
    have hxk : (x N k : ℝ) = (((k : ℝ)) / ((N : ℝ) + 1)) ^ q := hx N k (by omega)
    have hxk1 : (x N (k + 1) : ℝ) = ((((k : ℝ)) + 1) / ((N : ℝ) + 1)) ^ q := by
      rw [hx N (k + 1) (by omega)]
      norm_cast
    have hxk0 : 0 < (x N k : ℝ) := by
      rw [hxk]
      exact Real.rpow_pos_of_pos hB0 q
    have hsubset : Set.Icc ((x N k : ℝ)) ((x N (k + 1) : ℝ)) ⊆ Set.Ioi 0 :=
      fun s hs => lt_of_lt_of_le hxk0 hs.1
    obtain ⟨ξ, hξ, hξeq⟩ := exists_sub_piecewisePolyInterpCLM_apply_eq_of_contDiffOn hnodes
      isOpen_Ioi hk hsubset hUC hu h1 h2
    have hξ01 : ξ ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨lt_trans hxk0 hξ.1, le_trans hξ.2.le (x N (k + 1)).2.2⟩
    have hdneg : γ - ((m : ℝ) + 1) ≤ 0 := by linarith
    have hderiv : |iteratedDeriv (m + 1) U ξ| ≤ c * ((x N k : ℝ)) ^ (γ - ((m : ℝ) + 1)) := by
      refine (hUd ξ hξ01).trans (mul_le_mul_of_nonneg_left ?_ hc0)
      exact Real.rpow_le_rpow_of_nonpos hxk0 hξ.1.le hdneg
    have hprod : |∏ i, ((t : ℝ) - ((node N k i : ℝ)))|
        ≤ ((x N (k + 1) : ℝ) - (x N k : ℝ)) ^ (m + 1) := by
      rw [Finset.abs_prod]
      calc ∏ i, |(t : ℝ) - ((node N k i : ℝ))|
          ≤ ∏ _i : Fin (m + 1), ((x N (k + 1) : ℝ) - (x N k : ℝ)) := by
            refine Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => ?_
            have hmi := hnodes.mem k hk i
            rw [abs_sub_le_iff]
            exact ⟨by linarith [hmi.1], by linarith [hmi.2]⟩
        _ = ((x N (k + 1) : ℝ) - (x N k : ℝ)) ^ (m + 1) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hkN' : (k : ℝ) + 1 ≤ (N : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hkN
    have hABeq : ((k : ℝ) + 1) / ((N : ℝ) + 1) - (k : ℝ) / ((N : ℝ) + 1)
        = 1 / ((N : ℝ) + 1) := by
      rw [div_sub_div_same]
      norm_num
    have hBA' : (k : ℝ) / ((N : ℝ) + 1) < ((k : ℝ) + 1) / ((N : ℝ) + 1) := by
      have hpos : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
      linarith
    have hA1' : ((k : ℝ) + 1) / ((N : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hn0]
      exact hkN'
    have hA2B' : ((k : ℝ) + 1) / ((N : ℝ) + 1) ≤ 2 * ((k : ℝ) / ((N : ℝ) + 1)) := by
      have hdiff : 2 * ((k : ℝ) / ((N : ℝ) + 1)) - ((k : ℝ) + 1) / ((N : ℝ) + 1)
          = ((k : ℝ) - 1) / ((N : ℝ) + 1) := by
        rw [← mul_div_assoc, div_sub_div_same]
        congr 1
        ring
      have hnn : (0 : ℝ) ≤ ((k : ℝ) - 1) / ((N : ℝ) + 1) := div_nonneg (by linarith) hn0.le
      linarith
    have hgraded := graded_panel_le (m := m) (γ := γ) (q := q) (n := (N : ℝ) + 1)
      (A := ((k : ℝ) + 1) / ((N : ℝ) + 1)) (B := (k : ℝ) / ((N : ℝ) + 1)) hq1 hqγ hn0 hB0
      hBA' hA1' hABeq hA2B'
    rw [← hxk, ← hxk1] at hgraded
    have hpanel0 : (0 : ℝ) ≤ ((x N (k + 1) : ℝ) - (x N k : ℝ)) ^ (m + 1) :=
      pow_nonneg (by linarith [hnodes.step k hk]) _
    rw [hξeq, abs_mul, abs_div, abs_of_pos hfact0]
    calc |iteratedDeriv (m + 1) U ξ| / ((m + 1).factorial : ℝ)
          * |∏ i, ((t : ℝ) - ((node N k i : ℝ)))|
        ≤ (c * ((x N k : ℝ)) ^ (γ - ((m : ℝ) + 1))) / ((m + 1).factorial : ℝ)
            * ((x N (k + 1) : ℝ) - (x N k : ℝ)) ^ (m + 1) := by gcongr
      _ = c / ((m + 1).factorial : ℝ) * (((x N (k + 1) : ℝ) - (x N k : ℝ)) ^ (m + 1)
            * ((x N k : ℝ)) ^ (γ - ((m : ℝ) + 1))) := by ring
      _ ≤ c / ((m + 1).factorial : ℝ)
            * ((q * 2 ^ (q - 1)) ^ (m + 1) / ((N : ℝ) + 1) ^ (m + 1)) := by gcongr
      _ = c * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial / ((N : ℝ) + 1) ^ (m + 1) := by
          ring
      _ ≤ Cst / ((N : ℝ) + 1) ^ (m + 1) := by
          gcongr
          rw [hCstdef]
          have h1 : (0 : ℝ) ≤ (1 + Λ) * H := mul_nonneg (by linarith) hH0
          linarith
/-! ### The mesh graded towards both endpoints -/

/-- The scaled form of `graded_panel_le`: the panel of the mesh `a + (j/r)^q S` obeys the same
bound, with an extra factor `S^γ`. -/
private theorem graded_panel_le' {m : ℕ} {γ q n A B S : ℝ} (hq1 : 1 ≤ q)
    (hqγ : ((m : ℝ) + 1) ≤ q * γ) (hn0 : 0 < n) (hS0 : 0 < S) (hB0 : 0 < B) (hBA : B < A)
    (hA1 : A ≤ 1) (hAB : A - B = 1 / n) (hA2B : A ≤ 2 * B) :
    (S * A ^ q - S * B ^ q) ^ (m + 1) * ((S * B ^ q) ^ (γ - ((m : ℝ) + 1)))
      ≤ S ^ γ * ((q * 2 ^ (q - 1)) ^ (m + 1) / n ^ (m + 1)) := by
  have hSγ : S ^ (m + 1) * (S : ℝ) ^ (γ - ((m : ℝ) + 1)) = S ^ γ := by
    rw [← Real.rpow_natCast S (m + 1), ← Real.rpow_add hS0]
    congr 1
    push_cast
    ring
  have hS0' : (0 : ℝ) ≤ S ^ γ := Real.rpow_nonneg hS0.le γ
  have hfac : (S * A ^ q - S * B ^ q) ^ (m + 1) = S ^ (m + 1) * (A ^ q - B ^ q) ^ (m + 1) := by
    rw [← mul_sub, mul_pow]
  have hfac2 : (S * B ^ q) ^ (γ - ((m : ℝ) + 1))
      = S ^ (γ - ((m : ℝ) + 1)) * (B ^ q) ^ (γ - ((m : ℝ) + 1)) :=
    Real.mul_rpow hS0.le (Real.rpow_nonneg hB0.le q)
  rw [hfac, hfac2]
  calc S ^ (m + 1) * (A ^ q - B ^ q) ^ (m + 1)
        * (S ^ (γ - ((m : ℝ) + 1)) * (B ^ q) ^ (γ - ((m : ℝ) + 1)))
      = (S ^ (m + 1) * S ^ (γ - ((m : ℝ) + 1)))
          * ((A ^ q - B ^ q) ^ (m + 1) * (B ^ q) ^ (γ - ((m : ℝ) + 1))) := by ring
    _ = S ^ γ * ((A ^ q - B ^ q) ^ (m + 1) * (B ^ q) ^ (γ - ((m : ℝ) + 1))) := by rw [hSγ]
    _ ≤ S ^ γ * ((q * 2 ^ (q - 1)) ^ (m + 1) / n ^ (m + 1)) :=
        mul_le_mul_of_nonneg_left
          (graded_panel_le hq1 hqγ hn0 hB0 hBA hA1 hAB hA2B) hS0'

variable {a b : ℝ} {m r N : ℕ} {q : ℝ}

/-- **The symmetric graded mesh and its nodes form a panel node system.**  The `n = 2 r` panels of
`[a, b]` are graded towards both endpoints — `x_j = a + (2j/n)^q (b-a)/2` for `j ≤ n/2` and
`x_{n-j} = a + b - x_j` — and the nodes of a panel are the images of the partition `μ` on the left
half and of its reflection `1 - μ_{m-i}` on the right.  [han2009theoretical], §12.5, the paragraph
preceding Theorem 12.5.6. -/
theorem isPanelNodes_gradedSym (hab : a < b) (hr : 0 < r) (hN : N + 1 = 2 * r) (hq1 : 1 ≤ q)
    {μ : Fin (m + 1) → ℝ} (hμ0 : μ 0 = 0) (hμ1 : μ (Fin.last m) = 1) (hμmono : StrictMono μ)
    {x : ℕ → Set.Icc a b} {node : ℕ → Fin (m + 1) → Set.Icc a b}
    (hxL : ∀ j ≤ r, (x j : ℝ) = a + ((j : ℝ) / r) ^ q * ((b - a) / 2))
    (hxR : ∀ j ≤ r, (x (2 * r - j) : ℝ) = a + b - (x j : ℝ))
    (hnodeL : ∀ j < r, ∀ i, (node j i : ℝ)
      = (x j : ℝ) + μ i * ((x (j + 1) : ℝ) - (x j : ℝ)))
    (hnodeR : ∀ j, r ≤ j → j ≤ N → ∀ i, (node j i : ℝ)
      = (x j : ℝ) + (1 - μ i.rev) * ((x (j + 1) : ℝ) - (x j : ℝ))) :
    IsPanelNodes N m x node := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
  have hS0 : (0 : ℝ) < (b - a) / 2 := by linarith
  -- the left half increases
  have hstepL : ∀ j < r, (x j : ℝ) < (x (j + 1) : ℝ) := by
    intro j hj
    rw [hxL j (by omega), hxL (j + 1) (by omega)]
    have hlt : ((j : ℝ) / r) ^ q < (((j : ℝ) + 1) / r) ^ q := by
      refine Real.rpow_lt_rpow (by positivity) ?_ hq0
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      gcongr
      linarith
    push_cast
    nlinarith [hlt, hS0]
  -- the reflection identities for a panel of the right half
  have hrefl : ∀ j, r ≤ j → j ≤ N →
      (x j : ℝ) = a + b - (x (2 * r - 1 - j + 1) : ℝ) ∧
        (x (j + 1) : ℝ) = a + b - (x (2 * r - 1 - j) : ℝ) := by
    intro j hj1 hj2
    have hi : 2 * r - 1 - j < r := by omega
    constructor
    · have h := hxR (2 * r - 1 - j + 1) (by omega)
      rwa [show 2 * r - (2 * r - 1 - j + 1) = j by omega] at h
    · have h := hxR (2 * r - 1 - j) (by omega)
      rwa [show 2 * r - (2 * r - 1 - j) = j + 1 by omega] at h
  have hstep : ∀ j ≤ N, (x j : ℝ) < (x (j + 1) : ℝ) := by
    intro j hj
    rcases Nat.lt_or_ge j r with hjr | hjr
    · exact hstepL j hjr
    · obtain ⟨h1, h2⟩ := hrefl j hjr hj
      have h3 := hstepL (2 * r - 1 - j) (by omega)
      rw [h1, h2]
      linarith
  -- the two partitions of the unit interval
  have hμmem : ∀ i : Fin (m + 1), μ i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    exact ⟨by rw [← hμ0]; exact hμmono.monotone (Fin.zero_le i),
      by rw [← hμ1]; exact hμmono.monotone (Fin.le_last i)⟩
  refine ⟨hstep, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxL 0 (by omega), Nat.cast_zero, zero_div, Real.zero_rpow (ne_of_gt hq0)]
    ring
  · have h := hxR 0 (by omega)
    rw [Nat.sub_zero, hxL 0 (by omega), Nat.cast_zero, zero_div,
      Real.zero_rpow (ne_of_gt hq0)] at h
    rw [show N + 1 = 2 * r from hN, h]
    ring
  · intro j hj i
    have hd : (0 : ℝ) ≤ (x (j + 1) : ℝ) - (x j : ℝ) := sub_nonneg.mpr (hstep j hj).le
    rcases Nat.lt_or_ge j r with hjr | hjr
    · rw [hnodeL j hjr i]
      constructor <;> nlinarith [(hμmem i).1, (hμmem i).2]
    · rw [hnodeR j hjr hj i]
      constructor <;> nlinarith [(hμmem i.rev).1, (hμmem i.rev).2]
  · intro j hj i i' hii
    simp only at hii
    have hd : (0 : ℝ) < (x (j + 1) : ℝ) - (x j : ℝ) := sub_pos.mpr (hstep j hj)
    rcases Nat.lt_or_ge j r with hjr | hjr
    · rw [hnodeL j hjr i, hnodeL j hjr i'] at hii
      exact hμmono.injective (mul_right_cancel₀ (ne_of_gt hd) (by linarith))
    · rw [hnodeR j hjr hj i, hnodeR j hjr hj i'] at hii
      have hrev : μ i.rev = μ i'.rev := by
        have := mul_right_cancel₀ (ne_of_gt hd)
          (show (1 - μ i.rev) * ((x (j + 1) : ℝ) - (x j : ℝ))
            = (1 - μ i'.rev) * ((x (j + 1) : ℝ) - (x j : ℝ)) by linarith)
        linarith
      have := hμmono.injective hrev
      exact Fin.rev_injective this
  · intro j hj
    refine Subtype.ext ?_
    rcases Nat.lt_or_ge j r with hjr | hjr
    · rw [hnodeL j hjr 0, hμ0]
      ring
    · rw [hnodeR j hjr hj 0, Fin.rev_zero, hμ1]
      ring
  · intro j hj
    refine Subtype.ext ?_
    rcases Nat.lt_or_ge j r with hjr | hjr
    · rw [hnodeL j hjr (Fin.last m), hμ1]
      ring
    · rw [hnodeR j hjr hj (Fin.last m), Fin.rev_last, hμ0]
      ring

/-- **The panels of the symmetric graded mesh are short.**  On the mesh graded towards both
endpoints of `[a, b]` — `x_j = a + (j/r)^q (b-a)/2` on the left half and `x_{2r-j} = a + b - x_j`
on the right — every one of the `2 r` panels has width at most `(b - a) q / (2 r)`.

The mean value theorem gives it on the left half, in the crude form `A^q - B^q ≤ q (A - B)` for
`0 ≤ B < A ≤ 1`: unlike the sharp `q A^{q-1} (A - B)` it survives at `B = 0`, which is the panel
touching the endpoint, where the grading is steepest.  The reflection carries it to the right
half.  The bound is `𝒪(1/r)`, so it is the hypothesis that makes piecewise polynomial
interpolation on the family of these meshes converge for every continuous function, by
`tendsto_piecewisePolyInterpCLM`. -/
theorem sub_le_gradedSym (hab : a < b) (hr : 0 < r) (hN : N + 1 = 2 * r) (hq1 : 1 ≤ q)
    {x : ℕ → Set.Icc a b}
    (hxL : ∀ j ≤ r, (x j : ℝ) = a + ((j : ℝ) / r) ^ q * ((b - a) / 2))
    (hxR : ∀ j ≤ r, (x (2 * r - j) : ℝ) = a + b - (x j : ℝ)) :
    ∀ j ≤ N, (x (j + 1) : ℝ) - (x j : ℝ) ≤ (b - a) / 2 * q / r := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hS0 : (0 : ℝ) < (b - a) / 2 := by linarith
  -- a panel of the left half, by the mean value bound in the normalized variable
  have hleft : ∀ i < r, (x (i + 1) : ℝ) - (x i : ℝ) ≤ (b - a) / 2 * q / r := by
    intro i hi
    have hB0 : (0 : ℝ) ≤ (i : ℝ) / (r : ℝ) := by positivity
    have hABeq : ((i : ℝ) + 1) / (r : ℝ) - (i : ℝ) / (r : ℝ) = 1 / (r : ℝ) := by
      rw [div_sub_div_same]
      norm_num
    have hBA : (i : ℝ) / (r : ℝ) < ((i : ℝ) + 1) / (r : ℝ) := by
      have hpos : (0 : ℝ) < 1 / (r : ℝ) := by positivity
      linarith
    have hA1 : ((i : ℝ) + 1) / (r : ℝ) ≤ 1 := by
      rw [div_le_one hr0]
      exact_mod_cast (by omega : i + 1 ≤ r)
    have hstep := Real.rpow_sub_rpow_le_mul_sub hq1 hB0 hBA hA1
    rw [hABeq] at hstep
    have he1 : (x i : ℝ) = a + ((i : ℝ) / (r : ℝ)) ^ q * ((b - a) / 2) := hxL i (by omega)
    have he2 : (x (i + 1) : ℝ) = a + (((i : ℝ) + 1) / (r : ℝ)) ^ q * ((b - a) / 2) := by
      rw [hxL (i + 1) (by omega)]
      push_cast
      ring
    rw [he1, he2]
    calc a + (((i : ℝ) + 1) / (r : ℝ)) ^ q * ((b - a) / 2)
          - (a + ((i : ℝ) / (r : ℝ)) ^ q * ((b - a) / 2))
        = ((((i : ℝ) + 1) / (r : ℝ)) ^ q - ((i : ℝ) / (r : ℝ)) ^ q) * ((b - a) / 2) := by ring
      _ ≤ q * (1 / (r : ℝ)) * ((b - a) / 2) := mul_le_mul_of_nonneg_right hstep hS0.le
      _ = (b - a) / 2 * q / (r : ℝ) := by ring
  intro j hj
  rcases Nat.lt_or_ge j r with hjr | hjr
  · exact hleft j hjr
  · -- a panel of the right half is the mirror image of one of the left half
    have hxj : (x j : ℝ) = a + b - (x (2 * r - 1 - j + 1) : ℝ) := by
      have h := hxR (2 * r - 1 - j + 1) (by omega)
      rwa [show 2 * r - (2 * r - 1 - j + 1) = j by omega] at h
    have hxj1 : (x (j + 1) : ℝ) = a + b - (x (2 * r - 1 - j) : ℝ) := by
      have h := hxR (2 * r - 1 - j) (by omega)
      rwa [show 2 * r - (2 * r - 1 - j) = j + 1 by omega] at h
    have hmirror := hleft (2 * r - 1 - j) (by omega)
    rw [hxj, hxj1]
    linarith

/-- **The interpolation error on one panel from a bound on the `(m+1)`-st derivative there.**  Only
the smoothness of `G` on an open set containing the panel is used. -/
private theorem abs_sub_panel_le {a b : ℝ} {n m : ℕ} {x : ℕ → Set.Icc a b}
    {node : ℕ → Fin (m + 1) → Set.Icc a b} (h : IsPanelNodes n m x node)
    {V : Set ℝ} (hV : IsOpen V) {k : ℕ} (hk : k ≤ n)
    (hVsub : Set.Icc ((x k : ℝ)) ((x (k + 1) : ℝ)) ⊆ V)
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) G V) {f : C(Set.Icc a b, ℝ)}
    (hf : ∀ t : Set.Icc a b, f t = G ((t : ℝ))) {M : ℝ}
    (hM : ∀ s ∈ Set.Ioo ((x k : ℝ)) ((x (k + 1) : ℝ)), |iteratedDeriv (m + 1) G s| ≤ M)
    {t : Set.Icc a b} (h1 : (x k : ℝ) ≤ (t : ℝ)) (h2 : (t : ℝ) ≤ (x (k + 1) : ℝ)) :
    |f t - piecewisePolyInterpCLM n m x node f t|
      ≤ M * ((x (k + 1) : ℝ) - (x k : ℝ)) ^ (m + 1) / (m + 1).factorial := by
  have hfact0 : (0 : ℝ) < ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (m + 1)
  obtain ⟨ξ, hξ, hξeq⟩ := exists_sub_piecewisePolyInterpCLM_apply_eq_of_contDiffOn h hV hk hVsub
    hG hf h1 h2
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM ξ hξ)
  have hprod : |∏ i, ((t : ℝ) - ((node k i : ℝ)))|
      ≤ ((x (k + 1) : ℝ) - (x k : ℝ)) ^ (m + 1) := by
    rw [Finset.abs_prod]
    calc ∏ i, |(t : ℝ) - ((node k i : ℝ))|
        ≤ ∏ _i : Fin (m + 1), ((x (k + 1) : ℝ) - (x k : ℝ)) := by
          refine Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => ?_
          have hmi := h.mem k hk i
          rw [abs_sub_le_iff]
          exact ⟨by linarith [hmi.1], by linarith [hmi.2]⟩
      _ = ((x (k + 1) : ℝ) - (x k : ℝ)) ^ (m + 1) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hξeq, abs_mul, abs_div, abs_of_pos hfact0]
  calc |iteratedDeriv (m + 1) G ξ| / ((m + 1).factorial : ℝ)
        * |∏ i, ((t : ℝ) - ((node k i : ℝ)))|
      ≤ M / ((m + 1).factorial : ℝ) * ((x (k + 1) : ℝ) - (x k : ℝ)) ^ (m + 1) := by
        gcongr
        exact hM ξ hξ
    _ = M * ((x (k + 1) : ℝ) - (x k : ℝ)) ^ (m + 1) / (m + 1).factorial := by ring

/-- **The graded-mesh interpolation error on `[a, b]`, graded towards both endpoints.**  The
function is Hölder of exponent `γ` on the whole interval, of class `C^{m+1}` inside, and its
`(m+1)`-st derivative grows no faster than `(x - a)^{γ-(m+1)}` towards `a` and `(b - x)^{γ-(m+1)}`
towards `b` — the regularity that the solution of a weakly singular integral equation of the second
kind has ([han2009theoretical], §12.5, Theorem 12.5.4).

The two extreme panels are handled by the Hölder bound, the inner panels of the left half by the
derivative bound towards `a` and those of the right half by the one towards `b`, the latter being
the mirror image of the former through `x ↦ a + b - x`.  The constant is explicit, so that the
bound may be applied uniformly over a family of functions with common `H` and `c` — which is what
the row functions `y ↦ l (x, y) u (y)` of a product integration method are.

This is `norm_sub_piecewisePolyInterpCLM_le_graded` in the form that the convergence proof for
graded-mesh product integration uses; [han2009theoretical], §12.5, Theorem 12.5.6. -/
theorem norm_sub_piecewisePolyInterpCLM_le_gradedSym {a b : ℝ} {m r N : ℕ} {γ q H c Λ : ℝ}
    (hab : a < b) (hr : 0 < r)
    (hN : N + 1 = 2 * r) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hq : ((m : ℝ) + 1) / γ ≤ q)
    {μ : Fin (m + 1) → ℝ} (hμ0 : μ 0 = 0) (hμ1 : μ (Fin.last m) = 1) (hμmono : StrictMono μ)
    {x : ℕ → Set.Icc a b} {node : ℕ → Fin (m + 1) → Set.Icc a b}
    (hxL : ∀ j ≤ r, (x j : ℝ) = a + ((j : ℝ) / r) ^ q * ((b - a) / 2))
    (hxR : ∀ j ≤ r, (x (2 * r - j) : ℝ) = a + b - (x j : ℝ))
    (hnodeL : ∀ j < r, ∀ i, (node j i : ℝ)
      = (x j : ℝ) + μ i * ((x (j + 1) : ℝ) - (x j : ℝ)))
    (hnodeR : ∀ j, r ≤ j → j ≤ N → ∀ i, (node j i : ℝ)
      = (x j : ℝ) + (1 - μ i.rev) * ((x (j + 1) : ℝ) - (x j : ℝ)))
    (hΛ : IsPanelLebesgueBound N m x node Λ)
    {W : ℝ → ℝ} {w : C(Set.Icc a b, ℝ)} (hw : ∀ t : Set.Icc a b, w t = W ((t : ℝ)))
    (hH : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, |W s - W t| ≤ H * |s - t| ^ γ)
    (hWC : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) W (Set.Ioo a b))
    (hWL : ∀ s ∈ Set.Ioc a ((a + b) / 2),
      |iteratedDeriv (m + 1) W s| ≤ c * (s - a) ^ (γ - ((m : ℝ) + 1)))
    (hWR : ∀ s ∈ Set.Ico ((a + b) / 2) b,
      |iteratedDeriv (m + 1) W s| ≤ c * (b - s) ^ (γ - ((m : ℝ) + 1))) :
    ‖w - piecewisePolyInterpCLM N m x node w‖
      ≤ ((1 + Λ) * H * ((b - a) / 2) ^ γ
          + c * ((b - a) / 2) ^ γ * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial)
        / (r : ℝ) ^ (m + 1) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hS0 : (0 : ℝ) < (b - a) / 2 := by linarith
  have hSγ0 : (0 : ℝ) ≤ ((b - a) / 2) ^ γ := Real.rpow_nonneg hS0.le γ
  have hq1 : (1 : ℝ) ≤ q := by
    have h2 : (1 : ℝ) < ((m : ℝ) + 1) / γ := by
      rw [lt_div_iff₀ hγ0]
      linarith
    linarith
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
  have hqγ : ((m : ℝ) + 1) ≤ q * γ := by
    rw [div_le_iff₀ hγ0] at hq
    linarith
  have hfact0 : (0 : ℝ) < ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (m + 1)
  have hnodes := isPanelNodes_gradedSym hab hr hN hq1 hμ0 hμ1 hμmono hxL hxR hnodeL hnodeR
  have hΛ0 : (0 : ℝ) ≤ Λ := hΛ.nonneg hnodes
  have hH0 : 0 ≤ H := by
    have h := hH a ⟨le_rfl, hab.le⟩ b ⟨hab.le, le_rfl⟩
    rw [abs_of_nonpos (by linarith : a - b ≤ 0), neg_sub] at h
    have h2 : (0 : ℝ) < (b - a) ^ γ := Real.rpow_pos_of_pos (by linarith) γ
    by_contra hcon
    push Not at hcon
    have := mul_neg_of_neg_of_pos hcon h2
    linarith [abs_nonneg (W a - W b)]
  have hc0 : 0 ≤ c := by
    have h := hWL ((a + b) / 2) ⟨by linarith, le_rfl⟩
    have h2 : (0 : ℝ) < ((a + b) / 2 - a) ^ (γ - ((m : ℝ) + 1)) :=
      Real.rpow_pos_of_pos (by linarith) _
    by_contra hcon
    push Not at hcon
    have := mul_neg_of_neg_of_pos hcon h2
    linarith [abs_nonneg (iteratedDeriv (m + 1) W ((a + b) / 2))]
  -- the mesh: monotonicity, the midpoint, and the first panel
  have hmono : ∀ i j, i ≤ j → j ≤ N + 1 → (x i : ℝ) ≤ (x j : ℝ) := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact fun _ => le_rfl
    | succ k hk ih => exact fun hk1 => (ih (by omega)).trans (hnodes.step k (by omega)).le
  have hxr : (x r : ℝ) = (a + b) / 2 := by
    rw [hxL r le_rfl, div_self (ne_of_gt hr0), Real.one_rpow]
    ring
  have hx1 : (x 1 : ℝ) = a + (1 / (r : ℝ)) ^ q * ((b - a) / 2) := by
    rw [hxL 1 hr]
    norm_num
  have hx1a : (0 : ℝ) < (x 1 : ℝ) - a := by
    have hpos : (0 : ℝ) < (1 / (r : ℝ)) ^ q := Real.rpow_pos_of_pos (by positivity) q
    rw [hx1]
    nlinarith
  have hxN : (x N : ℝ) = a + b - (x 1 : ℝ) := by
    have h := hxR 1 hr
    rwa [show 2 * r - 1 = N by omega] at h
  have hpanel1 : ((x 1 : ℝ) - a) ^ γ ≤ ((b - a) / 2) ^ γ / (r : ℝ) ^ (m + 1) := by
    have hone : (0 : ℝ) < 1 / (r : ℝ) := by positivity
    have hone1 : (1 : ℝ) / (r : ℝ) ≤ 1 := by
      rw [div_le_one hr0]
      exact hr1
    have heq : (x 1 : ℝ) - a = (1 / (r : ℝ)) ^ q * ((b - a) / 2) := by
      rw [hx1]
      ring
    rw [heq, Real.mul_rpow (Real.rpow_nonneg hone.le q) hS0.le, ← Real.rpow_mul hone.le]
    have hle : (1 / (r : ℝ)) ^ (q * γ) ≤ 1 / (r : ℝ) ^ (m + 1) := by
      calc (1 / (r : ℝ)) ^ (q * γ) ≤ (1 / (r : ℝ)) ^ (((m + 1 : ℕ) : ℝ)) := by
            refine Real.rpow_le_rpow_of_exponent_ge hone hone1 ?_
            push_cast
            linarith
        _ = 1 / (r : ℝ) ^ (m + 1) := by rw [Real.rpow_natCast, div_pow, one_pow]
    calc (1 / (r : ℝ)) ^ (q * γ) * ((b - a) / 2) ^ γ
        ≤ (1 / (r : ℝ) ^ (m + 1)) * ((b - a) / 2) ^ γ := by gcongr
      _ = ((b - a) / 2) ^ γ / (r : ℝ) ^ (m + 1) := by ring
  -- the graded estimate for an inner panel of the left half
  have hinner : ∀ i, 1 ≤ i → i < r →
      ((x (i + 1) : ℝ) - (x i : ℝ)) ^ (m + 1) * ((x i : ℝ) - a) ^ (γ - ((m : ℝ) + 1))
        ≤ ((b - a) / 2) ^ γ * ((q * 2 ^ (q - 1)) ^ (m + 1) / (r : ℝ) ^ (m + 1)) := by
    intro i hi1 hir
    have hi1' : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
    have hir' : (i : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hir
    have hB0 : (0 : ℝ) < (i : ℝ) / r := by positivity
    have hABeq : ((i : ℝ) + 1) / r - (i : ℝ) / r = 1 / (r : ℝ) := by
      rw [div_sub_div_same]
      norm_num
    have hBA : (i : ℝ) / r < ((i : ℝ) + 1) / r := by
      have hpos : (0 : ℝ) < 1 / (r : ℝ) := by positivity
      linarith
    have hA1 : ((i : ℝ) + 1) / r ≤ 1 := by
      rw [div_le_one hr0]
      exact hir'
    have hA2B : ((i : ℝ) + 1) / r ≤ 2 * ((i : ℝ) / r) := by
      have hdiff : 2 * ((i : ℝ) / r) - ((i : ℝ) + 1) / r = ((i : ℝ) - 1) / r := by
        rw [← mul_div_assoc, div_sub_div_same]
        congr 1
        ring
      have hnn : (0 : ℝ) ≤ ((i : ℝ) - 1) / r := div_nonneg (by linarith) hr0.le
      linarith
    have hgr := graded_panel_le' (m := m) (γ := γ) (q := q) (n := (r : ℝ))
      (A := ((i : ℝ) + 1) / r) (B := (i : ℝ) / r) (S := (b - a) / 2) hq1 hqγ hr0 hS0 hB0 hBA
      hA1 hABeq hA2B
    have he1 : (x i : ℝ) - a = ((b - a) / 2) * ((i : ℝ) / r) ^ q := by
      rw [hxL i (by omega)]
      ring
    have he2 : (x (i + 1) : ℝ) - a = ((b - a) / 2) * (((i : ℝ) + 1) / r) ^ q := by
      rw [hxL (i + 1) (by omega)]
      push_cast
      ring
    have he3 : (x (i + 1) : ℝ) - (x i : ℝ)
        = ((b - a) / 2) * (((i : ℝ) + 1) / r) ^ q - ((b - a) / 2) * ((i : ℝ) / r) ^ q := by
      linarith
    rw [he3, he1]
    exact hgr
  -- the constant
  set Cst : ℝ := (1 + Λ) * H * ((b - a) / 2) ^ γ
    + c * ((b - a) / 2) ^ γ * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial with hCstdef
  have hCst1 : (0 : ℝ) ≤ (1 + Λ) * H * ((b - a) / 2) ^ γ :=
    mul_nonneg (mul_nonneg (by linarith) hH0) hSγ0
  have hCst2 : (0 : ℝ)
      ≤ c * ((b - a) / 2) ^ γ * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial :=
    div_nonneg (mul_nonneg (mul_nonneg hc0 hSγ0) (pow_nonneg (by positivity) _)) hfact0.le
  have hCst0 : 0 ≤ Cst := by
    rw [hCstdef]
    linarith
  rw [ContinuousMap.norm_le _ (div_nonneg hCst0 (by positivity))]
  intro t
  obtain ⟨k, hk, h1, h2⟩ := exists_mem_subinterval hnodes.first hnodes.last t
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs]
  rcases Nat.lt_or_ge k r with hkr | hkr
  · rcases Nat.eq_zero_or_pos k with rfl | hk1
    · -- the first panel, where only the Hölder bound is available
      have hx0 : (x 0 : ℝ) = a := hnodes.first
      have hosc : ∀ s : Set.Icc a b, (x 0 : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (x (0 + 1) : ℝ) →
          |w s - w (x 0)| ≤ H * ((x 1 : ℝ) - a) ^ γ := by
        intro s hs1 hs2
        rw [hx0] at hs1
        have hs2' : (s : ℝ) ≤ (x 1 : ℝ) := hs2
        rw [hw s, hw (x 0)]
        refine le_trans (hH ((s : ℝ)) s.2 ((x 0 : ℝ)) (x 0).2) ?_
        rw [hx0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (s : ℝ) - a)]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith) (by linarith) hγ0.le) hH0
      refine (abs_sub_piecewisePolyInterpCLM_apply_le_of_osc hnodes hΛ w hk h1 h2 hosc).trans ?_
      calc (1 + Λ) * (H * ((x 1 : ℝ) - a) ^ γ)
          ≤ (1 + Λ) * (H * (((b - a) / 2) ^ γ / (r : ℝ) ^ (m + 1))) := by gcongr
        _ = (1 + Λ) * H * ((b - a) / 2) ^ γ / (r : ℝ) ^ (m + 1) := by ring
        _ ≤ Cst / (r : ℝ) ^ (m + 1) := by
            gcongr
            rw [hCstdef]
            linarith
    · -- an inner panel of the left half
      have hxk1r : (x (k + 1) : ℝ) ≤ (a + b) / 2 := by
        rw [← hxr]
        exact hmono (k + 1) r (by omega) (by omega)
      have hxka : a < (x k : ℝ) := by
        have := hmono 1 k hk1 (by omega)
        linarith
      have hVsub : Set.Icc ((x k : ℝ)) ((x (k + 1) : ℝ)) ⊆ Set.Ioo a b := fun s hs =>
        ⟨lt_of_lt_of_le hxka hs.1, by linarith [hs.2]⟩
      have hM : ∀ s ∈ Set.Ioo ((x k : ℝ)) ((x (k + 1) : ℝ)),
          |iteratedDeriv (m + 1) W s| ≤ c * ((x k : ℝ) - a) ^ (γ - ((m : ℝ) + 1)) := by
        intro s hs
        refine le_trans (hWL s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
          (mul_le_mul_of_nonneg_left ?_ hc0)
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith [hs.1]) (by linarith)
      refine (abs_sub_panel_le hnodes isOpen_Ioo hk hVsub hWC hw hM h1 h2).trans ?_
      calc c * ((x k : ℝ) - a) ^ (γ - ((m : ℝ) + 1))
              * ((x (k + 1) : ℝ) - (x k : ℝ)) ^ (m + 1) / (m + 1).factorial
          = c / ((m + 1).factorial : ℝ) * (((x (k + 1) : ℝ) - (x k : ℝ)) ^ (m + 1)
              * ((x k : ℝ) - a) ^ (γ - ((m : ℝ) + 1))) := by ring
        _ ≤ c / ((m + 1).factorial : ℝ) * (((b - a) / 2) ^ γ
              * ((q * 2 ^ (q - 1)) ^ (m + 1) / (r : ℝ) ^ (m + 1))) :=
            mul_le_mul_of_nonneg_left (hinner k hk1 hkr) (div_nonneg hc0 hfact0.le)
        _ = c * ((b - a) / 2) ^ γ * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial
              / (r : ℝ) ^ (m + 1) := by ring
        _ ≤ Cst / (r : ℝ) ^ (m + 1) := by
            gcongr
            rw [hCstdef]
            linarith
  · have hxkr : (a + b) / 2 ≤ (x k : ℝ) := by
      rw [← hxr]
      exact hmono r k hkr (by omega)
    rcases eq_or_lt_of_le hk with rfl | hkN
    · -- the last panel, where only the Hölder bound is available
      have hxN1 : (x (k + 1) : ℝ) = b := hnodes.last
      have hosc : ∀ s : Set.Icc a b, (x k : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (x (k + 1) : ℝ) →
          |w s - w (x k)| ≤ H * ((x 1 : ℝ) - a) ^ γ := by
        intro s hs1 hs2
        rw [hw s, hw (x k)]
        refine le_trans (hH ((s : ℝ)) s.2 ((x k : ℝ)) (x k).2) ?_
        rw [abs_of_nonneg (by linarith)]
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) ?_ hγ0.le) hH0
        rw [hxN1] at hs2
        rw [hxN]
        linarith
      refine (abs_sub_piecewisePolyInterpCLM_apply_le_of_osc hnodes hΛ w hk h1 h2 hosc).trans ?_
      calc (1 + Λ) * (H * ((x 1 : ℝ) - a) ^ γ)
          ≤ (1 + Λ) * (H * (((b - a) / 2) ^ γ / (r : ℝ) ^ (m + 1))) := by gcongr
        _ = (1 + Λ) * H * ((b - a) / 2) ^ γ / (r : ℝ) ^ (m + 1) := by ring
        _ ≤ Cst / (r : ℝ) ^ (m + 1) := by
            gcongr
            rw [hCstdef]
            linarith
    · -- an inner panel of the right half, the mirror image of one of the left half
      have hi1 : 1 ≤ 2 * r - 1 - k := by omega
      have hir : 2 * r - 1 - k < r := by omega
      have hxk : (x k : ℝ) = a + b - (x (2 * r - 1 - k + 1) : ℝ) := by
        have h := hxR (2 * r - 1 - k + 1) (by omega)
        rwa [show 2 * r - (2 * r - 1 - k + 1) = k by omega] at h
      have hxk1 : (x (k + 1) : ℝ) = a + b - (x (2 * r - 1 - k) : ℝ) := by
        have h := hxR (2 * r - 1 - k) (by omega)
        rwa [show 2 * r - (2 * r - 1 - k) = k + 1 by omega] at h
      have hia : (0 : ℝ) < (x (2 * r - 1 - k) : ℝ) - a := by
        have := hmono 1 (2 * r - 1 - k) hi1 (by omega)
        linarith
      have hxk1b : (x (k + 1) : ℝ) < b := by
        rw [hxk1]
        linarith
      have hVsub : Set.Icc ((x k : ℝ)) ((x (k + 1) : ℝ)) ⊆ Set.Ioo a b := fun s hs =>
        ⟨by linarith [hs.1], lt_of_le_of_lt hs.2 hxk1b⟩
      have hM : ∀ s ∈ Set.Ioo ((x k : ℝ)) ((x (k + 1) : ℝ)),
          |iteratedDeriv (m + 1) W s|
            ≤ c * ((x (2 * r - 1 - k) : ℝ) - a) ^ (γ - ((m : ℝ) + 1)) := by
        intro s hs
        refine le_trans (hWR s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
          (mul_le_mul_of_nonneg_left ?_ hc0)
        refine Real.rpow_le_rpow_of_nonpos hia ?_ (by linarith)
        have := hs.2
        rw [hxk1] at this
        linarith
      have hlen : (x (k + 1) : ℝ) - (x k : ℝ)
          = (x (2 * r - 1 - k + 1) : ℝ) - (x (2 * r - 1 - k) : ℝ) := by
        rw [hxk, hxk1]
        ring
      refine (abs_sub_panel_le hnodes isOpen_Ioo hk hVsub hWC hw hM h1 h2).trans ?_
      rw [hlen]
      calc c * ((x (2 * r - 1 - k) : ℝ) - a) ^ (γ - ((m : ℝ) + 1))
              * ((x (2 * r - 1 - k + 1) : ℝ) - (x (2 * r - 1 - k) : ℝ)) ^ (m + 1)
              / (m + 1).factorial
          = c / ((m + 1).factorial : ℝ)
              * (((x (2 * r - 1 - k + 1) : ℝ) - (x (2 * r - 1 - k) : ℝ)) ^ (m + 1)
              * ((x (2 * r - 1 - k) : ℝ) - a) ^ (γ - ((m : ℝ) + 1))) := by ring
        _ ≤ c / ((m + 1).factorial : ℝ) * (((b - a) / 2) ^ γ
              * ((q * 2 ^ (q - 1)) ^ (m + 1) / (r : ℝ) ^ (m + 1))) :=
            mul_le_mul_of_nonneg_left (hinner (2 * r - 1 - k) hi1 hir)
              (div_nonneg hc0 hfact0.le)
        _ = c * ((b - a) / 2) ^ γ * (q * 2 ^ (q - 1)) ^ (m + 1) / (m + 1).factorial
              / (r : ℝ) ^ (m + 1) := by ring
        _ ≤ Cst / (r : ℝ) ^ (m + 1) := by
            gcongr
            rw [hCstdef]
            linarith

