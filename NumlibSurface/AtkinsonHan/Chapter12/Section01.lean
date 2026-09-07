import Numlib.IntegralEquations.SecondKind

/-!
# Atkinson–Han §12.1: projection methods for equations of the second kind

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §12.1.

The book's data is a Banach space `V`, a scalar `λ ≠ 0`, a bounded operator `K` on `V`, and a
sequence of bounded projections `P_n` of `V` onto finite-dimensional subspaces `V_n`.  `λ` is
Lean's lambda binder, so the scalar is written `μ` throughout.  The surface states everything for a
*single* bounded idempotent `P`, where the book states it for a sequence, and quantifies over `n`
only where a limit is taken; the finite dimensionality of `V_n` is never used and is not assumed.

## Main results

* `IsProjectionSolution` — (12.1.18), the projection method for `(λ - K) u = f`, with
  `isProjectionSolution_iff_smul_sub_comp` for the equivalent form (12.1.19) and
  `equation_12_1_17` for `‖P‖ ≥ 1`.
* `lemma_12_1_3`, `lemma_12_1_4` — pointwise convergence of bounded operators is uniform on
  compact sets, and hence `‖K - P_n K‖ → 0` for a compact `K` and projections converging
  pointwise to the identity, which is the hypothesis (12.1.21).
* `theorem_12_1_2` — stability: `(λ - P K)⁻¹` exists, is bounded by (12.1.22), and the projection
  equations are uniquely solvable.
* `equation_12_1_23`, `equation_12_1_24` — the error identity and the two-sided estimate, which
  together say that `‖u - u_n‖` and `‖u - P_n u‖ ` tend to zero at exactly the same rate.
* `exercise_12_1_3`, `exercise_12_1_4` — the asymptotic constant of the error bound is that of the
  exact inverse, and the leading term of the error is `λ (λ - K)⁻¹ (u - P_n u)`.

## Not formalized here

Sections 12.1.1 and 12.1.2, the collocation and Galerkin methods and their linear systems
(12.1.5) and (12.1.14).  They are this framework specialized to `C(D)` and `L²(D)` with a concrete
basis of the trial space, and nothing in the rest of the chapter uses them.
-/

open Filter Topology

namespace AtkinsonHan.Chapter12

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-! ### The projection equations -/

/-- **(12.1.18)**, the projection method for the equation of the second kind `(λ - K) u = f`: the
approximation `u_n` lies in the trial space `range P` and satisfies the *projected* equation
`P ((λ - K) u_n) = P f`.

This is the backbone `IsProjectionMethodSolution` of the operator `λ - K`
(`isProjectionSolution_iff`); the equivalent form (12.1.19), in which no membership hypothesis
appears, is `isProjectionSolution_iff_smul_sub_comp`. -/
def IsProjectionSolution (μ : 𝕜) (K P : X →L[𝕜] X) (f un : X) : Prop :=
  un ∈ LinearMap.range (P : X →ₗ[𝕜] X) ∧ P ((μ • 1 - K : X →L[𝕜] X) un) = P f

/-- (12.1.18) is the backbone's projection method for the operator `λ - K`. -/
theorem isProjectionSolution_iff (μ : 𝕜) (K P : X →L[𝕜] X) (f un : X) :
    IsProjectionSolution μ K P f un ↔
      IsProjectionMethodSolution ((μ • 1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) f P un :=
  Iff.rfl

/-- A projection solution fixes the projection, `P u_n = u_n`. -/
theorem IsProjectionSolution.apply_eq_self {μ : 𝕜} {K P : X →L[𝕜] X} (hP : IsIdempotentElem P)
    {f un : X} (h : IsProjectionSolution μ K P f un) : P un = un :=
  IsProjectionMethodSolution.apply_eq_self hP h

/-- **(12.1.19)**: for `λ ≠ 0` the projection equations `P ((λ - K) u_n) = P f` on the trial space
are the same as the equations `(λ - P K) u_n = P f` on the whole space.  The membership
`u_n ∈ range P` need not be assumed on the right, because `λ u_n = P (f + K u_n)` already forces
it. -/
theorem isProjectionSolution_iff_smul_sub_comp {μ : 𝕜} (hμ : μ ≠ 0) {K P : X →L[𝕜] X}
    (hP : IsIdempotentElem P) (f un : X) :
    IsProjectionSolution μ K P f un ↔ (μ • 1 - P ∘L K : X →L[𝕜] X) un = P f := by
  constructor
  · rintro ⟨hmem, heq⟩
    have hPun : P un = un := IsProjectionMethodSolution.apply_eq_self hP ⟨hmem, heq⟩
    rw [← heq]
    simp only [sub_apply, smul_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply, map_sub,
      map_smul, hPun]
  · intro heq
    have h1 : μ • un - P (K un) = P f := by
      simpa only [sub_apply, smul_apply, one_apply_eq_self,
        ContinuousLinearMap.comp_apply] using heq
    have h2 : P (f + K un) = μ • un := by rw [map_add, ← h1]; abel
    have hun : (P : X →ₗ[𝕜] X) (μ⁻¹ • (f + K un)) = un := by
      change P (μ⁻¹ • (f + K un)) = un
      rw [map_smul, h2, smul_smul, inv_mul_cancel₀ hμ, one_smul]
    have hmem : un ∈ LinearMap.range (P : X →ₗ[𝕜] X) := ⟨_, hun⟩
    refine ⟨hmem, ?_⟩
    have hPun : P un = un := by
      obtain ⟨v, hv⟩ := hmem
      rw [← hv]
      exact DFunLike.congr_fun hP v
    simp only [sub_apply, smul_apply, one_apply_eq_self, map_sub, map_smul, hPun]
    exact h1

/-- **(12.1.17)**: a nonzero bounded projection has norm at least one, because `‖P‖ = ‖P²‖ ≤ ‖P‖²`.
The book records it because `‖P_n‖` is the factor that enters the error constants of the projection
method, in (12.1.24) and in the hypothesis of Theorem 12.1.2; so no choice of `P_n` pushes those
constants below the value they take at `‖P_n‖ = 1`. -/
theorem equation_12_1_17 {P : X →L[𝕜] X} (hP : IsIdempotentElem P) (hP0 : P ≠ 0) : 1 ≤ ‖P‖ := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.1 hP0
  rw [zero_apply] at hx
  have hPP : P (P x) = P x := DFunLike.congr_fun hP x
  have hpos : 0 < ‖P x‖ := norm_pos_iff.2 hx
  have hle : ‖P x‖ ≤ ‖P‖ * ‖P x‖ :=
    calc ‖P x‖ = ‖P (P x)‖ := by rw [hPP]
      _ ≤ ‖P‖ * ‖P x‖ := ContinuousLinearMap.le_opNorm _ _
  nlinarith

/-! ### The two convergence lemmas -/

/-- **Lemma 12.1.3**: a pointwise convergent sequence of bounded linear operators on a Banach
space converges uniformly on every compact subset. -/
theorem lemma_12_1_3 [CompleteSpace X] {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    {A : ℕ → X →L[𝕜] W} {L : X →L[𝕜] W} (hA : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (L x)))
    {S : Set X} (hS : IsCompact S) :
    TendstoUniformlyOn (fun n => (A n : X → W)) L atTop S :=
  tendstoUniformlyOn_of_tendsto_of_isCompact hA hS

/-- **Lemma 12.1.4**: if `P_n u → u` for every `u` of a Banach space and `K` is a compact operator,
then `‖K - P_n K‖ → 0`.  This is the hypothesis (12.1.21) of Theorem 12.1.2, and it holds for
*every* compact `K` whenever the projections converge pointwise. -/
theorem lemma_12_1_4 [CompleteSpace X] {K : X →L[𝕜] X} (hK : IsCompactOperator K)
    {P : ℕ → X →L[𝕜] X} (hP : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x)) :
    Tendsto (fun n => ‖K - P n ∘L K‖) atTop (𝓝 0) := by
  have hA : ∀ x, Tendsto (fun n => (1 - P n : X →L[𝕜] X) x) atTop (𝓝 0) := by
    intro x
    have h : Tendsto (fun n => x - P n x) atTop (𝓝 (x - x)) := tendsto_const_nhds.sub (hP x)
    rw [sub_self] at h
    simpa using h
  have hid : ∀ n, ((1 - P n : X →L[𝕜] X) ∘L K : X →L[𝕜] X) = K - P n ∘L K := by
    intro n
    ext x
    simp
  simpa only [hid] using tendsto_opNorm_comp_of_isCompactOperator hA hK

/-! ### Stability and convergence -/

/-- **Theorem 12.1.2**, the stability half (12.1.22): if `λ - K` is invertible and the projection
error `‖K - P K‖` satisfies (12.1.25), namely `‖(λ - K)⁻¹‖ ‖K - P K‖ < 1`, then `λ - P K` is
invertible with

`‖(λ - P K)⁻¹‖ ≤ ‖(λ - K)⁻¹‖ / (1 - ‖(λ - K)⁻¹‖ ‖K - P K‖)`,

and the projection equations (12.1.18) are uniquely solvable for every right-hand side.  By
Lemma 12.1.4 the hypothesis holds for all large `n` as soon as `K` is compact and `P_n u → u`, so
the bound is uniform in `n`. -/
theorem theorem_12_1_2 [CompleteSpace X] {μ : 𝕜} (hμ : μ ≠ 0) {K P : X →L[𝕜] X}
    (hP : IsIdempotentElem P) (e : X ≃L[𝕜] X) (he : (e : X →L[𝕜] X) = μ • 1 - K)
    (h : ‖(e.symm : X →L[𝕜] X)‖ * ‖K - P ∘L K‖ < 1) :
    ∃ e' : X ≃L[𝕜] X, (e' : X →L[𝕜] X) = μ • 1 - P ∘L K ∧
      ‖(e'.symm : X →L[𝕜] X)‖ ≤
        ‖(e.symm : X →L[𝕜] X)‖ / (1 - ‖(e.symm : X →L[𝕜] X)‖ * ‖K - P ∘L K‖) ∧
      ∀ f : X, ∃! un : X, IsProjectionSolution μ K P f un := by
  obtain ⟨e', he'coe, he'norm⟩ := SecondKind.exists_equiv_of_projection e he h
  refine ⟨e', he'coe, he'norm, fun f => ?_⟩
  have hiff : ∀ un : X,
      IsProjectionSolution μ K P f un ↔ (μ • 1 - P ∘L K : X →L[𝕜] X) un = P f :=
    fun un => isProjectionSolution_iff_smul_sub_comp hμ hP f un
  simp only [hiff]
  refine ⟨e'.symm (P f), ?_, ?_⟩
  · dsimp only
    rw [← he'coe, ContinuousLinearEquiv.coe_coe, e'.apply_symm_apply]
  · intro y hy
    rw [← he'coe, ContinuousLinearEquiv.coe_coe] at hy
    rw [← hy, e'.symm_apply_apply]

/-- **(12.1.23)**, the error identity of a projection method: `u - u_n = λ (λ - P K)⁻¹ (u - P u)`.
Everything in the convergence analysis is read off it. -/
theorem equation_12_1_23 {μ : 𝕜} {K P : X →L[𝕜] X} (hP : IsIdempotentElem P) {e' : X ≃L[𝕜] X}
    (he' : (e' : X →L[𝕜] X) = μ • 1 - P ∘L K) {f u un : X}
    (hu : (μ • 1 - K : X →L[𝕜] X) u = f) (hun : IsProjectionSolution μ K P f un) :
    u - un = e'.symm (μ • (u - P u)) := by
  have hkey := SecondKind.sub_projection_eq hP hu hun
  rw [← hkey, ← he', ContinuousLinearEquiv.coe_coe, e'.symm_apply_apply]

/-- **(12.1.24)**, the two-sided estimate for a projection method:

`|λ| ‖u - P u‖ ≤ ‖λ - P K‖ ‖u - u_n‖` and `‖u - u_n‖ ≤ |λ| ‖(λ - P K)⁻¹‖ ‖u - P u‖`.

The book divides by `‖λ - P K‖`; the equivalent product form is stated here, so that no quotient
by a possibly vanishing norm occurs.  With the uniform bound of `theorem_12_1_2` the two
inequalities say that the error of the method and the approximation error of the trial space tend
to zero at exactly the same rate. -/
theorem equation_12_1_24 {μ : 𝕜} {K P : X →L[𝕜] X} (hP : IsIdempotentElem P) {e' : X ≃L[𝕜] X}
    (he' : (e' : X →L[𝕜] X) = μ • 1 - P ∘L K) {f u un : X}
    (hu : (μ • 1 - K : X →L[𝕜] X) u = f) (hun : IsProjectionSolution μ K P f un) :
    ‖μ‖ * ‖u - P u‖ ≤ ‖(μ • 1 - P ∘L K : X →L[𝕜] X)‖ * ‖u - un‖ ∧
      ‖u - un‖ ≤ ‖μ‖ * ‖(e'.symm : X →L[𝕜] X)‖ * ‖u - P u‖ :=
  ⟨SecondKind.norm_smul_sub_le_of_projection hP hu hun,
    SecondKind.norm_sub_le_of_projection hP he' hu hun⟩

/-! ### The asymptotic constant -/

/-- The geometric-series bound `A / (1 - A c) ≤ A (1 + 2 A c)`, valid as soon as `A c ≤ 1 / 2`.
It is what turns the constant of `theorem_12_1_2` into the constant of the exact inverse times
`1 + γ_n` with `γ_n → 0`. -/
private theorem div_le_mul_one_add {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (h : A * c ≤ 1 / 2) :
    A / (1 - A * c) ≤ A * (1 + 2 * (A * c)) := by
  have hx : 0 ≤ A * c := mul_nonneg hA hc
  have hpos : 0 < 1 - A * c := by linarith
  have h2 : 0 ≤ 1 - 2 * (A * c) := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith [mul_nonneg (mul_nonneg hA hx) h2]

/-- The smallness facts about the projection error that both exercises use: eventually
`‖(λ - K)⁻¹‖ ‖K - P_n K‖ < 1/2`, and then the inverse `(λ - P_n K)⁻¹` exists and is bounded both by
`‖(λ - K)⁻¹‖ (1 + γ_n)` with `γ_n = 2 ‖(λ - K)⁻¹‖ ‖K - P_n K‖` and, more crudely, by
`2 ‖(λ - K)⁻¹‖`. -/
private theorem eventually_exists_equiv [CompleteSpace X] {μ : 𝕜} {K : X →L[𝕜] X}
    {P : ℕ → X →L[𝕜] X} {e : X ≃L[𝕜] X} (he : (e : X →L[𝕜] X) = μ • 1 - K)
    (hc : Tendsto (fun n => ‖K - P n ∘L K‖) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∃ e' : X ≃L[𝕜] X, (e' : X →L[𝕜] X) = μ • 1 - P n ∘L K ∧
      ‖(e'.symm : X →L[𝕜] X)‖ ≤
        ‖(e.symm : X →L[𝕜] X)‖ *
          (1 + 2 * (‖(e.symm : X →L[𝕜] X)‖ * ‖K - P n ∘L K‖)) ∧
      ‖(e'.symm : X →L[𝕜] X)‖ ≤ 2 * ‖(e.symm : X →L[𝕜] X)‖ := by
  have hA : (0 : ℝ) ≤ ‖(e.symm : X →L[𝕜] X)‖ := norm_nonneg _
  have hhalf : ∀ᶠ n in atTop, ‖(e.symm : X →L[𝕜] X)‖ * ‖K - P n ∘L K‖ < 1 / 2 := by
    have h0 : Tendsto (fun n => ‖(e.symm : X →L[𝕜] X)‖ * ‖K - P n ∘L K‖) atTop (𝓝 0) := by
      simpa using hc.const_mul ‖(e.symm : X →L[𝕜] X)‖
    exact h0.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hhalf] with n hn
  obtain ⟨e', he'coe, he'norm⟩ :=
    SecondKind.exists_equiv_of_projection e he (by linarith)
  have hbound := he'norm.trans (div_le_mul_one_add hA (norm_nonneg _) hn.le)
  exact ⟨e', he'coe, hbound, hbound.trans (by nlinarith)⟩

/-- **Exercise 12.1.3**: the upper bound of (12.1.24) can be sharpened so that its constant is the
one built from the *exact* inverse,

`‖u - u_n‖ ≤ |λ| (1 + γ_n) ‖(λ - K)⁻¹‖ ‖u - P_n u‖` with `γ_n → 0`.

The explicit `γ_n` produced here is `2 ‖(λ - K)⁻¹‖ ‖K - P_n K‖`, which tends to zero by the
hypothesis (12.1.21) — for a compact `K` and pointwise convergent projections, by
Lemma 12.1.4. -/
theorem exercise_12_1_3 [CompleteSpace X] {μ : 𝕜} {K : X →L[𝕜] X}
    {P : ℕ → X →L[𝕜] X} (hP : ∀ n, IsIdempotentElem (P n)) {e : X ≃L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - K)
    (hc : Tendsto (fun n => ‖K - P n ∘L K‖) atTop (𝓝 0)) :
    ∃ γ : ℕ → ℝ, Tendsto γ atTop (𝓝 0) ∧ ∀ᶠ n in atTop, ∀ f u un : X,
      (μ • 1 - K : X →L[𝕜] X) u = f → IsProjectionSolution μ K (P n) f un →
        ‖u - un‖ ≤ ‖μ‖ * (1 + γ n) * ‖(e.symm : X →L[𝕜] X)‖ * ‖u - P n u‖ := by
  refine ⟨fun n => 2 * (‖(e.symm : X →L[𝕜] X)‖ * ‖K - P n ∘L K‖), ?_, ?_⟩
  · simpa using (hc.const_mul ‖(e.symm : X →L[𝕜] X)‖).const_mul 2
  filter_upwards [eventually_exists_equiv he hc] with n hn f u un hu hun
  obtain ⟨e', he'coe, he'norm, -⟩ := hn
  refine (SecondKind.norm_sub_le_of_projection (hP n) he'coe hu hun).trans ?_
  have h1 : ‖μ‖ * ‖(e'.symm : X →L[𝕜] X)‖ ≤
      ‖μ‖ * (‖(e.symm : X →L[𝕜] X)‖ *
        (1 + 2 * (‖(e.symm : X →L[𝕜] X)‖ * ‖K - P n ∘L K‖))) :=
    mul_le_mul_of_nonneg_left he'norm (norm_nonneg _)
  have h2 : ‖μ‖ * (1 + 2 * (‖(e.symm : X →L[𝕜] X)‖ * ‖K - P n ∘L K‖)) *
      ‖(e.symm : X →L[𝕜] X)‖ =
      ‖μ‖ * (‖(e.symm : X →L[𝕜] X)‖ *
        (1 + 2 * (‖(e.symm : X →L[𝕜] X)‖ * ‖K - P n ∘L K‖))) := by ring
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

/-- **Exercise 12.1.4**: split the error as `e_n = e_n^{(1)} + e_n^{(2)}` with the leading term
`e_n^{(1)} = λ (λ - K)⁻¹ (u - P_n u)` built from the *exact* inverse, as in (12.1.31).  Then

`‖e_n^{(2)}‖ ≤ δ_n ‖e_n^{(1)}‖` with `δ_n → 0`,

so the whole of the error is asymptotically the computable leading term.  The explicit `δ_n` is
again `2 ‖(λ - K)⁻¹‖ ‖K - P_n K‖`, because `(λ - P_n K) e_n^{(2)} = (P_n K - K) e_n^{(1)}`. -/
theorem exercise_12_1_4 [CompleteSpace X] {μ : 𝕜} {K : X →L[𝕜] X}
    {P : ℕ → X →L[𝕜] X} (hP : ∀ n, IsIdempotentElem (P n)) {e : X ≃L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - K)
    (hc : Tendsto (fun n => ‖K - P n ∘L K‖) atTop (𝓝 0)) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ᶠ n in atTop, ∀ f u un : X,
      (μ • 1 - K : X →L[𝕜] X) u = f → IsProjectionSolution μ K (P n) f un →
        ‖u - un - μ • e.symm (u - P n u)‖ ≤ δ n * ‖μ • e.symm (u - P n u)‖ := by
  refine ⟨fun n => 2 * (‖(e.symm : X →L[𝕜] X)‖ * ‖K - P n ∘L K‖), ?_, ?_⟩
  · simpa using (hc.const_mul ‖(e.symm : X →L[𝕜] X)‖).const_mul 2
  filter_upwards [eventually_exists_equiv he hc] with n hn f u un hu hun
  obtain ⟨e', he'coe, -, he'norm⟩ := hn
  set y : X := μ • e.symm (u - P n u) with hy
  -- the leading term solves the exact equation with the same right-hand side
  have hy1 : (μ • 1 - K : X →L[𝕜] X) y = μ • (u - P n u) := by
    rw [hy, map_smul, ← he, ContinuousLinearEquiv.coe_coe, e.apply_symm_apply]
  -- hence the remainder solves the projected equation with a small right-hand side
  have hkey : (μ • 1 - P n ∘L K : X →L[𝕜] X) (u - un - y)
      = -((K - P n ∘L K : X →L[𝕜] X) y) := by
    have hsplit : (μ • 1 - P n ∘L K : X →L[𝕜] X) y
        = (μ • 1 - K : X →L[𝕜] X) y + (K - P n ∘L K : X →L[𝕜] X) y := by
      simp only [sub_apply, smul_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply]
      abel
    rw [map_sub, SecondKind.sub_projection_eq (hP n) hu hun, hsplit, hy1]
    abel
  have hsol : u - un - y = e'.symm (-((K - P n ∘L K : X →L[𝕜] X) y)) := by
    rw [← hkey, ← he'coe, ContinuousLinearEquiv.coe_coe, e'.symm_apply_apply]
  rw [hsol]
  calc ‖e'.symm (-((K - P n ∘L K : X →L[𝕜] X) y))‖
      ≤ ‖(e'.symm : X →L[𝕜] X)‖ * ‖(K - P n ∘L K : X →L[𝕜] X) y‖ := by
        rw [← norm_neg ((K - P n ∘L K : X →L[𝕜] X) y)]
        exact ContinuousLinearMap.le_opNorm (e'.symm : X →L[𝕜] X) _
    _ ≤ 2 * ‖(e.symm : X →L[𝕜] X)‖ * (‖K - P n ∘L K‖ * ‖y‖) :=
        mul_le_mul he'norm (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _) (by positivity)
    _ = 2 * (‖(e.symm : X →L[𝕜] X)‖ * ‖K - P n ∘L K‖) * ‖y‖ := by ring

end AtkinsonHan.Chapter12
