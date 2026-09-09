import Mathlib.Analysis.Complex.ExponentialBounds
import Numlib.Approximation.CompositeQuadrature
import Numlib.Approximation.Interpolation
import Numlib.Approximation.PiecewiseLinearL2
import Numlib.IntegralEquations.Basic
import NumlibSurface.AtkinsonHan.Chapter12.Section01

/-!
# Atkinson–Han §12.3: iterated projection methods

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §12.3.

Sloan's observation: one fixed-point sweep applied to a projection solution `u_n` of
`(λ - K) u = f` produces an approximation `û_n` whose error carries an extra factor `I - P_n`
inside `K`, and therefore converges faster, whatever the size of `‖K‖`.  As in §12.1 the book's
scalar `λ` is written `μ`, `λ` being Lean's lambda binder, and the book's sequence of projections
is a single bounded idempotent `P`.

## Main results

* `iteratedSolution` — (12.3.1), the iterated projection solution `û_n = (f + K u_n)/λ`, with
  `equation_12_3_2` and `equation_12_3_3` for the identities `P û_n = u_n` and
  `(λ - K P) û_n = f`.
* `lemma_12_3_1` — Jacobson's identity: `λ - A B` is invertible if and only if `λ - B A` is, and
  then `(λ - B A)⁻¹ = (1/λ) [I + B (λ - A B)⁻¹ A]`, which is (12.3.9).
* `lemma_12_3_1_projection` — the instance `A = P`, `B = K` that §12.3 uses: an inverse of
  `λ - P K`, which `theorem_12_1_2` supplies, produces one of `λ - K P` with the same formula and
  a bound on its norm.
* `equation_12_3_11` — the error equation `(λ - K P) (u - û_n) = K (I - P) u` and the resulting
  bound `‖u - û_n‖ ≤ ‖(λ - K P)⁻¹‖ ‖K (I - P)‖ ‖u - P u‖`, which is Sloan superconvergence: one
  factor of the approximation error better than the bound (12.1.24) for `u_n` itself.
* `quadInterpCLM` — the piecewise quadratic interpolatory projection (12.3.24), the degree two
  case of the backbone `piecewisePolyInterpCLM` on the uniform mesh, with the Lebesgue bound
  `norm_quadInterpCLM_le` uniform in the mesh and the error bound `norm_sub_quadInterpCLM_le`,
  which is (12.3.27).
* `norm_kernelCLM_sub_quadInterpCLM_le` — **(12.3.31)**, `K (I - P_n) u = 𝒪(h⁴)`.
* `theorem_12_3_3` — the superconvergence of iterated piecewise quadratic collocation:
  (12.3.32), (12.3.33) and the superconvergence (12.3.34) at the mesh points.
* `example_12_3_2` — the iterated Galerkin method for `50 u - K u = f` with `k(x, y) = e^{xy}` over
  the *discontinuous* piecewise linear functions of the uniform mesh of width `h = 1/n`: the rates
  `‖u - u_n‖ = 𝒪(h²)` (12.3.19) and `‖u - û_n‖ = 𝒪(h⁴)` (12.3.20).  Its two inputs are
  `norm_sub_comp_expKernelCLM_le`, the `‖(I - P_n) K*‖ = 𝒪(h²)` that the book calls straightforward
  and does not prove, and `norm_sub_discGalerkinProj_expSolution_le`, which is `‖u - P_n u‖ =
  𝒪(h²)`; both rest on the backbone `discPiecewiseLinearProjCLM` and its approximation order.

## Not formalized here

The concrete parts of §12.3.2 and the linear system for the iterated collocation solution.

**Table 12.2** of Example 12.3.2, which is measured error data for `n = 2, 4, 8` obtained by running
the method, not mathematics.  What the table confirms — the pair of rates (12.3.19) and (12.3.20) —
is `example_12_3_2`, and the constants there are existentially quantified, as the book leaves them
unspecified too.

## Conventions

The book derives the bound of `equation_12_3_11` for an *orthogonal* projection in a Hilbert
space, from `(I - P_n)² = I - P_n`.  Only that idempotency is used, so the statement here asks
for nothing but `IsIdempotentElem P` and holds on a Banach space; the Galerkin case is the
specialization to an orthogonal projection.

Theorem 12.3.3 is proved for a kernel *Lipschitz* in `y` rather than the book's continuously
differentiable one — a weaker hypothesis, which a `C¹` kernel on the compact square satisfies.
That is what the route to (12.3.31) taken here needs: the book's proof differentiates a Newton
divided difference in `y`, and `Numlib/Approximation/DividedDifference` has no derivative rule;
splitting the kernel on each panel replaces that step by the Simpson panel error.
-/

open Filter Topology

namespace AtkinsonHan.Chapter12

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-! ### The iterated projection solution -/

/-- **(12.3.1)**, the iterated projection solution `û_n = (f + K u_n)/λ`: one sweep of the fixed
point iteration `u ↦ (f + K u)/λ` applied to the projection solution `u_n` of (12.1.18).

This is the backbone `SecondKind.iterated`; it is defined for every `u_n`, and the two identities
`equation_12_3_2` and `equation_12_3_3` are what use that `u_n` is a projection solution. -/
noncomputable abbrev iteratedSolution (μ : 𝕜) (K : X →L[𝕜] X) (f un : X) : X :=
  SecondKind.iterated μ K f un

/-- **(12.3.2)**: the iterated solution projects back onto the projection solution,
`P û_n = u_n`.  So `û_n` is an improvement of `u_n` that costs one application of `K` and loses
none of its information. -/
theorem equation_12_3_2 {μ : 𝕜} (hμ : μ ≠ 0) {K P : X →L[𝕜] X} (hP : IsIdempotentElem P)
    {f un : X} (hun : IsProjectionSolution μ K P f un) :
    P (iteratedSolution μ K f un) = un :=
  SecondKind.apply_iterated hμ hP hun

/-- **(12.3.3)**: the iterated solution satisfies `(λ - K P) û_n = f`, the companion of the
projection equations `(λ - P K) u_n = P f` under Jacobson's identity `lemma_12_3_1`. -/
theorem equation_12_3_3 {μ : 𝕜} (hμ : μ ≠ 0) {K P : X →L[𝕜] X} (hP : IsIdempotentElem P)
    {f un : X} (hun : IsProjectionSolution μ K P f un) :
    (μ • 1 - K ∘L P : X →L[𝕜] X) (iteratedSolution μ K f un) = f :=
  SecondKind.smul_sub_comp_iterated hμ hP hun

/-! ### Jacobson's identity -/

/-- **Lemma 12.3.1**: for bounded operators `A`, `B` on a Banach space and `λ ≠ 0`, the operator
`λ - A B` is invertible if and only if `λ - B A` is, and then

`(λ - B A)⁻¹ = (1/λ) [I + B (λ - A B)⁻¹ A]`,

which is **(12.3.9)**.  Neither compactness nor completeness of the space is used: the formula is
checked by multiplying out, and the inverse produced is a genuine two-sided one. -/
theorem lemma_12_3_1 {μ : 𝕜} (hμ : μ ≠ 0) (A B : X →L[𝕜] X) :
    (IsUnit (μ • 1 - A ∘L B : X →L[𝕜] X) ↔ IsUnit (μ • 1 - B ∘L A : X →L[𝕜] X)) ∧
      ∀ e : X ≃L[𝕜] X, (e : X →L[𝕜] X) = μ • 1 - A ∘L B →
        ∃ e' : X ≃L[𝕜] X, (e' : X →L[𝕜] X) = μ • 1 - B ∘L A ∧
          (e'.symm : X →L[𝕜] X) = μ⁻¹ • (1 + B ∘L ((e.symm : X →L[𝕜] X) ∘L A)) :=
  ⟨SecondKind.isUnit_smul_sub_comp_comm hμ A B,
    fun e he => SecondKind.exists_equiv_smul_sub_comp_comm hμ e he⟩

/-- **Lemma 12.3.1 applied to the projection method**, `A = P` and `B = K`: from the inverse of
`λ - P K` that `theorem_12_1_2` produces, the operator `λ - K P` of (12.3.3) is invertible with

`(λ - K P)⁻¹ = (1/λ) [I + K (λ - P K)⁻¹ P]` and
`‖(λ - K P)⁻¹‖ ≤ (1 + ‖K‖ ‖(λ - P K)⁻¹‖ ‖P‖) / |λ|`.

The uniform bound of `theorem_12_1_2` on `‖(λ - P_n K)⁻¹‖` therefore gives a uniform bound on
`‖(λ - K P_n)⁻¹‖`, which is what makes `equation_12_3_11` an error estimate rather than an
identity. -/
theorem lemma_12_3_1_projection {μ : 𝕜} (hμ : μ ≠ 0) (K P : X →L[𝕜] X) {e' : X ≃L[𝕜] X}
    (he' : (e' : X →L[𝕜] X) = μ • 1 - P ∘L K) :
    ∃ e'' : X ≃L[𝕜] X, (e'' : X →L[𝕜] X) = μ • 1 - K ∘L P ∧
      (e''.symm : X →L[𝕜] X) = μ⁻¹ • (1 + K ∘L ((e'.symm : X →L[𝕜] X) ∘L P)) ∧
      ‖(e''.symm : X →L[𝕜] X)‖ ≤
        ‖μ‖⁻¹ * (1 + ‖K‖ * (‖(e'.symm : X →L[𝕜] X)‖ * ‖P‖)) := by
  obtain ⟨e'', he''coe, he''symm⟩ := SecondKind.exists_equiv_smul_sub_comp_comm hμ e' he'
  refine ⟨e'', he''coe, he''symm, ?_⟩
  rw [he''symm, norm_smul, norm_inv]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_add_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le ?_)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))

/-! ### The error of the iterated solution -/

/-- **(12.3.11)** and Sloan superconvergence: the error of the iterated projection solution
satisfies

`(λ - K P) (u - û_n) = K (I - P) u`,

and hence `‖u - û_n‖ ≤ ‖(λ - K P)⁻¹‖ ‖K (I - P)‖ ‖u - P u‖`.

The right-hand side of the identity carries the factor `I - P` *inside* `K`, and `I - P` is
idempotent, so it may be inserted twice: the bound is `‖K (I - P)‖` times the approximation error
`‖u - P u‖`, one factor better than the bound `‖u - u_n‖ ≤ |λ| ‖(λ - P K)⁻¹‖ ‖u - P u‖` of
(12.1.24) for `u_n` itself, since `‖K (I - P_n)‖ → 0` for a compact `K`.  The book argues on a
Hilbert space with `P` an orthogonal projection; only `IsIdempotentElem P` is used. -/
theorem equation_12_3_11 {μ : 𝕜} (hμ : μ ≠ 0) {K P : X →L[𝕜] X} (hP : IsIdempotentElem P)
    {e'' : X ≃L[𝕜] X} (he'' : (e'' : X →L[𝕜] X) = μ • 1 - K ∘L P) {f u un : X}
    (hu : (μ • 1 - K : X →L[𝕜] X) u = f) (hun : IsProjectionSolution μ K P f un) :
    (μ • 1 - K ∘L P : X →L[𝕜] X) (u - iteratedSolution μ K f un) = K (u - P u) ∧
      ‖u - iteratedSolution μ K f un‖ ≤
        ‖(e''.symm : X →L[𝕜] X)‖ * ‖K ∘L (1 - P)‖ * ‖u - P u‖ := by
  have hkey : (μ • 1 - K ∘L P : X →L[𝕜] X) (u - iteratedSolution μ K f un) = K (u - P u) :=
    SecondKind.iterated_error_eq hμ hP hu hun
  refine ⟨hkey, ?_⟩
  -- `I - P` is idempotent, so the error is `K (I - P)` applied to the approximation error
  have hPP : P (P u) = P u := DFunLike.congr_fun hP u
  have hins : K (u - P u) = (K ∘L (1 - P) : X →L[𝕜] X) (u - P u) := by
    simp only [ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self, map_sub, hPP,
      sub_self, map_zero, sub_zero]
  have herr : u - iteratedSolution μ K f un = e''.symm ((K ∘L (1 - P) : X →L[𝕜] X) (u - P u)) := by
    rw [← hins, ← hkey, ← he'', ContinuousLinearEquiv.coe_coe, e''.symm_apply_apply]
  rw [herr]
  calc ‖e''.symm ((K ∘L (1 - P) : X →L[𝕜] X) (u - P u))‖
      ≤ ‖(e''.symm : X →L[𝕜] X)‖ * ‖(K ∘L (1 - P) : X →L[𝕜] X) (u - P u)‖ :=
        ContinuousLinearMap.le_opNorm (e''.symm : X →L[𝕜] X) _
    _ ≤ ‖(e''.symm : X →L[𝕜] X)‖ * (‖K ∘L (1 - P)‖ * ‖u - P u‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖(e''.symm : X →L[𝕜] X)‖ * ‖K ∘L (1 - P)‖ * ‖u - P u‖ := by ring

/-! ### The piecewise quadratic interpolatory projection -/

section PiecewiseQuadratic

variable {a b : ℝ}

/-- The `j`-th point `a + j (b - a)/n` of the uniform mesh of `[a, b]` into `n` subintervals, as a
point of the interval. -/
noncomputable def meshPoint (hab : a ≤ b) (n j : ℕ) : Set.Icc a b :=
  Set.projIcc a b hab (a + (j : ℝ) * ((b - a) / n))

/-- The value of a mesh point of index at most `n`, where the clamping does nothing. -/
theorem coe_meshPoint (hab : a ≤ b) {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    (meshPoint hab n j : ℝ) = a + (j : ℝ) * ((b - a) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hba : (0 : ℝ) ≤ b - a := sub_nonneg.mpr hab
  have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj
  have hnonneg : (0 : ℝ) ≤ (j : ℝ) * ((b - a) / n) := by positivity
  have hcan : (n : ℝ) * ((b - a) / n) = b - a := by field_simp
  have hle : (j : ℝ) * ((b - a) / n) ≤ b - a := by
    have h1 : (j : ℝ) * ((b - a) / n) ≤ (n : ℝ) * ((b - a) / n) :=
      mul_le_mul_of_nonneg_right hjn (by positivity)
    rwa [hcan] at h1
  rw [meshPoint, Set.coe_projIcc, min_eq_right (by linarith), max_eq_right (by linarith)]

/-- Distinct indices at most `n` give distinct mesh points. -/
theorem meshPoint_inj (hab : a < b) {n j k : ℕ} (hn : 0 < n) (hj : j ≤ n) (hk : k ≤ n)
    (h : (meshPoint hab.le n j : ℝ) = (meshPoint hab.le n k : ℝ)) : j = k := by
  have hδ : (0 : ℝ) < (b - a) / n := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_pos (sub_pos.mpr hab) this
  rw [coe_meshPoint hab.le hn hj, coe_meshPoint hab.le hn hk] at h
  have hmul : (j : ℝ) * ((b - a) / n) = (k : ℝ) * ((b - a) / n) := by linarith
  exact_mod_cast mul_right_cancel₀ (ne_of_gt hδ) hmul

/-- The **mesh size** `h = (b - a)/n` of the piecewise quadratic method of §12.3.2, whose `p + 1`
panels carry `n = 2 (p + 1)` subintervals of the uniform mesh. -/
noncomputable def quadMesh (a b : ℝ) (p : ℕ) : ℝ := (b - a) / (2 * (p + 1))

theorem quadMesh_pos (hab : a < b) (p : ℕ) : 0 < quadMesh a b p :=
  div_pos (sub_pos.mpr hab) (by positivity)

/-- The breakpoints `x_{2k} = a + 2 k h` of the piecewise quadratic trial space of §12.3.2: the
`p + 1` panels are `[x_0, x_2], …, [x_{n-2}, x_n]` with `n = 2 (p + 1)`. -/
noncomputable def quadBreak (hab : a ≤ b) (p k : ℕ) : Set.Icc a b :=
  meshPoint hab (2 * (p + 1)) (2 * k)

/-- The three interpolation nodes `x_{2k}, x_{2k+1}, x_{2k+2}` of the `k`-th panel. -/
noncomputable def quadNode (hab : a ≤ b) (p k : ℕ) (i : Fin 3) : Set.Icc a b :=
  meshPoint hab (2 * (p + 1)) (2 * k + (i : ℕ))

theorem coe_quadBreak (hab : a ≤ b) {p k : ℕ} (hk : k ≤ p + 1) :
    (quadBreak hab p k : ℝ) = a + 2 * (k : ℝ) * quadMesh a b p := by
  rw [quadBreak, coe_meshPoint hab (by omega) (by omega), quadMesh]
  push_cast
  ring

theorem coe_quadNode (hab : a ≤ b) {p k : ℕ} (hk : k ≤ p) (i : Fin 3) :
    (quadNode hab p k i : ℝ) = a + (2 * (k : ℝ) + ((i : ℕ) : ℝ)) * quadMesh a b p := by
  have hi := i.isLt
  rw [quadNode, coe_meshPoint hab (by omega) (by omega), quadMesh]
  push_cast
  ring

/-- **The nodes of the piecewise quadratic method form a panel node system**: the panels are the
`p + 1` intervals `[x_{2k}, x_{2k+2}]`, and each carries the three nodes `x_{2k}, x_{2k+1},
x_{2k+2}`, of which the outer two are the endpoints of the panel — which is what makes the
interpolant continuous. -/
theorem isPanelNodes_quad (hab : a < b) (p : ℕ) :
    IsPanelNodes p 2 (quadBreak hab.le p) (quadNode hab.le p) := by
  have hδ : 0 < quadMesh a b p := quadMesh_pos hab p
  refine ⟨fun k hk => ?_, ?_, ?_, fun k hk i => ?_, fun k hk => ?_, fun k hk => ?_,
    fun k hk => ?_⟩
  · rw [coe_quadBreak hab.le (by omega), coe_quadBreak hab.le (by omega)]
    push_cast
    linarith
  · rw [coe_quadBreak hab.le (by omega)]
    norm_num
  · rw [coe_quadBreak hab.le (le_refl (p + 1)), quadMesh]
    push_cast
    field_simp
    ring
  · have hi := i.isLt
    have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    have hi2 : ((i : ℕ) : ℝ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.mp hi
    rw [coe_quadNode hab.le hk i, coe_quadBreak hab.le (by omega),
      coe_quadBreak hab.le (by omega)]
    push_cast
    constructor <;> nlinarith
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hidx : 2 * k + (i : ℕ) = 2 * k + (j : ℕ) :=
      meshPoint_inj hab (by omega) (by omega) (by omega) hij
    exact Fin.ext (by omega)
  · simp only [quadNode, quadBreak, Fin.val_zero, Nat.add_zero]
  · have hidx : 2 * k + ((Fin.last 2 : Fin 3) : ℕ) = 2 * (k + 1) := by
      simp only [Fin.val_last]
      omega
    rw [quadNode, quadBreak, hidx]

/-- The panels of the piecewise quadratic method all have length `2 h`. -/
theorem quadBreak_sub (hab : a < b) {p k : ℕ} (hk : k ≤ p) :
    (quadBreak hab.le p (k + 1) : ℝ) - (quadBreak hab.le p k : ℝ) = 2 * quadMesh a b p := by
  rw [coe_quadBreak hab.le (by omega), coe_quadBreak hab.le (by omega)]
  push_cast
  ring

/-- The nodes of one panel are `h` apart, so the crude separation bound applies with `D = 2 h` and
`d = h`. -/
theorem quadNode_sep (hab : a < b) {p k : ℕ} (hk : k ≤ p) (i i' : Fin 3) (hii : i ≠ i') :
    quadMesh a b p ≤ |((quadNode hab.le p k i : ℝ)) - ((quadNode hab.le p k i' : ℝ))| := by
  have hδ : 0 < quadMesh a b p := quadMesh_pos hab p
  have hne : ((i : ℕ) : ℝ) ≠ ((i' : ℕ) : ℝ) := by
    exact_mod_cast fun hc => hii (Fin.ext (by exact_mod_cast hc))
  have hone : (1 : ℝ) ≤ |((i : ℕ) : ℝ) - ((i' : ℕ) : ℝ)| := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rw [abs_of_nonpos (by linarith)]
      have : ((i : ℕ) : ℝ) + 1 ≤ ((i' : ℕ) : ℝ) := by
        have : (i : ℕ) < (i' : ℕ) := by exact_mod_cast hlt
        exact_mod_cast this
      linarith
    · rw [abs_of_nonneg (by linarith)]
      have : ((i' : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by
        have : (i' : ℕ) < (i : ℕ) := by exact_mod_cast hlt
        exact_mod_cast this
      linarith
  rw [coe_quadNode hab.le hk i, coe_quadNode hab.le hk i']
  have hrw : a + (2 * (k : ℝ) + ((i : ℕ) : ℝ)) * quadMesh a b p
      - (a + (2 * (k : ℝ) + ((i' : ℕ) : ℝ)) * quadMesh a b p)
      = (((i : ℕ) : ℝ) - ((i' : ℕ) : ℝ)) * quadMesh a b p := by ring
  rw [hrw, abs_mul, abs_of_pos hδ]
  nlinarith

/-- **The Lebesgue bound of the piecewise quadratic projection**, uniformly in the mesh: the
crude bound `(m + 1) (D/d)^m` of `isPanelLebesgueBound_of_sep` with `D = 2 h` and `d = h`. -/
theorem isPanelLebesgueBound_quad (hab : a < b) (p : ℕ) :
    IsPanelLebesgueBound p 2 (quadBreak hab.le p) (quadNode hab.le p) 12 := by
  have hδ : 0 < quadMesh a b p := quadMesh_pos hab p
  have h := isPanelLebesgueBound_of_sep (isPanelNodes_quad hab p) (d := fun _ => quadMesh a b p)
    (ρ := 2) (fun _ _ => hδ) (fun k hk => le_of_eq (by rw [quadBreak_sub hab hk]))
    (fun k hk i i' hii => quadNode_sep hab hk i i' hii)
  have hval : ((2 : ℕ) + 1 : ℝ) * (2 : ℝ) ^ 2 = 12 := by norm_num
  rwa [hval] at h

/-- **The piecewise quadratic interpolatory projection** `P_n` of (12.3.24): the bounded projection
of `C[a, b]` onto the continuous functions that are quadratic on each panel `[x_{2k}, x_{2k+2}]`,
interpolating at the `n + 1` mesh points. -/
noncomputable def quadInterpCLM (hab : a ≤ b) (p : ℕ) :
    C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ) :=
  piecewisePolyInterpCLM p 2 (quadBreak hab p) (quadNode hab p)

/-- The piecewise quadratic projection is idempotent. -/
theorem isIdempotentElem_quadInterpCLM (hab : a < b) (p : ℕ) :
    IsIdempotentElem (quadInterpCLM hab.le p) :=
  isIdempotentElem_piecewisePolyInterpCLM (isPanelNodes_quad hab p)

/-- The norms of the piecewise quadratic projections are bounded uniformly in the mesh. -/
theorem norm_quadInterpCLM_le (hab : a < b) (p : ℕ) : ‖quadInterpCLM hab.le p‖ ≤ 12 :=
  norm_piecewisePolyInterpCLM_le (isPanelNodes_quad hab p) (isPanelLebesgueBound_quad hab p)

/-- The piecewise quadratic projection reproduces the value at every mesh point; in particular
`P_n u` and `u` agree at the `n + 1` collocation nodes. -/
theorem quadInterpCLM_apply_meshPoint (hab : a < b) (p : ℕ) (g : C(Set.Icc a b, ℝ)) {j : ℕ}
    (hj : j ≤ 2 * (p + 1)) :
    quadInterpCLM hab.le p g (meshPoint hab.le (2 * (p + 1)) j)
      = g (meshPoint hab.le (2 * (p + 1)) j) := by
  obtain ⟨k, i, hk, hki⟩ : ∃ (k : ℕ) (i : Fin 3), k ≤ p ∧ j = 2 * k + (i : ℕ) := by
    rcases Nat.lt_or_ge j (2 * p + 2) with hlt | hge
    · refine ⟨j / 2, ⟨j % 2, by omega⟩, by omega, ?_⟩
      change j = 2 * (j / 2) + j % 2
      omega
    · refine ⟨p, ⟨2, by norm_num⟩, le_rfl, ?_⟩
      change j = 2 * p + 2
      omega
  subst hki
  exact piecewisePolyInterpCLM_apply_node (isPanelNodes_quad hab p) g hk i

open Filter Topology in
/-- **The piecewise quadratic projections converge pointwise to the identity**, which is what
Lemma 12.1.4 needs in order to give `‖K - P_n K‖ → 0`. -/
theorem tendsto_quadInterpCLM (hab : a < b) (v : C(Set.Icc a b, ℝ)) :
    Tendsto (fun p => quadInterpCLM hab.le p v) atTop (𝓝 v) := by
  refine tendsto_piecewisePolyInterpCLM (hs := fun p => 2 * quadMesh a b p) (Λ := 12)
    (fun p => isPanelNodes_quad hab p) (fun p => isPanelLebesgueBound_quad hab p)
    (fun p k hk => le_of_eq (quadBreak_sub hab hk)) ?_ v
  have hlim : Tendsto (fun p : ℕ => (b - a) / (2 * ((p : ℝ) + 1))) atTop (𝓝 0) := by
    apply Filter.Tendsto.div_atTop (tendsto_const_nhds (x := b - a))
    exact Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop |>.const_mul_atTop
      (by norm_num)
  have h2 : Tendsto (fun p : ℕ => 2 * quadMesh a b p) atTop (𝓝 0) := by
    have := hlim.const_mul (2 : ℝ)
    simpa [quadMesh] using this
  exact h2

end PiecewiseQuadratic

/-! ### The interpolation error (12.3.27) and the smoothing estimate (12.3.31) -/

section QuadraticError

open IntegralOperator MeasureTheory

variable {a b : ℝ}

/-- **The extreme value of the nodal polynomial of a quadratic panel.**  In the variable
`w = y - x_{2k+1}` centred at the midpoint of the panel the nodal polynomial is `(w + h) w (w - h)`,
and `4 h⁶ - 27 w² (w² - h²)² = (3 w² - h²)² (4 h² - 3 w²)` is nonnegative for `|w| ≤ h`, so the
polynomial does not exceed `2 √3 h³/9`, its value at `w = ∓ h/√3`.

Divided by `3! = 6` this is the constant `√3/27` of (12.3.27). -/
theorem abs_cubic_nodal_le {δ w : ℝ} (hδ : 0 < δ) (hw : |w| ≤ δ) :
    |(w + δ) * w * (w - δ)| ≤ 2 * Real.sqrt 3 * δ ^ 3 / 9 := by
  have hwle := abs_le.mp hw
  have hsq : w ^ 2 ≤ δ ^ 2 := by nlinarith [hwle.1, hwle.2]
  have hc0 : (0 : ℝ) ≤ 2 * Real.sqrt 3 * δ ^ 3 / 9 := by positivity
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hkey : ((w + δ) * w * (w - δ)) ^ 2 ≤ (2 * Real.sqrt 3 * δ ^ 3 / 9) ^ 2 := by
    have hrhs : (2 * Real.sqrt 3 * δ ^ 3 / 9) ^ 2 = 4 * δ ^ 6 / 27 := by
      have hexp : (2 * Real.sqrt 3 * δ ^ 3 / 9) ^ 2
          = 4 * Real.sqrt 3 ^ 2 * δ ^ 6 / 81 := by ring
      rw [hexp, hs3]
      ring
    rw [hrhs]
    nlinarith [mul_nonneg (sq_nonneg (3 * w ^ 2 - δ ^ 2))
      (show (0 : ℝ) ≤ 4 * δ ^ 2 - 3 * w ^ 2 by nlinarith)]
  have hsqrt := Real.sqrt_le_sqrt hkey
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hc0] at hsqrt

/-- The nodal polynomial of the `k`-th panel of the piecewise quadratic mesh is bounded by
`2 √3 h³/9` on that panel. -/
theorem abs_prod_quadNode_le (hab : a < b) {p k : ℕ} (hk : k ≤ p) {s : ℝ}
    (hs : s ∈ Set.Icc ((quadBreak hab.le p k : ℝ)) ((quadBreak hab.le p (k + 1) : ℝ))) :
    |∏ i, (s - ((quadNode hab.le p k i : ℝ)))| ≤ 2 * Real.sqrt 3 * quadMesh a b p ^ 3 / 9 := by
  have hδ : 0 < quadMesh a b p := quadMesh_pos hab p
  have h0 : ((quadNode hab.le p k 0 : ℝ)) = a + 2 * (k : ℝ) * quadMesh a b p := by
    rw [coe_quadNode hab.le hk]
    norm_num
  have h1 : ((quadNode hab.le p k 1 : ℝ)) = a + (2 * (k : ℝ) + 1) * quadMesh a b p := by
    rw [coe_quadNode hab.le hk]
    norm_num
  have h2 : ((quadNode hab.le p k 2 : ℝ)) = a + (2 * (k : ℝ) + 2) * quadMesh a b p := by
    rw [coe_quadNode hab.le hk]
    norm_num
  rw [coe_quadBreak hab.le (by omega), coe_quadBreak hab.le (by omega)] at hs
  obtain ⟨hs1, hs2⟩ := hs
  push_cast at hs1 hs2
  set w : ℝ := s - (a + (2 * (k : ℝ) + 1) * quadMesh a b p) with hw
  have hwabs : |w| ≤ quadMesh a b p := by
    rw [abs_le, hw]
    constructor <;> nlinarith
  have hrw : ∏ i, (s - ((quadNode hab.le p k i : ℝ)))
      = (w + quadMesh a b p) * w * (w - quadMesh a b p) := by
    rw [Fin.prod_univ_three, h0, h1, h2, hw]
    ring
  rw [hrw]
  exact abs_cubic_nodal_le hδ hwabs

/-- **(12.3.27)**, the error of piecewise quadratic interpolation:
`‖u - P_n u‖_∞ ≤ (√3/27) h³ ‖u'''‖_∞`.

The panel error formula of `exists_sub_piecewisePolyInterpCLM_apply_eq` divided by `3! = 6`, with
the extreme value `2 √3 h³/9` of the nodal polynomial. -/
theorem norm_sub_quadInterpCLM_le (hab : a < b) (p : ℕ) {G : ℝ → ℝ}
    (hG : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) G) {u : C(Set.Icc a b, ℝ)}
    (hu : ∀ t : Set.Icc a b, u t = G ((t : ℝ))) {M₃ : ℝ}
    (hM₃ : ∀ s ∈ Set.Icc a b, |iteratedDeriv 3 G s| ≤ M₃) :
    ‖u - quadInterpCLM hab.le p u‖ ≤ Real.sqrt 3 / 27 * quadMesh a b p ^ 3 * M₃ := by
  have h := norm_sub_piecewisePolyInterpCLM_le (isPanelNodes_quad hab p) hG hu
    (W := 2 * Real.sqrt 3 * quadMesh a b p ^ 3 / 9) (M := M₃)
    (fun k hk s hs => abs_prod_quadNode_le hab hk hs) hM₃
  have hfact : (((2 + 1 : ℕ)).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [quadInterpCLM]
  refine h.trans (le_of_eq ?_)
  rw [hfact]
  ring

end QuadraticError


section Smoothing

open IntegralOperator MeasureTheory

variable {a b : ℝ}

/-- **One panel of (12.3.31).**  On the panel `[x_{2k}, x_{2k+2}]` split the kernel as
`k (x, y) = k (x, x_{2k}) + (k (x, y) - k (x, x_{2k}))`.  The first part contributes
`k (x, x_{2k}) ∫ (u - P_n u)`, and the integral of the quadratic interpolant over its own panel is
Simpson's rule for `u` there, so that integral is exactly the Simpson panel error, of size
`h⁵ ‖u⁗‖/90`.  The second part is at most `L (2h) ‖u - P_n u‖ (2h)`, so it is `𝒪(h⁵)` as well —
and it needs only a Lipschitz bound on the kernel, not the book's `C¹` in `y`. -/
private theorem abs_panel_integral_le (hab : a < b) {k : C(Set.Icc a b × Set.Icc a b, ℝ)} {L : ℝ}
    (hL0 : 0 ≤ L) (hL : ∀ x y z : Set.Icc a b, |k (x, y) - k (x, z)| ≤ L * |(y : ℝ) - (z : ℝ)|)
    {G : ℝ → ℝ} (hG : ContDiff ℝ ((4 : ℕ) : WithTop ℕ∞) G) {u : C(Set.Icc a b, ℝ)}
    (hu : ∀ t : Set.Icc a b, u t = G ((t : ℝ))) {M₄ E : ℝ}
    (hM₄ : ∀ s ∈ Set.Icc a b, |iteratedDeriv 4 G s| ≤ M₄) (p : ℕ)
    (hE : ‖u - quadInterpCLM hab.le p u‖ ≤ E) (x : Set.Icc a b) {j : ℕ} (hj : j ≤ p) :
    |∫ y in ((quadBreak hab.le p j : ℝ))..((quadBreak hab.le p (j + 1) : ℝ)),
        k (x, Set.projIcc a b hab.le y)
          * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y)|
      ≤ ‖k‖ * M₄ * quadMesh a b p ^ 5 / 90 + 4 * L * quadMesh a b p ^ 2 * E := by
  have hδ : 0 < quadMesh a b p := quadMesh_pos hab p
  have hnodes := isPanelNodes_quad hab p
  have hle : ((quadBreak hab.le p j : ℝ)) ≤ ((quadBreak hab.le p (j + 1) : ℝ)) :=
    (hnodes.step j hj).le
  have hlen : ((quadBreak hab.le p (j + 1) : ℝ)) - ((quadBreak hab.le p j : ℝ))
      = 2 * quadMesh a b p := quadBreak_sub hab hj
  have hmemab : ∀ y ∈ Set.Icc ((quadBreak hab.le p j : ℝ)) ((quadBreak hab.le p (j + 1) : ℝ)),
      y ∈ Set.Icc a b := fun y hy =>
    ⟨le_trans (quadBreak hab.le p j).2.1 hy.1, le_trans hy.2 (quadBreak hab.le p (j + 1)).2.2⟩
  -- the two factors of the integrand, as functions on the line
  have hκc : Continuous fun y : ℝ => k (x, Set.projIcc a b hab.le y) :=
    k.continuous.comp (continuous_const.prodMk continuous_projIcc)
  have hεc : Continuous fun y : ℝ =>
      (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y) :=
    (u - quadInterpCLM hab.le p u).continuous.comp continuous_projIcc
  -- the panel interpolant, and its values at the three nodes
  have hinj : Set.InjOn (fun q => ((quadNode hab.le p j q : ℝ)))
      (↑(Finset.univ : Finset (Fin (2 + 1)))) := (hnodes.injective j hj).injOn
  have hqnode : ∀ i : Fin 3,
      (panelPoly (quadNode hab.le p) j u).eval ((quadNode hab.le p j i : ℝ))
        = G ((quadNode hab.le p j i : ℝ)) := by
    intro i
    rw [panelPoly, Lagrange.eval_interpolate_at_node _ hinj (Finset.mem_univ i), hu]
  have hqdeg : (panelPoly (quadNode hab.le p) j u).natDegree ≤ 3 := by
    have hdeg := Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin 3)))
      (v := fun q => ((quadNode hab.le p j q : ℝ))) (r := fun i => u (quadNode hab.le p j i)) hinj
    rw [Finset.card_univ, Fintype.card_fin] at hdeg
    exact Polynomial.natDegree_le_iff_degree_le.mpr hdeg.le
  have hn0 : ((quadNode hab.le p j 0 : ℝ)) = ((quadBreak hab.le p j : ℝ)) := by
    rw [hnodes.node_zero j hj]
  have hn2 : ((quadNode hab.le p j 2 : ℝ)) = ((quadBreak hab.le p (j + 1) : ℝ)) := by
    have h := hnodes.node_last j hj
    rw [show (Fin.last 2 : Fin 3) = 2 from rfl] at h
    rw [h]
  have hn1 : ((quadNode hab.le p j 1 : ℝ))
      = (((quadBreak hab.le p j : ℝ)) + ((quadBreak hab.le p (j + 1) : ℝ))) / 2 := by
    have hA : ((quadNode hab.le p j 1 : ℝ)) = a + (2 * (j : ℝ) + 1) * quadMesh a b p := by
      rw [coe_quadNode hab.le hj]
      norm_num
    rw [hA, coe_quadBreak hab.le (by omega), coe_quadBreak hab.le (by omega)]
    push_cast
    ring
  have hqα : (panelPoly (quadNode hab.le p) j u).eval ((quadBreak hab.le p j : ℝ))
      = G ((quadBreak hab.le p j : ℝ)) := by
    rw [← hn0]
    exact hqnode 0
  have hqβ : (panelPoly (quadNode hab.le p) j u).eval ((quadBreak hab.le p (j + 1) : ℝ))
      = G ((quadBreak hab.le p (j + 1) : ℝ)) := by
    rw [← hn2]
    exact hqnode 2
  have hqm : (panelPoly (quadNode hab.le p) j u).eval
        (((quadBreak hab.le p j : ℝ) + (quadBreak hab.le p (j + 1) : ℝ)) / 2)
      = G (((quadBreak hab.le p j : ℝ) + (quadBreak hab.le p (j + 1) : ℝ)) / 2) := by
    rw [← hn1]
    exact hqnode 1
  -- the interpolant on the panel, and the resulting Simpson error
  have hεval : ∀ y ∈ Set.Icc ((quadBreak hab.le p j : ℝ)) ((quadBreak hab.le p (j + 1) : ℝ)),
      (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y)
        = G y - (panelPoly (quadNode hab.le p) j u).eval y := by
    intro y hy
    have hproj : ((Set.projIcc a b hab.le y : Set.Icc a b) : ℝ) = y := by
      rw [Set.projIcc_of_mem hab.le (hmemab y hy)]
    rw [ContinuousMap.sub_apply, hu, hproj, quadInterpCLM,
      piecewisePolyInterpCLM_apply_of_mem hnodes u hj (by rw [hproj]; exact hy.1)
        (by rw [hproj]; exact hy.2), hproj]
  have hinteps : (∫ y in ((quadBreak hab.le p j : ℝ))..((quadBreak hab.le p (j + 1) : ℝ)),
        (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y))
      = (∫ y in ((quadBreak hab.le p j : ℝ))..((quadBreak hab.le p (j + 1) : ℝ)), G y)
        - ((quadBreak hab.le p (j + 1) : ℝ) - (quadBreak hab.le p j : ℝ)) / 6 *
          (G ((quadBreak hab.le p j : ℝ))
            + 4 * G ((((quadBreak hab.le p j : ℝ)) + ((quadBreak hab.le p (j + 1) : ℝ))) / 2)
            + G ((quadBreak hab.le p (j + 1) : ℝ))) := by
    have hq := Quadrature.integral_eq_simpson_of_natDegree_le hle hqdeg
    rw [hqα, hqβ, hqm] at hq
    rw [← hq, ← intervalIntegral.integral_sub (hG.continuous.intervalIntegrable _ _)
      ((panelPoly (quadNode hab.le p) j u).continuous.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le hle] at hy
    exact hεval y hy
  have hstep : ∀ i : ℕ, i < 4 → ∀ y : ℝ,
      HasDerivAt (iteratedDeriv i G) (iteratedDeriv (i + 1) G y) y := by
    intro i hi y
    have hd := ((hG.differentiable_iteratedDeriv i (by exact_mod_cast hi)) y).hasDerivAt
    rwa [← iteratedDeriv_succ] at hd
  have hc4 : Continuous (iteratedDeriv 4 G) := hG.continuous_iteratedDeriv 4 le_rfl
  have hsimp : |∫ y in ((quadBreak hab.le p j : ℝ))..((quadBreak hab.le p (j + 1) : ℝ)),
        (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y)|
      ≤ M₄ * (2 * quadMesh a b p) ^ 5 / 2880 := by
    rw [hinteps, ← hlen]
    exact Quadrature.abs_sub_simpson_le (g := G) (g' := iteratedDeriv 1 G)
      (g'' := iteratedDeriv 2 G) (g₃ := iteratedDeriv 3 G) (g₄ := iteratedDeriv 4 G) hle
      (fun y _ => by simpa only [iteratedDeriv_zero] using hstep 0 (by norm_num) y)
      (fun y _ => hstep 1 (by norm_num) y) (fun y _ => hstep 2 (by norm_num) y)
      (fun y _ => hstep 3 (by norm_num) y) hc4.continuousOn
      (fun t ht => hM₄ t (hmemab t ht))
  -- the splitting of the kernel on the panel
  have hdecomp : (∫ y in ((quadBreak hab.le p j : ℝ))..((quadBreak hab.le p (j + 1) : ℝ)),
        k (x, Set.projIcc a b hab.le y)
          * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y))
      = k (x, Set.projIcc a b hab.le ((quadBreak hab.le p j : ℝ)))
          * (∫ y in ((quadBreak hab.le p j : ℝ))..((quadBreak hab.le p (j + 1) : ℝ)),
              (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y))
        + ∫ y in ((quadBreak hab.le p j : ℝ))..((quadBreak hab.le p (j + 1) : ℝ)),
            (k (x, Set.projIcc a b hab.le y)
                - k (x, Set.projIcc a b hab.le ((quadBreak hab.le p j : ℝ))))
              * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y) := by
    have hcongr : (∫ y in ((quadBreak hab.le p j : ℝ))..((quadBreak hab.le p (j + 1) : ℝ)),
          k (x, Set.projIcc a b hab.le y)
            * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y))
        = ∫ y in ((quadBreak hab.le p j : ℝ))..((quadBreak hab.le p (j + 1) : ℝ)),
            (k (x, Set.projIcc a b hab.le ((quadBreak hab.le p j : ℝ)))
                * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y)
              + (k (x, Set.projIcc a b hab.le y)
                  - k (x, Set.projIcc a b hab.le ((quadBreak hab.le p j : ℝ))))
                * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y)) :=
      intervalIntegral.integral_congr fun y _ => by ring
    have hint1 : IntervalIntegrable (fun y : ℝ =>
        k (x, Set.projIcc a b hab.le ((quadBreak hab.le p j : ℝ)))
          * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y)) MeasureTheory.volume
        ((quadBreak hab.le p j : ℝ)) ((quadBreak hab.le p (j + 1) : ℝ)) :=
      Continuous.intervalIntegrable (continuous_const.mul hεc) _ _
    have hint2 : IntervalIntegrable (fun y : ℝ =>
        (k (x, Set.projIcc a b hab.le y)
            - k (x, Set.projIcc a b hab.le ((quadBreak hab.le p j : ℝ))))
          * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y)) MeasureTheory.volume
        ((quadBreak hab.le p j : ℝ)) ((quadBreak hab.le p (j + 1) : ℝ)) :=
      Continuous.intervalIntegrable ((hκc.sub continuous_const).mul hεc) _ _
    rw [hcongr, intervalIntegral.integral_add hint1 hint2,
      intervalIntegral.integral_const_mul]
  -- the two terms
  have hterm1 : |k (x, Set.projIcc a b hab.le ((quadBreak hab.le p j : ℝ)))
        * (∫ y in ((quadBreak hab.le p j : ℝ))..((quadBreak hab.le p (j + 1) : ℝ)),
            (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y))|
      ≤ ‖k‖ * (M₄ * (2 * quadMesh a b p) ^ 5 / 2880) := by
    rw [abs_mul]
    refine mul_le_mul ?_ hsimp (abs_nonneg _) (norm_nonneg k)
    simpa using k.norm_coe_le_norm _
  have hterm2 : |∫ y in ((quadBreak hab.le p j : ℝ))..((quadBreak hab.le p (j + 1) : ℝ)),
        (k (x, Set.projIcc a b hab.le y)
            - k (x, Set.projIcc a b hab.le ((quadBreak hab.le p j : ℝ))))
          * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y)|
      ≤ L * (2 * quadMesh a b p) * E * (2 * quadMesh a b p) := by
    have hLd0 : (0 : ℝ) ≤ L * (2 * quadMesh a b p) := mul_nonneg hL0 (by linarith)
    have hbnd : ∀ y ∈ Set.uIoc ((quadBreak hab.le p j : ℝ)) ((quadBreak hab.le p (j + 1) : ℝ)),
        ‖(k (x, Set.projIcc a b hab.le y)
            - k (x, Set.projIcc a b hab.le ((quadBreak hab.le p j : ℝ))))
          * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y)‖
          ≤ L * (2 * quadMesh a b p) * E := by
      intro y hy
      rw [Set.uIoc_of_le hle] at hy
      have hy' : y ∈ Set.Icc ((quadBreak hab.le p j : ℝ)) ((quadBreak hab.le p (j + 1) : ℝ)) :=
        ⟨hy.1.le, hy.2⟩
      have hprojy : ((Set.projIcc a b hab.le y : Set.Icc a b) : ℝ) = y := by
        rw [Set.projIcc_of_mem hab.le (hmemab y hy')]
      have hproja : ((Set.projIcc a b hab.le ((quadBreak hab.le p j : ℝ)) : Set.Icc a b) : ℝ)
          = ((quadBreak hab.le p j : ℝ)) := by
        rw [Set.projIcc_of_mem hab.le (hmemab _ ⟨le_rfl, hle⟩)]
      have h1 : |k (x, Set.projIcc a b hab.le y)
          - k (x, Set.projIcc a b hab.le ((quadBreak hab.le p j : ℝ)))|
          ≤ L * (2 * quadMesh a b p) := by
        refine le_trans (hL x _ _) ?_
        rw [hprojy, hproja, abs_of_nonneg (by linarith [hy'.1])]
        nlinarith [hlen, hL0, hy'.1, hy'.2]
      have h2 : |(u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y)| ≤ E :=
        le_trans (by simpa using (u - quadInterpCLM hab.le p u).norm_coe_le_norm _) hE
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) hLd0
    have habs2 : |2 * quadMesh a b p| = 2 * quadMesh a b p := abs_of_nonneg (by linarith)
    have hres := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
    rw [Real.norm_eq_abs, hlen, habs2] at hres
    exact hres
  rw [hdecomp]
  calc |k (x, Set.projIcc a b hab.le ((quadBreak hab.le p j : ℝ)))
        * (∫ y in ((quadBreak hab.le p j : ℝ))..((quadBreak hab.le p (j + 1) : ℝ)),
            (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y))
        + ∫ y in ((quadBreak hab.le p j : ℝ))..((quadBreak hab.le p (j + 1) : ℝ)),
            (k (x, Set.projIcc a b hab.le y)
                - k (x, Set.projIcc a b hab.le ((quadBreak hab.le p j : ℝ))))
              * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y)|
      ≤ ‖k‖ * (M₄ * (2 * quadMesh a b p) ^ 5 / 2880)
          + L * (2 * quadMesh a b p) * E * (2 * quadMesh a b p) :=
        (abs_add_le _ _).trans (add_le_add hterm1 hterm2)
    _ = ‖k‖ * M₄ * quadMesh a b p ^ 5 / 90 + 4 * L * quadMesh a b p ^ 2 * E := by ring

/-- **(12.3.31)**: for a kernel Lipschitz in its second variable and `u ∈ C⁴[a, b]`,

`‖K (I - P_n) u‖_∞ ≤ (b - a) (‖k‖ ‖u⁗‖/180 + 2 √3 L ‖u'''‖/27) h⁴`,

so `K (I - P_n) u = 𝒪(h⁴)` — one power of `h` better than `‖(I - P_n) u‖ = 𝒪(h³)`.

The book obtains this from the `y`-derivative of a Newton divided difference; the route here is
the one of `abs_panel_integral_le`, which splits the kernel on each panel and reads the resulting
main term as the Simpson panel error.  It needs only a Lipschitz bound on `k` in `y`, which the
book's hypothesis that `k` be continuously differentiable in `y` supplies on the compact square.

Summing the `(b - a)/(2h)` panel bounds `𝒪(h⁵)` gives `𝒪(h⁴)`. -/
theorem norm_kernelCLM_sub_quadInterpCLM_le (hab : a < b)
    {k : C(Set.Icc a b × Set.Icc a b, ℝ)} {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x y z : Set.Icc a b, |k (x, y) - k (x, z)| ≤ L * |(y : ℝ) - (z : ℝ)|)
    {G : ℝ → ℝ} (hG : ContDiff ℝ ((4 : ℕ) : WithTop ℕ∞) G) {u : C(Set.Icc a b, ℝ)}
    (hu : ∀ t : Set.Icc a b, u t = G ((t : ℝ))) {M₃ M₄ : ℝ}
    (hM₃ : ∀ s ∈ Set.Icc a b, |iteratedDeriv 3 G s| ≤ M₃)
    (hM₄ : ∀ s ∈ Set.Icc a b, |iteratedDeriv 4 G s| ≤ M₄) (p : ℕ) :
    ‖kernelCLM (iccMeasure a b) k (u - quadInterpCLM hab.le p u)‖
      ≤ (b - a) * (‖k‖ * M₄ / 180 + 2 * Real.sqrt 3 * L * M₃ / 27) * quadMesh a b p ^ 4 := by
  have hδ : 0 < quadMesh a b p := quadMesh_pos hab p
  have hnodes := isPanelNodes_quad hab p
  have hab0 : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hM30 : 0 ≤ M₃ := le_trans (abs_nonneg _) (hM₃ a ⟨le_rfl, hab.le⟩)
  have hM40 : 0 ≤ M₄ := le_trans (abs_nonneg _) (hM₄ a ⟨le_rfl, hab.le⟩)
  have hs30 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hE : ‖u - quadInterpCLM hab.le p u‖ ≤ Real.sqrt 3 / 27 * quadMesh a b p ^ 3 * M₃ :=
    norm_sub_quadInterpCLM_le hab p (hG.of_le (by norm_num)) hu hM₃
  have hrhs0 : (0 : ℝ)
      ≤ (b - a) * (‖k‖ * M₄ / 180 + 2 * Real.sqrt 3 * L * M₃ / 27) * quadMesh a b p ^ 4 := by
    refine mul_nonneg (mul_nonneg hab0.le (add_nonneg ?_ ?_)) (pow_nonneg hδ.le 4)
    · exact div_nonneg (mul_nonneg (norm_nonneg k) hM40) (by norm_num)
    · exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) hL0) hM30) (by norm_num)
  rw [ContinuousMap.norm_le _ hrhs0]
  intro x
  rw [kernelCLM_apply, Real.norm_eq_abs]
  have hFc : Continuous fun y : ℝ => k (x, Set.projIcc a b hab.le y)
      * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y) :=
    (k.continuous.comp (continuous_const.prodMk continuous_projIcc)).mul
      ((u - quadInterpCLM hab.le p u).continuous.comp continuous_projIcc)
  have hconv : (∫ y, k (x, y) * (u - quadInterpCLM hab.le p u) y ∂iccMeasure a b)
      = ∫ y in a..b, k (x, Set.projIcc a b hab.le y)
          * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y) := by
    rw [← IntegralOperator.integral_iccMeasure hab.le fun y => k (x, Set.projIcc a b hab.le y)
      * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y)]
    simp
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j => ((quadBreak hab.le p j : ℝ))) (n := p + 1)
    (f := fun y : ℝ => k (x, Set.projIcc a b hab.le y)
      * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y))
    (μ := MeasureTheory.volume) fun j _ => Continuous.intervalIntegrable hFc _ _
  rw [(hnodes.first : ((quadBreak hab.le p 0 : ℝ)) = a),
    (hnodes.last : ((quadBreak hab.le p (p + 1) : ℝ)) = b)] at hsum
  have hpd : ((p : ℝ) + 1) * quadMesh a b p = (b - a) / 2 := by
    rw [quadMesh]
    field_simp
  rw [hconv, ← hsum]
  calc |∑ j ∈ Finset.range (p + 1),
        ∫ y in ((quadBreak hab.le p j : ℝ))..((quadBreak hab.le p (j + 1) : ℝ)),
          k (x, Set.projIcc a b hab.le y)
            * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y)|
      ≤ ∑ j ∈ Finset.range (p + 1),
          |∫ y in ((quadBreak hab.le p j : ℝ))..((quadBreak hab.le p (j + 1) : ℝ)),
            k (x, Set.projIcc a b hab.le y)
              * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (p + 1), (‖k‖ * M₄ * quadMesh a b p ^ 5 / 90
          + 4 * L * quadMesh a b p ^ 2 * (Real.sqrt 3 / 27 * quadMesh a b p ^ 3 * M₃)) :=
        Finset.sum_le_sum fun j hj => abs_panel_integral_le hab hL0 hL hG hu hM₄ p hE x
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    _ = ((p : ℝ) + 1) * (‖k‖ * M₄ * quadMesh a b p ^ 5 / 90
          + 4 * L * quadMesh a b p ^ 2 * (Real.sqrt 3 / 27 * quadMesh a b p ^ 3 * M₃)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ = (b - a) * (‖k‖ * M₄ / 180 + 2 * Real.sqrt 3 * L * M₃ / 27) * quadMesh a b p ^ 4 := by
        linear_combination (quadMesh a b p ^ 4 *
          (‖k‖ * M₄ / 90 + 4 * Real.sqrt 3 * L * M₃ / 27)) * hpd


end Smoothing


/-! ### Theorem 12.3.3 -/

section Theorem3

open IntegralOperator MeasureTheory

variable {a b : ℝ}

/-- **Theorem 12.3.3**, the superconvergence of iterated piecewise quadratic collocation.  For the
integral equation (12.3.23) with a kernel Lipschitz in `y` — which a kernel continuously
differentiable in `y` is on the compact square — a solution `u ∈ C⁴[a, b]` and the interpolatory
projection `P_n` onto the continuous piecewise quadratics of the uniform mesh of `n = 2 (p + 1)`
subintervals, the collocation equations are uniquely solvable for all large `n` with uniformly
bounded inverses, and

* `‖u - u_n‖_∞ ≤ |λ| M ‖u - P_n u‖_∞ ≤ (√3 |λ| M/27) h³ ‖u'''‖_∞`   (12.3.32),
* `‖u - û_n‖_∞ ≤ c h⁴`   (12.3.33),
* `max_j |u(x_j) - u_n(x_j)| ≤ c h⁴`   (12.3.34), the superconvergence at the breakpoints.

The two operator bounds come from `theorem_12_1_2` and `lemma_12_3_1_projection`, the first
inequality of (12.3.32) from `equation_12_1_24`, the second from `norm_sub_quadInterpCLM_le`, and
(12.3.33) from the error identity of `equation_12_3_11` together with (12.3.31),
`norm_kernelCLM_sub_quadInterpCLM_le`.  (12.3.34) is then one line: `P_n û_n = u_n` and the
projection reproduces the values at the mesh points, so `u_n` and `û_n` agree there. -/
theorem theorem_12_3_3 (hab : a < b) {k : C(Set.Icc a b × Set.Icc a b, ℝ)} {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x y z : Set.Icc a b, |k (x, y) - k (x, z)| ≤ L * |(y : ℝ) - (z : ℝ)|)
    {μ : ℝ} (hμ : μ ≠ 0) {e : C(Set.Icc a b, ℝ) ≃L[ℝ] C(Set.Icc a b, ℝ)}
    (he : (e : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))
      = μ • 1 - kernelCLM (iccMeasure a b) k)
    {G : ℝ → ℝ} (hG : ContDiff ℝ ((4 : ℕ) : WithTop ℕ∞) G) {u : C(Set.Icc a b, ℝ)}
    (hu : ∀ t : Set.Icc a b, u t = G ((t : ℝ))) {M₃ M₄ : ℝ}
    (hM₃ : ∀ s ∈ Set.Icc a b, |iteratedDeriv 3 G s| ≤ M₃)
    (hM₄ : ∀ s ∈ Set.Icc a b, |iteratedDeriv 4 G s| ≤ M₄) {f : C(Set.Icc a b, ℝ)}
    (hf : (μ • 1 - kernelCLM (iccMeasure a b) k :
      C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) u = f) :
    ∃ M c : ℝ, ∀ᶠ p in atTop, ∃ e' : C(Set.Icc a b, ℝ) ≃L[ℝ] C(Set.Icc a b, ℝ),
      (e' : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))
          = μ • 1 - quadInterpCLM hab.le p ∘L kernelCLM (iccMeasure a b) k ∧
        ‖(e'.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ ≤ M ∧
        (∀ g : C(Set.Icc a b, ℝ), ∃! un : C(Set.Icc a b, ℝ), IsProjectionSolution μ
          (kernelCLM (iccMeasure a b) k) (quadInterpCLM hab.le p) g un) ∧
        ∀ un : C(Set.Icc a b, ℝ), IsProjectionSolution μ (kernelCLM (iccMeasure a b) k)
            (quadInterpCLM hab.le p) f un →
          ‖u - un‖ ≤ |μ| * M * ‖u - quadInterpCLM hab.le p u‖ ∧
          ‖u - un‖ ≤ Real.sqrt 3 * (|μ| * M) / 27 * quadMesh a b p ^ 3 * M₃ ∧
          ‖u - iteratedSolution μ (kernelCLM (iccMeasure a b) k) f un‖
            ≤ c * quadMesh a b p ^ 4 ∧
          ∀ j ≤ 2 * (p + 1),
            |u (meshPoint hab.le (2 * (p + 1)) j) - un (meshPoint hab.le (2 * (p + 1)) j)|
              ≤ c * quadMesh a b p ^ 4 := by
  classical
  have hKc : IsCompactOperator (kernelCLM (iccMeasure a b) k) :=
    isCompactOperator_kernelCLM _ k
  have hS0 : (0 : ℝ) ≤ ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ := norm_nonneg _
  -- the uniform bounds
  refine ⟨2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖,
    |μ|⁻¹ * (1 + ‖kernelCLM (iccMeasure a b) k‖ *
        (2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ * 12)) *
      ((b - a) * (‖k‖ * M₄ / 180 + 2 * Real.sqrt 3 * L * M₃ / 27)), ?_⟩
  have hzero : Tendsto (fun p => ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ *
      ‖kernelCLM (iccMeasure a b) k
        - quadInterpCLM hab.le p ∘L kernelCLM (iccMeasure a b) k‖) atTop (𝓝 0) := by
    have h := (lemma_12_1_4 hKc (tendsto_quadInterpCLM hab)).const_mul
      ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖
    simpa using h
  filter_upwards [hzero.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with p hp
  -- Theorem 12.1.2 and the uniform bound on the inverses
  obtain ⟨e', he'coe, he'norm, he'sol⟩ := theorem_12_1_2 hμ (isIdempotentElem_quadInterpCLM hab p)
    e he (lt_of_lt_of_le hp (by norm_num))
  have hden : (0 : ℝ) < 1 - ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ *
      ‖kernelCLM (iccMeasure a b) k
        - quadInterpCLM hab.le p ∘L kernelCLM (iccMeasure a b) k‖ := by linarith
  have hM : ‖(e'.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖
      ≤ 2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ := by
    refine he'norm.trans ?_
    rw [div_le_iff₀ hden]
    nlinarith [hS0, hp]
  refine ⟨e', he'coe, hM, he'sol, fun un hun => ?_⟩
  -- (12.3.32)
  have h1224 := (equation_12_1_24 (isIdempotentElem_quadInterpCLM hab p) he'coe hf hun).2
  rw [Real.norm_eq_abs] at h1224
  have hinterp : ‖u - quadInterpCLM hab.le p u‖
      ≤ Real.sqrt 3 / 27 * quadMesh a b p ^ 3 * M₃ :=
    norm_sub_quadInterpCLM_le hab p (hG.of_le (by norm_num)) hu hM₃
  have hfirst : ‖u - un‖ ≤ |μ| * (2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖)
      * ‖u - quadInterpCLM hab.le p u‖ := by
    exact h1224.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hM (abs_nonneg μ)) (norm_nonneg _))
  have hsecond : ‖u - un‖ ≤ Real.sqrt 3 *
      (|μ| * (2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖)) / 27
        * quadMesh a b p ^ 3 * M₃ := by
    refine hfirst.trans ?_
    have h0 : (0 : ℝ) ≤ |μ| * (2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖) := by
      positivity
    nlinarith [hinterp, h0]
  -- Lemma 12.3.1 applied to the projection, and the error identity (12.3.11)
  obtain ⟨e'', he''coe, -, he''norm⟩ := lemma_12_3_1_projection hμ
    (kernelCLM (iccMeasure a b) k) (quadInterpCLM hab.le p) he'coe
  have hMpp : ‖(e''.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖
      ≤ |μ|⁻¹ * (1 + ‖kernelCLM (iccMeasure a b) k‖ *
        (2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ * 12)) := by
    refine he''norm.trans ?_
    rw [Real.norm_eq_abs]
    have hP12 : ‖quadInterpCLM hab.le p‖ ≤ 12 := norm_quadInterpCLM_le hab p
    have hKn : (0 : ℝ) ≤ ‖kernelCLM (iccMeasure a b) k‖ := norm_nonneg _
    have hinv : (0 : ℝ) ≤ |μ|⁻¹ := by positivity
    have hmono : ‖kernelCLM (iccMeasure a b) k‖ *
        (‖(e'.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ * ‖quadInterpCLM hab.le p‖)
        ≤ ‖kernelCLM (iccMeasure a b) k‖ *
          (2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ * 12) := by
      refine mul_le_mul_of_nonneg_left ?_ hKn
      have h1 : (0 : ℝ) ≤ ‖quadInterpCLM hab.le p‖ := norm_nonneg _
      have h2 : (0 : ℝ) ≤ ‖(e'.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ :=
        norm_nonneg _
      nlinarith [hM, hP12, hS0]
    exact mul_le_mul_of_nonneg_left (by linarith) hinv
  have hid := (equation_12_3_11 hμ (isIdempotentElem_quadInterpCLM hab p) he''coe hf hun).1
  have herr : u - iteratedSolution μ (kernelCLM (iccMeasure a b) k) f un
      = e''.symm (kernelCLM (iccMeasure a b) k (u - quadInterpCLM hab.le p u)) := by
    rw [← hid, ← he''coe, ContinuousLinearEquiv.coe_coe, e''.symm_apply_apply]
  have h1231 := norm_kernelCLM_sub_quadInterpCLM_le hab hL0 hL hG hu hM₃ hM₄ p
  have hthird : ‖u - iteratedSolution μ (kernelCLM (iccMeasure a b) k) f un‖
      ≤ |μ|⁻¹ * (1 + ‖kernelCLM (iccMeasure a b) k‖ *
          (2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ * 12)) *
        ((b - a) * (‖k‖ * M₄ / 180 + 2 * Real.sqrt 3 * L * M₃ / 27)) * quadMesh a b p ^ 4 := by
    rw [herr]
    have hstep1 : ‖e''.symm (kernelCLM (iccMeasure a b) k (u - quadInterpCLM hab.le p u))‖
        ≤ ‖(e''.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖
          * ‖kernelCLM (iccMeasure a b) k (u - quadInterpCLM hab.le p u)‖ :=
      ContinuousLinearMap.le_opNorm (e''.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) _
    have hnn : (0 : ℝ) ≤ ‖kernelCLM (iccMeasure a b) k (u - quadInterpCLM hab.le p u)‖ :=
      norm_nonneg _
    have hMpp0 : (0 : ℝ) ≤ |μ|⁻¹ * (1 + ‖kernelCLM (iccMeasure a b) k‖ *
        (2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ * 12)) :=
      le_trans (norm_nonneg _) hMpp
    calc ‖e''.symm (kernelCLM (iccMeasure a b) k (u - quadInterpCLM hab.le p u))‖
        ≤ ‖(e''.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖
            * ‖kernelCLM (iccMeasure a b) k (u - quadInterpCLM hab.le p u)‖ := hstep1
      _ ≤ (|μ|⁻¹ * (1 + ‖kernelCLM (iccMeasure a b) k‖ *
            (2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ * 12)))
            * ‖kernelCLM (iccMeasure a b) k (u - quadInterpCLM hab.le p u)‖ :=
          mul_le_mul_of_nonneg_right hMpp hnn
      _ ≤ (|μ|⁻¹ * (1 + ‖kernelCLM (iccMeasure a b) k‖ *
            (2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ * 12)))
            * ((b - a) * (‖k‖ * M₄ / 180 + 2 * Real.sqrt 3 * L * M₃ / 27)
              * quadMesh a b p ^ 4) := mul_le_mul_of_nonneg_left h1231 hMpp0
      _ = _ := by ring
  -- (12.3.34): the collocation solution agrees with the iterated solution at the mesh points
  refine ⟨hfirst, hsecond, hthird, fun j hj => ?_⟩
  have hnode : un (meshPoint hab.le (2 * (p + 1)) j)
      = iteratedSolution μ (kernelCLM (iccMeasure a b) k) f un
        (meshPoint hab.le (2 * (p + 1)) j) := by
    have hproj := equation_12_3_2 hμ (isIdempotentElem_quadInterpCLM hab p) hun
    calc un (meshPoint hab.le (2 * (p + 1)) j)
        = quadInterpCLM hab.le p (iteratedSolution μ (kernelCLM (iccMeasure a b) k) f un)
            (meshPoint hab.le (2 * (p + 1)) j) := by rw [hproj]
      _ = iteratedSolution μ (kernelCLM (iccMeasure a b) k) f un
            (meshPoint hab.le (2 * (p + 1)) j) :=
          quadInterpCLM_apply_meshPoint hab p _ hj
  rw [hnode]
  have hval : |u (meshPoint hab.le (2 * (p + 1)) j)
      - iteratedSolution μ (kernelCLM (iccMeasure a b) k) f un
        (meshPoint hab.le (2 * (p + 1)) j)|
      ≤ ‖u - iteratedSolution μ (kernelCLM (iccMeasure a b) k) f un‖ := by
    have := (u - iteratedSolution μ (kernelCLM (iccMeasure a b) k) f un).norm_coe_le_norm
      (meshPoint hab.le (2 * (p + 1)) j)
    simpa using this
  exact hval.trans hthird

end Theorem3


/-! ### Example 12.3.2: the iterated Galerkin method with discontinuous piecewise linears -/

section IteratedGalerkin

open MeasureTheory IntegralOperator

local notation "L²" => Lp ℝ 2 (IntegralOperator.iccMeasure 0 1)

/-- The kernel `k(x, y) = e^{x y}` of **(12.3.18)**.

This is the same function as `AtkinsonHan.Chapter12.expKernel` of §12.4, the book's standard test
kernel for the whole chapter; it is repeated here, privately, only because §12.4 comes later in the
chapter and a surface file may not import a later section.  The two should become one definition,
owned by this section, when §12.4 is next revised. -/
private noncomputable def expKernel : C(Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun p => Real.exp ((p.1 : ℝ) * (p.2 : ℝ)), by fun_prop⟩

/-- The value of the kernel of (12.3.18). -/
private theorem expKernel_apply (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) :
    expKernel p = Real.exp ((p.1 : ℝ) * (p.2 : ℝ)) := rfl

/-- `e^{xy} ≤ e` on the unit square. -/
private theorem norm_expKernel_le : ‖expKernel‖ ≤ Real.exp 1 := by
  refine (ContinuousMap.norm_le _ (Real.exp_nonneg 1)).2 fun p => ?_
  rw [expKernel_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ?_
  nlinarith [p.1.2.1, p.1.2.2, p.2.2.1, p.2.2.2]

/-- The integral operator `K u (x) = ∫_0^1 e^{xy} u(y) dy` of **(12.3.18)**, on `L²(0, 1)`. -/
noncomputable def expKernelCLM : L² →L[ℝ] L² :=
  l2KernelCLM (memLp_prod_iccMeasure expKernel)

/-- `‖K‖ ≤ e`, from the uniform bound on the kernel; in particular `‖K‖ < 50 = λ`, so the
integral equation (12.3.18) is uniquely solvable by the Neumann series and no compactness argument
is needed here. -/
theorem norm_expKernelCLM_le : ‖expKernelCLM‖ ≤ Real.exp 1 := by
  have h := norm_l2KernelCLM_comp_le (a := 0) (b := 1) zero_le_one
    (memLp_prod_iccMeasure expKernel) (Q := (1 : L² →L[ℝ] L²)) (IsSelfAdjoint.one _)
    (ε := Real.exp 1) (Real.exp_nonneg 1) ?_
  · rw [show (l2KernelCLM (memLp_prod_iccMeasure expKernel) ∘L (1 : L² →L[ℝ] L²))
      = expKernelCLM from mul_one _] at h
    simpa using h
  · intro z
    rw [one_apply_eq_self]
    refine (norm_iccToLp_le zero_le_one _).trans ?_
    have hrow : ‖expKernel.curry z‖ ≤ ‖expKernel‖ :=
      (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun t => expKernel.norm_coe_le_norm (z, t)
    simpa using hrow.trans norm_expKernel_le

/-- `‖K‖ < |λ|` at the book's `λ = 50`. -/
theorem norm_expKernelCLM_lt : ‖expKernelCLM‖ < |(50 : ℝ)| := by
  have h := norm_expKernelCLM_le
  have he := Real.exp_one_lt_d9
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 50)]
  linarith

/-- The kernel `e^{xy}` is symmetric, so `K* = K`. -/
theorem isSelfAdjoint_expKernelCLM : IsSelfAdjoint expKernelCLM :=
  isSelfAdjoint_l2KernelCLM _
    (Filter.Eventually.of_forall fun p => by simp [expKernel_apply, mul_comm])

/-- The uniform mesh `x_j = j h`, `h = 1/n`, of `[0, 1]` into `n` subintervals, as used in
Example 12.3.2.  The partition has `n` panels, so the index that
`Numlib/Approximation/PiecewiseLinearL2` calls `n` is `n - 1` here. -/
noncomputable def unitMesh (n j : ℕ) : Set.Icc (0 : ℝ) 1 := meshPoint zero_le_one n j

/-- The value `j/n` of a mesh point of Example 12.3.2. -/
theorem coe_unitMesh {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    (unitMesh n j : ℝ) = (j : ℝ) / n := by
  rw [unitMesh, coe_meshPoint zero_le_one hn hj]
  ring

/-- The mesh is increasing. -/
theorem unitMesh_step {n : ℕ} (hn : 0 < n) :
    ∀ i ≤ n - 1, (unitMesh n i : ℝ) < (unitMesh n (i + 1) : ℝ) := by
  intro i hi
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [coe_unitMesh hn (by omega), coe_unitMesh hn (by omega)]
  gcongr
  linarith

/-- The mesh starts at `0`. -/
theorem unitMesh_first (n : ℕ) : (unitMesh n 0 : ℝ) = 0 := by
  rw [unitMesh, meshPoint]
  simp

/-- The mesh ends at `1`. -/
theorem unitMesh_last {n : ℕ} (hn : 0 < n) : (unitMesh n (n - 1 + 1) : ℝ) = 1 := by
  rw [show n - 1 + 1 = n by omega, coe_unitMesh hn le_rfl]
  field_simp

/-- Every subinterval of the mesh has length `h = 1/n`. -/
theorem unitMesh_mesh {n : ℕ} (hn : 0 < n) :
    ∀ i ≤ n - 1, (unitMesh n (i + 1) : ℝ) - (unitMesh n i : ℝ) ≤ 1 / n := by
  intro i hi
  rw [coe_unitMesh hn (by omega), coe_unitMesh hn (by omega)]
  push_cast
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp
  linarith

/-- **The projection `P_n` of Example 12.3.2**: the `L²(0, 1)`-orthogonal projection onto the
functions that are linear on each subinterval of the uniform mesh of width `h = 1/n`, *without*
the continuity restriction of §12.2.3.  It is the backbone `discPiecewiseLinearProjCLM`.  The
book's count `d_n = 2 n` for the dimension of the trial space, twice that of the continuous
piecewise linear space, is not formalized: it is a remark on the size of the linear system, and
nothing in (12.3.19) or (12.3.20) uses it. -/
noncomputable def discGalerkinProj (n : ℕ) : L² →L[ℝ] L² :=
  discPiecewiseLinearProjCLM 0 1 (n - 1) (unitMesh n)

/-- `P_n` is a projection. -/
theorem isIdempotentElem_discGalerkinProj (n : ℕ) : IsIdempotentElem (discGalerkinProj n) :=
  isIdempotentElem_discPiecewiseLinearProjCLM 0 1 (n - 1) (unitMesh n)

/-- `P_n` is self-adjoint, being orthogonal; this is what (12.3.13) uses. -/
theorem isSelfAdjoint_discGalerkinProj (n : ℕ) : IsSelfAdjoint (discGalerkinProj n) :=
  isSelfAdjoint_discPiecewiseLinearProjCLM 0 1 (n - 1) (unitMesh n)

/-- **`‖K (I - P_n)‖ ≤ e h²/8`, the estimate Example 12.3.2 states without proof.**  The rows
`y ↦ e^{xy}` of the kernel are `C²` with `|∂²_y e^{xy}| = x² e^{xy} ≤ e` on the unit square, so the
`𝒪(h²)` approximation order of `P_n` applies to them uniformly. -/
theorem norm_expKernelCLM_comp_sub_discGalerkinProj_le {n : ℕ} (hn : 0 < n) :
    ‖expKernelCLM ∘L (1 - discGalerkinProj n)‖ ≤ (1 / (n : ℝ)) ^ 2 / 8 * Real.exp 1 := by
  have key := norm_l2KernelCLM_comp_sub_discPiecewiseLinearProjCLM_le (a := 0) (b := 1)
    zero_le_one (unitMesh_step hn) (unitMesh_first n) (unitMesh_last hn)
    (memLp_prod_iccMeasure expKernel) (G := fun z t => Real.exp ((z : ℝ) * t))
    (fun _ => Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
    (fun _ _ => rfl) (unitMesh_mesh hn) (M := Real.exp 1) ?_
  · simpa [expKernelCLM, discGalerkinProj] using key
  · intro z t ht
    rw [iteratedDeriv_exp_const_mul, abs_of_nonneg (by positivity)]
    have h1 : (z : ℝ) ^ 2 ≤ 1 := by nlinarith [z.2.1, z.2.2]
    have h2 : Real.exp ((z : ℝ) * t) ≤ Real.exp 1 :=
      Real.exp_le_exp.2 (by nlinarith [z.2.1, z.2.2, ht.1, ht.2])
    nlinarith [Real.exp_pos ((z : ℝ) * t), Real.exp_pos (1 : ℝ), sq_nonneg (z : ℝ)]

/-- **(12.3.13) in this example**: `‖K - P_n K‖ = ‖(I - P_n) K*‖ = ‖K (I - P_n)‖ ≤ e h²/8`.  The
first equality is the definition, the second is that an operator and its adjoint have the same
norm together with `isSelfAdjoint_discGalerkinProj`, and the kernel `e^{xy}` being symmetric makes
`K* = K`, so all three quantities coincide here.  This is the input `theorem_12_1_2` needs, and it
replaces the compactness argument of (12.3.15). -/
theorem norm_sub_comp_expKernelCLM_le {n : ℕ} (hn : 0 < n) :
    ‖expKernelCLM - discGalerkinProj n ∘L expKernelCLM‖
      ≤ (1 / (n : ℝ)) ^ 2 / 8 * Real.exp 1 := by
  have hsub : expKernelCLM - discGalerkinProj n ∘L expKernelCLM
      = (1 - discGalerkinProj n) ∘L expKernelCLM := by
    rw [ContinuousLinearMap.sub_comp, show (1 : L² →L[ℝ] L²) ∘L expKernelCLM
      = expKernelCLM from one_mul _]
  have hadj : ContinuousLinearMap.adjoint ((1 - discGalerkinProj n) ∘L expKernelCLM)
      = expKernelCLM ∘L (1 - discGalerkinProj n) := by
    rw [ContinuousLinearMap.adjoint_comp, isSelfAdjoint_expKernelCLM.adjoint_eq,
      (IsSelfAdjoint.sub (IsSelfAdjoint.one _) (isSelfAdjoint_discGalerkinProj n)).adjoint_eq]
  rw [hsub, ← ContinuousLinearMap.adjoint.norm_map, hadj]
  exact norm_expKernelCLM_comp_sub_discGalerkinProj_le hn

/-- If `‖K‖ < |λ|` then `λ - K` is invertible, by the Neumann series; the quantitative form is
`ContinuousLinearEquiv.exists_symm_norm_le_of_add`. -/
private theorem exists_equiv_smul_sub_of_norm_lt {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] [CompleteSpace Y] {μ : ℝ} (hμ : μ ≠ 0) {K : Y →L[ℝ] Y} (h : ‖K‖ < |μ|) :
    ∃ e : Y ≃L[ℝ] Y, (e : Y →L[ℝ] Y) = μ • 1 - K := by
  have habs : (0 : ℝ) < |μ| := abs_pos.2 hμ
  let v : (Y →L[ℝ] Y)ˣ :=
    { val := μ • 1
      inv := μ⁻¹ • 1
      val_inv := by ext x; simp [smul_smul, inv_mul_cancel₀ hμ]
      inv_val := by ext x; simp [smul_smul, mul_inv_cancel₀ hμ] }
  set e₀ : Y ≃L[ℝ] Y := ContinuousLinearEquiv.ofUnit v with he₀def
  have he₀ : (e₀ : Y →L[ℝ] Y) = μ • 1 := by ext x; rfl
  have hsymm : (e₀.symm : Y →L[ℝ] Y) = μ⁻¹ • 1 := by ext y; rfl
  have hns : ‖(e₀.symm : Y →L[ℝ] Y)‖ ≤ |μ|⁻¹ := by
    rw [hsymm, norm_smul, norm_inv, Real.norm_eq_abs]
    calc |μ|⁻¹ * ‖(1 : Y →L[ℝ] Y)‖ ≤ |μ|⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (by positivity)
      _ = |μ|⁻¹ := mul_one _
  have hlt : ‖(e₀.symm : Y →L[ℝ] Y)‖ * ‖(-K : Y →L[ℝ] Y)‖ < 1 := by
    rw [norm_neg]
    calc ‖(e₀.symm : Y →L[ℝ] Y)‖ * ‖K‖ ≤ |μ|⁻¹ * ‖K‖ :=
          mul_le_mul_of_nonneg_right hns (norm_nonneg _)
      _ < 1 := by rw [inv_mul_lt_one₀ habs]; exact h
  obtain ⟨e, he, -, -⟩ := ContinuousLinearEquiv.exists_symm_norm_le_of_add e₀ (-K) hlt
  exact ⟨e, by rw [he, he₀, ← sub_eq_add_neg]⟩

/-- The exact solution `u(x) = e^x` of Example 12.3.2, as a continuous function. -/
noncomputable def expSolutionFun : C(Set.Icc (0 : ℝ) 1, ℝ) := ⟨fun t => Real.exp t, by fun_prop⟩

/-- The exact solution `u(x) = e^x` of Example 12.3.2, as an element of `L²(0, 1)`. -/
noncomputable def expSolution : L² := iccToLp 0 1 expSolutionFun

/-- The right-hand side `f = 50 u - K u` of (12.3.18) at `λ = 50` and `u(x) = e^x`. -/
noncomputable def expRhs : L² := ((50 : ℝ) • 1 - expKernelCLM : L² →L[ℝ] L²) expSolution

/-- **`‖u - P_n u‖ ≤ e h²/8`**, the second input of Example 12.3.2: the solution `u(x) = e^x` is
`C²` with `|u''| ≤ e` on `[0, 1]`, so the `𝒪(h²)` approximation order of the discontinuous
piecewise linear projection applies to it. -/
theorem norm_sub_discGalerkinProj_expSolution_le {n : ℕ} (hn : 0 < n) :
    ‖expSolution - discGalerkinProj n expSolution‖ ≤ (1 / (n : ℝ)) ^ 2 / 8 * Real.exp 1 := by
  have hiter : iteratedDeriv 2 Real.exp = Real.exp := by
    simpa using iteratedDeriv_exp_const_mul 2 1
  have hinterp := norm_sub_piecewiseLinearInterpCLM_le (unitMesh_step hn) (unitMesh_first n)
    (unitMesh_last hn) (g := Real.exp) Real.contDiff_exp (f := expSolutionFun) (fun _ => rfl)
    (unitMesh_mesh hn) (M := Real.exp 1) (fun t ht => by
      rw [hiter, abs_of_pos (Real.exp_pos t)]
      exact Real.exp_le_exp.2 ht.2)
  refine (norm_sub_discPiecewiseLinearProjCLM_le (a := 0) (b := 1) zero_le_one (unitMesh_step hn)
    (unitMesh_first n) (unitMesh_last hn) expSolutionFun).trans ?_
  rw [show (1 : ℝ) - 0 = 1 by ring, Real.sqrt_one, one_mul]
  exact hinterp

/-- **Example 12.3.2**, the iterated Galerkin method for

`50 u(x) - ∫_0^1 e^{xy} u(y) dy = f(x)`,   `0 ≤ x ≤ 1`,   **(12.3.18)**

with the exact solution `u(x) = e^x`, over the *discontinuous* piecewise linear functions on the
uniform mesh of width `h = 1/n`.  For all large `n` the Galerkin equations
`(50 - P_n K) u_n = P_n f` are uniquely solvable, and

* `‖u - u_n‖_{L²} ≤ c₁ h²`   **(12.3.19)**,
* `‖u - û_n‖_{L²} ≤ c₂ h⁴`   **(12.3.20)**,

the second being the Sloan superconvergence of the iterated solution `û_n = (f + K u_n)/50`.

The two inputs the book asserts without proof are `norm_sub_comp_expKernelCLM_le`, which is
`‖(I - P_n) K*‖ = 𝒪(h²)` in the form `‖K - P_n K‖ = 𝒪(h²)` — the same quantity, since `P_n` is
self-adjoint and the kernel is symmetric — and `norm_sub_discGalerkinProj_expSolution_le`, which
is `‖u - P_n u‖ = 𝒪(h²)`.  Given those, (12.3.19) is `equation_12_1_24` and (12.3.20) is
`equation_12_3_11`, whose right-hand side carries the *product* of the two.  Unique solvability
comes from `theorem_12_1_2`; its hypothesis `‖K - P_n K‖ → 0` is here an explicit `𝒪(h²)` bound
rather than the compactness argument of (12.3.15), and the invertibility of `50 - K` is the
Neumann series, since `‖K‖ ≤ e < 50`.

**Table 12.2 is not formalized**: it is measured error data for `n = 2, 4, 8` produced by running
the method, not mathematics.  What the table confirms is the pair of rates above, and those are
what is proved here.  The constants `c₁` and `c₂` are existentially quantified, as in
`equation_12_2_19`; the proof produces `c₁ = 25 e ‖(50 - K)⁻¹‖` and a `c₂` of the same shape,
which the book does not state either. -/
theorem example_12_3_2 :
    ∃ c₁ c₂ : ℝ, ∀ᶠ n : ℕ in atTop,
      (∀ f : L², ∃! un : L²,
        IsProjectionSolution (50 : ℝ) expKernelCLM (discGalerkinProj n) f un) ∧
      ∀ un : L²,
        IsProjectionSolution (50 : ℝ) expKernelCLM (discGalerkinProj n) expRhs un →
          ‖expSolution - un‖ ≤ c₁ * (1 / (n : ℝ)) ^ 2 ∧
          ‖expSolution - iteratedSolution (50 : ℝ) expKernelCLM expRhs un‖
            ≤ c₂ * (1 / (n : ℝ)) ^ 4 := by
  obtain ⟨e, he⟩ := exists_equiv_smul_sub_of_norm_lt (μ := (50 : ℝ)) (by norm_num)
    norm_expKernelCLM_lt
  set A : ℝ := ‖(e.symm : L² →L[ℝ] L²)‖ with hAdef
  have hA0 : (0 : ℝ) ≤ A := norm_nonneg _
  set B : ℝ := 1 / 50 * (1 + Real.exp 1 * (2 * A)) with hBdef
  refine ⟨50 * (2 * A) * (Real.exp 1 / 8), B * (Real.exp 1 / 8) * (Real.exp 1 / 8), ?_⟩
  have hu : ((50 : ℝ) • 1 - expKernelCLM : L² →L[ℝ] L²) expSolution = expRhs := rfl
  have htend : Tendsto (fun n : ℕ => A * ((1 / (n : ℝ)) ^ 2 / 8 * Real.exp 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (1 / (n : ℝ))) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h2 := ((h1.pow 2).div_const 8).const_mul (Real.exp 1)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h2.const_mul A
  filter_upwards [eventually_gt_atTop 0,
    htend.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with n hn hsmall
  have hKP := norm_sub_comp_expKernelCLM_le hn
  have hprod : A * ‖expKernelCLM - discGalerkinProj n ∘L expKernelCLM‖ < 1 / 2 :=
    lt_of_le_of_lt (by gcongr) hsmall
  obtain ⟨e', he'coe, he'norm, huniq⟩ := theorem_12_1_2 (μ := (50 : ℝ)) (by norm_num)
    (isIdempotentElem_discGalerkinProj n) e he (by rw [← hAdef]; linarith)
  have hb1 : ‖(e'.symm : L² →L[ℝ] L²)‖ ≤ 2 * A := by
    refine he'norm.trans ?_
    rw [← hAdef, div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (expKernelCLM - discGalerkinProj n ∘L expKernelCLM)]
  refine ⟨huniq, fun un hun => ⟨?_, ?_⟩⟩
  · -- (12.3.19), from (12.1.24)
    have hkey := (equation_12_1_24 (isIdempotentElem_discGalerkinProj n) he'coe hu hun).2
    have hproj := norm_sub_discGalerkinProj_expSolution_le hn
    calc ‖expSolution - un‖
        ≤ ‖(50 : ℝ)‖ * ‖(e'.symm : L² →L[ℝ] L²)‖
            * ‖expSolution - discGalerkinProj n expSolution‖ := hkey
      _ ≤ 50 * (2 * A) * ((1 / (n : ℝ)) ^ 2 / 8 * Real.exp 1) := by
          rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 50)]
          gcongr
      _ = 50 * (2 * A) * (Real.exp 1 / 8) * (1 / (n : ℝ)) ^ 2 := by ring
  · -- (12.3.20), from (12.3.11)
    obtain ⟨e'', he''coe, -, he''norm⟩ := lemma_12_3_1_projection (μ := (50 : ℝ)) (by norm_num)
      expKernelCLM (discGalerkinProj n) he'coe
    have hP : ‖discGalerkinProj n‖ ≤ 1 :=
      norm_discPiecewiseLinearProjCLM_le_one 0 1 (n - 1) (unitMesh n)
    have hb2 : ‖(e''.symm : L² →L[ℝ] L²)‖ ≤ B := by
      refine he''norm.trans ?_
      rw [hBdef, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 50)]
      have hep : ‖(e'.symm : L² →L[ℝ] L²)‖ * ‖discGalerkinProj n‖ ≤ 2 * A := by
        calc ‖(e'.symm : L² →L[ℝ] L²)‖ * ‖discGalerkinProj n‖
            ≤ (2 * A) * 1 := mul_le_mul hb1 hP (norm_nonneg _) (by linarith)
          _ = 2 * A := mul_one _
      have hmul : ‖expKernelCLM‖ * (‖(e'.symm : L² →L[ℝ] L²)‖ * ‖discGalerkinProj n‖)
          ≤ Real.exp 1 * (2 * A) :=
        mul_le_mul norm_expKernelCLM_le hep (by positivity) (Real.exp_nonneg 1)
      rw [inv_eq_one_div]
      exact mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    have hkey := (equation_12_3_11 (μ := (50 : ℝ)) (by norm_num)
      (isIdempotentElem_discGalerkinProj n) he''coe hu hun).2
    have hproj := norm_sub_discGalerkinProj_expSolution_le hn
    have hcomp := norm_expKernelCLM_comp_sub_discGalerkinProj_le hn
    calc ‖expSolution - iteratedSolution (50 : ℝ) expKernelCLM expRhs un‖
        ≤ ‖(e''.symm : L² →L[ℝ] L²)‖ * ‖expKernelCLM ∘L (1 - discGalerkinProj n)‖
            * ‖expSolution - discGalerkinProj n expSolution‖ := hkey
      _ ≤ B * ((1 / (n : ℝ)) ^ 2 / 8 * Real.exp 1) * ((1 / (n : ℝ)) ^ 2 / 8 * Real.exp 1) := by
          have hB0 : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) hb2
          have hX0 : (0 : ℝ) ≤ (1 / (n : ℝ)) ^ 2 / 8 * Real.exp 1 := by positivity
          exact mul_le_mul (mul_le_mul hb2 hcomp (norm_nonneg _) hB0) hproj (norm_nonneg _)
            (mul_nonneg hB0 hX0)
      _ = B * (Real.exp 1 / 8) * (Real.exp 1 / 8) * (1 / (n : ℝ)) ^ 4 := by ring

end IteratedGalerkin

end AtkinsonHan.Chapter12
