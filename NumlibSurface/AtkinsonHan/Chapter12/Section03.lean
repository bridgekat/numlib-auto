import NumlibSurface.AtkinsonHan.Chapter12.Section01

/-!
# Atkinson–Han §12.3: iterated projection methods

Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009.

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

## Not formalized here

Theorem 12.3.3, a piecewise quadratic collocation error estimate on `C[a, b]` needing `u ∈ C⁴` and
an interpolation error bound; the concrete parts of §12.3.2; and the linear system for the
iterated collocation solution.

## Conventions

The book derives the bound of `equation_12_3_11` for an *orthogonal* projection in a Hilbert
space, from `(I - P_n)² = I - P_n`.  Only that idempotency is used, so the statement here asks
for nothing but `IsIdempotentElem P` and holds on a Banach space; the Galerkin case is the
specialization to an orthogonal projection.
-/

open Filter Topology

namespace AtkinsonHan.Ch12

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

end AtkinsonHan.Ch12
