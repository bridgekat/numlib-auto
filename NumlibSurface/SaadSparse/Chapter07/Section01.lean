import Numlib.Analysis.InnerProductSpace.Projection.ObliqueProjection
import Numlib.Krylov.BiLanczos
import NumlibSurface.SaadSparse.Chapter06.Common

/-!
# Saad §7.1: the Lanczos biorthogonalization procedure

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §7.1, with P-7.2 and P-7.6.

**Algorithm 7.1** is `bilanczos`, whose state carries the pair `(v_j, w_j)`, the previous pair and
the two scalars the next step consumes; `bilanczosV`, `bilanczosW`, `bilanczosVhat`,
`bilanczosWhat`, `bilanczosAlpha`, `bilanczosBeta` and `bilanczosDelta` read the seven quantities
the algorithm names off it, and `bilanczosDelta_succ`, `bilanczosBeta_succ`, `bilanczosW_succ`,
`bilanczosV_succ` are its lines 7–10. The pivot is `bilanczosV_eq` and `bilanczosW_eq`: the book's
recursion, with its explicit normalization `δ_{j+1} = |(v̂_{j+1}, ŵ_{j+1})|^{1/2}`,
`β_{j+1} = (v̂_{j+1}, ŵ_{j+1})/δ_{j+1}`, computes the backbone `BiLanczos.vec` and
`BiLanczos.dualVec` of `Numlib/Krylov/BiLanczos.lean`, so Proposition 7.1 and everything after it
are read off from there.

`NoBreakdown` bundles the hypothesis the book carries through §7.1: the starting pair is
normalized, `(v_1, w_1) = 1`, and the test of line 7 passes, `(v̂_{j+1}, ŵ_{j+1}) ≠ 0`, for every
`j < m`. Lean's "division by zero is zero" makes every vector after a breakdown `0`, which is the
book's "Stop", so the definitions are total. `NoSeriousBreakdown` is the weaker global hypothesis
the Hessenberg relation needs: a vanishing `(v̂_{j+1}, ŵ_{j+1})` must come with `v̂_{j+1} = 0`.
It is not implied by `NoBreakdown m` for any `m` — in finite dimension the process always
terminates — and (7.3) is *false* at a serious breakdown, where there is no `v_{m+1}` to expand
`A v_m` along.

The matrices `V_m`, `W_m`, `T_m` and `T̄_m` of (7.2) and (7.15) are `V`, `W`, `T` and `Tbar`;
(7.3), (7.4) and (7.15) are `equation_7_3` and (7.5) is `equation_7_5`.

§7.1.2 — look-ahead Lanczos, the indefinite bilinear form (7.7), the Hankel moment matrix and its
`LU` factorization — contains no statement the book proves and is not formalized; see
`plans/saadsparse-ch7-9.md` §4.

Indices are `0`-based: `bilanczosV A v₁ w₁ j` is the book's `v_{j+1}` and
`bilanczosDelta A v₁ w₁ j` its `δ_{j+1}`, so that `bilanczosDelta A v₁ w₁ 0 = 0` is the book's
`δ_1 = 0`.
-/

open Matrix

open scoped Matrix SaadSparse

namespace SaadSparse.Chapter07

open Chapter06 (op)

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-! ### The dual starting vector -/

section Start

/-- The dual starting vector `w_1` of Algorithm 7.1, line 1: a vector `w` — in Algorithm 7.3 the
dual residual `r_0^* = b^* - Aᴴ x_0^*` — rescaled so that the book's normalization
`(v_1, w_1) = 1` holds. It is `0` when `w ⟂ v_1`, where no such rescaling exists, by Lean's
`(0 : 𝕜)⁻¹ = 0`. -/
noncomputable def w₁ (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ w : EuclideanSpace 𝕜 (Fin n)) :
    EuclideanSpace 𝕜 (Fin n) :=
  (inner 𝕜 (Chapter06.v₁ A b x₀) w)⁻¹ • w

/-- Algorithm 7.1, line 1: the normalization `(v_1, w_1) = 1`, which in Mathlib's convention
(conjugate-linear in the *first* slot) reads `⟪w_1, v_1⟫ = 1`. -/
theorem inner_w₁_v₁ (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ w : EuclideanSpace 𝕜 (Fin n))
    (hw : inner 𝕜 (Chapter06.v₁ A b x₀) w ≠ 0) :
    inner 𝕜 (w₁ A b x₀ w) (Chapter06.v₁ A b x₀) = 1 := by
  have hconj : starRingEnd 𝕜 (inner 𝕜 (Chapter06.v₁ A b x₀) w) = inner 𝕜 w (Chapter06.v₁ A b x₀) :=
    inner_conj_symm _ _
  rw [w₁, inner_smul_left, map_inv₀, hconj, inv_mul_cancel₀]
  rw [← hconj]
  exact fun h => hw (by simpa using congrArg (starRingEnd 𝕜) h)

end Start

/-! ### Algorithm 7.1 -/

section Algorithm

variable (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ w₁ : EuclideanSpace 𝕜 (Fin n))

/-- One pass through lines 4–10 of **Algorithm 7.1**, on the state `(v_j, w_j, v_{j-1}, w_{j-1},
β_j, δ_j)`. The backbone record `BiLanczos.State` carries exactly that data. -/
noncomputable def bilanczosStep (s : BiLanczos.State 𝕜 (EuclideanSpace 𝕜 (Fin n))) :
    BiLanczos.State 𝕜 (EuclideanSpace 𝕜 (Fin n)) :=
  let α : 𝕜 := inner 𝕜 s.w (op A s.v)
  let vh : EuclideanSpace 𝕜 (Fin n) := op A s.v - α • s.v - s.beta • s.vPrev
  let wh : EuclideanSpace 𝕜 (Fin n) :=
    op Aᴴ s.w - starRingEnd 𝕜 α • s.w - starRingEnd 𝕜 s.delta • s.wPrev
  let δ : 𝕜 := ((Real.sqrt ‖inner 𝕜 wh vh‖ : ℝ) : 𝕜)
  { v := δ⁻¹ • vh
    w := (starRingEnd 𝕜 (inner 𝕜 wh vh / δ))⁻¹ • wh
    vPrev := s.v
    wPrev := s.w
    beta := inner 𝕜 wh vh / δ
    delta := δ }

/-- **Algorithm 7.1** (Lanczos biorthogonalization) run for `j` steps from the pair
`(v_1, w_1)`. -/
noncomputable def bilanczos (j : ℕ) : BiLanczos.State 𝕜 (EuclideanSpace 𝕜 (Fin n)) :=
  (bilanczosStep A)^[j] { v := v₁, w := w₁, vPrev := 0, wPrev := 0, beta := 0, delta := 0 }

/-- The primal Lanczos vectors `v_j` of Algorithm 7.1. -/
noncomputable def bilanczosV (j : ℕ) : EuclideanSpace 𝕜 (Fin n) := (bilanczos A v₁ w₁ j).v

/-- The dual Lanczos vectors `w_j` of Algorithm 7.1. -/
noncomputable def bilanczosW (j : ℕ) : EuclideanSpace 𝕜 (Fin n) := (bilanczos A v₁ w₁ j).w

/-- `v_{j-1}`, with the convention `v_0 = 0` of Algorithm 7.1, line 2. -/
noncomputable def bilanczosVPrev (j : ℕ) : EuclideanSpace 𝕜 (Fin n) := (bilanczos A v₁ w₁ j).vPrev

/-- `w_{j-1}`, with the convention `w_0 = 0` of Algorithm 7.1, line 2. -/
noncomputable def bilanczosWPrev (j : ℕ) : EuclideanSpace 𝕜 (Fin n) := (bilanczos A v₁ w₁ j).wPrev

/-- The superdiagonal coefficient `β_{j+1}` of Algorithm 7.1, line 8, with `β_1 = 0`. -/
noncomputable def bilanczosBeta (j : ℕ) : 𝕜 := (bilanczos A v₁ w₁ j).beta

/-- The subdiagonal coefficient `δ_{j+1}` of Algorithm 7.1, line 7, with `δ_1 = 0`. -/
noncomputable def bilanczosDelta (j : ℕ) : 𝕜 := (bilanczos A v₁ w₁ j).delta

/-- The diagonal coefficient `α_j = (A v_j, w_j)` of Algorithm 7.1, line 4. -/
noncomputable def bilanczosAlpha (j : ℕ) : 𝕜 :=
  inner 𝕜 (bilanczosW A v₁ w₁ j) (op A (bilanczosV A v₁ w₁ j))

/-- The unnormalized vector `v̂_{j+1} = A v_j - α_j v_j - β_j v_{j-1}` of Algorithm 7.1,
line 5. -/
noncomputable def bilanczosVhat (j : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  op A (bilanczosV A v₁ w₁ j) - bilanczosAlpha A v₁ w₁ j • bilanczosV A v₁ w₁ j -
    bilanczosBeta A v₁ w₁ j • bilanczosVPrev A v₁ w₁ j

/-- The unnormalized vector `ŵ_{j+1} = Aᴴ w_j - ᾱ_j w_j - δ̄_j w_{j-1}` of Algorithm 7.1,
line 6. -/
noncomputable def bilanczosWhat (j : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  op Aᴴ (bilanczosW A v₁ w₁ j) - starRingEnd 𝕜 (bilanczosAlpha A v₁ w₁ j) • bilanczosW A v₁ w₁ j -
    starRingEnd 𝕜 (bilanczosDelta A v₁ w₁ j) • bilanczosWPrev A v₁ w₁ j

/-! ### The bridge to the backbone two-sided Lanczos process -/

private theorem bilanczosStep_eq (s : BiLanczos.State 𝕜 (EuclideanSpace 𝕜 (Fin n))) :
    bilanczosStep A s = BiLanczos.step (op A) (op Aᴴ) s := rfl

private theorem bilanczos_eq (j : ℕ) :
    bilanczos A v₁ w₁ j = BiLanczos.state (op A) (op Aᴴ) v₁ w₁ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [bilanczos, Function.iterate_succ_apply', ← bilanczos, ih, bilanczosStep_eq,
      ← BiLanczos.state_succ]

/-- **The bridge to the backbone**: the primal sequence of Algorithm 7.1 is the backbone
two-sided Lanczos sequence of `op A` and its adjoint `op Aᴴ`. -/
theorem bilanczosV_eq (j : ℕ) :
    bilanczosV A v₁ w₁ j = BiLanczos.vec (op A) (op Aᴴ) v₁ w₁ j := by
  rw [bilanczosV, bilanczos_eq]; rfl

/-- The dual sequence of Algorithm 7.1 is the backbone dual sequence. -/
theorem bilanczosW_eq (j : ℕ) :
    bilanczosW A v₁ w₁ j = BiLanczos.dualVec (op A) (op Aᴴ) v₁ w₁ j := by
  rw [bilanczosW, bilanczos_eq]; rfl

/-- The shifted primal sequence `v_{j-1}` of Algorithm 7.1 is the backbone one. -/
theorem bilanczosVPrev_eq (j : ℕ) :
    bilanczosVPrev A v₁ w₁ j = BiLanczos.vecPrev (op A) (op Aᴴ) v₁ w₁ j := by
  rw [bilanczosVPrev, bilanczos_eq]; rfl

/-- The shifted dual sequence `w_{j-1}` of Algorithm 7.1 is the backbone one. -/
theorem bilanczosWPrev_eq (j : ℕ) :
    bilanczosWPrev A v₁ w₁ j = BiLanczos.dualVecPrev (op A) (op Aᴴ) v₁ w₁ j := by
  rw [bilanczosWPrev, bilanczos_eq]; rfl

/-- The superdiagonal coefficients of Algorithm 7.1 are the backbone ones. -/
theorem bilanczosBeta_eq (j : ℕ) :
    bilanczosBeta A v₁ w₁ j = BiLanczos.beta (op A) (op Aᴴ) v₁ w₁ j := by
  rw [bilanczosBeta, bilanczos_eq]; rfl

/-- The subdiagonal coefficients of Algorithm 7.1 are the backbone ones. -/
theorem bilanczosDelta_eq (j : ℕ) :
    bilanczosDelta A v₁ w₁ j = BiLanczos.delta (op A) (op Aᴴ) v₁ w₁ j := by
  rw [bilanczosDelta, bilanczos_eq]; rfl

/-- The diagonal coefficients of Algorithm 7.1 are the backbone ones. -/
theorem bilanczosAlpha_eq (j : ℕ) :
    bilanczosAlpha A v₁ w₁ j = BiLanczos.alpha (op A) (op Aᴴ) v₁ w₁ j := by
  rw [bilanczosAlpha, bilanczosV_eq, bilanczosW_eq]; rfl

/-- The unnormalized primal vectors of Algorithm 7.1, line 5, are the backbone ones. -/
theorem bilanczosVhat_eq (j : ℕ) :
    bilanczosVhat A v₁ w₁ j = BiLanczos.vhat (op A) (op Aᴴ) v₁ w₁ j := by
  rw [bilanczosVhat, bilanczosV_eq, bilanczosVPrev_eq, bilanczosAlpha_eq, bilanczosBeta_eq,
    BiLanczos.vhat_eq]

/-- The unnormalized dual vectors of Algorithm 7.1, line 6, are the backbone ones. -/
theorem bilanczosWhat_eq (j : ℕ) :
    bilanczosWhat A v₁ w₁ j = BiLanczos.dualVhat (op A) (op Aᴴ) v₁ w₁ j := by
  rw [bilanczosWhat, bilanczosW_eq, bilanczosWPrev_eq, bilanczosAlpha_eq, bilanczosDelta_eq,
    BiLanczos.dualVhat_eq]

/-! ### Lines 1 and 6–9 of Algorithm 7.1 -/

/-- Algorithm 7.1, line 1: the primal sequence starts at `v_1`. -/
@[simp] theorem bilanczosV_zero : bilanczosV A v₁ w₁ 0 = v₁ := rfl

/-- Algorithm 7.1, line 1: the dual sequence starts at `w_1`. -/
@[simp] theorem bilanczosW_zero : bilanczosW A v₁ w₁ 0 = w₁ := rfl

/-- Algorithm 7.1, line 2: `v_0 = 0`. -/
@[simp] theorem bilanczosVPrev_zero : bilanczosVPrev A v₁ w₁ 0 = 0 := rfl

/-- Algorithm 7.1, line 2: `w_0 = 0`. -/
@[simp] theorem bilanczosWPrev_zero : bilanczosWPrev A v₁ w₁ 0 = 0 := rfl

/-- Algorithm 7.1, line 2: `β_1 = 0`. -/
@[simp] theorem bilanczosBeta_zero : bilanczosBeta A v₁ w₁ 0 = 0 := rfl

/-- Algorithm 7.1, line 2: `δ_1 = 0`. -/
@[simp] theorem bilanczosDelta_zero : bilanczosDelta A v₁ w₁ 0 = 0 := rfl

/-- After step `j + 1` the previous-vector slot of the state holds `v_j`. -/
@[simp] theorem bilanczosVPrev_succ (j : ℕ) :
    bilanczosVPrev A v₁ w₁ (j + 1) = bilanczosV A v₁ w₁ j := by
  rw [bilanczosVPrev_eq, bilanczosV_eq, BiLanczos.vecPrev_succ]

/-- After step `j + 1` the previous-vector slot of the dual state holds `w_j`. -/
@[simp] theorem bilanczosWPrev_succ (j : ℕ) :
    bilanczosWPrev A v₁ w₁ (j + 1) = bilanczosW A v₁ w₁ j := by
  rw [bilanczosWPrev_eq, bilanczosW_eq, BiLanczos.dualVecPrev_succ]

/-- Algorithm 7.1, line 7: `δ_{j+1} = |(v̂_{j+1}, ŵ_{j+1})|^{1/2}`. -/
theorem bilanczosDelta_succ (j : ℕ) : bilanczosDelta A v₁ w₁ (j + 1) =
    ((Real.sqrt ‖inner 𝕜 (bilanczosWhat A v₁ w₁ j) (bilanczosVhat A v₁ w₁ j)‖ : ℝ) : 𝕜) := by
  rw [bilanczosDelta_eq, bilanczosWhat_eq, bilanczosVhat_eq, BiLanczos.delta_succ]
  rfl

/-- Algorithm 7.1, line 8: `β_{j+1} = (v̂_{j+1}, ŵ_{j+1})/δ_{j+1}`. -/
theorem bilanczosBeta_succ (j : ℕ) : bilanczosBeta A v₁ w₁ (j + 1) =
    inner 𝕜 (bilanczosWhat A v₁ w₁ j) (bilanczosVhat A v₁ w₁ j) /
      bilanczosDelta A v₁ w₁ (j + 1) := by
  rw [bilanczosBeta_eq, bilanczosWhat_eq, bilanczosVhat_eq, bilanczosDelta_eq,
    BiLanczos.beta_succ]
  rfl

/-- Algorithm 7.1, line 9: `w_{j+1} = ŵ_{j+1}/β̄_{j+1}`, and `0` on breakdown. -/
theorem bilanczosW_succ (j : ℕ) : bilanczosW A v₁ w₁ (j + 1) =
    (starRingEnd 𝕜 (bilanczosBeta A v₁ w₁ (j + 1)))⁻¹ • bilanczosWhat A v₁ w₁ j := by
  rw [bilanczosW_eq, bilanczosWhat_eq, bilanczosBeta_eq, BiLanczos.dualVec_succ]

/-- Algorithm 7.1, line 10: `v_{j+1} = v̂_{j+1}/δ_{j+1}`, and `0` on breakdown. -/
theorem bilanczosV_succ (j : ℕ) : bilanczosV A v₁ w₁ (j + 1) =
    (bilanczosDelta A v₁ w₁ (j + 1))⁻¹ • bilanczosVhat A v₁ w₁ j := by
  rw [bilanczosV_eq, bilanczosVhat_eq, bilanczosDelta_eq, BiLanczos.vec_succ]

end Algorithm

/-! ### The no-breakdown hypotheses -/

section Breakdown

variable {A : Matrix (Fin n) (Fin n) 𝕜} {v₁ w₁ : EuclideanSpace 𝕜 (Fin n)}

/-- Algorithm 7.1 runs `m` steps without breaking down: the starting pair is normalized as in
line 1, and the test of line 7, `(v̂_{j+1}, ŵ_{j+1}) ≠ 0`, passes for every `j < m`. This is the
hypothesis the book carries through §7.1, and it is the surface form of
`BiLanczos.NoBreakdown`; the adjoint relation the backbone takes as data is automatic here,
`op Aᴴ` being the adjoint of `op A`. -/
structure NoBreakdown (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ w₁ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) :
    Prop where
  /-- Line 1: `(v_1, w_1) = 1`. -/
  inner_start : inner 𝕜 w₁ v₁ = 1
  /-- Line 6 does not stop the algorithm before step `m`. -/
  inner_hat_ne_zero : ∀ j < m,
    inner 𝕜 (bilanczosWhat A v₁ w₁ j) (bilanczosVhat A v₁ w₁ j) ≠ 0

/-- Algorithm 7.1 suffers no *serious* breakdown: whenever line 7 stops the algorithm, the primal
recurrence has already terminated, `v̂_{j+1} = 0`. This holds generically and at a regular
termination, and unlike `SaadSparse.Chapter07.NoBreakdown` it is a hypothesis about every step —
which is what (7.3) needs, since at a serious breakdown there is no `v_{m+1}` to expand `A v_m`
along and the relation is genuinely false. -/
structure NoSeriousBreakdown (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ w₁ : EuclideanSpace 𝕜 (Fin n)) : Prop where
  /-- At a breakdown the primal recurrence has already terminated. -/
  vhat_eq_zero : ∀ j, inner 𝕜 (bilanczosWhat A v₁ w₁ j) (bilanczosVhat A v₁ w₁ j) = 0 →
    bilanczosVhat A v₁ w₁ j = 0

/-- `op Aᴴ` is the adjoint of `op A`. -/
theorem inner_op_conjTranspose (A : Matrix (Fin n) (Fin n) 𝕜)
    (x y : EuclideanSpace 𝕜 (Fin n)) : inner 𝕜 (op A x) y = inner 𝕜 x (op Aᴴ y) := by
  have hadj : (op Aᴴ) = LinearMap.adjoint (op A) := Matrix.toEuclideanLin_conjTranspose A
  rw [hadj, LinearMap.adjoint_inner_right]

private theorem zeta_eq (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ w₁ : EuclideanSpace 𝕜 (Fin n))
    (j : ℕ) : inner 𝕜 (bilanczosWhat A v₁ w₁ j) (bilanczosVhat A v₁ w₁ j)
      = BiLanczos.zeta (op A) (op Aᴴ) v₁ w₁ j := by
  rw [bilanczosWhat_eq, bilanczosVhat_eq, BiLanczos.zeta]

/-- Running `m` steps without breakdown entails running `k ≤ m` steps without breakdown. -/
theorem NoBreakdown.mono {m k : ℕ} (h : NoBreakdown A v₁ w₁ m) (hk : k ≤ m) :
    NoBreakdown A v₁ w₁ k :=
  ⟨h.inner_start, fun j hj => h.inner_hat_ne_zero j (hj.trans_le hk)⟩

/-- The surface no-breakdown hypothesis is the backbone one. -/
theorem NoBreakdown.toBiLanczos {m : ℕ} (h : NoBreakdown A v₁ w₁ m) :
    BiLanczos.NoBreakdown (op A) (op Aᴴ) v₁ w₁ m where
  adjoint := inner_op_conjTranspose A
  inner_start := h.inner_start
  delta_ne_zero j hj := by
    rw [← bilanczosDelta_eq]
    intro hc
    refine h.inner_hat_ne_zero j hj ?_
    rw [zeta_eq, ← BiLanczos.delta_succ_eq_zero_iff, ← bilanczosDelta_eq]
    exact hc

/-- The surface no-serious-breakdown hypothesis is the backbone one. -/
theorem NoSeriousBreakdown.toBiLanczos (h : NoSeriousBreakdown A v₁ w₁) :
    BiLanczos.NoSeriousBreakdown (op A) (op Aᴴ) v₁ w₁ where
  vhat_eq_zero j hj := by
    rw [← bilanczosVhat_eq]
    refine h.vhat_eq_zero j ?_
    rw [zeta_eq, ← BiLanczos.delta_succ_eq_zero_iff, ← bilanczosDelta_eq, bilanczosDelta_eq]
    exact hj

/-- Off breakdown, `δ_{j+1} ≠ 0`. -/
theorem bilanczosDelta_ne_zero {m : ℕ} (h : NoBreakdown A v₁ w₁ m) {j : ℕ} (hj : j < m) :
    bilanczosDelta A v₁ w₁ (j + 1) ≠ 0 := by
  rw [bilanczosDelta_eq]
  exact h.toBiLanczos.delta_ne_zero j hj

end Breakdown

/-! ### (7.2) and (7.15): the matrices `V_m`, `W_m`, `T_m` and `T̄_m` -/

section Matrices

variable (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ w₁ : EuclideanSpace 𝕜 (Fin n))

/-- The tridiagonal coefficient function of (7.2): `α_j` on the diagonal, `β_{j+1}` one above and
`δ_{j+1}` one below, `0` elsewhere. -/
noncomputable def bilanczosCoeff (i j : ℕ) : 𝕜 :=
  if i = j then bilanczosAlpha A v₁ w₁ i
  else if i = j + 1 then bilanczosDelta A v₁ w₁ i
  else if j = i + 1 then bilanczosBeta A v₁ w₁ j
  else 0

/-- The tridiagonal coefficient function is the backbone one. -/
theorem bilanczosCoeff_eq (i j : ℕ) :
    bilanczosCoeff A v₁ w₁ i j = BiLanczos.coeff (op A) (op Aᴴ) v₁ w₁ i j := by
  rw [bilanczosCoeff, BiLanczos.coeff, bilanczosAlpha_eq, bilanczosDelta_eq, bilanczosBeta_eq]

/-- The diagonal entry of `T_m` is `α_j`. -/
@[simp] theorem bilanczosCoeff_self (j : ℕ) :
    bilanczosCoeff A v₁ w₁ j j = bilanczosAlpha A v₁ w₁ j := by
  rw [bilanczosCoeff, ite_eq_left rfl]

/-- The subdiagonal entry of `T_m` is `δ_{j+1}`. -/
@[simp] theorem bilanczosCoeff_succ_self (j : ℕ) :
    bilanczosCoeff A v₁ w₁ (j + 1) j = bilanczosDelta A v₁ w₁ (j + 1) := by
  rw [bilanczosCoeff, ite_eq_right (by omega), ite_eq_left rfl]

/-- The superdiagonal entry of `T_m` is `β_{j+1}`. -/
@[simp] theorem bilanczosCoeff_self_succ (j : ℕ) :
    bilanczosCoeff A v₁ w₁ j (j + 1) = bilanczosBeta A v₁ w₁ (j + 1) := by
  rw [bilanczosCoeff, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

/-- Off the three diagonals the coefficient array vanishes. -/
theorem bilanczosCoeff_eq_zero {i j : ℕ} (h₁ : i ≠ j) (h₂ : i ≠ j + 1) (h₃ : j ≠ i + 1) :
    bilanczosCoeff A v₁ w₁ i j = 0 := by
  rw [bilanczosCoeff, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃]

/-- The coefficient array is upper Hessenberg, indeed tridiagonal. -/
theorem bilanczosCoeff_eq_zero_of_lt {i j : ℕ} (h : j + 1 < i) : bilanczosCoeff A v₁ w₁ i j = 0 :=
  bilanczosCoeff_eq_zero A v₁ w₁ (by omega) (by omega) (by omega)

/-- (7.2): the tridiagonal matrix `T_m` of the two-sided Lanczos process. -/
noncomputable def T (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  Matrix.of fun i j => bilanczosCoeff A v₁ w₁ i j

/-- (7.15): the `(m+1) × m` matrix `T̄_m`, `T_m` with the row `δ_{m+1} e_mᵀ` appended. -/
noncomputable def Tbar (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) 𝕜 :=
  Matrix.of fun i j => bilanczosCoeff A v₁ w₁ i j

/-- `V_m = [v_1, …, v_m]`, the matrix whose columns are the primal Lanczos vectors. -/
noncomputable def V (m : ℕ) : Matrix (Fin n) (Fin m) 𝕜 := Chapter06.colMatrix (bilanczosV A v₁ w₁) m

/-- `W_m = [w_1, …, w_m]`, the matrix whose columns are the dual Lanczos vectors. -/
noncomputable def W (m : ℕ) : Matrix (Fin n) (Fin m) 𝕜 := Chapter06.colMatrix (bilanczosW A v₁ w₁) m

/-- The entries of `T_m` are the tridiagonal coefficients. -/
@[simp] theorem T_apply {m : ℕ} (i j : Fin m) : T A v₁ w₁ m i j = bilanczosCoeff A v₁ w₁ i j := rfl

/-- The entries of `T̄_m` are the tridiagonal coefficients. -/
@[simp] theorem Tbar_apply {m : ℕ} (i : Fin (m + 1)) (j : Fin m) :
    Tbar A v₁ w₁ m i j = bilanczosCoeff A v₁ w₁ i j := rfl

/-- The columns of `V_m` are the primal Lanczos vectors. -/
@[simp] theorem V_apply {m : ℕ} (i : Fin n) (j : Fin m) :
    V A v₁ w₁ m i j = bilanczosV A v₁ w₁ (j : ℕ) i := rfl

/-- The columns of `W_m` are the dual Lanczos vectors. -/
@[simp] theorem W_apply {m : ℕ} (i : Fin n) (j : Fin m) :
    W A v₁ w₁ m i j = bilanczosW A v₁ w₁ (j : ℕ) i := rfl

/-- `T̄_m` is the backbone Hessenberg matrix of the tridiagonal coefficient array. -/
theorem Tbar_eq_hessenbergOf (m : ℕ) :
    Tbar A v₁ w₁ m = Krylov.hessenbergOf (bilanczosCoeff A v₁ w₁) m := rfl

/-- `T_m` is the backbone square Hessenberg matrix of the tridiagonal coefficient array. -/
theorem T_eq_hessenbergSqOf (m : ℕ) :
    T A v₁ w₁ m = Krylov.hessenbergSqOf (bilanczosCoeff A v₁ w₁) m := rfl

end Matrices

/-! ### Proposition 7.1 -/

section Proposition

variable {A : Matrix (Fin n) (Fin n) 𝕜} {v₁ w₁ : EuclideanSpace 𝕜 (Fin n)} {m : ℕ}

/-- **Proposition 7.1**: as long as Algorithm 7.1 has not broken down, the two families are
biorthogonal, `(v_j, w_i) = δ_ij`. -/
theorem proposition_7_1 (h : NoBreakdown A v₁ w₁ m) {i j : ℕ} (hi : i ≤ m) (hj : j ≤ m) :
    inner 𝕜 (bilanczosW A v₁ w₁ i) (bilanczosV A v₁ w₁ j) = if i = j then 1 else 0 := by
  rw [bilanczosW_eq, bilanczosV_eq]
  exact BiLanczos.inner_dualVec_vec h.toBiLanczos hi hj

/-- **Proposition 7.1** in the other order: `(w_j, v_i) = δ_ij`. -/
theorem proposition_7_1' (h : NoBreakdown A v₁ w₁ m) {i j : ℕ} (hi : i ≤ m) (hj : j ≤ m) :
    inner 𝕜 (bilanczosV A v₁ w₁ i) (bilanczosW A v₁ w₁ j) = if i = j then 1 else 0 := by
  rw [bilanczosW_eq, bilanczosV_eq]
  exact BiLanczos.inner_vec_dualVec h.toBiLanczos hi hj

private theorem range_fin_eq_image_Iio {α : Type*} (f : ℕ → α) (k : ℕ) :
    Set.range (fun i : Fin k => f (i : ℕ)) = f '' Set.Iio k := by
  ext z
  simp only [Set.mem_range, Set.mem_image, Set.mem_Iio]
  exact ⟨fun ⟨i, hi⟩ => ⟨(i : ℕ), i.2, hi⟩, fun ⟨i, hi, hz⟩ => ⟨⟨i, hi⟩, hz⟩⟩

/-- **Proposition 7.1**, the spans: `{v_1, …, v_m}` spans `𝒦_m(A, v_1)` and `{w_1, …, w_m}` spans
`𝒦_m(Aᴴ, w_1)`. With `problem_7_2` these are bases, which is the full-rank hypothesis
Theorem 7.4 therefore does not have to assume. -/
theorem proposition_7_1_span (h : NoBreakdown A v₁ w₁ m) :
    Submodule.span 𝕜 (Set.range fun i : Fin m => bilanczosV A v₁ w₁ (i : ℕ))
        = Chapter06.krylov A v₁ m ∧
      Submodule.span 𝕜 (Set.range fun i : Fin m => bilanczosW A v₁ w₁ (i : ℕ))
        = Chapter06.krylov Aᴴ w₁ m := by
  constructor
  · rw [range_fin_eq_image_Iio, Chapter06.krylov_eq,
      show (bilanczosV A v₁ w₁) = BiLanczos.vec (op A) (op Aᴴ) v₁ w₁ from
        funext (bilanczosV_eq A v₁ w₁)]
    exact BiLanczos.span_vec h.toBiLanczos
  · rw [range_fin_eq_image_Iio, Chapter06.krylov_eq,
      show (bilanczosW A v₁ w₁) = BiLanczos.dualVec (op A) (op Aᴴ) v₁ w₁ from
        funext (bilanczosW_eq A v₁ w₁)]
    exact BiLanczos.span_dualVec h.toBiLanczos

/-- A family biorthogonal to another is linearly independent: Mathlib's
`LinearIndependent.of_pairwise_dual_eq_zero_one` at the dual functionals `⟪w_i, ·⟫`. -/
private theorem linearIndependent_of_biorthogonal {k : ℕ}
    (v w : Fin k → EuclideanSpace 𝕜 (Fin n))
    (h0 : ∀ i j, i ≠ j → inner 𝕜 (w i) (v j) = (0 : 𝕜))
    (h1 : ∀ i, inner 𝕜 (w i) (v i) = (1 : 𝕜)) :
    LinearIndependent 𝕜 v :=
  LinearIndependent.of_pairwise_dual_eq_zero_one v (fun i => (innerSL 𝕜 (w i)).toLinearMap)
    (fun i j hij => by simpa using h0 i j hij) fun i => by simpa using h1 i

/-- **P-7.2**: while Algorithm 7.1 has not broken down, the columns of `V_m` are linearly
independent, and so are those of `W_m` — immediate from biorthogonality. -/
theorem problem_7_2 (h : NoBreakdown A v₁ w₁ m) :
    LinearIndependent 𝕜 (fun i : Fin m => bilanczosV A v₁ w₁ (i : ℕ)) ∧
      LinearIndependent 𝕜 (fun i : Fin m => bilanczosW A v₁ w₁ (i : ℕ)) :=
  ⟨linearIndependent_of_biorthogonal _ _
      (fun i j hij => by
        rw [proposition_7_1 h (le_of_lt i.2) (le_of_lt j.2),
          ite_eq_right (fun hc => hij (Fin.ext hc))])
      fun i => by rw [proposition_7_1 h (le_of_lt i.2) (le_of_lt i.2), ite_eq_left rfl],
    linearIndependent_of_biorthogonal _ _
      (fun i j hij => by
        rw [proposition_7_1' h (le_of_lt i.2) (le_of_lt j.2),
          ite_eq_right (fun hc => hij (Fin.ext hc))])
      fun i => by rw [proposition_7_1' h (le_of_lt i.2) (le_of_lt i.2), ite_eq_left rfl]⟩

end Proposition

/-! ### (7.3)–(7.5) and (7.15): the matrix relations -/

section Relations

/-- Everything strictly above the subdiagonal of a column collapses to the single `β_j` term. -/
private theorem sum_bilanczosCoeff_lt (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ w₁ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    ∑ i ∈ Finset.range j, bilanczosCoeff A v₁ w₁ i j • bilanczosV A v₁ w₁ i
      = bilanczosBeta A v₁ w₁ j • bilanczosVPrev A v₁ w₁ j := by
  cases j with
  | zero => simp
  | succ k =>
    have hz : ∑ i ∈ Finset.range k, bilanczosCoeff A v₁ w₁ i (k + 1) • bilanczosV A v₁ w₁ i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have hik : i < k := Finset.mem_range.1 hi
        rw [bilanczosCoeff_eq_zero A v₁ w₁ (by omega) (by omega) (by omega), zero_smul]
    rw [Finset.sum_range_succ, hz, zero_add, bilanczosCoeff_self_succ, bilanczosVPrev_succ]

/-- The dual companion of `sum_bilanczosCoeff_lt`: everything strictly above the subdiagonal of a
row of `T_mᴴ` collapses to the single `δ̄_j` term. -/
private theorem sum_dualCoeff_lt (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ w₁ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    ∑ i ∈ Finset.range j, starRingEnd 𝕜 (bilanczosCoeff A v₁ w₁ j i) • bilanczosW A v₁ w₁ i
      = starRingEnd 𝕜 (bilanczosDelta A v₁ w₁ j) • bilanczosWPrev A v₁ w₁ j := by
  cases j with
  | zero => simp
  | succ k =>
    have hz : ∑ i ∈ Finset.range k,
        starRingEnd 𝕜 (bilanczosCoeff A v₁ w₁ (k + 1) i) • bilanczosW A v₁ w₁ i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have hik : i < k := Finset.mem_range.1 hi
        rw [bilanczosCoeff_eq_zero A v₁ w₁ (by omega) (by omega) (by omega), map_zero, zero_smul]
    rw [Finset.sum_range_succ, hz, zero_add, bilanczosCoeff_succ_self, bilanczosWPrev_succ]

variable {A : Matrix (Fin n) (Fin n) 𝕜} {v₁ w₁ : EuclideanSpace 𝕜 (Fin n)} {m : ℕ}

/-- (7.3) columnwise: `A v_j = ∑_{i ≤ j+1} T_{ij} v_i`. -/
private theorem apply_bilanczosV_sum (h : NoBreakdown A v₁ w₁ m) {j : ℕ} (hj : j < m) :
    op A (bilanczosV A v₁ w₁ j)
      = ∑ i ∈ Finset.range (j + 2), bilanczosCoeff A v₁ w₁ i j • bilanczosV A v₁ w₁ i := by
  rw [show j + 2 = j + 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
    sum_bilanczosCoeff_lt, bilanczosCoeff_self, bilanczosCoeff_succ_self]
  simp only [bilanczosV_eq, bilanczosVPrev_eq, bilanczosAlpha_eq, bilanczosBeta_eq,
    bilanczosDelta_eq]
  exact BiLanczos.apply_vec _ _ _ _ (h.toBiLanczos.delta_ne_zero j hj)

/-- (7.4) columnwise: `Aᴴ w_j = ∑_{i ≤ j+1} conj(T_{ji}) w_i`. -/
private theorem apply_bilanczosW_sum (h : NoBreakdown A v₁ w₁ m) {j : ℕ} (hj : j < m) :
    op Aᴴ (bilanczosW A v₁ w₁ j) = ∑ i ∈ Finset.range (j + 2),
      starRingEnd 𝕜 (bilanczosCoeff A v₁ w₁ j i) • bilanczosW A v₁ w₁ i := by
  rw [show j + 2 = j + 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
    sum_dualCoeff_lt, bilanczosCoeff_self, bilanczosCoeff_self_succ]
  simp only [bilanczosW_eq, bilanczosWPrev_eq, bilanczosAlpha_eq, bilanczosBeta_eq,
    bilanczosDelta_eq]
  exact BiLanczos.apply_dualVec _ _ _ _ (h.toBiLanczos.delta_ne_zero j hj)

/-- The two-sided Lanczos basis satisfies the backbone `Krylov.HessenbergRelation`, so the
residual formula of `Numlib/Krylov/Hessenberg.lean` and the quasi-minimal-residual layer built on
it apply verbatim, with a basis that is biorthogonal rather than orthonormal. This is the hinge
of §7.2 and §7.3. -/
theorem bilanczos_hessenbergRelation (h : NoSeriousBreakdown A v₁ w₁) :
    Krylov.HessenbergRelation (op A) (bilanczosV A v₁ w₁) (bilanczosCoeff A v₁ w₁) := by
  have hv : bilanczosV A v₁ w₁ = BiLanczos.vec (op A) (op Aᴴ) v₁ w₁ :=
    funext (bilanczosV_eq A v₁ w₁)
  have hc : bilanczosCoeff A v₁ w₁ = BiLanczos.coeff (op A) (op Aᴴ) v₁ w₁ :=
    funext fun i => funext fun j => bilanczosCoeff_eq A v₁ w₁ i j
  rw [hv, hc]
  exact BiLanczos.hessenbergRelation h.toBiLanczos

/-! #### Two matrix forms of a truncated Hessenberg recurrence -/

private theorem sum_coord {ι : Type*} (s : Finset ι) (f : ι → EuclideanSpace 𝕜 (Fin n))
    (i : Fin n) : (∑ k ∈ s, f k) i = ∑ k ∈ s, f k i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]

/-- `B U_m = U_{m+1} H̄_m` for a Hessenberg recurrence known only up to step `m`. -/
private theorem mul_colMatrix_eq_of_apply {B : Matrix (Fin n) (Fin n) 𝕜}
    {u : ℕ → EuclideanSpace 𝕜 (Fin n)} {c : ℕ → ℕ → 𝕜} {k : ℕ}
    (happ : ∀ j < k, op B (u j) = ∑ i ∈ Finset.range (j + 2), c i j • u i)
    (hz : ∀ i j, j + 1 < i → c i j = 0) :
    B * Chapter06.colMatrix u k = Chapter06.colMatrix u (k + 1) * Krylov.hessenbergOf c k := by
  ext i j
  have hj : (j : ℕ) < k := j.2
  have hrange : op B (u (j : ℕ)) = ∑ l ∈ Finset.range (k + 1), c l (j : ℕ) • u l := by
    rw [happ (j : ℕ) hj]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun l _ hl => ?_
    rw [Finset.mem_range, not_lt] at hl
    rw [hz l (j : ℕ) (by omega), zero_smul]
  rw [Chapter06.mul_colMatrix_apply, hrange, sum_coord, Matrix.mul_apply,
    ← Fin.sum_univ_eq_sum_range (fun l => (c l (j : ℕ) • u l) i) (k + 1)]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- `B U_{m+1} = U_{m+1} H_{m+1} + c_{m+2,m+1} u_{m+2} e_{m+1}ᵀ`, the truncated form. -/
private theorem mul_colMatrix_eq_add_vecMulVec {B : Matrix (Fin n) (Fin n) 𝕜}
    {u : ℕ → EuclideanSpace 𝕜 (Fin n)} {c : ℕ → ℕ → 𝕜} {k : ℕ}
    (happ : ∀ j < k + 1, op B (u j) = ∑ i ∈ Finset.range (j + 2), c i j • u i)
    (hz : ∀ i j, j + 1 < i → c i j = 0) :
    B * Chapter06.colMatrix u (k + 1) =
      Chapter06.colMatrix u (k + 1) * Krylov.hessenbergSqOf c (k + 1)
      + Matrix.vecMulVec (WithLp.ofLp (c (k + 1) k • u (k + 1)))
          (Pi.single (M := fun _ : Fin (k + 1) => 𝕜) (Fin.last k) 1) := by
  have hlast : ∀ j : Fin (k + 1), c (k + 1) (j : ℕ) • u (k + 1)
      = (Pi.single (M := fun _ : Fin (k + 1) => 𝕜) (Fin.last k) 1 j)
        • (c (k + 1) k • u (k + 1)) := by
    intro j
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 j.2) with hj | hj
    · have hjl : j = Fin.last k := Fin.ext (by simpa using hj)
      rw [hjl, Fin.val_last, Pi.single_eq_same, one_smul]
    · have hne : (j : ℕ) ≠ k := by omega
      rw [hz (k + 1) (j : ℕ) (by omega), zero_smul]
      simp [Fin.ext_iff, hne]
  ext i j
  have hj : (j : ℕ) < k + 1 := j.2
  have hrange : op B (u (j : ℕ)) = ∑ l ∈ Finset.range (k + 2), c l (j : ℕ) • u l := by
    rw [happ (j : ℕ) hj]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun l _ hl => ?_
    rw [Finset.mem_range, not_lt] at hl
    rw [hz l (j : ℕ) (by omega), zero_smul]
  rw [Chapter06.mul_colMatrix_apply, hrange, Finset.sum_range_succ, hlast j, PiLp.add_apply,
    sum_coord, Matrix.add_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    ← Fin.sum_univ_eq_sum_range (fun l => (c l (j : ℕ) • u l) i) (k + 1)]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun l _ => mul_comm _ _) ?_
  rw [PiLp.smul_apply, smul_eq_mul, mul_comm]

/-! #### (7.3), (7.4) and (7.15) -/

private theorem dualCoeff_eq_zero_of_lt (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ w₁ : EuclideanSpace 𝕜 (Fin n)) {i j : ℕ} (hij : j + 1 < i) :
    starRingEnd 𝕜 (bilanczosCoeff A v₁ w₁ j i) = 0 := by
  rw [bilanczosCoeff_eq_zero A v₁ w₁ (by omega) (by omega) (by omega), map_zero]

private theorem hessenbergSqOf_dual (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ w₁ : EuclideanSpace 𝕜 (Fin n)) (k : ℕ) :
    Krylov.hessenbergSqOf (fun i j => starRingEnd 𝕜 (bilanczosCoeff A v₁ w₁ j i)) k
      = (T A v₁ w₁ k)ᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply, T_apply]
  rfl

/-- **Saad (7.3)**, **(7.4)** and **(7.15)**: the matrix forms of the two three-term recurrences,
`A V_m = V_m T_m + δ_{m+1} v_{m+1} e_mᵀ` and `Aᴴ W_m = W_m T_mᴴ + β̄_{m+1} w_{m+1} e_mᵀ`, and the
extended form `A V_m = V_{m+1} T̄_m` that Chapter 7 runs QMR on. -/
theorem equation_7_3 (h : NoBreakdown A v₁ w₁ (m + 1)) :
    A * V A v₁ w₁ (m + 1) = V A v₁ w₁ (m + 1) * T A v₁ w₁ (m + 1)
        + Matrix.vecMulVec
            (WithLp.ofLp (bilanczosDelta A v₁ w₁ (m + 1) • bilanczosV A v₁ w₁ (m + 1)))
            (Pi.single (M := fun _ : Fin (m + 1) => 𝕜) (Fin.last m) 1) ∧
      Aᴴ * W A v₁ w₁ (m + 1) = W A v₁ w₁ (m + 1) * (T A v₁ w₁ (m + 1))ᴴ
        + Matrix.vecMulVec
            (WithLp.ofLp (starRingEnd 𝕜 (bilanczosBeta A v₁ w₁ (m + 1))
              • bilanczosW A v₁ w₁ (m + 1)))
            (Pi.single (M := fun _ : Fin (m + 1) => 𝕜) (Fin.last m) 1) ∧
      A * V A v₁ w₁ m = V A v₁ w₁ (m + 1) * Tbar A v₁ w₁ m := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← bilanczosCoeff_succ_self A v₁ w₁ m]
    exact mul_colMatrix_eq_add_vecMulVec (fun j hj => apply_bilanczosV_sum h hj)
      (fun i j hij => bilanczosCoeff_eq_zero_of_lt A v₁ w₁ hij)
  · rw [← hessenbergSqOf_dual A v₁ w₁ (m + 1),
      ← bilanczosCoeff_self_succ A v₁ w₁ m]
    exact mul_colMatrix_eq_add_vecMulVec (fun j hj => apply_bilanczosW_sum h hj)
      (fun i j hij => dualCoeff_eq_zero_of_lt A v₁ w₁ hij)
  · exact mul_colMatrix_eq_of_apply (fun j hj => apply_bilanczosV_sum h (by omega))
      (fun i j hij => bilanczosCoeff_eq_zero_of_lt A v₁ w₁ hij)

private theorem mul_V_apply (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ w₁ : EuclideanSpace 𝕜 (Fin n))
    {k : ℕ} (i : Fin n) (j : Fin k) :
    (A * V A v₁ w₁ k) i j = op A (bilanczosV A v₁ w₁ (j : ℕ)) i :=
  Chapter06.mul_colMatrix_apply A _ i j

/-- **Saad (7.5)**: `W_mᴴ A V_m = T_m`, so `T_m` is the compression of `A` to `𝒦_m(A, v_1)`
along `𝒦_m(Aᴴ, w_1)`; conjugate-transposing, `V_mᴴ Aᴴ W_m = T_mᴴ` compresses `Aᴴ` the other
way. -/
theorem equation_7_5 (h : NoBreakdown A v₁ w₁ m) :
    (W A v₁ w₁ m)ᴴ * A * V A v₁ w₁ m = T A v₁ w₁ m ∧
      (V A v₁ w₁ m)ᴴ * Aᴴ * W A v₁ w₁ m = (T A v₁ w₁ m)ᴴ := by
  have hmain : (W A v₁ w₁ m)ᴴ * A * V A v₁ w₁ m = T A v₁ w₁ m := by
    cases m with
    | zero => ext i j; exact i.elim0
    | succ M =>
      have hcoeff : ∀ i j : Fin (M + 1),
          inner 𝕜 (bilanczosW A v₁ w₁ (i : ℕ)) (op A (bilanczosV A v₁ w₁ (j : ℕ)))
            = bilanczosCoeff A v₁ w₁ i j := by
        intro i j
        rw [bilanczosW_eq, bilanczosV_eq, bilanczosCoeff_eq]
        exact BiLanczos.inner_dualVec_apply_vec h.toBiLanczos (by omega) (by omega)
      ext i j
      rw [Matrix.mul_assoc, Matrix.mul_apply, T_apply, ← hcoeff i j, PiLp.inner_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.conjTranspose_apply, W_apply, mul_V_apply, RCLike.inner_apply, mul_comm]
      rfl
  refine ⟨hmain, ?_⟩
  have hT := congrArg Matrix.conjTranspose hmain
  rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    ← Matrix.mul_assoc] at hT

end Relations

/-! ### P-7.6: the oblique projector `V_m W_mᴴ` -/

section Projector

variable {A : Matrix (Fin n) (Fin n) 𝕜} {v₁ w₁ : EuclideanSpace 𝕜 (Fin n)} {m : ℕ}

/-- The cross Gram matrix `W_mᴴ V_m` of the two Lanczos bases is the identity: Proposition 7.1
read as a matrix identity. -/
theorem crossGram_eq_one (h : NoBreakdown A v₁ w₁ m) :
    LinearMap.crossGram 𝕜 (fun i : Fin m => bilanczosV A v₁ w₁ (i : ℕ))
        (fun i : Fin m => bilanczosW A v₁ w₁ (i : ℕ)) = 1 := by
  ext i j
  rw [LinearMap.crossGram, Matrix.of_apply, proposition_7_1 h (le_of_lt i.2) (le_of_lt j.2)]
  simp [Matrix.one_apply, Fin.val_inj]

private theorem toEuclideanLin_conjTranspose_W_apply (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ w₁ : EuclideanSpace 𝕜 (Fin n)) (k : ℕ) (x : EuclideanSpace 𝕜 (Fin n)) :
    Matrix.toEuclideanLin (W A v₁ w₁ k)ᴴ x
      = WithLp.toLp 2 (fun j : Fin k => inner 𝕜 (bilanczosW A v₁ w₁ (j : ℕ)) x) := by
  refine WithLp.ofLp_injective 2 (funext fun j => ?_)
  change ((W A v₁ w₁ k)ᴴ *ᵥ WithLp.ofLp x) j = inner 𝕜 (bilanczosW A v₁ w₁ (j : ℕ)) x
  rw [Matrix.mulVec_apply_eq_sum, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.conjTranspose_apply, W_apply, RCLike.inner_apply, mul_comm]
  rfl

/-- `V_m W_mᴴ x = ∑_j (x, w_j) v_j`, the coordinate form of the projector. -/
private theorem toEuclideanLin_V_mul_conjTranspose_W (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ w₁ : EuclideanSpace 𝕜 (Fin n)) (k : ℕ) (x : EuclideanSpace 𝕜 (Fin n)) :
    Matrix.toEuclideanLin (V A v₁ w₁ k * (W A v₁ w₁ k)ᴴ) x
      = ∑ j : Fin k, inner 𝕜 (bilanczosW A v₁ w₁ (j : ℕ)) x • bilanczosV A v₁ w₁ (j : ℕ) := by
  rw [show Matrix.toEuclideanLin (V A v₁ w₁ k * (W A v₁ w₁ k)ᴴ)
      = Matrix.toEuclideanLin (V A v₁ w₁ k) ∘ₗ Matrix.toEuclideanLin (W A v₁ w₁ k)ᴴ from
    Matrix.toLpLin_mul 2 2 2 _ _]
  rw [LinearMap.comp_apply, toEuclideanLin_conjTranspose_W_apply]
  exact Chapter06.toEuclideanLin_colMatrix_apply _ _

/-- **P-7.6(a)**: the oblique projector onto `𝒦_m(A, v_1)` orthogonally to `𝒦_m(Aᴴ, w_1)` is
`V_m W_mᴴ`; the general formula `V (Wᴴ V)⁻¹ Wᴴ` collapses because `W_mᴴ V_m = I` by
Proposition 7.1. -/
theorem problem_7_6 (h : NoBreakdown A v₁ w₁ m) :
    Matrix.toEuclideanLin (V A v₁ w₁ m * (W A v₁ w₁ m)ᴴ)
        = LinearMap.obliqueProjectionOfBases 𝕜 (fun i : Fin m => bilanczosV A v₁ w₁ (i : ℕ))
            (fun i : Fin m => bilanczosW A v₁ w₁ (i : ℕ)) ∧
      IsIdempotentElem (Matrix.toEuclideanLin (V A v₁ w₁ m * (W A v₁ w₁ m)ᴴ)) ∧
      LinearMap.range (Matrix.toEuclideanLin (V A v₁ w₁ m * (W A v₁ w₁ m)ᴴ))
          = Chapter06.krylov A v₁ m ∧
      LinearMap.ker (Matrix.toEuclideanLin (V A v₁ w₁ m * (W A v₁ w₁ m)ᴴ))
          = (Chapter06.krylov Aᴴ w₁ m)ᗮ := by
  have hG := crossGram_eq_one h
  have hU : IsUnit (LinearMap.crossGram 𝕜 (fun i : Fin m => bilanczosV A v₁ w₁ (i : ℕ))
      (fun i : Fin m => bilanczosW A v₁ w₁ (i : ℕ))) := hG ▸ isUnit_one
  have hobl : ∀ x : EuclideanSpace 𝕜 (Fin n),
      LinearMap.obliqueProjectionOfBases 𝕜 (fun i : Fin m => bilanczosV A v₁ w₁ (i : ℕ))
          (fun i : Fin m => bilanczosW A v₁ w₁ (i : ℕ)) x
        = ∑ j : Fin m, inner 𝕜 (bilanczosW A v₁ w₁ (j : ℕ)) x • bilanczosV A v₁ w₁ (j : ℕ) := by
    intro x
    have hdef : LinearMap.obliqueProjectionOfBases 𝕜 (fun i : Fin m => bilanczosV A v₁ w₁ (i : ℕ))
          (fun i : Fin m => bilanczosW A v₁ w₁ (i : ℕ)) x
        = ∑ j, (LinearMap.crossGram 𝕜 (fun i : Fin m => bilanczosV A v₁ w₁ (i : ℕ))
            (fun i : Fin m => bilanczosW A v₁ w₁ (i : ℕ)))⁻¹.mulVec
            (fun i => inner 𝕜 (bilanczosW A v₁ w₁ (i : ℕ)) x) j • bilanczosV A v₁ w₁ (j : ℕ) :=
      rfl
    rw [hdef, hG, _root_.inv_one, Matrix.one_mulVec]
  have hP : Matrix.toEuclideanLin (V A v₁ w₁ m * (W A v₁ w₁ m)ᴴ)
      = LinearMap.obliqueProjectionOfBases 𝕜 (fun i : Fin m => bilanczosV A v₁ w₁ (i : ℕ))
          (fun i : Fin m => bilanczosW A v₁ w₁ (i : ℕ)) :=
    LinearMap.ext fun x => by rw [toEuclideanLin_V_mul_conjTranspose_W, hobl]
  obtain ⟨hspanV, hspanW⟩ := proposition_7_1_span h
  refine ⟨hP, ?_, ?_, ?_⟩
  · rw [hP]
    exact LinearMap.obliqueProjectionOfBases_isIdempotentElem _ _ hU
  · rw [hP, LinearMap.range_obliqueProjectionOfBases _ _ hU, ← hspanV]
  · rw [hP, LinearMap.ker_obliqueProjectionOfBases _ _ hU, ← hspanW]

/-- **P-7.6(b)**: a projector onto `K` along `Lᗮ` exists exactly when `K ⊓ Lᗮ = ⊥`, and the two
Lanczos subspaces satisfy that condition as long as Algorithm 7.1 has not broken down. -/
theorem problem_7_6_inf_eq_bot (h : NoBreakdown A v₁ w₁ m) :
    Chapter06.krylov A v₁ m ⊓ (Chapter06.krylov Aᴴ w₁ m)ᗮ = ⊥ := by
  obtain ⟨-, hidem, hran, hker⟩ := problem_7_6 h
  refine Submodule.eq_bot_iff _ |>.2 fun x hx => ?_
  obtain ⟨z, hz⟩ : x ∈ LinearMap.range (Matrix.toEuclideanLin (V A v₁ w₁ m * (W A v₁ w₁ m)ᴴ)) := by
    rw [hran]; exact hx.1
  have hfix : Matrix.toEuclideanLin (V A v₁ w₁ m * (W A v₁ w₁ m)ᴴ) x = x := by
    rw [← hz]
    exact DFunLike.congr_fun hidem z
  have hzero : Matrix.toEuclideanLin (V A v₁ w₁ m * (W A v₁ w₁ m)ᴴ) x = 0 := by
    rw [← LinearMap.mem_ker, hker]; exact hx.2
  rw [← hfix, hzero]

end Projector

end SaadSparse.Chapter07
