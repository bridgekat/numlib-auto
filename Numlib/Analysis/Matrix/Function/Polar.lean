import Numlib.Analysis.Matrix.Function.CFC
import Numlib.LinearAlgebra.Matrix.Polar

/-!
# The polar decomposition as a function of matrices

The polar decomposition `A = U P` itself — the specification `Matrix.IsPolarDecomposition`, its
existence and the symmetric factor `P = (Aᴴ A)^{1/2}` — is the decomposition module
`Numlib/LinearAlgebra/Matrix/Polar`. Here are the facts about it that belong to the functions of
matrices of [golub2013matrix] §9.4.3:

* `Matrix.IsPolarDecomposition.eq_pfc_sqrt`: `P` is the primary square root of `Aᴴ A`;
* `Matrix.newtonPolarIterate`: Newton's iteration `X_{k+1} = (X_k + X_k⁻ᴴ)/2`
  ([golub2013matrix] (9.4.11)); `Matrix.newtonPolarIterate_eq`: `X_k = U P_k` with `P_k` the
  same iteration started at `P` ((9.4.12)), and `Matrix.tendsto_newtonPolarIterate`:
  `X_k → U`, with `‖X_k − U‖₂ = ‖P_k − 1‖₂` (`Matrix.l2_opNorm_newtonPolarIterate_sub`) and the
  quadratic step `P_{k+1} − 1 = ½ P_k⁻¹ (P_k − 1)²`
  (`Matrix.newtonPolarIterate_succ_sub_one`).

Every statement about "the polar factor `U`" takes an `IsPolarDecomposition A U P` hypothesis.

## Implementation notes

The convergence proof diagonalizes `P = V diag(σ) Vᴴ` (`Matrix.IsHermitian.spectral_theorem`):
then `P_k = V diag(r_k(σ_i)) Vᴴ` with the scalar Newton map `r ↦ (r + 1/r)/2`, which converges to
`1` from every `r > 0` — so no complex sign-function machinery is needed and the statements hold
over every `RCLike` field.

## References

* [golub2013matrix] §9.4.3.
-/

open Filter Topology
open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

section Sqrt

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

open scoped MatrixOrder in
/-- **The symmetric polar factor is the primary square root of `Aᴴ A`** ([golub2013matrix] §9.4.3,
"`P = (AᵀA)^{1/2}`" read in chapter 9's functional calculus): `P = pfc √· (Aᴴ A)`
(`Matrix.IsPolarDecomposition.eq_cfcSqrt`, `Matrix.PosSemidef.cfcSqrt_eq_pfc`). -/
theorem IsPolarDecomposition.eq_pfc_sqrt {A U : Matrix m n 𝕜} {P : Matrix n n 𝕜}
    (h : IsPolarDecomposition A U P) :
    P = pfc (fun z : 𝕜 => ((Real.sqrt (RCLike.re z) : ℝ) : 𝕜)) (Aᴴ * A) := by
  rw [h.eq_cfcSqrt, (posSemidef_conjTranspose_mul_self A).cfcSqrt_eq_pfc]

end Sqrt

section Newton

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Newton's polar iteration** ([golub2013matrix] (9.4.11), whose body the conversion lost;
reconstructed from (9.4.12)): `X₀ = A`, `X_{k+1} = (X_k + (X_k⁻¹)ᴴ)/2`. -/
noncomputable def newtonPolarIterate (A : Matrix n n 𝕜) : ℕ → Matrix n n 𝕜
  | 0 => A
  | k + 1 => (2 : 𝕜)⁻¹ • (newtonPolarIterate A k + (newtonPolarIterate A k)⁻¹ᴴ)

@[simp]
theorem newtonPolarIterate_zero (A : Matrix n n 𝕜) : newtonPolarIterate A 0 = A := rfl

theorem newtonPolarIterate_succ (A : Matrix n n 𝕜) (k : ℕ) :
    newtonPolarIterate A (k + 1)
      = (2 : 𝕜)⁻¹ • (newtonPolarIterate A k + (newtonPolarIterate A k)⁻¹ᴴ) := rfl

/-- The scalar Newton map `r ↦ (r + 1/r)/2`, iterated from `s`. -/
private noncomputable def newtonScalar (s : ℝ) : ℕ → ℝ
  | 0 => s
  | k + 1 => 2⁻¹ * (newtonScalar s k + (newtonScalar s k)⁻¹)

private theorem newtonScalar_pos {s : ℝ} (hs : 0 < s) (k : ℕ) : 0 < newtonScalar s k := by
  induction k with
  | zero => exact hs
  | succ k ih =>
    change 0 < 2⁻¹ * (newtonScalar s k + (newtonScalar s k)⁻¹)
    positivity

/-- From the first step on, the scalar Newton iterates lie in `[1, ∞)` and halve their distance to
`1` at each step: `r − 1 ≥ 0` and `(r + 1/r)/2 − 1 = (r − 1)²/(2r) ≤ (r − 1)/2`. -/
private theorem newtonScalar_succ_bounds {s : ℝ} (hs : 0 < s) (k : ℕ) :
    1 ≤ newtonScalar s (k + 1) ∧
      newtonScalar s (k + 1) - 1 ≤ (newtonScalar s 1 - 1) / 2 ^ k := by
  induction k with
  | zero =>
    refine ⟨?_, by simp⟩
    change 1 ≤ 2⁻¹ * (s + s⁻¹)
    have : 2 ≤ s + s⁻¹ := by
      have h1 : s + s⁻¹ - 2 = (s - 1) ^ 2 / s := by field_simp; ring
      nlinarith [div_nonneg (sq_nonneg (s - 1)) hs.le]
    linarith
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    set r := newtonScalar s (k + 1) with hr
    have hr0 : 0 < r := lt_of_lt_of_le one_pos h1
    have heq : newtonScalar s (k + 1 + 1) - 1 = (r - 1) ^ 2 / (2 * r) := by
      change 2⁻¹ * (r + r⁻¹) - 1 = _
      field_simp
      ring
    have hle : (r - 1) ^ 2 / (2 * r) ≤ (r - 1) / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    refine ⟨by nlinarith [div_nonneg (sq_nonneg (r - 1)) (by positivity : (0 : ℝ) ≤ 2 * r)], ?_⟩
    calc newtonScalar s (k + 1 + 1) - 1 = (r - 1) ^ 2 / (2 * r) := heq
      _ ≤ (r - 1) / 2 := hle
      _ ≤ (newtonScalar s 1 - 1) / 2 ^ k / 2 := div_le_div_of_nonneg_right h2 (by norm_num)
      _ = (newtonScalar s 1 - 1) / 2 ^ (k + 1) := by rw [pow_succ, div_div]

/-- The scalar Newton iteration converges to `1` from every `s > 0`. -/
private theorem tendsto_newtonScalar {s : ℝ} (hs : 0 < s) :
    Tendsto (newtonScalar s) atTop (𝓝 1) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have hup : Tendsto (fun k : ℕ => 1 + (newtonScalar s 1 - 1) / 2 ^ k) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := newtonScalar s 1 - 1)).div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
    simpa using this.const_add 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => ?_)
    fun k => ?_
  · exact (newtonScalar_succ_bounds hs k).1
  · have := (newtonScalar_succ_bounds hs k).2
    simp only
    linarith

/-- The inverse of a unitary conjugate of an invertible real diagonal matrix. -/
private theorem inv_conj_diagonal {V : Matrix n n 𝕜} (hV : V ∈ unitaryGroup n 𝕜) {d : n → ℝ}
    (hd : ∀ i, d i ≠ 0) :
    (V * diagonal (fun i => ((d i : ℝ) : 𝕜)) * Vᴴ)⁻¹
      = V * diagonal (fun i => (((d i)⁻¹ : ℝ) : 𝕜)) * Vᴴ := by
  have hVV : Vᴴ * V = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 hV
  refine inv_eq_left_inv ?_
  calc V * diagonal (fun i => (((d i)⁻¹ : ℝ) : 𝕜)) * Vᴴ *
        (V * diagonal (fun i => ((d i : ℝ) : 𝕜)) * Vᴴ)
      = V * (diagonal (fun i => (((d i)⁻¹ : ℝ) : 𝕜)) * (Vᴴ * V) *
          diagonal (fun i => ((d i : ℝ) : 𝕜))) * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = V * Vᴴ := by
        rw [hVV, Matrix.mul_one, diagonal_mul_diagonal,
          show (fun i => (((d i)⁻¹ : ℝ) : 𝕜) * ((d i : ℝ) : 𝕜)) = fun _ => 1 from
            funext fun i => by rw [← RCLike.ofReal_mul, inv_mul_cancel₀ (hd i),
              RCLike.ofReal_one], diagonal_one, Matrix.mul_one]
    _ = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.1 hV

/-- **Newton's polar iteration on a positive definite matrix, diagonalized**: if
`P = V diag(s) Vᴴ` with `V` unitary and `s > 0`, then `P_k = V diag(r_k(s_i)) Vᴴ` with the scalar
Newton iterates `r_k`. -/
private theorem newtonPolarIterate_conj_diagonal {V : Matrix n n 𝕜} (hV : V ∈ unitaryGroup n 𝕜)
    {s : n → ℝ} (hs : ∀ i, 0 < s i) (k : ℕ) :
    newtonPolarIterate (V * diagonal (fun i => ((s i : ℝ) : 𝕜)) * Vᴴ) k
      = V * diagonal (fun i => ((newtonScalar (s i) k : ℝ) : 𝕜)) * Vᴴ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hH : (V * diagonal (fun i => (((newtonScalar (s i) k)⁻¹ : ℝ) : 𝕜)) * Vᴴ)ᴴ
        = V * diagonal (fun i => (((newtonScalar (s i) k)⁻¹ : ℝ) : 𝕜)) * Vᴴ := by
      have hstar : star (fun i => (((newtonScalar (s i) k)⁻¹ : ℝ) : 𝕜))
          = fun i => (((newtonScalar (s i) k)⁻¹ : ℝ) : 𝕜) := funext fun i => by simp
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
        diagonal_conjTranspose, hstar, Matrix.mul_assoc]
    rw [newtonPolarIterate_succ, ih,
      inv_conj_diagonal hV fun i => (newtonScalar_pos (hs i) k).ne', hH, ← Matrix.add_mul,
      ← Matrix.mul_add, diagonal_add, ← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
    congr 3
    funext i
    rw [Pi.smul_apply, smul_eq_mul]
    change _ = ((2⁻¹ * (newtonScalar (s i) k + (newtonScalar (s i) k)⁻¹) : ℝ) : 𝕜)
    push_cast
    ring

/-- A positive definite matrix in its spectral form `V diag(σ) Vᴴ`. -/
private theorem PosDef.eq_conj_diagonal {P : Matrix n n 𝕜} (hP : P.PosDef) :
    P = (hP.isHermitian.eigenvectorUnitary : Matrix n n 𝕜)
      * diagonal (fun i => ((hP.isHermitian.eigenvalues i : ℝ) : 𝕜))
      * (hP.isHermitian.eigenvectorUnitary : Matrix n n 𝕜)ᴴ := by
  conv_lhs => rw [hP.isHermitian.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  rfl

/-- The Newton polar iterates of a positive definite matrix are positive definite. -/
theorem PosDef.newtonPolarIterate {P : Matrix n n 𝕜} (hP : P.PosDef) (k : ℕ) :
    (newtonPolarIterate P k).PosDef := by
  have hV := hP.isHermitian.eigenvectorUnitary.2
  rw [hP.eq_conj_diagonal, newtonPolarIterate_conj_diagonal hV hP.eigenvalues_pos]
  have hD : (diagonal fun i => ((newtonScalar (hP.isHermitian.eigenvalues i) k : ℝ) : 𝕜)).PosDef :=
    posDef_diagonal_iff.2 fun i => RCLike.ofReal_pos.2 (newtonScalar_pos (hP.eigenvalues_pos i) k)
  have hinj : Function.Injective
      ((hP.isHermitian.eigenvectorUnitary : Matrix n n 𝕜)ᴴ).mulVec := by
    refine mulVec_injective_iff_isUnit.2 ?_
    rw [← star_eq_conjTranspose]
    exact isUnit_of_mem_unitaryGroup (Unitary.star_mem hV)
  simpa using hD.conjTranspose_mul_mul_same hinj

variable {A U P : Matrix n n 𝕜}

/-- **Newton's polar iterates in polar form** ([golub2013matrix] (9.4.12)): for a nonsingular `A`
with polar decomposition `A = U P`, `X_k = U P_k`, where `P_k` is the same iteration started at
`P` — `P_{k+1} = (P_k + P_k⁻¹)/2`, the Newton sign iteration of `P` — and every `P_k` is positive
definite, so every `X_k` is nonsingular. Induction: `(U P_k)⁻ᴴ = U P_k⁻ᴴ`, `U` being unitary. -/
theorem newtonPolarIterate_eq (hA : IsUnit A) (h : IsPolarDecomposition A U P) (k : ℕ) :
    newtonPolarIterate A k = U * newtonPolarIterate P k ∧ (newtonPolarIterate P k).PosDef := by
  have hP : P.PosDef := h.posSemidef.posDef_iff_isUnit.2 (h.isUnit hA)
  have hUi : U⁻¹ = Uᴴ := inv_eq_left_inv h.conjTranspose_mul_self
  refine ⟨?_, hP.newtonPolarIterate k⟩
  induction k with
  | zero => exact h.eq_mul
  | succ k ih =>
    rw [newtonPolarIterate_succ, newtonPolarIterate_succ, ih, mul_inv_rev, hUi, conjTranspose_mul,
      conjTranspose_conjTranspose, ← Matrix.mul_add, Matrix.mul_smul]

open scoped Matrix.Norms.L2Operator in
/-- **The error of Newton's polar iteration** ([golub2013matrix] §9.4.3):
`‖X_k − U‖₂ = ‖U (P_k − I)‖₂ = ‖P_k − I‖₂`. -/
theorem l2_opNorm_newtonPolarIterate_sub (hA : IsUnit A) (h : IsPolarDecomposition A U P)
    (k : ℕ) :
    ‖newtonPolarIterate A k - U‖ = ‖newtonPolarIterate P k - 1‖ := by
  rw [(newtonPolarIterate_eq hA h k).1, ← Matrix.mul_one U, Matrix.mul_assoc, ← Matrix.mul_sub,
    Matrix.one_mul]
  exact l2_opNorm_mul_of_conjTranspose_mul_self_eq_one h.conjTranspose_mul_self _

/-- **The quadratic step of Newton's polar iteration**: for a positive definite `P`,
`P_{k+1} − I = ½ P_k⁻¹ (P_k − I)²`. -/
theorem newtonPolarIterate_succ_sub_one {P : Matrix n n 𝕜} (hP : P.PosDef) (k : ℕ) :
    newtonPolarIterate P (k + 1) - 1
      = (2 : 𝕜)⁻¹ • ((newtonPolarIterate P k)⁻¹ *
          ((newtonPolarIterate P k - 1) * (newtonPolarIterate P k - 1))) := by
  have hk := hP.newtonPolarIterate k
  have hdet : IsUnit (newtonPolarIterate P k).det :=
    (isUnit_iff_isUnit_det _).1 hk.isUnit
  rw [newtonPolarIterate_succ, hk.inv.isHermitian.eq]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, ← Matrix.mul_assoc,
    nonsing_inv_mul _ hdet]
  module

open scoped Matrix.Norms.L2Operator in
/-- **Quadratic convergence of Newton's polar iteration**, the step bound
([golub2013matrix] §9.4.3): `‖P_{k+1} − I‖₂ ≤ ½ ‖P_k⁻¹‖₂ ‖P_k − I‖₂²`. -/
theorem l2_opNorm_newtonPolarIterate_succ_sub_one_le {P : Matrix n n 𝕜} (hP : P.PosDef)
    (k : ℕ) :
    ‖newtonPolarIterate P (k + 1) - 1‖
      ≤ ‖(newtonPolarIterate P k)⁻¹‖ * ‖newtonPolarIterate P k - 1‖ ^ 2 / 2 := by
  rw [newtonPolarIterate_succ_sub_one hP k, norm_smul, norm_inv, RCLike.norm_ofNat]
  have h1 := l2_opNorm_mul (newtonPolarIterate P k)⁻¹
    ((newtonPolarIterate P k - 1) * (newtonPolarIterate P k - 1))
  have h2 := l2_opNorm_mul (newtonPolarIterate P k - 1) (newtonPolarIterate P k - 1)
  have h3 : ‖(newtonPolarIterate P k)⁻¹‖ * ‖(newtonPolarIterate P k - 1) *
      (newtonPolarIterate P k - 1)‖ ≤ ‖(newtonPolarIterate P k)⁻¹‖ *
        (‖newtonPolarIterate P k - 1‖ * ‖newtonPolarIterate P k - 1‖) :=
    mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  rw [sq]
  linarith

/-- **Newton's polar iteration converges to the orthonormal polar factor** ([golub2013matrix]
§9.4.3, quadratically by `Matrix.l2_opNorm_newtonPolarIterate_succ_sub_one_le`): for a
nonsingular `A = U P`, `X_k → U`. In an eigenbasis of `P = V diag(σ) Vᴴ`,
`X_k = U V diag(r_k(σ_i)) Vᴴ` with the scalar Newton iterates `r_k(σ) → 1`. -/
theorem tendsto_newtonPolarIterate (hA : IsUnit A) (h : IsPolarDecomposition A U P) :
    Tendsto (newtonPolarIterate A) atTop (𝓝 U) := by
  have hP : P.PosDef := h.posSemidef.posDef_iff_isUnit.2 (h.isUnit hA)
  set V := (hP.isHermitian.eigenvectorUnitary : Matrix n n 𝕜) with hVdef
  have hV : V ∈ unitaryGroup n 𝕜 := hP.isHermitian.eigenvectorUnitary.2
  set s := hP.isHermitian.eigenvalues with hsdef
  have hs : ∀ i, 0 < s i := hP.eigenvalues_pos
  have hform : ∀ k, newtonPolarIterate A k
      = U * (V * diagonal (fun i => ((newtonScalar (s i) k : ℝ) : 𝕜)) * Vᴴ) := fun k => by
    rw [(newtonPolarIterate_eq hA h k).1, hP.eq_conj_diagonal,
      newtonPolarIterate_conj_diagonal hV hs]
  have hlim : Tendsto (fun k => fun i => ((newtonScalar (s i) k : ℝ) : 𝕜)) atTop
      (𝓝 fun _ => (1 : 𝕜)) := by
    rw [tendsto_pi_nhds]
    intro i
    have := ((RCLike.continuous_ofReal (K := 𝕜)).tendsto 1).comp (tendsto_newtonScalar (hs i))
    simpa [Function.comp_def] using this
  have hc : Continuous fun d : n → 𝕜 => U * (V * diagonal d * Vᴴ) :=
    continuous_const.matrix_mul
      ((continuous_const.matrix_mul continuous_id.matrix_diagonal).matrix_mul continuous_const)
  have hval : U * (V * diagonal (fun _ => (1 : 𝕜)) * Vᴴ) = U := by
    rw [diagonal_one, Matrix.mul_one, ← star_eq_conjTranspose, mem_unitaryGroup_iff.1 hV,
      Matrix.mul_one]
  have := (hc.tendsto _).comp hlim
  rw [hval] at this
  exact this.congr fun k => (hform k).symm

end Newton

end Matrix
