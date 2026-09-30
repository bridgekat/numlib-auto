import Numlib.Analysis.Matrix.Function.CFC
import Numlib.Analysis.Matrix.Function.Sign
import Numlib.Analysis.Matrix.SingularValues
import Numlib.LinearAlgebra.Matrix.OrthogonalGroup
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
  (`Matrix.newtonPolarIterate_succ_sub_one`);
* `Matrix.IsPolarDecomposition.frobenius_norm_sub_le_div_iInf_colSingularValues`: the complex form
  of the Li–Sun perturbation bound `‖U − Ũ‖_F ≤ 2 ‖A − Ã‖_F / (σ_min(A) + σ_min(Ã))`, from the
  Sylvester bound `Matrix.frobenius_norm_le_of_mul_add_mul_eq`;
* `Matrix.frobenius_norm_polar_sub_le`: the real Li–Sun bound
  `‖U − Ũ‖_F ≤ 4 ‖A − Ã‖_F / (σ_{n-1} + σ_n + σ̃_{n-1} + σ̃_n)` (the two smallest singular values
  of each) when `det A · det Ã > 0`, from the pairing inequality `Matrix.trace_mul_one_sub_ge`
  for a rotation `W`: `tr(P (1 - W)) ≥ (σ_{n-1} + σ_n)/2 · tr(1 - W)`;
* `Matrix.matrixSign_hermitianDilation`: the sign of the Jordan–Wielandt matrix `[0 A; Aᴴ 0]` of a
  nonsingular `A = U P` is `[0 U; Uᴴ 0]`.

Every statement about "the polar factor `U`" takes an `IsPolarDecomposition A U P` hypothesis.

## Implementation notes

The convergence proof diagonalizes `P = V diag(σ) Vᴴ` (`Matrix.IsHermitian.spectral_theorem`):
then `P_k = V diag(r_k(σ_i)) Vᴴ` with the scalar Newton map `r ↦ (r + 1/r)/2`, which converges to
`1` from every `r > 0` — so no complex sign-function machinery is needed and the statements hold
over every `RCLike` field.

The real Li–Sun bound is not proved as Li and Sun do. With `W = Uᵀ Ũ` a rotation (this is where
`det A · det Ã > 0` enters) and `X = 1 − W`, `P X + X P' = R` with `‖R‖_F ≤ 2 ‖A − Ã‖_F`, and
`X Xᵀ = Xᵀ X = X + Xᵀ` turns `tr(Xᵀ R)` into `2 tr(P X) + 2 tr(P' X)`. Each is bounded below by the
pairing inequality, which needs only two facts about orthogonal matrices: `tr(R O) ≤ tr R` for
`R ⪰ 0` (`Matrix.PosSemidef.trace_mul_le_trace`) and `tr O ≤ n − 2` when `det O = −1`
(`Matrix.trace_le_card_sub_two_of_det_eq_neg_one`), applied to `O = (1 − 2 u uᵀ) W`.

## References

* [golub2013matrix] §9.4.3.
* W. Li and W. Sun, *Perturbation bounds of unitary and subunitary polar factors*, SIAM J. Matrix
  Anal. Appl. 23 (2002) 1183–1193.
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

/-! ### Perturbation of the unitary polar factor -/

section Perturbation

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Frobenius

/-- **A Sylvester equation with coefficients bounded below** (the step behind the perturbation
bound of the polar factor, Li and Sun 2003): if `σ ≤ P` and `τ ≤ Q` in the Loewner order with
`σ + τ > 0`, the solution of `P X + X Q = R` satisfies `‖X‖_F ≤ ‖R‖_F / (σ + τ)`. Indeed
`(σ + τ) ‖X‖_F² ≤ re tr(Xᴴ P X) + re tr(X Q Xᴴ) = re tr(Xᴴ R) ≤ ‖X‖_F ‖R‖_F`. -/
theorem frobenius_norm_le_of_mul_add_mul_eq {P Q X R : Matrix n n 𝕜} {σ τ : ℝ}
    (hP : (P - (σ : 𝕜) • 1).PosSemidef) (hQ : (Q - (τ : 𝕜) • 1).PosSemidef)
    (hστ : 0 < σ + τ) (h : P * X + X * Q = R) : ‖X‖ ≤ ‖R‖ / (σ + τ) := by
  have hX2 := frobenius_norm_sq_eq_trace X
  have hXX : trace (X * Xᴴ) = trace (Xᴴ * X) := trace_mul_comm X Xᴴ
  have h1 : σ * ‖X‖ ^ 2 ≤ RCLike.re (trace (Xᴴ * P * X)) := by
    have h0 := RCLike.nonneg_iff.1 (hP.conjTranspose_mul_mul_same X).trace_nonneg
    rw [Matrix.mul_sub, Matrix.sub_mul, trace_sub, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, trace_smul, ← hX2, smul_eq_mul, map_sub, ← RCLike.ofReal_mul,
      RCLike.ofReal_re] at h0
    linarith [h0.1]
  have h2 : τ * ‖X‖ ^ 2 ≤ RCLike.re (trace (Xᴴ * X * Q)) := by
    have h0 := RCLike.nonneg_iff.1 (hQ.mul_mul_conjTranspose_same X).trace_nonneg
    rw [Matrix.mul_sub, Matrix.sub_mul, trace_sub, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, trace_smul, hXX, ← hX2, smul_eq_mul, map_sub, ← RCLike.ofReal_mul,
      RCLike.ofReal_re, trace_mul_comm (X * Q), ← Matrix.mul_assoc] at h0
    linarith [h0.1]
  have h3 : RCLike.re (trace (Xᴴ * R)) = RCLike.re (trace (Xᴴ * P * X))
      + RCLike.re (trace (Xᴴ * X * Q)) := by
    rw [← h, Matrix.mul_add, trace_add, map_add, Matrix.mul_assoc, Matrix.mul_assoc]
  have h4 := re_trace_conjTranspose_mul_le X R
  rw [le_div_iff₀ hστ]
  rcases (norm_nonneg X).eq_or_lt with hX | hX
  · rw [← hX, zero_mul]
    exact norm_nonneg R
  · refine le_of_mul_le_mul_right ?_ hX
    nlinarith

/-- The Sylvester equation of two polar decompositions (shared by the complex and the real bounds):
with `X = Uᴴ (U - Ũ)`, `P X + X P' = Uᴴ Δ - Δᴴ Ũ` for `Δ = A - Ã`, whose Frobenius norm is at most
`2 ‖Δ‖_F`; and `‖X‖_F = ‖U - Ũ‖_F`. -/
private theorem IsPolarDecomposition.sylvester {A Ã U Ũ P P' : Matrix n n 𝕜}
    (h : IsPolarDecomposition A U P) (h' : IsPolarDecomposition Ã Ũ P') :
    ‖Uᴴ * (U - Ũ)‖ = ‖U - Ũ‖ ∧
      P * (Uᴴ * (U - Ũ)) + Uᴴ * (U - Ũ) * P' = Uᴴ * (A - Ã) - (A - Ã)ᴴ * Ũ ∧
      ‖Uᴴ * (A - Ã) - (A - Ã)ᴴ * Ũ‖ ≤ 2 * ‖A - Ã‖ := by
  have hU' := h'.mem_unitaryGroup
  have hUs : Uᴴ ∈ unitaryGroup n 𝕜 := by
    rw [← star_eq_conjTranspose]; exact Unitary.star_mem h.mem_unitaryGroup
  have hUU : Uᴴ * U = 1 := h.conjTranspose_mul_self
  have hUU' : Ũᴴ * Ũ = 1 := h'.conjTranspose_mul_self
  have hPh : Pᴴ = P := h.isHermitian
  have hPh' : P'ᴴ = P' := h'.isHermitian
  refine ⟨?_, ?_, ?_⟩
  · have := frobenius_norm_unitary_mul_mul_unitary hUs (U - Ũ) (one_mem (unitaryGroup n 𝕜))
    rwa [Matrix.mul_one] at this
  · have e1 : Uᴴ * (A - Ã) = P - Uᴴ * Ũ * P' := by
      rw [Matrix.mul_sub, h.eq_mul, h'.eq_mul, ← Matrix.mul_assoc, hUU, Matrix.one_mul,
        Matrix.mul_assoc]
    have e2 : (A - Ã)ᴴ * Ũ = P * (Uᴴ * Ũ) - P' := by
      rw [conjTranspose_sub, Matrix.sub_mul, h.eq_mul, h'.eq_mul, conjTranspose_mul,
        conjTranspose_mul, hPh, hPh', Matrix.mul_assoc, Matrix.mul_assoc, hUU', Matrix.mul_one]
    rw [e1, e2]
    simp only [Matrix.mul_sub, Matrix.sub_mul, hUU, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc]
    abel
  · have h1 : ‖Uᴴ * (A - Ã)‖ = ‖A - Ã‖ := by
      have := frobenius_norm_unitary_mul_mul_unitary hUs (A - Ã) (one_mem (unitaryGroup n 𝕜))
      rwa [Matrix.mul_one] at this
    have h2 : ‖(A - Ã)ᴴ * Ũ‖ = ‖A - Ã‖ := by
      have := frobenius_norm_unitary_mul_mul_unitary (one_mem (unitaryGroup n 𝕜)) (A - Ã)ᴴ hU'
      rw [Matrix.one_mul] at this
      rw [this, frobenius_norm_conjTranspose]
    calc ‖Uᴴ * (A - Ã) - (A - Ã)ᴴ * Ũ‖ ≤ ‖Uᴴ * (A - Ã)‖ + ‖(A - Ã)ᴴ * Ũ‖ := norm_sub_le _ _
      _ = 2 * ‖A - Ã‖ := by rw [h1, h2]; ring

/-- **The perturbation of the unitary polar factor** (the complex form of the Li–Sun bound,
[golub2013matrix] §9.4.3; W. Li and W. Sun 2002): if `A = U P` and `Ã = Ũ P'` are polar
decompositions of square matrices with `σ ≤ P`, `σ̃ ≤ P'` in the Loewner order and `σ + σ̃ > 0`
(for instance `σ`, `σ̃` the smallest singular values), then
`‖U − Ũ‖_F ≤ 2 ‖A − Ã‖_F / (σ + σ̃)`. With `W = Uᴴ Ũ` and `Δ = A − Ã`, `X = 1 − W` solves
`P X + X P' = Uᴴ Δ − Δᴴ Ũ` (`Matrix.frobenius_norm_le_of_mul_add_mul_eq`), and `‖X‖_F = ‖U − Ũ‖_F`.
The real refinement with the two smallest singular values is
`Matrix.IsPolarDecomposition.frobenius_norm_sub_le_of_det_mul_pos`. -/
theorem IsPolarDecomposition.frobenius_norm_sub_le {A Ã U Ũ P P' : Matrix n n 𝕜}
    (h : IsPolarDecomposition A U P) (h' : IsPolarDecomposition Ã Ũ P') {σ σ' : ℝ}
    (hP : (P - (σ : 𝕜) • 1).PosSemidef) (hP' : (P' - (σ' : 𝕜) • 1).PosSemidef)
    (hσ : 0 < σ + σ') : ‖U - Ũ‖ ≤ 2 * ‖A - Ã‖ / (σ + σ') := by
  obtain ⟨hX, hsyl, hR⟩ := h.sylvester h'
  rw [← hX]
  calc ‖Uᴴ * (U - Ũ)‖ ≤ ‖Uᴴ * (A - Ã) - (A - Ã)ᴴ * Ũ‖ / (σ + σ') :=
        frobenius_norm_le_of_mul_add_mul_eq hP hP' hσ hsyl
    _ ≤ 2 * ‖A - Ã‖ / (σ + σ') := div_le_div_of_nonneg_right hR hσ.le

/-- The symmetric polar factor dominates the smallest singular value: `σ_min(A) ≤ P` in the
Loewner order. The eigenvalues of `P` are the stretches `‖A v‖ = ‖P v‖` of its unit
eigenvectors. -/
theorem IsPolarDecomposition.posSemidef_sub_iInf_colSingularValues {A U P : Matrix n n 𝕜}
    (h : IsPolarDecomposition A U P) :
    (P - ((⨅ i, A.colSingularValues i : ℝ) : 𝕜) • 1).PosSemidef := by
  set c := ⨅ i, A.colSingularValues i
  have hP := h.isHermitian
  set V := (hP.eigenvectorUnitary : Matrix n n 𝕜)
  have hV : V ∈ unitaryGroup n 𝕜 := hP.eigenvectorUnitary.2
  have hVV : V * Vᴴ = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.1 hV
  have hspec : P = V * diagonal (fun i => ((hP.eigenvalues i : ℝ) : 𝕜)) * Vᴴ := by
    conv_lhs => rw [hP.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
    rfl
  have hc : ∀ i, c ≤ hP.eigenvalues i := by
    intro i
    have : Nonempty n := ⟨i⟩
    have h1 := A.iInf_colSingularValues_mul_norm_le (hP.eigenvectorBasis i)
    have h2 : ‖toEuclideanLin A (hP.eigenvectorBasis i)‖ = hP.eigenvalues i := by
      rw [toEuclideanLin_apply, h.eq_mul, ← mulVec_mulVec,
        norm_toLp_mulVec_of_mem_unitaryGroup h.mem_unitaryGroup, hP.mulVec_eigenvectorBasis,
        WithLp.toLp_smul, WithLp.toLp_ofLp, norm_smul, hP.eigenvectorBasis.orthonormal.1 i,
        mul_one, Real.norm_eq_abs, abs_of_nonneg (h.posSemidef.eigenvalues_nonneg i)]
    rw [hP.eigenvectorBasis.orthonormal.1 i, mul_one, h2] at h1
    exact h1
  have heq : P - (c : 𝕜) • 1
      = V * diagonal (fun i => ((hP.eigenvalues i - c : ℝ) : 𝕜)) * Vᴴ := by
    have hd : diagonal (fun i => ((hP.eigenvalues i - c : ℝ) : 𝕜))
        = diagonal (fun i => ((hP.eigenvalues i : ℝ) : 𝕜)) - (c : 𝕜) • 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [sub_apply, smul_apply, diagonal_apply_eq, one_apply_eq, smul_eq_mul, mul_one]
        push_cast
        ring
      · simp only [sub_apply, smul_apply, diagonal_apply_ne _ hij, one_apply_ne hij, smul_zero,
          sub_zero]
    rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hVV,
      ← hspec]
  rw [heq]
  refine (PosSemidef.diagonal fun i => ?_).mul_mul_conjTranspose_same V
  exact RCLike.ofReal_nonneg.2 (sub_nonneg.2 (hc i))

/-- **The perturbation of the unitary polar factor by the smallest singular values** (the complex
Li–Sun bound, [golub2013matrix] §9.4.3): `‖U − Ũ‖_F ≤ 2 ‖A − Ã‖_F / (σ_min(A) + σ_min(Ã))`
when the denominator is positive (for instance when `A` is nonsingular). -/
theorem IsPolarDecomposition.frobenius_norm_sub_le_div_iInf_colSingularValues
    {A Ã U Ũ P P' : Matrix n n 𝕜} (h : IsPolarDecomposition A U P)
    (h' : IsPolarDecomposition Ã Ũ P')
    (hσ : 0 < (⨅ i, A.colSingularValues i) + ⨅ i, Ã.colSingularValues i) :
    ‖U - Ũ‖ ≤ 2 * ‖A - Ã‖ / ((⨅ i, A.colSingularValues i) + ⨅ i, Ã.colSingularValues i) :=
  h.frobenius_norm_sub_le h' h.posSemidef_sub_iInf_colSingularValues
    h'.posSemidef_sub_iInf_colSingularValues hσ

end Perturbation

/-! ### The real Li–Sun bound -/

section RealPerturbation

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Frobenius

omit [Fintype n] in
/-- A symmetric matrix bounded below by `b` off a unit vector `u` and by `a ≤ b` along it is
symmetric: the hypothesis shape of `Matrix.trace_mul_one_sub_ge`. -/
private theorem transpose_eq_of_posSemidef_pair {P : Matrix n n ℝ} {u : n → ℝ} {a b : ℝ}
    (hP : (P - b • 1 + (b - a) • vecMulVec u u).PosSemidef) : Pᵀ = P := by
  have h := hP.isHermitian.eq
  rw [conjTranspose_eq_transpose_of_trivial, transpose_add, transpose_sub, transpose_smul,
    transpose_smul, transpose_one, transpose_vecMulVec] at h
  simpa using h

/-- **A real Sylvester equation for `1 - W` with `W` a rotation** (the step behind the real
Li–Sun bound): if `P X + X Q = R` with `X = 1 - W`, `Wᵀ W = 1`, `det W = 1`, and `P`, `Q` bounded
below as in `Matrix.trace_mul_one_sub_ge` by `a ≤ b` and `a' ≤ b'`, then
`‖X‖_F ≤ 2 ‖R‖_F / (a + b + a' + b')`. Since `X Xᵀ = Xᵀ X = X + Xᵀ`,
`tr(Xᵀ R) = 2 tr(P X) + 2 tr(Q X) ≥ (a + b + a' + b') tr X = (a + b + a' + b')/2 · ‖X‖_F²`. -/
theorem frobenius_norm_one_sub_le_of_mul_add_mul_eq {P Q W R : Matrix n n ℝ} {u v : n → ℝ}
    {a b a' b' : ℝ} (hab : a ≤ b) (hu : u ⬝ᵥ u = 1)
    (hP : (P - b • 1 + (b - a) • vecMulVec u u).PosSemidef) (hab' : a' ≤ b')
    (hv : v ⬝ᵥ v = 1) (hQ : (Q - b' • 1 + (b' - a') • vecMulVec v v).PosSemidef)
    (hW : Wᵀ * W = 1) (hdet : W.det = 1) (hs : 0 < a + b + a' + b')
    (h : P * (1 - W) + (1 - W) * Q = R) : ‖1 - W‖ ≤ 2 * ‖R‖ / (a + b + a' + b') := by
  have hW' : W * Wᵀ = 1 := mul_eq_one_comm.1 hW
  have hPt := transpose_eq_of_posSemidef_pair hP
  have hQt := transpose_eq_of_posSemidef_pair hQ
  set X := 1 - W with hX
  have hXX : Xᵀ * X = X + Xᵀ := by
    rw [hX, transpose_sub, transpose_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hW]
    abel
  have hXX' : X * Xᵀ = X + Xᵀ := by
    rw [hX, transpose_sub, transpose_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hW']
    abel
  have hsymm : ∀ S : Matrix n n ℝ, Sᵀ = S → trace (S * Xᵀ) = trace (S * X) := fun S hS => by
    rw [← trace_transpose, transpose_mul, transpose_transpose, hS, trace_mul_comm]
  have hnorm : ‖X‖ ^ 2 = 2 * trace X := by
    have := frobenius_norm_sq_eq_trace (𝕜 := ℝ) X
    rw [conjTranspose_eq_transpose_of_trivial, hXX, trace_add, trace_transpose] at this
    simpa [two_mul] using this
  have hkey : trace (Xᵀ * R) = 2 * trace (P * X) + 2 * trace (Q * X) := by
    rw [← h, Matrix.mul_add, trace_add, trace_mul_comm Xᵀ, Matrix.mul_assoc, hXX',
      ← Matrix.mul_assoc, hXX, trace_mul_comm (X + Xᵀ), Matrix.mul_add, Matrix.mul_add, trace_add,
      trace_add, hsymm P hPt, hsymm Q hQt]
    ring
  have h1 := trace_mul_one_sub_ge hab hu hP hW hdet
  have h2 := trace_mul_one_sub_ge hab' hv hQ hW hdet
  have h3 := re_trace_conjTranspose_mul_le X R
  rw [conjTranspose_eq_transpose_of_trivial, RCLike.re_to_real] at h3
  rw [le_div_iff₀ hs]
  rcases (norm_nonneg X).eq_or_lt with hX0 | hX0
  · rw [← hX0, zero_mul]
    positivity
  · refine le_of_mul_le_mul_right ?_ hX0
    nlinarith

/-- **The real Li–Sun bound, in Loewner form**: if `A = U P` and `Ã = Ũ P'` are real polar
decompositions with `det A · det Ã > 0` and `P`, `P'` are bounded below as in
`Matrix.trace_mul_one_sub_ge` by `a ≤ b` and `a' ≤ b'` (for instance the two smallest singular
values of `A` and of `Ã`), then `‖U - Ũ‖_F ≤ 4 ‖A - Ã‖_F / (a + b + a' + b')`. The determinant
condition makes `W = Uᵀ Ũ` a rotation, and `1 - W = Uᵀ (U - Ũ)` solves the Sylvester equation of
`Matrix.frobenius_norm_one_sub_le_of_mul_add_mul_eq`. -/
theorem IsPolarDecomposition.frobenius_norm_sub_le_of_det_mul_pos {A Ã U Ũ P P' : Matrix n n ℝ}
    (h : IsPolarDecomposition A U P) (h' : IsPolarDecomposition Ã Ũ P')
    (hdet : 0 < A.det * Ã.det) {u v : n → ℝ} {a b a' b' : ℝ} (hab : a ≤ b) (hu : u ⬝ᵥ u = 1)
    (hP : (P - b • 1 + (b - a) • vecMulVec u u).PosSemidef) (hab' : a' ≤ b')
    (hv : v ⬝ᵥ v = 1) (hP' : (P' - b' • 1 + (b' - a') • vecMulVec v v).PosSemidef)
    (hs : 0 < a + b + a' + b') : ‖U - Ũ‖ ≤ 4 * ‖A - Ã‖ / (a + b + a' + b') := by
  obtain ⟨hX, hsyl, hR⟩ := h.sylvester h'
  have hUU : Uᵀ * U = 1 := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact h.conjTranspose_mul_self
  have hUU' : Ũᵀ * Ũ = 1 := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact h'.conjTranspose_mul_self
  have hUU'' : U * Uᵀ = 1 := mul_eq_one_comm.1 hUU
  set W := Uᵀ * Ũ with hWdef
  have hW : Wᵀ * W = 1 := by
    rw [hWdef, transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc U,
      hUU'', Matrix.one_mul, hUU']
  have hdetW : W.det = 1 := by
    have hpos : 0 < U.det * Ũ.det := by
      have hP0 := h.posSemidef.det_nonneg
      have hP0' := h'.posSemidef.det_nonneg
      rw [h.eq_mul, h'.eq_mul, det_mul, det_mul] at hdet
      by_contra hneg
      push Not at hneg
      nlinarith [mul_nonneg hP0 hP0']
    have hsq : (U.det * Ũ.det) ^ 2 = 1 := by
      rw [mul_pow, det_sq_eq_one_of_transpose_mul_self hUU,
        det_sq_eq_one_of_transpose_mul_self hUU', one_mul]
    rw [hWdef, det_mul, det_transpose]
    nlinarith
  have hXW : Uᴴ * (U - Ũ) = 1 - W := by
    rw [conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, hUU]
  rw [hXW] at hX hsyl
  rw [← hX]
  calc ‖1 - W‖ ≤ 2 * ‖Uᴴ * (A - Ã) - (A - Ã)ᴴ * Ũ‖ / (a + b + a' + b') :=
        frobenius_norm_one_sub_le_of_mul_add_mul_eq hab hu hP hab' hv hP' hW hdetW hs hsyl
    _ ≤ 2 * (2 * ‖A - Ã‖) / (a + b + a' + b') := by gcongr
    _ = 4 * ‖A - Ã‖ / (a + b + a' + b') := by ring

/-- **The symmetric polar factor above its two smallest singular values**: for a real polar
decomposition `A = U P` of order `n ≥ 1` there is a unit vector `u` (a right singular vector for
`σ_{n-1}`) with `P ⪰ σ_{n-2} (1 - u uᵀ) + σ_{n-1} u uᵀ`, the sorted singular values `σ_k` being
`Matrix.sortedSingularValues` (0-based). Read off an SVD `A = W diag(σ) Vᵀ`, where
`P = V diag(σ) Vᵀ` (`Matrix.IsSVD.isPolarDecomposition_of_square` and uniqueness of `P`). -/
theorem IsPolarDecomposition.exists_posSemidef_sub_sortedSingularValues {m : ℕ}
    {A U P : Matrix (Fin m) (Fin m) ℝ} (h : IsPolarDecomposition A U P) (hm : m ≠ 0) :
    ∃ u : Fin m → ℝ, u ⬝ᵥ u = 1 ∧
      (P - A.sortedSingularValues (m - 2) • 1 +
        (A.sortedSingularValues (m - 2) - A.sortedSingularValues (m - 1)) •
          vecMulVec u u).PosSemidef := by
  obtain ⟨W, σ, V, hs⟩ := exists_isSVD A
  have hp := hs.isPolarDecomposition_of_square
  have hVV : Vᵀ * V = 1 := by
    have := mem_unitaryGroup_iff'.1 hs.mem_unitaryGroup_right
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have hVV' : V * Vᵀ = 1 := mul_eq_one_comm.1 hVV
  have hPeq : P = V * diagonal (fun i : Fin m => σ i) * Vᵀ := by
    rw [h.eq_cfcSqrt, ← hp.eq_cfcSqrt, conjTranspose_eq_transpose_of_trivial]
    rfl
  rw [← hs.singularValues_eq (by omega) (by omega), ← hs.singularValues_eq (by omega) (by omega)]
  set l : Fin m := ⟨m - 1, by omega⟩
  set c := σ (m - 2)
  set k := σ (m - 2) - σ (m - 1)
  refine ⟨fun i => V i l, ?_, ?_⟩
  · have := congrFun (congrFun hVV l) l
    simpa [mul_apply, dotProduct] using this
  have hvv : vecMulVec (fun i => V i l) (fun i => V i l) =
      V * diagonal (Pi.single l 1) * Vᵀ := by
    ext i j
    rw [mul_apply]
    simp [vecMulVec_apply, mul_diagonal, Pi.single_apply]
  set d : Fin m → ℝ := fun i => σ i - c + k * (Pi.single l 1 : Fin m → ℝ) i with hd
  have hdiag : diagonal d =
      diagonal (fun i : Fin m => σ i) - c • 1 + k • diagonal (Pi.single l 1) := by
    ext i j
    by_cases hij : i = j <;> simp [hd, hij]
  have heq : P - c • 1 + k • vecMulVec (fun i => V i l) (fun i => V i l) =
      V * diagonal d * Vᵀ := by
    rw [hPeq, hvv, hdiag]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hVV']
  have hd0 : 0 ≤ d := fun i => by
    by_cases hi : i = l
    · subst hi
      change 0 ≤ σ (m - 1) - σ (m - 2) + (σ (m - 2) - σ (m - 1)) * (Pi.single l 1 : Fin m → ℝ) l
      rw [Pi.single_eq_same]
      linarith
    · have hi' : (i : ℕ) ≤ m - 2 := by
        have : (i : ℕ) ≠ m - 1 := fun h' => hi (Fin.ext h')
        omega
      change 0 ≤ σ i - σ (m - 2) + k * (Pi.single l 1 : Fin m → ℝ) i
      rw [Pi.single_eq_of_ne hi, mul_zero]
      linarith [hs.antitone hi']
  rw [heq]
  have := (PosSemidef.diagonal hd0).mul_mul_conjTranspose_same V
  rwa [conjTranspose_eq_transpose_of_trivial] at this

/-- **The Li–Sun perturbation bound for the orthogonal polar factor** ([golub2013matrix] §9.4.3,
quoted there from W. Li and W. Sun, SIAM J. Matrix Anal. Appl. 23 (2002) 1183–1193): for real
`A, Ã : Matrix (Fin m) (Fin m) ℝ` with `det A · det Ã > 0` and polar decompositions `A = U P`,
`Ã = Ũ P'`,
`‖U - Ũ‖_F ≤ 4 ‖A - Ã‖_F / (σ_{m-2}(A) + σ_{m-1}(A) + σ_{m-2}(Ã) + σ_{m-1}(Ã))`, the sum of the two
smallest singular values of each (`Matrix.sortedSingularValues`, 0-based).

The determinant condition cannot be dropped: `A = diag(1, ε)`, `Ã = diag(1, -ε)` have
`‖U - Ũ‖_F = 2` and `‖A - Ã‖_F = 2ε`. Li and Sun assume `‖A - Ã‖₂ < σ_{m-1}(A) + σ_{m-1}(Ã)`, which
keeps the segment from `A` to `Ã` nonsingular and so implies it. The proof
(`Matrix.IsPolarDecomposition.frobenius_norm_sub_le_of_det_mul_pos`) is not Li and Sun's: with
`W = Uᵀ Ũ` a rotation, the pairing inequality `Matrix.trace_mul_one_sub_ge` replaces their
eigenvalue pairing. -/
theorem frobenius_norm_polar_sub_le {m : ℕ} {A Ã U Ũ P P' : Matrix (Fin m) (Fin m) ℝ}
    (h : IsPolarDecomposition A U P) (h' : IsPolarDecomposition Ã Ũ P')
    (hdet : 0 < A.det * Ã.det) :
    ‖U - Ũ‖ ≤ 4 * ‖A - Ã‖ / (A.sortedSingularValues (m - 2) + A.sortedSingularValues (m - 1) +
      Ã.sortedSingularValues (m - 2) + Ã.sortedSingularValues (m - 1)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [show U - Ũ = 0 from Subsingleton.elim _ _, norm_zero]
    refine div_nonneg (by positivity) ?_
    linarith [A.sortedSingularValues_nonneg (0 - 2), A.sortedSingularValues_nonneg (0 - 1),
      Ã.sortedSingularValues_nonneg (0 - 2), Ã.sortedSingularValues_nonneg (0 - 1)]
  obtain ⟨u, hu, hP⟩ := h.exists_posSemidef_sub_sortedSingularValues hm.ne'
  obtain ⟨v, hv, hP'⟩ := h'.exists_posSemidef_sub_sortedSingularValues hm.ne'
  have hanti : ∀ B : Matrix (Fin m) (Fin m) ℝ,
      B.sortedSingularValues (m - 1) ≤ B.sortedSingularValues (m - 2) := fun B =>
    B.sortedSingularValues_antitone (by omega)
  have hA : A.det ≠ 0 := fun h0 => by rw [h0, zero_mul] at hdet; exact lt_irrefl 0 hdet
  have hpos : 0 < A.sortedSingularValues (m - 1) := by
    refine lt_of_le_of_ne (A.sortedSingularValues_nonneg _) (Ne.symm fun h0 => ?_)
    have hr := (A.sortedSingularValues_eq_zero_iff_rank_le (m - 1)).1 h0
    rw [rank_of_isUnit A ((isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hA)),
      Fintype.card_fin] at hr
    omega
  have hs : 0 < A.sortedSingularValues (m - 1) + A.sortedSingularValues (m - 2) +
      Ã.sortedSingularValues (m - 1) + Ã.sortedSingularValues (m - 2) := by
    linarith [A.sortedSingularValues_nonneg (m - 2), Ã.sortedSingularValues_nonneg (m - 2),
      Ã.sortedSingularValues_nonneg (m - 1)]
  have key := h.frobenius_norm_sub_le_of_det_mul_pos h' hdet (hanti A) hu hP (hanti Ã) hv hP' hs
  convert key using 2
  ring

end RealPerturbation

/-! ### The sign of the Jordan–Wielandt matrix -/

section Sign

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped ComplexOrder in
/-- The eigenvalues of a positive definite matrix lie in the open right half-plane. -/
private theorem re_pos_of_mem_spectrum_of_posDef {M : Matrix n n ℂ} (hM : M.PosDef) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ M) : 0 < μ.re := by
  rw [spectrum.mem_iff, isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← exists_mulVec_eq_zero_iff] at hμ
  obtain ⟨v, hv0, hv⟩ := hμ
  have hMv : M *ᵥ v = μ • v := by
    rw [sub_mulVec, sub_eq_zero, Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec] at hv
    exact hv.symm
  have h1 := hM.dotProduct_mulVec_pos hv0
  have h2 := PosDef.one.dotProduct_mulVec_pos hv0
  rw [hMv, dotProduct_smul, smul_eq_mul] at h1
  rw [one_mulVec] at h2
  obtain ⟨hre1, him1⟩ := Complex.lt_def.1 h1
  obtain ⟨hre2, him2⟩ := Complex.lt_def.1 h2
  simp only [Complex.zero_re, Complex.zero_im, Complex.mul_re] at hre1 hre2 him2
  rw [← him2, mul_zero, sub_zero] at hre1
  exact pos_of_mul_pos_left hre1 hre2.le

/-- **The sign of the Jordan–Wielandt matrix** ([golub2013matrix] §9.4.3): for a nonsingular
`A : Matrix n n ℂ` with polar decomposition `A = U P`, the sign of `[0 A; Aᴴ 0]` (the Hermitian
dilation of `Aᴴ`, `Matrix.hermitianDilation Aᴴ = fromBlocks 0 A Aᴴ 0`) is `[0 U; Uᴴ 0]`. With
`M = U P Uᴴ` (positive definite) and `X = [1 1; −Uᴴ Uᴴ]`, whose inverse is `½ [1 −U; 1 U]`,
`X⁻¹ [0 A; Aᴴ 0] X = diag(−M, M)`, so `Matrix.matrixSign_conj_fromBlocks` gives
`X diag(−1, 1) X⁻¹ = [0 U; Uᴴ 0]`. (The book omits "nonsingular", needed so that no eigenvalue
`±σᵢ` of the dilation is `0`.) -/
theorem matrixSign_hermitianDilation {A U P : Matrix n n ℂ} (hA : IsUnit A)
    (h : IsPolarDecomposition A U P) :
    matrixSign (hermitianDilation Aᴴ) = hermitianDilation Uᴴ := by
  have hUU : Uᴴ * U = 1 := h.conjTranspose_mul_self
  have hUU' : U * Uᴴ = 1 := mul_eq_one_comm.1 hUU
  have hUhu : IsUnit Uᴴ := (isUnit_iff_isUnit_det _).2 (isUnit_det_of_right_inverse hUU)
  have hAh : Aᴴ = P * Uᴴ := by
    rw [h.eq_mul, conjTranspose_mul, h.isHermitian.eq]
  -- the positive definite matrix `M = U P Uᴴ = A Uᴴ`
  set M := U * P * Uᴴ with hMdef
  have hP : P.PosDef := h.posSemidef.posDef_iff_isUnit.2 (h.isUnit hA)
  have hM : M.PosDef := by
    have := hP.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit hUhu)
    rwa [conjTranspose_conjTranspose] at this
  have hAU : A * Uᴴ = M := by rw [h.eq_mul]
  have hUM : Uᴴ * M = P * Uᴴ := by
    rw [hMdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  -- the eigenvector matrix `X` and its inverse
  set X : Matrix (n ⊕ n) (n ⊕ n) ℂ := fromBlocks 1 1 (-Uᴴ) Uᴴ with hXdef
  set Y : Matrix (n ⊕ n) (n ⊕ n) ℂ := (2 : ℂ)⁻¹ • fromBlocks 1 (-U) 1 U with hYdef
  have hYX : Y * X = 1 := by
    rw [hYdef, hXdef, Matrix.smul_mul, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul]
    simp only [Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, neg_neg, hUU']
    congr 1 <;> [skip; simp; simp; skip] <;>
      rw [← two_smul ℂ (1 : Matrix n n ℂ), smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  have hXinv : X⁻¹ = Y := inv_eq_left_inv hYX
  have hXu : IsUnit X := (isUnit_iff_isUnit_det _).2 (isUnit_det_of_left_inverse hYX)
  -- `H X = X diag(−M, M)`
  have hH : hermitianDilation Aᴴ = fromBlocks 0 A Aᴴ 0 := by
    rw [hermitianDilation, conjTranspose_conjTranspose]
  have hHX : fromBlocks 0 A Aᴴ 0 * X = X * fromBlocks (-M) 0 0 M := by
    rw [hXdef, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add,
      add_zero, Matrix.mul_neg, Matrix.neg_mul, neg_neg, neg_zero, hAU, hUM, hAh]
  have hconj : X⁻¹ * hermitianDilation Aᴴ * X =
      reindex (Equiv.refl _) (Equiv.refl _) (fromBlocks (-M) 0 0 M) := by
    rw [reindex_refl_refl, hH, Matrix.mul_assoc, hHX, ← Matrix.mul_assoc,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det X).1 hXu), Matrix.one_mul]
  have hneg : ∀ μ ∈ spectrum ℂ (-M), μ.re < 0 := fun μ hμ => by
    rw [← spectrum.neg_eq, Set.mem_neg] at hμ
    have := re_pos_of_mem_spectrum_of_posDef hM hμ
    rw [Complex.neg_re] at this
    linarith
  rw [matrixSign_conj_fromBlocks (Equiv.refl _) hXu hconj hneg
    fun μ hμ => re_pos_of_mem_spectrum_of_posDef hM hμ, reindex_refl_refl, hXinv, hYdef,
    Matrix.mul_smul, hXdef, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_smul,
    hermitianDilation, conjTranspose_conjTranspose]
  simp only [Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg,
    Matrix.neg_mul, neg_neg, hUU, neg_add_cancel]
  congr 1 <;> [simp; skip; skip; simp] <;>
    rw [← two_smul ℂ, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

end Sign

end Matrix
