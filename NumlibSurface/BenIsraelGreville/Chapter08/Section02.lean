/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter05.Section03
import Numlib.Analysis.Convex.Duality.Ops
import Mathlib.Analysis.Matrix.Order

/-!
# Parallel sums

Section 8.2 of [benIsrael2003generalized] studies two matrix parallel
sums and the variational characterization of the Anderson–Duffin sum.

## Deviations from the source

The equivalence following Equation (9) requires additional hypotheses
for the Rao–Mitra formula. On singular positive semidefinite matrices the
sum of the conjugates has effective domain given by the intersection of
the two ranges.
-/

namespace BenIsraelGreville.Chapter08

open Matrix
open Chapter02 (orthogonalProjector)
open scoped InnerProductSpace ComplexOrder MatrixOrder

section ParallelSum

variable {𝕜 : Type*} [RCLike 𝕜]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Equation (2)** of [benIsrael2003generalized], Chapter 8.
The Anderson–Duffin parallel sum. -/
noncomputable def parallelSum (A B : Matrix m n 𝕜) : Matrix m n 𝕜 :=
  A * (A + B).pinv * B

/-- **Equation (3)** of [benIsrael2003generalized], Chapter 8.
The Rao–Mitra parallel sum. -/
noncomputable def reciprocalParallelSum (A B : Matrix m n 𝕜) : Matrix m n 𝕜 :=
  (A.pinv + B.pinv).pinv

/-- The real quadratic value used in **Equation (4)** of
[benIsrael2003generalized], Chapter 8. -/
noncomputable def quadraticValue (A : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) : ℝ :=
  RCLike.re ⟪A.toEuclideanLin x, x⟫_𝕜

private theorem quadraticValue_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (x : EuclideanSpace 𝕜 n) : 0 ≤ quadraticValue A x :=
  (isPositive_toEuclideanLin_iff.mpr hA).re_inner_nonneg_left x

private theorem quadraticValue_eq_zero_iff {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (x : EuclideanSpace 𝕜 n) : quadraticValue A x = 0 ↔ A.toEuclideanLin x = 0 := by
  let S := CFC.sqrt A
  have hS : Sᴴ * S = A := by
    rw [show Sᴴ = S from (CFC.sqrt_nonneg A).posSemidef.isHermitian]
    exact CFC.sqrt_mul_sqrt_self A hA.nonneg
  constructor
  · intro h
    have hn : ‖S.toEuclideanLin x‖ ^ 2 = 0 := by
      rw [quadraticValue, ← hS, toEuclideanLin_mul_apply, toEuclideanLin_conjTranspose_inner_left,
        inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re] at h
      exact h
    have hz := norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hn)
    rw [← hS, toEuclideanLin_mul_apply, hz, map_zero]
  · intro h
    simp [quadraticValue, h]

private theorem quadraticValue_add_matrix (A B : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    quadraticValue (A + B) x = quadraticValue A x + quadraticValue B x := by
  simp only [quadraticValue, map_add, LinearMap.add_apply, inner_add_left]

private theorem quadraticValue_add_vector {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (y d : EuclideanSpace 𝕜 n) :
    quadraticValue A (y + d) = quadraticValue A y + quadraticValue A d +
      2 * RCLike.re ⟪A.toEuclideanLin y, d⟫_𝕜 := by
  have hs := isSymmetric_toEuclideanLin_iff.mpr hA
  have he : RCLike.re ⟪A.toEuclideanLin d, y⟫_𝕜 =
      RCLike.re ⟪A.toEuclideanLin y, d⟫_𝕜 := by
    rw [hs d y]
    exact inner_re_symm _ _
  simp only [quadraticValue, map_add, inner_add_left, inner_add_right, he]
  ring

private theorem range_le_range_add_of_posSemidef {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    LinearMap.range B.toEuclideanLin ≤ LinearMap.range (A + B).toEuclideanLin := by
  have hker : LinearMap.ker (A + B).toEuclideanLin ≤ LinearMap.ker B.toEuclideanLin := by
    intro x hx
    change (A + B).toEuclideanLin x = 0 at hx
    change B.toEuclideanLin x = 0
    apply (quadraticValue_eq_zero_iff hB x).mp
    have he := (quadraticValue_eq_zero_iff (hA.add hB) x).mpr hx
    rw [quadraticValue_add_matrix] at he
    linarith [quadraticValue_nonneg hA x, quadraticValue_nonneg hB x]
  have hr := Submodule.orthogonal_le hker
  rwa [LinearMap.orthogonal_ker, LinearMap.orthogonal_ker,
    ← toEuclideanLin_conjTranspose_eq_adjoint, ← toEuclideanLin_conjTranspose_eq_adjoint,
    hB.isHermitian.eq, (hA.add hB).isHermitian.eq] at hr

private theorem add_mul_pinv_mul_right_of_posSemidef {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A + B) * (A + B).pinv * B = B := by
  apply toEuclideanLin.injective
  ext x
  rw [toEuclideanLin_mul_apply]
  have hx : B.toEuclideanLin x ∈ LinearMap.range (A + B).toEuclideanLin :=
    range_le_range_add_of_posSemidef hA hB ⟨x, rfl⟩
  obtain ⟨z, hz⟩ := hx
  rw [← hz, ← toEuclideanLin_mul_apply, mul_pinv_mul_self]

/-- **Equation (4)** of [benIsrael2003generalized], Chapter 8.
The real quadratic value of the parallel sum is the minimum energy of a
splitting of the vector. The minimum is attained at the first component
`(A + B)† B x`. -/
theorem parallelSum_isLeast_quadraticValue {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (x : EuclideanSpace 𝕜 n) :
    IsLeast (Set.range (fun y => quadraticValue A y + quadraticValue B (x - y)))
      (quadraticValue (parallelSum A B) x) := by
  let S := A + B
  let y₀ := S.pinv.toEuclideanLin (B.toEuclideanLin x)
  let z₀ := x - y₀
  have hS : S.toEuclideanLin y₀ = B.toEuclideanLin x := by
    change S.toEuclideanLin (S.pinv.toEuclideanLin (B.toEuclideanLin x)) = _
    rw [← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply]
    exact congrArg (fun M : Matrix n n 𝕜 => M.toEuclideanLin x)
      (add_mul_pinv_mul_right_of_posSemidef hA hB)
  have hmatch : B.toEuclideanLin z₀ = A.toEuclideanLin y₀ := by
    change B.toEuclideanLin (x - y₀) = A.toEuclideanLin y₀
    rw [map_sub, ← hS, map_add, LinearMap.add_apply, add_sub_cancel_right]
  have hvalue : quadraticValue A y₀ + quadraticValue B z₀ =
      quadraticValue (parallelSum A B) x := by
    have hsum : y₀ + z₀ = x := by dsimp [z₀]; abel
    have hy₀ : y₀ = (A + B).pinv.toEuclideanLin (B.toEuclideanLin x) := rfl
    simp only [quadraticValue, hmatch, ← map_add, ← inner_add_right, hsum, parallelSum,
      toEuclideanLin_mul_apply, ← hy₀]
  refine ⟨⟨y₀, hvalue⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  let d := y - y₀
  have hy : y₀ + d = y := by dsimp [d]; abel
  have hz : z₀ + -d = x - y := by dsimp [z₀, d]; abel
  change _ ≤ quadraticValue A y + quadraticValue B (x - y)
  rw [← hvalue]
  calc
    _ ≤ quadraticValue A (y₀ + d) + quadraticValue B (z₀ + -d) := by
      rw [quadraticValue_add_vector hA.isHermitian, quadraticValue_add_vector hB.isHermitian]
      have hneg : quadraticValue B (-d) = quadraticValue B d := by
        simp [quadraticValue, inner_neg_left, inner_neg_right]
      rw [hmatch, hneg, inner_neg_right, map_neg]
      linarith [quadraticValue_nonneg hA d, quadraticValue_nonneg hB d]
    _ = _ := by rw [hy, hz]

/-- **Equation (4)** of [benIsrael2003generalized], Chapter 8, expressed
as the infimum over all splittings of `x`. -/
theorem parallelSum_quadraticForm {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (x : EuclideanSpace 𝕜 n) :
    quadraticValue (parallelSum A B) x =
      ⨅ y, quadraticValue A y + quadraticValue B (x - y) :=
  (parallelSum_isLeast_quadraticValue hA hB x).csInf_eq.symm

/-- The Anderson–Duffin sum of positive semidefinite matrices is
positive semidefinite, as given by the minimum in Equation (4). -/
theorem parallelSum_posSemidef {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (parallelSum A B).PosSemidef := by
  let S := A + B
  have hs : S.pinvᴴ = S.pinv := by rw [← pinv_conjTranspose, (hA.add hB).isHermitian.eq]
  have he : parallelSum A B = B - B * S.pinv * B := by
    calc
      parallelSum A B = (A + B) * S.pinv * B - B * S.pinv * B := by
        change A * S.pinv * B = _
        rw [add_mul, add_mul, add_sub_cancel_right]
      _ = _ := by rw [add_mul_pinv_mul_right_of_posSemidef hA hB]
  have hHerm : (parallelSum A B).IsHermitian := by
    rw [he]
    change (B - B * S.pinv * B)ᴴ = B - B * S.pinv * B
    simp only [conjTranspose_sub, conjTranspose_mul, hs, hB.isHermitian.eq, mul_assoc]
  apply isPositive_toEuclideanLin_iff.mp
  refine ⟨isSymmetric_toEuclideanLin_iff.mpr hHerm, fun x => ?_⟩
  rcases (parallelSum_isLeast_quadraticValue hA hB x).1 with ⟨y, hy⟩
  change 0 ≤ quadraticValue (parallelSum A B) x
  rw [← hy]
  exact add_nonneg (quadraticValue_nonneg hA y) (quadraticValue_nonneg hB (x - y))

/-- The positive semidefinite parallel sum is symmetric in its two arguments. -/
theorem parallelSum_comm {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : parallelSum A B = parallelSum B A := by
  calc
    parallelSum A B = (parallelSum A B)ᴴ := (parallelSum_posSemidef hA hB).isHermitian.eq.symm
    _ = parallelSum B A := by
      unfold parallelSum
      rw [conjTranspose_mul, conjTranspose_mul, hA.isHermitian.eq, hB.isHermitian.eq,
        ← pinv_conjTranspose, (hA.add hB).isHermitian.eq, ← mul_assoc, add_comm A B]

/-- **Equation (5)** of [benIsrael2003generalized], Chapter 8.
Twice either parallel sum of the two orthogonal projectors equals the
orthogonal projector onto the intersection. -/
theorem projection_inf_eq_parallelSum (L M : Submodule ℂ (EuclideanSpace ℂ n)) :
    let P := orthogonalProjector L
    let Q := orthogonalProjector M
    orthogonalProjector (L ⊓ M) = (2 : ℂ) • parallelSum P Q ∧
      orthogonalProjector (L ⊓ M) = (2 : ℂ) • parallelSum Q P := by
  simpa only [parallelSum, add_comm (orthogonalProjector M) (orthogonalProjector L)] using
    Chapter05.theorem_5_3 L M

/-- **Equation (5)** of [benIsrael2003generalized], Chapter 8, in
variational form. Half the quadratic value of the common projector is
the minimum sum of the two projector quadratic values over splittings. -/
theorem projection_inf_quadraticForm (L M : Submodule ℂ (EuclideanSpace ℂ n))
    (x : EuclideanSpace ℂ n) :
    quadraticValue (orthogonalProjector (L ⊓ M)) x / 2 =
      ⨅ y, quadraticValue (orthogonalProjector L) y +
        quadraticValue (orthogonalProjector M) (x - y) := by
  have hpos (S : Submodule ℂ (EuclideanSpace ℂ n)) : (orthogonalProjector S).PosSemidef := by
    have hp := posSemidef_conjTranspose_mul_self (orthogonalProjector S)
    rw [(Chapter02.isHermitian_orthogonalProjector S).eq,
      show orthogonalProjector S * orthogonalProjector S = orthogonalProjector S from
        Chapter02.isIdempotentElem_orthogonalProjector S] at hp
    exact hp
  rw [← parallelSum_quadraticForm (hpos L) (hpos M), (projection_inf_eq_parallelSum L M).1]
  have h (A : Matrix n n ℂ) : quadraticValue ((2 : ℂ) • A) x = 2 * quadraticValue A x := by
    simp [quadraticValue, inner_smul_left]
  rw [h]
  ring

open Filter Topology Unitary in
/-- **Equation (1)** of [benIsrael2003generalized], Chapter 8.
In finite dimensions the powers of the product (PQP) converge to the
orthogonal projector onto the common range. -/
theorem tendsto_projection_inf (L M : Submodule ℂ (EuclideanSpace ℂ n)) :
    Tendsto (fun k : ℕ => (orthogonalProjector L * orthogonalProjector M *
      orthogonalProjector L) ^ k) atTop (𝓝 (orthogonalProjector (L ⊓ M))) := by
  classical
  let P := orthogonalProjector L
  let Q := orthogonalProjector M
  let T := P * Q * P
  let R := orthogonalProjector (L ⊓ M)
  have hp : Pᴴ = P := Chapter02.isHermitian_orthogonalProjector L
  have hq : Qᴴ = Q := Chapter02.isHermitian_orthogonalProjector M
  have hqq : Q * Q = Q := Chapter02.isIdempotentElem_orthogonalProjector M
  have hpos : T.PosSemidef := by
    have hG : (Q * P)ᴴ * (Q * P) = T := by
      calc
        _ = P * (Q * Q) * P := by simp only [conjTranspose_mul, hp, hq, Matrix.mul_assoc]
        _ = T := by rw [hqq]
    rw [← hG]
    exact posSemidef_conjTranspose_mul_self _
  let hT := hpos.isHermitian
  let d := hT.eigenvalues
  let v := hT.eigenvectorBasis
  let U := hT.eigenvectorUnitary
  have hv (i : n) : T.toEuclideanLin (v i) = d i • v i := by
    apply (WithLp.equiv 2 _).injective
    change (T.toEuclideanLin (v i)).ofLp = (d i • v i).ofLp
    rw [ofLp_toEuclideanLin, WithLp.ofLp_smul]
    exact hT.mulVec_eigenvectorBasis i
  have hd0 (i : n) : 0 ≤ d i := hpos.eigenvalues_nonneg i
  have hd1 (i : n) : d i ≤ 1 := by
    have hb (x : EuclideanSpace ℂ n) : ‖T.toEuclideanLin x‖ ≤ ‖x‖ := by
      simp only [T, P, Q, toEuclideanLin_mul_apply, Chapter02.toEuclideanLin_orthogonalProjector]
      exact (L.norm_starProjection_apply_le _).trans
        ((M.norm_starProjection_apply_le _).trans (L.norm_starProjection_apply_le _))
    have hi := hb (v i)
    have hn : ‖v i‖ = 1 := v.orthonormal.norm_eq_one i
    rwa [hv, norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_nonneg (hd0 i)] at hi
  have hfix (x : EuclideanSpace ℂ n) : T.toEuclideanLin x = x ↔ x ∈ L ⊓ M := by
    constructor
    · intro hx
      have hPx : P.toEuclideanLin x = x := calc
        _ = P.toEuclideanLin (T.toEuclideanLin x) := congrArg _ hx.symm
        _ = T.toEuclideanLin x := by
          rw [← toEuclideanLin_mul_apply]
          have hpp : P * P = P := Chapter02.isIdempotentElem_orthogonalProjector L
          have hPT : P * T = T := by
            change P * (P * Q * P) = _
            simp only [← Matrix.mul_assoc, hpp, T]
          rw [hPT]
        _ = x := hx
      have hPQ : P.toEuclideanLin (Q.toEuclideanLin x) = x := by
        simpa only [T, toEuclideanLin_mul_apply, hPx] using hx
      have hh := (Chapter05.theorem_5_4 L M).2.1
      rw [← hh]
      change x - L.starProjection (M.starProjection x) = 0
      simp only [P, Q, Chapter02.toEuclideanLin_orthogonalProjector] at hPQ
      exact sub_eq_zero.mpr hPQ.symm
    · rintro ⟨hxL, hxM⟩
      simp only [T, P, Q, toEuclideanLin_mul_apply, Chapter02.toEuclideanLin_orthogonalProjector]
      change L.starProjection (M.starProjection (L.starProjection x)) = x
      rw [L.starProjection_eq_self_iff.mpr hxL, M.starProjection_eq_self_iff.mpr hxM,
        L.starProjection_eq_self_iff.mpr hxL]
  let δ (i : n) : ℂ := if d i = 1 then 1 else 0
  have hR (i : n) : R.toEuclideanLin (v i) = δ i • v i := by
    rw [show R = orthogonalProjector (L ⊓ M) from rfl, Chapter02.toEuclideanLin_orthogonalProjector]
    change (L ⊓ M).starProjection (v i) = (if d i = 1 then (1 : ℂ) else 0) • v i
    by_cases hi : d i = 1
    · rw [ite_eq_left hi, one_smul]
      apply (L ⊓ M).starProjection_eq_self_iff.mpr
      rw [← hfix, hv, hi, one_smul]
    · rw [ite_eq_right hi, zero_smul]
      apply (L ⊓ M).starProjection_apply_eq_zero_iff.mpr
      intro w hw
      have h := (isSymmetric_toEuclideanLin_iff.mpr hT) w (v i)
      rw [(hfix w).mpr hw, hv, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right] at h
      have hz : (((d i : ℝ) : ℂ) - 1) * ⟪w, v i⟫_ℂ = 0 := by linear_combination -h
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (by exact_mod_cast hi))
  have hdiagR : conjStarAlgAut ℂ _ U (diagonal δ) = R := by
    apply toEuclideanLin.injective
    apply v.toBasis.ext
    intro i
    change (conjStarAlgAut ℂ _ U (diagonal δ)).toEuclideanLin (v i) = R.toEuclideanLin (v i)
    rw [hR]
    apply (WithLp.equiv 2 _).injective
    change ((conjStarAlgAut ℂ _ U (diagonal δ)).toEuclideanLin (v i)).ofLp = (δ i • v i).ofLp
    rw [ofLp_toEuclideanLin, WithLp.ofLp_smul, conjStarAlgAut_apply]
    have hUV : (U : Matrix n n ℂ) *ᵥ Pi.single i 1 = (v i).ofLp :=
      hT.eigenvectorUnitary_mulVec i
    have hVU : ((star U : unitaryGroup n ℂ) : Matrix n n ℂ) *ᵥ (v i).ofLp = Pi.single i 1 :=
      hT.star_eigenvectorUnitary_mulVec i
    have hsingle : Pi.single i (δ i * (1 : ℂ)) = δ i • Pi.single i (1 : ℂ) :=
      Pi.single_smul' i (δ i) (1 : ℂ)
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← Unitary.coe_star, hVU,
      Matrix.diagonal_mulVec_single, hsingle, mulVec_smul, hUV]
  have hpow (k : ℕ) :
      T ^ k = conjStarAlgAut ℂ _ U (diagonal (fun i => ((d i : ℝ) : ℂ) ^ k)) := by
    have he : (diagonal (RCLike.ofReal ∘ d : n → ℂ)) ^ k =
        diagonal (fun i => ((d i : ℝ) : ℂ) ^ k) := diagonal_pow _ _
    rw [← he, map_pow]
    exact congrArg (· ^ k) hT.spectral_theorem
  have hd : Tendsto (fun (k : ℕ) (i : n) => ((d i : ℝ) : ℂ) ^ k) atTop (𝓝 δ) := by
    rw [tendsto_pi_nhds]
    intro i
    by_cases hi : d i = 1
    · simp [hi, δ]
    · have hlt : d i < 1 := lt_of_le_of_ne (hd1 i) hi
      have hconv := tendsto_pow_atTop_nhds_zero_of_lt_one (hd0 i) hlt
      have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hconv
      simpa [δ, hi, Function.comp_def] using hc
  have hcon : Continuous (fun x : n → ℂ => conjStarAlgAut ℂ _ U (diagonal x)) := by
    simp only [conjStarAlgAut_apply]
    exact (continuous_const.matrix_mul continuous_id.matrix_diagonal).matrix_mul continuous_const
  change Tendsto (fun k : ℕ => T ^ k) atTop (𝓝 R)
  simp only [hpow, ← hdiagR]
  exact hcon.continuousAt.tendsto.comp hd

/-- The scalar resistance identity from Section 8.2 of
[benIsrael2003generalized], following Equation (4). -/
theorem parallelSum_scalar {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * b / (a + b) = (a⁻¹ + b⁻¹)⁻¹ := by
  have hab : a + b ≠ 0 := (add_pos ha hb).ne'
  have hinv : a⁻¹ + b⁻¹ ≠ 0 := (add_pos (inv_pos.mpr ha) (inv_pos.mpr hb)).ne'
  field_simp [ha.ne', hb.ne', hab, hinv]
  ring

/-- Complementary nonzero diagonal projections distinguish the two
parallel sums in Section 8.2 of [benIsrael2003generalized]. -/
theorem parallelSum_ne_reciprocalParallelSum :
    let A : Matrix (Fin 2) (Fin 2) ℝ := diagonal (fun i => if i = 0 then 1 else 0)
    let B : Matrix (Fin 2) (Fin 2) ℝ := diagonal (fun i => if i = 0 then 0 else 1)
    A.PosSemidef ∧ B.PosSemidef ∧ parallelSum A B = 0 ∧ reciprocalParallelSum A B = 1 := by
  intro A B
  have hA : A.PosSemidef := posSemidef_diagonal_iff.mpr (fun i => by split_ifs <;> norm_num)
  have hB : B.PosSemidef := posSemidef_diagonal_iff.mpr (fun i => by split_ifs <;> norm_num)
  have hsum : A + B = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i = 0 <;> simp [A, B, hi]
    · simp [A, B, hij]
  have hm : A * B = 0 := by
    change diagonal _ * diagonal _ = _
    rw [diagonal_mul_diagonal, ← diagonal_zero]
    congr 1
    ext i
    by_cases hi : i = 0 <;> simp [hi]
  have hpA : A * A = A := by
    change diagonal _ * diagonal _ = diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    ext i
    by_cases hi : i = 0 <;> simp [hi]
  have hpB : B * B = B := by
    change diagonal _ * diagonal _ = diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    ext i
    by_cases hi : i = 0 <;> simp [hi]
  have hp {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : P.IsHermitian) (hmul : P * P = P) :
      P.pinv = P :=
    (pinv_unique P (by rw [hmul, hmul]) (by rw [hmul, hmul])
      (hmul.symm ▸ hP) (hmul.symm ▸ hP)).symm
  have hone : (1 : Matrix (Fin 2) (Fin 2) ℝ).pinv = 1 := by
    rw [pinv_eq_inv isUnit_one, inv_one]
  refine ⟨hA, hB, ?_, ?_⟩
  · rw [parallelSum, hsum, hone, Matrix.mul_one, hm]
  · rw [reciprocalParallelSum, hp hA.isHermitian hpA, hp hB.isHermitian hpB, hsum, hone]

end ParallelSum

section Fenchel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Equation (6)** of [benIsrael2003generalized], Chapter 8.
The Fenchel conjugate in the real inner product pairing. -/
noncomputable abbrev convexConjugate (f : E → EReal) : E → EReal :=
  ConvexAnalysis.convexConj (innerₗ E) f

/-- The Fenchel conjugate is convex. A function with no value `−∞` is
its biconjugate exactly when it is convex and lower semicontinuous. -/
theorem convexConjugate_biconjugate [CompleteSpace E] (f : E → EReal)
    (hf : ∀ x, f x ≠ ⊥) : ConvexAnalysis.ConvexFn (convexConjugate f) ∧
      (ConvexAnalysis.convexBiconj (innerₗ E) f = f ↔
        ConvexAnalysis.ConvexFn f ∧ LowerSemicontinuous f) := by
  refine ⟨ConvexAnalysis.convexFn_convexConj _ _, ?_⟩
  constructor
  · intro he
    have hconv : ConvexAnalysis.ConvexFn f := he ▸ ConvexAnalysis.convexFn_convexConj _ _
    have hc : ConvexAnalysis.ClosedConvex f :=
      (ConvexAnalysis.convexBiconj_eq_convexCl_inner hconv).symm.trans he
    exact ⟨hconv, (ConvexAnalysis.closedConvex_iff_lowerSemicontinuous hf).mp hc⟩
  · rintro ⟨hconv, hsc⟩
    exact (ConvexAnalysis.convexBiconj_eq_convexCl_inner hconv).trans
      ((ConvexAnalysis.closedConvex_iff_lowerSemicontinuous hf).mpr hsc)

/-- **Equation (8)** of [benIsrael2003generalized], Chapter 8.
The extended-real infimal convolution. -/
noncomputable abbrev infimalConvolution (f g : E → EReal) : E → EReal :=
  ConvexAnalysis.infConv f g

omit [InnerProductSpace ℝ E] in
/-- **Equation (8)** of [benIsrael2003generalized], Chapter 8.
The pointwise infimum for functions with no value `−∞`. -/
theorem infimalConvolution_eq_iInf {f g : E → EReal}
    (hf : ∀ x, f x ≠ ⊥) (hg : ∀ x, g x ≠ ⊥) (x : E) :
    infimalConvolution f g x = ⨅ y, f y + g (x - y) := by
  change ConvexAnalysis.infConv f g x = _
  rw [ConvexAnalysis.infConv_apply hf hg]
  apply le_antisymm
  · apply le_iInf
    intro y
    have h := iInf_le (fun z => f (x - z) + g z) (x - y)
    simpa only [sub_sub_cancel] using h
  · apply le_iInf
    intro y
    have h := iInf_le (fun z => f z + g (x - z)) (x - y)
    simpa only [sub_sub_cancel] using h

/-- **Equation (9)** of [benIsrael2003generalized], Chapter 8.
Infimal convolution preserves convexity, and conjugation takes it to
pointwise addition. -/
theorem convexConjugate_infimalConvolution {f g : E → EReal}
    (hf : ConvexAnalysis.ConvexFn f) (hg : ConvexAnalysis.ConvexFn g) :
    ConvexAnalysis.ConvexFn (infimalConvolution f g) ∧
      convexConjugate (infimalConvolution f g) = convexConjugate f + convexConjugate g :=
  ⟨ConvexAnalysis.convexFn_infConv hf hg, ConvexAnalysis.convexConj_infConv _ f g⟩

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Equation (7)** of [benIsrael2003generalized], Chapter 8.
The conjugate of half of a positive semidefinite quadratic form is half
of the pseudoinverse quadratic form on the range and is infinite off it. -/
theorem convexConjugate_quadraticForm {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (ξ : EuclideanSpace ℝ n) :
    (ξ ∈ LinearMap.range A.toEuclideanLin →
      convexConjugate (fun x => ((quadraticValue A x / 2 : ℝ) : EReal)) ξ =
        ((quadraticValue A.pinv ξ / 2 : ℝ) : EReal)) ∧
    (ξ ∉ LinearMap.range A.toEuclideanLin →
      convexConjugate (fun x => ((quadraticValue A x / 2 : ℝ) : EReal)) ξ = ⊤) := by
  let term (x : EuclideanSpace ℝ n) := ⟪x, ξ⟫_ℝ - quadraticValue A x / 2
  have hconj :
      convexConjugate (fun x => ((quadraticValue A x / 2 : ℝ) : EReal)) ξ =
        ⨆ x, (term x : EReal) := by
    unfold convexConjugate ConvexAnalysis.convexConj
    congr 1
  rw [hconj]
  constructor
  · intro hξ
    let y := A.pinv.toEuclideanLin ξ
    have hy : A.toEuclideanLin y = ξ := by
      change A.toEuclideanLin (A.pinv.toEuclideanLin ξ) = ξ
      obtain ⟨z, hz⟩ := hξ
      rw [← hz, ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, mul_pinv_mul_self]
    have hcalc (d : EuclideanSpace ℝ n) :
        term (y + d) = quadraticValue A.pinv ξ / 2 - quadraticValue A d / 2 := by
      have hAy : quadraticValue A y = ⟪y, ξ⟫_ℝ := by
        simp only [quadraticValue, hy, RCLike.re_to_real]
        exact real_inner_comm _ _
      have hP : quadraticValue A.pinv ξ = ⟪y, ξ⟫_ℝ := rfl
      dsimp only [term]
      rw [inner_add_left, quadraticValue_add_vector hA.isHermitian, hAy, hP, hy,
        RCLike.re_to_real, real_inner_comm ξ d]
      ring
    apply le_antisymm
    · refine iSup_le fun x => EReal.coe_le_coe_iff.mpr ?_
      have hx := hcalc (x - y)
      rw [show y + (x - y) = x by abel] at hx
      linarith [quadraticValue_nonneg hA (x - y)]
    · have h := le_iSup (fun x => (term x : EReal)) (y + 0)
      rw [hcalc, show quadraticValue A 0 = 0 by simp [quadraticValue], zero_div, sub_zero] at h
      exact h
  · intro hξ
    have horth : (LinearMap.ker A.toEuclideanLin)ᗮ = LinearMap.range A.toEuclideanLin := by
      rw [LinearMap.orthogonal_ker, ← toEuclideanLin_conjTranspose_eq_adjoint, hA.isHermitian.eq]
    rw [← horth] at hξ
    change ¬ (∀ d ∈ LinearMap.ker A.toEuclideanLin, ⟪d, ξ⟫_ℝ = 0) at hξ
    push Not at hξ
    obtain ⟨d, hd, hne⟩ := hξ
    change A.toEuclideanLin d = 0 at hd
    refine (EReal.eq_top_iff_forall_lt _).mpr fun r => ?_
    let t := (r + 1) / ⟪d, ξ⟫_ℝ
    have ht : term (t • d) = r + 1 := by
      dsimp only [term]
      rw [real_inner_smul_left, quadraticValue, map_smul, hd, smul_zero, inner_zero_left]
      simp only [RCLike.re_to_real, zero_div, sub_zero]
      exact div_mul_cancel₀ _ hne
    apply lt_of_lt_of_le (b := ((r + 1 : ℝ) : EReal))
    · exact EReal.coe_lt_coe_iff.mpr (lt_add_one r)
    · rw [← ht]
      exact le_iSup (fun x => (term x : EReal)) (t • d)

/-- In the argument following Equation (9), the sum of the two quadratic
conjugates is finite exactly on the intersection of the ranges. -/
theorem parallelSum_conjugate_effectiveDomain {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (ξ : EuclideanSpace ℝ n) :
    convexConjugate (fun x => ((quadraticValue A x / 2 : ℝ) : EReal)) ξ +
        convexConjugate (fun x => ((quadraticValue B x / 2 : ℝ) : EReal)) ξ ≠ ⊤ ↔
      ξ ∈ LinearMap.range A.toEuclideanLin ⊓ LinearMap.range B.toEuclideanLin := by
  have ha := convexConjugate_quadraticForm hA ξ
  have hb := convexConjugate_quadraticForm hB ξ
  change _ ↔ ξ ∈ LinearMap.range A.toEuclideanLin ∧ ξ ∈ LinearMap.range B.toEuclideanLin
  by_cases hξA : ξ ∈ LinearMap.range A.toEuclideanLin <;>
    by_cases hξB : ξ ∈ LinearMap.range B.toEuclideanLin <;>
      simp [hξA, hξB, ha.1, ha.2, hb.1, hb.2, ← EReal.coe_add]

end Fenchel

end BenIsraelGreville.Chapter08
