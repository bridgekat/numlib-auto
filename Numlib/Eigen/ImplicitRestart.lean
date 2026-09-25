import Numlib.Eigen.QRAlgorithm
import Numlib.LinearAlgebra.Matrix.KrylovDecomposition

/-!
# Implicit restarting of the Arnoldi process

Implicit restarting (Sorensen 1992; [golub2013matrix] §10.5.2–10.5.4) compresses an `m`-step
Arnoldi decomposition `A Q = Q H + r e_mᵀ` to a `j`-step one whose starting vector has been filtered
by a polynomial `p(A) = ∏ (A − μ_i)`, without restarting the process from scratch. Two ingredients,
kept apart because the first is pure algebra:

* **the shifted-QR chain** `Matrix.IsShiftedQrChain H V R μ p` of `Numlib/Eigen/QRAlgorithm`
  (`H_i − μ_i I = V_i R_i`, `H_{i+1} = R_i V_i + μ_i I`), whose product identity
  `Matrix.prod_mul_prod_reverse_eq_prod_sub_smul_one` is [golub2013matrix] Theorem 10.5.1, and whose
  accumulated factor `V = V_0 ⋯ V_{p−1}` is unitary with `H_p = Vᴴ H_0 V`, has lower bandwidth `p`
  when the `V_i` are Hessenberg, and carries the filter polynomial in its first column;
* **what the chain does to an Arnoldi decomposition**: the change of basis
  `Matrix.IsKrylovDecomposition.mul_unitary` ((10.5.9)) followed by the truncation
  `Matrix.IsKrylovDecomposition.leading` to the leading `j + 1` columns
  (`Matrix.IsArnoldiDecomposition.implicitRestart`), whose first column is the filtered starting
  vector (`Matrix.IsArnoldiDecomposition.implicitRestart_first`).

Krylov–Schur restarting ([golub2013matrix] §10.5.4, Stewart 2001) is the same truncation applied
to a block-triangular (ordered Schur) change of basis, followed by a Hessenberg reduction with
prescribed last row (`Matrix.IsArnoldiDecomposition.krylovSchur`); its truncation keeps the
residual vector and restricts the residual row
(`Matrix.IsKrylovDecomposition.leading_of_apply_eq_zero`).

Indices: a decomposition with `j + p + 1` columns is the book's `m`-step one with `m = j + p + 1`;
it is truncated to `j + 1` columns (the book's `j`), `p` being the number of shifts.

## References

* [golub2013matrix] §10.5.
-/

open Finset

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- **Truncation of a Krylov decomposition across a zero block.** If `B` is block upper triangular
with respect to the split after index `j` (`B i l = 0` for `l ≤ j < i`), the leading `j + 1` columns
form a Krylov decomposition with the same residual vector and the residual row restricted. This is
the truncation of Krylov–Schur restarting ([golub2013matrix] §10.5.4). (It belongs beside
`Matrix.IsKrylovDecomposition.leading` in `Numlib/LinearAlgebra/Matrix/KrylovDecomposition`.) -/
theorem IsKrylovDecomposition.leading_of_apply_eq_zero {A : Matrix n n 𝕜} {r : n → 𝕜} {k : ℕ}
    {Q : Matrix n (Fin k) 𝕜} {B : Matrix (Fin k) (Fin k) 𝕜} {b : Fin k → 𝕜}
    (h : IsKrylovDecomposition A Q B r b) (j : Fin k)
    (hB : ∀ i l : Fin k, l ≤ j → j < i → B i l = 0) :
    IsKrylovDecomposition A (Q.submatrix id (Fin.castLE j.isLt))
      (B.submatrix (Fin.castLE j.isLt) (Fin.castLE j.isLt)) r (b ∘ Fin.castLE j.isLt) where
  conjTranspose_mul_self := by
    rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ id _ Function.bijective_id,
      h.conjTranspose_mul_self, submatrix_one _ (Fin.castLE_injective _)]
  conjTranspose_mulVec := by
    ext a
    change star (Q.col (Fin.castLE j.isLt a)) ⬝ᵥ r = 0
    exact h.star_col_dotProduct_residual _
  mul_eq := by
    ext x a
    have hcol := congrFun (congrFun h.mul_eq x) (Fin.castLE j.isLt a)
    have ha : Fin.castLE j.isLt a ≤ j := by
      rw [Fin.le_def, Fin.val_castLE]
      exact Nat.lt_succ_iff.1 a.isLt
    simp only [mul_apply, add_apply, vecMulVec_apply, submatrix_apply, id,
      Function.comp_apply] at hcol ⊢
    have hz : ∑ i ∈ Ioi j, Q x i * B i (Fin.castLE j.isLt a) = 0 :=
      sum_eq_zero fun i hi => by rw [hB i _ ha (mem_Ioi.1 hi), mul_zero]
    rw [hcol, sum_fin_eq_sum_castLE_add_sum_Ioi j (fun i => Q x i * B i (Fin.castLE j.isLt a)), hz,
      add_zero]

namespace IsArnoldiDecomposition

variable {A : Matrix n n 𝕜} {r : n → 𝕜}

omit [DecidableEq n] in
/-- **Implicit restart** ([golub2013matrix] §10.5.3). Let `A Q = Q H + r e_lastᵀ` be an Arnoldi
decomposition with `j + p + 1` columns and `H_0 = H, H_1, …, H_p` a chain of `p ≥ 1` shifted QR
steps with unitary upper Hessenberg `V_i` and upper triangular `R_i` ((10.5.4)). Put
`V = V_0 ⋯ V_{p−1}`, `W = Q V` and `H₊ = H_p = Vᴴ H V`. Then the leading `j + 1` columns of `W`
form a `(j + 1)`-column Arnoldi decomposition with matrix the leading block of `H₊` and residual
`H₊(j+1, j) w_{j+1} + V(last, j) r`. The book's residual `v_{mj} r_c` misses the first term. -/
theorem implicitRestart {j p : ℕ} {Q : Matrix n (Fin (j + p + 1)) 𝕜}
    {H : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) 𝕜} (h : IsArnoldiDecomposition A Q H r)
    {Hs V R : ℕ → Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) 𝕜} {μ : ℕ → 𝕜}
    (hc : IsShiftedQrChain Hs V R μ p) (h0 : Hs 0 = H)
    (hV : ∀ i < p, V i ∈ unitaryGroup (Fin (j + p + 1)) 𝕜)
    (hVH : ∀ i < p, (V i).IsUpperHessenberg) (hR : ∀ i < p, (R i).IsUpperTriangular)
    (hp : 0 < p) :
    IsArnoldiDecomposition A
      ((Q * ((List.range p).map V).prod).submatrix id
        (Fin.castLE (by omega : j + 1 ≤ j + p + 1)))
      ((Hs p).submatrix (Fin.castLE (by omega : j + 1 ≤ j + p + 1))
        (Fin.castLE (by omega : j + 1 ≤ j + p + 1)))
      (Hs p ⟨j + 1, by omega⟩ ⟨j, by omega⟩ •
          (Q * ((List.range p).map V).prod).col ⟨j + 1, by omega⟩ +
        ((List.range p).map V).prod (Fin.last (j + p)) ⟨j, by omega⟩ • r) := by
  set W := ((List.range p).map V).prod with hW
  obtain ⟨hWu, hHp⟩ := hc.conjTranspose_mul_mul hV
  have hK := h.toIsKrylovDecomposition.mul_unitary ((mem_unitaryGroup_iff').1 hWu)
  rw [← h0, ← star_eq_conjTranspose, ← hHp, single_one_vecMul] at hK
  have hHess : (Hs p).IsUpperHessenberg :=
    hc.isUpperHessenberg (h0 ▸ h.isUpperHessenberg) hR hVH p le_rfl
  set jj : Fin (j + p + 1) := ⟨j, by omega⟩
  have hb : ∀ l : Fin (j + p + 1), l < jj → W.row (Fin.last (j + p)) l = 0 := by
    intro l hl
    refine IsShiftedQrChain.hasLowerBandwidth_prod hVH _ _ ?_
    rw [card_filter_le_lt_fin, Fin.val_last]
    rw [Fin.lt_def] at hl
    change (l : ℕ) < j at hl
    omega
  have hA := hK.isArnoldiDecomposition_leading hHess jj hb
  have hres : ∑ i ∈ Ioi jj, Hs p i jj • (Q * W).col i + W.row (Fin.last (j + p)) jj • r =
      Hs p ⟨j + 1, by omega⟩ jj • (Q * W).col ⟨j + 1, by omega⟩ + W (Fin.last (j + p)) jj • r := by
    rw [sum_eq_single (⟨j + 1, by omega⟩ : Fin (j + p + 1))]
    · rfl
    · intro i hi hne
      have hi' : j < (i : ℕ) := Fin.lt_def.1 (mem_Ioi.1 hi)
      have hne' : (i : ℕ) ≠ j + 1 := fun h' => hne (Fin.ext h')
      rw [hHess i jj ⟨⟨j + 1, by omega⟩, Fin.lt_def.2 (show j < j + 1 by omega),
        Fin.lt_def.2 (show j + 1 < (i : ℕ) by omega)⟩, zero_smul]
    · intro hnot
      exact absurd (mem_Ioi.2 (Fin.lt_def.2 (show j < j + 1 by omega))) hnot
  rw [hres] at hA
  exact hA

/-- **The restarted starting vector is filtered** ([golub2013matrix] §10.5.3, `q₊ = p(A) q₁` up to
a scalar): in the setting of `Matrix.IsArnoldiDecomposition.implicitRestart`,
`p(A) (Q e₀) = (R_{p−1} ⋯ R_0)₀₀ · W e₀` with `p = ∏_{i<p} (X − μ_i)` and `W = Q V_0 ⋯ V_{p−1}`.
So the truncated decomposition is the `(j + 1)`-step Arnoldi decomposition started from `p(A) q₁`
(when that vector is nonzero), and the iteration continues at step `j + 1`. -/
theorem implicitRestart_first {j p : ℕ} {Q : Matrix n (Fin (j + p + 1)) 𝕜}
    {H : Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) 𝕜} (h : IsArnoldiDecomposition A Q H r)
    {Hs V R : ℕ → Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) 𝕜} {μ : ℕ → 𝕜}
    (hc : IsShiftedQrChain Hs V R μ p) (h0 : Hs 0 = H)
    (hR : ∀ i < p, (R i).IsUpperTriangular) :
    Polynomial.aeval A ((List.range p).map fun i => Polynomial.X - Polynomial.C (μ i)).prod *ᵥ
        (Q *ᵥ Pi.single 0 1) =
      ((List.range p).reverse.map R).prod 0 0 •
        ((Q * ((List.range p).map V).prod) *ᵥ Pi.single 0 1) := by
  have hdeg : (((List.range p).map fun i => Polynomial.X - Polynomial.C (μ i)).prod).natDegree ≤
      j + p := by
    refine (Polynomial.natDegree_list_prod_le _).trans ?_
    rw [List.map_map]
    refine (List.sum_le_length_nsmul _ 1 fun x hx => ?_).trans ?_
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact (Polynomial.natDegree_X_sub_C_le _)
    · simp
  have haeval : Polynomial.aeval H
      ((List.range p).map fun i => Polynomial.X - Polynomial.C (μ i)).prod =
      ((List.range p).map fun i => Hs 0 - μ i • 1).prod := by
    rw [map_list_prod, List.map_map, h0]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp [Algebra.algebraMap_eq_smul_one]
  have hfirst := hc.mulVec_first hR
  rw [bot_eq_zero] at hfirst
  rw [h.aeval_mulVec_first hdeg, haeval, hfirst, mulVec_smul, mulVec_mulVec]

omit [DecidableEq n] in
/-- **Krylov–Schur restarting** ([golub2013matrix] §10.5.4, Stewart 2001). Let
`A Q = Q H + r e_lastᵀ` be an Arnoldi decomposition with `k + 1` columns and `U` unitary with
`T = Uᴴ H U` block upper triangular with respect to the split after index `j` (an ordered Schur
form; triangularity itself is not needed). Then:

(a) the leading `j + 1` columns of `Q U` form a Krylov decomposition with the leading block `T₁₁`
of `T`, the same residual `r`, and residual row `u` the leading part of the last row of `U`;

(b) if moreover `Z` is unitary with `Zᴴ T₁₁ Z` upper Hessenberg and `Zᴴ ū = τ e_last` — such a `Z`
exists by `Matrix.exists_isUpperHessenberg_conj_lastCol` ([golub2013matrix] P10.5.2) applied to
`ū` — then `(Q U)(:, :j+1) Z` is an Arnoldi decomposition with matrix `Zᴴ T₁₁ Z` and residual
`τ̄ r` (the book's "`τ r_m`", real there). -/
theorem krylovSchur {k : ℕ} {Q : Matrix n (Fin (k + 1)) 𝕜}
    {H : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜} (h : IsArnoldiDecomposition A Q H r)
    {U : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜} (hU : U ∈ unitaryGroup (Fin (k + 1)) 𝕜)
    (j : Fin (k + 1)) (hT : ∀ i l : Fin (k + 1), l ≤ j → j < i → (star U * H * U) i l = 0) :
    IsKrylovDecomposition A ((Q * U).submatrix id (Fin.castLE j.isLt))
        ((star U * H * U).submatrix (Fin.castLE j.isLt) (Fin.castLE j.isLt)) r
        (fun l => U (Fin.last k) (Fin.castLE j.isLt l)) ∧
      ∀ Z ∈ unitaryGroup (Fin (j + 1)) 𝕜, ∀ τ : 𝕜,
        (star Z * (star U * H * U).submatrix (Fin.castLE j.isLt) (Fin.castLE j.isLt) *
          Z).IsUpperHessenberg →
        star Z *ᵥ star (fun l => U (Fin.last k) (Fin.castLE j.isLt l)) =
          Pi.single (Fin.last j) τ →
        IsArnoldiDecomposition A ((Q * U).submatrix id (Fin.castLE j.isLt) * Z)
          (star Z * (star U * H * U).submatrix (Fin.castLE j.isLt) (Fin.castLE j.isLt) * Z)
          (star τ • r) := by
  have hK := h.toIsKrylovDecomposition.mul_unitary ((mem_unitaryGroup_iff').1 hU)
  rw [single_one_vecMul] at hK
  have ha := hK.leading_of_apply_eq_zero j hT
  refine ⟨ha, fun Z hZ τ hZH hZu => ?_⟩
  have hK' := ha.mul_unitary ((mem_unitaryGroup_iff').1 hZ)
  have hrow : (U.row (Fin.last k) ∘ Fin.castLE j.isLt) ᵥ* Z = Pi.single (Fin.last j) (star τ) := by
    have := congrArg star hZu
    rw [star_mulVec, star_star, ← star_eq_conjTranspose, star_star, ← Pi.single_star] at this
    exact this
  rw [hrow] at hK'
  have hres : vecMulVec r (Pi.single (Fin.last j) (star τ)) =
      vecMulVec (star τ • r) (Pi.single (Fin.last j) 1) := by
    ext x l
    by_cases hl : l = Fin.last j
    · subst hl
      simp [vecMulVec_apply, mul_comm]
    · simp [vecMulVec_apply, Pi.single_eq_of_ne hl]
  exact ⟨⟨hK'.conjTranspose_mul_self, by rw [mulVec_smul, hK'.conjTranspose_mulVec, smul_zero],
    by rw [← hres]; exact hK'.mul_eq⟩, hZH⟩

end IsArnoldiDecomposition

end Matrix
