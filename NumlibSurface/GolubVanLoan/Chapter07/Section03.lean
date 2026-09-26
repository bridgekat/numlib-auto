import Numlib.Analysis.Matrix.SingularValues
import Numlib.Eigen.InvariantSubspace
import Numlib.Eigen.PowerMethod
import Numlib.Eigen.QRAlgorithm
import Numlib.LinearAlgebra.Matrix.LU
import NumlibSurface.GolubVanLoan.Chapter07.Section02

/-!
# Golub–Van Loan §7.3: power iterations

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition
[golub2013matrix], §7.3: the QR iteration (7.3.1)–(7.3.2) as a unitary similarity, the power method
(7.3.3) with its rate (7.3.5) and its backward error, orthogonal iteration (7.3.6) and the dominant
invariant subspace, the QR iteration as orthogonal iteration (§7.3.3), and the appendix: Lemma 7.3.2
and the proof displays (7.3.20), (7.3.23)–(7.3.24).

## Conventions

Complex matrices `Matrix (Fin n) (Fin n) ℂ` as in §7.1, except that the two iterations chapter 8
reuses — the power method (7.3.3) and orthogonal iteration (7.3.6) — are stated over any `RCLike`
field `𝕜`, so that chapter 8's (8.2.3) and (8.2.8) are their instances at `ℝ`. Vectors live in
`EuclideanSpace 𝕜 (Fin n)` where norms matter and `A` acts by `Matrix.toEuclideanLin`. "Some QR
factorization" is recorded as data (the factors `U_k`, `R_k`), or by the backbone's
`Matrix.IsShiftedQrStep` and `Matrix.IsOrthogonalIterationStep`, so that every statement holds for
every choice of factorization, as the book's do. Subspace distance is `Submodule.gap`.

## Sources

`Numlib/Eigen/PowerMethod` (`Krylov.powerIterate` and its rates), `Numlib/Eigen/QRAlgorithm`
(`Matrix.IsShiftedQrStep`, `Matrix.IsOrthogonalIterationStep`), `Numlib/Eigen/InvariantSubspace`
(Lemma 7.3.2, the dominant invariant subspace), `Numlib/LinearAlgebra/Matrix/Sylvester` (`sep`).

## Not formalized

Stewart's accelerated orthogonal iteration (`≈` rates, no algorithm given); the heuristics
`|λ^(k) - λ₁| ≈ ‖r^(k)‖₂ / s(λ₁)` and `s(λ₁) ≈ |w^(k)ᴴ q^(k)|`; "under reasonable assumptions the
`T_k` converge to upper triangular form" for the LR iteration; the proof-internal (7.3.17),
(7.3.21)–(7.3.23) (identities whose content is Theorem 7.3.1); the flop remark.
-/

open Matrix Filter Topology

namespace GolubVanLoan.Chapter07

variable {n : ℕ}

/-! ### The QR iteration (7.3.1) -/

/-- **(7.3.1)–(7.3.2).** If `T₀ = U₀ᴴ A U₀` with `U₀` unitary and `T_k` comes from `T_{k-1}` by a QR
step for some QR factorization, `T_{k-1} = U_k R_k`, `T_k = R_k U_k`, then
`T_k = (U₀ U₁ ⋯ U_k)ᴴ A (U₀ U₁ ⋯ U_k)`: each `T_k` is unitarily similar to `A`. -/
theorem equation_7_3_2 {A : Matrix (Fin n) (Fin n) ℂ} {T U R : ℕ → Matrix (Fin n) (Fin n) ℂ}
    (hU : ∀ k, U k ∈ unitaryGroup (Fin n) ℂ) (hT0 : T 0 = star (U 0) * A * U 0)
    (hQR : ∀ k, T k = U (k + 1) * R (k + 1)) (hRQ : ∀ k, T (k + 1) = R (k + 1) * U (k + 1))
    (k : ℕ) :
    T k = star ((List.range (k + 1)).map U).prod * A * ((List.range (k + 1)).map U).prod := by
  induction k with
  | zero => simpa using hT0
  | succ k ih =>
    have hUU : star (U (k + 1)) * U (k + 1) = 1 := mem_unitaryGroup_iff'.1 (hU (k + 1))
    have hstep : T (k + 1) = star (U (k + 1)) * T k * U (k + 1) := by
      rw [hRQ, hQR k, ← Matrix.mul_assoc (star (U (k + 1))), hUU, Matrix.one_mul]
    rw [hstep, ih, List.range_succ (n := k + 1), List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton, star_mul]
    simp only [Matrix.mul_assoc]

/-! ### §7.3.1 The power method -/

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **(7.3.3), the power method**, over any `RCLike` field (the book states it over `ℂ`; chapter 8's
(8.2.3) is the instance `𝕜 = ℝ`): `q^(0) = q₀`, `z^(k) = A q^(k-1)`, `q^(k) = z^(k)/‖z^(k)‖₂`,
`λ^(k) = q^(k)ᴴ A q^(k)`, returned as the pair `(q^(k), λ^(k))`. For a unit `q₀` the vectors are the
backbone's `Krylov.powerIterate` (`powerMethod_fst`). -/
noncomputable def powerMethod (A : Matrix (Fin n) (Fin n) 𝕜) (q₀ : EuclideanSpace 𝕜 (Fin n)) :
    ℕ → EuclideanSpace 𝕜 (Fin n) × 𝕜
  | 0 => (q₀, inner 𝕜 q₀ (toEuclideanLin A q₀))
  | k + 1 =>
    let z := toEuclideanLin A (powerMethod A q₀ k).1
    let q := (‖z‖ : 𝕜)⁻¹ • z
    (q, inner 𝕜 q (toEuclideanLin A q))

/-- The eigenvalue estimate of the power method is the Rayleigh quotient of its vector. -/
theorem powerMethod_snd (A : Matrix (Fin n) (Fin n) 𝕜) (q₀ : EuclideanSpace 𝕜 (Fin n)) (k : ℕ) :
    (powerMethod A q₀ k).2 =
      inner 𝕜 (powerMethod A q₀ k).1 (toEuclideanLin A (powerMethod A q₀ k).1) := by
  cases k <;> rfl

/-- For a unit starting vector the vectors of the power method (7.3.3) are the backbone's
`Krylov.powerIterate`, the normalizations of `A^k q₀`. -/
theorem powerMethod_fst (A : Matrix (Fin n) (Fin n) 𝕜) {q₀ : EuclideanSpace 𝕜 (Fin n)}
    (hq₀ : ‖q₀‖ = 1) (k : ℕ) :
    (powerMethod A q₀ k).1 = Krylov.powerIterate (toEuclideanLin A) q₀ k :=
  Krylov.eq_powerIterate_of_recurrence (toEuclideanLin A) q₀
    (y := fun j => (powerMethod A q₀ j).1) (by
    change q₀ = _
    rw [hq₀, RCLike.ofReal_one, inv_one, one_smul]) (fun _ => rfl) k

/-- **(7.3.5), rigorous.** Let `x : Fin n → EuclideanSpace 𝕜 (Fin n)` be unit eigenvectors of `A`,
`A x_i = λ_i x_i`, with `λ_{i₀}` dominant: `|λ_i| ≤ ρ < |λ_{i₀}|` for `i ≠ i₀` (the book's
`ρ = |λ₂|`). If the unit `q^(0) = ∑ a_i x_i` has `a_{i₀} ≠ 0` (7.3.4), then
`|λ_{i₀} - λ^(k)| ≤ C (ρ / |λ_{i₀}|)^k` for some `C` and all `k`. -/
theorem equation_7_3_5 {A : Matrix (Fin n) (Fin n) 𝕜} {x : Fin n → EuclideanSpace 𝕜 (Fin n)}
    {l : Fin n → 𝕜} (hx : ∀ i, toEuclideanLin A (x i) = l i • x i) (hx1 : ∀ i, ‖x i‖ = 1)
    {i₀ : Fin n} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ∀ i, i ≠ i₀ → ‖l i‖ ≤ ρ) (hdom : ρ < ‖l i₀‖)
    {a : Fin n → 𝕜}
    (ha : a i₀ ≠ 0) {q₀ : EuclideanSpace 𝕜 (Fin n)} (hq₀ : ‖q₀‖ = 1)
    (hq : q₀ = ∑ i, a i • x i) :
    ∃ C : ℝ, ∀ k, ‖l i₀ - (powerMethod A q₀ k).2‖ ≤ C * (ρ / ‖l i₀‖) ^ k := by
  have hl₀ : l i₀ ≠ 0 := norm_pos_iff.1 (hρ0.trans_lt hdom)
  obtain ⟨C, hC⟩ := Krylov.exists_norm_inner_powerIterate_sub_le_of_eigenbasis
    (LinearMap.continuous_of_finiteDimensional _) hx hx1 hl₀ hρ ha hq
  refine ⟨C, fun k => ?_⟩
  rw [powerMethod_snd, powerMethod_fst A hq₀, norm_sub_rev]
  exact hC k

section L2

open scoped Matrix.Norms.L2Operator

/-- **§7.3.1, the backward error of the power method.** With `r^(k) = A q^(k) - λ^(k) q^(k)`, the
eigenvalue estimate `λ^(k)` is an exact eigenvalue, with eigenvector `q^(k)`, of `A + E` for some
`E` with `‖E‖₂ = ‖r^(k)‖₂` (the book's `E^(k) = -r^(k) q^(k)ᴴ`), and no smaller perturbation does
this. -/
theorem powerMethod_backwardError (A : Matrix (Fin n) (Fin n) 𝕜) (q₀ : EuclideanSpace 𝕜 (Fin n))
    (k : ℕ) (hq : ‖(powerMethod A q₀ k).1‖ = 1) :
    IsLeast {ε : ℝ | ∃ E : Matrix (Fin n) (Fin n) 𝕜,
        toEuclideanLin (A + E) (powerMethod A q₀ k).1 =
          (powerMethod A q₀ k).2 • (powerMethod A q₀ k).1 ∧ ‖E‖ = ε}
      ‖toEuclideanLin A (powerMethod A q₀ k).1 -
        (powerMethod A q₀ k).2 • (powerMethod A q₀ k).1‖ := by
  set q := (powerMethod A q₀ k).1
  set θ := (powerMethod A q₀ k).2
  have h := isLeast_eigen_backwardError (toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) A) hq θ
  refine ⟨?_, fun ε ⟨E, hE, hεE⟩ => h.2 ⟨-toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) E, ?_, ?_⟩⟩
  · obtain ⟨ΔA, hΔ, hn⟩ := h.1
    refine ⟨(toEuclideanCLM (n := Fin n) (𝕜 := 𝕜)).symm (-ΔA), ?_, ?_⟩
    · rw [map_add, LinearMap.add_apply, ← coe_toEuclideanCLM_eq_toEuclideanLin,
        ← coe_toEuclideanCLM_eq_toEuclideanLin, StarAlgEquiv.apply_symm_apply]
      simpa [sub_eq_add_neg] using hΔ
    · rw [← l2_opNorm_toEuclideanCLM, StarAlgEquiv.apply_symm_apply, norm_neg, hn]
      rfl
  · rw [sub_neg_eq_add]
    rw [map_add, LinearMap.add_apply, ← coe_toEuclideanCLM_eq_toEuclideanLin,
      ← coe_toEuclideanCLM_eq_toEuclideanLin] at hE
    simpa using hE
  · rw [norm_neg, l2_opNorm_toEuclideanCLM, hεE]

end L2

/-! ### §7.3.2 Orthogonal iteration -/

/-- **(7.3.6), orthogonal iteration**, as a relation over any `RCLike` field (chapter 8's (8.2.8) is
the instance `𝕜 = ℝ`): `Q : ℕ → Matrix (Fin n) (Fin r) 𝕜` is an orthogonal iteration for `A` when
`Q₀` has orthonormal columns and each `Q_k` is the `Q`-factor of some thin QR factorization
`Q_k R_k = Z_k = A Q_{k-1}` (the backbone's `Matrix.IsOrthogonalIterationStep`). The eigenvalue
estimates are the spectrum of `Q_kᴴ A Q_k`. From every orthonormal `Q₀` with `r ≤ n` an orthogonal
iteration starts (`orthogonalIteration_exists`). -/
def orthogonalIteration {r : ℕ} (A : Matrix (Fin n) (Fin n) 𝕜)
    (Q : ℕ → Matrix (Fin n) (Fin r) 𝕜) : Prop :=
  (Q 0)ᴴ * Q 0 = 1 ∧ ∀ k, IsOrthogonalIterationStep A (Q k) (Q (k + 1))

/-- Orthogonal iteration can be run from every `Q₀` with orthonormal columns: each step has a thin
QR factorization, with no rank hypothesis. -/
theorem orthogonalIteration_exists {r : ℕ} (A : Matrix (Fin n) (Fin n) 𝕜)
    {Q₀ : Matrix (Fin n) (Fin r) 𝕜} (hQ₀ : Q₀ᴴ * Q₀ = 1) (hr : r ≤ n) :
    ∃ Q : ℕ → Matrix (Fin n) (Fin r) 𝕜, Q 0 = Q₀ ∧ orthogonalIteration A Q := by
  choose next hnext using fun Q : Matrix (Fin n) (Fin r) 𝕜 =>
    exists_isOrthogonalIterationStep A Q hr
  let Q : ℕ → Matrix (Fin n) (Fin r) 𝕜 := fun k => Nat.rec Q₀ (fun _ P => next P) k
  exact ⟨Q, rfl, hQ₀, fun k => hnext (Q k)⟩

/-- **§7.3.3, the QR iteration from orthogonal iteration**, over any `RCLike` field (chapter 8's
§8.2.5 is the instance `𝕜 = ℝ`): for an orthogonal iteration with `r = n` and
`T_k = Q_kᴴ A Q_k`, the triangular factor `R_{k+1}` of the step gives
`T_k = (Q_kᴴ Q_{k+1}) R_{k+1}` and `T_{k+1} = R_{k+1} (Q_kᴴ Q_{k+1})` with `Q_kᴴ Q_{k+1}` unitary —
"`T_k` is determined by computing the QR factorization of `T_{k-1}` and then multiplying the factors
together in reverse order", `Matrix.IsShiftedQrStep 0 T_k T_{k+1}`. -/
theorem orthogonalIteration_qr_step {A : Matrix (Fin n) (Fin n) 𝕜}
    {Q : ℕ → Matrix (Fin n) (Fin n) 𝕜} (hQ : orthogonalIteration A Q) (k : ℕ) :
    ∃ R : Matrix (Fin n) (Fin n) 𝕜, R.IsUpperTriangular ∧
      (Q k)ᴴ * Q (k + 1) ∈ unitaryGroup (Fin n) 𝕜 ∧
      (Q k)ᴴ * A * Q k = ((Q k)ᴴ * Q (k + 1)) * R ∧
      (Q (k + 1))ᴴ * A * Q (k + 1) = R * ((Q k)ᴴ * Q (k + 1)) ∧
      IsShiftedQrStep 0 ((Q k)ᴴ * A * Q k) ((Q (k + 1))ᴴ * A * Q (k + 1)) := by
  have hunit : ∀ j, Q j ∈ unitaryGroup (Fin n) 𝕜 := by
    intro j
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
    cases j with
    | zero => exact hQ.1
    | succ j => exact (hQ.2 j).choose_spec.conjTranspose_mul_self
  obtain ⟨R, hR⟩ := hQ.2 k
  have hQQ : Q k * (Q k)ᴴ = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.1 (hunit k)
  have hQQ' : (Q (k + 1))ᴴ * Q (k + 1) = 1 := hR.conjTranspose_mul_self
  have hA : A * Q k = Q (k + 1) * R := hR.mul_eq.symm
  have hmem : (Q k)ᴴ * Q (k + 1) ∈ unitaryGroup (Fin n) 𝕜 := by
    rw [← star_eq_conjTranspose]
    exact Submonoid.mul_mem _ (Unitary.star_mem (hunit k)) (hunit (k + 1))
  have h1 : (Q k)ᴴ * A * Q k = ((Q k)ᴴ * Q (k + 1)) * R := by
    rw [Matrix.mul_assoc, hA, Matrix.mul_assoc]
  have h2 : (Q (k + 1))ᴴ * A * Q (k + 1) = R * ((Q k)ᴴ * Q (k + 1)) := by
    have hA' : A = Q (k + 1) * R * (Q k)ᴴ := by
      rw [← hA, Matrix.mul_assoc, hQQ, Matrix.mul_one]
    rw [hA', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ', Matrix.one_mul, Matrix.mul_assoc]
  refine ⟨R, hR.isUpperTriangular, hmem, h1, h2, (Q k)ᴴ * Q (k + 1), hmem, R,
    hR.isUpperTriangular, ?_, ?_⟩
  · rw [zero_smul, sub_zero, h1]
  · rw [zero_smul, add_zero, h2]

/-- **§7.3.2, orthogonal iteration iterates subspaces and contains the power method.** For an
orthogonal iteration `Q` (7.3.6) with `A^k Q₀` of full column rank: `ran Q_k = A^k (ran Q₀)`
(`Krylov.subspaceIterate`); `A^k Q₀ = Q_k S` with `S` nonsingular upper triangular (the product
`R_k ⋯ R_1` of the triangular factors of the steps, the first display of the appendix proof); and
"the sequence `{Q_k e₁}` is precisely the sequence produced by the power iteration": the first
column of `Q_k` is the power method's `q^(k)` from `q₀ = Q₀ e₁`, up to a unimodular factor (the sign
or phase freedom of the QR factorizations). -/
theorem orthogonalIteration_range {r : ℕ} {A : Matrix (Fin n) (Fin n) 𝕜}
    {Q : ℕ → Matrix (Fin n) (Fin r) 𝕜} (hQ : orthogonalIteration A Q) {k : ℕ}
    (hk : LinearIndependent 𝕜 (A ^ k * Q 0)ᵀ) :
    LinearMap.range (toEuclideanLin (Q k)) =
        Krylov.subspaceIterate (toEuclideanLin A) (LinearMap.range (toEuclideanLin (Q 0))) k ∧
      (∃ S : Matrix (Fin r) (Fin r) 𝕜, IsUnit S ∧ S.IsUpperTriangular ∧ A ^ k * Q 0 = Q k * S) ∧
      ∀ h0 : 0 < r, ∃ c : 𝕜, ‖c‖ = 1 ∧
        (WithLp.toLp 2 ((Q k)ᵀ ⟨0, h0⟩) : EuclideanSpace 𝕜 (Fin n)) =
          c • (powerMethod A (WithLp.toLp 2 ((Q 0)ᵀ ⟨0, h0⟩)) k).1 := by
  obtain ⟨S, hS, hSt, hSeq⟩ := exists_pow_mul_eq_mul_of_isOrthogonalIterationStep hQ.2 hk
  refine ⟨range_eq_subspaceIterate_of_isOrthogonalIterationStep hQ.2 hk, ⟨S, hS, hSt, hSeq⟩,
    fun h0 => ?_⟩
  set j : Fin r := ⟨0, h0⟩
  have hortho : ∀ m, (Q m)ᴴ * Q m = 1 := fun m => by
    cases m with
    | zero => exact hQ.1
    | succ m => exact (hQ.2 m).choose_spec.conjTranspose_mul_self
  have hnorm : ∀ m, ‖(WithLp.toLp 2 ((Q m)ᵀ j) : EuclideanSpace 𝕜 (Fin n))‖ = 1 := fun m => by
    have h := norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one (hortho m)
      (WithLp.toLp 2 (Pi.single j 1))
    rwa [toEuclideanLin_toLp, mulVec_single_one, PiLp.toLp_single, PiLp.norm_single,
      norm_one] at h
  have hcol : A ^ k *ᵥ (Q 0)ᵀ j = S j j • (Q k)ᵀ j := by
    ext i
    have h2 : (Q k * S) i j = Q k i j * S j j := by
      rw [mul_apply, Finset.sum_eq_single j]
      · intro l _ hl
        rw [hSt (show j < l by
          rw [Fin.lt_def]
          exact Nat.pos_of_ne_zero fun h => hl (Fin.ext h)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    change (A ^ k * Q 0) i j = _
    rw [hSeq, h2, Pi.smul_apply, transpose_apply, smul_eq_mul, mul_comm]
  have hSjj : S j j ≠ 0 := by
    intro h
    apply hk.ne_zero j
    ext i
    have h' := congrFun hcol i
    rw [h, zero_smul] at h'
    exact h'
  have hn : (‖S j j‖ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hSjj)
  refine ⟨(S j j)⁻¹ * ‖S j j‖, ?_, ?_⟩
  · rw [norm_mul, norm_inv, RCLike.norm_ofReal, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hSjj)]
  · rw [powerMethod_fst A (hnorm 0) k, Krylov.powerIterate_eq_smul, ← toEuclideanLin_pow,
      toEuclideanLin_toLp, hcol, WithLp.toLp_smul, norm_smul, hnorm k, mul_one, smul_smul,
      smul_smul, show (S j j)⁻¹ * (‖S j j‖ : 𝕜) * (‖S j j‖ : 𝕜)⁻¹ * S j j = 1 by
        field_simp, one_smul]

end RCLike

/-! ### §7.3.4 LR iterations -/

/-- **(7.3.12)–(7.3.14), the LR iteration is treppeniteration.** Let `L₀` be unit lower triangular
and `T_k` the LR iterates: `T₀ = L₀⁻¹ A L₀`, `T_{k-1} = L_k R_k` an LU factorization,
`T_k = R_k L_k`. Then `G_k = L₀ L₁ ⋯ L_k` is unit lower triangular, `T_k = G_k⁻¹ A G_k` (7.3.13),
and `A G_k = G_{k+1} R_{k+1}` is an LU-type factorization of `A G_k` — the treppeniteration (7.3.12)
started from `G₀ = L₀`. (The book's "`G₀ ∈ ℂ^{n×r}` of rank `r`" with `r = n` and `L₀ = G₀` is read
with `G₀` unit lower triangular, which the identification needs.) -/
theorem equation_7_3_14 {A : Matrix (Fin n) (Fin n) ℂ} {L R T : ℕ → Matrix (Fin n) (Fin n) ℂ}
    (hL0 : (L 0).IsUnitLowerTriangular) (hT0 : T 0 = (L 0)⁻¹ * A * L 0)
    (hLU : ∀ k, IsLU (T k) (L (k + 1)) (R (k + 1)))
    (hRL : ∀ k, T (k + 1) = R (k + 1) * L (k + 1)) (k : ℕ) :
    ((List.range (k + 1)).map L).prod.IsUnitLowerTriangular ∧
      T k = ((List.range (k + 1)).map L).prod⁻¹ * A * ((List.range (k + 1)).map L).prod ∧
      A * ((List.range (k + 1)).map L).prod = ((List.range (k + 2)).map L).prod * R (k + 1) := by
  set G : ℕ → Matrix (Fin n) (Fin n) ℂ := fun j => ((List.range (j + 1)).map L).prod with hGdef
  have hG : ∀ j, G (j + 1) = G j * L (j + 1) := fun j => by
    simp only [G, List.range_succ (n := j + 1), List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton]
  have hG0 : G 0 = L 0 := by simp [G]
  have hGu : ∀ j, (G j).IsUnitLowerTriangular := by
    intro j
    induction j with
    | zero => rw [hG0]; exact hL0
    | succ j ih => rw [hG j]; exact ih.mul (hLU j).isUnitLowerTriangular
  have hdet : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.IsUnitLowerTriangular → IsUnit M.det :=
    fun M hM => (isUnit_iff_isUnit_det M).1 hM.isUnit
  have hT : ∀ j, T j = (G j)⁻¹ * A * G j := by
    intro j
    induction j with
    | zero => rw [hG0, hT0]
    | succ j ih =>
      have hR : R (j + 1) = (L (j + 1))⁻¹ * T j := by
        rw [← (hLU j).mul_eq, ← Matrix.mul_assoc,
          nonsing_inv_mul _ (hdet _ (hLU j).isUnitLowerTriangular), Matrix.one_mul]
      rw [hRL j, hR, ih, hG j, Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
  refine ⟨hGu k, hT k, ?_⟩
  change A * G k = G (k + 1) * R (k + 1)
  have hAG : A * G k = G k * T k := by
    rw [hT k, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (hdet _ (hGu k)),
      Matrix.one_mul]
  rw [hAG, ← (hLU k).mul_eq, hG k, Matrix.mul_assoc]

/-! ### The dominant invariant subspace -/

/-- The span of the leading Schur vectors when the diagonal blocks have disjoint spectra: if
`Qᴴ A Q = [T₁₁ T₁₂; 0 T₂₂]` with `Q` unitary and `λ(T₁₁) ∩ λ(T₂₂) = ∅`, then the first `p` columns
of `Q` span `⨆_{λ ∈ λ(T₁₁)} null((A - λI)^n)`, and every `A`-invariant subspace of dimension `p` on
which `A` has only eigenvalues from `λ(T₁₁)` equals it. Shared by §7.3.2 and §7.6.2. -/
theorem span_leading_schurVectors_eq {p q : ℕ} {A Q : Matrix (Fin (p + q)) (Fin (p + q)) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin (p + q)) ℂ) {T₁₁ : Matrix (Fin p) (Fin p) ℂ}
    {T₁₂ : Matrix (Fin p) (Fin q) ℂ} {T₂₂ : Matrix (Fin q) (Fin q) ℂ}
    (hT : (star Q * A * Q).reindex finSumFinEquiv.symm finSumFinEquiv.symm =
      fromBlocks T₁₁ T₁₂ 0 T₂₂)
    (hdisj : Disjoint (spectrum ℂ T₁₁) (spectrum ℂ T₂₂)) :
    Submodule.span ℂ (Set.range fun i : Fin p => Q.col (Fin.castAdd q i)) =
        ⨆ μ ∈ spectrum ℂ T₁₁, Module.End.maxGenEigenspace (toLin' A) μ ∧
      ∀ S ∈ Module.End.invtSubmodule (toLin' A), Module.finrank ℂ S = p →
        (∀ μ ∉ spectrum ℂ T₁₁, ∀ x ∈ S, A *ᵥ x = μ • x → x = 0) →
        S = Submodule.span ℂ (Set.range fun i : Fin p => Q.col (Fin.castAdd q i)) := by
  have hQu : IsUnit Q := (isUnit_iff_isUnit_det Q).2
    (isUnit_det_of_right_inverse (mem_unitaryGroup_iff.1 hQ))
  have hinv : Q⁻¹ = star Q := Matrix.inv_eq_left_inv (mem_unitaryGroup_iff'.1 hQ)
  have hspan := span_cols_eq_iSup_maxGenEigenspace_of_conj hQu finSumFinEquiv.symm
    (by rwa [hinv]) hdisj
  simp only [Equiv.symm_symm, finSumFinEquiv_apply_left] at hspan
  refine ⟨hspan, fun S hS hdim hΛ => ?_⟩
  have hli : LinearIndependent ℂ (fun i : Fin p => Q.col (Fin.castAdd q i)) :=
    (linearIndependent_cols_iff_isUnit.2 hQu).comp _ (Fin.castAdd_injective p q)
  have hfin : Module.finrank ℂ
      (Submodule.span ℂ (Set.range fun i : Fin p => Q.col (Fin.castAdd q i))) = p := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  rw [hspan]
  refine Module.End.invtSubmodule_eq_iSup_maxGenEigenspace hS
    (fun μ hμ x hx hAx => hΛ μ hμ x hx (by rwa [toLin'_apply] at hAx)) ?_
  rw [← hspan, hfin, hdim]

/-- **§7.3.2, the dominant invariant subspace.** With the Schur decomposition (7.3.7)–(7.3.8),
`Qᴴ A Q = [T₁₁ T₁₂; 0 T₂₂]`, and `|λ_r| > |λ_{r+1}|` (every eigenvalue of `T₁₁` exceeds every
eigenvalue of `T₂₂` in modulus), the dominant invariant subspace `D_r(A) = ran(Q_α)` spanned by the
first `r` Schur vectors "is the unique invariant subspace associated with the eigenvalues
`λ₁, …, λ_r`": it is `⨆_{λ ∈ λ(T₁₁)} null((A - λI)^n)`, and every `A`-invariant subspace of
dimension `r` on which `A` has only eigenvalues among `λ₁, …, λ_r` equals it. -/
theorem dominantInvariantSubspace_unique {r s : ℕ} {A Q : Matrix (Fin (r + s)) (Fin (r + s)) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin (r + s)) ℂ) {T₁₁ : Matrix (Fin r) (Fin r) ℂ}
    {T₁₂ : Matrix (Fin r) (Fin s) ℂ} {T₂₂ : Matrix (Fin s) (Fin s) ℂ}
    (hT : (star Q * A * Q).reindex finSumFinEquiv.symm finSumFinEquiv.symm =
      fromBlocks T₁₁ T₁₂ 0 T₂₂)
    (hdom : ∀ μ ∈ spectrum ℂ T₁₁, ∀ ν ∈ spectrum ℂ T₂₂, ‖ν‖ < ‖μ‖) :
    Submodule.span ℂ (Set.range fun i : Fin r => Q.col (Fin.castAdd s i)) =
        ⨆ μ ∈ spectrum ℂ T₁₁, Module.End.maxGenEigenspace (toLin' A) μ ∧
      ∀ S ∈ Module.End.invtSubmodule (toLin' A), Module.finrank ℂ S = r →
        (∀ μ ∉ spectrum ℂ T₁₁, ∀ x ∈ S, A *ᵥ x = μ • x → x = 0) →
        S = Submodule.span ℂ (Set.range fun i : Fin r => Q.col (Fin.castAdd s i)) :=
  span_leading_schurVectors_eq hQ hT
    (Set.disjoint_left.2 fun μ h₁ h₂ => lt_irrefl _ (hdom μ h₁ μ h₂))

/-! ### The appendix: Lemma 7.3.2 and the displays of the proof of Theorem 7.3.1 -/

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Lemma 7.3.2.** Let `Qᴴ A Q = T = D + N` be a Schur decomposition (`T` upper triangular with
diagonal `D`, `N` its strictly upper triangular part), `|λ_max| = max_i |t_ii|` and
`|λ_min| = min_i |t_ii|` the extreme moduli of the eigenvalues, and `μ ≥ 0`. Then
(7.3.15) `‖A^k‖₂ ≤ (1 + μ)^{n-1} (|λ_max| + ‖N‖_F/(1 + μ))^k` for all `k`, and (7.3.16) if
`(1 + μ)|λ_min| > ‖N‖_F` then `‖A^{-k}‖₂ ≤ (1 + μ)^{n-1} (1/(|λ_min| - ‖N‖_F/(1 + μ)))^k`. (The
book's last display writes `|μ|` for `|λ_min|`.) -/
theorem lemma_7_3_2 {A Q T : Matrix (Fin n) (Fin n) ℂ} (hQ : Q ∈ unitaryGroup (Fin n) ℂ)
    (hT : star Q * A * Q = T) (hTu : T.IsUpperTriangular) {μ : ℝ} (hμ : 0 ≤ μ) :
    (∀ k : ℕ, lpOpNorm 2 (A ^ k) ≤
      (1 + μ) ^ (n - 1) * ((⨆ i, ‖T i i‖) + ‖strictUpper T‖ / (1 + μ)) ^ k) ∧
    (‖strictUpper T‖ < (1 + μ) * (⨅ i, ‖T i i‖) → ∀ k : ℕ, lpOpNorm 2 (A⁻¹ ^ k) ≤
      (1 + μ) ^ (n - 1) * (1 / ((⨅ i, ‖T i i‖) - ‖strictUpper T‖ / (1 + μ))) ^ k) :=
  ⟨l2_opNorm_pow_le_of_schur hQ hT hTu hμ, fun hm => l2_opNorm_inv_pow_le_of_schur hQ hT hTu hμ hm⟩

/-- **(7.3.20).** If `λ(T₁₁) ∩ λ(T₂₂) = ∅`, the Sylvester equation `T₁₁ X - X T₂₂ = -T₁₂` has a
solution (Lemma 7.1.5), and `‖X‖_F ≤ ‖T₁₂‖_F / sep(T₁₁, T₂₂)`. -/
theorem equation_7_3_20 {p q : ℕ} [NeZero p] [NeZero q] {T₁₁ : Matrix (Fin p) (Fin p) ℂ}
    {T₂₂ : Matrix (Fin q) (Fin q) ℂ} (T₁₂ : Matrix (Fin p) (Fin q) ℂ)
    (h : spectrum ℂ T₁₁ ∩ spectrum ℂ T₂₂ = ∅) :
    ∃ X : Matrix (Fin p) (Fin q) ℂ, T₁₁ * X - X * T₂₂ = -T₁₂ ∧ ‖X‖ ≤ ‖T₁₂‖ / sep T₁₁ T₂₂ := by
  have hdisj : Disjoint (spectrum ℂ T₁₁) (spectrum ℂ T₂₂) := Set.disjoint_iff_inter_eq_empty.2 h
  obtain ⟨X, hX, -⟩ := existsUnique_sylvesterMap_eq hdisj (-T₁₂)
  refine ⟨X, hX, ?_⟩
  have hsep : 0 < sep T₁₁ T₂₂ := (sep_pos_iff_disjoint_spectrum).2 hdisj
  have h1 := frobenius_norm_le_div_sep hsep X
  rwa [hX, norm_neg] at h1

end Frobenius

/-- **(7.3.25) and the complementary invariant subspace.** With `X` from (7.3.20),
`T₁₁ X - X T₂₂ = -T₁₂`, the Schur coordinates `T = [T₁₁ T₁₂; 0 T₂₂]` satisfy
`T [X; I] = [X; I] T₂₂` — the columns of `Q [X; I] = Q_α X + Q_β` span the complementary invariant
subspace of `A` — and `Tᴴ [I; -Xᴴ] = [I; -Xᴴ] T₁₁ᴴ`, i.e. `Aᴴ (Q_α - Q_β Xᴴ) = (Q_α - Q_β Xᴴ) T₁₁ᴴ`:
the columns of `Q_α - Q_β Xᴴ` (orthonormalized by `G^{-H}` in the book) span the dominant invariant
subspace `D_r(Aᴴ)` of `Aᴴ`. -/
theorem equation_7_3_25 {p q : ℕ} {A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ}
    {Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hQ : Q ∈ unitaryGroup (Fin p ⊕ Fin q) ℂ)
    {T₁₁ : Matrix (Fin p) (Fin p) ℂ} {T₁₂ : Matrix (Fin p) (Fin q) ℂ}
    {T₂₂ : Matrix (Fin q) (Fin q) ℂ} (hT : star Q * A * Q = fromBlocks T₁₁ T₁₂ 0 T₂₂)
    {X : Matrix (Fin p) (Fin q) ℂ} (hX : T₁₁ * X - X * T₂₂ = -T₁₂) :
    fromBlocks T₁₁ T₁₂ 0 T₂₂ * fromRows X 1 = fromRows X 1 * T₂₂ ∧
      (fromBlocks T₁₁ T₁₂ 0 T₂₂)ᴴ * fromRows 1 (-Xᴴ) = fromRows 1 (-Xᴴ) * T₁₁ᴴ ∧
      (A * (Q * fromRows X 1) : Matrix (Fin p ⊕ Fin q) (Fin q) ℂ) =
        (Q * fromRows X 1 * T₂₂ : Matrix (Fin p ⊕ Fin q) (Fin q) ℂ) ∧
      (Aᴴ * (Q * fromRows 1 (-Xᴴ)) : Matrix (Fin p ⊕ Fin q) (Fin p) ℂ) =
        (Q * fromRows 1 (-Xᴴ) * T₁₁ᴴ : Matrix (Fin p ⊕ Fin q) (Fin p) ℂ) := by
  have h1 : fromBlocks T₁₁ T₁₂ 0 T₂₂ * fromRows X 1 = fromRows X 1 * T₂₂ := by
    simp only [fromBlocks_mul_fromRows, fromRows_mul, Matrix.zero_mul, zero_add, Matrix.mul_one,
      Matrix.one_mul]
    refine congrArg₂ fromRows ?_ rfl
    have e : T₁₂ = -(T₁₁ * X - X * T₂₂) := by rw [hX, neg_neg]
    rw [e]
    abel
  have h2 : (fromBlocks T₁₁ T₁₂ 0 T₂₂)ᴴ * fromRows 1 (-Xᴴ) = fromRows 1 (-Xᴴ) * T₁₁ᴴ := by
    have hXh := congrArg conjTranspose hX
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, conjTranspose_neg] at hXh
    simp only [fromBlocks_conjTranspose, fromBlocks_mul_fromRows, fromRows_mul, conjTranspose_zero,
      Matrix.zero_mul, neg_zero, add_zero, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
      Matrix.neg_mul]
    refine congrArg₂ fromRows rfl ?_
    have e : T₁₂ᴴ = -(Xᴴ * T₁₁ᴴ - T₂₂ᴴ * Xᴴ) := by rw [hXh, neg_neg]
    rw [e]
    abel
  have hQQ' : star Q * Q = 1 := mem_unitaryGroup_iff'.1 hQ
  have hQQ : Q * star Q = 1 := mem_unitaryGroup_iff.1 hQ
  have hA : A = Q * fromBlocks T₁₁ T₁₂ 0 T₂₂ * star Q := by
    rw [← hT, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ, Matrix.one_mul, Matrix.mul_assoc,
      hQQ, Matrix.mul_one]
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [hA]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star Q) Q, hQQ', Matrix.one_mul, h1]
  · have hQh : Qᴴ * Q = 1 := by rw [← star_eq_conjTranspose]; exact hQQ'
    rw [hA, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Qᴴ Q, hQh, Matrix.one_mul, h2]

open scoped ComplexOrder in
/-- **(7.3.23)–(7.3.24).** For any `X`, `I + X Xᴴ` is Hermitian positive definite, and any `G` with
`G Gᴴ = I + X Xᴴ` (for instance its Cholesky factor) has `σ_min(G) ≥ 1`: `‖Gᴴ v‖² = ‖v‖² + ‖Xᴴ v‖²`
bounds `Gᴴ` from below, hence `(Gᴴ)⁻¹` from above, and
`‖x‖² = ⟪(Gᴴ)⁻¹ x, G x⟫ ≤ ‖x‖ ‖G x‖`. -/
theorem equation_7_3_24 [NeZero n] {m : ℕ} (X : Matrix (Fin n) (Fin m) ℂ)
    {G : Matrix (Fin n) (Fin n) ℂ} (hG : G * Gᴴ = 1 + X * Xᴴ) :
    (1 + X * Xᴴ).PosDef ∧ 1 ≤ ⨅ i, G.singularValues i := by
  refine ⟨Matrix.PosDef.one.add_posSemidef (posSemidef_self_mul_conjTranspose X), ?_⟩
  -- `Gᴴ` is bounded below: `‖Gᴴ v‖² = ‖v‖² + ‖Xᴴ v‖²`
  have hlow : ∀ v : EuclideanSpace ℂ (Fin n), ‖v‖ ≤ ‖toEuclideanLin Gᴴ v‖ := by
    intro v
    have h1 : ‖toEuclideanLin Gᴴ v‖ ^ 2 = ‖v‖ ^ 2 + ‖toEuclideanLin Xᴴ v‖ ^ 2 := by
      have e1 : (inner ℂ (toEuclideanLin Gᴴ v) (toEuclideanLin Gᴴ v) : ℂ) =
          inner ℂ v (toEuclideanLin (G * Gᴴ) v) := by
        rw [toEuclideanLin_mul_apply, toEuclideanLin_conjTranspose G,
          LinearMap.adjoint_inner_left]
      have e2 : (inner ℂ v (toEuclideanLin (X * Xᴴ) v) : ℂ) =
          inner ℂ (toEuclideanLin Xᴴ v) (toEuclideanLin Xᴴ v) := by
        rw [toEuclideanLin_mul_apply, toEuclideanLin_conjTranspose X,
          LinearMap.adjoint_inner_left]
      rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, e1, hG,
        map_add, LinearMap.add_apply, toLpLin_one, LinearMap.id_apply, inner_add_right, e2,
        map_add]
    have h2 : ‖v‖ ^ 2 ≤ ‖toEuclideanLin Gᴴ v‖ ^ 2 := by
      rw [h1]; exact le_add_of_nonneg_right (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  -- hence `Gᴴ` is invertible
  have hGu : IsUnit Gᴴ := by
    rw [← mulVec_injective_iff_isUnit]
    intro a b hab
    have h := hlow (WithLp.toLp 2 (a - b))
    rw [toLpLin_toLp, toLin'_apply, mulVec_sub, hab, sub_self, WithLp.toLp_zero, norm_zero,
      norm_le_zero_iff, WithLp.toLp_eq_zero] at h
    exact sub_eq_zero.1 h
  -- and `G` is bounded below: `‖x‖² = ⟪(Gᴴ)⁻¹ x, G x⟫`
  have hGx : ∀ x : EuclideanSpace ℂ (Fin n), ‖x‖ ≤ ‖toEuclideanLin G x‖ := by
    intro x
    set y := toEuclideanLin (Gᴴ)⁻¹ x
    have hy : toEuclideanLin Gᴴ y = x := by
      rw [← toEuclideanLin_mul_apply, Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hGu),
        toLpLin_one, LinearMap.id_apply]
    have hyx : ‖y‖ ≤ ‖x‖ := hy ▸ hlow y
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    have h3 : ‖x‖ ^ 2 ≤ ‖x‖ * ‖toEuclideanLin G x‖ := by
      calc ‖x‖ ^ 2 = RCLike.re (inner ℂ (toEuclideanLin Gᴴ y) x) := by
            rw [hy, @norm_sq_eq_re_inner ℂ]
        _ = RCLike.re (inner ℂ y (toEuclideanLin G x)) := by
            rw [toEuclideanLin_conjTranspose, LinearMap.adjoint_inner_left]
        _ ≤ ‖y‖ * ‖toEuclideanLin G x‖ := (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
        _ ≤ ‖x‖ * ‖toEuclideanLin G x‖ := by gcongr
    nlinarith
  rw [iInf_singularValues_eq_iInf_norm]
  have : Nonempty {x : EuclideanSpace ℂ (Fin n) // ‖x‖ = 1} :=
    ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩
  refine le_ciInf fun x => ?_
  have h := hGx x
  rwa [x.2] at h


/-! ### The rates of §7.3.1–7.3.2 and the appendix displays (7.3.18), (7.3.19), (7.3.26) -/

section Lines

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **The gap between two lines is the sine of their angle**: for unit vectors `q`, `u`,
`dist(span{q}, span{u}) = sin θ(q, span{u}) = ‖q - ⟪u, q⟫ u‖`. The two lines have the same
dimension, so the gap is the one-sided `‖P_{u⊥} P_q‖`
(`Submodule.gap_eq_norm_orthogonal_mul_of_finrank_eq`), and `P_{u⊥} P_q w = ⟪q, w⟫ P_{u⊥} q`. -/
private theorem gap_span_singleton_eq_sinAngle {q u : E} (hq : ‖q‖ = 1) (hu : ‖u‖ = 1) :
    (𝕜 ∙ q).gap (𝕜 ∙ u) = (𝕜 ∙ u).sinAngle q := by
  have hq0 : q ≠ 0 := norm_ne_zero_iff.1 (by rw [hq]; exact one_ne_zero)
  have hu0 : u ≠ 0 := norm_ne_zero_iff.1 (by rw [hu]; exact one_ne_zero)
  rw [Submodule.gap_eq_norm_orthogonal_mul_of_finrank_eq _ _
    ((finrank_span_singleton hq0).trans (finrank_span_singleton hu0).symm),
    Submodule.sinAngle, hq, div_one]
  have hT : ∀ w, ((𝕜 ∙ u)ᗮ.starProjection * (𝕜 ∙ q).starProjection) w =
      (inner 𝕜 q w : 𝕜) • (q - (𝕜 ∙ u).starProjection q) := by
    intro w
    change (𝕜 ∙ u)ᗮ.starProjection ((𝕜 ∙ q).starProjection w) = _
    rw [Submodule.starProjection_singleton, hq, one_pow, RCLike.ofReal_one, div_one, map_smul,
      Submodule.starProjection_orthogonal_val]
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w => ?_) ?_
  · rw [hT, norm_smul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    simpa [hq] using norm_inner_le_norm (𝕜 := 𝕜) q w
  · have h := ((𝕜 ∙ u)ᗮ.starProjection * (𝕜 ∙ q).starProjection).le_opNorm q
    rwa [hT, inner_self_eq_norm_sq_to_K, hq, RCLike.ofReal_one, one_pow, one_smul,
      mul_one] at h

end Lines

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **§7.3.1**: "`dist(span{q^(k)}, span{x₁}) = O(|λ₂/λ₁|^k)`", rigorous. With unit eigenvectors
`x_i` of `A` (`A x_i = λ_i x_i`), `λ_{i₀}` dominant (`|λ_i| ≤ ρ < |λ_{i₀}|` for `i ≠ i₀`, the book's
`ρ = |λ₂|`) and a unit `q^(0) = ∑ a_i x_i` with `a_{i₀} ≠ 0` (7.3.4), there is `C` with
`dist(span{q^(k)}, span{x_{i₀}}) ≤ C (ρ / |λ_{i₀}|)^k` for all `k`, the distance being the gap.
For lines the gap is the sine of the angle, which the backbone bounds. -/
theorem powerMethod_dist {A : Matrix (Fin n) (Fin n) 𝕜} {x : Fin n → EuclideanSpace 𝕜 (Fin n)}
    {l : Fin n → 𝕜} (hx : ∀ i, toEuclideanLin A (x i) = l i • x i) (hx1 : ∀ i, ‖x i‖ = 1)
    {i₀ : Fin n} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ∀ i, i ≠ i₀ → ‖l i‖ ≤ ρ) (hdom : ρ < ‖l i₀‖)
    {a : Fin n → 𝕜} (ha : a i₀ ≠ 0) {q₀ : EuclideanSpace 𝕜 (Fin n)} (hq₀ : ‖q₀‖ = 1)
    (hq : q₀ = ∑ i, a i • x i) :
    ∃ C : ℝ, ∀ k, (𝕜 ∙ (powerMethod A q₀ k).1).gap (𝕜 ∙ x i₀) ≤ C * (ρ / ‖l i₀‖) ^ k := by
  have hl₀ : l i₀ ≠ 0 := norm_pos_iff.1 (hρ0.trans_lt hdom)
  obtain ⟨C, hC⟩ := Krylov.exists_norm_sub_smul_powerIterate_le_of_eigenbasis hx hx1 hl₀ hρ ha hq
  refine ⟨C, fun k => ?_⟩
  rw [powerMethod_fst A hq₀ k]
  rcases eq_or_ne ((toEuclideanLin A ^ k) q₀) 0 with h0 | h0
  · have hz := (Krylov.powerIterate_eq_zero_iff (toEuclideanLin A) q₀ k).2 h0
    have h := (hC k).1
    rw [hz, smul_zero, zero_sub, norm_neg, hx1] at h
    have hne : (𝕜 ∙ x i₀) ≠ ⊥ := fun h' =>
      (norm_ne_zero_iff.1 (by rw [hx1]; exact one_ne_zero)) ((Submodule.span_singleton_eq_bot).1 h')
    rw [hz, Submodule.gap_comm, Submodule.gap_congr _ _ (Submodule.span_zero_singleton 𝕜),
      Submodule.gap_comm, Submodule.gap_bot_eq_one _ hne]
    exact h
  · rw [gap_span_singleton_eq_sinAngle
      (Krylov.norm_powerIterate_of_ne_zero (toEuclideanLin A) q₀ k h0) (hx1 i₀)]
    exact (hC k).2

end RCLike

section Blocks

variable {r s : ℕ}

/-- The column blocks of a unitary `Q = [Q_α Q_β]`: orthonormal columns, mutually orthogonal. -/
private theorem conjTranspose_mul_fromCols_eq {Qα : Matrix (Fin n) (Fin r) ℂ}
    {Qβ : Matrix (Fin n) (Fin s) ℂ} (hQ : (fromCols Qα Qβ)ᴴ * fromCols Qα Qβ = 1) :
    Qαᴴ * Qα = 1 ∧ Qβᴴ * Qβ = 1 ∧ Qαᴴ * Qβ = 0 := by
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols,
    ← fromBlocks_one] at hQ
  obtain ⟨h1, h2, -, h4⟩ := fromBlocks_inj.1 hQ
  exact ⟨h1, h4, h2⟩

/-- For `Q = [Q_α Q_β]` unitary, `ran Q_β = (ran Q_α)ᗮ`. -/
private theorem range_eq_orthogonal_of_fromCols {Qα : Matrix (Fin n) (Fin r) ℂ}
    {Qβ : Matrix (Fin n) (Fin s) ℂ} (hQ : (fromCols Qα Qβ)ᴴ * fromCols Qα Qβ = 1)
    (hQ' : fromCols Qα Qβ * (fromCols Qα Qβ)ᴴ = 1) :
    LinearMap.range (toEuclideanLin Qβ) = (LinearMap.range (toEuclideanLin Qα))ᗮ := by
  obtain ⟨-, -, hαβ⟩ := conjTranspose_mul_fromCols_eq hQ
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows] at hQ'
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨z, rfl⟩
    rw [← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint,
      ← toEuclideanLin_mul_apply, hαβ, map_zero, LinearMap.zero_apply, inner_zero_right]
  · intro x hx
    have h0 : toEuclideanLin Qαᴴ x = 0 := by
      rw [toEuclideanLin_conjTranspose_eq_adjoint]
      refine ext_inner_left ℂ fun z => ?_
      rw [LinearMap.adjoint_inner_right, inner_zero_right]
      exact (Submodule.mem_orthogonal _ _).1 hx _ ⟨z, rfl⟩
    refine ⟨toEuclideanLin Qβᴴ x, ?_⟩
    have h := congrArg (fun M => toEuclideanLin M x) hQ'
    simp only [map_add, LinearMap.add_apply, toEuclideanLin_mul_apply, h0, map_zero, zero_add,
      toLpLin_one, LinearMap.id_apply] at h
    exact h

open scoped Matrix.Norms.L2Operator

/-- **(7.3.18)**: with `Q = [Q_α Q_β]` unitary (the Schur vectors, `D_r(A) = ran Q_α`) and `Q_k`
with orthonormal columns, `dist(D_r(A), ran Q_k) = ‖W_k‖₂` for `W_k = Q_βᴴ Q_k` — chapter 2's
characterization of the distance of two equal-dimensional subspaces (Theorem 2.5.1). -/
theorem equation_7_3_18 {Qα : Matrix (Fin n) (Fin r) ℂ} {Qβ : Matrix (Fin n) (Fin s) ℂ}
    (hQ : (fromCols Qα Qβ)ᴴ * fromCols Qα Qβ = 1) (hQ' : fromCols Qα Qβ * (fromCols Qα Qβ)ᴴ = 1)
    {Qk : Matrix (Fin n) (Fin r) ℂ} (hQk : Qkᴴ * Qk = 1) :
    (LinearMap.range (toEuclideanLin Qα)).gap (LinearMap.range (toEuclideanLin Qk)) =
      ‖Qβᴴ * Qk‖ := by
  obtain ⟨hα, hβ, -⟩ := conjTranspose_mul_fromCols_eq hQ
  rw [Submodule.gap_comm, gap_range_eq_l2_opNorm_conjTranspose_mul hQk hα hβ
    (range_eq_orthogonal_of_fromCols hQ hQ'), ← l2_opNorm_conjTranspose, conjTranspose_mul,
    conjTranspose_conjTranspose]

/-- **(7.3.19)**: for `Q_α`, `Q_k` with `r ≥ 1` orthonormal columns and `V_k = Q_αᴴ Q_k`,
`1 = d_k² + σ_min(V_k)²` with `d_k = dist(ran Q_α, ran Q_k)` — the thin CS decomposition read for
two subspaces (`σ_min = ⨅ i, σ_i`). -/
theorem equation_7_3_19 [NeZero r] {Qα Qk : Matrix (Fin n) (Fin r) ℂ} (hα : Qαᴴ * Qα = 1)
    (hQk : Qkᴴ * Qk = 1) :
    1 = (LinearMap.range (toEuclideanLin Qα)).gap (LinearMap.range (toEuclideanLin Qk)) ^ 2 +
      (⨅ i, (Qαᴴ * Qk).singularValues i) ^ 2 := by
  have : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩⟩
  rw [← sortedSingularValues_eq_iInf_singularValues, Fintype.card_fin]
  have h := gap_range_sq_add_sortedSingularValues_sq hα hQk
  rw [Fintype.card_fin] at h
  exact h.symm

/-- A square matrix with a positive least singular value is invertible. -/
private theorem isUnit_of_iInf_singularValues_pos [NeZero r] {B : Matrix (Fin r) (Fin r) ℂ}
    (h : 0 < ⨅ i, B.singularValues i) : IsUnit B := by
  have : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩⟩
  rw [← mulVec_injective_iff_isUnit]
  intro v w hvw
  have h1 := B.iInf_singularValues_mul_norm_le (WithLp.toLp 2 (v - w))
  rw [toEuclideanLin_toLp, mulVec_sub, hvw, sub_self, WithLp.toLp_zero, norm_zero] at h1
  have h2 : ‖(WithLp.toLp 2 (v - w) : EuclideanSpace ℂ (Fin r))‖ = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right h1 h) (norm_nonneg _)
  have h3 := congrArg WithLp.ofLp (norm_eq_zero.1 h2)
  simpa [sub_eq_zero] using h3

open scoped ComplexOrder in
/-- **(7.3.26), corrected.** Let `Q = [Q_α Q_β]` be unitary, `X` any `r × (n - r)` matrix,
`I + X Xᴴ = G Gᴴ` (7.3.23), and `Z = (Q_α - Q_β Xᴴ) G^{-H}`, whose columns are an orthonormal basis
of `ran(Q_α - Q_β Xᴴ)` — the dominant invariant subspace `D_r(Aᴴ)` when `X` solves the Sylvester
equation (7.3.20), by (7.3.25). For `Q₀` with orthonormal columns, `V₀ = Q_αᴴ Q₀`,
`W₀ = Q_βᴴ Q₀` and `d̃₀ = dist(D_r(Aᴴ), ran Q₀) < 1`: `V₀ - X W₀ = G (Zᴴ Q₀)` is nonsingular and
`‖(V₀ - X W₀)⁻¹‖₂ ≤ ‖G⁻¹‖₂ ‖(Zᴴ Q₀)⁻¹‖₂ ≤ 1/√(1 - d̃₀²)`. The book ends the chain with `d₀`, through
the claim `ran(Q_β) = D_r(Aᴴ)^⊥`, which is false unless `T₁₂ = 0` — the source of the error in
Theorem 7.3.1. -/
theorem equation_7_3_26 [NeZero r] {Qα : Matrix (Fin n) (Fin r) ℂ} {Qβ : Matrix (Fin n) (Fin s) ℂ}
    (hQ : (fromCols Qα Qβ)ᴴ * fromCols Qα Qβ = 1) {X : Matrix (Fin r) (Fin s) ℂ}
    {G : Matrix (Fin r) (Fin r) ℂ} (hG : G * Gᴴ = 1 + X * Xᴴ) {Z : Matrix (Fin n) (Fin r) ℂ}
    (hZ : Z = (Qα - Qβ * Xᴴ) * (Gᴴ)⁻¹) {Q₀ : Matrix (Fin n) (Fin r) ℂ} (hQ₀ : Q₀ᴴ * Q₀ = 1)
    (hd : (LinearMap.range (toEuclideanLin Z)).gap (LinearMap.range (toEuclideanLin Q₀)) < 1) :
    Zᴴ * Z = 1 ∧ Qαᴴ * Q₀ - X * (Qβᴴ * Q₀) = G * (Zᴴ * Q₀) ∧
      IsUnit (Qαᴴ * Q₀ - X * (Qβᴴ * Q₀)) ∧
      ‖(Qαᴴ * Q₀ - X * (Qβᴴ * Q₀))⁻¹‖ ≤ ‖G⁻¹‖ * ‖(Zᴴ * Q₀)⁻¹‖ ∧
      ‖G⁻¹‖ * ‖(Zᴴ * Q₀)⁻¹‖ ≤ 1 / Real.sqrt (1 -
        (LinearMap.range (toEuclideanLin Z)).gap (LinearMap.range (toEuclideanLin Q₀)) ^ 2) := by
  obtain ⟨hα, hβ, hαβ⟩ := conjTranspose_mul_fromCols_eq hQ
  have hβα : Qβᴴ * Qα = 0 := by
    rw [← conjTranspose_conjTranspose Qα, ← conjTranspose_mul, hαβ, conjTranspose_zero]
  obtain ⟨hpd, hσG⟩ := equation_7_3_24 X hG
  have hGu : IsUnit G.det := by
    have h := hpd.isUnit
    rw [← hG, isUnit_iff_isUnit_det, det_mul, det_conjTranspose] at h
    exact isUnit_of_mul_isUnit_left h
  have hGhu : IsUnit Gᴴ.det := by rw [det_conjTranspose]; exact hGu.star
  set Y := Qα - Qβ * Xᴴ with hY
  have hYY : Yᴴ * Y = 1 + X * Xᴴ := by
    rw [hY, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_sub, hα, Matrix.mul_assoc X, hβα, Matrix.mul_zero,
      ← Matrix.mul_assoc, hαβ, Matrix.zero_mul, Matrix.mul_assoc X, ← Matrix.mul_assoc Qβᴴ, hβ,
      Matrix.one_mul]
    abel
  have hZG : Z * Gᴴ = Y := by
    rw [hZ, Matrix.mul_assoc, nonsing_inv_mul _ hGhu, Matrix.mul_one]
  have hZZ : Zᴴ * Z = 1 := by
    have hGi : ((Gᴴ)⁻¹)ᴴ = G⁻¹ := by rw [conjTranspose_nonsing_inv, conjTranspose_conjTranspose]
    rw [hZ, conjTranspose_mul, hGi, Matrix.mul_assoc, ← Matrix.mul_assoc Yᴴ, hYY, ← hG,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hGu, Matrix.one_mul,
      mul_nonsing_inv _ hGhu]
  have hV : Qαᴴ * Q₀ - X * (Qβᴴ * Q₀) = G * (Zᴴ * Q₀) := by
    have h1 : G * Zᴴ = Yᴴ := by
      rw [← hZG, conjTranspose_mul, conjTranspose_conjTranspose]
    calc Qαᴴ * Q₀ - X * (Qβᴴ * Q₀) = Yᴴ * Q₀ := by
          rw [hY, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose,
            Matrix.sub_mul, Matrix.mul_assoc]
      _ = G * (Zᴴ * Q₀) := by rw [← h1, Matrix.mul_assoc]
  -- the least singular value of `Zᴴ Q₀`
  set d := (LinearMap.range (toEuclideanLin Z)).gap (LinearMap.range (toEuclideanLin Q₀))
  have hd0 : 0 ≤ d := Submodule.gap_nonneg _ _
  have hσ := equation_7_3_19 hZZ hQ₀
  have hσ0 : 0 ≤ ⨅ i, (Zᴴ * Q₀).singularValues i := le_ciInf fun i => singularValues_nonneg _ i
  have hσeq : ⨅ i, (Zᴴ * Q₀).singularValues i = Real.sqrt (1 - d ^ 2) := by
    rw [← Real.sqrt_sq hσ0]
    congr 1
    linarith
  have hσpos : 0 < ⨅ i, (Zᴴ * Q₀).singularValues i := by
    rw [hσeq]
    exact Real.sqrt_pos.2 (by nlinarith)
  have hZQu : IsUnit (Zᴴ * Q₀) := isUnit_of_iInf_singularValues_pos hσpos
  have hZQd : IsUnit (Zᴴ * Q₀).det := (isUnit_iff_isUnit_det _).1 hZQu
  have hunit : IsUnit (Qαᴴ * Q₀ - X * (Qβᴴ * Q₀)) := by
    rw [hV]; exact ((isUnit_iff_isUnit_det G).2 hGu).mul hZQu
  refine ⟨hZZ, hV, hunit, ?_, ?_⟩
  · rw [hV, Matrix.mul_inv_rev]
    refine (norm_mul_le _ _).trans (le_of_eq (mul_comm _ _))
  · have hG1 : ‖G⁻¹‖ ≤ 1 := by
      rw [l2_opNorm_inv_eq_inv_iInf_singularValues _ hGu]
      exact inv_le_one_of_one_le₀ hσG
    rw [l2_opNorm_inv_eq_inv_iInf_singularValues _ hZQd, hσeq, one_div]
    calc ‖G⁻¹‖ * (Real.sqrt (1 - d ^ 2))⁻¹ ≤ 1 * (Real.sqrt (1 - d ^ 2))⁻¹ :=
          mul_le_mul_of_nonneg_right hG1 (inv_nonneg.2 (Real.sqrt_nonneg _))
      _ = (Real.sqrt (1 - d ^ 2))⁻¹ := one_mul _

end Blocks

/-- The norm of a vector of `ℂ²`. -/
private theorem norm_euclidean_two (v : EuclideanSpace ℂ (Fin 2)) :
    ‖v‖ = Real.sqrt (‖v 0‖ ^ 2 + ‖v 1‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- `(√2)⁻¹ · (√2)⁻¹ = 1/2`. -/
private theorem inv_sqrt_two_mul_self : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_div]

/-- The column space of a one-column matrix is the line through its column. -/
private theorem range_toEuclideanLin_col {m : ℕ} (M : Matrix (Fin m) (Fin 1) ℂ) :
    LinearMap.range (toEuclideanLin M) = ℂ ∙ WithLp.toLp 2 (fun i => M i 0) := by
  have happ : ∀ y : EuclideanSpace ℂ (Fin 1),
      toEuclideanLin M y = y 0 • WithLp.toLp 2 (fun i => M i 0) := by
    intro y
    ext i
    simp [toEuclideanLin_apply, mulVec, dotProduct, mul_comm]
  ext x
  rw [LinearMap.mem_range, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y 0, (happ y).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨EuclideanSpace.single 0 a, ?_⟩
    rw [happ]
    simp

open scoped Matrix.Norms.Frobenius in
/-- **Theorem 7.3.1 as printed is false.** For `A = [2 1; 0 1]` (a Schur form with `Q = I`, `r = 1`,
`D₁(A) = span{e₁}`, `N = [0 1; 0 0]`, `‖N‖_F = 1`, `sep(2, 1) = 1`), `μ = 3` (so
`(1 + μ)|λ₁| = 8 > ‖N‖_F`) and `Q₀ = (1, -1)ᵀ/√2`, every orthogonal iteration (7.3.6) from `Q₀` has
`ran Q_k = ran Q₀` (`A Q₀ = Q₀`), so `d_k = dist(D₁(A), ran Q_k) = 1/√2 < 1` for every `k` — the
printed hypothesis (7.3.9) holds — while the printed right-hand side of (7.3.10),
`(1 + 1/1) ((1 + 1/4)/(2 - 1/4))^k d₀/√(1 - d₀²)`, tends to `0`. The hypothesis the proof really
uses fails: `D₁(Aᴴ) = span{(1, 1)}` (`Aᴴ (1, 1) = 2 (1, 1)`) is orthogonal to `ran Q₀`, so
`d̃₀ = dist(D₁(Aᴴ), ran Q₀) = 1`. -/
theorem theorem_7_3_1_counterexample {Q : ℕ → Matrix (Fin 2) (Fin 1) ℂ}
    (hQ : orthogonalIteration !![(2 : ℂ), 1; 0, 1] Q)
    (h0 : Q 0 = !![(((Real.sqrt 2)⁻¹ : ℝ) : ℂ); -(((Real.sqrt 2)⁻¹ : ℝ) : ℂ)]) :
    ‖strictUpper !![(2 : ℂ), 1; 0, 1]‖ = 1 ∧
      (∀ k, (ℂ ∙ EuclideanSpace.single (0 : Fin 2) (1 : ℂ)).gap
        (LinearMap.range (toEuclideanLin (Q k))) = (Real.sqrt 2)⁻¹) ∧
      Tendsto (fun k : ℕ => (1 + 3 : ℝ) ^ (2 - 2) *
          (1 + ‖!![(1 : ℂ)]‖ / sep !![(2 : ℂ)] !![(1 : ℂ)]) *
          ((‖(1 : ℂ)‖ + ‖strictUpper !![(2 : ℂ), 1; 0, 1]‖ / (1 + 3)) /
            (‖(2 : ℂ)‖ - ‖strictUpper !![(2 : ℂ), 1; 0, 1]‖ / (1 + 3))) ^ k *
          ((ℂ ∙ EuclideanSpace.single (0 : Fin 2) (1 : ℂ)).gap
              (LinearMap.range (toEuclideanLin (Q 0))) /
            Real.sqrt (1 - (ℂ ∙ EuclideanSpace.single (0 : Fin 2) (1 : ℂ)).gap
              (LinearMap.range (toEuclideanLin (Q 0))) ^ 2))) atTop (𝓝 0) ∧
      (!![(2 : ℂ), 1; 0, 1])ᴴ *ᵥ ![1, 1] = (2 : ℂ) • ![1, 1] ∧
      (ℂ ∙ WithLp.toLp 2 ![(((Real.sqrt 2)⁻¹ : ℝ) : ℂ), (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)]).gap
        (LinearMap.range (toEuclideanLin (Q 0))) = 1 := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := !![(2 : ℂ), 1; 0, 1] with hA
  set t : ℝ := (Real.sqrt 2)⁻¹ with ht
  have ht2 : t * t = 1 / 2 := inv_sqrt_two_mul_self
  have ht0 : 0 < t := inv_pos.2 (Real.sqrt_pos.2 (by norm_num))
  set Q₀ : Matrix (Fin 2) (Fin 1) ℂ := !![((t : ℝ) : ℂ); -((t : ℝ) : ℂ)] with hQ₀
  set q₀ : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![((t : ℝ) : ℂ), -((t : ℝ) : ℂ)] with hq₀
  -- `A Q₀ = Q₀`, hence `A^k Q₀ = Q₀`
  have hAQ : A * Q₀ = Q₀ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, Q₀, mul_apply, Fin.sum_univ_two]
    ring
  have hpow : ∀ k, A ^ k * Q₀ = Q₀ := by
    intro k
    induction k with
    | zero => rw [pow_zero, Matrix.one_mul]
    | succ k ih => rw [pow_succ', Matrix.mul_assoc, ih, hAQ]
  -- `ran Q_k = ran Q₀ = span{q₀}`
  have hrange0 : LinearMap.range (toEuclideanLin Q₀) = ℂ ∙ q₀ := by
    rw [range_toEuclideanLin_col]
    congr 2
    ext i
    fin_cases i <;> rfl
  have hrange : ∀ k, LinearMap.range (toEuclideanLin (Q k)) = ℂ ∙ q₀ := by
    intro k
    have hli : LinearIndependent ℂ (A ^ k * Q 0)ᵀ := by
      rw [h0, hpow]
      refine linearIndependent_unique_iff.2 fun h => ?_
      have := congrFun h 0
      simp [Q₀, ht0.ne'] at this
    rw [(orthogonalIteration_range hQ hli).1, h0, ← hrange0]
    ext x
    rw [Krylov.mem_subspaceIterate]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, rfl⟩ := hy
      refine ⟨z, ?_⟩
      rw [← toEuclideanLin_pow, ← toEuclideanLin_mul_apply, hpow]
    · intro hx
      obtain ⟨z, rfl⟩ := hx
      refine ⟨toEuclideanLin Q₀ z, ⟨z, rfl⟩, ?_⟩
      rw [← toEuclideanLin_pow, ← toEuclideanLin_mul_apply, hpow]
  have hq₀1 : ‖q₀‖ = 1 := by
    rw [norm_euclidean_two]
    simp [q₀, Complex.norm_real, abs_of_pos ht0, sq, ht2]
    norm_num
  have he1 : ‖EuclideanSpace.single (0 : Fin 2) (1 : ℂ)‖ = 1 := by simp
  have hc : ((t : ℝ) : ℂ) * ((t : ℝ) : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul, ht2]
    push_cast
    ring
  have hin : (inner ℂ q₀ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) : ℂ) = ((t : ℝ) : ℂ) := by
    simp [q₀, EuclideanSpace.inner_single_right]
  -- `d_k = 1/√2`
  have hd : ∀ k, (ℂ ∙ EuclideanSpace.single (0 : Fin 2) (1 : ℂ)).gap
      (LinearMap.range (toEuclideanLin (Q k))) = t := by
    intro k
    have hv : EuclideanSpace.single (0 : Fin 2) (1 : ℂ) -
        (inner ℂ q₀ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) / ((‖q₀‖ ^ 2 : ℝ) : ℂ)) • q₀ =
        WithLp.toLp 2 ![((1 / 2 : ℝ) : ℂ), ((1 / 2 : ℝ) : ℂ)] := by
      rw [hq₀1, hin]
      ext i
      fin_cases i
      · simp [q₀]
        linear_combination -hc
      · simp [q₀]
        linear_combination hc
    rw [Submodule.gap_congr _ _ (hrange k), gap_span_singleton_eq_sinAngle he1 hq₀1,
      Submodule.sinAngle, he1, div_one, Submodule.starProjection_singleton]
    refine (congrArg norm hv).trans ?_
    rw [norm_euclidean_two]
    have e0 : ‖(WithLp.toLp 2 ![((1 / 2 : ℝ) : ℂ), ((1 / 2 : ℝ) : ℂ)] :
        EuclideanSpace ℂ (Fin 2)) 0‖ = 1 / 2 := by
      simp
    have e1 : ‖(WithLp.toLp 2 ![((1 / 2 : ℝ) : ℂ), ((1 / 2 : ℝ) : ℂ)] :
        EuclideanSpace ℂ (Fin 2)) 1‖ = 1 / 2 := by
      simp
    rw [e0, e1, ht, ← Real.sqrt_inv]
    congr 1
    norm_num
  -- `‖N‖_F = 1`
  have hN : ‖strictUpper A‖ = 1 := by
    have e : strictUpper A = !![0, 1; 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [A, strictUpper_apply]
    rw [e, frobenius_norm_def]
    simp [Fin.sum_univ_two]
  refine ⟨hN, fun k => (hd k).trans rfl, ?_, ?_, ?_⟩
  · rw [hN]
    have hr : (‖(1 : ℂ)‖ + 1 / (1 + 3)) / (‖(2 : ℂ)‖ - 1 / (1 + 3)) = (5 / 7 : ℝ) := by
      norm_num
    rw [hr]
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 5 / 7)
      (by norm_num)).const_mul ((1 + 3 : ℝ) ^ (2 - 2) *
        (1 + ‖!![(1 : ℂ)]‖ / sep !![(2 : ℂ)] !![(1 : ℂ)]))
    rw [mul_zero] at h
    simpa using h.mul_const ((ℂ ∙ EuclideanSpace.single (0 : Fin 2) (1 : ℂ)).gap
      (LinearMap.range (toEuclideanLin (Q 0))) / Real.sqrt (1 - (ℂ ∙ EuclideanSpace.single
        (0 : Fin 2) (1 : ℂ)).gap (LinearMap.range (toEuclideanLin (Q 0))) ^ 2))
  · ext i
    fin_cases i <;> simp [A, mulVec, dotProduct, Fin.sum_univ_two, map_ofNat]
    norm_num
  · set w : EuclideanSpace ℂ (Fin 2) :=
      WithLp.toLp 2 ![((t : ℝ) : ℂ), ((t : ℝ) : ℂ)] with hw
    have hw1 : ‖w‖ = 1 := by
      rw [norm_euclidean_two]
      simp [w, Complex.norm_real, abs_of_pos ht0, sq, ht2]
      norm_num
    rw [Submodule.gap_congr _ _ (hrange 0), gap_span_singleton_eq_sinAngle hw1 hq₀1,
      Submodule.sinAngle, hw1, div_one, Submodule.starProjection_singleton]
    have hinner : (inner ℂ q₀ w : ℂ) = 0 := by
      simp [q₀, w, PiLp.inner_apply, Fin.sum_univ_two]
    rw [hinner, zero_div, zero_smul, sub_zero, hw1]

/-- The complementary-subspace identity behind (7.3.25), in the coordinates of a block Schur form
`Qᴴ A Q = [T₁₁ T₁₂; 0 T₂₂]` reindexed along `e`: with `T₁₁ X - X T₂₂ = -T₁₂` and
`P = Q [I; -Xᴴ]`, the powers satisfy `(Aᴴ)^k P = P (T₁₁ᴴ)^k`. -/
private theorem conjTranspose_pow_mul_eq {r : ℕ} {A Q : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) (e : Fin n ≃ Fin r ⊕ Fin (n - r))
    {T₁₁ : Matrix (Fin r) (Fin r) ℂ} {T₁₂ : Matrix (Fin r) (Fin (n - r)) ℂ}
    {T₂₂ : Matrix (Fin (n - r)) (Fin (n - r)) ℂ}
    (hT : (star Q * A * Q).reindex e e = fromBlocks T₁₁ T₁₂ 0 T₂₂)
    {X : Matrix (Fin r) (Fin (n - r)) ℂ} (hX : T₁₁ * X - X * T₂₂ = -T₁₂) (k : ℕ) :
    Aᴴ ^ k * (Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (-Xᴴ)).submatrix e id) =
      Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (-Xᴴ)).submatrix e id * T₁₁ᴴ ^ k := by
  set B := fromBlocks T₁₁ T₁₂ 0 T₂₂ with hBdef
  set M := fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (-Xᴴ) with hM
  have hBM : Bᴴ * M = M * T₁₁ᴴ :=
    (equation_7_3_25 (A := B) (Q := 1) (one_mem _) (by simp [hBdef]) hX).2.1
  have hQQ : Q * star Q = 1 := mem_unitaryGroup_iff.1 hQ
  have hQQ' : star Q * Q = 1 := mem_unitaryGroup_iff'.1 hQ
  have hB : star Q * A * Q = B.submatrix e e := by
    rw [← hT, reindex_apply, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
  have hA : A = Q * B.submatrix e e * star Q := by
    rw [← hB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ, Matrix.one_mul, Matrix.mul_assoc,
      hQQ, Matrix.mul_one]
  have h1 : Aᴴ * (Q * M.submatrix e id) = Q * M.submatrix e id * T₁₁ᴴ := by
    have hAh : Aᴴ = Q * Bᴴ.submatrix e e * star Q := by
      rw [hA, conjTranspose_mul, conjTranspose_mul, ← star_eq_conjTranspose (star Q), star_star,
        conjTranspose_submatrix, star_eq_conjTranspose, Matrix.mul_assoc]
    rw [hAh, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (star Q), hQQ',
      Matrix.one_mul, submatrix_mul_equiv, hBM,
      submatrix_mul _ _ _ _ _ Function.bijective_id, submatrix_id_id, Matrix.mul_assoc]
  induction k with
  | zero => rw [pow_zero, pow_zero, Matrix.one_mul, Matrix.mul_one]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_assoc, h1, ← Matrix.mul_assoc, ih, pow_succ, Matrix.mul_assoc]

open scoped Matrix.Norms.Frobenius

/-- **Theorem 7.3.1, corrected.** Let the Schur decomposition (7.3.7)–(7.3.8) be
`Qᴴ A Q = [T₁₁ T₁₂; 0 T₂₂]` (reindexed along `e`, `T₁₁` of size `r`, `0 < r < n`, both diagonal
blocks upper triangular), `|t_ii| ≥ a` on `T₁₁` and `|t_jj| ≤ b < a` on `T₂₂` (the book's
`a = |λ_r| > |λ_{r+1}| = b`), `ν ≥ ‖N‖_F` for the strictly upper parts of both blocks (the book's
`ν = ‖N‖_F`), `μ ≥ 0` with `(1 + μ) a > ν`, and `X` the solution of `T₁₁ X - X T₂₂ = -T₁₂` (7.3.20).
Let `Q_k` be an orthogonal iteration (7.3.6), `d_k = dist(D_r(A), ran Q_k)` with
`D_r(A) = ran(Q [I; 0])`, and `d̃₀ = dist(D_r(Aᴴ), ran Q₀)` with `D_r(Aᴴ) = ran(Q [I; -Xᴴ])` (the
dominant invariant subspace of `Aᴴ`, (7.3.25)). If `d̃₀ < 1` (in place of the printed (7.3.9)),
`d_k ≤ (1 + μ)^{n-2} (1 + ‖T₁₂‖_F / sep(T₁₁, T₂₂)) ((b + ν/(1+μ)) / (a - ν/(1+μ)))^k
d₀ / √(1 - d̃₀²)` for every `k`. `A^k Q₀` has full column rank (no vector of `ran Q₀` is orthogonal
to `D_r(Aᴴ)`, and `Aᴴ` is invertible on `D_r(Aᴴ)`), so `ran Q_k = A^k ran Q₀` and the backbone's
subspace-iteration bound applies. The printed version is false
(`theorem_7_3_1_counterexample`). -/
theorem theorem_7_3_1 {r : ℕ} {A Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q ∈ unitaryGroup (Fin n) ℂ)
    (e : Fin n ≃ Fin r ⊕ Fin (n - r)) {T₁₁ : Matrix (Fin r) (Fin r) ℂ}
    {T₁₂ : Matrix (Fin r) (Fin (n - r)) ℂ} {T₂₂ : Matrix (Fin (n - r)) (Fin (n - r)) ℂ}
    (hT : (star Q * A * Q).reindex e e = fromBlocks T₁₁ T₁₂ 0 T₂₂)
    (hT₁₁ : T₁₁.IsUpperTriangular) (hT₂₂ : T₂₂.IsUpperTriangular) (hr : 0 < r) (hrn : r < n)
    {a b ν μ : ℝ} (hμ : 0 ≤ μ) (ha : ∀ i, a ≤ ‖T₁₁ i i‖) (hb : ∀ j, ‖T₂₂ j j‖ ≤ b)
    (hab : b < a) (hν₁ : ‖strictUpper T₁₁‖ ≤ ν) (hν₂ : ‖strictUpper T₂₂‖ ≤ ν)
    (hνa : ν < (1 + μ) * a) {X : Matrix (Fin r) (Fin (n - r)) ℂ}
    (hX : T₁₁ * X - X * T₂₂ = -T₁₂) {Qk : ℕ → Matrix (Fin n) (Fin r) ℂ}
    (hQk : orthogonalIteration A Qk)
    (h0 : (LinearMap.range (toEuclideanLin
      (Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (-Xᴴ)).submatrix e id))).gap
        (LinearMap.range (toEuclideanLin (Qk 0))) < 1)
    (k : ℕ) :
    (LinearMap.range (toEuclideanLin (Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ)
        (0 : Matrix (Fin (n - r)) (Fin r) ℂ)).submatrix e id))).gap
        (LinearMap.range (toEuclideanLin (Qk k))) ≤
      (1 + μ) ^ (n - 2) * (1 + ‖T₁₂‖ / sep T₁₁ T₂₂) *
        ((b + ν / (1 + μ)) / (a - ν / (1 + μ))) ^ k *
        ((LinearMap.range (toEuclideanLin (Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ)
          (0 : Matrix (Fin (n - r)) (Fin r) ℂ)).submatrix e id))).gap
            (LinearMap.range (toEuclideanLin (Qk 0))) /
          Real.sqrt (1 - (LinearMap.range (toEuclideanLin
            (Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (-Xᴴ)).submatrix e id))).gap
              (LinearMap.range (toEuclideanLin (Qk 0))) ^ 2)) := by
  have hconj := conjTranspose_pow_mul_eq hQ e hT hX k
  have h0' := h0
  generalize hPdef : Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (-Xᴴ)).submatrix e id = P
    at h0' hconj
  set S₀ := LinearMap.range (toEuclideanLin (Qk 0)) with hS₀
  have hQ0 : (Qk 0)ᴴ * Qk 0 = 1 := hQk.1
  -- `T₁₁` is invertible
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb ⟨0, by omega⟩)
  have hT₁₁u : IsUnit T₁₁.det := by
    rw [det_of_isUpperTriangular hT₁₁, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro i _ h
    have := ha i
    rw [h, norm_zero] at this
    linarith
  have hTk : IsUnit (T₁₁ᴴ ^ k).det := by
    rw [det_pow, det_conjTranspose]
    exact (hT₁₁u.star).pow k
  -- `A^k` is injective on `ran Q₀`: a killed vector is orthogonal to `D_r(Aᴴ)`
  have hker : ∀ v ∈ S₀, (toEuclideanLin A ^ k) v = 0 → v = 0 := by
    intro v hv hAv
    refine Submodule.eq_zero_of_starProjection_eq_zero_of_gap_lt_one _ S₀ h0' hv ?_
    refine (Submodule.starProjection_apply_eq_zero_iff _).2 ((Submodule.mem_orthogonal _ _).2 ?_)
    rintro _ ⟨y, rfl⟩
    set y' := toEuclideanLin (T₁₁ᴴ ^ k)⁻¹ y
    have hy : toEuclideanLin P y = toEuclideanLin (Aᴴ ^ k) (toEuclideanLin P y') := by
      rw [← toEuclideanLin_mul_apply (Aᴴ ^ k), hconj, toEuclideanLin_mul_apply P,
        ← toEuclideanLin_mul_apply (T₁₁ᴴ ^ k), mul_nonsing_inv _ hTk, toLpLin_one,
        LinearMap.id_apply]
    rw [hy, ← conjTranspose_pow, toEuclideanLin_conjTranspose_eq_adjoint,
      LinearMap.adjoint_inner_left, toEuclideanLin_pow, hAv, inner_zero_right]
  -- hence `A^k Q₀` has full column rank
  have hli : LinearIndependent ℂ (A ^ k * Qk 0)ᵀ := by
    refine mulVec_injective_iff.1 fun c c' hcc => ?_
    have hd : (A ^ k * Qk 0) *ᵥ (c - c') = 0 := by rw [mulVec_sub, hcc, sub_self]
    set v := toEuclideanLin (Qk 0) (WithLp.toLp 2 (c - c'))
    have hv0 : v = 0 := by
      refine hker v ⟨_, rfl⟩ ?_
      rw [← toEuclideanLin_pow, ← toEuclideanLin_mul_apply, toEuclideanLin_toLp, hd,
        WithLp.toLp_zero]
    have hn : ‖v‖ = ‖(WithLp.toLp 2 (c - c') : EuclideanSpace ℂ (Fin r))‖ :=
      norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one hQ0 _
    rw [hv0, norm_zero, eq_comm, norm_eq_zero, WithLp.toLp_eq_zero] at hn
    exact sub_eq_zero.1 hn
  -- `dim ran Q₀ = r`
  have hdim : Module.finrank ℂ S₀ = r := by
    have hinj : Function.Injective (toEuclideanLin (Qk 0)) := by
      refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
      have hn := norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one hQ0 y
      rw [hy, norm_zero, eq_comm, norm_eq_zero] at hn
      exact hn
    rw [hS₀, LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace, Fintype.card_fin]
  subst hPdef
  have key := gap_subspaceIterate_le_of_schur hQ e hT hT₁₁ hT₂₂ hr hrn hμ ha hb hab hν₁ hν₂ hνa
    hX hdim h0 k
  exact (le_of_eq (Submodule.gap_congr _ _ (orthogonalIteration_range hQk hli).1)).trans key

end GolubVanLoan.Chapter07
