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

end GolubVanLoan.Chapter07
