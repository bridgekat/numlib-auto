import Numlib.Krylov.BiLanczos
import NumlibSurface.QuarteroniSaccoSaleri.Chapter04.Section04

/-!
# Quarteroni–Sacco–Saleri §4.5: the Lanczos method for unsymmetric systems

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §4.5, over the backbone `Numlib/Krylov/BiLanczos` (the two-sided
Lanczos process, its biorthogonality and spans, the tridiagonal `Z_mᵀ A V_m = T_m`, the
biconjugate gradient and quasi-minimal residual methods) and `Numlib/Krylov/Hessenberg` (the
residual formulas of a Hessenberg relation).

## Conventions

Vectors are `EuclideanSpace ℝ (Fin n)` acted on by `Matrix.toEuclideanLin A`, as in §4.3–4.4; the
transpose `Aᵀ` acts as the adjoint. The bi-orthogonalization algorithm of the book is written as
the book writes it, as one step `biLanczosStep` on the state
`(v_k, z_k, v_{k-1}, z_{k-1}, β_k, γ_k)` iterated from `(v₁, z₁, 0, 0, 0, 0)` (`biLanczos`), with
the readers `blV`, `blZ`, `blAlpha`, `blBeta`, `blGamma`; indices are `0`-based, so `blV A v₁ z₁ k`
is the book's `v_{k+1}`, `blAlpha … k` its `α_{k+1}`, and `blBeta … k`, `blGamma … k` its
`β_{k+1}`, `γ_{k+1}` (with `β_1 = γ_1 = 0`). The step is the backbone's `BiLanczos.step` with
`B = Aᵀ` (`biLanczos_eq`), whose `w`, `δ` are the book's `z`, `γ`. "The process terminates after
`m` steps" is `∀ j < m, γ_{j+2} ≠ 0`, the backbone's `BiLanczos.NoBreakdown … m` together with
`z₁ᵀ v₁ = 1` (`noBreakdown_of`).

## Contents

* `biLanczosStep`, `biLanczos`, `blV`, `blZ`, `blAlpha`, `blBeta`, `blGamma`, `biLanczos_succ`,
  `biLanczos_eq`, `noBreakdown_of` — the bi-orthogonalization algorithm.
* `equation_4_67` — biorthogonality and the two Krylov bases.
* `T`, `That`, `Vmat`, `Zmat`, `biLanczos_tridiag` — `Z_mᵀ A V_m = T_m`.
* `lanczosUnsym_norm_residual` — the Lanczos method for unsymmetric systems and its residual.
* `bicg_isPetrovGalerkin`, `qmr_norm_residual_le` — items 1–2 of the closing list.

Example 4.10 is a numerical run and Program 25 is code. CGS and BiCGStab (item 3) are named without
an algorithm or a result and have no node.

## Readings

The residual formula `‖r⁽ᵐ⁾‖₂ = |γ_{m+1} e_mᵀ y_m| ‖v_{m+1}‖₂` is stated, as the book's derivation
needs, for a run of `m` steps without breakdown (`γ_2, …, γ_{m+1} ≠ 0`); the backbone's
Hessenberg relation is stated for a process without *serious* breakdown at every step, and the
`m`-step form is obtained here by padding the relation with zeros beyond column `m`
(`hessenbergRelation_trunc`), which is worth moving to the backbone. The QMR bound (Saad,
Proposition 7.3) is stated the same way, with the norm of the coordinate map `V_{m+1}` as an
explicit constant.
-/

open Filter Finset Matrix Topology WithLp

namespace QuarteroniSaccoSaleri.Chapter04

variable {n : ℕ}

/-! ### The bi-orthogonalization algorithm -/

section Algorithm

variable (A : Matrix (Fin n) (Fin n) ℝ)

/-- **The bi-orthogonalization algorithm of §4.5**, one step in the book's letters on the state
`(v_k, z_k, v_{k-1}, z_{k-1}, β_k, γ_k)`: `α_k = z_kᵀ A v_k`,
`ṽ_{k+1} = A v_k - α_k v_k - β_k v_{k-1}`, `z̃_{k+1} = Aᵀ z_k - α_k z_k - γ_k z_{k-1}`,
`γ_{k+1} = √|z̃_{k+1}ᵀ ṽ_{k+1}|`, `β_{k+1} = z̃_{k+1}ᵀ ṽ_{k+1} / γ_{k+1}`,
`v_{k+1} = ṽ_{k+1}/γ_{k+1}`, `z_{k+1} = z̃_{k+1}/β_{k+1}`. The book's "if `γ_{k+1} = 0` the
algorithm is stopped" is Lean's `0⁻¹ = 0`: all later vectors are `0`. The state is the backbone's
record `BiLanczos.State`, whose `w`, `delta` are the book's `z`, `γ`; the step is `BiLanczos.step`
with `B = Aᵀ` (`biLanczos_eq`). -/
noncomputable def biLanczosStep (s : BiLanczos.State ℝ (EuclideanSpace ℝ (Fin n))) :
    BiLanczos.State ℝ (EuclideanSpace ℝ (Fin n)) :=
  let α := inner ℝ s.w (toEuclideanLin A s.v)
  let vt := toEuclideanLin A s.v - α • s.v - s.beta • s.vPrev
  let zt := toEuclideanLin Aᵀ s.w - α • s.w - s.delta • s.wPrev
  let γ := Real.sqrt |inner ℝ zt vt|
  let β := inner ℝ zt vt / γ
  { v := γ⁻¹ • vt, w := β⁻¹ • zt, vPrev := s.v, wPrev := s.w, beta := β, delta := γ }

/-- **The bi-orthogonalization algorithm** started from `v₁`, `z₁` with `β_1 = γ_1 = 0` and
`v_0 = z_0 = 0`: the state after `k` steps. -/
noncomputable def biLanczos (v₁ z₁ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    BiLanczos.State ℝ (EuclideanSpace ℝ (Fin n)) :=
  (biLanczosStep A)^[k] { v := v₁, w := z₁, vPrev := 0, wPrev := 0, beta := 0, delta := 0 }

variable (v₁ z₁ : EuclideanSpace ℝ (Fin n))

/-- The vector `v_{k+1}` of the bi-orthogonalization algorithm (`0`-based). -/
noncomputable def blV (k : ℕ) : EuclideanSpace ℝ (Fin n) := (biLanczos A v₁ z₁ k).v

/-- The vector `z_{k+1}` of the bi-orthogonalization algorithm (`0`-based). -/
noncomputable def blZ (k : ℕ) : EuclideanSpace ℝ (Fin n) := (biLanczos A v₁ z₁ k).w

/-- The coefficient `α_{k+1} = z_{k+1}ᵀ A v_{k+1}` (`0`-based). -/
noncomputable def blAlpha (k : ℕ) : ℝ := inner ℝ (blZ A v₁ z₁ k) (toEuclideanLin A (blV A v₁ z₁ k))

/-- The coefficient `β_{k+1}` (`0`-based; `β_1 = 0`). -/
noncomputable def blBeta (k : ℕ) : ℝ := (biLanczos A v₁ z₁ k).beta

/-- The coefficient `γ_{k+1}` (`0`-based; `γ_1 = 0`); `γ_{k+2} = 0` is a breakdown at step
`k + 1`. -/
noncomputable def blGamma (k : ℕ) : ℝ := (biLanczos A v₁ z₁ k).delta

/-- One step of the bi-Lanczos recursion: the state at `k + 1` is `biLanczosStep` of the state at
`k`. -/
theorem biLanczos_succ (k : ℕ) :
    biLanczos A v₁ z₁ (k + 1) = biLanczosStep A (biLanczos A v₁ z₁ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The book's step is the backbone's `BiLanczos.step` with `B = Aᵀ`, on every state: over `ℝ`
the conjugations are trivial and `‖·‖` is `|·|`. -/
theorem biLanczosStep_eq (s : BiLanczos.State ℝ (EuclideanSpace ℝ (Fin n))) :
    biLanczosStep A s = BiLanczos.step (toEuclideanLin A) (toEuclideanLin Aᵀ) s := by
  simp only [biLanczosStep, BiLanczos.step, BiLanczos.stepAlpha, BiLanczos.stepVhat,
    BiLanczos.stepWhat, RCLike.conj_to_real, Real.norm_eq_abs, RCLike.ofReal_real_eq_id, id_eq]

/-- **The bridge to the backbone.** The bi-orthogonalization algorithm of §4.5 is the two-sided
Lanczos process `BiLanczos.state` of `A` with adjoint `Aᵀ`, and its readers are the backbone's
`BiLanczos.vec`, `dualVec`, `alpha`, `beta`, `delta`: the book's `z`, `γ` are Saad's `w`, `δ`. -/
theorem biLanczos_eq (k : ℕ) :
    biLanczos A v₁ z₁ k = BiLanczos.state (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ k ∧
      blV A v₁ z₁ k = BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ k ∧
      blZ A v₁ z₁ k = BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ k ∧
      blAlpha A v₁ z₁ k = BiLanczos.alpha (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ k ∧
      blBeta A v₁ z₁ k = BiLanczos.beta (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ k ∧
      blGamma A v₁ z₁ k = BiLanczos.delta (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ k := by
  have hstate : ∀ k, biLanczos A v₁ z₁ k =
      BiLanczos.state (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [biLanczos_succ, ih, BiLanczos.state_succ, biLanczosStep_eq]
  refine ⟨hstate k, ?_, ?_, ?_, ?_, ?_⟩
  · rw [blV, hstate]; rfl
  · rw [blZ, hstate]; rfl
  · rw [blAlpha, blZ, blV, hstate]; rfl
  · rw [blBeta, hstate]; rfl
  · rw [blGamma, hstate]; rfl

/-- `Aᵀ` acts as the adjoint of `A`: `(A x)ᵀ y = xᵀ (Aᵀ y)`. -/
theorem inner_toEuclideanLin_transpose (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (toEuclideanLin A x) y = inner ℝ x (toEuclideanLin Aᵀ y) := by
  rw [← conjTranspose_eq_transpose_of_trivial, real_inner_comm (toEuclideanLin Aᴴ y) x,
    toEuclideanLin_conjTranspose_inner_left, real_inner_comm]

variable {A v₁ z₁}

/-- "The process terminates after `m` steps": `z₁ᵀ v₁ = 1` and `γ_2, …, γ_{m+1} ≠ 0` is the
backbone's `BiLanczos.NoBreakdown … m` for `A` and its adjoint `Aᵀ`. -/
theorem noBreakdown_of (hz : inner ℝ z₁ v₁ = 1) {m : ℕ}
    (hγ : ∀ j < m, blGamma A v₁ z₁ (j + 1) ≠ 0) :
    BiLanczos.NoBreakdown (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ m where
  adjoint := inner_toEuclideanLin_transpose A
  inner_start := hz
  delta_ne_zero j hj := by
    rw [← (biLanczos_eq A v₁ z₁ (j + 1)).2.2.2.2.2]
    exact hγ j hj

end Algorithm

/-! ### (4.67) and the tridiagonal matrix -/

section Biorthogonal

variable (A : Matrix (Fin n) (Fin n) ℝ) (v₁ z₁ : EuclideanSpace ℝ (Fin n))

/-- The range of a `Fin m`-indexed family is the image of `Set.Iio m`. -/
private theorem range_fin_eq_image_Iio {α : Type*} (f : ℕ → α) (m : ℕ) :
    Set.range (fun i : Fin m => f (i : ℕ)) = f '' Set.Iio m := by
  ext x
  simp only [Set.mem_range, Set.mem_image, Set.mem_Iio, Fin.exists_iff]
  tauto

/-- **(4.67).** If `z₁ᵀ v₁ = 1` and the process runs `m` steps without breakdown, the two families
are bi-orthogonal, `z_iᵀ v_j = δ_ij` for `i, j = 1, …, m + 1`, and `v_1, …, v_m` and `z_1, …, z_m`
are bases of `K_m(A; v₁)` and `K_m(Aᵀ; z₁)` (backbone `BiLanczos.inner_dualVec_vec`,
`BiLanczos.span_vec`, `BiLanczos.span_dualVec`). -/
theorem equation_4_67 (hz : inner ℝ z₁ v₁ = 1) {m : ℕ}
    (hγ : ∀ j < m, blGamma A v₁ z₁ (j + 1) ≠ 0) :
    (∀ i j, i ≤ m → j ≤ m → inner ℝ (blZ A v₁ z₁ i) (blV A v₁ z₁ j) = if i = j then 1 else 0) ∧
      Submodule.span ℝ (Set.range fun i : Fin m => blV A v₁ z₁ i) = krylovSubspace A v₁ m ∧
      Submodule.span ℝ (Set.range fun i : Fin m => blZ A v₁ z₁ i) = krylovSubspace Aᵀ z₁ m := by
  have h := noBreakdown_of hz hγ
  simp only [(biLanczos_eq A v₁ z₁ _).2.1, (biLanczos_eq A v₁ z₁ _).2.2.1]
  refine ⟨fun i j hi hj => BiLanczos.inner_dualVec_vec h hi hj, ?_, ?_⟩
  · rw [range_fin_eq_image_Iio, BiLanczos.span_vec h, krylovSubspace_eq]
  · rw [range_fin_eq_image_Iio, BiLanczos.span_dualVec h, krylovSubspace_eq]

/-- The tridiagonal matrix `T_m` of §4.5: `α_i` on the diagonal, `β_{i+1}` on the superdiagonal
and `γ_{i+1}` on the subdiagonal (`0`-based readers). -/
noncomputable def T (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then blAlpha A v₁ z₁ i
    else if (i : ℕ) = j + 1 then blGamma A v₁ z₁ i
    else if (j : ℕ) = i + 1 then blBeta A v₁ z₁ j
    else 0

/-- The `(m+1) × m` extension `T̄_m` of `T_m` by the row `(0, …, 0, γ_{m+1})`, the matrix of the
relation `A V_m = V_{m+1} T̄_m`. -/
noncomputable def That (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then blAlpha A v₁ z₁ i
    else if (i : ℕ) = j + 1 then blGamma A v₁ z₁ i
    else if (j : ℕ) = i + 1 then blBeta A v₁ z₁ j
    else 0

/-- The matrix `V_m ∈ ℝ^{n×m}` whose columns are `v_1, …, v_m`. -/
noncomputable def Vmat (m : ℕ) : Matrix (Fin n) (Fin m) ℝ := Matrix.of fun i j => blV A v₁ z₁ j i

/-- The matrix `Z_m ∈ ℝ^{n×m}` whose columns are `z_1, …, z_m`. -/
noncomputable def Zmat (m : ℕ) : Matrix (Fin n) (Fin m) ℝ := Matrix.of fun i j => blZ A v₁ z₁ j i

/-- The entries of `T_m` and `T̄_m` are the backbone's tridiagonal coefficient array. -/
theorem T_apply_eq_coeff (m : ℕ) (i j : Fin m) :
    T A v₁ z₁ m i j = BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ i j := by
  simp only [T, Matrix.of_apply, BiLanczos.coeff, (biLanczos_eq A v₁ z₁ _).2.2.2.1,
    (biLanczos_eq A v₁ z₁ _).2.2.2.2.1, (biLanczos_eq A v₁ z₁ _).2.2.2.2.2]

/-- The entries of `T̄_m` are the backbone's tridiagonal coefficient array. -/
theorem That_apply_eq_coeff (m : ℕ) (i : Fin (m + 1)) (j : Fin m) :
    That A v₁ z₁ m i j = BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ i j := by
  simp only [That, Matrix.of_apply, BiLanczos.coeff, (biLanczos_eq A v₁ z₁ _).2.2.2.1,
    (biLanczos_eq A v₁ z₁ _).2.2.2.2.1, (biLanczos_eq A v₁ z₁ _).2.2.2.2.2]

/-- The entry `(i, j)` of `Z_mᵀ A V_m` is `z_iᵀ A v_j`. -/
private theorem transpose_Zmat_mul_mul_Vmat_apply (m : ℕ) (i j : Fin m) :
    ((Zmat A v₁ z₁ m)ᵀ * A * Vmat A v₁ z₁ m) i j =
      inner ℝ (blZ A v₁ z₁ i) (toEuclideanLin A (blV A v₁ z₁ j)) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, ofLp_toEuclideanLin,
    Matrix.mul_apply, Matrix.transpose_apply, Zmat, Vmat, Matrix.of_apply, dotProduct,
    Matrix.mulVec, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **`Z_mᵀ A V_m = T_m`.** If the process runs `m` steps without breakdown from `z₁ᵀ v₁ = 1`, the
matrices of the two bases satisfy `Z_mᵀ A V_m = T_m` with `T_m` the tridiagonal matrix of the
coefficients (backbone `BiLanczos.inner_dualVec_apply_vec`). -/
theorem biLanczos_tridiag (hz : inner ℝ z₁ v₁ = 1) {m : ℕ}
    (hγ : ∀ j < m, blGamma A v₁ z₁ (j + 1) ≠ 0) :
    (Zmat A v₁ z₁ m)ᵀ * A * Vmat A v₁ z₁ m = T A v₁ z₁ m := by
  have h := noBreakdown_of hz hγ
  ext i j
  rw [transpose_Zmat_mul_mul_Vmat_apply, T_apply_eq_coeff, (biLanczos_eq A v₁ z₁ _).2.1,
    (biLanczos_eq A v₁ z₁ _).2.2.1]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := i.isLt; omega⟩
  exact BiLanczos.inner_dualVec_apply_vec h (by omega) (by have := j.isLt; omega)

end Biorthogonal

/-! ### The Lanczos method for unsymmetric systems -/

section Method

variable {A : Matrix (Fin n) (Fin n) ℝ} {v₁ z₁ : EuclideanSpace ℝ (Fin n)}

open BiLanczos in
/-- Everything strictly to the left of the subdiagonal of a column of the coefficient array
collapses to the single `β_j` term. -/
private theorem sum_coeff_lt (j : ℕ) :
    ∑ i ∈ Finset.range j, coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ i j •
        vec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ i =
      beta (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ j •
        vecPrev (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ j := by
  cases j with
  | zero => simp
  | succ k =>
    have hz : ∑ i ∈ Finset.range k, coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ i (k + 1) •
        vec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have hik : i < k := Finset.mem_range.1 hi
        rw [coeff_eq_zero _ _ _ _ (by omega) (by omega) (by omega), zero_smul]
    rw [Finset.sum_range_succ, hz, zero_add, coeff_self_succ, vecPrev_succ]

open BiLanczos in
-- TODO(backbone): an `m`-step form of `BiLanczos.hessenbergRelation` under `NoBreakdown m`.
/-- The `m`-step Hessenberg relation of the process: under `NoBreakdown m`, the first `m` columns
of `A V = V T̄` hold, and padding the iterate basis and the coefficients with zeros beyond column
`m - 1` gives a two-family Hessenberg relation to which the residual formulas of
`Numlib/Krylov/Hessenberg` apply. -/
private theorem hessenbergRelation_trunc {m : ℕ}
    (h : NoBreakdown (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ m) :
    Krylov.HessenbergRelation₂ (toEuclideanLin A)
      (fun j => if j < m then vec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ j else 0)
      (vec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁)
      (fun i j => if j < m then coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ i j else 0) where
  apply_eq j := by
    by_cases hj : j < m
    · simp only [hj, ite_true]
      rw [show j + 2 = j + 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
        sum_coeff_lt, coeff_self, coeff_succ_self]
      exact apply_vec _ _ _ _ (h.delta_ne_zero j hj)
    · simp only [hj, ite_false, map_zero, zero_smul, Finset.sum_const_zero]
  eq_zero_of_lt i j hij := by
    by_cases hj : j < m
    · simp only [hj, ite_true]
      exact coeff_eq_zero_of_lt _ _ _ _ hij
    · simp only [hj, ite_false]

/-- The residual of `x₀ + ∑_j y_j v_j` under `NoBreakdown m`, expanded in the basis
`v_1, …, v_{m+1}` with the coordinate vector `‖r⁽⁰⁾‖ e₁ - T̄_m y`. -/
private theorem residual_eq_sum {b x₀ : EuclideanSpace ℝ (Fin n)} {β : ℝ}
    (hr : b - toEuclideanLin A x₀ = β • v₁) {m : ℕ}
    (h : BiLanczos.NoBreakdown (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ m) (y : Fin m → ℝ) :
    b - toEuclideanLin A (x₀ + ∑ j, y j • blV A v₁ z₁ j) =
      ∑ i : Fin (m + 1), (β • e₁ (m + 1) - That A v₁ z₁ m *ᵥ y) i • blV A v₁ z₁ i := by
  have hv : ∀ k, blV A v₁ z₁ k = BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ k :=
    fun k => (biLanczos_eq A v₁ z₁ k).2.1
  have hrel := (hessenbergRelation_trunc h).residual_eq (β := β) (b := b) (x₀ := x₀)
    (by rw [hr]; rfl) m y
  have hz : ∑ j : Fin m, y j • (if (j : ℕ) < m then
      BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ j else 0) =
      ∑ j : Fin m, y j • BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ j :=
    Finset.sum_congr rfl fun j _ => by rw [ite_eq_left j.isLt]
  have hH : Krylov.hessenbergOf (fun i j => if j < m then
      BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ i j else 0) m =
      That A v₁ z₁ m := by
    ext i j
    rw [Krylov.hessenbergOf, Matrix.of_apply, ite_eq_left j.isLt, That_apply_eq_coeff]
  rw [hz, hH, ← smul_e₁_eq_firstVec] at hrel
  simp only [hv]
  exact hrel

/-- **The Lanczos method for unsymmetric systems and its residual.** With `v₁ = z₁ = r⁽⁰⁾/‖r⁽⁰⁾‖₂`
(Program 25's choice, for which `z₁ᵀ v₁ = 1`) and `m ≥ 1` steps run without breakdown, let
`y⁽ᵐ⁾` solve `T_m y⁽ᵐ⁾ = ‖r⁽⁰⁾‖₂ e₁` and set `x⁽ᵐ⁾ = x⁽⁰⁾ + V_m y⁽ᵐ⁾`. Then the residual is
`r⁽ᵐ⁾ = -(γ_{m+1} e_mᵀ y⁽ᵐ⁾) v_{m+1}`, so that `‖r⁽ᵐ⁾‖₂ = |γ_{m+1} e_mᵀ y⁽ᵐ⁾| ‖v_{m+1}‖₂` — the
book's stopping formula, which keeps `‖v_{m+1}‖₂` because the bi-Lanczos basis is not normalized.
The bi-Lanczos relation `A V_m = V_{m+1} T̄_m` is a Hessenberg relation with a non-orthonormal
basis, to which `Krylov.HessenbergRelation₂.residual_eq_of_mulVec_eq` applies verbatim. -/
theorem lanczosUnsym_norm_residual {b x₀ : EuclideanSpace ℝ (Fin n)}
    (hr : b - toEuclideanLin A x₀ ≠ 0) (hv₁ : v₁ = (‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ •
      (b - toEuclideanLin A x₀)) {m : ℕ} (hm : 0 < m)
    (hγ : ∀ j < m, blGamma A v₁ v₁ (j + 1) ≠ 0) (y : Fin m → ℝ)
    (hy : T A v₁ v₁ m *ᵥ y = ‖b - toEuclideanLin A x₀‖ • e₁ m) :
    b - toEuclideanLin A (x₀ + ∑ j, y j • blV A v₁ v₁ j) =
        -(blGamma A v₁ v₁ m * y ⟨m - 1, Nat.sub_lt hm one_pos⟩) • blV A v₁ v₁ m ∧
      ‖b - toEuclideanLin A (x₀ + ∑ j, y j • blV A v₁ v₁ j)‖ =
        |blGamma A v₁ v₁ m * y ⟨m - 1, Nat.sub_lt hm one_pos⟩| * ‖blV A v₁ v₁ m‖ := by
  have hnorm : ‖b - toEuclideanLin A x₀‖ ≠ 0 := norm_ne_zero_iff.mpr hr
  have hz : inner ℝ v₁ v₁ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv₁, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm,
      one_pow]
  have h := noBreakdown_of hz hγ
  have hv : ∀ k, blV A v₁ v₁ k = BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ v₁ k :=
    fun k => (biLanczos_eq A v₁ v₁ k).2.1
  have hr' : b - toEuclideanLin A x₀ = ‖b - toEuclideanLin A x₀‖ • v₁ := by
    rw [hv₁, smul_smul, mul_inv_cancel₀ hnorm, one_smul]
  have hT : Krylov.hessenbergSqOf (fun i j => if j < m then
      BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ v₁ i j else 0) m = T A v₁ v₁ m := by
    ext i j
    rw [Krylov.hessenbergSqOf, Matrix.of_apply, ite_eq_left j.isLt, T_apply_eq_coeff]
  have hy' : Krylov.hessenbergSqOf (fun i j => if j < m then
      BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ v₁ i j else 0) m *ᵥ y =
      Krylov.firstVec ‖b - toEuclideanLin A x₀‖ m := by
    rw [hT, hy, smul_e₁_eq_firstVec]
  have hres := (hessenbergRelation_trunc h).residual_eq_of_mulVec_eq (b := b) (x₀ := x₀)
    (show b - toEuclideanLin A x₀ = ‖b - toEuclideanLin A x₀‖ •
      BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ v₁ 0 from hr') hm y hy'
  have hsum : ∑ j : Fin m, y j • (if (j : ℕ) < m then
      BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ v₁ j else 0) =
      ∑ j : Fin m, y j • BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ v₁ j :=
    Finset.sum_congr rfl fun j _ => by rw [ite_eq_left j.isLt]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hδ := (biLanczos_eq A v₁ v₁ (m' + 1)).2.2.2.2.2
  simp only [Nat.add_sub_cancel, Nat.lt_succ_self, ite_true, BiLanczos.coeff_succ_self,
    hsum] at hres
  simp only [← hδ, ← hv] at hres
  simp only [Nat.add_sub_cancel]
  refine ⟨hres, ?_⟩
  rw [hres, norm_smul, norm_neg, Real.norm_eq_abs]

/-- **§4.5, item 1: the bi-conjugate gradient method.** BiCG "can be derived by the unsymmetric
Lanczos method in the same way as the conjugate gradient method is obtained from the FOM method":
its iterate (backbone `BCG.iterate`, Saad's Algorithm 7.3, with `Aᵀ` for the adjoint and the
shadow residual `r*⁽⁰⁾`) is, as long as it runs without breakdown, the oblique projection method
of Remark 4.4 with `Y_k = K_k(A; r⁽⁰⁾)` and `L_k = K_k(Aᵀ; r*⁽⁰⁾)` (backbone `BCG.isPetrovGalerkin`,
Saad's Proposition 7.2). -/
theorem bicg_isPetrovGalerkin {b x₀ rs₀ : EuclideanSpace ℝ (Fin n)} {k : ℕ}
    (h : BCG.NoBreakdown (toEuclideanLin A) (toEuclideanLin Aᵀ) b x₀ rs₀ k) :
    remark_4_4 A b x₀ (krylovSubspace A (b - toEuclideanLin A x₀) k) (krylovSubspace Aᵀ rs₀ k)
      (BCG.iterate (toEuclideanLin A) (toEuclideanLin Aᵀ) b x₀ rs₀ k).x := by
  rw [(remark_4_4_iff A b x₀ _ _ _).1, krylovSubspace_eq, krylovSubspace_eq]
  exact BCG.isPetrovGalerkin h

/-- **§4.5, item 2: the quasi-minimal residual method.** QMR "is analogous to the GMRES method,
the only difference being that the Arnoldi orthonormalization is replaced by the Lanczos
bi-orthogonalization": from `v₁ = z₁ = r⁽⁰⁾/‖r⁽⁰⁾‖₂`, `m` steps of the process without breakdown
give `A V_m = V_{m+1} T̄_m`, so that the residual of `x⁽⁰⁾ + V_m y` is
`V_{m+1} (‖r⁽⁰⁾‖₂ e₁ - T̄_m y)` and is bounded by `‖V_{m+1}‖₂ ‖‖r⁽⁰⁾‖₂ e₁ - T̄_m y‖₂` — the
quasi-residual that QMR minimizes over `y` in place of the residual GMRES minimizes, the two
differing because `V_{m+1}` is not orthogonal (Saad, Proposition 7.3; backbone
`QMR.norm_residual_le_norm_quasiResidual`). The bound `C` on the coordinate map `y ↦ V_{m+1} y`
is `‖V_{m+1}‖₂`. -/
theorem qmr_norm_residual_le {b x₀ : EuclideanSpace ℝ (Fin n)}
    (hr : b - toEuclideanLin A x₀ ≠ 0) (hv₁ : v₁ = (‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ •
      (b - toEuclideanLin A x₀)) {m : ℕ} (hγ : ∀ j < m, blGamma A v₁ v₁ (j + 1) ≠ 0) {C : ℝ}
    (hC : ∀ z : Fin (m + 1) → ℝ, ‖∑ i, z i • blV A v₁ v₁ i‖ ≤
      C * ‖(toLp 2 z : EuclideanSpace ℝ (Fin (m + 1)))‖) (y : Fin m → ℝ) :
    b - toEuclideanLin A (x₀ + ∑ j, y j • blV A v₁ v₁ j) =
        ∑ i : Fin (m + 1), (‖b - toEuclideanLin A x₀‖ • e₁ (m + 1) - That A v₁ v₁ m *ᵥ y) i •
          blV A v₁ v₁ i ∧
      ‖b - toEuclideanLin A (x₀ + ∑ j, y j • blV A v₁ v₁ j)‖ ≤
        C * ‖(toLp 2 (‖b - toEuclideanLin A x₀‖ • e₁ (m + 1) - That A v₁ v₁ m *ᵥ y) :
          EuclideanSpace ℝ (Fin (m + 1)))‖ := by
  have hnorm : ‖b - toEuclideanLin A x₀‖ ≠ 0 := norm_ne_zero_iff.mpr hr
  have hz : inner ℝ v₁ v₁ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv₁, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm,
      one_pow]
  have h := noBreakdown_of hz hγ
  have hr' : b - toEuclideanLin A x₀ = ‖b - toEuclideanLin A x₀‖ • v₁ := by
    rw [hv₁, smul_smul, mul_inv_cancel₀ hnorm, one_smul]
  have hres := residual_eq_sum hr' h y
  exact ⟨hres, by rw [hres]; exact hC _⟩

end Method

end QuarteroniSaccoSaleri.Chapter04
