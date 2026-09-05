import SaadSparse.Ch06.GCR

/-!
# Saad, §6.10: optimality and the Faber–Manteuffel condition

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003, §6.10.

**Proposition 6.22** says that when `Aᵀ v ∈ 𝒦_s(A, v)` for every `v`, the Arnoldi coefficients
obey the band condition `h_{ij} = 0` for `i + s ≤ j` (6.108), so that the incomplete
orthogonalization process of Algorithm 6.6 with a window of `s` drops nothing and DIOM(s)
computes the FOM approximation. The band condition itself is the backbone's
`Arnoldi.coeff_eq_zero_of_adjoint_mem` (`Numlib/Krylov/Arnoldi.lean`); the algorithmic
consequence is `iop_eq_arnoldiMGS_of_band` (IOP(s) is Algorithm 6.2) together with
`iomFixed_eq_fomFixed_of_band` and `diom_eq_fomFixed_of_band`, which use the IOP/DIOM layer of
`Ch06/FOM.lean`.

The section's two objects are here: `ν A`, the least degree of a polynomial `q` with
`A^H = q(A)`, and `IsCGs A s`, Faber and Manteuffel's class `CG(s)` of matrices for which the
Arnoldi process is an `s`-term recurrence for every starting vector. The text's two remarks
about normality are `isStarNormal_of_exists_aeval` (if `A^H = q(A)` then `A` is normal, since
`A` commutes with every polynomial in `A`) and `exists_aeval_eq_conjTranspose` (the converse).

**Deferred to a later phase** (`tracker/saadsparse-ch6.md` §4, item 2, the normal-matrix
theory of the backbone: normal ⟺ every eigenvector of `A` is an eigenvector of `A^H`, the
spectral theorem for normal matrices, and `natDegree (minpoly ℂ A)` = the number of distinct
eigenvalues): **Lemma 6.23** (`A` nonsingular satisfies `A^H v ∈ 𝒦_s(A, v)` for every `v` iff
`A` is normal with `ν(A) ≤ s - 1`) and **Theorem 6.24** (Faber–Manteuffel: `A ∈ CG(s)` iff the
minimal polynomial of `A` has degree `≤ s`, or `A` is normal with `ν(A) ≤ s - 1`), which the
book itself states without proof. The converse half of the text's normality remark
(`exists_aeval_eq_conjTranspose`) belongs to the same deferred item.

Proposition 6.22 is stated over `ℝ` with `Aᵀ`, and §6.10's normality material over `ℂ` with
`A^H`, following the book. The band lemmas are polymorphic in `𝕜`.
-/

open Polynomial

open scoped ComplexOrder Matrix

namespace SaadSparse.Ch06

section Band

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

variable (A : Matrix (Fin n) (Fin n) 𝕜) (v : EuclideanSpace 𝕜 (Fin n))

/-! ### (6.108): the band structure of the Arnoldi coefficients -/

/-- **(6.108)**: if `A^H v ∈ 𝒦_s(A, v)` for every `v`, the Arnoldi coefficients vanish outside a
band of width `s`. This is the backbone's `Arnoldi.coeff_eq_zero_of_adjoint_mem`, whose `s = 2`
case is the tridiagonality of the symmetric Lanczos process. -/
theorem arnoldiCoeff_eq_zero_of_adjoint_mem {s : ℕ}
    (hs : ∀ w : 𝔼, LinearMap.adjoint (op A) w ∈ krylov A w s) (hv : ‖v‖ = 1) {i j : ℕ}
    (h : i + s ≤ j) : arnoldiCoeff A v i j = 0 := by
  rw [arnoldiCoeff_eq A v hv]
  refine Arnoldi.coeff_eq_zero_of_adjoint_mem (op A) v
    (fun x y => (LinearMap.adjoint_inner_right (op A) x y).symm) (fun w => ?_) h
  rw [← krylov_eq]
  exact hs w

/-! ### The truncated inner loop of Algorithm 6.6 under a band condition -/

private theorem mgsW_eq_sub_sum' (u : ℕ → 𝔼) (w₀ : 𝔼) (k : ℕ) :
    mgsW u w₀ k = w₀ - ∑ i ∈ Finset.range k, inner 𝕜 (u i) (mgsW u w₀ i) • u i := by
  induction k with
  | zero => simp [mgsW]
  | succ k ih =>
    have h : mgsW u w₀ (k + 1) = mgsW u w₀ k - inner 𝕜 (u k) (mgsW u w₀ k) • u k := by rw [mgsW]
    rw [h, Finset.sum_range_succ]
    nth_rewrite 1 [ih]
    abel

/-- For an orthogonal family the modified Gram–Schmidt loop does not change the coefficient it
is about to compute. -/
private theorem inner_mgsW_self' {u : ℕ → 𝔼} (ho : ∀ a c, a ≠ c → inner 𝕜 (u a) (u c) = 0)
    (w₀ : 𝔼) (k : ℕ) : inner 𝕜 (u k) (mgsW u w₀ k) = inner 𝕜 (u k) w₀ := by
  rw [mgsW_eq_sub_sum' u w₀ k, inner_sub_right, inner_sum,
    Finset.sum_eq_zero fun i hi => by
      rw [inner_smul_right, ho k i (by have := Finset.mem_range.1 hi; omega), mul_zero],
    sub_zero]

/-- The truncated loop of Algorithm 6.6 agrees with the full loop of Algorithm 6.2 as soon as
the coefficients it skips vanish. -/
private theorem iopW_eq_mgsW_of_band {u : ℕ → 𝔼} {lo : ℕ} (w₀ : 𝔼)
    (h : ∀ i < lo, inner 𝕜 (u i) (mgsW u w₀ i) = 0) (N : ℕ) :
    iopW u lo w₀ N = mgsW u w₀ N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [iopW_succ, iopCoeffOf, ih, mgsW]
    by_cases hlo : lo ≤ N
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hlo)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hlo), h N (by omega), zero_smul]

variable {A v}

private theorem inner_mgsW_arnoldiMGS_eq_zero {s : ℕ} (hv : ‖v‖ = 1)
    (hband : ∀ i j : ℕ, i + s ≤ j → arnoldiCoeff A v i j = 0) (j : ℕ) :
    ∀ i < j + 1 - s,
      inner 𝕜 (arnoldiMGS A v i) (mgsW (arnoldiMGS A v) (op A (arnoldiMGS A v j)) i) = 0 := by
  have ho : ∀ a c : ℕ, a ≠ c → inner 𝕜 (arnoldiMGS A v a) (arnoldiMGS A v c) = 0 := by
    intro a c hac
    rw [arnoldiMGS_eq_arnoldiCGS A v hv, arnoldiMGS_eq_arnoldiCGS A v hv]
    exact inner_arnoldiCGS_eq_zero A v hv hac
  intro i hi
  rw [inner_mgsW_self' ho, arnoldiMGS_eq_arnoldiCGS A v hv, arnoldiMGS_eq_arnoldiCGS A v hv]
  exact hband i j (by omega)

/-- **The algorithmic content of Proposition 6.22**: under the band condition (6.108) the
incomplete orthogonalization process of **Algorithm 6.6** with window `s` is the full modified
Gram–Schmidt Arnoldi process of **Algorithm 6.2** — the terms it drops are zero. -/
theorem iop_eq_arnoldiMGS_of_band {s : ℕ} (hv : ‖v‖ = 1)
    (hband : ∀ i j : ℕ, i + s ≤ j → arnoldiCoeff A v i j = 0) (j : ℕ) :
    iop A v s j = arnoldiMGS A v j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero => rw [iop_zero, arnoldiMGS_zero]
    | succ j =>
      have hprev : ∀ i < j + 1, iop A v s i = arnoldiMGS A v i := fun i hi => ih i hi
      have hw : iopVecW A v s j = arnoldiMGSW A v j := by
        rw [iopVecW, arnoldiMGSW, hprev j j.lt_succ_self,
          iopW_congr (v := iop A v s) (v' := arnoldiMGS A v) (j + 1 - s)
            (op A (arnoldiMGS A v j)) hprev]
        exact iopW_eq_mgsW_of_band _ (inner_mgsW_arnoldiMGS_eq_zero hv hband j) (j + 1)
      rw [iop_succ, arnoldiMGS_succ, hw]

private theorem iop_eq_arnoldiMGS_fun {s : ℕ} (hv : ‖v‖ = 1)
    (hband : ∀ i j : ℕ, i + s ≤ j → arnoldiCoeff A v i j = 0) :
    iop A v s = arnoldiMGS A v :=
  funext (iop_eq_arnoldiMGS_of_band hv hband)

/-- Under the band condition the coefficients of Algorithm 6.6 are the Arnoldi coefficients. -/
theorem iopCoeff_eq_arnoldiCoeff_of_band {s : ℕ} (hv : ‖v‖ = 1)
    (hband : ∀ i j : ℕ, i + s ≤ j → arnoldiCoeff A v i j = 0) (i j : ℕ) :
    iopCoeff A v s i j = arnoldiCoeff A v i j := by
  have hfun := iop_eq_arnoldiMGS_fun hv hband
  have hiw : ∀ N, iopW (arnoldiMGS A v) (j + 1 - s) (op A (arnoldiMGS A v j)) N
      = mgsW (arnoldiMGS A v) (op A (arnoldiMGS A v j)) N := fun N =>
    iopW_eq_mgsW_of_band _ (inner_mgsW_arnoldiMGS_eq_zero hv hband j) N
  rw [← arnoldiMGSCoeff_eq_arnoldiCoeff A v hv, iopCoeff, arnoldiMGSCoeff, iopVecW, hfun,
    arnoldiMGSW, hiw]
  split_ifs with h1 h2
  · rw [iopCoeffOf, hiw]
    by_cases hlo : j + 1 - s ≤ i
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hlo)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hlo),
        inner_mgsW_arnoldiMGS_eq_zero hv hband j i (by omega)]
  · rfl
  · rfl

end Band

section BandFOM

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

variable {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ : EuclideanSpace 𝕜 (Fin n)} {s : ℕ}

/-- Under the band condition, Algorithm 6.6 and Algorithm 6.1 build the same basis. -/
theorem VI_eq_V (hv : ‖v₁ A b x₀‖ = 1)
    (hband : ∀ i j : ℕ, i + s ≤ j → arnoldiCoeff A (v₁ A b x₀) i j = 0) (m : ℕ) :
    VI A (v₁ A b x₀) s m = V A (v₁ A b x₀) m := by
  rw [VI, V, iop_eq_arnoldiMGS_fun hv hband,
    funext fun l => arnoldiMGS_eq_arnoldiCGS A (v₁ A b x₀) hv l]

/-- Under the band condition, Algorithm 6.6 and Algorithm 6.1 build the same `H_m`. -/
theorem HI_eq_H (hv : ‖v₁ A b x₀‖ = 1)
    (hband : ∀ i j : ℕ, i + s ≤ j → arnoldiCoeff A (v₁ A b x₀) i j = 0) (m : ℕ) :
    HI A (v₁ A b x₀) s m = H A (v₁ A b x₀) m := by
  ext i j
  rw [HI_apply, H_apply, iopCoeff_eq_arnoldiCoeff_of_band hv hband]

/-- **IOM(s) is FOM** under the band condition (6.108): Algorithm 6.7 and Algorithm 6.4 solve
the same system in the same basis. -/
theorem iomFixed_eq_fomFixed_of_band (hv : ‖v₁ A b x₀‖ = 1)
    (hband : ∀ i j : ℕ, i + s ≤ j → arnoldiCoeff A (v₁ A b x₀) i j = 0) (m : ℕ) :
    iomFixed A b x₀ s m = fomFixed A b x₀ m := by
  rw [iomFixed, fomFixed, iomY, fomY, HI_eq_H hv hband, VI_eq_V hv hband]

/-- **DIOM(s) is mathematically equivalent to FOM** under the band condition (6.108), which is
the conclusion of Proposition 6.22. -/
theorem diom_eq_fomFixed_of_band (hv : ‖v₁ A b x₀‖ = 1)
    (hband : ∀ i j : ℕ, i + s ≤ j → arnoldiCoeff A (v₁ A b x₀) i j = 0) {m : ℕ}
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) s) l l ≠ 0) :
    diom A b x₀ s m = fomFixed A b x₀ m := by
  rw [diom_eq_iomFixed A b x₀ s hpiv, iomFixed_eq_fomFixed_of_band hv hband]

end BandFOM

/-! ### Proposition 6.22, in the book's real setting -/

section BookResults

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)

/-- Over `ℝ` the transpose induces the adjoint of `op A`. -/
private theorem adjoint_op_eq :
    LinearMap.adjoint (op A) = op Aᵀ := by
  rw [← Matrix.toEuclideanLin_conjTranspose A, Matrix.conjTranspose_eq_transpose_of_trivial]

/-- **Proposition 6.22**. Assume that `A` is such that `Aᵀ v ∈ 𝒦_s(A, v)` for every vector `v`.
Then DIOM(s) is mathematically equivalent to FOM: the Arnoldi coefficients satisfy
`h_{ij} = 0` for `i + s ≤ j` (6.108), so the incomplete orthogonalization process of Algorithm
6.6 with window `s` coincides with the full process of Algorithm 6.2, IOM(s) computes the FOM
iterate, and so does DIOM(s). -/
theorem prop_6_22 {s : ℕ} (hs : ∀ w : EuclideanSpace ℝ (Fin n), op Aᵀ w ∈ krylov A w s)
    (b x₀ : EuclideanSpace ℝ (Fin n)) (hr : r₀ A b x₀ ≠ 0) {m : ℕ}
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) s) l l ≠ 0) :
    (∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → ∀ i j : ℕ, i + s ≤ j →
        arnoldiCoeff A v i j = 0) ∧
      (∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → iop A v s = arnoldiMGS A v) ∧
      iomFixed A b x₀ s m = fomFixed A b x₀ m ∧ diom A b x₀ s m = fomFixed A b x₀ m := by
  have hadj : ∀ w : EuclideanSpace ℝ (Fin n), LinearMap.adjoint (op A) w ∈ krylov A w s := by
    intro w
    rw [adjoint_op_eq A]
    exact hs w
  have h108 : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → ∀ i j : ℕ, i + s ≤ j →
      arnoldiCoeff A v i j = 0 :=
    fun v hv _ _ h => arnoldiCoeff_eq_zero_of_adjoint_mem A v hadj hv h
  have hv : ‖v₁ A b x₀‖ = 1 := norm_v₁ A b x₀ hr
  exact ⟨h108, fun v hvu => iop_eq_arnoldiMGS_fun hvu (h108 v hvu),
    iomFixed_eq_fomFixed_of_band hv (h108 _ hv) m,
    diom_eq_fomFixed_of_band hv (h108 _ hv) hpiv⟩

end BookResults

/-! ### §6.10: `ν(A)`, the class `CG(s)`, and normality -/

section Normal

variable {n : ℕ}

local notation "ℂ𝔼" => EuclideanSpace ℂ (Fin n)

/-- `ν(A)` (§6.10): the least degree of a polynomial `q` with `A^H = q(A)`. The set of such
degrees is empty exactly when no polynomial in `A` equals `A^H`, in which case `ν(A) = 0` by
Lean's `sInf ∅ = 0`; by the text this happens only for non-normal `A`
(`isStarNormal_of_exists_aeval`). -/
noncomputable def ν (A : Matrix (Fin n) (Fin n) ℂ) : ℕ :=
  sInf {d : ℕ | ∃ q : ℂ[X], q.natDegree = d ∧ aeval A q = Aᴴ}

/-- Faber and Manteuffel's class **`CG(s)`** (§6.10): `A ∈ CG(s)` when, for every unit starting
vector `v_1`, the Arnoldi coefficients satisfy `h_{ij} = 0` for `i + s ≤ j ≤ μ(v_1) - 1`, so
that the Arnoldi process is an `s`-term recurrence up to the grade `μ(v_1)` of `v_1`. -/
def IsCGs (A : Matrix (Fin n) (Fin n) ℂ) (s : ℕ) : Prop :=
  ∀ v₁ : ℂ𝔼, ‖v₁‖ = 1 → ∀ i j : ℕ, i + s ≤ j → j + 1 ≤ grade A v₁ → arnoldiCoeff A v₁ i j = 0

/-- Every polynomial in `A` commutes with `A`. -/
private theorem commute_aeval_self (A : Matrix (Fin n) (Fin n) ℂ) (q : ℂ[X]) :
    Commute (aeval A q) A := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr => rw [map_add]; exact hp.add_left hr
  | monomial k c =>
    rw [Polynomial.aeval_monomial]
    have h1 : Commute (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) c) A := Algebra.commutes c A
    exact Commute.mul_left h1 ((Commute.refl A).pow_left k)

/-- **§6.10**: if `A^H = q(A)` for some polynomial `q`, then `A` is normal, because `A` commutes
with every polynomial in itself. -/
theorem isStarNormal_of_exists_aeval {A : Matrix (Fin n) (Fin n) ℂ}
    (h : ∃ q : ℂ[X], aeval A q = Aᴴ) : IsStarNormal A := by
  obtain ⟨q, hq⟩ := h
  refine ⟨?_⟩
  rw [Matrix.star_eq_conjTranspose, ← hq]
  exact commute_aeval_self A q

-- BACKBONE DEMAND: `exists_aeval_eq_conjTranspose_of_isStarNormal` needs the spectral theorem
-- for normal matrices — a normal `A` is unitarily diagonalizable, and any `q` interpolating
-- `z ↦ z̄` at its distinct eigenvalues satisfies `q(A) = A^H`. Mathlib has `IsStarNormal` and
-- `Lagrange.interpolate` but neither Schur triangulation nor unitary diagonalization of normal
-- matrices, and this is deferred backbone material
-- (`tracker/saadsparse-ch6.md` §4, item 2, a candidate `Numlib/Eigen/Normal.lean`), not
-- surface material: proving it here would be new mathematics in the surface layer. Lemma 6.23
-- and Theorem 6.24 wait on the same item. Only the existence of `q` is demanded; the degree
-- bound of the text is derived from it in `exists_aeval_eq_conjTranspose` below.
/-- **§6.10**: conversely, a normal `A` satisfies `A^H = q(A)` for some polynomial `q`: writing
`A = Q Λ Q^H`, any `q` with `q(λ_j) = conj λ_j` at the eigenvalues does. -/
theorem exists_aeval_eq_conjTranspose_of_isStarNormal {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : IsStarNormal A) : ∃ q : ℂ[X], aeval A q = Aᴴ := by
  sorry

/-- **§6.10**: a normal `A` satisfies `A^H = q(A)` for a polynomial `q` of degree at most
`n - 1`. Reducing any polynomial with `q(A) = A^H` modulo the characteristic polynomial, which
is monic of degree `n` and annihilates `A` by the Cayley–Hamilton theorem, lowers its degree
below `n` without changing `q(A)`. -/
theorem exists_aeval_eq_conjTranspose {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A) :
    ∃ q : ℂ[X], q.natDegree ≤ n - 1 ∧ aeval A q = Aᴴ := by
  obtain ⟨q, hq⟩ := exists_aeval_eq_conjTranspose_of_isStarNormal hA
  have hmonic := A.charpoly_monic
  have hlt : (q %ₘ A.charpoly).degree < A.charpoly.degree := degree_modByMonic_lt q hmonic
  have hcd : A.charpoly.degree = (n : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, A.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  refine ⟨q %ₘ A.charpoly, ?_, ?_⟩
  · rcases eq_or_ne (q %ₘ A.charpoly) 0 with h0 | h0
    · simp [h0]
    · rw [Polynomial.degree_eq_natDegree h0, hcd] at hlt
      have hn : (q %ₘ A.charpoly).natDegree < n := by exact_mod_cast hlt
      omega
  · rw [aeval_modByMonic_eq_self_of_root (by rw [Matrix.aeval_self_charpoly]), hq]

end Normal

end SaadSparse.Ch06
