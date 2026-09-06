import Mathlib.Analysis.Complex.Polynomial.Basic
import Numlib.Eigen.Normal
import Numlib.Krylov.Arnoldi
import Numlib.Krylov.Subspace
import NumlibSurface.SaadSparse.Chapter06.Section09

/-!
# Saad §6.10: optimality and the Faber–Manteuffel condition

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §6.10.

**Proposition 6.22** says that when `Aᵀ v ∈ 𝒦_s(A, v)` for every `v`, the Arnoldi coefficients
obey the band condition `h_{ij} = 0` for `i + s ≤ j` (6.108), so that the incomplete
orthogonalization process of Algorithm 6.6 with a window of `s` drops nothing and DIOM(s)
computes the FOM approximation. The band condition itself is the backbone's
`Arnoldi.coeff_eq_zero_of_adjoint_mem` (`Numlib/Krylov/Arnoldi.lean`); the algorithmic
consequence is `iop_eq_arnoldiMGS_of_band` (IOP(s) is Algorithm 6.2) together with
`iomFixed_eq_fomFixed_of_band` and `diom_eq_fomFixed_of_band`, which use the IOP/DIOM layer of
`Chapter06/Section04.lean`.

The section's two objects are here: `ν A`, the least degree of a polynomial `q` with
`A^H = q(A)`, and `IsCGs A s`, Faber and Manteuffel's class `CG(s)` of matrices for which the
Arnoldi process is an `s`-term recurrence for every starting vector. The text's two remarks
about normality are `isStarNormal_of_exists_aeval` (if `A^H = q(A)` then `A` is normal, since
`A` commutes with every polynomial in `A`) and `exists_aeval_eq_conjTranspose` (the converse).

The converse is the backbone's `Matrix.IsStarNormal.exists_aeval_eq_conjTranspose`
(`Numlib/Eigen/Normal.lean`): a normal operator is diagonalizable and shares its eigenvectors
with its adjoint, so Lagrange interpolation of `z ↦ conj z` at its eigenvalues produces `q`.

**Lemma 6.23** (Faber and Manteuffel) is `lemma_6_23`: `A^H v ∈ 𝒦_s(A, v)` for every `v` iff `A`
is normal with `ν(A) ≤ s - 1`. Its proof departs from the book's twice, and both departures are
recorded on the declaration: the eigenvector-sum argument replaces the book's maximal vector, and
the book's nonsingularity hypothesis is not needed, while a missing `0 < s` is.

**Left out**: **Theorem 6.24** (Faber–Manteuffel: `A ∈ CG(s)` iff the minimal polynomial of `A` has
degree `≤ s`, or `A` is normal with `ν(A) ≤ s - 1`), which the book itself states without proof; the
known proofs are research-level (`plans/saadsparse-ch6.md` §5).

Proposition 6.22 is stated over `ℝ` with `Aᵀ`, and §6.10's normality material over `ℂ` with
`A^H`, following the book. The band lemmas are polymorphic in `𝕜`.
-/

open Polynomial

open scoped ComplexOrder Matrix

namespace SaadSparse.Chapter06

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
theorem proposition_6_22 {s : ℕ} (hs : ∀ w : EuclideanSpace ℝ (Fin n), op Aᵀ w ∈ krylov A w s)
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

/-- **§6.10**: conversely, a normal `A` satisfies `A^H = q(A)` for some polynomial `q`: writing
`A = Q Λ Q^H`, any `q` with `q(λ_j) = conj λ_j` at the eigenvalues does. This is the backbone's
`Matrix.IsStarNormal.exists_aeval_eq_conjTranspose`, which builds `q` by Lagrange interpolation
of `z ↦ conj z` at the eigenvalues without ever forming `Q`. -/
theorem exists_aeval_eq_conjTranspose_of_isStarNormal {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : IsStarNormal A) : ∃ q : ℂ[X], aeval A q = Aᴴ :=
  Matrix.IsStarNormal.exists_aeval_eq_conjTranspose hA

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

/-! ### Lemma 6.23 -/

/-- For a normal `A` the set of degrees whose infimum is `ν(A)` is nonempty, so the infimum is
attained: some `q` of degree exactly `ν(A)` satisfies `q(A) = A^H`. -/
theorem exists_natDegree_eq_nu {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A) :
    ∃ q : ℂ[X], q.natDegree = ν A ∧ aeval A q = Aᴴ := by
  have hne : {d : ℕ | ∃ q : ℂ[X], q.natDegree = d ∧ aeval A q = Aᴴ}.Nonempty := by
    obtain ⟨q, hq⟩ := exists_aeval_eq_conjTranspose_of_isStarNormal hA
    exact ⟨q.natDegree, q, rfl, hq⟩
  exact Nat.sInf_mem hne

/-- `ν(A)` is a lower bound: any `q` with `q(A) = A^H` has degree at least `ν(A)`. -/
theorem nu_le_natDegree {A : Matrix (Fin n) (Fin n) ℂ} {q : ℂ[X]} (hq : aeval A q = Aᴴ) :
    ν A ≤ q.natDegree :=
  Nat.sInf_le ⟨q, rfl, hq⟩

/-- **Lemma 6.23** (Faber and Manteuffel). `A` satisfies `A^H v ∈ 𝒦_s(A, v)` for every vector `v`
if and only if `A` is normal and `ν(A) ≤ s - 1`.

The proof of `→` is not the book's. At an eigenvector `v` of `A` the subspace `𝒦_s(A, v)` sits
inside `span {v}`, so `A^H v` is a multiple of `v`: every eigenvector of `A` is an eigenvector of
`A^H`, and `A` is normal by Saad's Lemma 1.15
(`LinearMap.isStarNormal_of_adjoint_apply_eq_smul`). Where the book then takes a vector `w` whose
grade is the degree `μ` of the minimal polynomial and argues that `μ ≤ s`, we take
`w = ∑ x_i` with one nonzero `x_i` from each eigenspace: the `x_i` are pairwise orthogonal, so the
polynomial `q` of degree `≤ s - 1` supplied by `A^H w ∈ 𝒦_s(A, w)` must satisfy
`q(λ_i) = conj λ_i` at every eigenvalue, whence `q(A) = A^H` and `ν(A) ≤ s - 1`. That route needs
neither a maximal vector nor the identity `deg (minpoly A)` = number of distinct eigenvalues, and
it does not use the book's hypothesis that `A` is nonsingular, which is therefore omitted.

The hypothesis `0 < s` is not in the book, and is not optional: `ℕ` truncates `s - 1`, so at
`s = 0` the right-hand side holds for `A = 1` (`ν(1) = 0`) while the left-hand side fails
(`𝒦_0(A, v) = ⊥`). -/
theorem lemma_6_23 {A : Matrix (Fin n) (Fin n) ℂ} {s : ℕ} (hs : 0 < s) :
    (∀ v : ℂ𝔼, op Aᴴ v ∈ krylov A v s) ↔ IsStarNormal A ∧ ν A ≤ s - 1 := by
  have hadj : op Aᴴ = LinearMap.adjoint (op A) := Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  constructor
  · intro h
    classical
    have hev : ∀ (μ : ℂ) (y : ℂ𝔼), op A y = μ • y →
        ∃ ν : ℂ, LinearMap.adjoint (op A) y = ν • y := by
      intro μ y hy
      obtain ⟨p, _, hpy⟩ := (mem_krylov_iff_exists_aeval A y).1 (h y)
      exact ⟨p.eval μ, by rw [← hadj, ← hpy]; exact Module.End.aeval_apply_of_mem_apply_eq_smul hy⟩
    have hT : IsStarNormal (op A) := LinearMap.isStarNormal_of_adjoint_apply_eq_smul hev
    refine ⟨Matrix.isStarNormal_toEuclideanLin_iff.1 hT, ?_⟩
    obtain ⟨S, hS⟩ : ∃ S : Finset ℂ, ∀ μ : ℂ, μ ∈ S ↔ Module.End.HasEigenvalue (op A) μ :=
      ⟨(Module.End.finite_hasEigenvalue (op A)).toFinset, fun _ => Set.Finite.mem_toFinset _⟩
    have hexists : ∀ μ : ℂ, ∃ y : ℂ𝔼, μ ∈ S →
        y ∈ Module.End.eigenspace (op A) μ ∧ y ≠ 0 := by
      intro μ
      by_cases hμ : μ ∈ S
      · obtain ⟨y, hy⟩ := Module.End.HasEigenvalue.exists_hasEigenvector ((hS μ).1 hμ)
        exact ⟨y, fun _ => ⟨hy.1, hy.2⟩⟩
      · exact ⟨0, fun hc => absurd hc hμ⟩
    choose x hx using hexists
    obtain ⟨w, hw⟩ : ∃ w : ℂ𝔼, w = ∑ μ ∈ S, x μ := ⟨_, rfl⟩
    obtain ⟨p, hpdeg, hpw⟩ := (mem_krylov_iff_exists_aeval A w).1 (h w)
    have hAdjw : LinearMap.adjoint (op A) w = ∑ μ ∈ S, starRingEnd ℂ μ • x μ := by
      rw [hw, map_sum]
      refine Finset.sum_congr rfl fun μ hμ => Module.End.mem_eigenspace_iff.1 ?_
      rw [LinearMap.IsStarNormal.eigenspace_adjoint hT μ]
      exact (hx μ hμ).1
    have hEvalw : aeval (op A) p w = ∑ μ ∈ S, p.eval μ • x μ := by
      rw [hw, map_sum]
      exact Finset.sum_congr rfl fun μ hμ => Module.End.aeval_apply_of_mem_apply_eq_smul
        (Module.End.mem_eigenspace_iff.1 (hx μ hμ).1)
    have hsum : ∑ μ ∈ S, (p.eval μ - starRingEnd ℂ μ) • x μ = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hEvalw, ← hAdjw, hpw, hadj, sub_self]
    have hcoef : ∀ ν ∈ S, p.eval ν = starRingEnd ℂ ν := by
      intro ν hν
      have hsingle : (∑ μ ∈ S, (inner ℂ (x ν) ((p.eval μ - starRingEnd ℂ μ) • x μ) : ℂ))
          = inner ℂ (x ν) ((p.eval ν - starRingEnd ℂ ν) • x ν) := by
        refine Finset.sum_eq_single_of_mem ν hν fun μ hμ hμν => ?_
        rw [inner_smul_right, LinearMap.IsStarNormal.inner_eq_zero_of_ne hT
          (Ne.symm hμν) (hx ν hν).1 (hx μ hμ).1, mul_zero]
      have hj : (0 : ℂ) = (p.eval ν - starRingEnd ℂ ν) * inner ℂ (x ν) (x ν) := by
        rw [← inner_smul_right, ← hsingle, ← inner_sum, hsum, inner_zero_right]
      have hxx : (inner ℂ (x ν) (x ν) : ℂ) ≠ 0 :=
        fun hc => (hx ν hν).2 (inner_self_eq_zero.1 hc)
      exact sub_eq_zero.1 ((mul_eq_zero.1 hj.symm).resolve_right hxx)
    have hqM : aeval A p = Aᴴ :=
      Matrix.aeval_eq_conjTranspose_iff.1
        (LinearMap.IsStarNormal.aeval_eq_adjoint_of_eval_eq hT
          fun μ hμ => hcoef μ ((hS μ).2 hμ))
    refine le_trans (nu_le_natDegree hqM) ?_
    rcases eq_or_ne p 0 with rfl | hp0
    · simp
    · have hlt : p.natDegree < s := (Polynomial.natDegree_lt_iff_degree_lt hp0).2 hpdeg
      omega
  · rintro ⟨hn, hν⟩ v
    obtain ⟨q, hqd, hq⟩ := exists_natDegree_eq_nu hn
    have hdeg : q.degree < (s : ℕ) := by
      rcases eq_or_ne q 0 with rfl | hq0
      · simp
      · exact (Polynomial.natDegree_lt_iff_degree_lt hq0).1 (by omega)
    rw [← hq, op_aeval]
    exact aeval_mem_krylov A v hdeg

end Normal

end SaadSparse.Chapter06
