import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Numlib.Analysis.Normed.Algebra.PrimaryFunctionalCalculus.Basic
import Numlib.LinearAlgebra.Matrix.Jordan

/-!
# Functions of matrices: the matrix forms of the primary functional calculus

For a square matrix `A` over a nontrivially normed field `𝕜` and a function `f : 𝕜 → 𝕜`, the
matrix function `f(A)` is `pfc f A`, the primary functional calculus of
`Numlib/Analysis/Normed/Algebra/PrimaryFunctionalCalculus/Basic`: the Hermite interpolant of `f`
on the eigenvalues of `A`, to their indices, evaluated at `A`. This module collects its matrix
forms ([golub2013matrix] §9.1.1–9.1.2): similarity, diagonal, block diagonal and reindexed
matrices, Jordan blocks and the Jordan-form expression that is the book's definition (9.1.3),
the transpose, and realness on real matrices read in `ℂ`.

## Main results

* `Matrix.pfc_conj`: `f(P A P⁻¹) = P f(A) P⁻¹` ([golub2013matrix] (9.1.8), with `X` and `X⁻¹` in
  the printed formula exchanged).
* `Matrix.pfc_diagonal`, `Matrix.pfc_blockDiagonal'`, `Matrix.pfc_fromBlocks_zero`,
  `Matrix.pfc_reindex`: diagonal and block diagonal matrices.
* `Matrix.pfc_jordanBlock`, `Matrix.pfc_jordanBlock_apply`: a Jordan block ((9.1.4)–(9.1.6)).
* `Matrix.pfc_conj_jordanForm`: the Jordan-form expression (9.1.3), a theorem here.
* `Matrix.pfc_transpose`: `f(Aᵀ) = f(A)ᵀ`.
* `Matrix.pfc_map_conj`, `Matrix.pfc_map_ofReal_of_conj`: `f(Ā) = (f̄(A))‾` for
  `f̄ = conj ∘ f ∘ conj`, hence `f(A)` is real for a real `A` when `f` commutes with conjugation
  near the spectrum.

## Implementation notes

`Matrix n n 𝕜` is finite-dimensional, so every matrix is integral (`Algebra.IsIntegral.isIntegral`);
the splitting of the minimal polynomial is the only hypothesis `pfc` needs, and it is automatic
over an algebraically closed field (`IsAlgClosed.splits`). Most results here need not even that:
they go through `pfc_eq_aeval_of_isJetInterpolant` with an explicit multiset of eigenvalues (the
diagonal entries, the eigenvalue of a Jordan block) or through algebra equivalences
(`AlgEquiv.map_pfc`, similarity, reindexing, the transpose).
-/

open Polynomial Hermite

/-- The Hermite interpolant of the jets of `f` takes the value `f x` at every node `x`. (Natural
home `Numlib/Analysis/Calculus/HermiteInterpolation`.) -/
theorem Hermite.eval_interpolateJet_taylorJet {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [DecidableEq 𝕜] {f : 𝕜 → 𝕜} {s : Multiset 𝕜} {x : 𝕜} (hx : x ∈ s) :
    (interpolateJet s (taylorJet f)).eval x = f x := by
  have := isJetInterpolant_iff_coeff_taylor.mp (isJetInterpolant_interpolateJet s (taylorJet f))
    x hx 0 (Multiset.count_pos.mpr hx)
  rwa [taylor_coeff_zero, taylorJet_zero] at this

section AlgEquiv

variable {𝕜 A B : Type*} [NontriviallyNormedField 𝕜] [Ring A] [Algebra 𝕜 A] [Ring B]
  [Algebra 𝕜 B]

/-- **Naturality under algebra equivalences**, with no hypothesis on `a`: an algebra equivalence
preserves the minimal polynomial. (Algebra-level; natural home
`Numlib/Analysis/Normed/Algebra/PrimaryFunctionalCalculus/Basic`, beside `AlgHom.map_pfc`.) -/
theorem AlgEquiv.map_pfc (φ : A ≃ₐ[𝕜] B) (f : 𝕜 → 𝕜) (a : A) : φ (pfc f a) = pfc f (φ a) := by
  classical
  rw [pfc_def, pfc_def, minpoly.algEquiv_eq, ← aeval_algHom_apply]

/-- Conjugation by a unit as an algebra automorphism. -/
private def unitsConjAlgEquiv (u : Aˣ) : A ≃ₐ[𝕜] A where
  toFun x := u * x * ↑u⁻¹
  invFun x := ↑u⁻¹ * x * u
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]
  map_mul' x y := by simp [mul_assoc]
  map_add' x y := by simp [mul_add, add_mul]
  commutes' c := by simp [Algebra.commutes, mul_assoc]

/-- **Similarity** in any algebra: `f(u a u⁻¹) = u f(a) u⁻¹` for a unit `u`. -/
theorem pfc_units_conj (u : Aˣ) (f : 𝕜 → 𝕜) (a : A) :
    pfc f (u * a * ↑u⁻¹) = u * pfc f a * ↑u⁻¹ :=
  ((unitsConjAlgEquiv u).map_pfc f a).symm

end AlgEquiv

namespace Matrix

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Similarity, diagonal and block diagonal matrices -/

/-- **Similarity** ([golub2013matrix] (9.1.8), printed there as `f(X⁻¹AX) = X f(A) X⁻¹`, with `X`
and `X⁻¹` exchanged): `f(P A P⁻¹) = P f(A) P⁻¹` for an invertible `P`. -/
theorem pfc_conj {P : Matrix n n 𝕜} (hP : IsUnit P) (f : 𝕜 → 𝕜) (A : Matrix n n 𝕜) :
    pfc f (P * A * P⁻¹) = P * pfc f A * P⁻¹ := by
  have h := pfc_units_conj (𝕜 := 𝕜) hP.unit f A
  rwa [coe_units_inv, IsUnit.unit_spec] at h

/-- The minimal polynomial of `A` divides the nodal polynomial of any multiset of scalars whose
nodal polynomial vanishes at `A`. -/
private theorem minpoly_dvd_of_aeval_eq_zero {A : Matrix n n 𝕜} {s : Multiset 𝕜}
    (h : aeval A (nodalMultiset s) = 0) : minpoly 𝕜 A ∣ nodalMultiset s :=
  minpoly.dvd 𝕜 A h

/-- **Diagonal matrices**: `f(diag(d)) = diag(f ∘ d)`, with no hypothesis on `f`. -/
theorem pfc_diagonal (f : 𝕜 → 𝕜) (d : n → 𝕜) : pfc f (diagonal d) = diagonal (f ∘ d) := by
  classical
  set s := (Finset.univ.image d).val
  have hs : s.Nodup := Finset.nodup _
  have hmem : ∀ i, d i ∈ s := fun i => Finset.mem_image_of_mem d (Finset.mem_univ i)
  have hdiag : ∀ p : 𝕜[X], aeval (diagonal d) p = diagonal fun i => p.eval (d i) := fun p => by
    rw [← diagonalAlgHom_apply 𝕜, aeval_algHom_apply, aeval_pi_apply]
    simp [coe_aeval_eq_eval]
  have hdvd : minpoly 𝕜 (diagonal d) ∣ nodalMultiset s := by
    refine minpoly_dvd_of_aeval_eq_zero ?_
    rw [hdiag, ← diagonal_zero]
    congr 1
    funext i
    rw [eval_nodalMultiset]
    exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨d i, hmem i, sub_self _⟩)
  have hP := isJetInterpolant_interpolateJet s (taylorJet f)
  rw [pfc_eq_aeval_of_isJetInterpolant hdvd hP, hdiag]
  congr 1
  funext i
  exact eval_interpolateJet_taylorJet (hmem i)

section BlockDiagonal

variable {o : Type*} [Fintype o] [DecidableEq o] {m : o → Type*} [∀ i, Fintype (m i)]
  [∀ i, DecidableEq (m i)]

/-- Polynomials commute with `blockDiagonal'`. -/
theorem aeval_blockDiagonal' (M : ∀ i, Matrix (m i) (m i) 𝕜) (p : 𝕜[X]) :
    aeval (blockDiagonal' M) p = blockDiagonal' fun i => aeval (M i) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq, ← blockDiagonal'_add]
    congr 1
    funext i
    rw [Pi.add_apply, map_add]
  | monomial k c =>
    simp only [aeval_monomial, ← Algebra.smul_def, ← blockDiagonal'_pow, ← blockDiagonal'_smul]
    rfl

/-- **Block diagonal matrices**: `f(diag(M₁, …, M_k)) = diag(f(M₁), …, f(M_k))`, when every
block has a split minimal polynomial (automatic over `ℂ`). -/
theorem pfc_blockDiagonal' {M : ∀ i, Matrix (m i) (m i) 𝕜}
    (hs : ∀ i, (minpoly 𝕜 (M i)).Splits) (f : 𝕜 → 𝕜) :
    pfc f (blockDiagonal' M) = blockDiagonal' fun i => pfc f (M i) := by
  classical
  set s := ∑ i, (minpoly 𝕜 (M i)).roots
  have hdvd : ∀ i, minpoly 𝕜 (M i) ∣ nodalMultiset s := fun i =>
    (minpoly_dvd_nodalMultiset_roots (Algebra.IsIntegral.isIntegral _) (hs i)).trans
      (nodalMultiset_dvd_nodalMultiset
        (Finset.single_le_sum (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)))
  have hdvd' : minpoly 𝕜 (blockDiagonal' M) ∣ nodalMultiset s := by
    refine minpoly_dvd_of_aeval_eq_zero ?_
    rw [aeval_blockDiagonal', ← blockDiagonal'_zero]
    congr 1
    funext i
    exact (minpoly.dvd_iff).mp (hdvd i)
  have hP := isJetInterpolant_interpolateJet s (taylorJet f)
  rw [pfc_eq_aeval_of_isJetInterpolant hdvd' hP, aeval_blockDiagonal']
  congr 1
  funext i
  exact (pfc_eq_aeval_of_isJetInterpolant (hdvd i) hP).symm

end BlockDiagonal

section FromBlocks

variable {l : Type*} [Fintype l] [DecidableEq l]

/-- Polynomials commute with block diagonal `fromBlocks`. -/
theorem aeval_fromBlocks_zero (B : Matrix l l 𝕜) (C : Matrix n n 𝕜) (p : 𝕜[X]) :
    aeval (fromBlocks B 0 0 C) p = fromBlocks (aeval B p) 0 0 (aeval C p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq, map_add, map_add, fromBlocks_add]
    simp only [add_zero]
  | monomial k c =>
    simp only [aeval_monomial, ← Algebra.smul_def, fromBlocks_diagonal_pow, fromBlocks_smul,
      smul_zero]

/-- **Two diagonal blocks**: `f([B 0; 0 C]) = [f(B) 0; 0 f(C)]`. -/
theorem pfc_fromBlocks_zero {B : Matrix l l 𝕜} {C : Matrix n n 𝕜} (hB : (minpoly 𝕜 B).Splits)
    (hC : (minpoly 𝕜 C).Splits) (f : 𝕜 → 𝕜) :
    pfc f (fromBlocks B 0 0 C) = fromBlocks (pfc f B) 0 0 (pfc f C) := by
  classical
  set s := (minpoly 𝕜 B).roots + (minpoly 𝕜 C).roots
  have hdB : minpoly 𝕜 B ∣ nodalMultiset s :=
    (minpoly_dvd_nodalMultiset_roots (Algebra.IsIntegral.isIntegral _) hB).trans
      (nodalMultiset_dvd_nodalMultiset (Multiset.le_add_right _ _))
  have hdC : minpoly 𝕜 C ∣ nodalMultiset s :=
    (minpoly_dvd_nodalMultiset_roots (Algebra.IsIntegral.isIntegral _) hC).trans
      (nodalMultiset_dvd_nodalMultiset (Multiset.le_add_left _ _))
  have hd : minpoly 𝕜 (fromBlocks B 0 0 C) ∣ nodalMultiset s := by
    refine minpoly_dvd_of_aeval_eq_zero ?_
    rw [aeval_fromBlocks_zero, minpoly.dvd_iff.mp hdB, minpoly.dvd_iff.mp hdC, fromBlocks_zero]
  have hP := isJetInterpolant_interpolateJet s (taylorJet f)
  rw [pfc_eq_aeval_of_isJetInterpolant hd hP, aeval_fromBlocks_zero,
    pfc_eq_aeval_of_isJetInterpolant hdB hP, pfc_eq_aeval_of_isJetInterpolant hdC hP]

end FromBlocks

/-- **Reindexing**: `f(reindex e e A) = reindex e e (f(A))`. -/
theorem pfc_reindex {l : Type*} [Fintype l] [DecidableEq l] (e : n ≃ l) (f : 𝕜 → 𝕜)
    (A : Matrix n n 𝕜) : pfc f (reindex e e A) = reindex e e (pfc f A) :=
  ((reindexAlgEquiv 𝕜 𝕜 e).map_pfc f A).symm

/-! ### Jordan blocks and the Jordan form -/

section Jordan

variable (f : 𝕜 → 𝕜) (k : ℕ) (μ : 𝕜)

/-- The nodal polynomial of `k` copies of `μ`. -/
private theorem nodalMultiset_replicate :
    nodalMultiset (Multiset.replicate k μ) = (X - C μ) ^ k := by
  simp [nodalMultiset, Multiset.map_replicate, Multiset.prod_replicate]

/-- **A Jordan block** ([golub2013matrix] (9.1.5)–(9.1.6)):
`f(J_k(μ)) = ∑_{j<k} f⁽ʲ⁾(μ)/j! N^j` with `N = J_k(0)` the nilpotent shift. No hypothesis on `f`. -/
theorem pfc_jordanBlock :
    pfc f (jordanBlock k μ) = ∑ j ∈ Finset.range k, taylorJet f μ j • jordanBlock k 0 ^ j := by
  classical
  have hdvd : minpoly 𝕜 (jordanBlock k μ) ∣ nodalMultiset (Multiset.replicate k μ) := by
    rw [nodalMultiset_replicate, ← charpoly_jordanBlock]
    exact minpoly_dvd_charpoly _
  have hP : IsJetInterpolant (Multiset.replicate k μ) (taylorJet f)
      (jetPoly (taylorJet f μ) μ k) := by
    intro x hx
    obtain rfl := Multiset.eq_of_mem_replicate hx
    rw [Multiset.count_replicate_self, sub_self]
    exact dvd_zero _
  rw [pfc_eq_aeval_of_isJetInterpolant hdvd hP, jetPoly, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, aeval_C, map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one μ,
    jordanBlock_sub_smul_one, sub_self, ← Algebra.smul_def]

/-- **The entries of `f` of a Jordan block** ([golub2013matrix] (9.1.4)): upper triangular Toeplitz,
`f(J_k(μ))_{ij} = f⁽ʲ⁻ⁱ⁾(μ)/(j - i)!` for `i ≤ j`. -/
theorem pfc_jordanBlock_apply (i j : Fin k) :
    pfc f (jordanBlock k μ) i j = if i ≤ j then taylorJet f μ (j - i) else 0 := by
  rw [pfc_jordanBlock, sum_apply]
  simp only [smul_apply, jordanBlock_zero_pow_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single ((j : ℕ) - i) (fun b _ hb => ?_) (fun hb => ?_)]
    · rw [ite_eq_left_iff.mpr]; intro h'; exact absurd (by rw [Fin.le_def] at h; omega) h'
    · rw [ite_eq_right_iff.mpr]; intro h'; omega
    · exact absurd (Finset.mem_range.mpr (by omega)) hb
  · exact Finset.sum_eq_zero fun b _ => by
      rw [ite_eq_right_iff.mpr]; intro h'; rw [Fin.le_def] at h; omega

/-- A Jordan block has a split minimal polynomial. -/
theorem splits_minpoly_jordanBlock : (minpoly 𝕜 (jordanBlock k μ)).Splits := by
  refine (splits_nodalMultiset (Multiset.replicate k μ)).of_dvd
    (monic_nodalMultiset _).ne_zero ?_
  rw [nodalMultiset_replicate, ← charpoly_jordanBlock]
  exact minpoly_dvd_charpoly _

end Jordan

/-- **The Jordan-form expression** ([golub2013matrix] (9.1.3), the book's definition of `f(A)`, a
theorem here): if `P⁻¹ A P` is the Jordan form with blocks `J_{e i}(μ i)`, then
`f(A) = P diag(f(J_{e i}(μ i))) P⁻¹`. In particular the right side does not depend on the Jordan
decomposition. Each block is given by `Matrix.pfc_jordanBlock`. -/
theorem pfc_conj_jordanForm {ι : Type*} [Finite ι] [DecidableEq ι] {e : ι → ℕ} {μ : ι → 𝕜}
    (σ : (Σ i, Fin (e i)) ≃ n) {A P : Matrix n n 𝕜} (hP : IsUnit P)
    (h : P⁻¹ * A * P = reindex σ σ (jordanForm e μ)) (f : 𝕜 → 𝕜) :
    pfc f A =
      P * reindex σ σ (blockDiagonal' fun i => pfc f (jordanBlock (e i) (μ i))) * P⁻¹ := by
  have := Fintype.ofFinite ι
  have hdet := (isUnit_iff_isUnit_det P).mp hP
  have hA : A = P * (P⁻¹ * A * P) * P⁻¹ := by
    simp only [← mul_assoc, mul_nonsing_inv _ hdet, one_mul]
    rw [mul_assoc, mul_nonsing_inv _ hdet, mul_one]
  rw [hA, pfc_conj hP, h, pfc_reindex, jordanForm_def,
    pfc_blockDiagonal' fun i => splits_minpoly_jordanBlock _ _]

/-! ### The transpose -/

/-- Polynomials commute with the transpose. -/
theorem aeval_transpose (A : Matrix n n 𝕜) (p : 𝕜[X]) : aeval Aᵀ p = (aeval A p)ᵀ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, map_add, transpose_add]
  | monomial k c =>
    simp only [aeval_monomial, ← Algebra.smul_def, transpose_smul, transpose_pow]

/-- A matrix and its transpose have the same minimal polynomial. -/
theorem minpoly_transpose (A : Matrix n n 𝕜) : minpoly 𝕜 Aᵀ = minpoly 𝕜 A := by
  have hA : IsIntegral 𝕜 A := Algebra.IsIntegral.isIntegral _
  refine (minpoly.unique 𝕜 Aᵀ (minpoly.monic hA) ?_ fun q hq h0 => ?_).symm
  · rw [aeval_transpose, minpoly.aeval, transpose_zero]
  · refine minpoly.min 𝕜 A hq ?_
    rw [← transpose_transpose A, aeval_transpose, h0, transpose_zero]

/-- **The transpose**: `f(Aᵀ) = f(A)ᵀ`. -/
theorem pfc_transpose (f : 𝕜 → 𝕜) (A : Matrix n n 𝕜) : pfc f Aᵀ = (pfc f A)ᵀ := by
  classical
  rw [pfc_def, pfc_def, minpoly_transpose, aeval_transpose]

/-! ### Complex conjugation and real matrices -/

section Conj

open ComplexConjugate

/-- The iterated derivatives of `conj ∘ f ∘ conj` are `conj ∘ f⁽ʲ⁾ ∘ conj`, junk values included. -/
theorem _root_.iteratedDeriv_conj_conj (f : ℂ → ℂ) (j : ℕ) :
    iteratedDeriv j (conj ∘ f ∘ conj) = conj ∘ iteratedDeriv j f ∘ conj := by
  induction j with
  | zero => simp
  | succ j ih => rw [iteratedDeriv_succ, ih, deriv_conj_conj, iteratedDeriv_succ]

/-- Polynomials commute with an entrywise ring endomorphism of the scalars. -/
theorem map_aeval (φ : 𝕜 →+* 𝕜) (A : Matrix n n 𝕜) (p : 𝕜[X]) :
    (aeval A p).map φ = aeval (A.map φ) (p.map φ) := by
  change φ.mapMatrix (aeval A p) = aeval (φ.mapMatrix A) (p.map φ)
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, Polynomial.map_add, map_add, hp, hq]
  | monomial k c =>
    have hc : φ.mapMatrix (algebraMap 𝕜 (Matrix n n 𝕜) c) = algebraMap 𝕜 (Matrix n n 𝕜) (φ c) := by
      ext i j
      by_cases h : i = j <;> simp [algebraMap_eq_diagonal, h]
    rw [aeval_monomial, Polynomial.map_monomial, aeval_monomial, map_mul, map_pow, hc]

/-- **Conjugation** ([golub2013matrix] §9.1): `f(Ā) = (f̄(A))‾` for `f̄ = conj ∘ f ∘ conj`, with no
hypothesis on `f`. -/
theorem pfc_map_conj (f : ℂ → ℂ) (A : Matrix n n ℂ) :
    pfc f (A.map conj) = (pfc (conj ∘ f ∘ conj) A).map conj := by
  classical
  set s := (minpoly ℂ A).roots
  set P := interpolateJet s (taylorJet (conj ∘ f ∘ conj))
  have hP := isJetInterpolant_interpolateJet s (taylorJet (conj ∘ f ∘ conj))
  have hA : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral _
  have hnodal : nodalMultiset (s.map conj) = (nodalMultiset s).map conj := by
    simp [nodalMultiset, Polynomial.map_multiset_prod, Multiset.map_map]
  have hdvd : minpoly ℂ (A.map conj) ∣ nodalMultiset (s.map conj) := by
    refine minpoly.dvd ℂ _ ?_
    rw [hnodal, ← map_aeval,
      minpoly.dvd_iff.mp (minpoly_dvd_nodalMultiset_roots hA (IsAlgClosed.splits _))]
    exact Matrix.map_zero _ (map_zero _)
  have hP' : IsJetInterpolant (s.map conj) (taylorJet f) (P.map conj) := by
    refine isJetInterpolant_iff_coeff_taylor.mpr fun x hx j hj => ?_
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    rw [Multiset.count_map_eq_count' _ _ (RingHom.injective _)] at hj
    rw [← map_taylor, coeff_map, isJetInterpolant_iff_coeff_taylor.mp hP y hy j hj, taylorJet,
      taylorJet, iteratedDeriv_conj_conj, map_div₀, map_natCast]
    simp
  rw [pfc_eq_aeval_of_isJetInterpolant hdvd hP', pfc_def, map_aeval]

/-- **Real matrices** ([golub2013matrix] §9.1): if `A` is real and `f` commutes with conjugation
near every eigenvalue (e.g. `exp`, `sin`, `cos`, and `Complex.log` or `z ^ (1/2)` when no eigenvalue
lies on `(-∞, 0]`), then `f(A)` is real. -/
theorem pfc_map_ofReal_of_conj {f : ℂ → ℂ} (B : Matrix n n ℝ)
    (hf : ∀ μ ∈ spectrum ℂ (B.map Complex.ofReal), (conj ∘ f ∘ conj) =ᶠ[nhds μ] f) :
    ∃ C : Matrix n n ℝ, pfc f (B.map Complex.ofReal) = C.map Complex.ofReal := by
  set A := B.map Complex.ofReal
  have hA : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral _
  have hconj : A.map conj = A := by
    ext i j
    simp [A]
  have h1 : pfc f A = (pfc (conj ∘ f ∘ conj) A).map conj := by rw [← pfc_map_conj, hconj]
  have h2 : pfc (conj ∘ f ∘ conj) A = pfc f A := pfc_congr fun μ hμ j _ =>
    (hf μ ((spectrum.mem_iff_isRoot_minpoly hA).mpr
      ((Polynomial.mem_roots (minpoly.ne_zero hA)).mp hμ))).iteratedDeriv_eq j
  have hfix : (pfc f A).map conj = pfc f A := by
    rw [h2] at h1
    exact h1.symm
  refine ⟨(pfc f A).map Complex.re, ?_⟩
  ext i j
  have h := congrFun (congrFun hfix i) j
  simp only [map_apply] at h ⊢
  exact (Complex.conj_eq_iff_re.mp h).symm

end Conj

end Matrix
