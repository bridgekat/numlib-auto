/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: a file beside `Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Symmetric spectra and the half-sum of two involutions

Characteristic polynomials read off from traces of powers, and their application to the spectrum
of the half-sum of two symmetric involutions of trace zero (Ammar–Gragg–Reichel; the spectral half
of [golub2013matrix] §12.2.10, Fact 2).

## Main results

* `Matrix.roots_charpoly_diagonal`, `Matrix.charpoly_unitary_conj`: the roots of the
  characteristic polynomial of a diagonal matrix are its entries, and a unitary conjugation keeps
  the characteristic polynomial — the two steps from a unitary diagonalization to a spectrum;
  `Matrix.IsHermitian.star_eigenvectorUnitary_mul_mul`, `Uᴴ A U = diag(λ)` for Mathlib's
  eigenvector unitary, and its real form `Matrix.IsHermitian.transpose_eigenvectorUnitary_mul_mul`.
* `Matrix.trace_add_pow_odd_eq_zero`: if `A² = B² = 1` and `tr A = tr B = 0`, the odd powers of
  `A + B` are traceless.
* `Fintype.map_neg_eq_of_sum_pow_odd`: over a field of characteristic zero, a finite family whose
  odd power sums vanish is symmetric about `0` (as a multiset).
* `Matrix.IsHermitian.trace_pow_eq_sum`, `Matrix.IsHermitian.charpoly_neg_of_trace_pow_odd`: a
  Hermitian matrix whose odd powers are traceless has `charpoly (-A) = charpoly A`.
* `Matrix.card_eq_of_charpoly_eq_prod`: a characteristic polynomial that is a product of `m` monic
  quadratics forces order `2m`.
* `Matrix.charpoly_half_add_of_involutive`: if `A`, `B` are real symmetric involutions of trace
  zero and the eigenvalues of `AB` are the pairs `e^{±iθ_k}`, then those of `(A + B)/2` are the
  pairs `± cos(θ_k/2)`.

## References

* [golub2013matrix] §12.2.10.
-/

open Finset Polynomial

namespace Matrix

/-! ### Diagonal matrices and unitary conjugates -/

/-- The roots of the characteristic polynomial of a diagonal matrix are its diagonal entries. -/
theorem roots_charpoly_diagonal {R n : Type*} [CommRing R] [IsDomain R] [Fintype n]
    [DecidableEq n] (d : n → R) :
    (diagonal d).charpoly.roots = Multiset.map d Finset.univ.val := by
  rw [charpoly_diagonal, Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- The characteristic polynomial of a unitary conjugate `U M Uᴴ` is that of `M`. -/
theorem charpoly_unitary_conj {R n : Type*} [CommRing R] [StarRing R] [Fintype n]
    [DecidableEq n] {U : Matrix n n R} (hU : U ∈ unitaryGroup n R) (M : Matrix n n R) :
    (U * M * star U).charpoly = M.charpoly := by
  rw [charpoly_mul_comm, ← Matrix.mul_assoc, mem_unitaryGroup_iff'.1 hU, Matrix.one_mul]

/-! ### The Hermitian spectral decomposition, unfolded -/

section Spectral

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The spectral decomposition of a Hermitian matrix**, unfolded: `Uᴴ A U = diag(λ)` for the
eigenvector unitary `U` (Mathlib's `Matrix.IsHermitian.conjStarAlgAut_star_eigenvectorUnitary`
without the algebra automorphism). -/
theorem IsHermitian.star_eigenvectorUnitary_mul_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    star (hA.eigenvectorUnitary : Matrix n n 𝕜) * A * (hA.eigenvectorUnitary : Matrix n n 𝕜) =
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
  simpa [Unitary.conjStarAlgAut_apply] using hA.conjStarAlgAut_star_eigenvectorUnitary

/-- The real form of `Matrix.IsHermitian.star_eigenvectorUnitary_mul_mul`: `Qᵀ A Q = diag(λ)`. -/
theorem IsHermitian.transpose_eigenvectorUnitary_mul_mul {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ * A * (hA.eigenvectorUnitary : Matrix n n ℝ) =
      diagonal hA.eigenvalues := by
  have h := hA.star_eigenvectorUnitary_mul_mul
  rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id,
    Function.id_comp] at h

end Spectral

/-! ### Two involutions of trace zero -/

section Involution

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n R}

/-- The key step for `Matrix.trace_add_pow_odd_eq_zero`: with `Z = (A + B)²`, which commutes with
`A` and `B`, and `D = AB − BA`, which anticommutes with `A` and commutes with `Z`,
`tr (A Zʲ D²) = tr (D A Zʲ D) = −tr (A Zʲ D²)` vanishes; since `D² = Z² − 4Z`, the traces
`tr (A Zʲ)` satisfy `t_{j+2} = 4 t_{j+1}`, and `t₀ = tr A`, `t₁ = 2 tr A + 2 tr B` vanish. -/
private theorem trace_mul_sq_pow_eq_zero [NoZeroDivisors R] [CharZero R] (hA : A * A = 1)
    (hB : B * B = 1) (htA : trace A = 0) (htB : trace B = 0) (j : ℕ) :
    trace (A * ((A + B) * (A + B)) ^ j) = 0 := by
  have hA' : ∀ M, A * (A * M) = M := fun M => by rw [← Matrix.mul_assoc, hA, Matrix.one_mul]
  have hB' : ∀ M, B * (B * M) = M := fun M => by rw [← Matrix.mul_assoc, hB, Matrix.one_mul]
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = (A + B) * (A + B) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = A * B - B * A := ⟨_, rfl⟩
  rw [← hZ]
  have hZA : Commute Z A := by
    rw [Commute, SemiconjBy, hZ]
    simp only [add_mul, mul_add, Matrix.mul_assoc, hA, hB, hA', Matrix.mul_one, Matrix.one_mul]
    abel
  have hZB : Commute Z B := by
    rw [Commute, SemiconjBy, hZ]
    simp only [add_mul, mul_add, Matrix.mul_assoc, hA, hB, hB', Matrix.mul_one, Matrix.one_mul]
    abel
  have hDZ : Commute D Z := hD ▸ (hZA.symm.mul_left hZB.symm).sub_left
    (hZB.symm.mul_left hZA.symm)
  have hDA : D * A = -(A * D) := by
    rw [hD]
    simp only [sub_mul, mul_sub, Matrix.mul_assoc, hA, hA', Matrix.mul_one]
    abel
  have hDD : D * D = Z * Z - 4 • Z := by
    rw [hD, hZ]
    simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.mul_assoc, hA, hB, hA', hB',
      Matrix.mul_one, Matrix.one_mul]
    abel
  have hrec : ∀ j, trace (A * Z ^ (j + 2)) = 4 • trace (A * Z ^ (j + 1)) := fun j => by
    have h0 : trace (A * Z ^ j * (D * D)) = 0 := by
      have e : D * (A * Z ^ j * D) = -(A * Z ^ j * (D * D)) := by
        calc D * (A * Z ^ j * D) = D * A * Z ^ j * D := by simp only [Matrix.mul_assoc]
          _ = -(A * (D * Z ^ j) * D) := by
            rw [hDA]
            simp only [Matrix.neg_mul, Matrix.mul_assoc]
          _ = -(A * Z ^ j * (D * D)) := by
            rw [(hDZ.pow_right j).eq]
            simp only [Matrix.mul_assoc]
      have e' : trace (A * Z ^ j * (D * D)) = -trace (A * Z ^ j * (D * D)) := by
        rw [← trace_neg, ← e, ← Matrix.mul_assoc, trace_mul_comm]
      exact self_eq_neg.mp e'
    rw [hDD, Matrix.mul_sub, trace_sub, Matrix.mul_smul, trace_smul, sub_eq_zero] at h0
    rw [pow_succ, pow_succ, show A * (Z ^ j * Z * Z) = A * Z ^ j * (Z * Z) by
      simp only [Matrix.mul_assoc], h0, Matrix.mul_assoc]
  have hAZ : trace (A * Z) = 0 := by
    rw [hZ]
    simp only [add_mul, mul_add, hA, hB, hA', Matrix.mul_one, trace_add]
    rw [trace_mul_comm A (B * A), Matrix.mul_assoc, hA, Matrix.mul_one, htA, htB]
    simp
  have h2 : ∀ j, trace (A * Z ^ j) = 0 ∧ trace (A * Z ^ (j + 1)) = 0 := fun j => by
    induction j with
    | zero => exact ⟨by rw [pow_zero, Matrix.mul_one, htA], by rw [zero_add, pow_one, hAZ]⟩
    | succ j ih => exact ⟨ih.2, by rw [hrec, ih.2, smul_zero]⟩
  exact (h2 j).1

/-- **Odd powers of a sum of two involutions of trace zero are traceless**: if `A² = B² = 1` and
`tr A = tr B = 0` then `tr (A + B)^{2j+1} = 0`. Expanded, every odd word in `A` and `B` reduces
cyclically to a single letter; the proof runs instead through `Z = (A + B)²`, which commutes with
`A` and `B`, and the commutator `AB − BA`: the traces `tr (A Zʲ)` satisfy `t_{j+2} = 4 t_{j+1}`
with `t₀ = t₁ = 0`. -/
theorem trace_add_pow_odd_eq_zero [NoZeroDivisors R] [CharZero R] (hA : A * A = 1)
    (hB : B * B = 1) (htA : trace A = 0) (htB : trace B = 0) (j : ℕ) :
    trace ((A + B) ^ (2 * j + 1)) = 0 := by
  rw [pow_succ', pow_mul, sq, add_mul, trace_add, trace_mul_sq_pow_eq_zero hA hB htA htB,
    add_comm A B, trace_mul_sq_pow_eq_zero hB hA htB htA, add_zero]

end Involution

end Matrix

/-! ### Symmetric spectra from odd power sums -/

section PowerSum

variable {ι K : Type*} [Fintype ι] [Field K]

namespace Fintype

/-- If the odd power sums of `μ` vanish, then every polynomial has the same sum over `μ` and over
`-μ`: its odd part sums to zero on both. -/
theorem sum_eval_neg_eq_of_sum_pow_odd {μ : ι → K} (h : ∀ j, ∑ i, μ i ^ (2 * j + 1) = 0)
    (p : K[X]) : ∑ i, p.eval (-μ i) = ∑ i, p.eval (μ i) := by
  simp only [eval_eq_sum_range]
  refine Finset.sum_comm.trans ((Finset.sum_congr rfl fun k _ => ?_).trans Finset.sum_comm)
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  rcases Nat.even_or_odd k with hk | ⟨j, rfl⟩
  · simp only [hk.neg_pow]
  · simp only [Odd.neg_pow ⟨j, rfl⟩, Finset.sum_neg_distrib, h j, neg_zero]

/-- Summing a polynomial vanishing on `T` except at `v` over a family with values in `T` counts
the members equal to `v`. -/
private theorem sum_eval_prod_erase [DecidableEq K] {T : Finset K} (v : K) {ν : ι → K}
    (hν : ∀ i, ν i ∈ T) :
    ∑ i, (∏ w ∈ T.erase v, (X - C w)).eval (ν i) =
      #(univ.filter fun i => v = ν i) • ∏ w ∈ T.erase v, (v - w) := by
  have h : ∀ i, (∏ w ∈ T.erase v, (X - C w)).eval (ν i) =
      if v = ν i then ∏ w ∈ T.erase v, (v - w) else 0 := fun i => by
    rw [eval_prod]
    split_ifs with hv
    · simp [hv]
    · exact Finset.prod_eq_zero (mem_erase.2 ⟨Ne.symm hv, hν i⟩) (by simp)
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
    add_zero]

/-- **A family whose odd power sums vanish is symmetric**: over a field of characteristic zero,
if `∑ μ_i^{2j+1} = 0` for every `j`, then the multiset of the `-μ_i` is that of the `μ_i`. Each
multiplicity is read off by summing a polynomial that vanishes at every other value of `±μ`
(`Fintype.sum_eval_neg_eq_of_sum_pow_odd`). -/
theorem map_neg_eq_of_sum_pow_odd [CharZero K] {μ : ι → K}
    (h : ∀ j, ∑ i, μ i ^ (2 * j + 1) = 0) :
    univ.val.map (fun i => -μ i) = univ.val.map μ := by
  classical
  refine Multiset.ext' fun v => ?_
  obtain ⟨T, hT⟩ : ∃ T : Finset K, T = univ.image μ ∪ univ.image fun i => -μ i := ⟨_, rfl⟩
  have hne : ∏ w ∈ T.erase v, (v - w) ≠ 0 :=
    prod_ne_zero_iff.2 fun w hw => sub_ne_zero.2 (Ne.symm (ne_of_mem_erase hw))
  have key := sum_eval_neg_eq_of_sum_pow_odd h (∏ w ∈ T.erase v, (X - C w))
  rw [sum_eval_prod_erase v (ν := fun i => -μ i) fun i => hT ▸ mem_union_right _
      (mem_image_of_mem _ (mem_univ i)),
    sum_eval_prod_erase v (ν := μ) fun i => hT ▸ mem_union_left _
      (mem_image_of_mem _ (mem_univ i)), nsmul_eq_mul, nsmul_eq_mul] at key
  rw [Multiset.count_map, Multiset.count_map]
  exact_mod_cast mul_right_cancel₀ hne key

end Fintype

@[deprecated (since := "2026-09-30")]
alias sum_eval_neg_eq_of_sum_pow_odd := Fintype.sum_eval_neg_eq_of_sum_pow_odd

@[deprecated (since := "2026-09-30")]
alias map_neg_eq_of_sum_pow_odd := Fintype.map_neg_eq_of_sum_pow_odd

end PowerSum

namespace Matrix

namespace IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

/-- The trace of a power of a Hermitian matrix is the power sum of its eigenvalues. -/
theorem trace_pow_eq_sum (hA : A.IsHermitian) (k : ℕ) :
    trace (A ^ k) = ∑ i, (hA.eigenvalues i : 𝕜) ^ k := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, trace_mul_comm, ← Matrix.mul_assoc,
    Unitary.coe_star_mul_self, Matrix.one_mul, diagonal_pow, trace_diagonal]
  simp

/-- **A Hermitian matrix whose odd powers are traceless has a spectrum symmetric about `0`**:
`charpoly (-A) = charpoly A`. The odd power sums of the eigenvalues vanish
(`Matrix.IsHermitian.trace_pow_eq_sum`), so the eigenvalue multiset is symmetric
(`Fintype.map_neg_eq_of_sum_pow_odd`). -/
theorem charpoly_neg_of_trace_pow_odd (hA : A.IsHermitian)
    (h : ∀ j, trace (A ^ (2 * j + 1)) = 0) : (-A).charpoly = A.charpoly := by
  have hs : univ.val.map (fun i => -hA.eigenvalues i) = univ.val.map hA.eigenvalues :=
    Fintype.map_neg_eq_of_sum_pow_odd fun j => by
      have := h j
      rw [hA.trace_pow_eq_sum] at this
      exact_mod_cast this
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_neg, Unitary.conjStarAlgAut_apply, charpoly_mul_comm, ← Matrix.mul_assoc,
    Unitary.coe_star_mul_self, Matrix.one_mul, diagonal_neg, charpoly_diagonal, hA.charpoly_eq,
    Finset.prod_eq_multiset_prod, Finset.prod_eq_multiset_prod]
  have := congrArg (Multiset.map fun x : ℝ => (X - C (x : 𝕜))) hs
  simp only [Multiset.map_map, Function.comp_def] at this
  simpa using congrArg Multiset.prod this

end IsHermitian

end Matrix

namespace Matrix

/-! ### The half-sum of two symmetric involutions -/

section HalfSum

open Complex in
/-- The factor identity behind `Matrix.charpoly_half_add_of_involutive`: if `r₁ r₂ = 1` and
`r₁ + r₂ = 4z² − 2`, then with `a = e^{iθ}`, `b = e^{−iθ}` (so `ab = 1`,
`a + b = 4 cos²(θ/2) − 2`), `(r₁ − a)(r₁ − b)(r₂ − a)(r₂ − b) = 16 (z² − cos²(θ/2))²`. -/
private theorem prod_sub_exp_mul_prod_sub_exp (θ : ℝ) {z r₁ r₂ : ℂ} (h12 : r₁ * r₂ = 1)
    (hs : r₁ + r₂ = 4 * z ^ 2 - 2) :
    (r₁ - exp (θ * I)) * (r₁ - exp (-θ * I)) * ((r₂ - exp (θ * I)) * (r₂ - exp (-θ * I))) =
      16 * ((z - (Real.cos (θ / 2) : ℂ)) * (z + (Real.cos (θ / 2) : ℂ))) ^ 2 := by
  obtain ⟨a, ha⟩ : ∃ a, a = exp (θ * I) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = exp (-θ * I) := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have hab : a * b = 1 := by
    rw [ha, hb, ← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero]
  have hc : a + b = 4 * (Real.cos (θ / 2) : ℂ) ^ 2 - 2 := by
    have h2 : (θ : ℂ) = 2 * ((θ / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [ha, hb, ← Complex.two_cos, h2, Complex.cos_two_mul, Complex.ofReal_cos]
    ring
  have hP : (r₁ - a) * (r₂ - a) = 1 - a * (4 * z ^ 2 - 2) + a ^ 2 := by
    linear_combination h12 - a * hs
  have hQ : (r₁ - b) * (r₂ - b) = 1 - b * (4 * z ^ 2 - 2) + b ^ 2 := by
    linear_combination h12 - b * hs
  calc (r₁ - a) * (r₁ - b) * ((r₂ - a) * (r₂ - b))
      = ((r₁ - a) * (r₂ - a)) * ((r₁ - b) * (r₂ - b)) := by ring
    _ = (1 - a * (4 * z ^ 2 - 2) + a ^ 2) * (1 - b * (4 * z ^ 2 - 2) + b ^ 2) := by rw [hP, hQ]
    _ = (a + b - (4 * z ^ 2 - 2)) ^ 2 := by
      linear_combination ((4 * z ^ 2 - 2) ^ 2 - (a + b) * (4 * z ^ 2 - 2) + (a * b - 1)) * hab
    _ = _ := by rw [hc]; ring

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix whose characteristic polynomial is a product of `m` monic quadratics has order
`2m`. -/
theorem card_eq_of_charpoly_eq_prod {K : Type*} [Field K] {M : Matrix n n K} {m : ℕ}
    {a b : Fin m → K} (h : M.charpoly = ∏ k, (X - C (a k)) * (X - C (b k))) :
    Fintype.card n = 2 * m := by
  have h' := congrArg natDegree h
  rw [charpoly_natDegree_eq_dim, natDegree_prod_of_monic _ _ fun k _ =>
    (monic_X_sub_C _).mul (monic_X_sub_C _)] at h'
  simp only [natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _), natDegree_X_sub_C,
    sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h'
  omega

open Complex in
/-- **The spectrum of the half-sum of two symmetric involutions of trace zero**
(Ammar–Gragg–Reichel; [golub2013matrix] §12.2.10, Fact 2): if `A`, `B` are real symmetric with
`A² = B² = 1` and `tr A = tr B = 0`, and the eigenvalues of `AB` are the `m` pairs `e^{±iθ_k}`,
then the eigenvalues of `(A + B)/2` are the `m` pairs `± cos(θ_k/2)`.

The spectrum of `C = (A + B)/2` is symmetric about `0`: its odd powers are traceless
(`Matrix.trace_add_pow_odd_eq_zero`, `Matrix.IsHermitian.charpoly_neg_of_trace_pow_odd`), so
`p_C(z)² = p_C(z) p_{−C}(z) = det (z² − C²)`. For `r₁ r₂ = 1`, `r₁ + r₂ = 4z² − 2`,
`4 (z² − C²) AB = −(r₁ − AB)(r₂ − AB)`, which gives `det (z² − C²)` from the characteristic
polynomial of `AB` at `r₁`, `r₂` (`det AB = 1`), and so `p_C² = ∏ (X² − cos²(θ_k/2))²`; both being
monic, `p_C = ∏ (X² − cos²(θ_k/2))`. -/
theorem charpoly_half_add_of_involutive {A B : Matrix n n ℝ} (hAs : A.IsSymm) (hBs : B.IsSymm)
    (hA : A * A = 1) (hB : B * B = 1) (htA : trace A = 0) (htB : trace B = 0) {m : ℕ}
    (θ : Fin m → ℝ)
    (hθ : ((A * B).map (algebraMap ℝ ℂ)).charpoly =
      ∏ k, (X - C (exp (θ k * I))) * (X - C (exp (-θ k * I)))) :
    ((1 / 2 : ℝ) • (A + B)).charpoly =
      ∏ k, (X - C (Real.cos (θ k / 2))) * (X + C (Real.cos (θ k / 2))) := by
  have hn := card_eq_of_charpoly_eq_prod hθ
  have hneg1 : ∀ M : Matrix n n ℂ, det (-M) = det M := fun M => by
    rw [det_neg, hn, pow_mul, neg_one_sq, one_pow, one_mul]
  have hsc : ∀ w : ℂ, scalar n w = w • (1 : Matrix n n ℂ) := fun w => by
    rw [scalar_apply, smul_one_eq_diagonal]
  obtain ⟨Cm, hCm⟩ : ∃ Cm : Matrix n n ℝ, Cm = (1 / 2 : ℝ) • (A + B) := ⟨_, rfl⟩
  rw [← hCm]
  have hCh : Cm.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hCm, transpose_smul, transpose_add,
      hAs.eq, hBs.eq]
  have hsym : (-Cm).charpoly = Cm.charpoly := hCh.charpoly_neg_of_trace_pow_odd fun j => by
    rw [hCm, smul_pow, trace_smul, trace_add_pow_odd_eq_zero hA hB htA htB, smul_zero]
  obtain ⟨p, hp⟩ : ∃ p, p = Cm.charpoly := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ[X],
      r = ∏ k, (X - C (Real.cos (θ k / 2))) * (X + C (Real.cos (θ k / 2))) := ⟨_, rfl⟩
  rw [← hp, ← hr]
  -- the complexified matrices
  obtain ⟨Ac, hAc⟩ : ∃ Ac, Ac = A.map (algebraMap ℝ ℂ) := ⟨_, rfl⟩
  obtain ⟨Bc, hBc⟩ : ∃ Bc, Bc = B.map (algebraMap ℝ ℂ) := ⟨_, rfl⟩
  have hMc : (A * B).map (algebraMap ℝ ℂ) = Ac * Bc := by rw [hAc, hBc, Matrix.map_mul]
  have hAA : Ac * Ac = 1 := by
    rw [hAc, ← Matrix.map_mul, hA, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBB : Bc * Bc = 1 := by
    rw [hBc, ← Matrix.map_mul, hB, Matrix.map_one _ (map_zero _) (map_one _)]
  have hAA' : ∀ M, Ac * (Ac * M) = M := fun M => by rw [← Matrix.mul_assoc, hAA, Matrix.one_mul]
  have hCc : Cm.map (algebraMap ℝ ℂ) = (1 / 2 : ℂ) • (Ac + Bc) := by
    ext i j
    simp [hCm, hAc, hBc]
    ring
  have hCneg : (-Cm).map (algebraMap ℝ ℂ) = -((1 / 2 : ℂ) • (Ac + Bc)) := by
    rw [← hCc]
    ext i j
    simp
  have hev : ∀ w : ℂ, det (w • 1 - Ac * Bc) =
      ∏ k, (w - exp (θ k * I)) * (w - exp (-θ k * I)) := fun w => by
    have h := congrArg (eval w) hθ
    rw [eval_charpoly, eval_prod, hsc, hMc] at h
    simpa using h
  have hdet : det (Ac * Bc) = 1 := by
    have h := hev 0
    rw [zero_smul, zero_sub, hneg1] at h
    rw [h]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [zero_sub, zero_sub, neg_mul_neg, ← Complex.exp_add, neg_mul, add_neg_cancel,
      Complex.exp_zero]
  have hpt : ∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).eval z ^ 2 =
      (r.map (algebraMap ℝ ℂ)).eval z ^ 2 := fun z => by
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_eq_mul_self ((4 * z ^ 2 - 2) ^ 2 - 4)
    have h12 : (4 * z ^ 2 - 2 + d) / 2 * ((4 * z ^ 2 - 2 - d) / 2) = 1 := by
      linear_combination (1 / 4 : ℂ) * hd
    have hs : (4 * z ^ 2 - 2 + d) / 2 + (4 * z ^ 2 - 2 - d) / 2 = 4 * z ^ 2 - 2 := by ring
    generalize (4 * z ^ 2 - 2 + d) / 2 = r₁ at h12 hs
    generalize (4 * z ^ 2 - 2 - d) / 2 = r₂ at h12 hs
    -- `p_C(z)² = det (z² − C²)`
    have e1 : (p.map (algebraMap ℝ ℂ)).eval z = det (z • 1 - (1 / 2 : ℂ) • (Ac + Bc)) := by
      rw [hp, ← charpoly_map, eval_charpoly, hsc, hCc]
    have e2 : (p.map (algebraMap ℝ ℂ)).eval z = det (z • 1 + (1 / 2 : ℂ) • (Ac + Bc)) := by
      rw [hp, ← hsym, ← charpoly_map, eval_charpoly, hsc, hCneg, sub_neg_eq_add]
    have eX : (z • 1 - (1 / 2 : ℂ) • (Ac + Bc)) * (z • 1 + (1 / 2 : ℂ) • (Ac + Bc)) =
        (4 : ℂ)⁻¹ • ((4 * z ^ 2 - 2) • 1 - (Ac * Bc + Bc * Ac)) := by
      simp only [sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
        Matrix.one_mul, Matrix.mul_one, smul_add, hAA, hBB]
      module
    -- `4 (z² − C²) AB = −(r₁ − AB)(r₂ − AB)`
    have eY : ((4 * z ^ 2 - 2) • 1 - (Ac * Bc + Bc * Ac)) * (Ac * Bc) =
        -((r₁ • 1 - Ac * Bc) * (r₂ • 1 - Ac * Bc)) := by
      have e : (r₁ • 1 - Ac * Bc) * (r₂ • 1 - Ac * Bc) =
          (r₁ * r₂) • 1 - (r₁ + r₂) • (Ac * Bc) + Ac * Bc * (Ac * Bc) := by
        simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, Matrix.one_mul,
          Matrix.mul_one, add_smul]
        module
      rw [e, h12, hs]
      simp only [sub_mul, add_mul, smul_mul_assoc, Matrix.one_mul, Matrix.mul_assoc, hAA', hBB]
      module
    have key : (4 : ℂ)⁻¹ ^ Fintype.card n * ((∏ k, (r₁ - exp (θ k * I)) * (r₁ - exp (-θ k * I))) *
        ∏ k, (r₂ - exp (θ k * I)) * (r₂ - exp (-θ k * I))) =
        (p.map (algebraMap ℝ ℂ)).eval z ^ 2 := by
      rw [← hev, ← hev, ← det_mul, ← hneg1, ← eY, det_mul, hdet, mul_one, ← det_smul, ← eX,
        det_mul, ← e1, ← e2, sq]
    rw [← key, ← prod_mul_distrib,
      Finset.prod_congr rfl fun k _ => prod_sub_exp_mul_prod_sub_exp (θ k) h12 hs, prod_mul_distrib,
      prod_const, card_univ, Fintype.card_fin, prod_pow, hr, Polynomial.map_prod, eval_prod, hn,
      pow_mul, ← mul_assoc, ← mul_pow]
    norm_num
  have hsq : p ^ 2 = r ^ 2 :=
    Polynomial.map_injective _ (RingHom.injective (algebraMap ℝ ℂ)) <| Polynomial.funext fun z => by
      simp only [Polynomial.map_pow, eval_pow, hpt]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exact h
  · have h1 : p.leadingCoeff = 1 := hp ▸ charpoly_monic Cm
    have h2 : r.Monic := hr ▸ monic_prod_of_monic _ _ fun k _ =>
      (monic_X_sub_C _).mul (monic_X_add_C _)
    rw [h, leadingCoeff_neg, h2.leadingCoeff] at h1
    norm_num at h1

end HalfSum

end Matrix
