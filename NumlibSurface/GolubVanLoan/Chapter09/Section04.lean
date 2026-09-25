import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Numlib.Analysis.Matrix.Function.Log
import Numlib.Analysis.Matrix.Function.Sign
import Numlib.Analysis.Matrix.Function.Sqrt
import NumlibSurface.GolubVanLoan.Chapter09.Section03

/-!
# Golub–Van Loan §9.4: the sign, square root, and log of a matrix

Surface file for [golub2013matrix] §9.4: the matrix sign function, its Jordan-form expression and
the half-plane projector; Newton's sign iteration (9.4.1) with (9.4.2)–(9.4.4), its convergence and
the Newton–Schulz step (9.4.5); the principal square root, Newton's square-root iteration (9.4.7)
and the Denman–Beavers iteration (9.4.8)–(9.4.10) with `sign([0 A; I 0])`; the principal logarithm
with the Maclaurin and Gregory series, the `(3,3)` Padé approximant of `log(1 + x)` and the identity
behind inverse scaling and squaring.

## Conventions

`A : Matrix (Fin n) (Fin n) ℂ` (the book's `ℂ^{n×n}`) except for the real logarithm. `sign(A)` is
the backbone's `Matrix.matrixSign A = pfc (z ↦ sign (Re z)) A`, `A^{1/2}` is
`Matrix.principalSqrt A` and `log(A)` is `Matrix.principalLog A`. "No eigenvalue on the imaginary
axis" is `∀ μ ∈ spectrum ℂ A, μ.re ≠ 0`; "no eigenvalue on `(-∞, 0]`" is
`spectrum ℂ A ⊆ Complex.slitPlane`. Block matrices `[P Q; R S]` are `Matrix.fromBlocks` over
`Fin m ⊕ Fin n`; a partition `X = [X₁ X₂]` of the columns is a reindexing
`e : Fin m₁ ⊕ Fin m₂ ≃ Fin n` with `X_i = X.submatrix id (e ∘ Sum.in_)`, and the columns of
`X⁻ᴴ = [Y₁ Y₂]` are read through the rows of `X⁻¹`, `Y_iᴴ = X⁻¹.submatrix (e ∘ Sum.in_) id`
(written `Z_i` in statements). `‖·‖₂` is the scoped `Matrix.Norms.L2Operator`.

## Sources

`Numlib/Analysis/Matrix/Function/{Sign,Sqrt,Log}`.

## Not formalized

The four square roots of `[4 10; 0 9]` (a numerical example), the scaled iteration (9.4.6) and its
choices of `μ_k`, QR with column pivoting on `(I + sign(A))/2` (only the range statement is
formalized), the inverse-scaling-and-squaring `while` loop (only its identity
`log(A) = 2^k log(A_k)` is formalized), the Problems.

## Errata

§9.4.1 derives the Jordan-form expression of `sign(A)` "from Theorem 9.1.1", which does not exist
(it is the definition (9.1.3)–(9.1.4)), and uses "`S² = S`" for `S² = I`. §9.4.2's principal square
root needs no eigenvalue of `A` on `(-∞, 0]`, which the book leaves implicit.
-/

open Polynomial Finset Filter Topology Asymptotics

namespace GolubVanLoan.Chapter09

variable {n : ℕ}

/-! ### The matrix sign function -/

/-- §9.4.1: if `X⁻¹ A X = [J₁ 0; 0 J₂]` with the eigenvalues of `J₁` (of size `m₁`) in the open
left half plane and those of `J₂` (of size `m₂`) in the open right half plane, then
`sign(A) = X [-I_{m₁} 0; 0 I_{m₂}] X⁻¹`. -/
theorem matrixSign_eq_conj {m₁ m₂ : ℕ} (e : Fin m₁ ⊕ Fin m₂ ≃ Fin n)
    {A X : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X) {J₁ : Matrix (Fin m₁) (Fin m₁) ℂ}
    {J₂ : Matrix (Fin m₂) (Fin m₂) ℂ}
    (h : X⁻¹ * A * X = Matrix.reindex e e (Matrix.fromBlocks J₁ 0 0 J₂))
    (h₁ : ∀ μ ∈ spectrum ℂ J₁, μ.re < 0) (h₂ : ∀ μ ∈ spectrum ℂ J₂, 0 < μ.re) :
    Matrix.matrixSign A = X * Matrix.reindex e e (Matrix.fromBlocks (-1) 0 0 1) * X⁻¹ :=
  Matrix.matrixSign_conj_fromBlocks e hX h h₁ h₂

/-- The column partition of `X X⁻¹ = I`: `I = X₁ Y₁ᴴ + X₂ Y₂ᴴ`. -/
private theorem one_eq_add_blocks {m₁ m₂ : ℕ} (e : Fin m₁ ⊕ Fin m₂ ≃ Fin n)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X) :
    (1 : Matrix (Fin n) (Fin n) ℂ) =
      X.submatrix id (e ∘ Sum.inl) * X⁻¹.submatrix (e ∘ Sum.inl) id +
        X.submatrix id (e ∘ Sum.inr) * X⁻¹.submatrix (e ∘ Sum.inr) id := by
  rw [← Matrix.mul_nonsing_inv X ((Matrix.isUnit_iff_isUnit_det X).mp hX)]
  ext i j
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.submatrix_apply, Function.comp_apply,
    id_eq]
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type]

/-- §9.4.1, the half-plane projector: with the partitions `X = [X₁ X₂]`, `X⁻ᴴ = [Y₁ Y₂]` of
`matrixSign_eq_conj`, `sign(A) = X₂ Y₂ᴴ - X₁ Y₁ᴴ`, `I_n = X₁ Y₁ᴴ + X₂ Y₂ᴴ`, and
`X₂ Y₂ᴴ = (I_n + sign(A))/2`, a projection whose range is `ran(X₂)`, the invariant subspace of the
right half-plane eigenvalues, of dimension `m₂`. -/
theorem sign_projector {m₁ m₂ : ℕ} (e : Fin m₁ ⊕ Fin m₂ ≃ Fin n)
    {A X : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X) {J₁ : Matrix (Fin m₁) (Fin m₁) ℂ}
    {J₂ : Matrix (Fin m₂) (Fin m₂) ℂ}
    (h : X⁻¹ * A * X = Matrix.reindex e e (Matrix.fromBlocks J₁ 0 0 J₂))
    (h₁ : ∀ μ ∈ spectrum ℂ J₁, μ.re < 0) (h₂ : ∀ μ ∈ spectrum ℂ J₂, 0 < μ.re) :
    let X₁ := X.submatrix id (e ∘ Sum.inl)
    let X₂ := X.submatrix id (e ∘ Sum.inr)
    let Z₁ := X⁻¹.submatrix (e ∘ Sum.inl) id
    let Z₂ := X⁻¹.submatrix (e ∘ Sum.inr) id
    Matrix.matrixSign A = X₂ * Z₂ - X₁ * Z₁ ∧
    (1 : Matrix (Fin n) (Fin n) ℂ) = X₁ * Z₁ + X₂ * Z₂ ∧
    X₂ * Z₂ = (2 : ℂ)⁻¹ • (1 + Matrix.matrixSign A) ∧
    IsIdempotentElem ((2 : ℂ)⁻¹ • (1 + Matrix.matrixSign A)) ∧
    LinearMap.range ((2 : ℂ)⁻¹ • (1 + Matrix.matrixSign A)).mulVecLin =
      Submodule.span ℂ (Set.range X₂.col) ∧
    Module.finrank ℂ (LinearMap.range ((2 : ℂ)⁻¹ • (1 + Matrix.matrixSign A)).mulVecLin) = m₂ := by
  intro X₁ X₂ Z₁ Z₂
  obtain ⟨hP, hidem, hran, hdim⟩ := Matrix.range_one_add_matrixSign e hX h h₁ h₂
  have hI : (1 : Matrix (Fin n) (Fin n) ℂ) = X₁ * Z₁ + X₂ * Z₂ := one_eq_add_blocks e hX
  refine ⟨?_, hI, hP.symm, hidem, hran, by rw [hdim, Fintype.card_fin]⟩
  have hS : Matrix.matrixSign A = (2 : ℂ) • ((2 : ℂ)⁻¹ • (1 + Matrix.matrixSign A)) - 1 := by
    rw [smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul, add_sub_cancel_left]
  rw [hS, hP, hI]
  module

/-- §9.4.1, "this iteration is well-defined": for `A` without eigenvalues on the imaginary axis
every Newton iterate `S_k` ((9.4.1): `S₀ = A`, `S_{k+1} = (S_k + S_k⁻¹)/2`) is nonsingular and has
no eigenvalue on the imaginary axis, and `sign(S_k) = sign(A)`. -/
theorem newtonSign_isUnit {A : Matrix (Fin n) (Fin n) ℂ} (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0)
    (k : ℕ) :
    IsUnit (Matrix.newtonSignIterate A k) ∧
    (∀ μ ∈ spectrum ℂ (Matrix.newtonSignIterate A k), μ.re ≠ 0) ∧
    Matrix.matrixSign (Matrix.newtonSignIterate A k) = Matrix.matrixSign A :=
  ⟨(Matrix.isUnit_newtonSignIterate hA k).1, (Matrix.isUnit_newtonSignIterate hA k).2,
    Matrix.matrixSign_newtonSignIterate hA k⟩

/-- The iterates commute with `sign(A)`, whose square is `I`. -/
private theorem newtonSign_aux {A : Matrix (Fin n) (Fin n) ℂ} (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0)
    (k : ℕ) :
    Matrix.matrixSign A * Matrix.matrixSign A = 1 ∧
    Commute (Matrix.newtonSignIterate A k) (Matrix.matrixSign A) := by
  refine ⟨by rw [← sq]; exact Matrix.matrixSign_sq hA, ?_⟩
  rw [← Matrix.matrixSign_newtonSignIterate hA k]
  exact Matrix.commute_matrixSign _

/-- **(9.4.2)**: with `S = sign(A)`, `S_{k+1} - S = ½ S_k⁻¹ (S_k - S)²`. -/
theorem equation_9_4_2 {A : Matrix (Fin n) (Fin n) ℂ} (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0)
    (k : ℕ) :
    Matrix.newtonSignIterate A (k + 1) - Matrix.matrixSign A =
      (2 : ℂ)⁻¹ • ((Matrix.newtonSignIterate A k)⁻¹ *
        (Matrix.newtonSignIterate A k - Matrix.matrixSign A) ^ 2) := by
  obtain ⟨hS, hc⟩ := newtonSign_aux hA k
  rw [Matrix.newtonSignIterate_succ, Matrix.nonsing_inv_eq_ringInverse]
  exact half_smul_add_inverse_sub_eq_of_commute (newtonSign_isUnit hA k).1 hS hc

/-- **(9.4.3)**: `S_{k+1} + S = ½ S_k⁻¹ (S_k + S)²`. -/
theorem equation_9_4_3 {A : Matrix (Fin n) (Fin n) ℂ} (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0)
    (k : ℕ) :
    Matrix.newtonSignIterate A (k + 1) + Matrix.matrixSign A =
      (2 : ℂ)⁻¹ • ((Matrix.newtonSignIterate A k)⁻¹ *
        (Matrix.newtonSignIterate A k + Matrix.matrixSign A) ^ 2) := by
  obtain ⟨hS, hc⟩ := newtonSign_aux hA k
  rw [Matrix.newtonSignIterate_succ, Matrix.nonsing_inv_eq_ringInverse]
  exact half_smul_add_inverse_add_eq_of_commute (newtonSign_isUnit hA k).1 hS hc

/-- §9.4.1: if `sign(M)` is defined (no eigenvalue of `M` on the imaginary axis), then
`M + sign(M)` is nonsingular. -/
theorem isUnit_add_sign {M : Matrix (Fin n) (Fin n) ℂ} (hM : ∀ μ ∈ spectrum ℂ M, μ.re ≠ 0) :
    IsUnit (M + Matrix.matrixSign M) :=
  Matrix.isUnit_add_matrixSign hM

/-- The scalar sign function `z ↦ sign (Re z)` is locally constant off the imaginary axis. -/
private theorem sign_eventuallyEq {μ : ℂ} (hμ : μ.re ≠ 0) :
    (fun z : ℂ => ((SignType.sign z.re : SignType) : ℂ)) =ᶠ[𝓝 μ]
      fun _ => ((SignType.sign μ.re : SignType) : ℂ) := by
  rcases lt_or_gt_of_ne hμ with h | h
  · filter_upwards [Complex.continuous_re.continuousAt.eventually (gt_mem_nhds h)] with z hz
    rw [sign_neg hz, sign_neg h]
  · filter_upwards [Complex.continuous_re.continuousAt.eventually (lt_mem_nhds h)] with z hz
    rw [sign_pos hz, sign_pos h]

/-- `|λ - sign λ| < |λ + sign λ|` off the imaginary axis. -/
private theorem norm_sub_sign_lt {z : ℂ} (hz : z.re ≠ 0) :
    ‖z - ((SignType.sign z.re : SignType) : ℂ)‖ < ‖z + ((SignType.sign z.re : SignType) : ℂ)‖ := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  rcases lt_or_gt_of_ne hz with h | h
  · simp only [sign_neg h, SignType.coe_neg, SignType.coe_one, Complex.sub_re, Complex.add_re,
      Complex.sub_im, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.one_re,
      Complex.one_im]
    nlinarith
  · simp only [sign_pos h, SignType.coe_one, Complex.sub_re, Complex.add_re, Complex.sub_im,
      Complex.add_im, Complex.one_re, Complex.one_im]
    nlinarith

/-- **(9.4.4)**: `G_k = (S_k - S)(S_k + S)⁻¹` satisfies `G_{k+1} = G_k²`, hence `G_k = G₀^{2^k}`;
and every eigenvalue of `G₀ = (A - S)(A + S)⁻¹` is `μ = (λ - sign λ)/(λ + sign λ)` for an
eigenvalue `λ` of `A`, with `|μ| < 1`. -/
theorem equation_9_4_4 {A : Matrix (Fin n) (Fin n) ℂ} (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0) :
    let S := Matrix.matrixSign A
    let G := fun k => (Matrix.newtonSignIterate A k - S) * (Matrix.newtonSignIterate A k + S)⁻¹
    (∀ k, G (k + 1) = G k ^ 2) ∧ (∀ k, G k = G 0 ^ 2 ^ k) ∧
    ∀ μ ∈ spectrum ℂ (G 0), ∃ l ∈ spectrum ℂ A,
      μ = (l - ((SignType.sign l.re : SignType) : ℂ)) /
        (l + ((SignType.sign l.re : SignType) : ℂ)) ∧
      ‖μ‖ < 1 := by
  intro S G
  have hstep : ∀ k, G (k + 1) = G k ^ 2 := by
    intro k
    set s := Matrix.newtonSignIterate A k
    obtain ⟨hS2, hsS⟩ := newtonSign_aux hA k
    obtain ⟨hsu, hsre, hsign⟩ := newtonSign_isUnit hA k
    obtain ⟨-, hsre', hsign'⟩ := newtonSign_isUnit hA (k + 1)
    have hQ : IsUnit (s + S) := by
      have := Matrix.isUnit_add_matrixSign hsre
      rwa [hsign] at this
    have hQ' : IsUnit (Matrix.newtonSignIterate A (k + 1) + S) := by
      have := Matrix.isUnit_add_matrixSign hsre'
      rwa [hsign'] at this
    set P := s - S
    set Q := s + S
    have hPs : Commute P s := (Commute.refl s).sub_left hsS.symm
    have hPQ : Commute P Q := hPs.add_right (hsS.sub_left (Commute.refl S))
    have hPQi : Commute P Q⁻¹ := Matrix.commute_nonsing_inv_right hPQ
    have hQis : Commute Q⁻¹ s⁻¹ := Matrix.commute_nonsing_inv_right
      (Matrix.commute_nonsing_inv_right ((Commute.refl s).add_right hsS)).symm
    have hQiQc : Commute Q⁻¹ Q := (Matrix.commute_nonsing_inv_right (Commute.refl Q)).symm
    have hPsi : Commute P s⁻¹ := Matrix.commute_nonsing_inv_right hPs
    have hQiQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q ((Matrix.isUnit_iff_isUnit_det Q).mp hQ)
    have key : G k ^ 2 * (Matrix.newtonSignIterate A (k + 1) + S) =
        Matrix.newtonSignIterate A (k + 1) - S := by
      rw [equation_9_4_2 hA k, equation_9_4_3 hA k, mul_smul_comm]
      congr 1
      change (P * Q⁻¹) ^ 2 * (s⁻¹ * Q ^ 2) = s⁻¹ * P ^ 2
      calc (P * Q⁻¹) ^ 2 * (s⁻¹ * Q ^ 2)
          = P ^ 2 * ((Q⁻¹ ^ 2 * s⁻¹) * Q ^ 2) := by
            rw [hPQi.mul_pow]; simp only [mul_assoc]
        _ = P ^ 2 * s⁻¹ * (Q⁻¹ ^ 2 * Q ^ 2) := by
            rw [(hQis.pow_left 2).eq]; simp only [mul_assoc]
        _ = s⁻¹ * P ^ 2 := by
            rw [← hQiQc.mul_pow, hQiQ, one_pow, mul_one, (hPsi.pow_left 2).eq]
    have hQ'i : (Matrix.newtonSignIterate A (k + 1) + S) *
        (Matrix.newtonSignIterate A (k + 1) + S)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hQ')
    change (Matrix.newtonSignIterate A (k + 1) - S) *
      (Matrix.newtonSignIterate A (k + 1) + S)⁻¹ = G k ^ 2
    rw [← key, mul_assoc, hQ'i, mul_one]
  have hpow : ∀ k, G k = G 0 ^ 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [hstep, ih, ← pow_mul, pow_succ]
  refine ⟨hstep, hpow, ?_⟩
  -- the spectrum of `G₀` through the functional calculus
  have hI : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral A
  have hs := IsAlgClosed.splits (minpoly ℂ A)
  set sg : ℂ → ℂ := fun z => ((SignType.sign z.re : SignType) : ℂ)
  have hroot : ∀ μ ∈ (minpoly ℂ A).roots, μ.re ≠ 0 := fun μ hμ =>
    hA μ ((spectrum.mem_iff_isRoot_minpoly hI).2 (Polynomial.isRoot_of_mem_roots hμ))
  have hsg : ∀ (k : ℕ), ∀ μ ∈ (minpoly ℂ A).roots, ContDiffAt ℂ k sg μ := fun k μ hμ =>
    contDiffAt_const.congr_of_eventuallyEq (sign_eventuallyEq (hroot μ hμ))
  have hid : ∀ (k : ℕ), ∀ μ ∈ (minpoly ℂ A).roots, ContDiffAt ℂ k (fun z : ℂ => z) μ :=
    fun k μ _ => contDiffAt_id
  have hnz : ∀ μ ∈ (minpoly ℂ A).roots, μ + sg μ ≠ 0 := fun μ hμ h => by
    have := norm_sub_sign_lt (hroot μ hμ)
    simp only [sg] at h
    rw [h, norm_zero] at this
    exact absurd this (not_lt.mpr (norm_nonneg _))
  have hsub : A - S = pfc (fun z => z - sg z) A := by
    rw [show (fun z => z - sg z) = (fun z : ℂ => z) - sg from rfl,
      pfc_sub (fun μ hμ => hid _ μ hμ) (fun μ hμ => hsg _ μ hμ), pfc_id hI hs]
    rfl
  have hadd : A + S = pfc (fun z => z + sg z) A := by
    rw [show (fun z => z + sg z) = (fun z : ℂ => z) + sg from rfl,
      pfc_add (fun μ hμ => hid _ μ hμ) (fun μ hμ => hsg _ μ hμ), pfc_id hI hs]
    rfl
  have hcadd : ∀ (k : ℕ), ∀ μ ∈ (minpoly ℂ A).roots, ContDiffAt ℂ k (fun z => z + sg z) μ :=
    fun k μ hμ => (hid k μ hμ).add (hsg k μ hμ)
  have hinv := (pfc_inv hI hs (fun μ hμ => hcadd _ μ hμ) hnz).2
  have hG0 : G 0 = pfc (fun z => (z - sg z) * (z + sg z)⁻¹) A := by
    change (A - S) * (A + S)⁻¹ = _
    rw [show (fun z => (z - sg z) * (z + sg z)⁻¹) =
        (fun z => z - sg z) * fun z => (z + sg z)⁻¹ from rfl,
      pfc_mul (f := fun z => z - sg z) (g := fun z => (z + sg z)⁻¹) hI hs
        (fun μ hμ => (hid _ μ hμ).sub (hsg _ μ hμ))
        (fun μ hμ => (hcadd _ μ hμ).inv (hnz μ hμ)), hinv, hsub, hadd,
      Matrix.nonsing_inv_eq_ringInverse]
  intro μ hμ
  rw [hG0, spectrum_pfc hI hs] at hμ
  obtain ⟨l, hl, rfl⟩ := hμ
  refine ⟨l, hl, by simp only [sg, div_eq_mul_inv], ?_⟩
  have hlt := norm_sub_sign_lt (hA l hl)
  rw [norm_mul, norm_inv, ← div_eq_mul_inv, div_lt_one ((norm_nonneg _).trans_lt hlt)]
  exact hlt

open scoped Matrix.Norms.L2Operator in
/-- §9.4.1: for `A` without eigenvalues on the imaginary axis, `S_k → sign(A)`, quadratically:
`‖S_{k+1} - S‖₂ ≤ ½ ‖S_k⁻¹‖₂ ‖S_k - S‖₂²`. -/
theorem newtonSign_tendsto {A : Matrix (Fin n) (Fin n) ℂ} (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0) :
    Tendsto (Matrix.newtonSignIterate A) atTop (𝓝 (Matrix.matrixSign A)) ∧
    ∀ k, ‖Matrix.newtonSignIterate A (k + 1) - Matrix.matrixSign A‖ ≤
      2⁻¹ * ‖(Matrix.newtonSignIterate A k)⁻¹‖ *
        ‖Matrix.newtonSignIterate A k - Matrix.matrixSign A‖ ^ 2 :=
  ⟨Matrix.tendsto_newtonSignIterate hA, Matrix.norm_newtonSignIterate_sub_le hA⟩

/-- **(9.4.5)**, the Newton–Schulz step: replacing `S_k⁻¹` by its Newton approximation
`S_k (2I - S_k²)` in (9.4.1) gives `½ (S_k + S_k (2I - S_k²)) = ½ S_k (3I - S_k²)`. -/
theorem equation_9_4_5 (S : Matrix (Fin n) (Fin n) ℂ) :
    (2 : ℂ)⁻¹ • (S + S * (2 • 1 - S ^ 2)) = (2 : ℂ)⁻¹ • (S * (3 • 1 - S ^ 2)) := by
  congr 1
  noncomm_ring

/-! ### The matrix square root -/

/-- §9.4.2's definition: `F` is **the principal square root** of `A` if (a) `F² = A` and (b) every
eigenvalue of `F` has positive real part. -/
def IsPrincipalSqrt (F A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  F ^ 2 = A ∧ ∀ μ ∈ spectrum ℂ F, 0 < μ.re

/-- §9.4.2, "we designate this matrix by `A^{1/2}`": if no eigenvalue of `A` lies on `(-∞, 0]`,
`A` has exactly one principal square root, `Matrix.principalSqrt A`. -/
theorem principalSqrt_existsUnique {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : spectrum ℂ A ⊆ Complex.slitPlane) :
    (∃! F, IsPrincipalSqrt F A) ∧ IsPrincipalSqrt (Matrix.principalSqrt A) A :=
  ⟨Matrix.existsUnique_sq_eq_of_re_pos hA,
    ⟨(Matrix.principalSqrt_sq hA).1, (Matrix.principalSqrt_sq hA).2.2⟩⟩

/-- **(9.4.7)** and §9.4.2: Newton's square-root iteration `X₀ = A`,
`X_{k+1} = (X_k + X_k⁻¹ A)/2` satisfies `X_k = A^{1/2} S_k`, `S_k` the Newton sign iterates of
`A^{1/2}`, and converges to `A^{1/2}` when no eigenvalue of `A` lies on `(-∞, 0]`. -/
theorem newtonSqrt_tendsto {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : spectrum ℂ A ⊆ Complex.slitPlane) :
    (∀ k, Matrix.newtonSqrtIterate A k =
      Matrix.principalSqrt A * Matrix.newtonSignIterate (Matrix.principalSqrt A) k) ∧
    Tendsto (Matrix.newtonSqrtIterate A) atTop (𝓝 (Matrix.principalSqrt A)) :=
  ⟨Matrix.newtonSqrtIterate_eq_mul_newtonSignIterate hA, Matrix.tendsto_newtonSqrtIterate hA⟩

/-- **(9.4.8)**: the Newton sign iterates `S̃_k` of `Ã = [0 A; I 0]` have the form
`[0 X_k; Y_k 0]`, with `X₀ = A`, `Y₀ = I`, `X_{k+1} = (X_k + Y_k⁻¹)/2`,
`Y_{k+1} = (Y_k + X_k⁻¹)/2` (the Denman–Beavers iteration), `X_k`, `Y_k` nonsingular. -/
theorem equation_9_4_8 {A : Matrix (Fin n) (Fin n) ℂ} (hA : spectrum ℂ A ⊆ Complex.slitPlane)
    (k : ℕ) :
    Matrix.newtonSignIterate (Matrix.fromBlocks 0 A 1 0) k =
      Matrix.fromBlocks 0 (Matrix.denmanBeavers A k).1 (Matrix.denmanBeavers A k).2 0 ∧
    Matrix.denmanBeavers A 0 = (A, 1) ∧
    Matrix.denmanBeavers A (k + 1) =
      ((2 : ℂ)⁻¹ • ((Matrix.denmanBeavers A k).1 + (Matrix.denmanBeavers A k).2⁻¹),
        (2 : ℂ)⁻¹ • ((Matrix.denmanBeavers A k).2 + (Matrix.denmanBeavers A k).1⁻¹)) ∧
    IsUnit (Matrix.denmanBeavers A k).1 ∧ IsUnit (Matrix.denmanBeavers A k).2 :=
  ⟨(Matrix.newtonSignIterate_fromBlocks hA k).1, rfl, rfl,
    (Matrix.newtonSignIterate_fromBlocks hA k).2.1, (Matrix.newtonSignIterate_fromBlocks hA k).2.2⟩

/-- **(9.4.9)** (the book's P9.4.4): `X_k = A Y_k` for all `k`. -/
theorem equation_9_4_9 {A : Matrix (Fin n) (Fin n) ℂ} (hA : spectrum ℂ A ⊆ Complex.slitPlane)
    (k : ℕ) : (Matrix.denmanBeavers A k).1 = A * (Matrix.denmanBeavers A k).2 :=
  (Matrix.denmanBeavers_fst_eq_mul_snd hA k).1

/-- **(9.4.10)**: `X_{k+1} = (X_k + A X_k⁻¹)/2` and `Y_{k+1} = (Y_k + A⁻¹ Y_k⁻¹)/2`. -/
theorem equation_9_4_10 {A : Matrix (Fin n) (Fin n) ℂ} (hA : spectrum ℂ A ⊆ Complex.slitPlane)
    (k : ℕ) :
    (Matrix.denmanBeavers A (k + 1)).1 =
      (2 : ℂ)⁻¹ • ((Matrix.denmanBeavers A k).1 + A * (Matrix.denmanBeavers A k).1⁻¹) ∧
    (Matrix.denmanBeavers A (k + 1)).2 =
      (2 : ℂ)⁻¹ • ((Matrix.denmanBeavers A k).2 + A⁻¹ * (Matrix.denmanBeavers A k).2⁻¹) := by
  set X := (Matrix.denmanBeavers A k).1
  set Y := (Matrix.denmanBeavers A k).2
  have hXY : X = A * Y := equation_9_4_9 hA k
  have hAu : IsUnit A.det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← spectrum.zero_notMem_iff ℂ]
    exact fun h => Complex.slitPlane_ne_zero (hA h) rfl
  -- `X_k` commutes with `A`
  have hcomm : ∀ j, Commute A (Matrix.denmanBeavers A j).1 := by
    intro j
    rw [(Matrix.denmanBeavers_fst_eq_mul_snd hA j).2]
    induction j with
    | zero => exact Commute.refl A
    | succ j ih =>
      rw [Matrix.newtonSqrtIterate]
      exact ((ih.add_right ((Matrix.commute_nonsing_inv_right ih).mul_right
        (Commute.refl A)))).smul_right _
  have hc : Commute A X := hcomm k
  have hY : Y = A⁻¹ * X := by rw [hXY, ← mul_assoc, Matrix.nonsing_inv_mul A hAu, one_mul]
  have hYi : Y⁻¹ = A * X⁻¹ := by
    rw [hY, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv A hAu,
      (Matrix.commute_nonsing_inv_right hc).eq]
  have hAY : Commute A Y := by
    rw [hY]
    exact (Matrix.commute_nonsing_inv_right (Commute.refl A)).mul_right hc
  have hXi : X⁻¹ = A⁻¹ * Y⁻¹ := by
    rw [hXY, Matrix.mul_inv_rev,
      (Matrix.commute_nonsing_inv_right (Matrix.commute_nonsing_inv_right hAY).symm).eq]
  constructor
  · change (2 : ℂ)⁻¹ • (X + Y⁻¹) = _
    rw [hYi]
  · change (2 : ℂ)⁻¹ • (Y + X⁻¹) = _
    rw [hXi]

/-- §9.4.2: `X_k → A^{1/2}`, `Y_k → A^{-1/2}`, and `sign([0 A; I 0]) = [0 A^{1/2}; A^{-1/2} 0]`,
for `A` without eigenvalues on `(-∞, 0]`. -/
theorem sign_block_sqrt {A : Matrix (Fin n) (Fin n) ℂ} (hA : spectrum ℂ A ⊆ Complex.slitPlane) :
    Tendsto (fun k => (Matrix.denmanBeavers A k).1) atTop (𝓝 (Matrix.principalSqrt A)) ∧
    Tendsto (fun k => (Matrix.denmanBeavers A k).2) atTop (𝓝 (Matrix.principalSqrt A)⁻¹) ∧
    Matrix.matrixSign (Matrix.fromBlocks 0 A 1 0) =
      Matrix.fromBlocks 0 (Matrix.principalSqrt A) (Matrix.principalSqrt A)⁻¹ 0 :=
  Matrix.matrixSign_fromBlocks_zero_one hA

/-! ### The matrix logarithm -/

/-- §9.4.4: if the real eigenvalues of `A ∈ ℝ^{n×n}` are all positive, there is a unique real `X`
with `e^X = A` and `λ(X) ⊆ {z : -π < Im z < π}`: the principal logarithm `log(A)`. -/
theorem realLog_existsUnique {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), μ.im = 0 → 0 < μ.re) :
    ∃! X : Matrix (Fin n) (Fin n) ℝ, NormedSpace.exp X = A ∧
      ∀ μ ∈ spectrum ℂ (X.map Complex.ofReal), |μ.im| < Real.pi := by
  refine Matrix.existsUnique_real_exp_eq fun μ hμ => ?_
  rw [Complex.mem_slitPlane_iff]
  by_cases h : μ.im = 0
  · exact Or.inl (hA μ hμ h)
  · exact Or.inr h

open scoped Matrix.Norms.L2Operator in
/-- §9.4.4, the Maclaurin approximant `M_q(A) = ∑_{k=1}^{q} (-1)^{k+1} (A - I)ᵏ/k`: if
`ρ(A - I) < 1` (every eigenvalue within `1` of `1`), then `M_q(A) → log(A)`, and `log(A)` is
Mathlib's series logarithm (in the spectral norm). -/
theorem log_maclaurin {A : Matrix (Fin n) (Fin n) ℂ} (hA : ∀ μ ∈ spectrum ℂ A, ‖μ - 1‖ < 1) :
    HasSum (fun k : ℕ => ((-1) ^ k / (k + 1) : ℂ) • (A - 1) ^ (k + 1)) (Matrix.principalLog A) ∧
    Matrix.principalLog A = NormedSpace.log A :=
  ⟨Matrix.hasSum_principalLog hA,
    pfc_log_eq_normedSpace_log (Algebra.IsIntegral.isIntegral A) hA⟩

/-- §9.4.4, the Gregory approximant
`G_q(A) = -2 ∑_{k=0}^{q} ((I - A)(I + A)⁻¹)^{2k+1}/(2k + 1)`: if every eigenvalue of `A` has
positive real part, then `G_q(A) → log(A)`. -/
theorem log_gregory {A : Matrix (Fin n) (Fin n) ℂ} (hA : ∀ μ ∈ spectrum ℂ A, 0 < μ.re) :
    HasSum (fun k : ℕ => (-2 / (2 * k + 1) : ℂ) • ((1 - A) * (1 + A)⁻¹) ^ (2 * k + 1))
      (Matrix.principalLog A) :=
  Matrix.hasSum_principalLog_gregory hA

/-- §9.4.4: `r₃₃(x) = N(x)/D(x)` with `D(x) = 60 + 90x + 36x² + 3x³` and
`N(x) = 60x + 60x² + 11x³` (the book writes them at `x = A - I`) is the `(3,3)` Padé approximant
of `log(1 + x)`: `D(0) ≠ 0` and `r₃₃(x) - log(1 + x) = O(x⁷)` as `x → 0`. -/
theorem logPade33 :
    (60 + 90 * 0 + 36 * 0 ^ 2 + 3 * 0 ^ 3 : ℂ) ≠ 0 ∧
    (fun x : ℂ => (60 * x + 60 * x ^ 2 + 11 * x ^ 3) / (60 + 90 * x + 36 * x ^ 2 + 3 * x ^ 3) -
      Complex.log (1 + x)) =O[𝓝 0] fun x => x ^ 7 := by
  refine ⟨by norm_num, ?_⟩
  set D : ℂ → ℂ := fun x => 60 + 90 * x + 36 * x ^ 2 + 3 * x ^ 3
  set P : ℂ → ℂ := fun x => -171 / 20 - 27 / 5 * x - 1 / 2 * x ^ 2
  set R : ℂ → ℂ := fun x => Complex.log (1 + x) - Complex.logTaylor 7 x
  have hD : Continuous D := by fun_prop
  have hD0 : D 0 = 60 := by simp [D]
  have hDne : ∀ᶠ x in 𝓝 (0 : ℂ), D x ≠ 0 :=
    hD.continuousAt.eventually_ne (by rw [hD0]; norm_num)
  -- the polynomial part: `D T₆ - N = x⁷ P`
  have hpoly : ∀ x : ℂ, D x * Complex.logTaylor 7 x - (60 * x + 60 * x ^ 2 + 11 * x ^ 3) =
      x ^ 7 * P x := fun x => by
    simp only [D, P, Complex.logTaylor, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    ring
  -- the remainder is `O(x⁷)`
  have hR : R =O[𝓝 0] fun x => x ^ 7 := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    have hb := Complex.norm_log_sub_logTaylor_le 6 (hx.trans (by norm_num))
    have h1 : (1 - ‖x‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    calc ‖R x‖ ≤ ‖x‖ ^ 7 * (1 - ‖x‖)⁻¹ / (6 + 1) := hb
      _ ≤ ‖x‖ ^ 7 * 2 / 1 := by gcongr; norm_num
      _ = 2 * ‖x ^ 7‖ := by rw [norm_pow]; ring
  have hinvD : (fun x => (D x)⁻¹) =O[𝓝 0] fun _ => (1 : ℂ) :=
    ((hD.continuousAt.inv₀ (by rw [hD0]; norm_num)).tendsto).isBigO_one ℂ
  have hPb : P =O[𝓝 0] fun _ => (1 : ℂ) :=
    ((show Continuous P by fun_prop).continuousAt.tendsto).isBigO_one ℂ
  have hmain : (fun x => -(x ^ 7 * P x) * (D x)⁻¹ - R x) =O[𝓝 0] fun x => x ^ 7 := by
    refine IsBigO.sub ?_ hR
    have := ((isBigO_refl (fun x : ℂ => x ^ 7) (𝓝 0)).mul hPb).mul hinvD
    simpa only [mul_one, neg_mul] using this.neg_left
  refine hmain.congr' ?_ EventuallyEq.rfl
  filter_upwards [hDne] with x hx
  have hx' : (60 + 90 * x + 36 * x ^ 2 + 3 * x ^ 3 : ℂ) ≠ 0 := hx
  have hDD : (60 + 90 * x + 36 * x ^ 2 + 3 * x ^ 3 : ℂ) *
      (60 + 90 * x + 36 * x ^ 2 + 3 * x ^ 3)⁻¹ = 1 := mul_inv_cancel₀ hx'
  rw [← hpoly x]
  simp only [R, D]
  rw [div_eq_mul_inv]
  linear_combination (-Complex.logTaylor 7 x) * hDD

/-- §9.4.4, inverse scaling and squaring: with `A₀ = A` and `A_k = A_{k-1}^{1/2}`,
`log(A) = 2^k log(A_k)` for every `k`, when no eigenvalue of `A` lies on `(-∞, 0]`. -/
theorem log_inverse_scaling {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : spectrum ℂ A ⊆ Complex.slitPlane) (k : ℕ) :
    Matrix.principalLog A = (2 ^ k : ℂ) • Matrix.principalLog (Matrix.principalSqrt^[k] A) :=
  Matrix.principalLog_eq_two_pow_smul hA k

end GolubVanLoan.Chapter09
