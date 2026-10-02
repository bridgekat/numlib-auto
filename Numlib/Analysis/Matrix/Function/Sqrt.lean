import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Topology.Instances.Matrix
import Numlib.Analysis.Matrix.Function.Sign

/-!
# The principal square root of a matrix

The principal square root ([golub2013matrix] §9.4.2; Higham, *Functions of Matrices*, Ch. 6)
`A^{1/2} = pfc Complex.sqrt A`, with Mathlib's principal branch `Complex.sqrt z = z ^ (1/2)` (cut
along `(-∞, 0]`, analytic on `Complex.slitPlane`). For `A` with no eigenvalue on `(-∞, 0]` it is the
unique square root whose eigenvalues have positive real part (`Matrix.existsUnique_sq_eq_of_re_pos`)
— the book's definition of `A^{1/2}`, whose existence and uniqueness it leaves implicit.

Newton's iteration (9.4.7) `X_{k+1} = (X_k + X_k⁻¹ A)/2` is the sign iteration in disguise:
`X_k = A^{1/2} S_k` with `S_k` the Newton sign iterates of `A^{1/2}`
(`Matrix.newtonSqrtIterate_eq_mul_newtonSignIterate`), whence convergence. The Denman–Beavers
iteration (9.4.8) is the sign iteration of the block matrix `[0 A; I 0]`
(`Matrix.newtonSignIterate_fromBlocks`), whose sign is `[0 A^{1/2}; A^{-1/2} 0]`
(`Matrix.matrixSign_fromBlocks_zero_one`), whence `X_k → A^{1/2}` and `Y_k → A^{-1/2}`
(`Matrix.tendsto_denmanBeavers_fst`, `Matrix.tendsto_denmanBeavers_snd`).
-/

open Polynomial Filter Topology Complex

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The principal square root** ([golub2013matrix] §9.4.2's `A^{1/2}`):
`pfc Complex.sqrt A`, `Complex.sqrt z = z ^ (1/2)` the principal branch. -/
noncomputable def principalSqrt (A : Matrix n n ℂ) : Matrix n n ℂ :=
  pfc Complex.sqrt A

/-- The square root is analytic on the slit plane. -/
private theorem contDiffAt_sqrt {z : ℂ} (hz : z ∈ slitPlane) : ContDiffAt ℂ ⊤ Complex.sqrt z :=
  (analyticAt_id.cpow analyticAt_const hz).contDiffAt

/-- The principal square root of a point of the slit plane has positive real part. -/
theorem _root_.Complex.re_sqrt_pos {z : ℂ} (hz : z ∈ slitPlane) : 0 < (Complex.sqrt z).re := by
  rw [Complex.sqrt, cpow_inv_two_re]
  refine Real.sqrt_pos.mpr (half_pos ?_)
  rcases mem_slitPlane_iff.mp hz with h | h
  · linarith [norm_nonneg z]
  · have := Complex.abs_re_lt_norm.mpr h
    linarith [neg_abs_le z.re]

/-- The principal square root maps the slit plane into itself (into the right half-plane). -/
theorem _root_.Complex.sqrt_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) :
    Complex.sqrt z ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl (Complex.re_sqrt_pos hz))

/-- **The principal square root is a square root** ([golub2013matrix] §9.4.2): with no eigenvalue
on `(-∞, 0]`, `(A^{1/2})² = A`, `A^{1/2}` commutes with `A`, and its eigenvalues have positive real
part. -/
theorem principalSqrt_sq {A : Matrix n n ℂ} (hA : spectrum ℂ A ⊆ slitPlane) :
    principalSqrt A ^ 2 = A ∧ Commute A (principalSqrt A) ∧
      ∀ μ ∈ spectrum ℂ (principalSqrt A), 0 < μ.re := by
  have hI : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral _
  refine ⟨?_, commute_pfc A _, ?_⟩
  · have h := pfc_comp hI (IsAlgClosed.splits _) (f := Complex.sqrt) (g := fun w => w ^ 2)
      (fun μ hμ => (contDiffAt_sqrt (hA (spectrum.mem_of_mem_roots_minpoly hμ))).of_le le_top)
      (fun μ _ => (contDiff_id.pow 2).contDiffAt)
    rw [pfc_pow (Algebra.IsIntegral.isIntegral _) (IsAlgClosed.splits _)] at h
    rw [principalSqrt, ← h]
    have hsq : (fun w : ℂ => w ^ 2) ∘ Complex.sqrt = fun z => z := by
      funext z
      simp [Complex.sqrt, cpow_ofNat_inv_pow]
    rw [hsq, pfc_id hI (IsAlgClosed.splits _)]
  · rw [principalSqrt, spectrum_pfc hI (IsAlgClosed.splits _)]
    rintro _ ⟨μ, hμ, rfl⟩
    exact Complex.re_sqrt_pos (hA hμ)

/-- **Existence and uniqueness of the principal square root** ([golub2013matrix] §9.4.2): with no
eigenvalue on `(-∞, 0]`, `A^{1/2}` is the only square root of `A` with eigenvalues in the open right
half-plane. Uniqueness (after Higham, *Functions of Matrices*, Theorem 1.29, without simultaneous
triangularization): `G = A^{1/2}` is a polynomial `q(F)` in any such root `F`, with `q(μ) = μ` on
the spectrum of `F`, so `F + G` has eigenvalues `2μ ≠ 0`, and `(F - G)(F + G) = F² - G² = 0`. -/
theorem existsUnique_sq_eq_of_re_pos {A : Matrix n n ℂ} (hA : spectrum ℂ A ⊆ slitPlane) :
    ∃! F : Matrix n n ℂ, F ^ 2 = A ∧ ∀ μ ∈ spectrum ℂ F, 0 < μ.re := by
  classical
  obtain ⟨hsq, -, hre⟩ := principalSqrt_sq hA
  refine ⟨principalSqrt A, ⟨hsq, hre⟩, fun F ⟨hF, hFre⟩ => ?_⟩
  have hI : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral _
  have hFI : IsIntegral ℂ F := Algebra.IsIntegral.isIntegral _
  set p := Hermite.interpolateJet (minpoly ℂ A).roots (Hermite.taylorJet Complex.sqrt)
  set q := p.comp (X ^ 2)
  have hG : principalSqrt A = aeval F q := by
    rw [principalSqrt, pfc_def, aeval_comp, map_pow, aeval_X, hF]
  -- `q(μ) = μ` on the spectrum of `F`
  have hq : ∀ μ ∈ spectrum ℂ F, q.eval μ = μ := fun μ hμ => by
    have hμ2 : μ ^ 2 ∈ (minpoly ℂ A).roots := by
      have : μ ^ 2 ∈ spectrum ℂ A := by
        rw [← hF, ← pfc_pow hFI (IsAlgClosed.splits _), spectrum_pfc hFI (IsAlgClosed.splits _)]
        exact ⟨μ, hμ, rfl⟩
      exact (spectrum.mem_iff_mem_roots_minpoly hI).1 this
    rw [eval_comp, eval_pow, eval_X, Hermite.eval_interpolateJet_taylorJet hμ2, Complex.sqrt,
      sq_cpow_two_inv (hFre μ hμ)]
  have hunit : IsUnit (F + principalSqrt A) := by
    rw [hG, ← spectrum.zero_notMem_iff ℂ]
    have h1 : F + aeval F q = pfc (fun z => (X + q).eval z) F := by
      rw [pfc_polynomial hFI (IsAlgClosed.splits _), map_add, aeval_X]
    rw [h1, spectrum_pfc hFI (IsAlgClosed.splits _)]
    rintro ⟨μ, hμ, h0⟩
    simp only [eval_add, eval_X] at h0
    rw [hq μ hμ] at h0
    have := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.zero_re] at this
    linarith [hFre μ hμ]
  have hc : Commute F (principalSqrt A) := by
    rw [hG]
    simpa using commute_aeval_aeval F X q
  have h0 : (F - principalSqrt A) * (F + principalSqrt A) = 0 := by
    rw [sub_mul, mul_add, mul_add, hc.eq, ← sq, ← sq, hF, hsq]
    abel
  rw [← sub_eq_zero]
  exact (hunit.mul_left_eq_zero).mp h0

/-! ### Newton's iteration -/

/-- **Newton's iteration for the square root** ([golub2013matrix] (9.4.7)): `X₀ = A`,
`X_{k+1} = (X_k + X_k⁻¹ A)/2`. -/
noncomputable def newtonSqrtIterate (A : Matrix n n ℂ) : ℕ → Matrix n n ℂ
  | 0 => A
  | k + 1 => (2 : ℂ)⁻¹ • (newtonSqrtIterate A k + (newtonSqrtIterate A k)⁻¹ * A)

/-- **Newton's square root iteration is the sign iteration** ([golub2013matrix] §9.4.2): with no
eigenvalue on `(-∞, 0]`, `X_k = A^{1/2} S_k` for the Newton sign iterates `S_k` of `A^{1/2}`. -/
theorem newtonSqrtIterate_eq_mul_newtonSignIterate {A : Matrix n n ℂ}
    (hA : spectrum ℂ A ⊆ slitPlane) (k : ℕ) :
    newtonSqrtIterate A k = principalSqrt A * newtonSignIterate (principalSqrt A) k := by
  obtain ⟨hsq, -, hre⟩ := principalSqrt_sq hA
  set R := principalSqrt A
  have hR : ∀ μ ∈ spectrum ℂ R, μ.re ≠ 0 := fun μ hμ => (hre μ hμ).ne'
  have hRu : IsUnit R := by
    rw [← spectrum.zero_notMem_iff ℂ]
    intro h0
    simpa using hre 0 h0
  have hRdet := (isUnit_iff_isUnit_det R).mp hRu
  induction k with
  | zero =>
    rw [newtonSignIterate_zero, ← sq, hsq]
    rfl
  | succ k ih =>
    set S := newtonSignIterate R k
    have hSu := (isUnit_newtonSignIterate hR k).1
    have hSdet := (isUnit_iff_isUnit_det S).mp hSu
    have hc : Commute R S := commute_newtonSignIterate R k
    change (2 : ℂ)⁻¹ • (newtonSqrtIterate A k + (newtonSqrtIterate A k)⁻¹ * A) = _
    rw [ih, newtonSignIterate_succ, mul_smul_comm, mul_add, mul_inv_rev, ← hsq, sq]
    congr 2
    rw [mul_assoc, ← mul_assoc R⁻¹, nonsing_inv_mul _ hRdet, one_mul,
      (commute_nonsing_inv_right hc).symm.eq]

/-- **Convergence of Newton's square root iteration** ([golub2013matrix] §9.4.2): with no eigenvalue
on `(-∞, 0]`, `X_k → A^{1/2}`, since `S_k → sign(A^{1/2}) = 1`. -/
theorem tendsto_newtonSqrtIterate {A : Matrix n n ℂ} (hA : spectrum ℂ A ⊆ slitPlane) :
    Tendsto (newtonSqrtIterate A) atTop (𝓝 (principalSqrt A)) := by
  obtain ⟨-, -, hre⟩ := principalSqrt_sq hA
  have hR : ∀ μ ∈ spectrum ℂ (principalSqrt A), μ.re ≠ 0 := fun μ hμ => (hre μ hμ).ne'
  have h := (tendsto_newtonSignIterate hR).const_mul (principalSqrt A)
  rw [matrixSign_eq_one_of_re_pos hre, mul_one] at h
  exact h.congr fun k => (newtonSqrtIterate_eq_mul_newtonSignIterate hA k).symm

/-! ### The Denman–Beavers iteration -/

/-- **The Denman–Beavers iteration** ([golub2013matrix] (9.4.8)): `(X₀, Y₀) = (A, 1)`,
`X_{k+1} = (X_k + Y_k⁻¹)/2`, `Y_{k+1} = (Y_k + X_k⁻¹)/2`. -/
noncomputable def denmanBeavers (A : Matrix n n ℂ) : ℕ → Matrix n n ℂ × Matrix n n ℂ
  | 0 => (A, 1)
  | k + 1 => ((2 : ℂ)⁻¹ • ((denmanBeavers A k).1 + (denmanBeavers A k).2⁻¹),
      (2 : ℂ)⁻¹ • ((denmanBeavers A k).2 + (denmanBeavers A k).1⁻¹))

/-- The inverse of a block antidiagonal matrix. -/
private theorem fromBlocks_antidiag_mul {X Y : Matrix n n ℂ} (hX : IsUnit X) (hY : IsUnit Y) :
    fromBlocks 0 X Y 0 * fromBlocks 0 Y⁻¹ X⁻¹ 0 = 1 := by
  rw [fromBlocks_multiply]
  simp [mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hX),
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hY), fromBlocks_one]

/-- The spectrum of `[0 A; I 0]` avoids the imaginary axis when that of `A` avoids `(-∞, 0]`: its
square is `diag(A, A)`. -/
private theorem re_ne_zero_of_mem_spectrum_fromBlocks {A : Matrix n n ℂ}
    (hA : spectrum ℂ A ⊆ slitPlane) :
    ∀ μ ∈ spectrum ℂ (fromBlocks 0 A (1 : Matrix n n ℂ) 0), μ.re ≠ 0 := by
  intro μ hμ hre
  set T : Matrix (n ⊕ n) (n ⊕ n) ℂ := fromBlocks 0 A 1 0
  have hTI : IsIntegral ℂ T := Algebra.IsIntegral.isIntegral _
  have hT2 : T ^ 2 = fromBlocks A 0 0 A := by
    rw [sq, fromBlocks_multiply]
    simp
  have hμ2 : μ ^ 2 ∈ spectrum ℂ (fromBlocks A 0 0 A) := by
    rw [← hT2, ← pfc_pow hTI (IsAlgClosed.splits _), spectrum_pfc hTI (IsAlgClosed.splits _)]
    exact ⟨μ, hμ, rfl⟩
  have hμA : μ ^ 2 ∈ spectrum ℂ A := by
    by_contra h
    apply hμ2
    rw [spectrum.notMem_iff] at h
    rw [spectrum.mem_resolventSet_iff]
    obtain ⟨u, hu⟩ := h
    refine ⟨⟨fromBlocks u 0 0 u, fromBlocks ↑u⁻¹ 0 0 ↑u⁻¹, ?_, ?_⟩, ?_⟩
    · rw [fromBlocks_multiply]; simp [fromBlocks_one]
    · rw [fromBlocks_multiply]; simp [fromBlocks_one]
    · simp only [hu, Algebra.algebraMap_eq_smul_one]
      ext (i | i) (j | j) <;> simp [fromBlocks, one_apply]
  have hneg : μ ^ 2 = ((-(μ.im ^ 2) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [sq, hre]
  have := hA hμA
  rw [hneg, ofReal_mem_slitPlane] at this
  nlinarith [sq_nonneg μ.im]

/-- **The Denman–Beavers iteration is the sign iteration of `[0 A; I 0]`**
([golub2013matrix] §9.4.2): with no eigenvalue of `A` on `(-∞, 0]`, the Newton sign iterates of
`Ã = [0 A; I 0]` are `[0 X_k; Y_k 0]`, all `X_k`, `Y_k` invertible. -/
theorem newtonSignIterate_fromBlocks {A : Matrix n n ℂ} (hA : spectrum ℂ A ⊆ slitPlane) (k : ℕ) :
    newtonSignIterate (fromBlocks 0 A 1 0) k =
        fromBlocks 0 (denmanBeavers A k).1 (denmanBeavers A k).2 0 ∧
      IsUnit (denmanBeavers A k).1 ∧ IsUnit (denmanBeavers A k).2 := by
  have hT := re_ne_zero_of_mem_spectrum_fromBlocks hA
  have hunits : ∀ {X Y : Matrix n n ℂ}, IsUnit (fromBlocks 0 X Y 0) → IsUnit X ∧ IsUnit Y := by
    intro X Y h
    obtain ⟨u, hu⟩ := h
    have h1 := u.mul_inv
    rw [hu] at h1
    set V := (↑u⁻¹ : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    have hV : V = fromBlocks (V.toBlocks₁₁) (V.toBlocks₁₂) (V.toBlocks₂₁) (V.toBlocks₂₂) :=
      (fromBlocks_toBlocks V).symm
    rw [hV, fromBlocks_multiply, ← fromBlocks_one] at h1
    simp only [zero_mul, zero_add, add_zero, fromBlocks_inj] at h1
    exact ⟨(isUnit_iff_isUnit_det _).mpr (isUnit_det_of_right_inverse h1.1),
      (isUnit_iff_isUnit_det _).mpr (isUnit_det_of_right_inverse h1.2.2.2)⟩
  induction k with
  | zero =>
    refine ⟨rfl, ?_, isUnit_one⟩
    exact (hunits ((isUnit_newtonSignIterate hT 0).1)).1
  | succ k ih =>
    obtain ⟨hk, hX, hY⟩ := ih
    have hS : newtonSignIterate (fromBlocks 0 A 1 0) (k + 1) =
        fromBlocks 0 (denmanBeavers A (k + 1)).1 (denmanBeavers A (k + 1)).2 0 := by
      rw [newtonSignIterate_succ, hk,
        inv_eq_right_inv (fromBlocks_antidiag_mul hX hY), fromBlocks_add, fromBlocks_smul]
      simp [denmanBeavers]
    refine ⟨hS, hunits ?_⟩
    rw [← hS]
    exact (isUnit_newtonSignIterate hT (k + 1)).1

/-- **[golub2013matrix] (9.4.9)–(9.4.10)**: `X_k = A Y_k`, and `X_k` is Newton's square root
iterate. -/
theorem denmanBeavers_fst_eq_mul_snd {A : Matrix n n ℂ} (hA : spectrum ℂ A ⊆ slitPlane)
    (k : ℕ) : (denmanBeavers A k).1 = A * (denmanBeavers A k).2 ∧
      (denmanBeavers A k).1 = newtonSqrtIterate A k := by
  have hAu : IsUnit A := by
    rw [← spectrum.zero_notMem_iff ℂ]
    intro h0
    simpa using hA h0
  have hAdet := (isUnit_iff_isUnit_det A).mp hAu
  -- `Y_k` commutes with `A`
  have hcomm : ∀ k, Commute A (denmanBeavers A k).2 ∧ Commute A (denmanBeavers A k).1 := by
    intro k
    induction k with
    | zero => exact ⟨Commute.one_right A, Commute.refl A⟩
    | succ k ih =>
      obtain ⟨hY, hX⟩ := ih
      exact ⟨(hY.add_right (commute_nonsing_inv_right hX)).smul_right _,
        (hX.add_right (commute_nonsing_inv_right hY)).smul_right _⟩
  induction k with
  | zero => exact ⟨(mul_one A).symm, rfl⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨-, hX, hY⟩ := newtonSignIterate_fromBlocks hA k
    have hYdet := (isUnit_iff_isUnit_det _).mp hY
    have hinv : (denmanBeavers A k).1⁻¹ = (denmanBeavers A k).2⁻¹ * A⁻¹ := by
      rw [h1, mul_inv_rev]
    refine ⟨?_, ?_⟩
    · change (2 : ℂ)⁻¹ • ((denmanBeavers A k).1 + (denmanBeavers A k).2⁻¹) =
        A * ((2 : ℂ)⁻¹ • ((denmanBeavers A k).2 + (denmanBeavers A k).1⁻¹))
      rw [mul_smul_comm, mul_add, ← h1, hinv, ← mul_assoc,
        (commute_nonsing_inv_right (hcomm k).1).eq, mul_assoc, mul_nonsing_inv _ hAdet, mul_one]
    · change (2 : ℂ)⁻¹ • ((denmanBeavers A k).1 + (denmanBeavers A k).2⁻¹) =
        (2 : ℂ)⁻¹ • (newtonSqrtIterate A k + (newtonSqrtIterate A k)⁻¹ * A)
      rw [← h2, hinv, mul_assoc, nonsing_inv_mul _ hAdet, mul_one]

/-- **The Denman–Beavers iteration converges to the square root** ([golub2013matrix] §9.4.2):
with no eigenvalue of `A` on `(-∞, 0]`, `X_k → A^{1/2}`. -/
theorem tendsto_denmanBeavers_fst {A : Matrix n n ℂ} (hA : spectrum ℂ A ⊆ slitPlane) :
    Tendsto (fun k => (denmanBeavers A k).1) atTop (𝓝 (principalSqrt A)) :=
  (tendsto_newtonSqrtIterate hA).congr fun k => ((denmanBeavers_fst_eq_mul_snd hA k).2).symm

/-- **The Denman–Beavers iteration converges to the inverse square root** ([golub2013matrix]
§9.4.2): with no eigenvalue of `A` on `(-∞, 0]`, `Y_k → A^{-1/2}`. -/
theorem tendsto_denmanBeavers_snd {A : Matrix n n ℂ} (hA : spectrum ℂ A ⊆ slitPlane) :
    Tendsto (fun k => (denmanBeavers A k).2) atTop (𝓝 (principalSqrt A)⁻¹) := by
  obtain ⟨hsq, -, -⟩ := principalSqrt_sq hA
  have hAu : IsUnit A := by
    rw [← spectrum.zero_notMem_iff ℂ]
    intro h0
    simpa using hA h0
  have hAdet := (isUnit_iff_isUnit_det A).mp hAu
  have h := (tendsto_denmanBeavers_fst hA).const_mul A⁻¹
  have hR : A⁻¹ * principalSqrt A = (principalSqrt A)⁻¹ := by
    generalize principalSqrt A = R at hsq ⊢
    subst hsq
    have hRdet : IsUnit R.det := by
      have := (isUnit_iff_isUnit_det _).mp hAu
      rwa [det_pow, isUnit_pow_iff two_ne_zero] at this
    rw [sq, mul_inv_rev, Matrix.mul_assoc, nonsing_inv_mul _ hRdet, Matrix.mul_one]
  rw [hR] at h
  refine h.congr fun k => ?_
  rw [(denmanBeavers_fst_eq_mul_snd hA k).1, ← mul_assoc, nonsing_inv_mul _ hAdet, one_mul]

/-- **The sign of `[0 A; I 0]`** ([golub2013matrix] §9.4.2): with no eigenvalue of `A` on
`(-∞, 0]`, `sign([0 A; I 0]) = [0 A^{1/2}; A^{-1/2} 0]`, the limit of the Newton sign iteration,
whose iterates are the Denman–Beavers pairs (`Matrix.tendsto_denmanBeavers_fst`,
`Matrix.tendsto_denmanBeavers_snd`). -/
theorem matrixSign_fromBlocks_zero_one {A : Matrix n n ℂ} (hA : spectrum ℂ A ⊆ slitPlane) :
    matrixSign (fromBlocks 0 A 1 0) = fromBlocks 0 (principalSqrt A) (principalSqrt A)⁻¹ 0 := by
  have hX := tendsto_denmanBeavers_fst hA
  have hY := tendsto_denmanBeavers_snd hA
  have hS := tendsto_newtonSignIterate (re_ne_zero_of_mem_spectrum_fromBlocks hA)
  have hS' : Tendsto (fun k => newtonSignIterate (fromBlocks 0 A 1 0) k) atTop
      (𝓝 (fromBlocks 0 (principalSqrt A) (principalSqrt A)⁻¹ 0)) := by
    refine ((continuous_const.matrix_fromBlocks continuous_fst continuous_snd
      continuous_const).tendsto _ |>.comp (hX.prodMk_nhds hY)).congr fun k => ?_
    exact ((newtonSignIterate_fromBlocks hA k).1).symm
  exact tendsto_nhds_unique hS hS'

end Matrix
