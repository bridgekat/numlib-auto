/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Normed.Algebra.SpectralRadius
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic

/-!
# Complexification of real matrices

`Matrix.complexify A = A.map Complex.ofReal`, its characteristic polynomial and spectrum, and the
spectral radius of a real matrix *defined as* the spectral radius of its complexification
(`Matrix.complexSpectralRadius`). This is the only meaningful notion for real matrices:
`spectralRadius ℝ` of the rotation `![![0, -1], ![1, 0]]` is `0` (empty real spectrum) although
its powers do not tend to `0`, so `spectralRadius ℝ G < 1 → Gᵏ → 0` is **false** over `ℝ`; all
Gelfand-formula results (`Numlib/Analysis/Normed/Algebra/SpectralRadius.lean`) are used over `ℂ` and
transported through `complexify`.

`Matrix.complexSpectralRadius_le_of_norm` bounds the spectral radius by any submultiplicative,
absolutely homogeneous, positive definite matrix norm; the three scoped norms of
`Mathlib.Analysis.Matrix.Normed` and `Mathlib.Analysis.CStarAlgebra.Matrix` are recorded as
corollaries at the end of the file.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace Matrix

variable {n : Type*}

/-- The complexification of a real matrix. -/
def complexify (A : Matrix n n ℝ) : Matrix n n ℂ := A.map Complex.ofReal

@[simp] theorem complexify_apply (A : Matrix n n ℝ) (i j : n) : complexify A i j = A i j := rfl

@[simp] theorem complexify_zero : complexify (0 : Matrix n n ℝ) = 0 := by
  ext i j; simp

theorem complexify_add (A B : Matrix n n ℝ) : complexify (A + B) = complexify A + complexify B := by
  ext i j; simp

theorem complexify_neg (A : Matrix n n ℝ) : complexify (-A) = -complexify A := by
  ext i j; simp

theorem complexify_sub (A B : Matrix n n ℝ) : complexify (A - B) = complexify A - complexify B := by
  ext i j; simp

theorem complexify_smul (c : ℝ) (A : Matrix n n ℝ) :
    complexify (c • A) = (c : ℂ) • complexify A := by
  ext i j; simp

theorem complexify_injective : Function.Injective (complexify (n := n)) := by
  intro A B hAB
  ext i j
  have h : ((A i j : ℝ) : ℂ) = ((B i j : ℝ) : ℂ) := congrFun (congrFun hAB i) j
  exact_mod_cast h

theorem complexify_transpose (A : Matrix n n ℝ) : complexify Aᵀ = (complexify A)ᵀ := by
  ext i j; simp

/-- Conjugate transposition commutes with complexification: the entries of `complexify A` are
real, so conjugating them does nothing. -/
theorem complexify_conjTranspose (A : Matrix n n ℝ) : complexify Aᴴ = (complexify A)ᴴ := by
  ext i j; simp

/-- A real matrix is symmetric exactly when its complexification is Hermitian. -/
@[simp] theorem isHermitian_complexify_iff (A : Matrix n n ℝ) :
    IsHermitian (complexify A) ↔ IsHermitian A := by
  refine ⟨fun h => complexify_injective ?_, fun h => ?_⟩
  · rw [complexify_conjTranspose]
    exact h.eq
  · exact (complexify_conjTranspose A).symm.trans (congrArg complexify h.eq)

theorem complexify_mul [Fintype n] (A B : Matrix n n ℝ) :
    complexify (A * B) = complexify A * complexify B := by
  ext i j
  simp only [complexify_apply, Matrix.mul_apply]
  push_cast
  rfl

/-- `Matrix.complexify` as an `ℝ`-linear map; it is used to compare the topologies of
`Matrix n n ℝ` and `Matrix n n ℂ`. -/
private def complexifyₗ : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℂ where
  toFun := complexify
  map_add' := complexify_add
  map_smul' c A := by ext i j; simp [Complex.real_smul]

variable [DecidableEq n]

@[simp] theorem complexify_one : complexify (1 : Matrix n n ℝ) = 1 :=
  Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one

variable [Fintype n]

theorem complexify_pow (A : Matrix n n ℝ) (k : ℕ) : complexify (A ^ k) = complexify A ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, complexify_mul, ih]

@[simp] theorem det_complexify (A : Matrix n n ℝ) : (complexify A).det = ((A.det : ℝ) : ℂ) :=
  (RingHom.map_det Complex.ofRealHom A).symm

theorem isUnit_complexify_iff (A : Matrix n n ℝ) : IsUnit (complexify A) ↔ IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, det_complexify]
  simp [isUnit_iff_ne_zero]

/-- `charpoly (complexify A) = charpoly A` mapped to `ℂ` (Mathlib: `Matrix.charpoly_map`). -/
theorem charpoly_complexify (A : Matrix n n ℝ) :
    (complexify A).charpoly = A.charpoly.map (algebraMap ℝ ℂ) := by
  have h : complexify A = A.map (algebraMap ℝ ℂ) := rfl
  rw [h, Matrix.charpoly_map]

theorem mem_spectrum_complexify_iff (A : Matrix n n ℝ) (μ : ℂ) :
    μ ∈ spectrum ℂ (complexify A) ↔ (A.charpoly.map (algebraMap ℝ ℂ)).IsRoot μ := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, charpoly_complexify]

/-- Real eigenvalues of `A` are exactly the real points of the complex spectrum. -/
theorem ofReal_mem_spectrum_complexify_iff (A : Matrix n n ℝ) (μ : ℝ) :
    (μ : ℂ) ∈ spectrum ℂ (complexify A) ↔ μ ∈ spectrum ℝ A := by
  rw [mem_spectrum_complexify_iff, Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def,
    Polynomial.IsRoot.def, Polynomial.eval_map, ← Complex.coe_algebraMap,
    Polynomial.eval₂_at_apply]
  simp

/-- The spectral radius of a real matrix, computed over `ℂ`. -/
noncomputable def complexSpectralRadius (A : Matrix n n ℝ) : ENNReal :=
  spectralRadius ℂ (complexify A)

@[simp] theorem complexSpectralRadius_zero : complexSpectralRadius (0 : Matrix n n ℝ) = 0 := by
  rw [complexSpectralRadius, complexify_zero, spectrum.spectralRadius_zero]

/-- The spectral radius is absolutely homogeneous. -/
theorem complexSpectralRadius_smul (c : ℝ) (A : Matrix n n ℝ) :
    complexSpectralRadius (c • A) = ‖c‖₊ * complexSpectralRadius A := by
  rw [complexSpectralRadius, complexify_smul, spectralRadius_smul, complexSpectralRadius]
  simp

/-- `ρ(A)ᵏ ≤ ρ(Aᵏ)` (Mathlib: `spectrum.spectralRadius_pow_le`; equality holds by the spectral
mapping theorem, but the inequality is all the Gelfand-formula arguments need). -/
theorem complexSpectralRadius_pow_le (A : Matrix n n ℝ) {k : ℕ} (hk : k ≠ 0) :
    complexSpectralRadius A ^ k ≤ complexSpectralRadius (A ^ k) := by
  rw [complexSpectralRadius, complexSpectralRadius, complexify_pow]
  exact spectrum.spectralRadius_pow_le _ k hk

theorem spectralRadius_le_complexSpectralRadius (A : Matrix n n ℝ) :
    spectralRadius ℝ A ≤ complexSpectralRadius A := by
  refine iSup₂_le fun μ hμ => ?_
  have hμ' : (μ : ℂ) ∈ spectrum ℂ (complexify A) :=
    (ofReal_mem_spectrum_complexify_iff A μ).mpr hμ
  calc (‖μ‖₊ : ENNReal) = (‖(μ : ℂ)‖₊ : ENNReal) := by simp
    _ ≤ complexSpectralRadius A := le_iSup₂ (α := ENNReal) (μ : ℂ) hμ'

/-- `Matrix.toEuclideanCLM` as a bare `ℂ`-linear map; used to compare the product topology on
`Matrix n n ℂ` with the operator-norm topology of the Banach algebra it is isomorphic to. -/
private noncomputable def toEuclideanCLMₗ :
    Matrix n n ℂ →ₗ[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) where
  toFun M := toEuclideanCLM (n := n) (𝕜 := ℂ) M
  map_add' := map_add _
  map_smul' c M := map_smul _ c M

/-- Convergence of matrix powers in the product topology is convergence of the powers of the
corresponding operator in the operator norm. -/
private theorem tendsto_pow_iff_tendsto_pow_toEuclideanCLM (M : Matrix n n ℂ) :
    Tendsto (fun k => M ^ k) atTop (𝓝 0) ↔
      Tendsto (fun k => toEuclideanCLM (n := n) (𝕜 := ℂ) M ^ k) atTop (𝓝 0) := by
  have hinj : Function.Injective (toEuclideanCLMₗ (n := n)) := fun _ _ h =>
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).injective h
  have hemb : Topology.IsEmbedding (toEuclideanCLMₗ (n := n)) :=
    (LinearMap.isClosedEmbedding_of_injective (f := toEuclideanCLMₗ (n := n))
      (LinearMap.ker_eq_bot.mpr hinj)).isEmbedding
  rw [hemb.tendsto_nhds_iff, map_zero]
  simp only [Function.comp_def, toEuclideanCLMₗ, LinearMap.coe_mk, AddHom.coe_mk, map_pow]

/-- `Aᵏ → 0` iff `ρ(A) < 1`, for real matrices (via the complexification and the Gelfand
formula). -/
theorem tendsto_pow_iff_complexSpectralRadius_lt_one (A : Matrix n n ℝ) :
    Tendsto (fun k => A ^ k) atTop (𝓝 0) ↔ complexSpectralRadius A < 1 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hsubR : Subsingleton (Matrix n n ℝ) := ⟨fun _ _ => by ext i; exact isEmptyElim i⟩
    have hsubC : Subsingleton (Matrix n n ℂ) := ⟨fun _ _ => by ext i; exact isEmptyElim i⟩
    have hle : complexSpectralRadius A ≤ 0 :=
      iSup₂_le fun k hk => absurd (isUnit_of_subsingleton _) hk
    have hconv : Tendsto (fun k => A ^ k) atTop (𝓝 0) := by
      have : (fun k => A ^ k) = fun _ : ℕ => (0 : Matrix n n ℝ) :=
        funext fun _ => Subsingleton.elim _ _
      rw [this]
      exact tendsto_const_nhds
    exact iff_of_true hconv (hle.trans_lt zero_lt_one)
  · have hR : Tendsto (fun k => A ^ k) atTop (𝓝 0) ↔
        Tendsto (fun k => complexify A ^ k) atTop (𝓝 0) := by
      have hemb : Topology.IsEmbedding (complexifyₗ (n := n)) :=
        (LinearMap.isClosedEmbedding_of_injective (f := complexifyₗ (n := n))
          (LinearMap.ker_eq_bot.mpr complexify_injective)).isEmbedding
      rw [hemb.tendsto_nhds_iff]
      simp only [Function.comp_def, complexifyₗ, LinearMap.coe_mk, AddHom.coe_mk, complexify_pow,
        map_zero]
    have hspec : spectrum ℂ (toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A))
        = spectrum ℂ (complexify A) :=
      AlgEquiv.spectrum_eq (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) (complexify A)
    have hsr : spectralRadius ℂ (toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A))
        = complexSpectralRadius A := by
      simp only [spectralRadius, complexSpectralRadius, hspec]
    rw [hR, tendsto_pow_iff_tendsto_pow_toEuclideanCLM,
      ← spectralRadius_lt_one_iff_tendsto_pow, hsr]

/-- Neumann: `ρ(A) < 1` makes `1 - A` invertible over `ℝ`. The complex spectral radius is what
matters, as `spectralRadius ℝ` can be `0` for a matrix with `1 ∈ spectrum ℂ`. -/
theorem isUnit_one_sub_of_complexSpectralRadius_lt_one {A : Matrix n n ℝ}
    (h : complexSpectralRadius A < 1) : IsUnit (1 - A) := by
  rw [← isUnit_complexify_iff, complexify_sub, complexify_one]
  have h' : spectralRadius ℂ (complexify A) < 1 := h
  have h1 : (1 : ℂ) ∈ resolventSet ℂ (complexify A) :=
    spectrum.mem_resolventSet_of_spectralRadius_lt (by simpa using h')
  simpa [resolventSet] using h1

/-! ### The spectral radius is bounded by every matrix norm

The norm is carried by an explicit function `f : Matrix n n ℝ → ℝ≥0` rather than by
`[NormedRing (Matrix n n ℝ)]` and friends.  This is not a stylistic choice: an instance argument
`[NormedRing (Matrix n n ℝ)]` carries a `Ring` structure on the *type* `Matrix n n ℝ` that is
unrelated to `Matrix.instRing`, and the statement
`[NormedRing (Matrix n n ℝ)] [NormOneClass (Matrix n n ℝ)] [NormedAlgebra ℝ (Matrix n n ℝ)] →
complexSpectralRadius A ≤ ‖A‖₊` is therefore **false**.  A counterexample: for finite nonempty `n`
pick a bijection `e : Matrix n n ℝ ≃ ℝ` with `e 1 = 1` and `e A = 0` for `A = (2 : ℝ) • 1`, and
transport the normed field structure of `ℝ` along `e`.  All three classes hold (`NormOneClass`
elaborates against `Matrix.one`, which `e` sends to `1`), yet `‖A‖ = 0` while
`complexSpectralRadius A = 2`, which is computed from the canonical structures.  Taking `f` as a
plain function keeps every hypothesis attached to the canonical `Ring` and `Module ℝ` structures
of `Matrix n n ℝ`.
-/

section NormBound

variable (f : Matrix n n ℝ → ℝ≥0)

omit [DecidableEq n] in
/-- A submultiplicative, absolutely homogeneous, positive definite `f` dominates the entries of a
matrix up to one constant: `‖B i j‖ ≤ c * f B` for all `B`, `i`, `j`.

The constant comes from the matrix units `Matrix.single i j 1`, for which
`single i i 1 * B * single j j 1 = B i j • single i j 1`
(Mathlib: `Matrix.single_mul_mul_single`); positive definiteness is what makes
`f (single i j 1)` invertible. -/
theorem exists_nnnorm_apply_le (hmul : ∀ B C : Matrix n n ℝ, f (B * C) ≤ f B * f C)
    (hsmul : ∀ (r : ℝ) (B : Matrix n n ℝ), f (r • B) = ‖r‖₊ * f B)
    (hzero : ∀ B : Matrix n n ℝ, f B = 0 → B = 0) :
    ∃ c : ℝ≥0, ∀ (B : Matrix n n ℝ) (i j : n), ‖B i j‖₊ ≤ c * f B := by
  classical
  have hne : ∀ i j : n, f (single i j (1 : ℝ)) ≠ 0 := by
    intro i j h
    have h0 := hzero _ h
    have h1 : (single i j (1 : ℝ)) i j = 0 := by rw [h0]; simp
    simp at h1
  refine ⟨Finset.univ.sup fun p : n × n =>
    f (single p.1 p.1 (1 : ℝ)) * f (single p.2 p.2 (1 : ℝ)) / f (single p.1 p.2 (1 : ℝ)), ?_⟩
  intro B i j
  have key : single i i (1 : ℝ) * B * single j j (1 : ℝ) = B i j • single i j (1 : ℝ) := by
    rw [single_mul_mul_single, smul_single]
    simp
  have h1 : f (single i i (1 : ℝ) * B * single j j (1 : ℝ))
      ≤ f (single i i (1 : ℝ)) * f B * f (single j j (1 : ℝ)) :=
    (hmul _ _).trans (by gcongr; exact hmul _ _)
  rw [key, hsmul] at h1
  have h2 : ‖B i j‖₊ ≤ f (single i i (1 : ℝ)) * f B * f (single j j (1 : ℝ))
      / f (single i j (1 : ℝ)) := by
    rw [le_div_iff₀ (pos_iff_ne_zero.mpr (hne i j))]
    exact h1
  refine h2.trans ?_
  have h3 : f (single i i (1 : ℝ)) * f B * f (single j j (1 : ℝ)) / f (single i j (1 : ℝ))
      = (f (single i i (1 : ℝ)) * f (single j j (1 : ℝ)) / f (single i j (1 : ℝ))) * f B := by
    ring
  rw [h3]
  gcongr
  exact Finset.le_sup (f := fun p : n × n =>
    f (single p.1 p.1 (1 : ℝ)) * f (single p.2 p.2 (1 : ℝ)) / f (single p.1 p.2 (1 : ℝ)))
    (Finset.mem_univ (i, j))

/-- Submultiplicativity iterated over the positive powers. Stated from exponent `1` because
nothing forces `f 1 ≤ 1`. -/
private theorem apply_pow_le (hmul : ∀ B C : Matrix n n ℝ, f (B * C) ≤ f B * f C)
    (B : Matrix n n ℝ) (k : ℕ) : f (B ^ (k + 1)) ≤ f B ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc f (B ^ (k + 1 + 1)) = f (B ^ (k + 1) * B) := by rw [pow_succ]
        _ ≤ f (B ^ (k + 1)) * f B := hmul _ _
        _ ≤ f B ^ (k + 1) * f B := by gcongr
        _ = f B ^ (k + 1 + 1) := (pow_succ _ _).symm

/-- `f B < 1` forces `Bᵏ → 0` entrywise, hence `ρ(B) < 1` by
`Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one`. -/
private theorem complexSpectralRadius_lt_one_of_lt_one
    (hmul : ∀ B C : Matrix n n ℝ, f (B * C) ≤ f B * f C) {c : ℝ≥0}
    (hc : ∀ (B : Matrix n n ℝ) (i j : n), ‖B i j‖₊ ≤ c * f B)
    {B : Matrix n n ℝ} (hB : f B < 1) : complexSpectralRadius B < 1 := by
  rw [← tendsto_pow_iff_complexSpectralRadius_lt_one]
  have hg : Tendsto (fun k : ℕ => (c : ℝ) * (f B : ℝ) ^ k) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (f B : ℝ)) (f B).coe_nonneg
      (by exact_mod_cast hB)
    simpa using h.const_mul (c : ℝ)
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  simp only [Matrix.zero_apply]
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_ge_atTop 1] with k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h : ‖(B ^ (m + 1)) i j‖₊ ≤ c * f B ^ (m + 1) :=
    (hc _ i j).trans (by gcongr; exact apply_pow_le f hmul B m)
  exact_mod_cast h

/-- **The spectral radius of a real matrix is at most any submultiplicative matrix norm of it.**

`f` is assumed submultiplicative (`f (B * C) ≤ f B * f C`), absolutely homogeneous
(`f (r • B) = ‖r‖ * f B`) and positive definite (`f B = 0 → B = 0`). Subadditivity is never used,
but none of the other three can be dropped: for `n = Fin 2` the function `B ↦ |B.det| ^ (1/2)` is
submultiplicative, absolutely homogeneous and sends `1` to `1`, yet it vanishes on
`!![1, 0; 0, 0]`, whose spectral radius is `1`. Every scoped matrix norm satisfies all three, and
the corollaries `Matrix.complexSpectralRadius_le_linfty_opNNNorm`,
`Matrix.complexSpectralRadius_le_frobenius_nnnorm` and
`Matrix.complexSpectralRadius_le_l2_opNNNorm` record the specialisations.

Proof: for `f A < t` the entries of the powers of `t⁻¹ • A` are `O((f A / t) ^ k)` by
`Matrix.exists_nnnorm_apply_le`, so `ρ (t⁻¹ • A) < 1` by
`Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one`, and `Matrix.complexSpectralRadius_smul`
undoes the scaling. -/
theorem complexSpectralRadius_le_of_norm (A : Matrix n n ℝ)
    (hmul : ∀ B C : Matrix n n ℝ, f (B * C) ≤ f B * f C)
    (hsmul : ∀ (r : ℝ) (B : Matrix n n ℝ), f (r • B) = ‖r‖₊ * f B)
    (hzero : ∀ B : Matrix n n ℝ, f B = 0 → B = 0) :
    complexSpectralRadius A ≤ f A := by
  obtain ⟨c, hc⟩ := exists_nnnorm_apply_le f hmul hsmul hzero
  suffices h : ∀ t : ℝ≥0, f A < t → complexSpectralRadius A ≤ (t : ℝ≥0∞) by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    simpa using h (f A + ε) (lt_add_of_pos_right _ hε)
  intro t ht
  have ht0 : (0 : ℝ≥0) < t := zero_le.trans_lt ht
  have htR : (t : ℝ) ≠ 0 := by simpa using ht0.ne'
  have hlt : complexSpectralRadius ((t : ℝ)⁻¹ • A) < 1 := by
    refine complexSpectralRadius_lt_one_of_lt_one f hmul hc ?_
    rw [hsmul]
    have hinv : ‖(t : ℝ)⁻¹‖₊ = t⁻¹ := by rw [nnnorm_inv]; simp
    rw [hinv, inv_mul_eq_div, div_lt_one ht0]
    exact ht
  have hA : (t : ℝ) • ((t : ℝ)⁻¹ • A) = A := by
    rw [smul_smul, mul_inv_cancel₀ htR, one_smul]
  calc complexSpectralRadius A
      = complexSpectralRadius ((t : ℝ) • ((t : ℝ)⁻¹ • A)) := by rw [hA]
    _ = (t : ℝ≥0∞) * complexSpectralRadius ((t : ℝ)⁻¹ • A) := by
        rw [complexSpectralRadius_smul]; norm_num
    _ ≤ (t : ℝ≥0∞) * 1 := by gcongr
    _ = t := mul_one _

end NormBound

/-! ### Specialisations to the scoped matrix norms -/

section Operator

open scoped Matrix.Norms.Operator

/-- `ρ(A)` is at most the maximum absolute row sum (Mathlib: `Matrix.linfty_opNNNorm_def`). -/
theorem complexSpectralRadius_le_linfty_opNNNorm (A : Matrix n n ℝ) :
    complexSpectralRadius A ≤ ‖A‖₊ :=
  complexSpectralRadius_le_of_norm (‖·‖₊) A (fun _ _ => nnnorm_mul_le _ _)
    (fun _ _ => nnnorm_smul _ _) fun _ h => by simpa using h

/-- The spectral radius of a matrix over a finite index type is finite. -/
theorem complexSpectralRadius_ne_top (A : Matrix n n ℝ) : complexSpectralRadius A ≠ ⊤ :=
  ((complexSpectralRadius_le_linfty_opNNNorm A).trans_lt ENNReal.coe_lt_top).ne

end Operator

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- `ρ(A)` is at most the Frobenius (Hilbert–Schmidt) norm of `A`. -/
theorem complexSpectralRadius_le_frobenius_nnnorm (A : Matrix n n ℝ) :
    complexSpectralRadius A ≤ ‖A‖₊ :=
  complexSpectralRadius_le_of_norm (‖·‖₊) A (fun _ _ => nnnorm_mul_le _ _)
    (fun _ _ => nnnorm_smul _ _) fun _ h => by simpa using h

end Frobenius

section L2Operator

open scoped Matrix.Norms.L2Operator

/-- `ρ(A)` is at most the Euclidean operator norm of `A`. -/
theorem complexSpectralRadius_le_l2_opNNNorm (A : Matrix n n ℝ) :
    complexSpectralRadius A ≤ ‖A‖₊ :=
  complexSpectralRadius_le_of_norm (‖·‖₊) A (fun _ _ => nnnorm_mul_le _ _)
    (fun _ _ => nnnorm_smul _ _) fun _ h => by simpa using h

end L2Operator

end Matrix
