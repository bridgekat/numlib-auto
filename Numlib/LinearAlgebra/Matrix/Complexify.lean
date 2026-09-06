/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Topology.Instances.Matrix
import Numlib.Analysis.Normed.Algebra.SpectralRadius

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

/-- Determinants commute with complexification: `det (complexify A)` is `det A` read in `ℂ`. -/
@[simp] theorem det_complexify (A : Matrix n n ℝ) : (complexify A).det = ((A.det : ℝ) : ℂ) :=
  (RingHom.map_det Complex.ofRealHom A).symm

/-- A real matrix is invertible exactly when its complexification is, so invertibility may be
settled after passing to `ℂ`.  That is the route taken by
`Matrix.isUnit_one_sub_of_complexSpectralRadius_lt_one`, where only the complex Neumann series is
available. -/
theorem isUnit_complexify_iff (A : Matrix n n ℝ) : IsUnit (complexify A) ↔ IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, det_complexify]
  simp [isUnit_iff_ne_zero]

/-- `charpoly (complexify A) = charpoly A` mapped to `ℂ` (Mathlib: `Matrix.charpoly_map`). -/
theorem charpoly_complexify (A : Matrix n n ℝ) :
    (complexify A).charpoly = A.charpoly.map (algebraMap ℝ ℂ) := by
  have h : complexify A = A.map (algebraMap ℝ ℂ) := rfl
  rw [h, Matrix.charpoly_map]

/-- The complex spectrum of a real matrix is the root set of its characteristic polynomial pushed
forward to `ℂ`; no eigenvalue is lost, as one would be over `ℝ`.  This is the spectrum that
governs the decay of `Aᵏ`: the real characteristic polynomial of a rotation has no root at all,
yet its powers stay at norm one. -/
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

/-- The maximum-absolute-row-sum norm is unchanged by complexification: it is computed
entrywise, and complexification does not change the absolute value of an entry. -/
theorem linfty_opNorm_complexify (A : Matrix n n ℝ) : ‖complexify A‖ = ‖A‖ := by
  simp only [linfty_opNorm_def, complexify, Matrix.map_apply, Complex.nnnorm_real]

end Operator

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- `ρ(A)` is at most the Frobenius (Hilbert–Schmidt) norm of `A`. -/
theorem complexSpectralRadius_le_frobenius_nnnorm (A : Matrix n n ℝ) :
    complexSpectralRadius A ≤ ‖A‖₊ :=
  complexSpectralRadius_le_of_norm (‖·‖₊) A (fun _ _ => nnnorm_mul_le _ _)
    (fun _ _ => nnnorm_smul _ _) fun _ h => by simpa using h

/-- The Frobenius norm is unchanged by complexification, being computed entrywise. -/
theorem frobenius_norm_complexify (A : Matrix n n ℝ) : ‖complexify A‖ = ‖A‖ :=
  A.frobenius_norm_map_eq Complex.ofReal fun a => by simp

end Frobenius

section L2Operator

open scoped Matrix.Norms.L2Operator

/-- `ρ(A)` is at most the Euclidean operator norm of `A`. -/
theorem complexSpectralRadius_le_l2_opNNNorm (A : Matrix n n ℝ) :
    complexSpectralRadius A ≤ ‖A‖₊ :=
  complexSpectralRadius_le_of_norm (‖·‖₊) A (fun _ _ => nnnorm_mul_le _ _)
    (fun _ _ => nnnorm_smul _ _) fun _ h => by simpa using h

omit [DecidableEq n] in
/-- A complex vector has the Pythagorean decomposition into its real and imaginary parts. -/
private theorem norm_sq_toLp_complex (w : n → ℂ) :
    ‖(WithLp.toLp 2 w : EuclideanSpace ℂ n)‖ ^ 2
      = ‖(WithLp.toLp 2 (fun i => (w i).re) : EuclideanSpace ℝ n)‖ ^ 2
        + ‖(WithLp.toLp 2 (fun i => (w i).im) : EuclideanSpace ℝ n)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Real.norm_eq_abs, sq_abs, Complex.sq_norm, Complex.normSq_apply]
  ring

omit [DecidableEq n] in
/-- The real part of a complexified matrix–vector product is the product with the real part. -/
private theorem complexify_mulVec_re (A : Matrix n n ℝ) (w : n → ℂ) (i : n) :
    ((complexify A *ᵥ w) i).re = (A *ᵥ fun j => (w j).re) i := by
  simp [mulVec, dotProduct, Complex.re_sum]

omit [DecidableEq n] in
/-- The imaginary part of a complexified matrix–vector product is the product with the imaginary
part. -/
private theorem complexify_mulVec_im (A : Matrix n n ℝ) (w : n → ℂ) (i : n) :
    ((complexify A *ᵥ w) i).im = (A *ᵥ fun j => (w j).im) i := by
  simp [mulVec, dotProduct, Complex.im_sum]

omit [DecidableEq n] in
/-- Complexification does not change the Euclidean norm of a real vector. -/
private theorem norm_toLp_ofReal (x : n → ℝ) :
    ‖(WithLp.toLp 2 (fun i => (x i : ℂ)) : EuclideanSpace ℂ n)‖
      = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp

/-- **The Euclidean operator norm is unchanged by complexification**, `‖complexify A‖₂ = ‖A‖₂`.

`≥` because a real vector is a complex vector of the same norm; `≤` because a complex vector
splits as `x + i y` with `‖A (x + i y)‖² = ‖A x‖² + ‖A y‖² ≤ ‖A‖² (‖x‖² + ‖y‖²)`.  Together with
`Matrix.linfty_opNorm_complexify` and `Matrix.frobenius_norm_complexify`, both of which hold for
the trivial reason that those norms are computed entrywise, this transports every statement about
`‖A ^ k‖` to the complexification, where the Gelfand formula lives. -/
theorem l2_opNorm_complexify (A : Matrix n n ℝ) : ‖complexify A‖ = ‖A‖ := by
  refine le_antisymm ?_ ?_
  · rw [← l2_opNorm_toEuclideanCLM]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
    set w : n → ℂ := WithLp.ofLp z with hw
    have hz : z = WithLp.toLp 2 w := rfl
    have himg : ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A) z‖ ^ 2
        = ‖(WithLp.toLp 2 (A *ᵥ fun j => (w j).re) : EuclideanSpace ℝ n)‖ ^ 2
          + ‖(WithLp.toLp 2 (A *ᵥ fun j => (w j).im) : EuclideanSpace ℝ n)‖ ^ 2 := by
      rw [hz, toEuclideanCLM_toLp, norm_sq_toLp_complex]
      simp only [complexify_mulVec_re, complexify_mulVec_im]
    have hnorm : ‖z‖ ^ 2
        = ‖(WithLp.toLp 2 (fun j => (w j).re) : EuclideanSpace ℝ n)‖ ^ 2
          + ‖(WithLp.toLp 2 (fun j => (w j).im) : EuclideanSpace ℝ n)‖ ^ 2 := by
      rw [hz, norm_sq_toLp_complex]
    have hre : ‖(WithLp.toLp 2 (A *ᵥ fun j => (w j).re) : EuclideanSpace ℝ n)‖
        ≤ ‖A‖ * ‖(WithLp.toLp 2 (fun j => (w j).re) : EuclideanSpace ℝ n)‖ := by
      rw [← toEuclideanCLM_toLp, ← l2_opNorm_toEuclideanCLM (𝕜 := ℝ)]
      exact ContinuousLinearMap.le_opNorm _ _
    have him : ‖(WithLp.toLp 2 (A *ᵥ fun j => (w j).im) : EuclideanSpace ℝ n)‖
        ≤ ‖A‖ * ‖(WithLp.toLp 2 (fun j => (w j).im) : EuclideanSpace ℝ n)‖ := by
      rw [← toEuclideanCLM_toLp, ← l2_opNorm_toEuclideanCLM (𝕜 := ℝ)]
      exact ContinuousLinearMap.le_opNorm _ _
    have hre2 : ‖(WithLp.toLp 2 (A *ᵥ fun j => (w j).re) : EuclideanSpace ℝ n)‖ ^ 2
        ≤ (‖A‖ * ‖(WithLp.toLp 2 (fun j => (w j).re) : EuclideanSpace ℝ n)‖) ^ 2 := by
      rw [sq, sq]; exact mul_self_le_mul_self (norm_nonneg _) hre
    have him2 : ‖(WithLp.toLp 2 (A *ᵥ fun j => (w j).im) : EuclideanSpace ℝ n)‖ ^ 2
        ≤ (‖A‖ * ‖(WithLp.toLp 2 (fun j => (w j).im) : EuclideanSpace ℝ n)‖) ^ 2 := by
      rw [sq, sq]; exact mul_self_le_mul_self (norm_nonneg _) him
    have hsq : ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A) z‖ ^ 2 ≤ (‖A‖ * ‖z‖) ^ 2 := by
      rw [himg, mul_pow, hnorm, mul_add]
      rw [mul_pow] at hre2 him2
      linarith
    calc ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A) z‖
        = √(‖toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A) z‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ √((‖A‖ * ‖z‖) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = ‖A‖ * ‖z‖ := Real.sqrt_sq (by positivity)
  · rw [← l2_opNorm_toEuclideanCLM]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    set v : n → ℝ := WithLp.ofLp x with hv
    have hx : x = WithLp.toLp 2 v := rfl
    have hmul : (fun i => (((A *ᵥ v) i : ℝ) : ℂ)) = complexify A *ᵥ fun j => ((v j : ℝ) : ℂ) := by
      funext i
      simp [mulVec, dotProduct, complexify]
    calc ‖toEuclideanCLM (n := n) (𝕜 := ℝ) A x‖
        = ‖(WithLp.toLp 2 (fun i => (((A *ᵥ v) i : ℝ) : ℂ)) : EuclideanSpace ℂ n)‖ := by
          rw [norm_toLp_ofReal, hx, toEuclideanCLM_toLp]
      _ = ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A)
            (WithLp.toLp 2 fun j => ((v j : ℝ) : ℂ))‖ := by rw [hmul, toEuclideanCLM_toLp]
      _ ≤ ‖complexify A‖ * ‖(WithLp.toLp 2 fun j => ((v j : ℝ) : ℂ) : EuclideanSpace ℂ n)‖ := by
          rw [← l2_opNorm_toEuclideanCLM (𝕜 := ℂ)]
          exact ContinuousLinearMap.le_opNorm _ _
      _ = ‖complexify A‖ * ‖x‖ := by rw [norm_toLp_ofReal, hx]

/-- **Gelfand's formula for a real matrix**: `‖A ^ k‖ ^ (1 / k) → ρ(A)`, the spectral radius being
the complex one.  This is the general convergence factor of a linear stationary iteration: the
asymptotic rate at which the powers of the iteration matrix decay is its spectral radius, whatever
the norm.

Stated for the Euclidean operator norm; the same three lines prove it for the maximum-row-sum and
Frobenius norms, through `Matrix.linfty_opNorm_complexify` and `Matrix.frobenius_norm_complexify`
in place of `Matrix.l2_opNorm_complexify`.  In fact the limit does not depend on the norm at all,
since two norms on a finite-dimensional space differ by a factor `C` with `C ^ (1 / k) → 1`. -/
theorem tendsto_pow_rpow_complexSpectralRadius (A : Matrix n n ℝ) :
    Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / k : ℝ)) atTop
      (𝓝 (complexSpectralRadius A).toReal) := by
  have _ : CompleteSpace (Matrix n n ℂ) := FiniteDimensional.complete ℂ _
  have hnorm : ∀ k : ℕ, ‖(complexify A) ^ k‖ = ‖A ^ k‖ := fun k => by
    rw [← complexify_pow, l2_opNorm_complexify]
  have hgel := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (complexify A)
  simp only [hnorm] at hgel
  have h := (ENNReal.tendsto_toReal (complexSpectralRadius_ne_top A)).comp hgel
  refine h.congr fun k => ?_
  simp only [Function.comp_apply]
  exact ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)

/-- The Euclidean norm is submultiplicative against the Euclidean operator norm. -/
private theorem norm_toLp_mulVec_le (A : Matrix n n ℝ) (d : n → ℝ) :
    ‖(WithLp.toLp 2 (A *ᵥ d) : EuclideanSpace ℝ n)‖
      ≤ ‖A‖ * ‖(WithLp.toLp 2 d : EuclideanSpace ℝ n)‖ := by
  rw [← toEuclideanCLM_toLp, ← l2_opNorm_toEuclideanCLM (𝕜 := ℝ)]
  exact ContinuousLinearMap.le_opNorm _ _

/-- The specific convergence factor of an initial error is bounded termwise by the general one. -/
private theorem rpow_le_rpow_norm_pow (G : Matrix n n ℝ) (d₀ : n → ℝ) (k : ℕ) :
    (‖(WithLp.toLp 2 (G ^ k *ᵥ d₀) : EuclideanSpace ℝ n)‖
      / ‖(WithLp.toLp 2 d₀ : EuclideanSpace ℝ n)‖) ^ (1 / k : ℝ) ≤ ‖G ^ k‖ ^ (1 / k : ℝ) := by
  refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
  rcases eq_or_lt_of_le (norm_nonneg (WithLp.toLp 2 d₀ : EuclideanSpace ℝ n)) with h | h
  · have hd : (WithLp.toLp 2 d₀ : EuclideanSpace ℝ n) = 0 := by
      rwa [eq_comm, norm_eq_zero] at h
    have hd0 : d₀ = 0 := by
      have hc := congrArg (WithLp.ofLp (p := 2)) hd
      simpa using hc
    simp [hd0]
  · rw [div_le_iff₀ h]
    exact norm_toLp_mulVec_le _ _

/-- The *specific convergence factor* of an initial error `d₀` for the iteration matrix `G`:
`limsup (‖Gᵏ d₀‖ / ‖d₀‖) ^ (1 / k)`.  It is at most the spectral radius, for every `d₀`.

Together with `Matrix.exists_limsup_norm_pow_mulVec_rpow_eq`, which says that some `d₀` attains it,
this identifies the spectral radius as the worst asymptotic rate of a linear stationary iteration:
no starting error decays more slowly, and some starting error decays exactly that slowly. -/
theorem limsup_norm_pow_mulVec_rpow_le (G : Matrix n n ℝ) (d₀ : n → ℝ) :
    limsup (fun k : ℕ => (‖(WithLp.toLp 2 (G ^ k *ᵥ d₀) : EuclideanSpace ℝ n)‖
        / ‖(WithLp.toLp 2 d₀ : EuclideanSpace ℝ n)‖) ^ (1 / k : ℝ)) atTop
      ≤ (complexSpectralRadius G).toReal := by
  calc limsup (fun k : ℕ => (‖(WithLp.toLp 2 (G ^ k *ᵥ d₀) : EuclideanSpace ℝ n)‖
        / ‖(WithLp.toLp 2 d₀ : EuclideanSpace ℝ n)‖) ^ (1 / k : ℝ)) atTop
      ≤ limsup (fun k : ℕ => ‖G ^ k‖ ^ (1 / k : ℝ)) atTop :=
        Filter.limsup_le_limsup (Filter.Eventually.of_forall (rpow_le_rpow_norm_pow G d₀))
          (Filter.isCoboundedUnder_le_of_le atTop fun k => Real.rpow_nonneg (by positivity) _)
          (tendsto_pow_rpow_complexSpectralRadius G).isBoundedUnder_le
    _ = (complexSpectralRadius G).toReal :=
        (tendsto_pow_rpow_complexSpectralRadius G).limsup_eq

/-- The spectral radius of a real matrix is attained at a complex eigenvalue, together with an
eigenvector: the complex spectrum is compact and nonempty, so the modulus attains its maximum on
it, and a matrix eigenvalue always has an eigenvector. -/
private theorem exists_eigenvector_norm_eq [Nonempty n] (G : Matrix n n ℝ) :
    ∃ (μ : ℂ) (v : n → ℂ), v ≠ 0 ∧ complexify G *ᵥ v = μ • v ∧
      ‖μ‖ = (complexSpectralRadius G).toReal := by
  have _ : CompleteSpace (Matrix n n ℂ) := FiniteDimensional.complete ℂ _
  obtain ⟨μ, hμ, hmax⟩ := (spectrum.isCompact (complexify G)).exists_isMaxOn
    (spectrum.nonempty (complexify G)) continuous_norm.continuousOn
  have hsr : complexSpectralRadius G = (‖μ‖₊ : ℝ≥0∞) := by
    refine le_antisymm (iSup₂_le fun ν hν => ?_) (le_iSup₂ (α := ENNReal) μ hμ)
    exact_mod_cast hmax hν
  have hdet : (algebraMap ℂ (Matrix n n ℂ) μ - complexify G).det = 0 := by
    have h := spectrum.mem_iff.mp hμ
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at h
    exact not_not.mp h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨μ, v, hv0, ?_, ?_⟩
  · rw [sub_mulVec] at hv
    have halg : algebraMap ℂ (Matrix n n ℂ) μ *ᵥ v = μ • v := by
      rw [Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec]
    rw [halg] at hv
    exact (sub_eq_zero.mp hv).symm
  · rw [hsr]
    simp

/-- **The general convergence factor is attained.** Some nonzero real vector has its images under
the powers of `G` frequently as large as `c ρ ^ k`, with a fixed `c > 0`: take the real or the
imaginary part of an eigenvector for an eigenvalue of maximal modulus.

Which of the two parts works can depend on `k`, but not both can fail infinitely often, so one
choice serves for infinitely many `k`, and a `limsup` is all the conclusion asks for. -/
private theorem exists_frequently_norm_pow_mulVec_ge [Nonempty n] (G : Matrix n n ℝ) :
    ∃ d₀ : n → ℝ, d₀ ≠ 0 ∧ ∃ c > 0, ∃ᶠ k : ℕ in atTop,
      c * (complexSpectralRadius G).toReal ^ k
        ≤ ‖(WithLp.toLp 2 (G ^ k *ᵥ d₀) : EuclideanSpace ℝ n)‖ := by
  obtain ⟨μ, v, hv0, heig, hμ⟩ := exists_eigenvector_norm_eq G
  set ρ := (complexSpectralRadius G).toReal with hρdef
  have hρ0 : 0 ≤ ρ := hμ ▸ norm_nonneg μ
  set x : n → ℝ := fun j => (v j).re with hxdef
  set y : n → ℝ := fun j => (v j).im with hydef
  set P : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ with hPdef
  have hvne : (WithLp.toLp 2 v : EuclideanSpace ℂ n) ≠ 0 := fun h =>
    hv0 (by simpa using congrArg (WithLp.ofLp (p := 2)) h)
  have hP : 0 < P := norm_pos_iff.mpr hvne
  have hsplit : P ^ 2 = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ ^ 2
      + ‖(WithLp.toLp 2 y : EuclideanSpace ℝ n)‖ ^ 2 := norm_sq_toLp_complex v
  have hpow : ∀ k : ℕ, complexify (G ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    rw [complexify_pow]
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ, ← mulVec_mulVec, heig, mulVec_smul, ih, smul_smul, mul_comm]
  have hpy : ∀ k : ℕ, ‖(WithLp.toLp 2 (G ^ k *ᵥ x) : EuclideanSpace ℝ n)‖ ^ 2
      + ‖(WithLp.toLp 2 (G ^ k *ᵥ y) : EuclideanSpace ℝ n)‖ ^ 2 = (ρ ^ k * P) ^ 2 := by
    intro k
    have h := norm_sq_toLp_complex (complexify (G ^ k) *ᵥ v)
    simp only [complexify_mulVec_re, complexify_mulVec_im] at h
    rw [← h, hpow k]
    have hsm : (WithLp.toLp 2 (μ ^ k • v) : EuclideanSpace ℂ n)
        = μ ^ k • (WithLp.toLp 2 v : EuclideanSpace ℂ n) := rfl
    rw [hsm, norm_smul, norm_pow, hμ]
  have hmaxk : ∀ k : ℕ, ρ ^ k * P / 2
      ≤ max ‖(WithLp.toLp 2 (G ^ k *ᵥ x) : EuclideanSpace ℝ n)‖
          ‖(WithLp.toLp 2 (G ^ k *ᵥ y) : EuclideanSpace ℝ n)‖ := by
    intro k
    have ha : (0 : ℝ) ≤ ‖(WithLp.toLp 2 (G ^ k *ᵥ x) : EuclideanSpace ℝ n)‖ := norm_nonneg _
    have hb : (0 : ℝ) ≤ ‖(WithLp.toLp 2 (G ^ k *ᵥ y) : EuclideanSpace ℝ n)‖ := norm_nonneg _
    have hpk : (0 : ℝ) ≤ ρ ^ k * P := mul_nonneg (pow_nonneg hρ0 k) hP.le
    have h := hpy k
    rcases le_total ‖(WithLp.toLp 2 (G ^ k *ᵥ x) : EuclideanSpace ℝ n)‖
        ‖(WithLp.toLp 2 (G ^ k *ᵥ y) : EuclideanSpace ℝ n)‖ with h' | h'
    · rw [max_eq_right h']; nlinarith
    · rw [max_eq_left h']; nlinarith
  -- the degenerate case `ρ = 0`: any nonzero real or imaginary part will do
  rcases eq_or_lt_of_le hρ0 with hρ | hρ
  · have hchoice : ∃ d₀ : n → ℝ, d₀ ≠ 0 := by
      rcases eq_or_ne x 0 with hx0 | hx0
      · refine ⟨y, fun hy0 => ?_⟩
        have h1 : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ = 0 := by rw [hx0]; simp
        have h2 : ‖(WithLp.toLp 2 y : EuclideanSpace ℝ n)‖ = 0 := by rw [hy0]; simp
        rw [h1, h2] at hsplit
        nlinarith
      · exact ⟨x, hx0⟩
    obtain ⟨d₀, hd₀⟩ := hchoice
    refine ⟨d₀, hd₀, 1, one_pos, Filter.Eventually.frequently ?_⟩
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [← hρ, zero_pow (by omega), mul_zero]
    exact norm_nonneg _
  -- the generic case: one of the two parts is frequently large, and is then nonzero
  · have hne : ∀ d : n → ℝ, (∃ᶠ k : ℕ in atTop,
        ρ ^ k * P / 2 ≤ ‖(WithLp.toLp 2 (G ^ k *ᵥ d) : EuclideanSpace ℝ n)‖) → d ≠ 0 := by
      rintro d hd rfl
      obtain ⟨k, hk⟩ := hd.exists
      have hz : ‖(WithLp.toLp 2 (G ^ k *ᵥ (0 : n → ℝ)) : EuclideanSpace ℝ n)‖ = 0 := by simp
      rw [hz] at hk
      nlinarith [pow_pos hρ k, hP]
    by_cases hfx : ∃ᶠ k : ℕ in atTop,
        ρ ^ k * P / 2 ≤ ‖(WithLp.toLp 2 (G ^ k *ᵥ x) : EuclideanSpace ℝ n)‖
    · exact ⟨x, hne x hfx, P / 2, by linarith, hfx.mono fun k hk => by linarith [hk]⟩
    · rw [Filter.not_frequently] at hfx
      have hfy : ∃ᶠ k : ℕ in atTop,
          ρ ^ k * P / 2 ≤ ‖(WithLp.toLp 2 (G ^ k *ᵥ y) : EuclideanSpace ℝ n)‖ := by
        refine Filter.Eventually.frequently ?_
        filter_upwards [hfx] with k hk
        rcases max_cases ‖(WithLp.toLp 2 (G ^ k *ᵥ x) : EuclideanSpace ℝ n)‖
            ‖(WithLp.toLp 2 (G ^ k *ᵥ y) : EuclideanSpace ℝ n)‖ with ⟨he, -⟩ | ⟨he, -⟩
        · exact absurd (he ▸ hmaxk k) hk
        · exact he ▸ hmaxk k
      exact ⟨y, hne y hfy, P / 2, by linarith, hfy.mono fun k hk => by linarith [hk]⟩

/-- **The general convergence factor of a real iteration matrix is its spectral radius, and it is
attained**: there is a nonzero initial error `d₀` whose specific convergence factor
`limsup (‖Gᵏ d₀‖ / ‖d₀‖) ^ (1 / k)` equals `ρ(G)`.

With `Matrix.limsup_norm_pow_mulVec_rpow_le`, which bounds every specific factor by `ρ(G)`, this
says that the spectral radius is the exact asymptotic rate of the slowest-decaying error of a
linear stationary iteration.  The witness is the real or the imaginary part of an eigenvector for
an eigenvalue of maximal modulus; a rotation shows that neither part need work for every `k`,
which is why the statement is about a `limsup` and not about a limit. -/
theorem exists_limsup_norm_pow_mulVec_rpow_eq [Nonempty n] (G : Matrix n n ℝ) :
    ∃ d₀ : n → ℝ, d₀ ≠ 0 ∧
      limsup (fun k : ℕ => (‖(WithLp.toLp 2 (G ^ k *ᵥ d₀) : EuclideanSpace ℝ n)‖
          / ‖(WithLp.toLp 2 d₀ : EuclideanSpace ℝ n)‖) ^ (1 / k : ℝ)) atTop
        = (complexSpectralRadius G).toReal := by
  obtain ⟨d₀, hd₀, c, hc, hfreq⟩ := exists_frequently_norm_pow_mulVec_ge G
  refine ⟨d₀, hd₀, le_antisymm (limsup_norm_pow_mulVec_rpow_le G d₀) ?_⟩
  set ρ := (complexSpectralRadius G).toReal with hρdef
  have hρ0 : 0 ≤ ρ := ENNReal.toReal_nonneg
  set D : ℝ := ‖(WithLp.toLp 2 d₀ : EuclideanSpace ℝ n)‖ with hDdef
  have hD : 0 < D := norm_pos_iff.mpr fun h =>
    hd₀ (by simpa using congrArg (WithLp.ofLp (p := 2)) h)
  set a : ℕ → ℝ := fun k => (‖(WithLp.toLp 2 (G ^ k *ᵥ d₀) : EuclideanSpace ℝ n)‖ / D)
    ^ (1 / k : ℝ) with hadef
  have habdd : Filter.IsBoundedUnder (· ≤ ·) atTop a := by
    obtain ⟨B, hB⟩ := (tendsto_pow_rpow_complexSpectralRadius G).isBoundedUnder_le
    rw [Filter.eventually_map] at hB
    refine ⟨B, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [hB] with k hk using (rpow_le_rpow_norm_pow G d₀ k).trans hk
  have hfa : ∃ᶠ k : ℕ in atTop, (c / D) ^ (1 / k : ℝ) * ρ ≤ a k := by
    refine (hfreq.and_eventually (eventually_ge_atTop 1)).mono ?_
    rintro k ⟨hk, hk1⟩
    have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hstep : c / D * ρ ^ k ≤ ‖(WithLp.toLp 2 (G ^ k *ᵥ d₀) : EuclideanSpace ℝ n)‖ / D := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hD]
      exact hk
    calc (c / D) ^ (1 / k : ℝ) * ρ
        = (c / D * ρ ^ k) ^ (1 / k : ℝ) := by
          rw [Real.mul_rpow (by positivity) (pow_nonneg hρ0 k), one_div,
            Real.pow_rpow_inv_natCast hρ0 (by omega)]
      _ ≤ a k := Real.rpow_le_rpow (by positivity) hstep (by positivity)
  have hlim : Tendsto (fun k : ℕ => (c / D) ^ (1 / k : ℝ) * ρ) atTop (𝓝 ρ) := by
    have h1 : Tendsto (fun k : ℕ => (1 : ℝ) / (k : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h2 : ContinuousAt (fun t : ℝ => (c / D) ^ t) 0 :=
      Real.continuousAt_const_rpow (by positivity)
    have h3 : Tendsto (fun k : ℕ => (c / D) ^ (1 / k : ℝ)) atTop (𝓝 1) := by
      simpa [Function.comp_def] using h2.tendsto.comp h1
    simpa using h3.mul_const ρ
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h2 : ∀ᶠ k : ℕ in atTop, ρ - ε < (c / D) ^ (1 / k : ℝ) * ρ :=
    hlim.eventually_const_lt (by linarith)
  have h3 : ∃ᶠ k : ℕ in atTop, ρ - ε ≤ a k :=
    (hfa.and_eventually h2).mono fun k hk => le_trans hk.2.le hk.1
  have h4 := Filter.le_limsup_of_frequently_le h3 habdd
  linarith

end L2Operator

/-- **A real iteration matrix of algebra norm less than one has powers tending to `0`**, for any
consistent (submultiplicative) matrix norm at all, not only the scoped ones.

The norm is bundled as an `AlgebraNorm ℝ (Matrix n n ℝ)`, so that its hypotheses are attached to
the canonical ring and module structures of `Matrix n n ℝ`.  Stating it instead with a class
argument `[NormedRing (Matrix n n ℝ)]` would make it false, for the reason explained above
`Matrix.exists_nnnorm_apply_le`. -/
theorem tendsto_pow_of_algebraNorm_lt_one (N : AlgebraNorm ℝ (Matrix n n ℝ)) {A : Matrix n n ℝ}
    (h : N A < 1) : Tendsto (fun k => A ^ k) atTop (𝓝 0) := by
  have hmono : ∀ B, (0 : ℝ) ≤ N B := fun B => apply_nonneg N B
  refine (tendsto_pow_iff_complexSpectralRadius_lt_one A).mpr ?_
  refine lt_of_le_of_lt (complexSpectralRadius_le_of_norm (fun B => (N B).toNNReal) A ?_ ?_ ?_) ?_
  · intro B C
    rw [← Real.toNNReal_mul (hmono B)]
    exact Real.toNNReal_mono (map_mul_le_mul N B C)
  · intro r B
    rw [map_smul_eq_mul N, Real.toNNReal_mul (norm_nonneg r)]
    congr 1
    ext
    simp
  · intro B hB
    refine eq_zero_of_map_eq_zero N (le_antisymm ?_ (hmono B))
    simpa [Real.toNNReal_eq_zero] using hB
  · rw [ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_coe]
    simpa [Real.coe_toNNReal _ (hmono A)] using h

end Matrix
