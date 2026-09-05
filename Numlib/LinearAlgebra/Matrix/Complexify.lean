/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Normed.Algebra.SpectralRadius
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
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
-/

open Filter Topology

namespace Matrix

variable {n : Type*}

/-- The complexification of a real matrix. -/
def complexify (A : Matrix n n ℝ) : Matrix n n ℂ := A.map Complex.ofReal

@[simp] theorem complexify_apply (A : Matrix n n ℝ) (i j : n) : complexify A i j = A i j := rfl

@[simp] theorem complexify_zero : complexify (0 : Matrix n n ℝ) = 0 := by
  ext i j; simp

theorem complexify_add (A B : Matrix n n ℝ) : complexify (A + B) = complexify A + complexify B := by
  ext i j; simp

theorem complexify_smul (c : ℝ) (A : Matrix n n ℝ) :
    complexify (c • A) = (c : ℂ) • complexify A := by
  ext i j; simp

theorem complexify_injective : Function.Injective (complexify (n := n)) := by
  intro A B hAB
  ext i j
  have h : ((A i j : ℝ) : ℂ) = ((B i j : ℝ) : ℂ) := congrFun (congrFun hAB i) j
  exact_mod_cast h

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

theorem isUnit_complexify_iff (A : Matrix n n ℝ) : IsUnit (complexify A) ↔ IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det,
    show (complexify A).det = ((A.det : ℝ) : ℂ) from (RingHom.map_det Complex.ofRealHom A).symm]
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

/-- `ρ(A) ≤ ‖A‖` for any submultiplicative matrix norm (Saad Cor 4.2): open a norm scope such as
`Matrix.Norms.LinftyOp`, `Matrix.Norms.L2Operator` or `Matrix.Norms.Frobenius` to supply the
instances. Submultiplicativity is the operative hypothesis; a *multiplicative* norm
(`NormMulClass`) does not exist on `Matrix n n ℝ` for `1 < card n`. Proof: `ρ` is unchanged by
powers (`complexSpectralRadius_pow`), and norm equivalence in finite dimension gives
`ρ (complexify B) ≤ C ‖B‖`; apply it to `A ^ k` and let `k → ∞`. -/
-- Statement corrected: `[NormedRing (Matrix n n ℝ)] [NormOneClass (Matrix n n ℝ)]` alone make the
-- statement **false**.  Those two classes only say that `‖·‖` is a submultiplicative group norm
-- with `‖1‖ = 1`; they do not force it to be `ℝ`-homogeneous.  For `n = Fin 1` transport the norm
-- `‖M‖ = |M 0 0| ^ (1/2)` of `ℝ` along `Matrix (Fin 1) (Fin 1) ℝ ≃+* ℝ`: it is subadditive
-- (`√` is), multiplicative, and has `‖1‖ = 1`, yet for `A = !![4]` we get `ρ(A) = 4 > 2 = ‖A‖`.
-- Adding `[NormedAlgebra ℝ (Matrix n n ℝ)]` (satisfied by every scoped matrix-norm instance:
-- `Matrix.Norms.Operator`, `Matrix.Norms.L2Operator`, `Matrix.Norms.Frobenius`) restores
-- homogeneity and makes the statement true.
theorem complexSpectralRadius_le_of_norm {A : Matrix n n ℝ} [NormedRing (Matrix n n ℝ)]
    [NormOneClass (Matrix n n ℝ)] [NormedAlgebra ℝ (Matrix n n ℝ)] :
    complexSpectralRadius A ≤ ‖A‖₊ := by
  -- Left open.  The intended argument is: `Matrix.toEuclideanCLM ∘ Matrix.complexify` is an
  -- `ℝ`-linear map out of a finite-dimensional normed space, hence bounded by some `C`, so
  -- `spectrum.spectralRadius_le_pow_nnnorm_pow_one_div` applied to `A ^ (k+1)` gives
  -- `ρ ≤ (C * ‖A‖ ^ (k+1)) ^ (1/(k+1)) * c ^ (1/(k+1))`, and `k → ∞` finishes.
  -- Two obstructions were hit: (i) `FiniteDimensional ℝ (Matrix n n ℝ)` is stated for the
  -- canonical `Module ℝ (Matrix n n ℝ)`, while the hypotheses above carry their own `Ring`,
  -- `AddCommGroup` and `Algebra` structures, so the two need not be the same instance and the
  -- norm-equivalence lemmas do not apply verbatim; (ii) the closing `ENNReal.rpow` limit
  -- (`(C ^ (1/(k+1)) : ℝ≥0∞) → 1`) is a substantial computation on its own.
  sorry

end Matrix
