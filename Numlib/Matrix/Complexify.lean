/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic

/-!
# Complexification of real matrices

`Matrix.complexify A = A.map Complex.ofReal`, its characteristic polynomial and spectrum, and the
spectral radius of a real matrix *defined as* the spectral radius of its complexification
(`Matrix.complexSpectralRadius`). This is the only meaningful notion for real matrices:
`spectralRadius ℝ` of the rotation `![![0, -1], ![1, 0]]` is `0` (empty real spectrum) although
its powers do not tend to `0`, so `spectralRadius ℝ G < 1 → Gᵏ → 0` is **false** over `ℝ`; all
Gelfand-formula results (`Numlib/Analysis/SpectralRadius.lean`) are used over `ℂ` and
transported through `complexify`.
-/

open Filter Topology

namespace Matrix

variable {n : Type*}

/-- The complexification of a real matrix. -/
def complexify (A : Matrix n n ℝ) : Matrix n n ℂ := A.map Complex.ofReal

@[simp] theorem complexify_apply (A : Matrix n n ℝ) (i j : n) : complexify A i j = A i j := rfl

@[simp] theorem complexify_zero : complexify (0 : Matrix n n ℝ) = 0 := by
  sorry

theorem complexify_add (A B : Matrix n n ℝ) : complexify (A + B) = complexify A + complexify B := by
  sorry

theorem complexify_smul (c : ℝ) (A : Matrix n n ℝ) :
    complexify (c • A) = (c : ℂ) • complexify A := by
  sorry

theorem complexify_injective : Function.Injective (complexify (n := n)) := by
  sorry

theorem complexify_mul [Fintype n] (A B : Matrix n n ℝ) :
    complexify (A * B) = complexify A * complexify B := by
  sorry

variable [DecidableEq n]

@[simp] theorem complexify_one : complexify (1 : Matrix n n ℝ) = 1 := by
  sorry

variable [Fintype n]

theorem complexify_pow (A : Matrix n n ℝ) (k : ℕ) : complexify (A ^ k) = complexify A ^ k := by
  sorry

theorem isUnit_complexify_iff (A : Matrix n n ℝ) : IsUnit (complexify A) ↔ IsUnit A := by
  sorry

/-- `charpoly (complexify A) = charpoly A` mapped to `ℂ` (Mathlib: `Matrix.charpoly_map`). -/
theorem charpoly_complexify (A : Matrix n n ℝ) :
    (complexify A).charpoly = A.charpoly.map (algebraMap ℝ ℂ) := by
  sorry

theorem mem_spectrum_complexify_iff (A : Matrix n n ℝ) (μ : ℂ) :
    μ ∈ spectrum ℂ (complexify A) ↔ (A.charpoly.map (algebraMap ℝ ℂ)).IsRoot μ := by
  sorry

/-- Real eigenvalues of `A` are exactly the real points of the complex spectrum. -/
theorem ofReal_mem_spectrum_complexify_iff (A : Matrix n n ℝ) (μ : ℝ) :
    (μ : ℂ) ∈ spectrum ℂ (complexify A) ↔ μ ∈ spectrum ℝ A := by
  sorry

/-- The spectral radius of a real matrix, computed over `ℂ`. -/
noncomputable def complexSpectralRadius (A : Matrix n n ℝ) : ENNReal :=
  spectralRadius ℂ (complexify A)

theorem spectralRadius_le_complexSpectralRadius (A : Matrix n n ℝ) :
    spectralRadius ℝ A ≤ complexSpectralRadius A := by
  sorry

/-- `Aᵏ → 0` iff `ρ(A) < 1`, for real matrices (via the complexification and the Gelfand
formula). -/
theorem tendsto_pow_iff_complexSpectralRadius_lt_one (A : Matrix n n ℝ) :
    Tendsto (fun k => A ^ k) atTop (𝓝 0) ↔ complexSpectralRadius A < 1 := by
  sorry

/-- `ρ(A) ≤ ‖A‖` for any submultiplicative matrix norm (Saad Cor 4.2): open a norm scope such as
`Matrix.Norms.LinftyOp`, `Matrix.Norms.L2Operator` or `Matrix.Norms.Frobenius` to supply the
instances. Submultiplicativity is the operative hypothesis; a *multiplicative* norm
(`NormMulClass`) does not exist on `Matrix n n ℝ` for `1 < card n`. Proof: `ρ` is unchanged by
powers (`complexSpectralRadius_pow`), and norm equivalence in finite dimension gives
`ρ (complexify B) ≤ C ‖B‖`; apply it to `A ^ k` and let `k → ∞`. -/
theorem complexSpectralRadius_le_of_norm {A : Matrix n n ℝ} [NormedRing (Matrix n n ℝ)]
    [NormOneClass (Matrix n n ℝ)] :
    complexSpectralRadius A ≤ ‖A‖₊ := by
  sorry

end Matrix
