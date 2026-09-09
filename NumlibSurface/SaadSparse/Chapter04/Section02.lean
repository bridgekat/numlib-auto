import Mathlib.Analysis.Normed.Unbundled.AlgebraNorm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Numlib.Eigen.Perturbation
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.MMatrix
import Numlib.LinearAlgebra.Sparse.Pattern
import Numlib.LinearSolve.Stationary.ConsistentlyOrdered
import Numlib.LinearSolve.Stationary.DiagDominant
import Numlib.LinearSolve.Stationary.RegularSplitting
import Numlib.LinearSolve.Stationary.SPD
import Numlib.LinearSolve.Stationary.Splitting
import NumlibSurface.SaadSparse.Chapter01.Section13
import NumlibSurface.SaadSparse.Chapter04.Section01

/-!
# Saad §4.2: convergence of the basic iterative methods

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §4.2, in three parts.

**§4.2–4.2.2, the affine iteration** `x_{k+1} = G x_k + f` (4.28)–(4.30): Theorem 4.1 (`ρ(G) < 1`
characterizes convergence), Corollary 4.2 (`‖G‖ < 1` suffices), the remark `|λ| ≤ ‖A‖` before
Theorem 4.6, and Example 4.1 (Richardson). The proofs specialize the backbone's spectral-radius
theory (`Numlib/LinearAlgebra/Matrix/Complexify.lean`,
`Numlib/Analysis/Normed/Algebra/SpectralRadius.lean`, `Numlib/LinearSolve/Stationary/Basic.lean`) to
real matrices acting on `Fin n → ℝ`.

**§4.2.3, diagonally dominant matrices**: Definition 4.5, Gershgorin's theorem (Theorem 4.6) in its
row and column forms, the nonsingularity of strictly diagonally dominant matrices (Corollary 4.8),
and the convergence of the Jacobi and Gauss–Seidel iterations for such matrices (Theorem 4.9).
Saad's Definition 4.5 as printed uses column sums for all three dominance conditions, while the
proofs of Theorems 4.6 and 4.9 use row sums; both forms are stated here, following the backbone's
`Matrix.IsStrictDiagDominant` (rows) and `Matrix.IsStrictColDiagDominant` (columns). The three
conditions the definition names are `definition_4_5`, `definition_4_5_strict` and
`definition_4_5_irreducible`, written in the book's column form, and `definition_4_5_iff` reads them
back as the backbone's predicates at `Aᵀ`.

The third condition of Definition 4.5, *irreducible* diagonal dominance, carries a clause that is
easy to drop and that both Corollary 4.8 and Theorem 4.9 need: weak dominance at every index **and
strict dominance at at least one**. The backbone's `Matrix.IsIrreduciblyDiagDominant` keeps it as
the field `exists_strict` (in the row form, as above). Without it both results are false:
`!![1, -1; -1, 1]` is irreducible and weakly diagonally dominant yet singular, and its Jacobi
iteration matrix `!![0, 1; 1, 0]` has spectral radius `1`.

**§4.2.4–4.2.5, symmetric positive definite matrices and Young's theory**: Proposition 4.12, by the
similarity argument the book uses — for a block anti-diagonal `B` the spectrum is symmetric under
negation, and the spectrum of `B(α) = α L + α⁻¹ U` does not depend on `α ≠ 0`; Theorem 4.10 (SOR
converges exactly for positive definite `A`), Definitions 4.11 and 4.13 (Property A, consistent
orderings, T-matrices), Propositions 4.14–4.15, Theorem 4.16 and the optimal relaxation parameter
(4.47).

Saad's Definition 4.13 is a *labelling* of the indices, and it is the labelling that the surface
takes as `SaadSparse.Chapter04.IsConsistentlyOrdered`; the backbone's `Matrix.IsConsistentlyOrdered`
is Kress's spectral property, which Young's theory actually uses, and
`SaadSparse.Chapter04.IsConsistentlyOrdered.matrix_isConsistentlyOrdered` is the implication between
them — Saad's Proposition 4.15.

Left out of the plan: the *specific* convergence factor of §4.2.1 for a generic `d₀`, which the book
derives heuristically from the Jordan form.
-/

open Matrix

namespace SaadSparse.Chapter04

/-! ### §4.2–4.2.2 The affine iteration and its convergence -/

section AffineIteration

open Filter Topology Stationary

open scoped SaadSparse ENNReal

variable {n : ℕ} {A G : Matrix (Fin n) (Fin n) ℝ}

/-! ### Elementary limits of matrices and matrix–vector products -/

/-- Entrywise convergence of matrices to `0` is convergence in the product topology. -/
theorem tendsto_zero_of_entries {M : ℕ → Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ i j, Tendsto (fun k => M k i j) atTop (𝓝 0)) : Tendsto M atTop (𝓝 0) := by
  have key : Tendsto (fun k => (fun i j => M k i j : Fin n → Fin n → ℝ)) atTop
      (𝓝 (fun _ _ => (0 : ℝ))) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => h i j
  exact key

/-- If `M k → 0` then `M k v → 0` for every fixed `v`. -/
theorem tendsto_mulVec_zero {M : ℕ → Matrix (Fin n) (Fin n) ℝ} (h : Tendsto M atTop (𝓝 0))
    (v : Fin n → ℝ) : Tendsto (fun k => M k *ᵥ v) atTop (𝓝 0) := by
  have hc : Continuous fun B : Matrix (Fin n) (Fin n) ℝ => B *ᵥ v :=
    Continuous.matrix_mulVec continuous_id continuous_const
  have h1 := (hc.tendsto 0).comp h
  simpa [Function.comp_def] using h1

/-- Conversely, if `M k v → 0` for every `v` then `M k → 0`. -/
theorem tendsto_zero_of_forall_mulVec {M : ℕ → Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ v, Tendsto (fun k => M k *ᵥ v) atTop (𝓝 0)) : Tendsto M atTop (𝓝 0) := by
  refine tendsto_zero_of_entries fun i j => ?_
  have hsingle : ∀ k, (M k *ᵥ Pi.single j 1) i = M k i j := fun k => by
    simp [mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq']
  simpa only [hsingle, Pi.zero_apply] using tendsto_pi_nhds.mp (h (Pi.single j 1)) i

/-! ### The affine iteration (4.28)–(4.30) -/

/-- The affine step is continuous. -/
theorem continuous_affineStep (G : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → ℝ) :
    Continuous (affineStep G f) :=
  (Continuous.matrix_mulVec continuous_const continuous_id).add continuous_const

/-- Saad (4.29): `x` is a fixed point of `x ↦ G x + f` iff `(I - G) x = f`. -/
theorem affineStep_fixed_iff (G : Matrix (Fin n) (Fin n) ℝ) (f x : Fin n → ℝ) :
    affineStep G f x = x ↔ (1 - G) *ᵥ x = f := by
  rw [affineStep, sub_mulVec, one_mulVec, sub_eq_iff_eq_add', eq_comm]

/-- Saad (4.29): the limit of a convergent affine iteration is a fixed point. -/
theorem tendsto_affineStep_fixed {G : Matrix (Fin n) (Fin n) ℝ} {f x₀ x : Fin n → ℝ}
    (h : Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 x)) : affineStep G f x = x := by
  have h1 : Tendsto (fun k => (affineStep G f)^[k + 1] x₀) atTop (𝓝 x) := by
    simpa [Function.comp_def] using h.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun k => (affineStep G f)^[k + 1] x₀) atTop (𝓝 (affineStep G f x)) := by
    simpa only [Function.iterate_succ_apply', Function.comp_def] using
      ((continuous_affineStep G f).tendsto x).comp h
  exact tendsto_nhds_unique h2 h1

/-- Saad (4.29): the limit of a convergent splitting iteration solves `A x = b`. -/
theorem tendsto_step_solves (s : Splitting A) {b x₀ x : Fin n → ℝ}
    (h : Tendsto (fun k => (Splitting.step s b)^[k] x₀) atTop (𝓝 x)) : A *ᵥ x = b :=
  (step_fixed_iff s b x).mp (tendsto_affineStep_fixed h)

/-- Saad (4.30): the error recursion `x_k - x* = G^k (x₀ - x*)`. -/
theorem affineStep_iterate_sub {G : Matrix (Fin n) (Fin n) ℝ} {f x' : Fin n → ℝ}
    (hfix : affineStep G f x' = x') (x₀ : Fin n → ℝ) (k : ℕ) :
    (affineStep G f)^[k] x₀ - x' = (G ^ k) *ᵥ (x₀ - x') := by
  have hfix' : G *ᵥ x' + f = x' := hfix
  have hf : f = x' - G *ᵥ x' := eq_sub_of_add_eq' hfix'
  have key : ∀ a : Fin n → ℝ, affineStep G f a - x' = G *ᵥ (a - x') := by
    intro a
    rw [affineStep, mulVec_sub, hf]
    abel
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', key, ih, pow_succ', ← mulVec_mulVec]

/-- Saad (4.30): the increment recursion `x_{k+1} - x_k = G^k (f - (I - G) x₀)`. -/
theorem affineStep_iterate_succ_sub (G : Matrix (Fin n) (Fin n) ℝ) (f x₀ : Fin n → ℝ) (k : ℕ) :
    (affineStep G f)^[k + 1] x₀ - (affineStep G f)^[k] x₀ = (G ^ k) *ᵥ (f - (1 - G) *ᵥ x₀) := by
  have key : ∀ a c : Fin n → ℝ, affineStep G f a - affineStep G f c = G *ᵥ (a - c) := by
    intro a c
    rw [affineStep, affineStep, add_sub_add_right_eq_sub, ← mulVec_sub]
  induction k with
  | zero =>
    change affineStep G f x₀ - x₀ = (G ^ 0) *ᵥ (f - (1 - G) *ᵥ x₀)
    rw [affineStep, pow_zero, one_mulVec, sub_mulVec, one_mulVec]
    abel
  | succ k ih =>
    have h1 : (affineStep G f)^[k + 1 + 1] x₀ = affineStep G f ((affineStep G f)^[k + 1] x₀) :=
      Function.iterate_succ_apply' _ _ _
    have h2 : (affineStep G f)^[k + 1] x₀ = affineStep G f ((affineStep G f)^[k] x₀) :=
      Function.iterate_succ_apply' _ _ _
    rw [h1]
    nth_rewrite 2 [h2]
    rw [key, ih, mulVec_mulVec, ← pow_succ']

/-! ### Theorem 4.1 -/

/-- `ρ(G) < 1` makes `I - G` nonsingular (Saad, Thm 4.1, first half; Thm 1.11). -/
theorem isUnit_one_sub_of_complexSpectralRadius_lt_one (hG : complexSpectralRadius G < 1) :
    IsUnit (1 - G) := by
  have h1 : (1 : ℂ) ∉ spectrum ℂ (complexify G) := by
    intro hmem
    have hle : (1 : ENNReal) ≤ complexSpectralRadius G := by
      have h2 : ((‖(1 : ℂ)‖₊ : ENNReal)) ≤ complexSpectralRadius G := by
        rw [complexSpectralRadius, spectralRadius]
        exact le_iSup₂ (α := ENNReal) (1 : ℂ) hmem
      simpa using h2
    exact absurd hG (not_lt.mpr hle)
  rw [spectrum.notMem_iff] at h1
  simp only [map_one] at h1
  rw [← complexify_one, ← complexify_sub, isUnit_complexify_iff] at h1
  exact h1

/-- Saad, Thm 4.1 (⇒): if `ρ(G) < 1` the iteration converges to any fixed point. -/
theorem tendsto_affineStep_of_complexSpectralRadius_lt_one (hG : complexSpectralRadius G < 1)
    (f x₀ : Fin n → ℝ) {x' : Fin n → ℝ} (hfix : affineStep G f x' = x') :
    Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 x') := by
  have hpow : Tendsto (fun k => G ^ k) atTop (𝓝 0) :=
    (tendsto_pow_iff_complexSpectralRadius_lt_one G).mpr hG
  rw [← tendsto_sub_nhds_zero_iff]
  simpa only [affineStep_iterate_sub hfix] using tendsto_mulVec_zero hpow (x₀ - x')

/-- Saad, Theorem 4.1 (⇒): `ρ(G) < 1` implies that `I - G` is nonsingular and that (4.28) converges
to `(I - G)⁻¹ f` for every `f` and every `x₀`. -/
theorem theorem_4_1_mp (hG : complexSpectralRadius G < 1) :
    IsUnit (1 - G) ∧ ∀ f x₀ : Fin n → ℝ,
      Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 ((1 - G)⁻¹ *ᵥ f)) := by
  have hu := isUnit_one_sub_of_complexSpectralRadius_lt_one hG
  refine ⟨hu, fun f x₀ => tendsto_affineStep_of_complexSpectralRadius_lt_one hG f x₀ ?_⟩
  rw [affineStep_fixed_iff]
  exact mulVec_inv_mulVec hu f

/-- Saad, Theorem 4.1 (⇐): if (4.28) converges for every `f` and every `x₀` then `ρ(G) < 1`. -/
theorem theorem_4_1_mpr (h : ∀ f x₀ : Fin n → ℝ,
    ∃ x, Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 x)) :
    complexSpectralRadius G < 1 := by
  rw [← tendsto_pow_iff_complexSpectralRadius_lt_one]
  refine tendsto_zero_of_forall_mulVec fun w => ?_
  obtain ⟨x, hx⟩ := h w 0
  have hx1 : Tendsto (fun k => (affineStep G w)^[k + 1] 0) atTop (𝓝 x) := by
    simpa [Function.comp_def] using hx.comp (tendsto_add_atTop_nat 1)
  have hd : Tendsto
      (fun k => (affineStep G w)^[k + 1] 0 - (affineStep G w)^[k] 0) atTop (𝓝 0) := by
    simpa using hx1.sub hx
  simpa only [affineStep_iterate_succ_sub, mulVec_zero, sub_zero] using hd

/-- Saad, Theorem 4.1: the iteration (4.28) converges for every `f` and every `x₀` iff `ρ(G) < 1`.
-/
theorem theorem_4_1 (G : Matrix (Fin n) (Fin n) ℝ) :
    (∀ f x₀ : Fin n → ℝ, ∃ x, Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 x)) ↔
      complexSpectralRadius G < 1 :=
  ⟨theorem_4_1_mpr, fun hG f x₀ => ⟨_, (theorem_4_1_mp hG).2 f x₀⟩⟩

/-- Saad §4.2: a splitting whose iteration matrix has spectral radius `< 1` converges to the
solution `A⁻¹ b` from every starting vector. -/
theorem Splitting.tendsto_step (s : Splitting A)
    (hs : complexSpectralRadius s.iterationOperator < 1) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (Splitting.step s b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  have hu : IsUnit (1 - s.iterationOperator) :=
    isUnit_one_sub_of_complexSpectralRadius_lt_one hs
  have hGA : (1 : Matrix (Fin n) (Fin n) ℝ) - s.iterationOperator = s.m⁻¹ * A := by
    rw [iterationOperator_eq_one_sub, sub_sub_cancel]
  have hA : IsUnit A := by
    rw [isUnit_iff_isUnit_det] at hu ⊢
    rw [hGA, det_mul] at hu
    exact isUnit_of_mul_isUnit_right hu
  have hstep : Splitting.step s b = affineStep s.iterationOperator (s.m⁻¹ *ᵥ b) := rfl
  rw [hstep]
  exact tendsto_affineStep_of_complexSpectralRadius_lt_one hs _ x₀
    ((step_fixed_iff s b _).mpr (mulVec_inv_mulVec hA b))

/-! ### Corollary 4.2 -/

section Lp

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- `lpCLM` is multiplicative on powers. -/
theorem lpCLM_pow (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : lpCLM p (A ^ k) = lpCLM p A ^ k := by
  induction k with
  | zero => simpa using lpCLM_one p
  | succ k ih => rw [pow_succ, pow_succ, lpCLM_mul, ih]

/-- Submultiplicativity of the induced `p`-norm on powers, including `k = 0`. -/
theorem lpOpNorm_pow_le (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    lpOpNorm p (A ^ k) ≤ lpOpNorm p A ^ k := by
  simp only [lpOpNorm, lpCLM_pow]
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

/-- Saad, Corollary 4.2, for the norm `‖·‖_p` induced by a vector `p`-norm: `‖G‖_p < 1` forces `ρ(G)
< 1`. -/
theorem complexSpectralRadius_lt_one_of_lpOpNorm_lt_one {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : lpOpNorm p G < 1) : complexSpectralRadius G < 1 := by
  have hnn : (0 : ℝ) ≤ lpOpNorm p G := norm_nonneg _
  rw [← tendsto_pow_iff_complexSpectralRadius_lt_one]
  refine tendsto_zero_of_forall_mulVec fun v => ?_
  set y : PiLp p (fun _ : Fin n => ℝ) := WithLp.toLp p v with hy
  have hbound : ∀ k, ‖(WithLp.toLp p ((G ^ k) *ᵥ v) : PiLp p (fun _ : Fin n => ℝ))‖
      ≤ lpOpNorm p G ^ k * ‖y‖ := by
    intro k
    have h1 : (WithLp.toLp p ((G ^ k) *ᵥ v) : PiLp p (fun _ : Fin n => ℝ)) = lpCLM p (G ^ k) y :=
      rfl
    rw [h1]
    exact (lpCLM p (G ^ k)).le_opNorm y |>.trans
      (mul_le_mul_of_nonneg_right (lpOpNorm_pow_le p G k) (norm_nonneg y))
  have hlim : Tendsto (fun k => lpOpNorm p G ^ k * ‖y‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hnn hG).mul_const ‖y‖
  have hL : Tendsto (fun k => (WithLp.toLp p ((G ^ k) *ᵥ v) : PiLp p (fun _ : Fin n => ℝ)))
      atTop (𝓝 0) := squeeze_zero_norm hbound hlim
  have hc : Continuous (WithLp.ofLp : PiLp p (fun _ : Fin n => ℝ) → (Fin n → ℝ)) :=
    PiLp.continuous_ofLp p _
  simpa [Function.comp_def] using (hc.tendsto 0).comp hL

/-- Saad, Corollary 4.2 for `‖·‖_p`. -/
theorem corollary_4_2_lp {G : Matrix (Fin n) (Fin n) ℝ} (hG : lpOpNorm p G < 1) :
    IsUnit (1 - G) ∧ ∀ f x₀ : Fin n → ℝ,
      Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 ((1 - G)⁻¹ *ᵥ f)) :=
  theorem_4_1_mp (complexSpectralRadius_lt_one_of_lpOpNorm_lt_one p hG)

/-- Saad §4.2, the remark before Theorem 4.6: every eigenvalue is bounded by any induced matrix
norm, `|λ| ≤ ‖A‖_p`. -/
theorem norm_le_lpOpNorm_of_mem_spectrum (A : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ A) : ‖μ‖ ≤ lpOpNorm p A := by
  rw [← Matrix.spectrum_toLin'] at hμ
  obtain ⟨v, hv, hv0⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ).exists_hasEigenvector
  have hAv : A *ᵥ v = μ • v := Module.End.mem_eigenspace_iff.mp hv
  set y : PiLp p (fun _ : Fin n => ℂ) := WithLp.toLp p v with hy
  have hy0 : ‖y‖ ≠ 0 := by
    simp only [ne_eq, norm_eq_zero, hy]
    intro hc
    exact hv0 (by simpa using congrArg WithLp.ofLp hc)
  have h1 : lpCLM p A y = μ • y := by
    rw [lpCLM_apply]
    simp [hy, hAv]
  have h2 : ‖μ‖ * ‖y‖ ≤ lpOpNorm p A * ‖y‖ := by
    have h3 := (lpCLM p A).le_opNorm y
    rw [h1, norm_smul] at h3
    exact h3
  exact le_of_mul_le_mul_right (by simpa using h2)
    (lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy0))

end Lp

/-! ### Example 4.1: Richardson's iteration -/

/-- Saad, Example 4.1: the Richardson step `x ↦ x + α (b - A x)`. -/
def richardsonStep (A : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b x : Fin n → ℝ) : Fin n → ℝ :=
  x + α • (b - A *ᵥ x)

/-- Saad, Example 4.1: the Richardson iteration matrix is `G_α = I - α A`. -/
theorem richardsonStep_eq_affine (A : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b : Fin n → ℝ) :
    richardsonStep A α b = affineStep (1 - α • A) (α • b) := by
  funext x
  rw [richardsonStep, affineStep, sub_mulVec, one_mulVec, smul_mulVec, smul_sub]
  abel

/-- Saad, Example 4.1: Richardson's iteration is the splitting with `M = α⁻¹ I`. -/
theorem richardsonStep_eq (A : Matrix (Fin n) (Fin n) ℝ) {α : ℝ} (hα : α ≠ 0) (b : Fin n → ℝ) :
    richardsonStep A α b = Splitting.step (Stationary.Splitting.richardson A hα) b := by
  funext x
  refine (Splitting.step_eq_of_mulVec _ b x _ ?_).symm
  have hm : (Stationary.Splitting.richardson A hα).m = α⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ) := rfl
  have hx : richardsonStep A α b x - x = α • (b - A *ᵥ x) := by
    rw [richardsonStep]; abel
  rw [hm, hx, smul_mulVec, one_mulVec, smul_smul, inv_mul_cancel₀ hα, one_smul]

/-- Saad, Example 4.1: Richardson's iteration converges for every `b` and `x₀` iff `ρ(I - α A) < 1`.
-/
theorem richardson_tendsto_iff (A : Matrix (Fin n) (Fin n) ℝ) {α : ℝ} (hα : α ≠ 0) :
    (∀ b x₀ : Fin n → ℝ, ∃ x, Tendsto (fun k => (richardsonStep A α b)^[k] x₀) atTop (𝓝 x)) ↔
      complexSpectralRadius (1 - α • A) < 1 := by
  constructor
  · intro h
    refine theorem_4_1_mpr fun f x₀ => ?_
    obtain ⟨x, hx⟩ := h (α⁻¹ • f) x₀
    refine ⟨x, ?_⟩
    rw [richardsonStep_eq_affine, smul_smul, mul_inv_cancel₀ hα, one_smul] at hx
    exact hx
  · intro hG b x₀
    rw [richardsonStep_eq_affine]
    exact ⟨_, (theorem_4_1_mp hG).2 (α • b) x₀⟩

end AffineIteration

/-! ### §4.2.3 Diagonally dominant matrices -/

section DiagonallyDominant

open Filter Topology Finset Stationary

open scoped SaadSparse

variable {n : ℕ}

/-! ### Definition 4.5 -/

/-- **Definition 4.5**, first clause: `A` is *(weakly) diagonally dominant* when
`|a_jj| ≥ ∑_{i ≠ j} |a_ij|` for `j = 1, …, n`.

The sum runs down the *column* `j`, which is how the book prints all three clauses of the
definition, while the proofs of Theorems 4.6 and 4.9 use the row form; both are carried in this
file.  Weak dominance is the clause with no name of its own in the backbone: it is the `dominant`
field of `Matrix.IsIrreduciblyDiagDominant`, and is written out wherever else it is needed. -/
def definition_4_5 {𝕜 : Type*} [RCLike 𝕜] (A : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  ∀ j, ∑ i ∈ univ.erase j, ‖A i j‖ ≤ ‖A j j‖

/-- **Definition 4.5**, second clause: `A` is *strictly diagonally dominant* when
`|a_jj| > ∑_{i ≠ j} |a_ij|` for `j = 1, …, n`. -/
def definition_4_5_strict {𝕜 : Type*} [RCLike 𝕜] (A : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  ∀ j, ∑ i ∈ univ.erase j, ‖A i j‖ < ‖A j j‖

/-- **Definition 4.5**, third clause: `A` is *irreducibly diagonally dominant* when `A` is
irreducible — §3.3.4's `Matrix.IsPatternIrreducible` — and weakly diagonally dominant, with strict
inequality for at least one `j`.

The last conjunct is easy to lose sight of and neither Corollary 4.8 nor Theorem 4.9 holds without
it: `!![1, -1; -1, 1]` is irreducible and weakly diagonally dominant yet singular. -/
def definition_4_5_irreducible {𝕜 : Type*} [RCLike 𝕜] (A : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  A.IsPatternIrreducible ∧ definition_4_5 A ∧ ∃ j, ∑ i ∈ univ.erase j, ‖A i j‖ < ‖A j j‖

/-- Definition 4.5 read back as the backbone's predicates.  The book's three conditions are column
conditions on `A`, hence row conditions on `Aᵀ`: weak dominance is the `dominant` field of
`Matrix.IsIrreduciblyDiagDominant` at `Aᵀ`, and the strict and irreducible clauses are
`Matrix.IsStrictColDiagDominant` and `Matrix.IsIrreduciblyColDiagDominant`, which are the row
predicates of the backbone read at `Aᵀ` by definition.  Corollary 4.8 and Theorem 4.9 below are
stated in those predicates, in both the row and the column form. -/
theorem definition_4_5_iff {𝕜 : Type*} [RCLike 𝕜] (A : Matrix (Fin n) (Fin n) 𝕜) :
    (definition_4_5 A ↔ ∀ i, ∑ j ∈ univ.erase i, ‖Aᵀ i j‖ ≤ ‖Aᵀ i i‖) ∧
      (definition_4_5_strict A ↔ A.IsStrictColDiagDominant) ∧
      (definition_4_5_irreducible A ↔ A.IsIrreduciblyColDiagDominant) :=
  ⟨Iff.rfl, Iff.rfl,
    ⟨fun h => ⟨isIrreducibleAbs_transpose_iff.2 h.1, h.2.1, h.2.2⟩,
      fun h => ⟨isIrreducibleAbs_transpose_iff.1 h.irreducible, h.dominant, h.exists_strict⟩⟩⟩

/-! ### Theorem 4.6 (Gershgorin) -/

/-- Saad, Theorem 4.6 (rows): every eigenvalue lies in one of the discs `|λ - a_ii| ≤ ∑_{j ≠ i}
|a_ij|`. -/
theorem theorem_4_6 (A : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    ∃ i, ‖μ - A i i‖ ≤ ∑ j ∈ univ.erase i, ‖A i j‖ := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (spectrum_subset_iUnion_closedBall A hμ)
  exact ⟨i, by simpa [Metric.mem_closedBall, dist_eq_norm] using hi⟩

/-- Transposing does not change the spectrum.  This is Mathlib's `Matrix.spectrum_transpose`,
restated at `ℂ` because it is the step that turns the row form of Gershgorin's theorem into the
column form. -/
theorem spectrum_transpose (A : Matrix (Fin n) (Fin n) ℂ) : spectrum ℂ Aᵀ = spectrum ℂ A :=
  Matrix.spectrum_transpose A

/-- Saad, Theorem 4.6 (columns): the same statement for the column sums, obtained by transposing. -/
theorem theorem_4_6_col (A : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    ∃ j, ‖μ - A j j‖ ≤ ∑ i ∈ univ.erase j, ‖A i j‖ := by
  obtain ⟨j, hj⟩ := theorem_4_6 Aᵀ (by rwa [spectrum_transpose])
  exact ⟨j, hj⟩

/-! ### Corollary 4.8 -/

/-- Saad, Corollary 4.8 (strict row dominance): a strictly diagonally dominant matrix is
nonsingular. -/
theorem corollary_4_8_strict {𝕜 : Type*} [RCLike 𝕜] {A : Matrix (Fin n) (Fin n) 𝕜}
    (h : A.IsStrictDiagDominant) : IsUnit A :=
  h.isUnit

/-- Saad, Corollary 4.8 (strict column dominance). -/
theorem corollary_4_8_col {𝕜 : Type*} [RCLike 𝕜] {A : Matrix (Fin n) (Fin n) 𝕜}
    (h : A.IsStrictColDiagDominant) : IsUnit A := by
  have hT : IsUnit Aᵀ := ((IsStrictColDiagDominant.transpose_iff A).mpr h).isUnit
  rwa [isUnit_iff_isUnit_det, det_transpose, ← isUnit_iff_isUnit_det] at hT

/-! ### Complexification of the classical splittings -/

/-- Complexification commutes with the iteration operator `1 - m⁻¹ a` of a splitting. -/
theorem complexify_one_sub_inverse_mul (m A : Matrix (Fin n) (Fin n) ℝ) :
    complexify (1 - Ring.inverse m * A) = 1 - Ring.inverse (complexify m) * complexify A := by
  rw [complexify_sub, complexify_one, complexify_mul, ← nonsing_inv_eq_ringInverse,
    ← nonsing_inv_eq_ringInverse, complexify_inv]

/-- The complexification of a real strictly diagonally dominant matrix is strictly diagonally
dominant. -/
theorem isStrictDiagDominant_complexify {A : Matrix (Fin n) (Fin n) ℝ}
    (h : A.IsStrictDiagDominant) : (complexify A).IsStrictDiagDominant := by
  intro i
  simpa using h i

/-- The diagonal part of the complexification is a unit as soon as that of `A` is. -/
theorem isUnit_diagPart_complexify {A : Matrix (Fin n) (Fin n) ℝ} (h : IsUnit (diagPart A)) :
    IsUnit (diagPart (complexify A)) := by
  rw [← complexify_diagPart, isUnit_complexify_iff]
  exact h

/-- The Jacobi iteration matrix of `complexify A` is the complexification of that of `A`. -/
theorem complexify_jacobi_iterationOperator (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (diagPart A)) (h' : IsUnit (diagPart (complexify A))) :
    complexify (jacobiSplitting A h).iterationOperator =
      (jacobiSplitting (complexify A) h').iterationOperator := by
  have e1 : (jacobiSplitting A h).iterationOperator = 1 - Ring.inverse (diagPart A) * A := rfl
  have e2 : (jacobiSplitting (complexify A) h').iterationOperator
      = 1 - Ring.inverse (diagPart (complexify A)) * complexify A := rfl
  rw [e1, e2, ← complexify_diagPart, complexify_one_sub_inverse_mul]

/-- The Gauss–Seidel iteration matrix of `complexify A` is the complexification of that of `A`. -/
theorem complexify_gaussSeidel_iterationOperator (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (diagPart A)) (h' : IsUnit (diagPart (complexify A))) :
    complexify (gaussSeidelSplitting A h).iterationOperator =
      (gaussSeidelSplitting (complexify A) h').iterationOperator := by
  have e1 : (gaussSeidelSplitting A h).iterationOperator
      = 1 - Ring.inverse (diagPart A + strictLower A) * A := rfl
  have e2 : (gaussSeidelSplitting (complexify A) h').iterationOperator
      = 1 - Ring.inverse (diagPart (complexify A) + strictLower (complexify A)) * complexify A :=
    rfl
  rw [e1, e2, ← complexify_diagPart, ← complexify_strictLower, ← complexify_add,
    complexify_one_sub_inverse_mul]

/-! ### Theorem 4.9 -/

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- Saad, Theorem 4.9 (Jacobi, strict row dominance): the Jacobi iteration matrix has spectral
radius `< 1`. -/
theorem jacobi_complexSpectralRadius_lt_one (h : A.IsStrictDiagDominant)
    (hd : IsUnit (diagPart A)) :
    complexSpectralRadius (jacobiSplitting A hd).iterationOperator < 1 := by
  have h' := isUnit_diagPart_complexify hd
  rw [complexSpectralRadius, complexify_jacobi_iterationOperator A hd h']
  exact jacobi_spectralRadius_lt_one _ (isStrictDiagDominant_complexify h) h'

/-- Saad, Theorem 4.9 (Gauss–Seidel, strict row dominance): the Gauss–Seidel iteration matrix has
spectral radius `< 1`. -/
theorem gaussSeidel_complexSpectralRadius_lt_one (h : A.IsStrictDiagDominant)
    (hd : IsUnit (diagPart A)) :
    complexSpectralRadius (gaussSeidelSplitting A hd).iterationOperator < 1 := by
  have h' := isUnit_diagPart_complexify hd
  rw [complexSpectralRadius, complexify_gaussSeidel_iterationOperator A hd h']
  exact gaussSeidel_spectralRadius_lt_one _ (isStrictDiagDominant_complexify h) h'

/-- Saad, Theorem 4.9 (Jacobi): for a strictly diagonally dominant `A` the Jacobi iteration
converges to the solution from every starting vector. -/
theorem theorem_4_9_jacobi (h : A.IsStrictDiagDominant) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (jacobiStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  have hd := h.isUnit_diagPart
  rw [jacobiStep_eq hd]
  exact Splitting.tendsto_step _ (jacobi_complexSpectralRadius_lt_one h hd) b x₀

/-- Saad, Theorem 4.9 (Gauss–Seidel): for a strictly diagonally dominant `A` the Gauss–Seidel
iteration converges to the solution from every starting vector. -/
theorem theorem_4_9_gs (h : A.IsStrictDiagDominant) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (gsStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  have hd := h.isUnit_diagPart
  rw [gsStep_eq hd]
  exact Splitting.tendsto_step _ (gaussSeidel_complexSpectralRadius_lt_one h hd) b x₀

/-- Saad, Theorem 4.9 (Jacobi, strict column dominance): Kress's variant, from
`Matrix.jacobi_spectralRadius_lt_one_of_col`. -/
theorem theorem_4_9_jacobi_col (h : A.IsStrictColDiagDominant) (hd : IsUnit (diagPart A))
    (b x₀ : Fin n → ℝ) : Tendsto (fun k => (jacobiStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  have h' := isUnit_diagPart_complexify hd
  have hcol : (complexify A).IsStrictColDiagDominant := by
    intro j
    simpa using h j
  have hρ : complexSpectralRadius (jacobiSplitting A hd).iterationOperator < 1 := by
    rw [complexSpectralRadius, complexify_jacobi_iterationOperator A hd h']
    exact jacobi_spectralRadius_lt_one_of_col _ hcol h'
  rw [jacobiStep_eq hd]
  exact Splitting.tendsto_step _ hρ b x₀

end DiagonallyDominant

/-! ### §4.2.4–4.2.5 Symmetric positive definite matrices and Young's theory -/

section SymmetricPositiveDefinite

/-- `I n₁, n₂` abbreviates `Fin n₁ ⊕ Fin n₂`, the index type of the two-block partition that
Proposition 4.12 is stated over. -/
local notation "I" n₁ ", " n₂ => Fin n₁ ⊕ Fin n₂

variable {n₁ n₂ : ℕ}

/-- Saad, Proposition 4.12: the block anti-diagonal matrix `B = [[0, B₁₂], [B₂₁, 0]]`. -/
def antiDiag (B₁₂ : Matrix (Fin n₁) (Fin n₂) ℂ) (B₂₁ : Matrix (Fin n₂) (Fin n₁) ℂ) :
    Matrix (I n₁, n₂) (I n₁, n₂) ℂ :=
  fromBlocks 0 B₁₂ B₂₁ 0

/-- The strictly lower block of `B`. -/
def antiDiagL (B₂₁ : Matrix (Fin n₂) (Fin n₁) ℂ) : Matrix (I n₁, n₂) (I n₁, n₂) ℂ :=
  fromBlocks 0 0 B₂₁ 0

/-- The strictly upper block of `B`. -/
def antiDiagU (B₁₂ : Matrix (Fin n₁) (Fin n₂) ℂ) : Matrix (I n₁, n₂) (I n₁, n₂) ℂ :=
  fromBlocks 0 B₁₂ 0 0

/-- `B = L + U`: a block anti-diagonal matrix is the sum of its strictly lower and strictly upper
blocks, so the family `B(α) = α L + α⁻¹ U` of `proposition_4_12_alpha` passes through `B` at `α =
1`. -/
theorem antiDiag_eq_add (B₁₂ : Matrix (Fin n₁) (Fin n₂) ℂ) (B₂₁ : Matrix (Fin n₂) (Fin n₁) ℂ) :
    antiDiag B₁₂ B₂₁ = antiDiagL B₂₁ + antiDiagU B₁₂ := by
  rw [antiDiag, antiDiagL, antiDiagU, fromBlocks_add]
  simp

/-- The sign-flip similarity `diag(I, -I)`, an involution. -/
private def signFlip (n₁ n₂ : ℕ) : Matrix (I n₁, n₂) (I n₁, n₂) ℂ := fromBlocks 1 0 0 (-1)

private theorem signFlip_mul_self (n₁ n₂ : ℕ) : signFlip n₁ n₂ * signFlip n₁ n₂ = 1 := by
  rw [signFlip, fromBlocks_multiply]
  simp [← fromBlocks_one]

/-- `diag(I, -I)` as a unit. -/
private def signFlipUnit (n₁ n₂ : ℕ) : (Matrix (I n₁, n₂) (I n₁, n₂) ℂ)ˣ where
  val := signFlip n₁ n₂
  inv := signFlip n₁ n₂
  val_inv := signFlip_mul_self n₁ n₂
  inv_val := signFlip_mul_self n₁ n₂

/-- Saad, Proposition 4.12 (1): the spectrum of a block anti-diagonal matrix is symmetric under
negation. -/
theorem proposition_4_12_neg (B₁₂ : Matrix (Fin n₁) (Fin n₂) ℂ) (B₂₁ : Matrix (Fin n₂) (Fin n₁) ℂ)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (antiDiag B₁₂ B₂₁)) :
    -μ ∈ spectrum ℂ (antiDiag B₁₂ B₂₁) := by
  have hconj : ((signFlipUnit n₁ n₂ : (Matrix (I n₁, n₂) (I n₁, n₂) ℂ)ˣ) :
        Matrix (I n₁, n₂) (I n₁, n₂) ℂ) * antiDiag B₁₂ B₂₁ *
      (((signFlipUnit n₁ n₂)⁻¹ : (Matrix (I n₁, n₂) (I n₁, n₂) ℂ)ˣ) :
        Matrix (I n₁, n₂) (I n₁, n₂) ℂ) = -antiDiag B₁₂ B₂₁ := by
    change signFlip n₁ n₂ * antiDiag B₁₂ B₂₁ * signFlip n₁ n₂ = _
    rw [signFlip, antiDiag, fromBlocks_multiply, fromBlocks_multiply]
    simp [fromBlocks_neg]
  have hspec : spectrum ℂ (-antiDiag B₁₂ B₂₁) = spectrum ℂ (antiDiag B₁₂ B₂₁) := by
    rw [← hconj]
    exact spectrum.units_conjugate
  have hneg : -spectrum ℂ (antiDiag B₁₂ B₂₁) = spectrum ℂ (antiDiag B₁₂ B₂₁) := by
    rw [spectrum.neg_eq, hspec]
  rw [← hneg, Set.mem_neg, neg_neg]
  exact hμ

/-- The scaling similarity `diag(I, α I)`. -/
private def scaleBlock (n₁ n₂ : ℕ) (α : ℂ) : Matrix (I n₁, n₂) (I n₁, n₂) ℂ :=
  fromBlocks 1 0 0 (α • 1)

private theorem scaleBlock_mul_inv (n₁ n₂ : ℕ) {α : ℂ} (hα : α ≠ 0) :
    scaleBlock n₁ n₂ α * scaleBlock n₁ n₂ α⁻¹ = 1 := by
  rw [scaleBlock, scaleBlock, fromBlocks_multiply]
  simp [smul_smul, inv_mul_cancel₀ hα, ← fromBlocks_one]

/-- `diag(I, α I)` as a unit, for `α ≠ 0`. -/
private noncomputable def scaleBlockUnit (n₁ n₂ : ℕ) {α : ℂ} (hα : α ≠ 0) :
    (Matrix (I n₁, n₂) (I n₁, n₂) ℂ)ˣ where
  val := scaleBlock n₁ n₂ α
  inv := scaleBlock n₁ n₂ α⁻¹
  val_inv := scaleBlock_mul_inv n₁ n₂ hα
  inv_val := by
    have h := scaleBlock_mul_inv n₁ n₂ (α := α⁻¹) (inv_ne_zero hα)
    rwa [inv_inv] at h

/-- Saad, Proposition 4.12 (2): the eigenvalues of `B(α) = α L + α⁻¹ U` do not depend on `α ≠ 0`. -/
theorem proposition_4_12_alpha (B₁₂ : Matrix (Fin n₁) (Fin n₂) ℂ) (B₂₁ : Matrix (Fin n₂) (Fin n₁) ℂ)
    {α : ℂ} (hα : α ≠ 0) :
    spectrum ℂ (α • antiDiagL B₂₁ + α⁻¹ • antiDiagU B₁₂) =
      spectrum ℂ (antiDiag B₁₂ B₂₁) := by
  have hconj : ((scaleBlockUnit n₁ n₂ hα : (Matrix (I n₁, n₂) (I n₁, n₂) ℂ)ˣ) :
        Matrix (I n₁, n₂) (I n₁, n₂) ℂ) * antiDiag B₁₂ B₂₁ *
      (((scaleBlockUnit n₁ n₂ hα)⁻¹ : (Matrix (I n₁, n₂) (I n₁, n₂) ℂ)ˣ) :
        Matrix (I n₁, n₂) (I n₁, n₂) ℂ)
      = α • antiDiagL B₂₁ + α⁻¹ • antiDiagU B₁₂ := by
    change scaleBlock n₁ n₂ α * antiDiag B₁₂ B₂₁ * scaleBlock n₁ n₂ α⁻¹ = _
    rw [scaleBlock, scaleBlock, antiDiag, antiDiagL, antiDiagU, fromBlocks_multiply,
      fromBlocks_multiply, fromBlocks_smul, fromBlocks_smul, fromBlocks_add]
    simp [Matrix.smul_mul, Matrix.mul_smul]
  rw [← hconj]
  exact spectrum.units_conjugate

end SymmetricPositiveDefinite

/-! ### §4.2.1 The convergence factors, and Corollary 4.2 for a general matrix norm -/

section Factors

open Filter Topology Stationary

open scoped SaadSparse ENNReal NNReal

variable {n : ℕ}

/-- Saad §1.5/§4.2: the spectral radius is at most any *consistent* matrix norm, that is any
submultiplicative, absolutely homogeneous, positive definite `N`.  This is the remark `|λ| ≤ ‖A‖`
before Theorem 4.6, for a norm that need not be one of the induced `p`-norms. -/
theorem complexSpectralRadius_le_algebraNorm (N : AlgebraNorm ℝ (Matrix (Fin n) (Fin n) ℝ))
    (G : Matrix (Fin n) (Fin n) ℝ) : complexSpectralRadius G ≤ ENNReal.ofReal (N G) := by
  have hnn : ∀ B : Matrix (Fin n) (Fin n) ℝ, 0 ≤ N B := fun B => apply_nonneg N B
  set f : Matrix (Fin n) (Fin n) ℝ → ℝ≥0 := fun B => ⟨N B, hnn B⟩ with hf
  have hcoe : ∀ B : Matrix (Fin n) (Fin n) ℝ, ((f B : ℝ≥0) : ℝ) = N B := fun _ => rfl
  have hmul : ∀ B C : Matrix (Fin n) (Fin n) ℝ, f (B * C) ≤ f B * f C := by
    intro B C
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, hcoe, hcoe, hcoe]
    exact map_mul_le_mul N B C
  have hsmul : ∀ (r : ℝ) (B : Matrix (Fin n) (Fin n) ℝ), f (r • B) = ‖r‖₊ * f B := by
    intro r B
    refine NNReal.coe_injective ?_
    rw [NNReal.coe_mul, coe_nnnorm, hcoe, hcoe]
    exact map_smul_eq_mul N r B
  have hzero : ∀ B : Matrix (Fin n) (Fin n) ℝ, f B = 0 → B = 0 := by
    intro B hB
    refine eq_zero_of_map_eq_zero N ?_
    rw [← hcoe B, hB, NNReal.coe_zero]
  rw [ENNReal.ofReal_eq_coe_nnreal (hnn G)]
  exact Matrix.complexSpectralRadius_le_of_norm f G hmul hsmul hzero

/-- Saad, Corollary 4.2: if `N G < 1` for some consistent matrix norm `N`, then `I - G` is
nonsingular and the iteration (4.28) converges for every `f` and every `x₀`.  The induced-norm
instances are `corollary_4_2_lp`. -/
theorem corollary_4_2 (N : AlgebraNorm ℝ (Matrix (Fin n) (Fin n) ℝ))
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : N G < 1) :
    IsUnit (1 - G) ∧ ∀ f x₀ : Fin n → ℝ,
      Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 ((1 - G)⁻¹ *ᵥ f)) := by
  refine theorem_4_1_mp ((complexSpectralRadius_le_algebraNorm N G).trans_lt ?_)
  exact ENNReal.ofReal_lt_one.mpr hG

open scoped Matrix.Norms.L2Operator in
/-- Saad §4.2.1: the *general convergence factor* `φ = lim ‖G^k‖^{1/k}` is the spectral radius of
`G` — Gelfand's formula for a real matrix, under the `l²` operator norm. -/
theorem tendsto_generalFactor (G : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k : ℕ => ‖G ^ k‖ ^ (1 / k : ℝ)) atTop
      (𝓝 (complexSpectralRadius G).toReal) :=
  Matrix.tendsto_pow_rpow_complexSpectralRadius G

/-- Saad §4.2.1: the general convergence factor is *attained* — some initial error `d₀` decays
exactly at the rate `ρ(G)`. -/
theorem exists_specific_eq [NeZero n] (G : Matrix (Fin n) (Fin n) ℝ) :
    ∃ d₀ : Fin n → ℝ, d₀ ≠ 0 ∧
      limsup (fun k : ℕ => (‖(WithLp.toLp 2 ((G ^ k) *ᵥ d₀) : EuclideanSpace ℝ (Fin n))‖ /
          ‖(WithLp.toLp 2 d₀ : EuclideanSpace ℝ (Fin n))‖) ^ (1 / k : ℝ)) atTop =
        (complexSpectralRadius G).toReal :=
  Matrix.exists_limsup_norm_pow_mulVec_rpow_eq G

end Factors

/-! ### Example 4.1: the spectral analysis of Richardson's iteration -/

section Richardson

open Filter Topology Stationary

open scoped SaadSparse ENNReal

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {lmin lmax : ℝ}

/-- Saad, Example 4.1: for a symmetric `A` whose eigenvalues fill `[λmin, λmax]`, the spectral
radius of the Richardson iteration matrix `G_α = I - α A` is `max |1 - α λmin| |1 - α λmax|`. -/
theorem example_4_1_spectralRadius (hA : A.IsHermitian) (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ A) (hmax : lmax ∈ spectrum ℝ A) {α : ℝ} (hα : α ≠ 0) :
    complexSpectralRadius (1 - α • A) = ENNReal.ofReal (max |1 - α * lmin| |1 - α * lmax|) := by
  rw [← Splitting.richardson_iterationOperator A hα]
  exact Splitting.richardson_complexSpectralRadius_eq hA hsub hmin hmax hα

/-- Saad, Example 4.1: for a symmetric positive definite `A`, Richardson's iteration converges for
every right-hand side and every starting vector exactly when `0 < α < 2/λmax`. -/
theorem example_4_1_tendsto_iff (hA : A.IsHermitian) (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ A) (hmax : lmax ∈ spectrum ℝ A) (hpos : 0 < lmin) {α : ℝ}
    (hα : α ≠ 0) :
    (∀ b x₀ : Fin n → ℝ, ∃ x, Tendsto (fun k => (richardsonStep A α b)^[k] x₀) atTop (𝓝 x)) ↔
      0 < α ∧ α < 2 / lmax := by
  rw [richardson_tendsto_iff A hα, ← Splitting.richardson_iterationOperator A hα]
  exact Splitting.richardson_complexSpectralRadius_lt_one_iff hA hsub hmin hmax hpos hα

/-- Saad, Example 4.1: when `A` has eigenvalues of both signs, Richardson's iteration diverges for
some right-hand side and some starting vector, whatever the parameter `α ≠ 0`. -/
theorem example_4_1_diverges (hA : A.IsHermitian) (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ A) (hmax : lmax ∈ spectrum ℝ A) (hneg : lmin < 0) (hpos : 0 < lmax)
    {α : ℝ} (hα : α ≠ 0) :
    ∃ b x₀ : Fin n → ℝ, ¬ ∃ x, Tendsto (fun k => (richardsonStep A α b)^[k] x₀) atTop (𝓝 x) := by
  have hge : (1 : ℝ) ≤ max |1 - α * lmin| |1 - α * lmax| := by
    rcases lt_or_gt_of_ne hα with hlt | hlt
    · refine le_max_of_le_right ?_
      rw [le_abs]
      exact Or.inl (by nlinarith)
    · refine le_max_of_le_left ?_
      rw [le_abs]
      exact Or.inl (by nlinarith)
  have hρ : ¬ complexSpectralRadius (1 - α • A) < 1 := by
    rw [example_4_1_spectralRadius hA hsub hmin hmax hα, not_lt, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hge
  by_contra hcon
  push Not at hcon
  exact hρ ((richardson_tendsto_iff A hα).mp fun b x₀ => hcon b x₀)

/-- Saad, Example 4.1: the optimal Richardson parameter is `α_opt = 2/(λmin + λmax)`, where the
spectral radius is `(λmax - λmin)/(λmax + λmin)`. -/
theorem example_4_1_opt (hA : A.IsHermitian) (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ A) (hmax : lmax ∈ spectrum ℝ A) (hpos : 0 < lmin) :
    IsMinOn (fun α : ℝ => complexSpectralRadius (1 - α • A)) (Set.Ioi 0)
        (2 / (lmin + lmax)) ∧
      complexSpectralRadius (1 - (2 / (lmin + lmax)) • A) =
        ENNReal.ofReal ((lmax - lmin) / (lmax + lmin)) :=
  ⟨Splitting.isMinOn_richardson_complexSpectralRadius hA hsub hmin hmax hpos,
    Splitting.richardson_complexSpectralRadius_optimal_eq hA hsub hmin hmax hpos⟩

end Richardson

/-! ### Definition 4.3 and Theorem 4.4: regular splittings -/

section Regular

open Filter Topology Stationary

open scoped SaadSparse ENNReal

variable {n : ℕ} {A M N : Matrix (Fin n) (Fin n) ℝ}

/-- Saad, Definition 4.3: `A = M - N` is a *regular splitting* of `A` when `M` is nonsingular with
`M⁻¹ ≥ 0` and `N ≥ 0`. -/
def IsRegularSplitting (A M N : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A = M - N ∧ IsUnit M ∧ (∀ i j, 0 ≤ M⁻¹ i j) ∧ ∀ i j, 0 ≤ N i j

/-- The complementary part of the splitting determined by `M` is `N`. -/
theorem splitting_n_eq (h : IsRegularSplitting A M N) :
    (⟨M, h.2.1⟩ : Splitting A).n = N := by
  have h1 : (⟨M, h.2.1⟩ : Splitting A).n = M - A := rfl
  rw [h1, h.1]
  abel

/-- Saad, Definition 4.3 is the backbone's `Stationary.Splitting.IsRegular` for the splitting
determined by `M`. -/
theorem isRegularSplitting_iff (hMN : A = M - N) (hM : IsUnit M) :
    IsRegularSplitting A M N ↔ (⟨M, hM⟩ : Splitting A).IsRegular := by
  have hn : (⟨M, hM⟩ : Splitting A).n = N := by
    have h1 : (⟨M, hM⟩ : Splitting A).n = M - A := rfl
    rw [h1, hMN]; abel
  have hinv : Ring.inverse (⟨M, hM⟩ : Splitting A).m = M⁻¹ :=
    (nonsing_inv_eq_ringInverse M).symm
  rw [Stationary.Splitting.IsRegular, hinv, hn]
  simp only [Matrix.entrywiseNonneg_iff, IsRegularSplitting]
  exact ⟨fun h => ⟨h.2.2.1, h.2.2.2⟩, fun h => ⟨hMN, hM, h.1, h.2⟩⟩

/-- **Saad, Theorem 4.4**: a regular splitting converges exactly when `A` is nonsingular with a
nonnegative inverse. -/
theorem theorem_4_4 (h : IsRegularSplitting A M N) :
    complexSpectralRadius (M⁻¹ * N) < 1 ↔ IsUnit A ∧ ∀ i j, 0 ≤ A⁻¹ i j := by
  have hreg : (⟨M, h.2.1⟩ : Splitting A).IsRegular :=
    (isRegularSplitting_iff h.1 h.2.1).mp h
  have hiter : (⟨M, h.2.1⟩ : Splitting A).iterationOperator = M⁻¹ * N := by
    rw [Stationary.Splitting.iterationOperator_eq, splitting_n_eq h,
      ← nonsing_inv_eq_ringInverse]
  rw [← hiter, hreg.complexSpectralRadius_lt_one_iff]
  simp [Matrix.entrywiseNonneg_iff]

/-- Saad, the remark after Theorem 4.4: the iteration (4.34) of *every* regular splitting of an
M-matrix converges to the solution, from every starting vector. -/
theorem theorem_4_4_mmatrix (h : IsRegularSplitting A M N) (hA : A.IsMMatrix) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (affineStep (M⁻¹ * N) (M⁻¹ *ᵥ b))^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  have hreg : (⟨M, h.2.1⟩ : Splitting A).IsRegular :=
    (isRegularSplitting_iff h.1 h.2.1).mp h
  have hiter : (⟨M, h.2.1⟩ : Splitting A).iterationOperator = M⁻¹ * N := by
    rw [Stationary.Splitting.iterationOperator_eq, splitting_n_eq h,
      ← nonsing_inv_eq_ringInverse]
  have hstep : affineStep (M⁻¹ * N) (M⁻¹ *ᵥ b) = Splitting.step (⟨M, h.2.1⟩ : Splitting A) b := by
    rw [Splitting.step, hiter]
  rw [hstep]
  exact Splitting.tendsto_step _ (hiter ▸ hreg.complexSpectralRadius_lt_one_of_isMMatrix hA) b x₀

end Regular

/-! ### Theorem 4.7 and the irreducible halves of Corollary 4.8 and Theorem 4.9 -/

section Irreducible

open Filter Topology Finset Stationary

open scoped SaadSparse

variable {n : ℕ}

/-- **Saad, Theorem 4.7**: for an irreducible matrix, an eigenvalue on the boundary of the union of
the Gershgorin discs lies on the boundary of *every* disc. -/
theorem theorem_4_7 {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsIrreducibleAbs) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ A)
    (hfr : μ ∈ frontier (⋃ i, Metric.closedBall (A i i) (∑ j ∈ univ.erase i, ‖A i j‖)))
    (i : Fin n) : ‖μ - A i i‖ = ∑ j ∈ univ.erase i, ‖A i j‖ :=
  hA.norm_sub_eq_of_mem_frontier hμ hfr i

/-- Saad, Corollary 4.8, the irreducibly diagonally dominant half: an irreducibly diagonally
dominant matrix is nonsingular. -/
theorem corollary_4_8_irred {𝕜 : Type*} [RCLike 𝕜] {A : Matrix (Fin n) (Fin n) 𝕜}
    (h : A.IsIrreduciblyDiagDominant) : IsUnit A :=
  h.isUnit

/-- Saad, Corollary 4.8 for irreducible dominance by *columns*, the reading of Definition 4.5 as
printed. -/
theorem corollary_4_8_irred_col {𝕜 : Type*} [RCLike 𝕜] {A : Matrix (Fin n) (Fin n) 𝕜}
    (h : A.IsIrreduciblyColDiagDominant) : IsUnit A := by
  have hT : IsUnit Aᵀ := Matrix.IsIrreduciblyDiagDominant.isUnit h
  rwa [isUnit_iff_isUnit_det, det_transpose, ← isUnit_iff_isUnit_det] at hT

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- Complexification changes no entrywise absolute value, so it preserves irreducibility. -/
theorem isIrreducibleAbs_complexify (h : A.IsIrreducibleAbs) :
    (complexify A).IsIrreducibleAbs := by
  have hmap : (complexify A).map (fun x : ℂ => ‖x‖) = A.map fun x : ℝ => ‖x‖ := by
    ext i j; simp [complexify]
  change Matrix.IsIrreducible ((complexify A).map fun x : ℂ => ‖x‖)
  rw [hmap]
  exact h

/-- Complexification preserves irreducible diagonal dominance. -/
theorem isIrreduciblyDiagDominant_complexify (h : A.IsIrreduciblyDiagDominant) :
    (complexify A).IsIrreduciblyDiagDominant where
  irreducible := isIrreducibleAbs_complexify h.irreducible
  dominant i := by simpa using h.dominant i
  exists_strict := by
    obtain ⟨i, hi⟩ := h.exists_strict
    exact ⟨i, by simpa using hi⟩

/-- Saad, Theorem 4.9 (Jacobi, irreducible dominance): the Jacobi iteration matrix of an irreducibly
diagonally dominant matrix has spectral radius `< 1`. -/
theorem jacobi_complexSpectralRadius_lt_one_irred (h : A.IsIrreduciblyDiagDominant) :
    complexSpectralRadius (jacobiSplitting A h.isUnit_diagPart).iterationOperator < 1 := by
  have h' := isUnit_diagPart_complexify h.isUnit_diagPart
  rw [complexSpectralRadius, complexify_jacobi_iterationOperator A h.isUnit_diagPart h']
  exact (isIrreduciblyDiagDominant_complexify h).jacobi_spectralRadius_lt_one h'

/-- Saad, Theorem 4.9 (Gauss–Seidel, irreducible dominance). -/
theorem gaussSeidel_complexSpectralRadius_lt_one_irred (h : A.IsIrreduciblyDiagDominant) :
    complexSpectralRadius (gaussSeidelSplitting A h.isUnit_diagPart).iterationOperator < 1 := by
  have h' := isUnit_diagPart_complexify h.isUnit_diagPart
  rw [complexSpectralRadius, complexify_gaussSeidel_iterationOperator A h.isUnit_diagPart h']
  exact (isIrreduciblyDiagDominant_complexify h).gaussSeidel_spectralRadius_lt_one h'

/-- **Saad, Theorem 4.9** (Jacobi), the irreducibly diagonally dominant half: the Jacobi iteration
converges to the solution from every starting vector. -/
theorem theorem_4_9_jacobi_irred (h : A.IsIrreduciblyDiagDominant) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (jacobiStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  rw [jacobiStep_eq h.isUnit_diagPart]
  exact Splitting.tendsto_step _ (jacobi_complexSpectralRadius_lt_one_irred h) b x₀

/-- **Saad, Theorem 4.9** (Gauss–Seidel), the irreducibly diagonally dominant half. -/
theorem theorem_4_9_gs_irred (h : A.IsIrreduciblyDiagDominant) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (gsStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  rw [gsStep_eq h.isUnit_diagPart]
  exact Splitting.tendsto_step _ (gaussSeidel_complexSpectralRadius_lt_one_irred h) b x₀

/-- Saad, Theorem 4.9 (Gauss–Seidel) under strict *column* diagonal dominance, the reading of
Definition 4.5 as printed. -/
theorem theorem_4_9_gs_col (h : A.IsStrictColDiagDominant) (hd : IsUnit (diagPart A))
    (b x₀ : Fin n → ℝ) : Tendsto (fun k => (gsStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  have h' := isUnit_diagPart_complexify hd
  have hcol : (complexify A).IsStrictColDiagDominant := by
    intro j
    simpa using h j
  have hρ : complexSpectralRadius (gaussSeidelSplitting A hd).iterationOperator < 1 := by
    rw [complexSpectralRadius, complexify_gaussSeidel_iterationOperator A hd h']
    exact Matrix.gaussSeidel_spectralRadius_lt_one_of_col _ hcol h'
  rw [gsStep_eq hd]
  exact Splitting.tendsto_step _ hρ b x₀

end Irreducible

/-! ### Theorem 4.10: SOR for symmetric positive definite matrices -/

section SOR

open Filter Topology Stationary

open scoped SaadSparse

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}

/-- **Saad, Theorem 4.10**: for a real symmetric `A` with positive diagonal and `0 < ω < 2`, the SOR
iteration matrix has spectral radius `< 1` exactly when `A` is positive definite. -/
theorem theorem_4_10 (hA : A.IsSymm) (hd : ∀ i, 0 < A i i) (h : IsUnit (diagPart A)) {ω : ℝ}
    (hω0 : 0 < ω) (hω2 : ω < 2) :
    complexSpectralRadius (A.sorSplitting h hω0.ne').iterationOperator < 1 ↔ A.PosDef :=
  Matrix.sorSplitting_complexSpectralRadius_lt_one_iff_posDef
    (Matrix.isHermitian_iff_isSymm.2 hA) hd h hω0 hω2

/-- **Saad, Theorem 4.10** in the book's words, read through Theorem 4.1: SOR converges for every
right-hand side and every starting vector exactly when `A` is positive definite.  The quantifier
over the right-hand side cannot be dropped: for a singular positive semidefinite `A` and `b = 0` the
iterates converge for every `x₀`. -/
theorem theorem_4_10_tendsto (hA : A.IsSymm) (hd : ∀ i, 0 < A i i) (h : IsUnit (diagPart A))
    {ω : ℝ} (hω0 : 0 < ω) (hω2 : ω < 2) :
    (∀ b x₀ : Fin n → ℝ, ∃ x, Tendsto (fun k => (sorStep A ω b)^[k] x₀) atTop (𝓝 x)) ↔
      A.PosDef := by
  rw [← theorem_4_10 hA hd h hω0 hω2]
  constructor
  · intro hconv
    refine theorem_4_1_mpr fun f x₀ => ?_
    obtain ⟨x, hx⟩ := hconv ((A.sorSplitting h hω0.ne').m *ᵥ f) x₀
    refine ⟨x, ?_⟩
    rw [sorStep_eq h hω0.ne', Splitting.step,
      inv_mulVec_mulVec (A.sorSplitting h hω0.ne').isUnit f] at hx
    exact hx
  · intro hρ b x₀
    rw [sorStep_eq h hω0.ne']
    exact ⟨_, Splitting.tendsto_step _ hρ b x₀⟩

end SOR

/-! ### §4.2.5 Property A, consistent orderings and Young's theory -/

section Young

open Filter Topology Finset Stationary

open scoped SaadSparse ENNReal

variable {n : ℕ}

/-! #### Definition 4.11: Property A -/

/-- **Saad, Definition 4.11**: `A` has *Property A* when the index set splits into two parts `S` and
its complement in such a way that every nonzero off-diagonal entry couples the two parts. -/
def HasPropertyA (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ S : Finset (Fin n), ∀ i j, A i j ≠ 0 → i ≠ j → (i ∈ S ↔ j ∉ S)

/-- Saad (4.42): Property A says exactly that the symmetric permutation listing `S` before its
complement brings `A` to the two-by-two block form whose diagonal blocks `D₁` and `D₂` are
*diagonal* matrices. -/
theorem hasPropertyA_iff_toBlocks_isDiag (A : Matrix (Fin n) (Fin n) ℂ) :
    HasPropertyA A ↔ ∃ S : Finset (Fin n),
      Matrix.IsDiag (A.submatrix (Equiv.sumCompl (· ∈ S))
          (Equiv.sumCompl (· ∈ S))).toBlocks₁₁ ∧
        Matrix.IsDiag (A.submatrix (Equiv.sumCompl (· ∈ S))
          (Equiv.sumCompl (· ∈ S))).toBlocks₂₂ := by
  have hb₁ : ∀ (S : Finset (Fin n)) (i j : {x : Fin n // x ∈ S}),
      (A.submatrix (Equiv.sumCompl (· ∈ S)) (Equiv.sumCompl (· ∈ S))).toBlocks₁₁ i j =
        A (i : Fin n) (j : Fin n) := fun _ _ _ => rfl
  have hb₂ : ∀ (S : Finset (Fin n)) (i j : {x : Fin n // x ∉ S}),
      (A.submatrix (Equiv.sumCompl (· ∈ S)) (Equiv.sumCompl (· ∈ S))).toBlocks₂₂ i j =
        A (i : Fin n) (j : Fin n) := fun _ _ _ => rfl
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S, fun i j hij => ?_, fun i j hij => ?_⟩
    · dsimp only
      rw [hb₁]
      by_contra hA
      exact ((hS _ _ hA fun h => hij (Subtype.ext h)).mp i.2) j.2
    · dsimp only
      rw [hb₂]
      by_contra hA
      exact i.2 ((hS _ _ hA fun h => hij (Subtype.ext h)).mpr j.2)
  · rintro ⟨S, h₁, h₂⟩
    refine ⟨S, fun i j hA hij => ?_⟩
    constructor
    · intro hi hj
      refine hA ?_
      rw [← hb₁ S ⟨i, hi⟩ ⟨j, hj⟩]
      exact h₁ fun h => hij (congrArg Subtype.val h)
    · intro hj
      by_contra hi
      refine hA ?_
      rw [← hb₂ S ⟨i, hi⟩ ⟨j, hj⟩]
      exact h₂ fun h => hij (congrArg Subtype.val h)

/-- Property A is invariant under symmetric permutations of the indices. -/
theorem hasPropertyA_reindex (A : Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) :
    HasPropertyA (A.submatrix σ σ) ↔ HasPropertyA A := by
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S.map σ.toEmbedding, fun a b hA hab => ?_⟩
    have h := hS (σ.symm a) (σ.symm b) (by simpa using hA)
      (fun h => hab (by simpa using congrArg σ h))
    simpa [Finset.mem_map_equiv] using h
  · rintro ⟨S, hS⟩
    refine ⟨S.map σ.symm.toEmbedding, fun i j hA hij => ?_⟩
    have h := hS (σ i) (σ j) hA fun h => hij (σ.injective h)
    simpa [Finset.mem_map_equiv] using h

/-! #### Definition 4.13: consistent orderings and T-matrices -/

/-- **Saad, Definition 4.13**: `A` is *consistently ordered* when the indices carry a labelling `c`
— Saad's partition into the sets `S_k = c⁻¹ {k}` — such that `c j = c i - 1` for every nonzero entry
`a_ij` below the diagonal and `c j = c i + 1` for every nonzero entry above it. -/
def IsConsistentlyOrdered (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ c : Fin n → ℕ, (∀ i j, j < i → A i j ≠ 0 → c i = c j + 1) ∧
    ∀ i j, i < j → A i j ≠ 0 → c j = c i + 1

/-- **Saad §4.2.5**: `A` is a *T-matrix* — the block tridiagonal form (4.44), whose diagonal blocks
are diagonal matrices — when the indices carry a *nondecreasing* block labelling under which every
nonzero off-diagonal entry joins two neighbouring blocks. -/
def IsTMatrix (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ c : Fin n → ℕ, Monotone c ∧ ∀ i j, i ≠ j → A i j ≠ 0 → c i = c j + 1 ∨ c j = c i + 1

/-- Saad §4.2.5: a T-matrix is consistently ordered — its block labelling is a consistent ordering,
precisely because it is nondecreasing along the index order. -/
theorem isConsistentlyOrdered_of_isTMatrix {A : Matrix (Fin n) (Fin n) ℂ} (h : IsTMatrix A) :
    IsConsistentlyOrdered A := by
  obtain ⟨c, hmono, hstep⟩ := h
  refine ⟨c, fun i j hji hA => ?_, fun i j hij hA => ?_⟩
  · have hle : c j ≤ c i := hmono hji.le
    rcases hstep i j hji.ne' hA with h1 | h1
    · exact h1
    · omega
  · have hle : c i ≤ c j := hmono hij.le
    rcases hstep i j hij.ne hA with h1 | h1
    · omega
    · exact h1

/-- Saad §4.2.5: a consistently ordered matrix has Property A — the labelling splits the indices by
the parity of `c`, and a nonzero off-diagonal entry changes `c` by one. -/
theorem hasPropertyA_of_isConsistentlyOrdered {A : Matrix (Fin n) (Fin n) ℂ}
    (h : IsConsistentlyOrdered A) : HasPropertyA A := by
  classical
  obtain ⟨c, hlow, hupp⟩ := h
  refine ⟨Finset.univ.filter fun i => Even (c i), fun i j hA hij => ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · rw [hupp i j hlt hA, Nat.even_add_one]
    tauto
  · rw [hlow i j hgt hA, Nat.even_add_one]

/-- **Saad §4.2.5** (the second bullet after Proposition 4.15, repeated as Problem P-4.6): `A` has
Property A *if and only if* some symmetric permutation `PᵀAP` of it is consistently ordered.

For `⇐` the permuted matrix has Property A by the previous result, and Property A is invariant
under symmetric permutations.  For `⇒`, order the set `S` of Definition 4.11 before its complement:
the stable sort of the two-valued labelling `c i = if i ∈ S then 0 else 1` does that, and `c`
composed with it is the consistent ordering.  A nonzero off-diagonal entry joins the two parts, so
the two labels differ, and they are `0` then `1` in the direction Definition 4.13 demands because
the sorted labelling is nondecreasing. -/
theorem hasPropertyA_iff_exists_isConsistentlyOrdered (A : Matrix (Fin n) (Fin n) ℂ) :
    HasPropertyA A ↔ ∃ σ : Equiv.Perm (Fin n), IsConsistentlyOrdered (A.submatrix σ σ) := by
  classical
  constructor
  · rintro ⟨S, hS⟩
    set c : Fin n → ℕ := fun i => if i ∈ S then 0 else 1 with hc
    set σ := Tuple.sort c with hσ
    have hmono : Monotone (c ∘ σ) := Tuple.monotone_sort c
    have key : ∀ i j : Fin n, i ≠ j → A (σ i) (σ j) ≠ 0 →
        ((c ∘ σ) i = 0 ∧ (c ∘ σ) j = 1) ∨ ((c ∘ σ) i = 1 ∧ (c ∘ σ) j = 0) := by
      intro i j hij hA
      have h := hS (σ i) (σ j) hA fun h => hij (σ.injective h)
      by_cases hi : σ i ∈ S
      · exact Or.inl ⟨by simp [hc, hi], by simp [hc, h.mp hi]⟩
      · exact Or.inr ⟨by simp [hc, hi], by simp [hc, not_not.mp fun hj => hi (h.mpr hj)]⟩
    refine ⟨σ, c ∘ σ, fun i j hji hA => ?_, fun i j hij hA => ?_⟩
    · have hle := hmono hji.le
      rcases key i j hji.ne' hA with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · have hle := hmono hij.le
      rcases key i j hij.ne hA with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · rintro ⟨σ, hσ⟩
    exact (hasPropertyA_reindex A σ).mp (hasPropertyA_of_isConsistentlyOrdered hσ)

/-- **Saad, Proposition 4.15**: the book's labelling definition of a consistent ordering implies the
spectral one that Young's theory uses — the spectrum of `α L + α⁻¹ U` does not depend on `α ≠ 0`,
`L` and `U` being the strict parts of the Jacobi iteration matrix. -/
theorem IsConsistentlyOrdered.matrix_isConsistentlyOrdered {A : Matrix (Fin n) (Fin n) ℂ}
    (h : IsConsistentlyOrdered A) (hd : IsUnit (diagPart A)) : A.IsConsistentlyOrdered := by
  obtain ⟨c, hlow, hupp⟩ := h
  exact Matrix.isConsistentlyOrdered_of_labelling hd c hlow hupp

/-- **Saad, Proposition 4.15**: for a consistently ordered `A` with nonzero diagonal the eigenvalues
of `B(α) = α L + α⁻¹ U` do not depend on `α ≠ 0`. -/
theorem proposition_4_15 {A : Matrix (Fin n) (Fin n) ℂ} (h : IsConsistentlyOrdered A)
    (hd : IsUnit (diagPart A)) {α : ℂ} (hα : α ≠ 0) :
    spectrum ℂ (α • Matrix.jacobiLower A + α⁻¹ • Matrix.jacobiUpper A) =
      spectrum ℂ (Matrix.jacobiSplitting A hd).iterationOperator := by
  have hCO := IsConsistentlyOrdered.matrix_isConsistentlyOrdered h hd
  rw [← Matrix.jacobiLower_add_jacobiUpper A hd]
  exact hCO α hα

/-- **Saad, Proposition 4.14**: a consistently ordered matrix is brought to a T-matrix by the
*stable* sort of the indices by their label, and that permutation commutes with taking the strict
triangular parts: `(PᵀAP)_L = Pᵀ A_L P` and `(PᵀAP)_U = Pᵀ A_U P`.

The sort is `Tuple.sort`, which is stable; the two commutation identities hold because an entry that
the sort would move across the diagonal joins two blocks in the wrong order, which the monotonicity
of the sorted labelling forbids. -/
theorem proposition_4_14 {A : Matrix (Fin n) (Fin n) ℂ} (h : IsConsistentlyOrdered A) :
    ∃ σ : Equiv.Perm (Fin n), IsTMatrix (A.submatrix σ σ) ∧
      strictLower (A.submatrix σ σ) = (strictLower A).submatrix σ σ ∧
        strictUpper (A.submatrix σ σ) = (strictUpper A).submatrix σ σ := by
  obtain ⟨c, hlow, hupp⟩ := h
  refine ⟨Tuple.sort c, ⟨c ∘ Tuple.sort c, Tuple.monotone_sort c, fun i j hij hA => ?_⟩, ?_, ?_⟩
  · have hne : Tuple.sort c i ≠ Tuple.sort c j := fun hc => hij ((Tuple.sort c).injective hc)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inr (hupp _ _ hlt hA)
    · exact Or.inl (hlow _ _ hgt hA)
  · ext i j
    have hmono := Tuple.monotone_sort c
    rcases lt_trichotomy j i with hji | rfl | hij
    · by_cases hσ : Tuple.sort c j < Tuple.sort c i
      · simp [hji, hσ]
      · have hne : Tuple.sort c i ≠ Tuple.sort c j :=
          fun hc => absurd ((Tuple.sort c).injective hc) hji.ne'
        have hlt : Tuple.sort c i < Tuple.sort c j := lt_of_le_of_ne (not_lt.mp hσ) hne
        have hz : A (Tuple.sort c i) (Tuple.sort c j) = 0 := by
          by_contra hA
          have h1 := hupp _ _ hlt hA
          have h2 : (c ∘ Tuple.sort c) j ≤ (c ∘ Tuple.sort c) i := hmono hji.le
          simp only [Function.comp_apply] at h2
          omega
        simp [hji, hσ, hz]
    · simp
    · by_cases hσ : Tuple.sort c j < Tuple.sort c i
      · have hz : A (Tuple.sort c i) (Tuple.sort c j) = 0 := by
          by_contra hA
          have h1 := hlow _ _ hσ hA
          have h2 : (c ∘ Tuple.sort c) i ≤ (c ∘ Tuple.sort c) j := hmono hij.le
          simp only [Function.comp_apply] at h2
          omega
        simp [asymm hij, hσ, hz]
      · simp [asymm hij, hσ]
  · ext i j
    have hmono := Tuple.monotone_sort c
    rcases lt_trichotomy i j with hij | rfl | hji
    · by_cases hσ : Tuple.sort c i < Tuple.sort c j
      · simp [hij, hσ]
      · have hne : Tuple.sort c j ≠ Tuple.sort c i :=
          fun hc => absurd ((Tuple.sort c).injective hc) hij.ne'
        have hlt : Tuple.sort c j < Tuple.sort c i := lt_of_le_of_ne (not_lt.mp hσ) hne
        have hz : A (Tuple.sort c i) (Tuple.sort c j) = 0 := by
          by_contra hA
          have h1 := hlow _ _ hlt hA
          have h2 : (c ∘ Tuple.sort c) i ≤ (c ∘ Tuple.sort c) j := hmono hij.le
          simp only [Function.comp_apply] at h2
          omega
        simp [hij, hσ, hz]
    · simp
    · by_cases hσ : Tuple.sort c i < Tuple.sort c j
      · have hz : A (Tuple.sort c i) (Tuple.sort c j) = 0 := by
          by_contra hA
          have h1 := hupp _ _ hσ hA
          have h2 : (c ∘ Tuple.sort c) j ≤ (c ∘ Tuple.sort c) i := hmono hji.le
          simp only [Function.comp_apply] at h2
          omega
        simp [asymm hji, hσ, hz]
      · simp [asymm hji, hσ]

/-! #### Theorem 4.16 and the optimal relaxation parameter (4.47) -/

variable {A : Matrix (Fin n) (Fin n) ℂ}

/-- **Saad, Theorem 4.16** (⇒): if `λ ≠ 0` is an eigenvalue of the SOR iteration matrix and `(λ + ω
- 1)² = λ ω² μ²`, then `μ` is an eigenvalue of the Jacobi iteration matrix. -/
theorem theorem_4_16_mp (h : IsConsistentlyOrdered A) (hd : IsUnit (diagPart A)) {ω : ℂ}
    (hω : ω ≠ 0) {l μ : ℂ} (hl : l ≠ 0) (hrel : (l + ω - 1) ^ 2 = l * ω ^ 2 * μ ^ 2)
    (hlG : l ∈ spectrum ℂ (Matrix.sorSplitting A hd hω).iterationOperator) :
    μ ∈ spectrum ℂ (Matrix.jacobiSplitting A hd).iterationOperator :=
  ((IsConsistentlyOrdered.matrix_isConsistentlyOrdered h hd).mem_spectrum_jacobi_iff_sor hd hω hl
    hrel).mpr hlG

/-- **Saad, Theorem 4.16** (⇐): if `μ` is an eigenvalue of the Jacobi iteration matrix and `λ ≠ 0`
satisfies `(λ + ω - 1)² = λ ω² μ²`, then `λ` is an eigenvalue of the SOR iteration matrix. -/
theorem theorem_4_16_mpr (h : IsConsistentlyOrdered A) (hd : IsUnit (diagPart A)) {ω : ℂ}
    (hω : ω ≠ 0) {l μ : ℂ} (hl : l ≠ 0) (hrel : (l + ω - 1) ^ 2 = l * ω ^ 2 * μ ^ 2)
    (hμB : μ ∈ spectrum ℂ (Matrix.jacobiSplitting A hd).iterationOperator) :
    l ∈ spectrum ℂ (Matrix.sorSplitting A hd hω).iterationOperator :=
  ((IsConsistentlyOrdered.matrix_isConsistentlyOrdered h hd).mem_spectrum_jacobi_iff_sor hd hω hl
    hrel).mp hμB

/-- **Saad (4.47)**: for a consistently ordered `A` whose Jacobi iteration matrix has real
eigenvalues and spectral radius `ρ(B) < 1`, the relaxation parameter `ω_opt = 2/(1 + √(1 - ρ(B)²))`
minimizes the SOR spectral radius over `0 < ω < 2`, and the value there is `ω_opt - 1`. -/
theorem equation_4_47 [NeZero n] (h : IsConsistentlyOrdered A) (hd : IsUnit (diagPart A))
    (hreal : ∀ μ ∈ spectrum ℂ (Matrix.jacobiSplitting A hd).iterationOperator, μ.im = 0)
    (hlt : spectralRadius ℂ (Matrix.jacobiSplitting A hd).iterationOperator < 1) :
    IsMinOn (fun ω : ℝ => spectralRadius ℂ (Matrix.sorIterationMatrix A (ω : ℂ)))
        (Set.Ioo 0 2)
        (2 / (1 + Real.sqrt (1 -
          (spectralRadius ℂ (Matrix.jacobiSplitting A hd).iterationOperator).toReal ^ 2))) ∧
      spectralRadius ℂ (Matrix.sorIterationMatrix A
          ((2 / (1 + Real.sqrt (1 -
            (spectralRadius ℂ (Matrix.jacobiSplitting A hd).iterationOperator).toReal ^ 2))
            : ℝ) : ℂ)) =
        ENNReal.ofReal (2 / (1 + Real.sqrt (1 -
          (spectralRadius ℂ (Matrix.jacobiSplitting A hd).iterationOperator).toReal ^ 2)) - 1) := by
  have hCO := IsConsistentlyOrdered.matrix_isConsistentlyOrdered h hd
  exact ⟨hCO.isMinOn_complexSpectralRadius_sor hd hreal hlt,
    hCO.spectralRadius_sor_optimalRelaxation hd hreal hlt⟩

end Young

end SaadSparse.Chapter04
