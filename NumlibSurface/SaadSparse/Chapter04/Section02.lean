import Numlib.Eigen.Perturbation
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearSolve.Stationary.DiagDominant
import Numlib.LinearSolve.Stationary.Splitting
import NumlibSurface.SaadSparse.Chapter01.Section13
import NumlibSurface.SaadSparse.Chapter04.Section01

/-!
# §4.2 Convergence of the basic iterative methods

Section 4.2 of Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003, in three parts.

**§4.2–§4.2.2, the affine iteration** `x_{k+1} = G x_k + f` (4.28)–(4.30): Theorem 4.1 (`ρ(G) < 1`
characterizes convergence), Corollary 4.2 (`‖G‖ < 1` suffices), the remark `|λ| ≤ ‖A‖` before
Theorem 4.6, and Example 4.1 (Richardson). The proofs specialize the backbone's spectral-radius
theory (`Numlib/LinearAlgebra/Matrix/Complexify.lean`,
`Numlib/Analysis/Normed/Algebra/SpectralRadius.lean`, `Numlib/LinearSolve/Stationary/Basic.lean`)
to real matrices acting on `Fin n → ℝ`.

**§4.2.3, diagonally dominant matrices**: Gershgorin's theorem (Theorem 4.6) in its row and column
forms, the nonsingularity of strictly diagonally dominant matrices (Corollary 4.8), and the
convergence of the Jacobi and Gauss–Seidel iterations for such matrices (Theorem 4.9). Saad's
Definition 4.5 as printed uses column sums for all three dominance conditions, while the proofs of
Theorems 4.6 and 4.9 use row sums; both forms are stated here, following the backbone's
`Matrix.IsStrictDiagDominant` (rows) and `Matrix.IsStrictColDiagDominant` (columns).

**§4.2.4–§4.2.5, symmetric positive definite matrices and Young's theory**: only Proposition 4.12
is proved, by the similarity argument the book uses — for a block anti-diagonal `B` the spectrum
is symmetric under negation, and the spectrum of `B(α) = α L + α⁻¹ U` does not depend on `α ≠ 0`.

Left open here (each waits on a phase-2 backbone item, see `tracker/backbone.md` §7 and
`tracker/saadsparse-ch1-4-5.md` §3):

* §4.2.1 the convergence factors and rates: the Gelfand limit `‖G^k‖^{1/k} → ρ(G)` for a *real*
  matrix needs `‖complexify A‖ = ‖A‖` for the scoped operator norms (§3 item 1); the "specific"
  factor for a generic `d₀` uses the Jordan form and is left out of the plan altogether.
* Theorem 4.4 on regular splittings and M-matrices (§3 item 3).
* Theorem 4.7 and the *irreducibly* diagonally dominant halves of Corollary 4.8 and Theorem 4.9,
  which need Saad's irreducibility (`Matrix.IsIrreducible (A.map ‖·‖)`) and the path argument along
  the adjacency graph; and Gauss–Seidel under strict *column* dominance (§3 item 4).
* Theorem 4.10 (SOR converges for `0 < ω < 2` iff `A` is positive definite), which needs the
  Householder–John / Ostrowski–Reich criterion and its converse; Definitions 4.11 and 4.13
  (Property A, consistent ordering, T-matrices) with Propositions 4.14–4.15; Theorem 4.16 (the
  relation `(λ + ω - 1)² = λ ω² μ²` between the SOR and Jacobi spectra), the optimal parameter
  (4.47), and the spectral analysis of Example 4.1 (§3 item 5).
-/

open Matrix

namespace SaadSparse.Ch04

/-! ### §4.2–§4.2.2 The affine iteration and its convergence -/

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

/-- Saad, Theorem 4.1 (⇒): `ρ(G) < 1` implies that `I - G` is nonsingular and that (4.28)
converges to `(I - G)⁻¹ f` for every `f` and every `x₀`. -/
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

/-- Saad, Theorem 4.1: the iteration (4.28) converges for every `f` and every `x₀` iff
`ρ(G) < 1`. -/
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

/-- Saad, Corollary 4.2, for the norm `‖·‖_p` induced by a vector `p`-norm: `‖G‖_p < 1` forces
`ρ(G) < 1`. -/
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

/-- Saad, Example 4.1: Richardson's iteration converges for every `b` and `x₀` iff
`ρ(I - α A) < 1`. -/
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

/-! ### Theorem 4.6 (Gershgorin) -/

/-- Saad, Theorem 4.6 (rows): every eigenvalue lies in one of the discs
`|λ - a_ii| ≤ ∑_{j ≠ i} |a_ij|`. -/
theorem theorem_4_6 (A : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    ∃ i, ‖μ - A i i‖ ≤ ∑ j ∈ univ.erase i, ‖A i j‖ := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (spectrum_subset_iUnion_closedBall A hμ)
  exact ⟨i, by simpa [Metric.mem_closedBall, dist_eq_norm] using hi⟩

/-- Transposing does not change the spectrum. -/
theorem spectrum_transpose (A : Matrix (Fin n) (Fin n) ℂ) : spectrum ℂ Aᵀ = spectrum ℂ A := by
  ext μ
  have hT : (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) μ - A)ᵀ
      = algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) μ - Aᵀ := by
    rw [transpose_sub]
    congr 1
    simp [Algebra.algebraMap_eq_smul_one]
  simp only [spectrum.mem_iff, ← hT, isUnit_iff_isUnit_det, det_transpose]

/-- Saad, Theorem 4.6 (columns): the same statement for the column sums, obtained by
transposing. -/
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

/-! ### §4.2.4–§4.2.5 Symmetric positive definite matrices and Young's theory -/

section SymmetricPositiveDefinite

/-- The index type of a two-block partition. -/
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

/-- Saad, Proposition 4.12 (2): the eigenvalues of `B(α) = α L + α⁻¹ U` do not depend on
`α ≠ 0`. -/
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

end SaadSparse.Ch04
