import Numlib.Surface.SaadSparse.Ch01.LinearSystems
import Numlib.Surface.SaadSparse.Ch04.Splittings

/-!
# §4.2 Convergence of the basic iterative methods

Section 4.2 of Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003: the general theory of the affine iteration `x_{k+1} = G x_k + f` (4.28)–(4.30),
Theorem 4.1 (`ρ(G) < 1` characterizes convergence), Corollary 4.2 (`‖G‖ < 1` suffices), the
remark `|λ| ≤ ‖A‖` before Theorem 4.6, and Example 4.1 (Richardson).

The proofs specialize the backbone's spectral-radius theory
(`Numlib/LinearAlgebra/Matrix/Complexify.lean`,
`Numlib/Analysis/Normed/Algebra/SpectralRadius.lean`,
`Numlib/LinearSolve/Stationary/Basic.lean`) to real matrices acting on `Fin n → ℝ`.

Left open here (each waits on a phase-2 backbone item, see `tracker/backbone.md` §7 and
`tracker/saadsparse-ch1-4-5.md` §3):

* §4.2.1 the convergence factors and rates: the Gelfand limit `‖G^k‖^{1/k} → ρ(G)` for a *real*
  matrix needs `‖complexify A‖ = ‖A‖` for the scoped operator norms (§3 item 1); the "specific"
  factor for a generic `d₀` uses the Jordan form and is left out of the plan altogether.
* Theorem 4.4 on regular splittings and M-matrices (§3 item 3).
* The spectral analysis of Example 4.1 (optimal `α`) and Theorems 4.10, 4.16, (4.47) (§3 item 5).
-/

open Matrix Filter Topology Stationary
open scoped SaadSparse ENNReal

namespace SaadSparse.Ch04

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
theorem thm_4_1_mp (hG : complexSpectralRadius G < 1) :
    IsUnit (1 - G) ∧ ∀ f x₀ : Fin n → ℝ,
      Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 ((1 - G)⁻¹ *ᵥ f)) := by
  have hu := isUnit_one_sub_of_complexSpectralRadius_lt_one hG
  refine ⟨hu, fun f x₀ => tendsto_affineStep_of_complexSpectralRadius_lt_one hG f x₀ ?_⟩
  rw [affineStep_fixed_iff]
  exact mulVec_inv_mulVec hu f

/-- Saad, Theorem 4.1 (⇐): if (4.28) converges for every `f` and every `x₀` then `ρ(G) < 1`. -/
theorem thm_4_1_mpr (h : ∀ f x₀ : Fin n → ℝ,
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
theorem thm_4_1 (G : Matrix (Fin n) (Fin n) ℝ) :
    (∀ f x₀ : Fin n → ℝ, ∃ x, Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 x)) ↔
      complexSpectralRadius G < 1 :=
  ⟨thm_4_1_mpr, fun hG f x₀ => ⟨_, (thm_4_1_mp hG).2 f x₀⟩⟩

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
theorem cor_4_2_lp {G : Matrix (Fin n) (Fin n) ℝ} (hG : lpOpNorm p G < 1) :
    IsUnit (1 - G) ∧ ∀ f x₀ : Fin n → ℝ,
      Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 ((1 - G)⁻¹ *ᵥ f)) :=
  thm_4_1_mp (complexSpectralRadius_lt_one_of_lpOpNorm_lt_one p hG)

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
    refine thm_4_1_mpr fun f x₀ => ?_
    obtain ⟨x, hx⟩ := h (α⁻¹ • f) x₀
    refine ⟨x, ?_⟩
    rw [richardsonStep_eq_affine, smul_smul, mul_inv_cancel₀ hα, one_smul] at hx
    exact hx
  · intro hG b x₀
    rw [richardsonStep_eq_affine]
    exact ⟨_, (thm_4_1_mp hG).2 (α • b) x₀⟩

end SaadSparse.Ch04
