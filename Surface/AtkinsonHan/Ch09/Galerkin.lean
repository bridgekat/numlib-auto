import AtkinsonHan.Ch08.LaxMilgram

/-!
# The Galerkin method (§9.1)

Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009.

The Galerkin problem (9.1.4) `u_N ∈ V_N`, `a(u_N, v) = ℓ(v) ∀ v ∈ V_N`, its stiffness matrix and
load vector (9.1.5), the Ritz formulation (9.1.6)–(9.1.8), Céa's inequality (Proposition 9.1.3,
estimates (9.1.11)–(9.1.12)) with its symmetric sharpening, and the convergence corollary
(Corollary 9.1.4, (9.1.13)–(9.1.14)).  Everything is the backbone's `IsGalerkinSolution` theory
read through the definitional bridge `galerkinProblem_iff`.
-/

open Filter Topology
open scoped InnerProductSpace

namespace AtkinsonHan

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Galerkin problem (9.1.4): `u_N ∈ V_N` with `a(u_N, v) = ℓ(v)` for all `v ∈ V_N`. -/
def GalerkinProblem (a : BilinForm V) (ℓ : StrongDual ℝ V) (VN : Submodule ℝ V) (uN : V) : Prop :=
  uN ∈ VN ∧ ∀ v ∈ VN, a uN v = ℓ v

/-- The stiffness matrix `A = (a(φ_j, φ_i))` of (9.1.5). -/
def stiffnessMatrix (a : BilinForm V) {N : ℕ} (φ : Fin N → V) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => a (φ j) (φ i)

/-- The load vector `b = (ℓ(φ_i))` of (9.1.5). -/
def loadVector (ℓ : StrongDual ℝ V) {N : ℕ} (φ : Fin N → V) : Fin N → ℝ := fun i => ℓ (φ i)

namespace Ch09

variable {a : BilinForm V} {M α c₀ : ℝ} {ℓ : StrongDual ℝ V} {VN : Submodule ℝ V} {u uN : V}

/-- The Galerkin problem is the backbone's `IsGalerkinSolution` for the bundled form. -/
theorem galerkinProblem_iff (hM : a.IsBoundedWith M) :
    GalerkinProblem a ℓ VN uN ↔ IsGalerkinSolution (a.toCLM hM) ℓ VN uN := Iff.rfl

/-! ### Well-posedness -/

/-- (9.1.1): under (9.1.2) and (9.1.3) the continuous problem has a unique solution; this is
Lax–Milgram. -/
theorem existsUnique_solution [CompleteSpace V] (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀)
    (ha : a.IsEllipticWith c₀) (ℓ : StrongDual ℝ V) : ∃! u, ∀ v, a u v = ℓ v :=
  Ch08.thm_8_3_4 hM hc₀ ha ℓ

/-- (9.1.4) is uniquely solvable on any finite-dimensional subspace `V_N`: the form restricted to
`V_N` is still bounded and `V_N`-elliptic with the same constants, so Lax–Milgram applies there.
No completeness of `V` is needed, since `V_N` is finite-dimensional. -/
theorem existsUnique_galerkinProblem (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀)
    (ha : a.IsEllipticWith c₀) (ℓ : StrongDual ℝ V) (VN : Submodule ℝ V)
    [FiniteDimensional ℝ VN] : ∃! uN, GalerkinProblem a ℓ VN uN :=
  IsGalerkinSolution.existsUnique (a := a.toCLM hM) (ℓ := ℓ) (K := VN) hc₀ ha

/-! ### The linear system (9.1.5) -/

/-- (9.1.5): with respect to a basis `{φ_i}` of `V_N`, the Galerkin problem for
`u_N = ∑ ξ_j φ_j` is the linear system `A ξ = b` with `A` the stiffness matrix and `b` the load
vector. -/
theorem galerkinProblem_iff_mulVec (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V)
    (VN : Submodule ℝ V) {N : ℕ} (φ : Module.Basis (Fin N) ℝ VN) (ξ : Fin N → ℝ) :
    GalerkinProblem a ℓ VN (∑ j, ξ j • (φ j : V)) ↔
      (stiffnessMatrix a fun i => (φ i : V)).mulVec ξ = loadVector ℓ fun i => (φ i : V) := by
  have hstar : star ξ = ξ := funext fun i => star_trivial (ξ i)
  rw [galerkinProblem_iff hM, IsGalerkinSolution.iff_mulVec φ ξ, hstar]
  rfl

/-! ### Exercise 9.1.2: symmetry and positive definiteness of the stiffness matrix -/

theorem stiffnessMatrix_apply (a : BilinForm V) {N : ℕ} (φ : Fin N → V) (i j : Fin N) :
    stiffnessMatrix a φ i j = a (φ j) (φ i) := rfl

/-- Exercise 9.1.2: a symmetric form has a symmetric stiffness matrix. -/
theorem stiffnessMatrix_isSymm (hs : LinearMap.BilinForm.IsSymm a) {N : ℕ} (φ : Fin N → V) :
    (stiffnessMatrix a φ).IsSymm := by
  ext i j
  exact BilinForm.isSymm_iff.mp hs (φ i) (φ j)

theorem stiffnessMatrix_isHermitian (hs : LinearMap.BilinForm.IsSymm a) {N : ℕ} (φ : Fin N → V) :
    (stiffnessMatrix a φ).IsHermitian := by
  ext i j
  exact BilinForm.isSymm_iff.mp hs (φ i) (φ j)

/-- The quadratic form of the stiffness matrix is the form evaluated at the corresponding
elements of `V_N`. -/
theorem dotProduct_stiffnessMatrix_mulVec (a : BilinForm V) {N : ℕ} (φ : Fin N → V)
    (ξ η : Fin N → ℝ) :
    η ⬝ᵥ (stiffnessMatrix a φ).mulVec ξ = a (∑ j, ξ j • φ j) (∑ i, η i • φ i) := by
  have hL : η ⬝ᵥ (stiffnessMatrix a φ).mulVec ξ
      = ∑ i, ∑ j, η i * ξ j * a (φ j) (φ i) := by
    simp only [dotProduct, Matrix.mulVec, stiffnessMatrix, Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hR : a (∑ j, ξ j • φ j) (∑ i, η i • φ i)
      = ∑ i, ∑ j, η i * ξ j * a (φ j) (φ i) := by
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hL, hR]

/-- Exercise 9.1.2: a `V`-elliptic form has a positive definite stiffness matrix, in the sense
that `ξᵀ A ξ > 0` for `ξ ≠ 0`.  Symmetry is not needed for this half. -/
theorem stiffnessMatrix_dotProduct_pos (hα : 0 < α) (ha : a.IsEllipticWith α) {N : ℕ}
    {φ : Fin N → V} (hφ : LinearIndependent ℝ φ) {ξ : Fin N → ℝ} (hξ : ξ ≠ 0) :
    0 < ξ ⬝ᵥ (stiffnessMatrix a φ).mulVec ξ := by
  rw [dotProduct_stiffnessMatrix_mulVec]
  have hne : (∑ j, ξ j • φ j) ≠ 0 := fun h =>
    hξ (funext fun i => Fintype.linearIndependent_iff.mp hφ ξ h i)
  have hnorm : 0 < ‖(∑ j, ξ j • φ j : V)‖ := norm_pos_iff.mpr hne
  exact lt_of_lt_of_le (mul_pos hα (pow_pos hnorm 2)) (ha _)

/-- Exercise 9.1.2, in Mathlib's bundled form: for a symmetric `V`-elliptic form the stiffness
matrix is positive definite. -/
theorem stiffnessMatrix_posDef (hs : LinearMap.BilinForm.IsSymm a) (hα : 0 < α)
    (ha : a.IsEllipticWith α) {N : ℕ} {φ : Fin N → V} (hφ : LinearIndependent ℝ φ) :
    (stiffnessMatrix a φ).PosDef :=
  Matrix.PosDef.of_dotProduct_mulVec_pos (stiffnessMatrix_isHermitian hs φ) fun _ hx => by
    rw [show star _ = _ from funext fun i => star_trivial _]
    exact stiffnessMatrix_dotProduct_pos hα ha hφ hx

/-! ### The Ritz formulation (9.1.6)–(9.1.8) and Exercise 9.1.1 -/

/-- (9.1.8), and Exercise 9.1.1: for a symmetric `V`-elliptic form the Galerkin problem (9.1.4) is
equivalent to minimizing the energy (9.1.7) over `V_N`; taking `V_N = ⊤` gives (9.1.6). -/
theorem galerkinProblem_iff_isMinOn [CompleteSpace V] (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀)
    (ha : a.IsEllipticWith c₀) (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V)
    (VN : Submodule ℝ V) (uN : V) :
    GalerkinProblem a ℓ VN uN ↔ uN ∈ VN ∧ IsMinOn (a.energy ℓ) (VN : Set V) uN := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (Ch08.thm_8_3_3_subspace hM hc₀ ha hs ℓ VN h1).mpr h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (Ch08.thm_8_3_3_subspace hM hc₀ ha hs ℓ VN h1).mp h2⟩

/-! ### Céa's inequality (Proposition 9.1.3) -/

/-- (9.1.12), Galerkin orthogonality: the error is `a`-orthogonal to the trial space. -/
theorem galerkin_orthogonality (hM : a.IsBoundedWith M) (hu : ∀ v, a u v = ℓ v)
    (huN : GalerkinProblem a ℓ VN uN) {v : V} (hv : v ∈ VN) : a (u - uN) v = 0 :=
  IsGalerkinSolution.apply_sub_eq_zero (a := a.toCLM hM) huN hu hv

/-- Céa's inequality (9.1.11), pointwise form: `‖u − u_N‖ ≤ (M/c₀) ‖u − v‖` for every
`v ∈ V_N`. -/
theorem prop_9_1_3_le (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀)
    (hu : ∀ v, a u v = ℓ v) (huN : GalerkinProblem a ℓ VN uN) {v : V} (hv : v ∈ VN) :
    ‖u - uN‖ ≤ M / c₀ * ‖u - v‖ :=
  IsGalerkinSolution.norm_sub_le hc₀ (BilinForm.isBoundedWith_toCLM hM) ha huN hu hv

private theorem iInf_norm_sub_eq_infDist (u : V) (K : Submodule ℝ V) :
    (⨅ v : K, ‖u - (v : V)‖) = Metric.infDist u (K : Set V) := by
  simp [Metric.infDist_eq_iInf, dist_eq_norm]

/-- Proposition 9.1.3, Céa's inequality (9.1.11): the Galerkin error is quasi-optimal, with the
constant `c = M/c₀`.  Neither finite-dimensionality of `V_N` nor completeness of `V` is used. -/
theorem prop_9_1_3 (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀)
    (hu : ∀ v, a u v = ℓ v) (huN : GalerkinProblem a ℓ VN uN) :
    ‖u - uN‖ ≤ M / c₀ * ⨅ v : VN, ‖u - (v : V)‖ := by
  rw [iInf_norm_sub_eq_infDist]
  exact IsGalerkinSolution.norm_sub_le_infDist hc₀ (BilinForm.isBoundedWith_toCLM hM) ha huN hu

/-! ### The symmetric case: best approximation in the energy norm -/

/-- The remark after Proposition 9.1.3: in the symmetric `V`-elliptic case `u_N` is the best
approximation to `u` from `V_N` in the energy norm, i.e. the `a`-orthogonal projection. -/
theorem energyNorm_sub_le (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀)
    (hs : LinearMap.BilinForm.IsSymm a) (hu : ∀ v, a u v = ℓ v)
    (huN : GalerkinProblem a ℓ VN uN) {v : V} (hv : v ∈ VN) :
    a.energyNorm (u - uN) ≤ a.energyNorm (u - v) :=
  IsGalerkinSolution.energyNorm_sub_le ((BilinForm.isSymm_iff_isHermitian hM).mp hs)
    (SesqForm.IsCoerciveWith.mono (a.toCLM hM) ha hc₀.le) huN hu hv

/-- The same statement with the infimum: `‖u − u_N‖_a = inf_{v ∈ V_N} ‖u − v‖_a`. -/
theorem energyNorm_sub_eq_iInf (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀)
    (ha : a.IsEllipticWith c₀) (hs : LinearMap.BilinForm.IsSymm a) (hu : ∀ v, a u v = ℓ v)
    (huN : GalerkinProblem a ℓ VN uN) :
    a.energyNorm (u - uN) = ⨅ v : VN, a.energyNorm (u - (v : V)) := by
  have hbdd : BddBelow (Set.range fun v : VN => a.energyNorm (u - (v : V))) :=
    ⟨0, Set.forall_mem_range.2 fun v => BilinForm.energyNorm_nonneg a _⟩
  have : Nonempty VN := ⟨⟨uN, huN.1⟩⟩
  refine le_antisymm (le_ciInf fun v => energyNorm_sub_le hM hc₀ ha hs hu huN v.2) ?_
  exact ciInf_le hbdd ⟨uN, huN.1⟩

/-- The symmetric sharpening of Céa's inequality: the constant improves from `M/c₀` to
`√(M/c₀)`. -/
theorem prop_9_1_3_sqrt (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀)
    (hs : LinearMap.BilinForm.IsSymm a) (hu : ∀ v, a u v = ℓ v)
    (huN : GalerkinProblem a ℓ VN uN) {v : V} (hv : v ∈ VN) :
    ‖u - uN‖ ≤ Real.sqrt (M / c₀) * ‖u - v‖ :=
  IsGalerkinSolution.norm_sub_le_sqrt hc₀ (BilinForm.isBoundedWith_toCLM hM) ha
    ((BilinForm.isSymm_iff_isHermitian hM).mp hs) huN hu hv

/-! ### Corollary 9.1.4 -/

/-- Corollary 9.1.4, (9.1.13)–(9.1.14): if the trial spaces increase and their union is dense,
the Galerkin solutions converge to the exact solution. -/
theorem cor_9_1_4 (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀)
    (ℓ : StrongDual ℝ V) (VN : ℕ → Submodule ℝ V) (hmono : Monotone VN)
    (hdense : Dense (⋃ n, (VN n : Set V))) (hu : ∀ v, a u v = ℓ v) (uN : ℕ → V)
    (huN : ∀ n, GalerkinProblem a ℓ (VN n) (uN n)) :
    Tendsto (fun n => ‖u - uN n‖) atTop (𝓝 0) := by
  have h := IsGalerkinSolution.tendsto (a := a.toCLM hM) (ℓ := ℓ) hc₀
    (BilinForm.isBoundedWith_toCLM hM) ha hmono hdense huN hu
  rw [tendsto_iff_norm_sub_tendsto_zero] at h
  simpa only [norm_sub_rev] using h

end Ch09

end AtkinsonHan
