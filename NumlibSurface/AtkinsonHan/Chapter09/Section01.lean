import Mathlib.NumberTheory.ZetaValues
import Numlib.Analysis.Fourier.CosineBasis
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Analysis.InnerProductSpace.WeakCompactness
import Numlib.Projection.Basic
import Numlib.Projection.Optimality
import Numlib.Variational.Forms
import Numlib.Variational.EllipticInterval
import Numlib.Variational.Galerkin
import NumlibSurface.AtkinsonHan.Chapter08.Section03

/-!
# Atkinson–Han §9.1: the Galerkin method

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §9.1.

The Galerkin problem (9.1.4) `u_N ∈ V_N`, `a(u_N, v) = ℓ(v) ∀ v ∈ V_N`, its stiffness matrix and
load vector (9.1.5), the Ritz formulation (9.1.6)–(9.1.8), Céa's inequality (Proposition 9.1.3,
estimates (9.1.11)–(9.1.12)) with its symmetric sharpening, and the convergence corollary
(Corollary 9.1.4, (9.1.13)–(9.1.14)).  All of that is the backbone's `IsGalerkinSolution` theory
read through the definitional bridge `galerkinProblem_iff`.

Example 9.1.1 is the concrete instance: `-u'' = f` on `(0, 1)` with `u(0) = u(1) = 0`, weakly
posed on `H¹₀(0, 1)` — the backbone's `SobolevIntervalZero 0 1` of
`Numlib/Analysis/Sobolev/Interval.lean` — with the polynomial trial space
`V_N = span{x^i(1 - x) : 1 ≤ i ≤ N}`, whose stiffness matrix entries the example displays. The
bilinear form, its boundedness and its coercivity on `H¹₀(0, 1)` are the backbone's
`EllipticInterval.form` and `EllipticInterval.form_isCoerciveWith_restrict`. Example 9.1.2 is the
same problem with the trigonometric trial space `span{sin(iπx) : 1 ≤ i ≤ N}`, which is orthogonal
for the energy inner product, so the Galerkin system is diagonal and the Galerkin solution is the
kernel approximation (9.1.10).

Exercise 9.1.3, the Fourier expansion of the Green kernel of Example 9.1.2, and Exercise 9.1.4,
which turns the Galerkin method into a second proof that (9.1.1) is solvable, close the section.
The latter is deliberately independent of `AtkinsonHan.Chapter08.theorem_8_3_4`, so that
`existsUnique_solution_of_galerkin` is a genuine second proof of Lax–Milgram and not a corollary of
the first one.
-/

open Filter Topology
open scoped InnerProductSpace Real

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

namespace Chapter09

variable {a : BilinForm V} {M α c₀ : ℝ} {ℓ : StrongDual ℝ V} {VN : Submodule ℝ V} {u uN : V}

/-- The Galerkin problem is the backbone's `IsGalerkinSolution` for the bundled form. -/
theorem galerkinProblem_iff (hM : a.IsBoundedWith M) :
    GalerkinProblem a ℓ VN uN ↔ IsGalerkinSolution (a.toCLM hM) ℓ VN uN := Iff.rfl

/-! ### Well-posedness

That (9.1.1) itself is uniquely solvable under (9.1.2) and (9.1.3) is Lax–Milgram,
`Chapter08.theorem_8_3_4`, and is not restated here. -/

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

/-- The entries of the stiffness matrix, `A_{ij} = a(φ_j, φ_i)`. -/
theorem stiffnessMatrix_apply (a : BilinForm V) {N : ℕ} (φ : Fin N → V) (i j : Fin N) :
    stiffnessMatrix a φ i j = a (φ j) (φ i) := rfl

/-- Exercise 9.1.2: a symmetric form has a symmetric stiffness matrix. -/
theorem stiffnessMatrix_isSymm (hs : LinearMap.BilinForm.IsSymm a) {N : ℕ} (φ : Fin N → V) :
    (stiffnessMatrix a φ).IsSymm := by
  ext i j
  exact BilinForm.isSymm_iff.mp hs (φ i) (φ j)

/-- Exercise 9.1.2 in Mathlib's spelling: over `ℝ` a symmetric matrix is Hermitian. -/
theorem stiffnessMatrix_isHermitian (hs : LinearMap.BilinForm.IsSymm a) {N : ℕ} (φ : Fin N → V) :
    (stiffnessMatrix a φ).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.2 (stiffnessMatrix_isSymm hs φ)

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
    exact ⟨h1, (Chapter08.theorem_8_3_3_subspace hM hc₀ ha hs ℓ VN h1).mpr h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (Chapter08.theorem_8_3_3_subspace hM hc₀ ha hs ℓ VN h1).mp h2⟩

/-! ### Céa's inequality (Proposition 9.1.3) -/

/-- (9.1.12), Galerkin orthogonality: the error is `a`-orthogonal to the trial space. -/
theorem galerkin_orthogonality (hM : a.IsBoundedWith M) (hu : ∀ v, a u v = ℓ v)
    (huN : GalerkinProblem a ℓ VN uN) {v : V} (hv : v ∈ VN) : a (u - uN) v = 0 :=
  IsGalerkinSolution.apply_sub_eq_zero (a := a.toCLM hM) huN hu hv

/-- Céa's inequality (9.1.11), pointwise form: `‖u − u_N‖ ≤ (M/c₀) ‖u − v‖` for every
`v ∈ V_N`. -/
theorem proposition_9_1_3_le (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀)
    (hu : ∀ v, a u v = ℓ v) (huN : GalerkinProblem a ℓ VN uN) {v : V} (hv : v ∈ VN) :
    ‖u - uN‖ ≤ M / c₀ * ‖u - v‖ :=
  IsGalerkinSolution.norm_sub_le hc₀ (BilinForm.isBoundedWith_toCLM hM) ha huN hu hv

/-- The infimum over a subspace, as the book writes it, is the distance to that subspace: the
bridge between the `inf_{v ∈ V_N}` of (9.1.11) and the `Metric.infDist` the backbone states its
quasi-optimality bounds in.  §10.4 uses it again for (10.4.5). -/
theorem iInf_norm_sub_eq_infDist (u : V) (K : Submodule ℝ V) :
    (⨅ v : K, ‖u - (v : V)‖) = Metric.infDist u (K : Set V) := by
  simp [Metric.infDist_eq_iInf, dist_eq_norm]

/-- Proposition 9.1.3, Céa's inequality (9.1.11): the Galerkin error is quasi-optimal, with the
constant `c = M/c₀`.  Neither finite-dimensionality of `V_N` nor completeness of `V` is used. -/
theorem proposition_9_1_3 (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀)
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

/-- Céa, symmetric case: the Galerkin solution is the `a`-orthogonal projection of the exact
solution onto `V_N`, i.e. the orthogonal projection in the energy space `WithEnergy`.  This is the
statement that makes `energyNorm_sub_eq_iInf` above a best-approximation result.

The operator hypothesis is the backbone's `IsSymmetricCoercive` for `A = toOperator a`; §9.4's
`isSymmetricBoundedBy_toOperator` produces it from boundedness, symmetry and `V`-ellipticity. -/
theorem galerkin_eq_energyProjection [CompleteSpace V] (hM : a.IsBoundedWith M)
    (hA : (BilinForm.toOperator a hM : V →ₗ[ℝ] V).IsSymmetricCoercive) [FiniteDimensional ℝ VN]
    (hu : ∀ v, a u v = ℓ v) (huN : GalerkinProblem a ℓ VN uN) :
    WithEnergy.equiv _ hA uN
      = (WithEnergy.submoduleMap _ hA VN).starProjection (WithEnergy.equiv _ hA u) := by
  have hstar : (BilinForm.toOperator a hM : V →ₗ[ℝ] V) u = SesqForm.rieszRep ℓ :=
    (BilinForm.toOperator_eq_rieszRep_iff hM ℓ u).mpr hu
  have hx : IsGalerkin (BilinForm.toOperator a hM : V →ₗ[ℝ] V) (SesqForm.rieszRep ℓ) 0 VN uN :=
    IsGalerkinSolution.iff_isGalerkin.mp ((galerkinProblem_iff hM).mp huN)
  have herr := IsGalerkin.error_eq_starProjection hA hx hstar
  have hsplit := (WithEnergy.submoduleMap _ hA VN).starProjection_add_starProjection_orthogonal
    (WithEnergy.equiv _ hA u)
  rw [sub_zero] at herr
  have hlin : WithEnergy.equiv _ hA (u - uN)
      = WithEnergy.equiv _ hA u - WithEnergy.equiv _ hA uN := map_sub _ _ _
  rw [hlin] at herr
  rw [eq_sub_of_add_eq hsplit, ← herr]
  abel

/-- The symmetric sharpening of Céa's inequality: the constant improves from `M/c₀` to
`√(M/c₀)`. -/
theorem proposition_9_1_3_sqrt (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀)
    (hs : LinearMap.BilinForm.IsSymm a) (hu : ∀ v, a u v = ℓ v)
    (huN : GalerkinProblem a ℓ VN uN) {v : V} (hv : v ∈ VN) :
    ‖u - uN‖ ≤ Real.sqrt (M / c₀) * ‖u - v‖ :=
  IsGalerkinSolution.norm_sub_le_sqrt hc₀ (BilinForm.isBoundedWith_toCLM hM) ha
    ((BilinForm.isSymm_iff_isHermitian hM).mp hs) huN hu hv

/-! ### Corollary 9.1.4 -/

/-- Corollary 9.1.4, (9.1.13)–(9.1.14): if the trial spaces increase and their union is dense,
the Galerkin solutions converge to the exact solution. -/
theorem corollary_9_1_4 (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀)
    (ℓ : StrongDual ℝ V) (VN : ℕ → Submodule ℝ V) (hmono : Monotone VN)
    (hdense : Dense (⋃ n, (VN n : Set V))) (hu : ∀ v, a u v = ℓ v) (uN : ℕ → V)
    (huN : ∀ n, GalerkinProblem a ℓ (VN n) (uN n)) :
    Tendsto (fun n => ‖u - uN n‖) atTop (𝓝 0) := by
  have h := IsGalerkinSolution.tendsto (a := a.toCLM hM) (ℓ := ℓ) hc₀
    (BilinForm.isBoundedWith_toCLM hM) ha hmono hdense huN hu
  rw [tendsto_iff_norm_sub_tendsto_zero] at h
  simpa only [norm_sub_rev] using h

/-! ### Exercise 9.1.3: the Fourier expansion of the Green kernel -/

/-- The second Bernoulli polynomial over `ℝ`: `B₂(x) = x² − x + 1/6`.  Mathlib returns the sum of
the cosine series in that shape. -/
private theorem bernoulli_two_eval (x : ℝ) :
    (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli 2)).eval x = x ^ 2 - x + 1 / 6 := by
  simp [Polynomial.bernoulli, Finset.sum_range_succ, bernoulli_eq_bernoulli'_of_ne_one]
  ring

/-- The classical cosine series `∑_{n ≥ 1} cos(nθ)/n² = π²/6 − πθ/2 + θ²/4` for `θ ∈ [0, 2π]`,
read off Mathlib's Fourier expansion of the Bernoulli polynomials at `k = 1`.  The sum is taken
over all of `ℕ`, as Mathlib takes it: the `n = 0` term is `cos 0 / 0 = 0`. -/
private theorem hasSum_cos_div_sq {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (2 * π)) :
    HasSum (fun n : ℕ => Real.cos (n * θ) / n ^ 2) (π ^ 2 / 6 - π * θ / 2 + θ ^ 2 / 4) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hx : θ / (2 * π) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hθ.1 (by positivity), (div_le_one (by positivity)).2 hθ.2⟩
  convert hasSum_one_div_nat_pow_mul_cos one_ne_zero hx using 1
  · ext1 n
    have harg : 2 * π * (n : ℝ) * (θ / (2 * π)) = n * θ := by field_simp
    rw [harg]
    norm_num
    ring
  · rw [show (2 * 1 : ℕ) = 2 from rfl, bernoulli_two_eval]
    norm_num [Nat.factorial]
    field_simp
    ring

/-- Exercise 9.1.3 for `x ≤ t`, where `min(x,t) (1 − max(x,t)) = x (1 − t)`.  The product formula
`sin(jπx) sin(jπt) = ½ (cos(jπ(t−x)) − cos(jπ(t+x)))` turns the series into the difference of two
copies of `hasSum_cos_div_sq`, at `θ = π(t−x) ∈ [0, π]` and at `θ = π(t+x) ∈ [0, 2π]`. -/
private theorem hasSum_kernel_aux {x t : ℝ} (hx0 : 0 ≤ x) (hxt : x ≤ t) (ht1 : t ≤ 1) :
    HasSum (fun n : ℕ => 2 / π ^ 2 * (Real.sin (n * π * x) * Real.sin (n * π * t) / n ^ 2))
      (x * (1 - t)) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h1 := hasSum_cos_div_sq (θ := π * (t - x)) ⟨by nlinarith, by nlinarith⟩
  have h2 := hasSum_cos_div_sq (θ := π * (t + x)) ⟨by nlinarith, by nlinarith⟩
  have hfun : ∀ n : ℕ, 2 / π ^ 2 * (Real.sin (n * π * x) * Real.sin (n * π * t) / n ^ 2)
      = 1 / π ^ 2 * (Real.cos ((n : ℝ) * (π * (t - x))) / (n : ℝ) ^ 2
        - Real.cos ((n : ℝ) * (π * (t + x))) / (n : ℝ) ^ 2) := by
    intro n
    have ha : (n : ℝ) * (π * (t - x)) = n * π * t - n * π * x := by ring
    have hb : (n : ℝ) * (π * (t + x)) = n * π * t + n * π * x := by ring
    rw [ha, hb, Real.cos_sub, Real.cos_add]
    ring
  have hval : x * (1 - t) = 1 / π ^ 2 *
      ((π ^ 2 / 6 - π * (π * (t - x)) / 2 + (π * (t - x)) ^ 2 / 4)
        - (π ^ 2 / 6 - π * (π * (t + x)) / 2 + (π * (t + x)) ^ 2 / 4)) := by
    field_simp
    ring
  rw [funext hfun, hval]
  exact (h1.sub h2).mul_left _

/-- Exercise 9.1.3 with the sum taken over all of `ℕ`; the `j = 0` term vanishes.  Both the
summand and `min`/`max` are symmetric in `x` and `t`, so the case `t ≤ x` is `hasSum_kernel_aux`
with the two swapped. -/
private theorem hasSum_kernel {x t : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ => 2 / π ^ 2 * (Real.sin (n * π * x) * Real.sin (n * π * t) / n ^ 2))
      (min x t * (1 - max x t)) := by
  rcases le_total x t with h | h
  · rw [min_eq_left h, max_eq_right h]
    exact hasSum_kernel_aux hx.1 h ht.2
  · rw [min_eq_right h, max_eq_left h]
    have hcomm : ∀ n : ℕ, 2 / π ^ 2 * (Real.sin (n * π * x) * Real.sin (n * π * t) / n ^ 2)
        = 2 / π ^ 2 * (Real.sin (n * π * t) * Real.sin (n * π * x) / n ^ 2) := fun n => by ring
    rw [funext hcomm]
    exact hasSum_kernel_aux ht.1 h hx.2

/-- Exercise 9.1.3: the Green kernel `K(x,t) = min(x,t) (1 − max(x,t))` of `−u'' = f` on `(0,1)`
under `u(0) = u(1) = 0`, the kernel of the solution formula (9.1.15) of Example 9.1.2, has the
expansion

`K(x,t) = (2/π²) ∑_{j ≥ 1} sin(jπx) sin(jπt) / j²`.

The statement is the pointwise one, a `HasSum` at each `x, t ∈ [0,1]`; the series converges
absolutely, being dominated by `1/j²`.  The kernel `K_N` of (9.1.10) is the `N`-th partial sum, so
the Galerkin solution of Example 9.1.2 is what (9.1.15) gives after truncating this series — that
second half of the exercise needs `H¹₀(0,1)` and the weak form of (9.1.9), neither of which the
project has yet, so only the expansion is stated here. -/
theorem exercise_9_1_3 {x t : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun j : ℕ => 2 / π ^ 2 *
        (Real.sin (((j : ℝ) + 1) * π * x) * Real.sin (((j : ℝ) + 1) * π * t) / ((j : ℝ) + 1) ^ 2))
      (min x t * (1 - max x t)) := by
  have h0 : HasSum (fun n : ℕ => 2 / π ^ 2 *
      (Real.sin (n * π * x) * Real.sin (n * π * t) / (n : ℝ) ^ 2))
      (min x t * (1 - max x t) + ∑ i ∈ Finset.range 1, 2 / π ^ 2 *
        (Real.sin (i * π * x) * Real.sin (i * π * t) / (i : ℝ) ^ 2)) := by
    simpa using hasSum_kernel hx ht
  have hshift : ∀ n : ℕ, 2 / π ^ 2 *
      (Real.sin (((n : ℝ) + 1) * π * x) * Real.sin (((n : ℝ) + 1) * π * t) / ((n : ℝ) + 1) ^ 2)
      = 2 / π ^ 2 * (Real.sin ((↑(n + 1) : ℝ) * π * x) * Real.sin ((↑(n + 1) : ℝ) * π * t)
        / (↑(n + 1) : ℝ) ^ 2) := by
    intro n
    push_cast
    ring
  rw [funext hshift]
  exact (hasSum_nat_add_iff 1).2 h0

/-! ### Exercise 9.1.4: the Galerkin method as a second existence proof -/

/-- Exercise 9.1.4(a): zero is the only solution of the Galerkin system for `ℓ = 0`.  Testing the
equation against the solution itself and using `V`-ellipticity is all it takes; nothing here needs
`a` bounded, `V` complete or `V_N` finite-dimensional. -/
theorem eq_zero_of_galerkinProblem_zero (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀)
    (h : GalerkinProblem a (0 : StrongDual ℝ V) VN uN) : uN = 0 := by
  have h0 : a uN uN = 0 := by simpa using h.2 uN h.1
  have hle : c₀ * ‖uN‖ ^ 2 ≤ 0 := h0 ▸ ha uN
  have hsq : ‖uN‖ ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)

/-- Exercise 9.1.4(a): the discrete problem (9.1.4) is uniquely solvable on a finite-dimensional
`V_N`.  This is the book's own argument — the square system is injective by
`eq_zero_of_galerkinProblem_zero`, hence surjective — rather than
`existsUnique_galerkinProblem`, which invokes Lax–Milgram on `V_N`.  It therefore assumes neither
boundedness of `a` nor completeness of `V`, and Exercise 9.1.4 can build on it without becoming a
corollary of the theorem it is meant to reprove. -/
theorem exercise_9_1_4_a (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀) (ℓ : StrongDual ℝ V)
    (VN : Submodule ℝ V) [FiniteDimensional ℝ VN] : ∃! uN, GalerkinProblem a ℓ VN uN := by
  obtain ⟨b, hb⟩ : ∃ b : VN →ₗ[ℝ] Module.Dual ℝ VN, ∀ w v : VN, b w v = a (w : V) (v : V) :=
    ⟨LinearMap.BilinForm.restrict a VN, fun _ _ => rfl⟩
  have hinj : Function.Injective b := by
    refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun z hz => ?_)
    refine Subtype.ext (eq_zero_of_galerkinProblem_zero hc₀ ha ⟨z.2, fun v hv => ?_⟩)
    have := congrArg (fun φ : Module.Dual ℝ VN => φ ⟨v, hv⟩) hz
    simpa [hb] using this
  have hsurj : Function.Surjective b :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      Subspace.dual_finrank_eq.symm).1 hinj
  obtain ⟨z, hz⟩ := hsurj ((ℓ : V →ₗ[ℝ] ℝ).domRestrict VN)
  have hsol : ∀ v ∈ VN, a (z : V) v = ℓ v := by
    intro v hv
    have := congrArg (fun φ : Module.Dual ℝ VN => φ ⟨v, hv⟩) hz
    simpa [hb] using this
  refine ⟨(z : V), ⟨z.2, hsol⟩, fun y hy => ?_⟩
  refine sub_eq_zero.mp (eq_zero_of_galerkinProblem_zero hc₀ ha
    ⟨VN.sub_mem hy.1 z.2, fun v hv => ?_⟩)
  simp [map_sub, LinearMap.sub_apply, hy.2 v hv, hsol v hv]

/-- Exercise 9.1.4, steps (b)–(e): under the hypotheses of Corollary 9.1.4 the Galerkin solutions
`u_n` themselves produce a solution of (9.1.1).  (b) `V`-ellipticity bounds `‖u_n‖` by `‖ℓ‖/c₀`, so
some subsequence converges weakly to a `u ∈ V`; (c) for fixed `N` the relation `a(u_n, v) = ℓ(v)`
holds for every `v ∈ V_N` once `n ≥ N`, and passing to the weak limit gives `a(u, v) = ℓ(v)` there;
(d) the union of the `V_N` is dense and `v ↦ a(u,v) − ℓ(v)` is continuous, so `u` solves (9.1.1);
(e) Corollary 9.1.4 then makes the *whole* sequence converge to `u` in norm.

The ascending chain `{V_n}` is taken as given data, as the book does — it is what forces `V` to be
separable, a hypothesis the book notes but never states.  Finite-dimensionality of the `V_n` is not
needed here: it enters only in producing the `u_n`, which is Exercise 9.1.4(a). -/
theorem exercise_9_1_4 [CompleteSpace V] (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀)
    (ha : a.IsEllipticWith c₀) (ℓ : StrongDual ℝ V) (VN : ℕ → Submodule ℝ V)
    (hmono : Monotone VN) (hdense : Dense (⋃ n, (VN n : Set V))) (uN : ℕ → V)
    (huN : ∀ n, GalerkinProblem a ℓ (VN n) (uN n)) :
    ∃ u, (∀ v, a u v = ℓ v) ∧ Tendsto (fun n => ‖u - uN n‖) atTop (𝓝 0) := by
  -- (b) the discrete solutions are bounded by `‖ℓ‖ / c₀`.
  have hbdd : ∀ n, ‖uN n‖ ≤ ‖ℓ‖ / c₀ := by
    intro n
    have h1 : c₀ * ‖uN n‖ ^ 2 ≤ a (uN n) (uN n) := ha _
    have h2 : a (uN n) (uN n) = ℓ (uN n) := (huN n).2 _ (huN n).1
    have h3 : ℓ (uN n) ≤ ‖ℓ‖ * ‖uN n‖ := (Real.le_norm_self _).trans (ℓ.le_opNorm _)
    rcases eq_or_lt_of_le (norm_nonneg (uN n)) with h | h
    · rw [← h]
      exact div_nonneg (norm_nonneg ℓ) hc₀.le
    · rw [le_div_iff₀ hc₀]
      nlinarith
  obtain ⟨σ, w, hσ, hweak⟩ := exists_subseq_weak_tendsto (𝕜 := ℝ) hbdd
  -- the same weak convergence, in the form the functionals see it
  have hfun : ∀ f : StrongDual ℝ V, Tendsto (fun k => f (uN (σ k))) atTop (𝓝 (f w)) := by
    intro f
    have hval : ∀ z : V, ⟪z, (InnerProductSpace.toDual ℝ V).symm f⟫_ℝ = f z := fun z => by
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    simpa only [hval] using hweak ((InnerProductSpace.toDual ℝ V).symm f)
  -- (c) the weak limit solves the variational equation on every `V_N`.
  have hcv : ∀ N : ℕ, ∀ v ∈ VN N, a w v = ℓ v := by
    intro N v hv
    have hlim1 : Tendsto (fun k => a (uN (σ k)) v) atTop (𝓝 (a w v)) :=
      hfun ((a.toCLM hM).flip v)
    have hlim2 : Tendsto (fun k => a (uN (σ k)) v) atTop (𝓝 (ℓ v)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_ge_atTop N] with k hk
      exact ((huN (σ k)).2 v (hmono (hk.trans hσ.le_apply) hv)).symm
    exact tendsto_nhds_unique hlim1 hlim2
  -- (d) the density (9.1.13) upgrades that to all of `V`.
  have hsol : ∀ v, a w v = ℓ v := by
    have hclosed : IsClosed {v : V | a.toCLM hM w v = ℓ v} :=
      isClosed_eq (a.toCLM hM w).continuous ℓ.continuous
    have hsub : (⋃ n, (VN n : Set V)) ⊆ {v : V | a.toCLM hM w v = ℓ v} := by
      rintro v hv
      obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hv
      exact hcv N v hN
    exact fun v => closure_minimal hsub hclosed (hdense v)
  -- (e) with a solution in hand, Corollary 9.1.4 moves the whole sequence.
  exact ⟨w, hsol, corollary_9_1_4 hM hc₀ ha ℓ VN hmono hdense hsol uN huN⟩

/-- Exercise 9.1.4, the payoff: an ascending chain of finite-dimensional subspaces with dense union
already forces (9.1.1) to be uniquely solvable.  This is Lax–Milgram again, proved through the
Galerkin method — the finite-dimensional systems of `exercise_9_1_4_a`, a weakly convergent
subsequence, and the density (9.1.13) — and it uses `AtkinsonHan.Chapter08.theorem_8_3_4` nowhere.
Uniqueness is the `ℓ = 0` case of `eq_zero_of_galerkinProblem_zero` on `V_N = ⊤`. -/
theorem existsUnique_solution_of_galerkin [CompleteSpace V] (hM : a.IsBoundedWith M)
    (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀) (ℓ : StrongDual ℝ V) (VN : ℕ → Submodule ℝ V)
    [∀ n, FiniteDimensional ℝ (VN n)] (hmono : Monotone VN)
    (hdense : Dense (⋃ n, (VN n : Set V))) : ∃! u, ∀ v, a u v = ℓ v := by
  choose uN huN using fun n => (exercise_9_1_4_a hc₀ ha ℓ (VN n)).exists
  obtain ⟨u, hu, -⟩ := exercise_9_1_4 hM hc₀ ha ℓ VN hmono hdense uN huN
  refine ⟨u, hu, fun y hy => ?_⟩
  refine sub_eq_zero.mp (eq_zero_of_galerkinProblem_zero hc₀ ha
    ⟨Submodule.mem_top, fun v _ => ?_⟩)
  simp [map_sub, LinearMap.sub_apply, hy v, hu v]

/-! ### Example 9.1.1: the Galerkin method for `-u'' = f` with the basis `xⁱ(1 - x)`

The weak problem is `u ∈ H¹₀(0, 1)` with `∫₀¹ u' v' = ∫₀¹ f v` for all `v ∈ H¹₀(0, 1)`, and the
trial space is `V_N = span{xⁱ(1 - x) : 1 ≤ i ≤ N}`. The exponents are indexed from `0` here, so
`polyBasis k` is `x^{k+1}(1 - x)` and `polyBasis` over `Fin N` spans exactly the book's `V_N`.

*Erratum.* With the book's own indexing — the basis `xⁱ(1 - x)` for `i = 1, …, N` and the matrix
entry `A_{ij} = ∫₀¹ [xʲ(1 - x)]' [xⁱ(1 - x)]' dx` — the displayed formula is off by one: at
`i = j = 1` it gives `2/15` while the integral is `1/3`. The displayed formula is the entry for
the exponents `i + 1`, `j + 1`, which is what the `0`-based indexing used here makes it, so
`example_9_1_1` states the book's formula verbatim in `(i : ℝ)` and `(j : ℝ)`.

The condition numbers of Table 9.1 are numerical output and are not formalized. -/

section Example911

open MeasureTheory Set SobolevInterval
open scoped ContDiff

noncomputable section

/-- The basis function `x^{k+1}(1 - x)` of Example 9.1.1. -/
def polyBasisFun (k : ℕ) : ℝ → ℝ := fun x => x ^ (k + 1) * (1 - x)

theorem contDiff_polyBasisFun (k : ℕ) : ContDiff ℝ ω (polyBasisFun k) := by
  unfold polyBasisFun; fun_prop

theorem contDiffOn_polyBasisFun (k : ℕ) :
    ContDiffOn ℝ ((1 : ℕ) : ℕ∞ω) (polyBasisFun k) (Icc (0 : ℝ) 1) :=
  ((contDiff_polyBasisFun k).of_le le_top).contDiffOn

/-- The derivative of `x^{k+1}(1 - x)` is `(k+1) x^k - (k+2) x^{k+1}`. -/
theorem deriv_polyBasisFun (k : ℕ) (x : ℝ) :
    _root_.deriv (polyBasisFun k) x = ((k : ℝ) + 1) * x ^ k - ((k : ℝ) + 2) * x ^ (k + 1) := by
  unfold polyBasisFun
  have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := (hasDerivAt_id x).const_sub 1
  have h : HasDerivAt (fun x : ℝ => x ^ (k + 1) * (1 - x))
      ((k + 1 : ℕ) * x ^ (k + 1 - 1) * (1 - x) + x ^ (k + 1) * (-1)) x :=
    (hasDerivAt_pow (k + 1) x).mul h1
  rw [h.deriv]
  push_cast
  ring

/-- The basis function `x^{k+1}(1 - x)` as an element of `H¹(0, 1)`. -/
def polyBasis (k : ℕ) : SobolevInterval 1 0 1 :=
  ContDiffMapIcc.toSobolevInterval zero_le_one zero_lt_one 1
    (ContDiffMapIcc.ofContDiffOn zero_le_one zero_lt_one (contDiffOn_polyBasisFun k))

theorem coeFn_deriv_polyBasis_zero (k : ℕ) :
    (SobolevInterval.deriv (polyBasis k) 0 : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] polyBasisFun k := by
  refine (ContDiffMapIcc.coeFn_derivLp _ 0).trans ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => ?_)
  rw [IccExtend_of_mem zero_le_one _ (Ioo_subset_Icc_self hx)]
  rfl

theorem coeFn_deriv_polyBasis_one (k : ℕ) :
    (SobolevInterval.deriv (polyBasis k) 1 : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x => ((k : ℝ) + 1) * x ^ k - ((k : ℝ) + 2) * x ^ (k + 1) := by
  refine (ContDiffMapIcc.coeFn_derivLp _ 1).trans ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => ?_)
  have hx' : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  rw [IccExtend_of_mem zero_le_one _ hx',
    ContDiffMapIcc.deriv_ofContDiffOn zero_le_one zero_lt_one (contDiffOn_polyBasisFun k) 1
      ⟨x, hx'⟩,
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      ((contDiff_polyBasisFun k).contDiffAt.of_le le_top) hx']
  simpa using deriv_polyBasisFun k x

/-- `x^{k+1}(1 - x)` vanishes at both endpoints, so it lies in `H¹₀(0, 1)`. -/
theorem polyBasis_mem (k : ℕ) : polyBasis k ∈ SobolevIntervalZero 0 1 := by
  have hc : ContinuousOn (polyBasisFun k) (Icc (0 : ℝ) 1) :=
    (contDiff_polyBasisFun k).continuous.continuousOn
  rw [mem_sobolevIntervalZero_iff zero_lt_one]
  refine ⟨?_, ?_⟩ <;>
    rw [toContinuousMap_eq_of_continuousOn zero_lt_one _ hc (coeFn_deriv_polyBasis_zero k)] <;>
    simp [polyBasisFun]

/-- The constant coefficient `1`, as an element of `L^∞(0, 1)`. -/
def oneLinf : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1)) :=
  (ContinuousOn.memLp_top_restrict_Ioo (g := fun _ => (1 : ℝ)) continuousOn_const).toLp _

theorem coeFn_oneLinf : (oneLinf : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun _ => (1 : ℝ) :=
  MemLp.coeFn_toLp _

theorem one_le_oneLinf : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), (1 : ℝ) ≤ oneLinf x := by
  filter_upwards [coeFn_oneLinf] with x hx
  rw [hx]

theorem zero_le_zeroLinf :
    ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      (0 : ℝ) ≤ (0 : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) x := by
  filter_upwards [Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))] with x hx
  rw [hx]
  rfl

/-- **The bilinear form of (9.1.9)**, `a(u, v) = ∫₀¹ u' v'` on `H¹(0, 1)`: the backbone's
`EllipticInterval.form` with `α = 1`, `β = γ = 0`. -/
def dirichletForm : SesqForm ℝ (SobolevInterval 1 0 1) := EllipticInterval.form 0 1 oneLinf 0 0

theorem dirichletForm_apply (u v : SobolevInterval 1 0 1) :
    dirichletForm u v = ∫ x in Ioo (0 : ℝ) 1, SobolevInterval.deriv u 1 x *
      SobolevInterval.deriv v 1 x := by
  rw [dirichletForm, EllipticInterval.form_apply]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_oneLinf, Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))] with x h1 h0
  rw [h1, h0]
  simp

/-- **The trial space `V_N`** of Example 9.1.1, `span{xⁱ(1 - x) : 1 ≤ i ≤ N}`. -/
def polySpace (N : ℕ) : Submodule ℝ (SobolevInterval 1 0 1) :=
  Submodule.span ℝ (Set.range fun i : Fin N => polyBasis i)

theorem polySpace_le (N : ℕ) : polySpace N ≤ SobolevIntervalZero 0 1 :=
  Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact polyBasis_mem i)

instance (N : ℕ) : FiniteDimensional ℝ (polySpace N) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem integral_pow_unit (n : ℕ) : ∫ x in (0 : ℝ)..1, x ^ n = 1 / (n + 1) := by
  rw [integral_pow]; simp

/-- **Unique solvability of the weak problem in any subspace of `H¹₀(0, 1)`**, by Lax–Milgram:
the form is coercive there by the Poincaré inequality. Taking `K = H¹₀(0, 1)` gives the weak
problem of Example 9.1.1, and `K = V_N` its Galerkin approximation. -/
theorem existsUnique_dirichletGalerkin {K : Submodule ℝ (SobolevInterval 1 0 1)}
    (hK : K ≤ SobolevIntervalZero 0 1) [CompleteSpace K]
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! u, IsGalerkinSolution dirichletForm (EllipticInterval.load 0 1 f) K u := by
  have hc : (0 : ℝ) < 1 / (1 + ((1 : ℝ) - 0) ^ 2 / 2) := by norm_num
  have hcoer : (dirichletForm.restrict K).IsCoerciveWith (1 / (1 + ((1 : ℝ) - 0) ^ 2 / 2)) := by
    intro v
    have h := EllipticInterval.form_isCoerciveWith_restrict (a := 0) (b := 1) zero_lt_one oneLinf 0
      one_le_oneLinf zero_le_zeroLinf zero_le_one ⟨(v : SobolevInterval 1 0 1), hK v.2⟩
    rw [SesqForm.restrict_apply] at h
    rw [SesqForm.restrict_apply]
    simpa [dirichletForm] using h
  obtain ⟨w, hw, hwu⟩ := SesqForm.laxMilgram (dirichletForm.restrict K)
    ((EllipticInterval.load 0 1 f).comp K.subtypeL) hc hcoer
  refine ⟨(w : SobolevInterval 1 0 1), ⟨w.2, fun v hv => hw ⟨v, hv⟩⟩, ?_⟩
  rintro y ⟨hyK, hy⟩
  exact congrArg Subtype.val (hwu ⟨y, hyK⟩ fun z => hy (z : SobolevInterval 1 0 1) z.2)

/-- The stiffness matrix entry of Example 9.1.1:
`∫₀¹ [x^{j+1}(1 - x)]' [x^{i+1}(1 - x)]' dx`, expanded and integrated term by term. -/
theorem dirichletForm_polyBasis (i j : ℕ) :
    dirichletForm (polyBasis j) (polyBasis i)
      = ((i : ℝ) + 1) * ((j : ℝ) + 1) / ((i : ℝ) + (j : ℝ) + 1)
        + ((i : ℝ) + 2) * ((j : ℝ) + 2) / ((i : ℝ) + (j : ℝ) + 3)
        - (((i : ℝ) + 1) * ((j : ℝ) + 2) + ((i : ℝ) + 2) * ((j : ℝ) + 1))
            / ((i : ℝ) + (j : ℝ) + 2) := by
  rw [dirichletForm_apply,
    show (∫ x in Ioo (0 : ℝ) 1, SobolevInterval.deriv (polyBasis j) 1 x *
          SobolevInterval.deriv (polyBasis i) 1 x)
        = ∫ x in Ioo (0 : ℝ) 1,
          (((j : ℝ) + 1) * x ^ j - ((j : ℝ) + 2) * x ^ (j + 1)) *
            (((i : ℝ) + 1) * x ^ i - ((i : ℝ) + 2) * x ^ (i + 1)) from ?_]
  · rw [← intervalIntegral.integral_eq_setIntegral_Ioo zero_le_one]
    have hexp : ∀ x : ℝ,
        (((j : ℝ) + 1) * x ^ j - ((j : ℝ) + 2) * x ^ (j + 1)) *
          (((i : ℝ) + 1) * x ^ i - ((i : ℝ) + 2) * x ^ (i + 1))
        = (((j : ℝ) + 1) * ((i : ℝ) + 1)) * x ^ (i + j)
          + (-(((j : ℝ) + 1) * ((i : ℝ) + 2)) - ((j : ℝ) + 2) * ((i : ℝ) + 1)) * x ^ (i + j + 1)
          + (((j : ℝ) + 2) * ((i : ℝ) + 2)) * x ^ (i + j + 2) := fun x => by ring
    simp only [hexp]
    have hint : ∀ (c : ℝ) (n : ℕ), IntervalIntegrable (fun x : ℝ => c * x ^ n) volume 0 1 :=
      fun c n => (continuous_const.mul (continuous_pow n)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add ((hint _ _).add (hint _ _)) (hint _ _),
      intervalIntegral.integral_add (hint _ _) (hint _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_pow_unit, integral_pow_unit,
      integral_pow_unit]
    have h1 : ((i : ℝ) + (j : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((i : ℝ) + (j : ℝ) + 2) ≠ 0 := by positivity
    have h3 : ((i : ℝ) + (j : ℝ) + 3) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · refine integral_congr_ae ?_
    filter_upwards [coeFn_deriv_polyBasis_one j, coeFn_deriv_polyBasis_one i] with x hj hi
    rw [hj, hi]

/-- The load vector entry of Example 9.1.1, `b_i = ∫₀¹ f(x) x^{i+1}(1 - x) dx`. -/
theorem load_polyBasis (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (i : ℕ) :
    EllipticInterval.load 0 1 f (polyBasis i) = ∫ x in Ioo (0 : ℝ) 1, f x * polyBasisFun i x := by
  rw [EllipticInterval.load_apply]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_deriv_polyBasis_zero i] with x hx
  rw [hx]

/-- **Example 9.1.1.** For `-u'' = f` on `(0, 1)` with `u(0) = u(1) = 0`, weakly posed on
`V = H¹₀(0, 1)` with `a(u, v) = ∫₀¹ u' v'` and `ℓ(v) = ∫₀¹ f v`:

* the weak problem has exactly one solution, by Lax–Milgram;
* so does its Galerkin approximation on `V_N = span{xⁱ(1 - x) : 1 ≤ i ≤ N}`;
* the stiffness matrix entries are the ones the book displays, and the load vector entries are
  `b_i = ∫₀¹ f(x) xⁱ(1 - x) dx`.

The exponents are `0`-indexed here (`polyBasis i` is `x^{i+1}(1 - x)`), which is the indexing
under which the book's displayed entry formula is correct; see the section's erratum note. Table
9.1, the condition numbers showing this basis to be a poor one, is numerical output and is not
formalized. -/
theorem example_9_1_1 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (N : ℕ) :
    (∃! u, IsGalerkinSolution dirichletForm (EllipticInterval.load 0 1 f)
        (SobolevIntervalZero 0 1) u) ∧
      (∃! uN, IsGalerkinSolution dirichletForm (EllipticInterval.load 0 1 f) (polySpace N) uN) ∧
      (∀ i j : Fin N,
        stiffnessMatrix (BilinForm.ofCLM dirichletForm) (fun i : Fin N => polyBasis i) i j =
          ((i : ℝ) + 1) * ((j : ℝ) + 1) / ((i : ℝ) + (j : ℝ) + 1)
            + ((i : ℝ) + 2) * ((j : ℝ) + 2) / ((i : ℝ) + (j : ℝ) + 3)
            - (((i : ℝ) + 1) * ((j : ℝ) + 2) + ((i : ℝ) + 2) * ((j : ℝ) + 1))
                / ((i : ℝ) + (j : ℝ) + 2)) ∧
      (∀ i : Fin N, loadVector (EllipticInterval.load 0 1 f) (fun i : Fin N => polyBasis i) i
        = ∫ x in Ioo (0 : ℝ) 1, f x * polyBasisFun i x) := by
  refine ⟨existsUnique_dirichletGalerkin le_rfl f,
    existsUnique_dirichletGalerkin (polySpace_le N) f, fun i j => ?_, fun i => load_polyBasis f i⟩
  rw [stiffnessMatrix_apply, BilinForm.ofCLM_apply]
  exact dirichletForm_polyBasis i j

end

end Example911

/-! ### Example 9.1.2: the same problem with the basis `sin(iπx)`

The trial space is `V_N = span{sin(iπx) : 1 ≤ i ≤ N}`, indexed from `0` here as in Example 9.1.1,
so `sineBasis k` is `sin((k+1)πx)`. The basis is orthogonal for `a(u, v) = ∫₀¹ u' v'`, the
Galerkin system is diagonal, and the Galerkin solution is the kernel approximation (9.1.10) with
the `N`-term truncation of the Green kernel; the full kernel is `exercise_9_1_3`. -/

section Example912

open MeasureTheory Set SobolevInterval
open scoped ContDiff

noncomputable section

/-- The basis function `sin((k+1) π x)` of Example 9.1.2. -/
def sineBasisFun (k : ℕ) : ℝ → ℝ := fun x => Real.sin (((k : ℝ) + 1) * π * x)

theorem contDiff_sineBasisFun (k : ℕ) : ContDiff ℝ ω (sineBasisFun k) := by
  unfold sineBasisFun; fun_prop

theorem contDiffOn_sineBasisFun (k : ℕ) :
    ContDiffOn ℝ ((1 : ℕ) : ℕ∞ω) (sineBasisFun k) (Icc (0 : ℝ) 1) :=
  ((contDiff_sineBasisFun k).of_le le_top).contDiffOn

theorem deriv_sineBasisFun (k : ℕ) (x : ℝ) :
    _root_.deriv (sineBasisFun k) x
      = ((k : ℝ) + 1) * π * Real.cos (((k : ℝ) + 1) * π * x) := by
  unfold sineBasisFun
  have h1 : HasDerivAt (fun y : ℝ => ((k : ℝ) + 1) * π * y) (((k : ℝ) + 1) * π) x := by
    simpa using (hasDerivAt_id x).const_mul (((k : ℝ) + 1) * π)
  have h2 : HasDerivAt (fun y : ℝ => Real.sin (((k : ℝ) + 1) * π * y))
      (Real.cos (((k : ℝ) + 1) * π * x) * (((k : ℝ) + 1) * π)) x :=
    (Real.hasDerivAt_sin _).comp x h1
  rw [h2.deriv]
  ring

/-- `sin((k+1) π x)` as an element of `H¹(0, 1)`. -/
def sineBasis (k : ℕ) : SobolevInterval 1 0 1 :=
  ContDiffMapIcc.toSobolevInterval zero_le_one zero_lt_one 1
    (ContDiffMapIcc.ofContDiffOn zero_le_one zero_lt_one (contDiffOn_sineBasisFun k))

theorem coeFn_deriv_sineBasis_zero (k : ℕ) :
    (SobolevInterval.deriv (sineBasis k) 0 : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] sineBasisFun k := by
  refine (ContDiffMapIcc.coeFn_derivLp _ 0).trans ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => ?_)
  rw [IccExtend_of_mem zero_le_one _ (Ioo_subset_Icc_self hx)]
  rfl

theorem coeFn_deriv_sineBasis_one (k : ℕ) :
    (SobolevInterval.deriv (sineBasis k) 1 : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x => ((k : ℝ) + 1) * π * Real.cos (((k : ℝ) + 1) * π * x) := by
  refine (ContDiffMapIcc.coeFn_derivLp _ 1).trans ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => ?_)
  have hx' : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  rw [IccExtend_of_mem zero_le_one _ hx',
    ContDiffMapIcc.deriv_ofContDiffOn zero_le_one zero_lt_one (contDiffOn_sineBasisFun k) 1
      ⟨x, hx'⟩,
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      ((contDiff_sineBasisFun k).contDiffAt.of_le le_top) hx']
  simpa using deriv_sineBasisFun k x

theorem rep_sineBasis (k : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    SobolevInterval.rep (sineBasis k) x = sineBasisFun k x :=
  rep_eq_of_continuousOn zero_lt_one _ (contDiff_sineBasisFun k).continuous.continuousOn
    (coeFn_deriv_sineBasis_zero k) hx

theorem sineBasis_mem (k : ℕ) : sineBasis k ∈ SobolevIntervalZero 0 1 := by
  have hc : ContinuousOn (sineBasisFun k) (Icc (0 : ℝ) 1) :=
    (contDiff_sineBasisFun k).continuous.continuousOn
  rw [mem_sobolevIntervalZero_iff zero_lt_one]
  refine ⟨?_, ?_⟩ <;>
    rw [toContinuousMap_eq_of_continuousOn zero_lt_one _ hc (coeFn_deriv_sineBasis_zero k)]
  · simp [sineBasisFun]
  · have hone : ((k : ℝ) + 1) * π * 1 = ((k + 1 : ℕ) : ℝ) * π := by push_cast; ring
    simp only [sineBasisFun, hone, Real.sin_nat_mul_pi]

/-- **The orthogonality relation of Example 9.1.2**:
`∫₀¹ (sin jπx)' (sin iπx)' dx = i j π² δ_{ij} / 2`. -/
theorem dirichletForm_sineBasis (i j : ℕ) :
    dirichletForm (sineBasis j) (sineBasis i)
      = if i = j then ((i : ℝ) + 1) * ((j : ℝ) + 1) * π ^ 2 / 2 else 0 := by
  rw [dirichletForm_apply,
    show (∫ x in Ioo (0 : ℝ) 1, SobolevInterval.deriv (sineBasis j) 1 x *
          SobolevInterval.deriv (sineBasis i) 1 x)
        = ∫ x in Ioo (0 : ℝ) 1,
          (((j : ℝ) + 1) * π * Real.cos (((j : ℝ) + 1) * π * x)) *
            (((i : ℝ) + 1) * π * Real.cos (((i : ℝ) + 1) * π * x)) from ?_]
  · rw [← intervalIntegral.integral_eq_setIntegral_Ioo zero_le_one]
    have hre : ∀ x : ℝ,
        (((j : ℝ) + 1) * π * Real.cos (((j : ℝ) + 1) * π * x)) *
          (((i : ℝ) + 1) * π * Real.cos (((i : ℝ) + 1) * π * x))
        = (((j : ℝ) + 1) * π * (((i : ℝ) + 1) * π)) *
            (Real.cos (((j + 1 : ℕ) : ℝ) * π * x) * Real.cos (((i + 1 : ℕ) : ℝ) * π * x)) := by
      intro x
      push_cast
      ring
    simp only [hre]
    rw [intervalIntegral.integral_const_mul,
      integral_cos_mul_cos_unit (Nat.succ_pos j) (Nat.succ_pos i)]
    rcases eq_or_ne i j with rfl | hij
    · rw [ite_eq_left (rfl : i = i), ite_eq_left (rfl : i + 1 = i + 1)]
      ring
    · rw [ite_eq_right hij, ite_eq_right (by simpa using fun h => hij (by omega))]
      ring
  · refine integral_congr_ae ?_
    filter_upwards [coeFn_deriv_sineBasis_one j, coeFn_deriv_sineBasis_one i] with x hj hi
    rw [hj, hi]

/-- **The trial space of Example 9.1.2**, `V_N = span{sin(iπx) : 1 ≤ i ≤ N}`. -/
def sineSpace (N : ℕ) : Submodule ℝ (SobolevInterval 1 0 1) :=
  Submodule.span ℝ (Set.range fun i : Fin N => sineBasis i)

theorem sineSpace_le (N : ℕ) : sineSpace N ≤ SobolevIntervalZero 0 1 :=
  Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact sineBasis_mem i)

instance (N : ℕ) : FiniteDimensional ℝ (sineSpace N) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- **The Galerkin coefficient** `ξ_i = (2 / (π² i²)) ∫₀¹ f(x) sin(iπx) dx` of Example 9.1.2. -/
def sineCoeff (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (k : ℕ) : ℝ :=
  2 / (π ^ 2 * ((k : ℝ) + 1) ^ 2) * ∫ x in Ioo (0 : ℝ) 1, f x * sineBasisFun k x

/-- **The Galerkin solution** `u_N = ∑ ξ_j sin(jπx)` of Example 9.1.2. -/
def sineGalerkin (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (N : ℕ) : SobolevInterval 1 0 1 :=
  ∑ j : Fin N, sineCoeff f j • sineBasis j

theorem load_sineBasis (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (i : ℕ) :
    EllipticInterval.load 0 1 f (sineBasis i) = ∫ x in Ioo (0 : ℝ) 1, f x * sineBasisFun i x := by
  rw [EllipticInterval.load_apply]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_deriv_sineBasis_zero i] with x hx
  rw [hx]

/-- The diagonal Galerkin system of Example 9.1.2 is solved by `ξ_i = (2/(π² i²)) ∫₀¹ f sin(iπx)`:
the coefficients of `sineGalerkin` do solve the Galerkin problem on `V_N`. -/
theorem isGalerkinSolution_sineGalerkin (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (N : ℕ) :
    IsGalerkinSolution dirichletForm (EllipticInterval.load 0 1 f) (sineSpace N)
      (sineGalerkin f N) := by
  classical
  refine ⟨Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩), ?_⟩
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have hsum : dirichletForm (sineGalerkin f N) (sineBasis i)
          = ∑ j : Fin N, sineCoeff f j * dirichletForm (sineBasis j) (sineBasis i) := by
        rw [sineGalerkin, map_sum]
        simp only [FunLike.coe_sum, Finset.sum_apply, map_smul, FunLike.coe_smul, Pi.smul_apply,
          smul_eq_mul]
      rw [hsum]
      simp only [dirichletForm_sineBasis, mul_ite, mul_zero]
      have hfin : ∀ j : Fin N, ((i : ℕ) = (j : ℕ)) = (i = j) := fun j => by simp [Fin.val_inj]
      simp only [hfin]
      rw [Finset.sum_ite_eq Finset.univ i
        (fun j : Fin N => sineCoeff f j * (((i : ℝ) + 1) * ((j : ℝ) + 1) * π ^ 2 / 2)),
        ite_eq_left (Finset.mem_univ i), load_sineBasis, sineCoeff]
      have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
      have hik : ((i : ℝ) + 1) ≠ 0 := by positivity
      field_simp
  | zero => simp
  | add x y _ _ ihx ihy => rw [map_add, map_add, ihx, ihy]
  | smul c x _ ih => rw [map_smul, map_smul, ih]

/-- **The kernel form (9.1.10) of the Galerkin solution**: `u_N(x) = ∫₀¹ f(t) K_N(x, t) dt` with
`K_N(x, t) = (2/π²) ∑_{j ≤ N} sin(jπx) sin(jπt) / j²`, the `N`-term truncation of the Green
kernel of `exercise_9_1_3`. -/
theorem rep_sineGalerkin (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (N : ℕ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    SobolevInterval.rep (sineGalerkin f N) x
      = ∫ t in Ioo (0 : ℝ) 1, f t * (2 / π ^ 2 *
          ∑ j : Fin N, sineBasisFun j x * sineBasisFun j t / ((j : ℝ) + 1) ^ 2) := by
  have hintg : ∀ j : Fin N, IntegrableOn
      (fun t => f t * (2 / π ^ 2 * (sineBasisFun j x * sineBasisFun j t / ((j : ℝ) + 1) ^ 2)))
      (Ioo (0 : ℝ) 1) := by
    intro j
    have hg : ContinuousOn
        (fun t => 2 / π ^ 2 * (sineBasisFun j x * sineBasisFun j t / ((j : ℝ) + 1) ^ 2))
        (Icc (0 : ℝ) 1) := by
      have hcont : Continuous (sineBasisFun (j : ℕ)) := (contDiff_sineBasisFun j).continuous
      fun_prop
    exact (MeasureTheory.integrableOn_continuousOn_mul hg f).congr_fun
      (fun t _ => mul_comm _ _) measurableSet_Ioo
  rw [sineGalerkin, rep_finset_sum zero_lt_one _ _ _ hx]
  have hterm : ∀ j : Fin N, sineCoeff f j * SobolevInterval.rep (sineBasis j) x
      = ∫ t in Ioo (0 : ℝ) 1,
        f t * (2 / π ^ 2 * (sineBasisFun j x * sineBasisFun j t / ((j : ℝ) + 1) ^ 2)) := by
    intro j
    have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    have hjk : ((j : ℝ) + 1) ≠ 0 := by positivity
    have hre : ∀ t : ℝ,
        (f : ℝ → ℝ) t * (2 / π ^ 2 * (sineBasisFun j x * sineBasisFun j t / ((j : ℝ) + 1) ^ 2))
        = (2 / (π ^ 2 * ((j : ℝ) + 1) ^ 2) * sineBasisFun j x) *
            ((f : ℝ → ℝ) t * sineBasisFun j t) := by
      intro t
      field_simp
    rw [rep_sineBasis j hx, sineCoeff]
    simp only [hre]
    rw [integral_const_mul]
    ring
  simp only [hterm]
  rw [← integral_finsetSum _ fun j _ => hintg j]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [Finset.mul_sum, Finset.mul_sum]

/-- **Example 9.1.2.** The same boundary value problem (9.1.9) with the trigonometric trial space
`V_N = span{sin(iπx) : 1 ≤ i ≤ N}`:

* the basis is orthogonal for the energy inner product,
  `∫₀¹ (sin jπx)' (sin iπx)' dx = i j π² δ_{ij} / 2`, so the Galerkin system is diagonal;
* its unique solution is `u_N = ∑ ξ_j sin(jπx)` with `ξ_i = (2/(π² i²)) ∫₀¹ f(x) sin(iπx) dx`;
* and `u_N` is the kernel approximation (9.1.10), `u_N(x) = ∫₀¹ f(t) K_N(x, t) dt` with
  `K_N(x, t) = (2/π²) ∑_{j ≤ N} sin(jπx) sin(jπt)/j²`, the `N`-term truncation of the Green
  kernel of `exercise_9_1_3`.

Exponents are `0`-indexed, `sineBasis k = sin((k+1)πx)`. -/
theorem example_9_1_2 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (N : ℕ) :
    (∀ i j : ℕ, dirichletForm (sineBasis j) (sineBasis i)
        = if i = j then ((i : ℝ) + 1) * ((j : ℝ) + 1) * π ^ 2 / 2 else 0) ∧
      (∀ uN, IsGalerkinSolution dirichletForm (EllipticInterval.load 0 1 f) (sineSpace N) uN ↔
        uN = ∑ j : Fin N, (2 / (π ^ 2 * ((j : ℝ) + 1) ^ 2) *
          ∫ x in Ioo (0 : ℝ) 1, f x * sineBasisFun j x) • sineBasis j) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, SobolevInterval.rep (sineGalerkin f N) x
        = ∫ t in Ioo (0 : ℝ) 1, f t * (2 / π ^ 2 *
            ∑ j : Fin N, sineBasisFun j x * sineBasisFun j t / ((j : ℝ) + 1) ^ 2)) := by
  refine ⟨dirichletForm_sineBasis, fun uN => ⟨fun h => ?_, fun h => ?_⟩,
    fun x hx => rep_sineGalerkin f N hx⟩
  · obtain ⟨w, -, huniq⟩ := existsUnique_dirichletGalerkin (sineSpace_le N) f
    exact (huniq uN h).trans (huniq _ (isGalerkinSolution_sineGalerkin f N)).symm
  · rw [h]
    exact isGalerkinSolution_sineGalerkin f N

end

end Example912

end Chapter09

end AtkinsonHan
