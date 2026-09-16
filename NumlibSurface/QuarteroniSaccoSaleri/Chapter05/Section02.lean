import Mathlib.LinearAlgebra.Eigenspace.Zero
import Numlib.Eigen.ReducedResolvent
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section01

/-!
# Quarteroni–Sacco–Saleri §5.2: stability and conditioning analysis

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §5.2, over the backbone `Numlib/Eigen/Perturbation` (Bauer–Fike, the
condition number of a simple eigenvalue and the derivative of an eigenvalue along a branch, the
Hermitian residual bounds) and `Numlib/Eigen/ReducedResolvent` (the derivative of an eigenvector
along a branch and the condition number of an eigenvector).

## Conventions

The book works in `ℂ^{n×n}` with the Euclidean norm: matrices are `Matrix (Fin n) (Fin n) ℂ`,
vectors are `EuclideanSpace ℂ (Fin n)` acted on through `Matrix.toEuclideanLin`, `‖·‖₂` on
matrices is Mathlib's scoped `Matrix.Norms.L2Operator` norm and `K₂(X) = ‖X‖₂ ‖X⁻¹‖₂` is
`NormedRing.condNumber X` under it. A right eigenvector is `A x = λ x`; a left eigenvector
`yᴴ A = λ yᴴ` is written `Aᴴ y = λ̄ y`, that is `toEuclideanLin Aᴴ y = star λ • y`, and `yᴴ x` is
the inner product `inner ℂ y x`. A *simple* eigenvalue has algebraic multiplicity one (§1.7), the
multiplicity of `λ` as a root of the characteristic polynomial: `A.charpoly.rootMultiplicity λ = 1`,
which Mathlib's `LinearMap.finrank_maxGenEigenspace_eq` identifies with the dimension of the
generalized eigenspace the backbone works with (`Matrix.finrank_maxGenEigenspace_toEuclideanLin`).
A
diagonalizable matrix is given by `X⁻¹ A X = diagonal d` with `X` nonsingular. The perturbation
parameter `ε` of Theorem 5.4 and Property 5.5 is a complex `t`, the book's real `ε ≥ 0` being its
restriction, and a "branch" `λ(ε), x(ε)` is a pair of functions `mu : ℂ → ℂ`, `v : ℂ → ℂⁿ` with
`HasDerivAt` at `0`.

## Contents

* `theorem_5_3`, `equation_5_9` — Bauer–Fike and its normal case.
* `theorem_5_4`, `theorem_5_4_branch`, `theorem_5_4_inner_ne_zero` — the first-order
  perturbation of a simple eigenvalue, the branch it presupposes, and `yᴴ x ≠ 0`.
* `equation_5_11`, `equation_5_11_eq_eigenvalueCondNumber`, `equation_5_11_one_le`,
  `equation_5_11_normal`, `eigenvalueCondNumber_conj_unitary` — the condition number `κ(λ)`.
* `property_5_5` — the first-order perturbation of the eigenvector of a simple eigenvalue.
* `theorem_5_5`, `property_5_6`, `property_5_7` — the a posteriori estimates.

## Readings and errata

Theorem 5.3 is stated for the `2`-norm only; the book says "any matrix `p`-norm". Theorem 5.4 does
not need `A` diagonalizable, only the differentiable branch it presupposes, which
`theorem_5_4_branch` supplies at a simple eigenvalue and whose eigen-equation holds near `ε = 0`
(the book's "in a neighborhood of `ε = 0`"). Property 5.5 is stated for a *Hermitian* `A`, with the
normalization `x_kᴴ x_k(ε) = 1` in place of `‖x_k(ε)‖₂ = 1` (the two differ by a factor
`1 + O(ε²)`) and with `o(ε)` in place of `O(ε²)`: for a non-normal `A` the constant
`1 / min_{j ≠ k} |λ_k − λ_j|` is false, the first-order constant being the norm of the reduced
resolvent (`Module.End.eigenvectorCondNumber`), and `O(ε²)` needs a `C²` branch the hypotheses do
not provide; its branch is quantified over every `ε`, as the book quantifies `x_k(ε)`. Property
5.6's hypothesis `|λ_i − λ̂| ≤ ‖r̂‖₂` for `i = 1, …, m` plays no role and is dropped. The
floating-point estimate (5.12) and Example 5.2 are not nodes.
-/

open Filter Matrix Topology
open scoped Matrix.Norms.L2Operator

namespace QuarteroniSaccoSaleri.Chapter05

variable {n : ℕ}

/-! ### Bridges between the matrix and the operator vocabulary -/

/-- A left eigenvector in the book's sense, `yᴴ A = λ yᴴ` (here `Aᴴ y = λ̄ y`), is a left
eigenvector in the backbone's sense, `⟪y, A z⟫ = λ ⟪y, z⟫` for every `z`. -/
theorem inner_toEuclideanLin_eq_of_conjTranspose_eq {A : Matrix (Fin n) (Fin n) ℂ} {lam : ℂ}
    {y : EuclideanSpace ℂ (Fin n)} (hy : toEuclideanLin Aᴴ y = star lam • y)
    (z : EuclideanSpace ℂ (Fin n)) : inner ℂ y (toEuclideanLin A z) = lam * inner ℂ y z := by
  rw [← toEuclideanLin_conjTranspose_inner_left, hy, inner_smul_left]
  simp

-- TODO(backbone): `Module.End.deriv_eigenvalue_perturbation` and
-- `Module.End.norm_deriv_eigenvalue_perturbation_le` use their hypothesis `heig` only through
-- `Filter.Eventually.of_forall`; generalize it to `∀ᶠ t in 𝓝 0` there and delete this.
/-- `Module.End.norm_deriv_eigenvalue_perturbation_le` with the eigen-equation of the branch
required only near `0`: the branch is replaced by one that agrees with it near `0` and is the zero
eigenpair elsewhere. -/
theorem norm_deriv_eigenvalue_perturbation_le_of_eventually {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {A B : E →L[ℂ] E} {u : ℂ → E} {mu : ℂ → ℂ} {u' : E} {mu' lam : ℂ}
    {w : E} (hu : HasDerivAt u u' 0) (hmu : HasDerivAt mu mu' 0)
    (heig : ∀ᶠ t in 𝓝 0, A (u t) + t • B (u t) = mu t • u t)
    (hw : ∀ y, inner ℂ w (A y) = lam * inner ℂ w y) (hlam : mu 0 = lam)
    (hne : inner ℂ w (u 0) ≠ 0) :
    ‖mu'‖ ≤ ‖B‖ * Module.End.eigenvalueCondNumber ℂ (u 0) w := by
  classical
  set p : ℂ → Prop := fun t => A (u t) + t • B (u t) = mu t • u t with hp
  have h0 : p 0 := heig.self_of_nhds
  have hu₁ : (fun t => if p t then u t else 0) =ᶠ[𝓝 0] u :=
    heig.mono fun t ht => ite_eq_left ht
  have hmu₁ : (fun t => if p t then mu t else 0) =ᶠ[𝓝 0] mu :=
    heig.mono fun t ht => ite_eq_left ht
  have key := Module.End.norm_deriv_eigenvalue_perturbation_le (A := A) (B := B)
    (hu.congr_of_eventuallyEq hu₁) (hmu.congr_of_eventuallyEq hmu₁) (fun t => ?_) hw
    (by simp only [ite_eq_left h0, hlam]) (by simpa only [ite_eq_left h0] using hne)
  · simpa only [ite_eq_left h0] using key
  · by_cases ht : p t
    · simp only [ite_eq_left ht]
      exact ht
    · simp only [ite_eq_right ht, map_zero, smul_zero, add_zero]

/-! ### Theorem 5.3: Bauer–Fike -/

/-- **Theorem 5.3 (Bauer–Fike), (5.8), `p = 2`.** Let `A ∈ ℂ^{n×n}` be diagonalizable,
`D = X⁻¹ A X = diag(λ_1, …, λ_n)` with `X` the nonsingular matrix of its right eigenvectors, and
let `μ` be an eigenvalue of `A + E`. Then `min_{λ ∈ σ(A)} |λ − μ| ≤ K₂(X) ‖E‖₂`, where
`K₂(X) = ‖X‖₂ ‖X⁻¹‖₂` is the condition number of the eigenvalue problem for `A`. Backbone
`Matrix.bauer_fike`; the eigenvalue attaining the minimum is a diagonal entry `d i`, and
`σ(A) = σ(D)` by similarity. The book's "any matrix `p`-norm" is not formalized beyond `p = 2`. -/
theorem theorem_5_3 {A X : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X) {d : Fin n → ℂ}
    (hD : X⁻¹ * A * X = diagonal d) (E : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (A + E)) :
    ∃ lam ∈ spectrum ℂ A, ‖lam - μ‖ ≤ NormedRing.condNumber X * ‖E‖ := by
  have hdet := (isUnit_iff_isUnit_det X).mp hX
  have hA : A = X * diagonal d * X⁻¹ := by
    rw [← hD, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv X hdet, Matrix.mul_one,
      ← Matrix.mul_assoc, mul_nonsing_inv X hdet, Matrix.one_mul]
  obtain ⟨i, hi⟩ := bauer_fike X d hX E (hA ▸ hμ)
  refine ⟨d i, ?_, by rwa [norm_sub_rev]⟩
  have hspec := spectrum.units_conjugate' (R := ℂ) (a := A) (u := hX.unit)
  rw [coe_units_inv, IsUnit.unit_spec, hD, spectrum_diagonal] at hspec
  rw [← hspec]
  exact ⟨i, rfl⟩

/-- **(5.9).** If `A` is normal, the similarity transformation matrix `X` of Theorem 5.3 is
unitary, so `K₂(X) = 1` and `min_{λ ∈ σ(A)} |λ − μ| ≤ ‖E‖₂` for every `μ ∈ σ(A + E)`: the
eigenvalue problem of a normal matrix is well conditioned with respect to the absolute error. From
`theorem_5_3` with the spectral theorem for normal matrices (`Matrix.IsStarNormal.spectral_theorem`)
and `Matrix.condNumber_l2_of_mem_unitaryGroup`. -/
theorem equation_5_9 {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A)
    (E : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ} (hμ : μ ∈ spectrum ℂ (A + E)) :
    ∃ lam ∈ spectrum ℂ A, ‖lam - μ‖ ≤ ‖E‖ := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · have : Subsingleton (Matrix (Fin n) (Fin n) ℂ) := ⟨fun _ _ => by ext i; exact isEmptyElim i⟩
    simp [spectrum.of_subsingleton] at hμ
  obtain ⟨U, hU, d, hd⟩ := Matrix.IsStarNormal.spectral_theorem.mp hA
  have hUinv : U⁻¹ = Uᴴ := inv_eq_left_inv (mem_unitaryGroup_iff'.mp hU)
  obtain ⟨lam, hlam, h⟩ :=
    theorem_5_3 (X := U) ⟨Unitary.toUnits ⟨U, hU⟩, rfl⟩ (hUinv ▸ hd) E hμ
  exact ⟨lam, hlam, by rwa [condNumber_l2_of_mem_unitaryGroup hU, one_mul] at h⟩

/-! ### Theorem 5.4: the first-order perturbation of a simple eigenvalue -/

/-- **Theorem 5.4, (5.10).** Let `λ` be a simple eigenvalue of `A ∈ ℂ^{n×n}` with right and left
eigenvectors `x`, `y` (`A x = λ x`, `yᴴ A = λ yᴴ`), `‖x‖₂ = ‖y‖₂ = 1`, and `A(ε) = A + ε E` with
`‖E‖₂ = 1`. Denoting by `λ(ε)`, `x(ε)` an eigenvalue and eigenvector of `A(ε)` — a branch
differentiable at `ε = 0`, with `(A + ε E) x(ε) = λ(ε) x(ε)` in a neighborhood of `ε = 0`
(`theorem_5_4_branch`) — such that `λ(0) = λ` and `x(0) = x`,
`|∂λ/∂ε (0)| ≤ 1 / |yᴴ x|`. Backbone `Module.End.norm_deriv_eigenvalue_perturbation_le` with
`Module.End.eigenvalueCondNumber ℂ x y = 1 / |yᴴ x|` for unit vectors, and `yᴴ x ≠ 0` by
`theorem_5_4_inner_ne_zero`. The book's hypothesis that `A` be diagonalizable is not needed. -/
theorem theorem_5_4 {A E : Matrix (Fin n) (Fin n) ℂ} (hE : ‖E‖ = 1) {lam : ℂ}
    {x y : EuclideanSpace ℂ (Fin n)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hAx : toEuclideanLin A x = lam • x) (hAy : toEuclideanLin Aᴴ y = star lam • y)
    (hsimple : A.charpoly.rootMultiplicity lam = 1) {mu : ℂ → ℂ}
    {v : ℂ → EuclideanSpace ℂ (Fin n)} {v' : EuclideanSpace ℂ (Fin n)} {mu' : ℂ}
    (hv : HasDerivAt v v' 0) (hmu : HasDerivAt mu mu' 0)
    (heig : ∀ᶠ t in 𝓝 0, toEuclideanLin (A + t • E) (v t) = mu t • v t) (hlam : mu 0 = lam)
    (hv0 : v 0 = x) : ‖mu'‖ ≤ 1 / ‖inner ℂ y x‖ := by
  have hne : inner ℂ y x ≠ 0 :=
    Module.End.inner_ne_zero_of_finrank_maxGenEigenspace_eq_one hAx (by simp [← norm_pos_iff, hx])
      (inner_toEuclideanLin_eq_of_conjTranspose_eq hAy) (by simp [← norm_pos_iff, hy])
      (by rw [finrank_maxGenEigenspace_toEuclideanLin]; exact hsimple)
  have h := norm_deriv_eigenvalue_perturbation_le_of_eventually
    (A := toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A) (B := toEuclideanCLM (n := Fin n) (𝕜 := ℂ) E)
    hv hmu (heig.mono fun t ht => by
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply] at ht
      exact ht)
    (inner_toEuclideanLin_eq_of_conjTranspose_eq hAy) hlam (by rwa [hv0])
  rw [l2_opNorm_toEuclideanCLM, hE, one_mul, Module.End.eigenvalueCondNumber, hv0, hx, hy,
    one_mul] at h
  exact h

/-- **Theorem 5.4, the branch it presupposes.** At a simple eigenvalue `λ` of `A` with right
eigenvector `x ≠ 0` and left eigenvector `y ≠ 0`, there are `λ(ε)`, `x(ε)` with `λ(0) = λ`,
`x(0) = x`, `(A + ε E) x(ε) = λ(ε) x(ε)` in a neighborhood of `ε = 0`, `x(ε)` differentiable at
`0`, and `∂λ/∂ε (0) = yᴴ E x / yᴴ x` — the identity the book's proof derives. Backbone
`Module.End.hasDerivAt_eigenvalue_perturbation_of_finrank_eq_one`, built by the inverse function
theorem rather than by the continuity of the roots of the characteristic polynomial. -/
theorem theorem_5_4_branch {A : Matrix (Fin n) (Fin n) ℂ} (E : Matrix (Fin n) (Fin n) ℂ) {lam : ℂ}
    {x y : EuclideanSpace ℂ (Fin n)} (hx : x ≠ 0) (hy : y ≠ 0)
    (hAx : toEuclideanLin A x = lam • x) (hAy : toEuclideanLin Aᴴ y = star lam • y)
    (hsimple : A.charpoly.rootMultiplicity lam = 1) :
    ∃ (mu : ℂ → ℂ) (v : ℂ → EuclideanSpace ℂ (Fin n)) (v' : EuclideanSpace ℂ (Fin n)),
      mu 0 = lam ∧ v 0 = x ∧
        (∀ᶠ t in 𝓝 0, toEuclideanLin (A + t • E) (v t) = mu t • v t) ∧
        HasDerivAt v v' 0 ∧
        HasDerivAt mu (inner ℂ y (toEuclideanLin E x) / inner ℂ y x) 0 := by
  obtain ⟨mu, v, v', h0, hv0, heig, hv, hmu⟩ :=
    Module.End.hasDerivAt_eigenvalue_perturbation_of_finrank_eq_one
      (A := toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A) (B := toEuclideanCLM (n := Fin n) (𝕜 := ℂ) E)
      hAx hx (inner_toEuclideanLin_eq_of_conjTranspose_eq hAy) hy
      (by rw [coe_toEuclideanCLM_eq_toEuclideanLin, finrank_maxGenEigenspace_toEuclideanLin]
          exact hsimple)
  refine ⟨mu, v, v', h0, hv0, heig.mono fun t ht => ?_, hv, hmu⟩
  rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  exact ht

/-- **Theorem 5.4, the first step of its proof.** For a simple eigenvalue `λ` of `A ∈ ℂ^{n×n}`, a
right eigenvector `x ≠ 0` and a left eigenvector `y ≠ 0` satisfy `yᴴ x ≠ 0`. Backbone
`Module.End.inner_ne_zero_of_finrank_maxGenEigenspace_eq_one`, which needs no diagonalizability
(the book argues through the biorthogonality of the columns of `X` and `Y = X⁻ᴴ`). -/
theorem theorem_5_4_inner_ne_zero {A : Matrix (Fin n) (Fin n) ℂ} {lam : ℂ}
    {x y : EuclideanSpace ℂ (Fin n)} (hx : x ≠ 0) (hy : y ≠ 0)
    (hAx : toEuclideanLin A x = lam • x) (hAy : toEuclideanLin Aᴴ y = star lam • y)
    (hsimple : A.charpoly.rootMultiplicity lam = 1) : inner ℂ y x ≠ 0 :=
  Module.End.inner_ne_zero_of_finrank_maxGenEigenspace_eq_one hAx hx
    (inner_toEuclideanLin_eq_of_conjTranspose_eq hAy) hy
    (by rw [finrank_maxGenEigenspace_toEuclideanLin]; exact hsimple)

/-! ### (5.11): the condition number of an eigenvalue -/

/-- **(5.11).** The condition number of the eigenvalue `λ` with unit right and left eigenvectors
`x`, `y`: `κ(λ) = 1 / |yᴴ x| = 1 / |cos θ_λ|`, `θ_λ` the angle between `y` and `x`. -/
noncomputable def equation_5_11 (x y : EuclideanSpace ℂ (Fin n)) : ℝ := 1 / ‖inner ℂ y x‖

/-- For unit vectors, `κ(λ)` is the backbone's `Module.End.eigenvalueCondNumber ℂ x y =
‖x‖ ‖y‖ / |⟪y, x⟫|`. -/
theorem equation_5_11_eq_eigenvalueCondNumber {x y : EuclideanSpace ℂ (Fin n)} (hx : ‖x‖ = 1)
    (hy : ‖y‖ = 1) : equation_5_11 x y = Module.End.eigenvalueCondNumber ℂ x y := by
  rw [equation_5_11, Module.End.eigenvalueCondNumber, hx, hy, one_mul]

/-- **(5.11), `κ(λ) ≥ 1`.** For unit `x`, `y` with `yᴴ x ≠ 0` (which holds at a simple
eigenvalue, `theorem_5_4_inner_ne_zero`), `1 ≤ κ(λ)`; backbone
`Module.End.one_le_eigenvalueCondNumber`, Cauchy–Schwarz. -/
theorem equation_5_11_one_le {x y : EuclideanSpace ℂ (Fin n)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hne : inner ℂ y x ≠ 0) : 1 ≤ equation_5_11 x y := by
  rw [equation_5_11_eq_eigenvalueCondNumber hx hy]
  exact Module.End.one_le_eigenvalueCondNumber hne

/-- **(5.11), the normal case.** When `A` is normal the left and right eigenvectors of a simple
eigenvalue `λ` coincide up to a scalar, so that for unit `x`, `y`, `κ(λ) = 1 / ‖x‖₂² = 1`.
Backbone `Module.End.eigenvalueCondNumber_eq_one_of_isStarNormal`, which asks for geometric
simplicity; the algebraic simplicity of the book implies it
(`Module.End.finrank_eigenspace_le`). -/
theorem equation_5_11_normal {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A) {lam : ℂ}
    {x y : EuclideanSpace ℂ (Fin n)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hAx : toEuclideanLin A x = lam • x) (hAy : toEuclideanLin Aᴴ y = star lam • y)
    (hsimple : A.charpoly.rootMultiplicity lam = 1) : equation_5_11 x y = 1 := by
  have hx0 : x ≠ 0 := by simp [← norm_pos_iff, hx]
  have hgeom : Module.finrank ℂ (Module.End.eigenspace (toEuclideanLin A) lam) = 1 := by
    refine le_antisymm ?_ ?_
    · rw [← hsimple, ← finrank_maxGenEigenspace_toEuclideanLin]
      exact Submodule.finrank_mono (Module.End.eigenspace_le_maxGenEigenspace)
    · exact Submodule.one_le_finrank_iff.mpr
        ((Submodule.ne_bot_iff _).mpr ⟨x, Module.End.mem_eigenspace_iff.mpr hAx, hx0⟩)
  rw [equation_5_11_eq_eigenvalueCondNumber hx hy]
  exact Module.End.eigenvalueCondNumber_eq_one_of_isStarNormal
    (isStarNormal_toEuclideanLin_iff.mpr hA) hAx hx0
    (by rw [← toEuclideanLin_conjTranspose]; exact hAy) (by simp [← norm_pos_iff, hy]) hgeom

/-- **Unitary similarity preserves the conditioning** (§5.2.1, after (5.11)). Let `U` be unitary
and `Ã = Uᴴ A U`. If `x`, `y` are right and left eigenvectors of `A` for `λ`, then `Uᴴ x`, `Uᴴ y`
are right and left eigenvectors of `Ã` for `λ`, and the condition number is unchanged:
`κ̃(λ) = |yᴴ U Uᴴ x|⁻¹ = κ(λ)` — a unitary matrix changes neither Euclidean lengths nor the
angles between vectors. -/
theorem eigenvalueCondNumber_conj_unitary {A U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ unitaryGroup (Fin n) ℂ) {lam : ℂ} {x y : EuclideanSpace ℂ (Fin n)}
    (hAx : toEuclideanLin A x = lam • x) (hAy : toEuclideanLin Aᴴ y = star lam • y) :
    toEuclideanLin (Uᴴ * A * U) (toEuclideanLin Uᴴ x) = lam • toEuclideanLin Uᴴ x ∧
      toEuclideanLin (Uᴴ * A * U)ᴴ (toEuclideanLin Uᴴ y) = star lam • toEuclideanLin Uᴴ y ∧
      equation_5_11 (toEuclideanLin Uᴴ x) (toEuclideanLin Uᴴ y) = equation_5_11 x y := by
  have hUU : U * Uᴴ = 1 := mem_unitaryGroup_iff.mp hU
  refine ⟨?_, ?_, ?_⟩
  · simp only [toEuclideanLin_mul_apply]
    rw [← toEuclideanLin_mul_apply U, hUU, toEuclideanLin_one, LinearMap.id_apply, hAx, map_smul]
  · simp only [conjTranspose_mul, conjTranspose_conjTranspose, toEuclideanLin_mul_apply]
    rw [← toEuclideanLin_mul_apply U, hUU, toEuclideanLin_one, LinearMap.id_apply, hAy, map_smul]
  · have hU' : Uᴴ ∈ unitaryGroup (Fin n) ℂ := Unitary.star_mem hU
    simp only [equation_5_11]
    rw [← inner_toLp_mulVec_of_mem_unitaryGroup hU' (WithLp.ofLp y) (WithLp.ofLp x)]
    rfl

/-! ### Property 5.5: the first-order perturbation of an eigenvector -/

/-- **Property 5.5, for a Hermitian `A`.** Let `λ_k` be a simple eigenvalue of the Hermitian
matrix `A ∈ ℂ^{n×n}` with unit eigenvector `x_k`, let `δ_k = min_{j ≠ k} |λ_k − λ_j|` — the
distance from `λ_k` to the rest of the spectrum, `Metric.infDist λ_k (σ(A) \ {λ_k})` — and let
`ε ↦ (λ_k(ε), x_k(ε))` be a branch of eigenpairs of `A(ε) = A + ε E`, differentiable at `ε = 0`,
with `λ_k(0) = λ_k`, `x_k(0) = x_k` and normalized by `x_kᴴ x_k(ε) = 1`. Then
`‖∂x_k/∂ε (0)‖₂ ≤ ‖E‖₂ / δ_k`, hence `‖x_k(ε) − x_k‖₂ ≤ ε ‖E‖₂ / δ_k + o(ε)` as `ε → 0`, with
`κ(x_k) = 1 / δ_k` the condition number of the eigenvector. Backbone
`Module.End.norm_deriv_eigenvector_perturbation_le` — the normalization is the spectral-projector
normalization `P x_k(ε) = x_k`, `Module.End.spectralProjector_apply_of_finrank_eq_one` — with
`Module.End.eigenvectorCondNumber_eq_inv_dist_of_isSymmetric` evaluating the constant; the `o(ε)`
form is `HasDerivAt.isLittleO`. Errata: the book's `O(ε²)` needs a `C²` branch, its normalization
`‖x_k(ε)‖₂ = 1` differs from `x_kᴴ x_k(ε) = 1` by `1 + O(ε²)`, and for a non-normal `A` the constant
`1 / δ_k` is false. -/
theorem property_5_5 {A E : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) {lam : ℝ}
    {x : EuclideanSpace ℂ (Fin n)} (hx : ‖x‖ = 1) (hAx : toEuclideanLin A x = (lam : ℂ) • x)
    (hsimple : A.charpoly.rootMultiplicity (lam : ℂ) = 1) {δ : ℝ}
    (hδ : δ = Metric.infDist (lam : ℂ) (spectrum ℂ A \ {(lam : ℂ)})) {mu : ℂ → ℂ}
    {v : ℂ → EuclideanSpace ℂ (Fin n)} {v' : EuclideanSpace ℂ (Fin n)} {mu' : ℂ}
    (hv : HasDerivAt v v' 0) (hmu : HasDerivAt mu mu' 0)
    (heig : ∀ t, toEuclideanLin (A + t • E) (v t) = mu t • v t) (hlam : mu 0 = lam)
    (hv0 : v 0 = x) (hnorm : ∀ t, inner ℂ x (v t) = 1) :
    ‖v'‖ ≤ ‖E‖ / δ ∧
      ∃ o : ℂ → ℝ, o =o[𝓝 0] (fun ε : ℂ => ε) ∧ ∀ ε, ‖v ε - x‖ ≤ ‖ε‖ * (‖E‖ / δ) + o ε := by
  have hx0 : x ≠ 0 := by simp [← norm_pos_iff, hx]
  have hAy : toEuclideanLin Aᴴ x = star (lam : ℂ) • x := by rwa [hA.eq, Complex.star_def,
    Complex.conj_ofReal]
  set A' : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A with hA'
  set E' : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    toEuclideanCLM (n := Fin n) (𝕜 := ℂ) E with hE'
  have hA'lin : (A' : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) = toEuclideanLin A :=
    rfl
  have hsimple' : Module.finrank ℂ (Module.End.maxGenEigenspace
      (A' : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) (lam : ℂ)) = 1 := by
    rw [hA'lin, finrank_maxGenEigenspace_toEuclideanLin]
    exact hsimple
  have hAx' : (A' : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) x = (lam : ℂ) • x := by
    rw [hA'lin]; exact hAx
  have hw' : ∀ z, inner ℂ x ((A' : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) z) =
      (lam : ℂ) * inner ℂ x z := fun z => by
    rw [hA'lin]; exact inner_toEuclideanLin_eq_of_conjTranspose_eq hAy z
  have hP : ∀ t, Krylov.spectralProjector
      (A' : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) (· = (lam : ℂ)) (v t) = v 0 :=
    fun t => by
      rw [Module.End.spectralProjector_apply_of_finrank_eq_one hAx' hx0 hw' hx0 hsimple', hnorm,
        inner_self_eq_norm_sq_to_K, hx, hv0]
      simp
  have hbound : ‖v'‖ ≤ ‖E‖ / δ := by
    have h := Module.End.norm_deriv_eigenvector_perturbation_le (A := A') (B := E') hv hmu
      (fun t => by
        have ht := heig t
        rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply] at ht
        exact ht) hlam hP
    rw [hA'lin, Module.End.eigenvectorCondNumber_eq_inv_dist_of_isSymmetric
      (isSymmetric_toEuclideanLin_iff.mpr hA), spectrum_toLpLin, hE',
      l2_opNorm_toEuclideanCLM, hv0, hx, mul_one, ← hδ] at h
    rwa [div_eq_inv_mul]
  refine ⟨hbound, fun ε => ‖v ε - x - ε • v'‖, ?_, fun ε => ?_⟩
  · have h := hv.isLittleO
    simpa [hv0] using h.norm_left
  · calc ‖v ε - x‖ = ‖ε • v' + (v ε - x - ε • v')‖ := by congr 1; abel
      _ ≤ ‖ε • v'‖ + ‖v ε - x - ε • v'‖ := norm_add_le _ _
      _ ≤ ‖ε‖ * (‖E‖ / δ) + ‖v ε - x - ε • v'‖ := by
          rw [norm_smul]
          gcongr

/-! ### §5.2.2: a posteriori estimates -/

/-- **Theorem 5.5, (5.13).** Let `A ∈ ℂ^{n×n}` be Hermitian and `(λ̂, x̂)`, `x̂ ≠ 0`, a computed
approximation of an eigenpair, with residual `r̂ = A x̂ − λ̂ x̂`. Then
`min_{λ_i ∈ σ(A)} |λ̂ − λ_i| ≤ ‖r̂‖₂ / ‖x̂‖₂`. Backbone
`LinearMap.IsSymmetric.exists_hasEigenvalue_dist_le` for `toEuclideanLin A`, whose eigenvalues
are the spectrum of `A`. The book's `λ̂` is real, as a Rayleigh quotient of a Hermitian matrix. -/
theorem theorem_5_5 {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (lam : ℝ)
    {x : EuclideanSpace ℂ (Fin n)} (hx : x ≠ 0) :
    ∃ μ ∈ spectrum ℂ A, ‖(lam : ℂ) - μ‖ ≤ ‖toEuclideanLin A x - (lam : ℂ) • x‖ / ‖x‖ := by
  obtain ⟨μ, hμ, h⟩ :=
    (isSymmetric_toEuclideanLin_iff.mpr hA).exists_hasEigenvalue_dist_le lam hx
  exact ⟨μ, (hasEigenvalue_toEuclideanLin_iff A μ).mp hμ, by rwa [norm_sub_rev]⟩

/-- **Property 5.6, (5.15).** Under the assumptions of Theorem 5.5, let `{u_i}` be the
orthonormal eigenvectors of `A` with eigenvalues `λ_i` (Mathlib's
`Matrix.IsHermitian.eigenvectorBasis`, `Matrix.IsHermitian.eigenvalues`), let `s` be a set of
indices (the book's `i = 1, …, m`) and suppose `|λ_i − λ̂| ≥ δ > 0` for `i ∉ s`. Then the
Euclidean distance from `x̂` to the space `U_m` generated by the `u_i`, `i ∈ s`, satisfies
`d(x̂, U_m) ≤ ‖r̂‖₂ / δ`. Backbone
`LinearMap.IsSymmetric.dist_eigenvectorSpan_le_norm_residual_div`, the distance being attained at
the orthogonal projection (`Submodule.starProjection_minimal`). The book's further hypothesis
`|λ_i − λ̂| ≤ ‖r̂‖₂` for `i ∈ s` plays no role and is dropped. -/
theorem property_5_6 {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (lam : ℝ)
    (x : EuclideanSpace ℂ (Fin n)) (s : Finset (Fin n)) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i ∉ s, δ ≤ |hA.eigenvalues i - lam|) :
    Metric.infDist x (Submodule.span ℂ (hA.eigenvectorBasis '' s) : Set (EuclideanSpace ℂ (Fin n)))
      ≤ ‖toEuclideanLin A x - (lam : ℂ) • x‖ / δ := by
  set hA' := isSymmetric_toEuclideanLin_iff.mpr hA
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  have hspan : Submodule.span ℂ (hA.eigenvectorBasis '' s) =
      hA'.eigenvectorSpan finrank_euclideanSpace (s.map e.symm.toEmbedding) := by
    rw [LinearMap.IsSymmetric.eigenvectorSpan, Finset.coe_map, Set.image_image]
    congr 1
    refine Set.image_congr fun i _ => ?_
    simp only [Matrix.IsHermitian.eigenvectorBasis, OrthonormalBasis.reindex_apply]
    rfl
  rw [hspan]
  refine (Metric.infDist_le_dist_of_mem
    (Submodule.starProjection_apply_mem (hA'.eigenvectorSpan finrank_euclideanSpace
      (s.map e.symm.toEmbedding)) x)).trans ?_
  rw [dist_eq_norm]
  refine hA'.dist_eigenvectorSpan_le_norm_residual_div finrank_euclideanSpace _ lam x hδ
    fun i hi => ?_
  have hi' : e i ∉ s := fun h => hi (Finset.mem_map.mpr ⟨e i, h, e.symm_apply_apply i⟩)
  have h := hsep (e i) hi'
  rwa [show hA.eigenvalues (e i) = hA'.eigenvalues finrank_euclideanSpace i from
    congrArg (hA'.eigenvalues finrank_euclideanSpace) (e.symm_apply_apply i)] at h

/-- **Property 5.7.** Let `A ∈ ℂ^{n×n}` be diagonalizable, `X⁻¹ A X = diag(λ_1, …, λ_n)` with `X`
nonsingular. If for some `ε > 0` the residual `r̂ = A x̂ − λ̂ x̂` of an approximate pair
`(λ̂, x̂)`, `x̂ ≠ 0`, satisfies `‖r̂‖₂ ≤ ε ‖x̂‖₂`, then
`min_{λ_i ∈ σ(A)} |λ̂ − λ_i| ≤ ε ‖X⁻¹‖₂ ‖X‖₂`. Backbone `Matrix.bauer_fike_residual` applied to
the unit vector `x̂ / ‖x̂‖₂`. -/
theorem property_5_7 {A X : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X) {d : Fin n → ℂ}
    (hD : X⁻¹ * A * X = diagonal d) (lam : ℂ) {x : EuclideanSpace ℂ (Fin n)} (hx : x ≠ 0)
    {ε : ℝ} (hr : ‖toEuclideanLin A x - lam • x‖ ≤ ε * ‖x‖) :
    ∃ μ ∈ spectrum ℂ A, ‖lam - μ‖ ≤ ε * (‖X⁻¹‖ * ‖X‖) := by
  have hdet := (isUnit_iff_isUnit_det X).mp hX
  have hA : A = X * diagonal d * X⁻¹ := by
    rw [← hD, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv X hdet, Matrix.mul_one,
      ← Matrix.mul_assoc, mul_nonsing_inv X hdet, Matrix.one_mul]
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖(‖x‖⁻¹ : ℂ) • x‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxn,
      inv_mul_cancel₀ hxn.ne']
  obtain ⟨i, hi⟩ := bauer_fike_residual X d hX hu lam
  refine ⟨d i, ?_, ?_⟩
  · have hspec := spectrum.units_conjugate' (R := ℂ) (a := A) (u := hX.unit)
    rw [coe_units_inv, IsUnit.unit_spec, hD, spectrum_diagonal] at hspec
    rw [← hspec]
    exact ⟨i, rfl⟩
  · have hres : ‖toEuclideanLin (X * diagonal d * X⁻¹) ((‖x‖⁻¹ : ℂ) • x) - lam • (‖x‖⁻¹ : ℂ) • x‖
        ≤ ε := by
      rw [← hA, map_smul, smul_comm lam, ← smul_sub, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hxn, inv_mul_le_iff₀ hxn, mul_comm]
      exact hr
    calc ‖lam - d i‖ ≤ NormedRing.condNumber X *
          ‖toEuclideanLin (X * diagonal d * X⁻¹) ((‖x‖⁻¹ : ℂ) • x) - lam • (‖x‖⁻¹ : ℂ) • x‖ := hi
      _ ≤ NormedRing.condNumber X * ε :=
          mul_le_mul_of_nonneg_left hres (NormedRing.condNumber_nonneg X)
      _ = ε * (‖X⁻¹‖ * ‖X‖) := by
          rw [NormedRing.condNumber, ← nonsing_inv_eq_ringInverse]
          ring

end QuarteroniSaccoSaleri.Chapter05
