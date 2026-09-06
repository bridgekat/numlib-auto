import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Topology.Algebra.Polynomial
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Analysis.InnerProductSpace.Projection.Compression

/-!
# Polynomials in a symmetric operator: spectral norm bounds

`‖p(A) x‖ ≤ max_{λ ∈ σ(A)} |p(λ)| ‖x‖` and the energy-norm analogue for symmetric `A` in finite
dimension (via `LinearMap.IsSymmetric.eigenvectorBasis`), and the real-interval form used by the
Chebyshev bounds: for `A.IsSymmetricBoundedBy a b`, `‖p(A) x‖ ≤ sup_{[a,b]} |p| ‖x‖` in *any*
inner product space, obtained by compressing `A` to the finite-dimensional
`span {x, A x, …, A^(deg p) x}` (the "compression trick";
Saad, *Iterative Methods*[^saad-iterative] Lemma 6.28/6.31 proofs,
Saad, *Large Eigenvalue Problems*[^saad-eigenvalue] Lemma 6.1,
Atkinson–Han[^atkinson-han] (5.6.16)–(5.6.19), Meurant–Strakoš[^meurant-strakos] (3.7)–(3.8)).
The Hilbert-space version via the continuous functional calculus is a phase-2 alternative, not
needed for the statements.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
[^saad-eigenvalue]: Yousef Saad, *Numerical Methods for Large Eigenvalue Problems*, 2nd edition,
  SIAM, 2011.
[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
[^meurant-strakos]: Gérard Meurant and Zdeněk Strakoš, *The Lanczos and conjugate gradient
  algorithms in finite precision arithmetic*, Acta Numerica (2006), 471–542.
-/

open Polynomial

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

section FiniteDimensional

variable [FiniteDimensional 𝕜 E]

namespace LinearMap.IsSymmetric

variable {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
include hA

/-- In the eigenvector basis, `A^k` acts diagonally by `λ^k`. -/
private theorem repr_pow_apply {n : ℕ} (hn : Module.finrank 𝕜 E = n) (k : ℕ) (x : E) (i : Fin n) :
    (hA.eigenvectorBasis hn).repr ((A ^ k) x) i =
      (hA.eigenvalues hn i : 𝕜) ^ k * (hA.eigenvectorBasis hn).repr x i := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, ih, hA.eigenvectorBasis_apply_self_apply hn]
      ring

/-- In the eigenvector basis, `p(A)` acts diagonally by `p(λ)`.  This is the expansion behind
every bound on `p(A)` in terms of the values of `p` on the spectrum, here and in the Krylov
eigenvalue estimates. -/
theorem repr_aeval_apply {n : ℕ} (hn : Module.finrank 𝕜 E = n) (p : 𝕜[X]) (x : E)
    (i : Fin n) :
    (hA.eigenvectorBasis hn).repr (aeval A p x) i =
      p.eval (hA.eigenvalues hn i : 𝕜) * (hA.eigenvectorBasis hn).repr x i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_mul]
  | monomial k c =>
      have hmon : aeval A (monomial k c) x = c • (A ^ k) x := by
        simp [aeval_monomial]
      rw [hmon, map_smul, PiLp.smul_apply, smul_eq_mul, hA.repr_pow_apply hn, eval_monomial]
      ring

/-- The quadratic form in the eigenvector basis. -/
private theorem re_inner_apply_self {n : ℕ} (hn : Module.finrank 𝕜 E = n) (x : E) :
    RCLike.re (inner 𝕜 (A x) x) =
      ∑ i, hA.eigenvalues hn i * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  rw [← (hA.eigenvectorBasis hn).sum_inner_mul_inner (A x) x, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hA x (hA.eigenvectorBasis hn i), hA.apply_eigenvectorBasis hn, inner_smul_right,
    ← inner_conj_symm x (hA.eigenvectorBasis hn i), mul_assoc, RCLike.conj_mul,
    OrthonormalBasis.repr_apply_apply]
  simp

/-- Eigenvalues of `p(A)` are `p(λ)`; hence `‖p(A) x‖ ≤ C ‖x‖` whenever `‖p(λ)‖ ≤ C` on the
spectrum. -/
theorem norm_aeval_apply_le {C : ℝ} (p : 𝕜[X])
    (hC : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → ‖p.eval μ‖ ≤ C) (x : E) :
    ‖aeval A p x‖ ≤ C * ‖x‖ := by
  set n := Module.finrank 𝕜 E with hn'
  have hn : Module.finrank 𝕜 E = n := rfl
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · have : Subsingleton E := Module.finrank_zero_iff.mp (hn'.symm.trans h0)
    simp [Subsingleton.elim x 0]
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ (hA.hasEigenvalue_eigenvalues hn ⟨0, h0⟩))
  have key : ‖aeval A p x‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    rw [← (hA.eigenvectorBasis hn).sum_sq_norm_inner_right (aeval A p x), mul_pow,
      ← (hA.eigenvectorBasis hn).sum_sq_norm_inner_right x, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← OrthonormalBasis.repr_apply_apply, ← OrthonormalBasis.repr_apply_apply,
      hA.repr_aeval_apply hn, norm_mul, mul_pow]
    gcongr
    exact hC _ (hA.hasEigenvalue_eigenvalues hn i)
  have := Real.sqrt_le_sqrt key
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (mul_nonneg hC0 (norm_nonneg x))] at this

/-- Energy-norm version for symmetric coercive `A`. -/
theorem energyNorm_aeval_apply_le (hA' : A.IsSymmetricCoercive) {C : ℝ} (p : 𝕜[X])
    (hC : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → ‖p.eval μ‖ ≤ C) (x : E) :
    energyNorm A (aeval A p x) ≤ C * energyNorm A x := by
  set n := Module.finrank 𝕜 E with hn'
  have hn : Module.finrank 𝕜 E = n := rfl
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · have : Subsingleton E := Module.finrank_zero_iff.mp (hn'.symm.trans h0)
    simp [Subsingleton.elim x 0, energyNorm]
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ (hA.hasEigenvalue_eigenvalues hn ⟨0, h0⟩))
  have hpos : ∀ i : Fin n, 0 ≤ hA.eigenvalues hn i := fun i => by
    have h := hA'.re_pos_of_hasEigenvalue (hA.hasEigenvalue_eigenvalues hn i)
    simpa using h.le
  have key : RCLike.re (inner 𝕜 (A (aeval A p x)) (aeval A p x)) ≤
      C ^ 2 * RCLike.re (inner 𝕜 (A x) x) := by
    rw [hA.re_inner_apply_self hn, hA.re_inner_apply_self hn, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hA.repr_aeval_apply hn, norm_mul, mul_pow]
    have hle : ‖p.eval (hA.eigenvalues hn i : 𝕜)‖ ^ 2 ≤ C ^ 2 := by
      gcongr
      exact hC _ (hA.hasEigenvalue_eigenvalues hn i)
    have hnn : 0 ≤ hA.eigenvalues hn i * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 :=
      mul_nonneg (hpos i) (sq_nonneg _)
    linarith [mul_le_mul_of_nonneg_left hle hnn]
  calc energyNorm A (aeval A p x) ≤ Real.sqrt (C ^ 2 * RCLike.re (inner 𝕜 (A x) x)) :=
        Real.sqrt_le_sqrt key
    _ = C * energyNorm A x := by
        rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC0]; rfl

omit [FiniteDimensional 𝕜 E] in
/-- The eigenvalues of a symmetric operator are real. -/
theorem im_eq_zero_of_hasEigenvalue {μ : 𝕜} (hμ : Module.End.HasEigenvalue A μ) :
    RCLike.im μ = 0 :=
  RCLike.conj_eq_iff_im.mp (hA.conj_eigenvalue_eq_self hμ)

end LinearMap.IsSymmetric

/-- Saad, *Iterative Methods*, Prop 6.32 (diagonalizable `A`): if `A` is conjugate by `X` to an
operator `D` whose polynomial images satisfy `‖p(D) y‖ ≤ C ‖y‖`, then `‖p(A) x‖ ≤ κ(X) C ‖x‖`,
where `κ(X) = ‖X‖ ‖X⁻¹‖` is the condition number of `X`. Stated with `D` symmetric so that the
finite-dimensional bound above applies. -/
theorem norm_aeval_apply_le_of_conj {A D : E →ₗ[𝕜] E} (X : E ≃L[𝕜] E)
    (hconj : A = (X : E →ₗ[𝕜] E) ∘ₗ D ∘ₗ (X.symm : E →ₗ[𝕜] E)) (hD : D.IsSymmetric) {C : ℝ}
    (p : 𝕜[X]) (hC : ∀ μ : 𝕜, Module.End.HasEigenvalue D μ → ‖p.eval μ‖ ≤ C) (x : E) :
    ‖aeval A p x‖ ≤ ‖(X : E →L[𝕜] E)‖ * ‖(X.symm : E →L[𝕜] E)‖ * C * ‖x‖ := by
  have hAe : A = (X.toLinearEquiv.conjAlgEquiv 𝕜) D := hconj
  have haeval : aeval A p = (X.toLinearEquiv.conjAlgEquiv 𝕜) (aeval D p) := by
    rw [hAe, ← aeval_algHom_apply]
  have hx : aeval A p x = X (aeval D p (X.symm x)) := by rw [haeval]; rfl
  rcases Nat.eq_zero_or_pos (Module.finrank 𝕜 E) with h0 | h0
  · have : Subsingleton E := Module.finrank_zero_iff.mp h0
    simp [Subsingleton.elim x 0]
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ (hD.hasEigenvalue_eigenvalues rfl ⟨0, h0⟩))
  calc ‖aeval A p x‖ = ‖X (aeval D p (X.symm x))‖ := by rw [hx]
    _ ≤ ‖(X : E →L[𝕜] E)‖ * ‖aeval D p (X.symm x)‖ :=
        (X : E →L[𝕜] E).le_opNorm (aeval D p (X.symm x))
    _ ≤ ‖(X : E →L[𝕜] E)‖ * (C * ‖X.symm x‖) :=
        mul_le_mul_of_nonneg_left (hD.norm_aeval_apply_le p hC _) (norm_nonneg _)
    _ ≤ ‖(X : E →L[𝕜] E)‖ * (C * (‖(X.symm : E →L[𝕜] E)‖ * ‖x‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left ((X.symm : E →L[𝕜] E).le_opNorm x) hC0) (norm_nonneg _)
    _ = ‖(X : E →L[𝕜] E)‖ * ‖(X.symm : E →L[𝕜] E)‖ * C * ‖x‖ := by ring

end FiniteDimensional

section Compression

/-! ### The compression trick

Everything a Krylov method does in `m` steps happens inside the finite-dimensional
`𝒦_{m+1}`, on which `A` acts (up to the last step) as its compression. -/

namespace compression

variable (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]

/-- Quadratic-form bounds pass to compressions. -/
theorem isSymmetricBoundedBy {lmin lmax : ℝ} (hA : A.IsSymmetricBoundedBy lmin lmax) :
    (compression A K).IsSymmetricBoundedBy lmin lmax :=
  hA.of_inner_eq (compression.isSymmetric A K hA.isSymmetric) K.subtypeₗᵢ
    fun x => compression.inner_apply A K x x

/-- Coercivity passes to compressions, with the same constant: the compression of a symmetric
coercive `A` to `K` is symmetric coercive on `K`. Its quadratic form is the restriction of that of
`A` (`compression.inner_apply`), so the defining inequality is inherited verbatim, and the
finite-dimensional energy-norm bounds may be applied inside `K`. -/
theorem isSymmetricCoercive (hA : A.IsSymmetricCoercive) :
    (compression A K).IsSymmetricCoercive := by
  obtain ⟨c, hc, hcA⟩ := hA.isCoercive
  refine ⟨compression.isSymmetric A K hA.isSymmetric, c, hc, fun x => ?_⟩
  rw [compression.inner_apply A K x x]
  exact hcA (x : E)

theorem energyInner_apply (x y : K) : energyInner (compression A K) x y = energyInner A x y :=
  compression.inner_apply A K x y

/-- Measuring a vector of `K` in the energy norm of the compression gives the same number as
measuring it in the energy norm of `A`. This is what lets the compression trick carry an
energy-norm bound proved in the finite-dimensional `K` back to `E` with no constant lost. -/
theorem energyNorm_apply (x : K) : energyNorm (compression A K) x = energyNorm A x := by
  rw [energyNorm, energyNorm, compression.inner_apply A K x x]

end compression

end Compression

section Interval

/-- The image of a compact interval under `|p|` is bounded above. -/
private theorem bddAbove_image_abs_eval (p : ℝ[X]) (a b : ℝ) :
    BddAbove ((fun t => |p.eval t|) '' Set.Icc a b) :=
  (isCompact_Icc.image p.continuous.abs).bddAbove

/-- For a symmetric operator with quadratic form in `[a, b]`, the values of a real polynomial at
the (real) eigenvalues are bounded by its sup over `[a, b]`. -/
private theorem norm_eval_map_le_sSup {A : E →ₗ[𝕜] E} {a b : ℝ}
    (hA : A.IsSymmetricBoundedBy a b) (p : ℝ[X]) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue A μ) :
    ‖(p.map (algebraMap ℝ 𝕜)).eval μ‖ ≤ sSup ((fun t => |p.eval t|) '' Set.Icc a b) := by
  have hre : ((RCLike.re μ : ℝ) : 𝕜) = μ :=
    RCLike.conj_eq_iff_re.mp (RCLike.conj_eq_iff_im.mpr
      (hA.isSymmetric.im_eq_zero_of_hasEigenvalue hμ))
  have hmem : RCLike.re μ ∈ Set.Icc a b := hA.re_mem_Icc_of_hasEigenvalue hμ
  have hμ' : μ = algebraMap ℝ 𝕜 (RCLike.re μ) := by
    rw [RCLike.algebraMap_eq_ofReal]; exact hre.symm
  have heval : (p.map (algebraMap ℝ 𝕜)).eval μ = ((p.eval (RCLike.re μ) : ℝ) : 𝕜) := by
    conv_lhs => rw [hμ']
    rw [eval_map, eval₂_at_apply, RCLike.algebraMap_eq_ofReal]
  rw [heval, RCLike.norm_ofReal]
  exact le_csSup (bddAbove_image_abs_eval p a b) ⟨RCLike.re μ, hmem, rfl⟩

end Interval

section CompressionSpace

/-- The Krylov subspace used by the compression trick: it contains `x` and `p(A) x` can be
computed inside it. -/
private noncomputable def compressionSpace (A : E →ₗ[𝕜] E) (d : ℕ) (x : E) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range fun i : Fin (d + 1) => (A ^ (i : ℕ)) x)

private instance (A : E →ₗ[𝕜] E) (d : ℕ) (x : E) :
    FiniteDimensional 𝕜 (compressionSpace A d x) :=
  FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)

private theorem pow_mem_compressionSpace {A : E →ₗ[𝕜] E} {d : ℕ} (x : E) {i : ℕ} (hi : i ≤ d) :
    (A ^ i) x ∈ compressionSpace A d x :=
  Submodule.subset_span ⟨⟨i, Nat.lt_succ_of_le hi⟩, rfl⟩

end CompressionSpace

namespace LinearMap.IsSymmetricBoundedBy

variable {A : E →ₗ[𝕜] E} {a b : ℝ} (hA : A.IsSymmetricBoundedBy a b)
include hA

/-- Real-interval form, in any inner product space: `‖p(A) x‖ ≤ sup_{[a,b]} |p| ‖x‖` for a real
polynomial `p`. -/
theorem norm_aeval_map_apply_le (p : ℝ[X]) (x : E) :
    ‖aeval A (p.map (algebraMap ℝ 𝕜)) x‖ ≤
      sSup ((fun t => |p.eval t|) '' Set.Icc a b) * ‖x‖ := by
  set q := p.map (algebraMap ℝ 𝕜) with hq
  set K := compressionSpace A p.natDegree x with hK
  have hxK : x ∈ K := by
    have := pow_mem_compressionSpace (A := A) (d := p.natDegree) (i := 0) x (Nat.zero_le _)
    simpa [hK] using this
  have hpow : ∀ i ≤ q.natDegree, (A ^ i) ((⟨x, hxK⟩ : K) : E) ∈ K := fun i hi =>
    pow_mem_compressionSpace x (hi.trans (hq ▸ natDegree_map_le))
  have h1 : ((aeval (compression A K) q (⟨x, hxK⟩ : K) : K) : E) = aeval A q x :=
    compression.aeval_apply_of_forall_pow_mem A K q hpow
  have h2 := (compression.isSymmetricBoundedBy A K hA).isSymmetric.norm_aeval_apply_le
    (C := sSup ((fun t => |p.eval t|) '' Set.Icc a b)) q
    (fun _ hμ => norm_eval_map_le_sSup (compression.isSymmetricBoundedBy A K hA) p hμ)
    (⟨x, hxK⟩ : K)
  have h3 : ‖aeval (compression A K) q (⟨x, hxK⟩ : K)‖ = ‖aeval A q x‖ := by rw [← h1]; rfl
  rwa [h3, show ‖(⟨x, hxK⟩ : K)‖ = ‖x‖ from rfl] at h2

/-- Energy-norm version (`0 < a`). -/
theorem energyNorm_aeval_map_apply_le (ha : 0 < a) (p : ℝ[X]) (x : E) :
    energyNorm A (aeval A (p.map (algebraMap ℝ 𝕜)) x) ≤
      sSup ((fun t => |p.eval t|) '' Set.Icc a b) * energyNorm A x := by
  set q := p.map (algebraMap ℝ 𝕜) with hq
  set K := compressionSpace A p.natDegree x with hK
  have hxK : x ∈ K := by
    have := pow_mem_compressionSpace (A := A) (d := p.natDegree) (i := 0) x (Nat.zero_le _)
    simpa [hK] using this
  have hpow : ∀ i ≤ q.natDegree, (A ^ i) ((⟨x, hxK⟩ : K) : E) ∈ K := fun i hi =>
    pow_mem_compressionSpace x (hi.trans (hq ▸ natDegree_map_le))
  have h1 : ((aeval (compression A K) q (⟨x, hxK⟩ : K) : K) : E) = aeval A q x :=
    compression.aeval_apply_of_forall_pow_mem A K q hpow
  have hAK := compression.isSymmetricBoundedBy A K hA
  have h2 := hAK.isSymmetric.energyNorm_aeval_apply_le (hAK.isSymmetricCoercive ha)
    (C := sSup ((fun t => |p.eval t|) '' Set.Icc a b)) q
    (fun _ hμ => norm_eval_map_le_sSup hAK p hμ) (⟨x, hxK⟩ : K)
  rw [compression.energyNorm_apply A K, compression.energyNorm_apply A K, h1] at h2
  exact h2

end LinearMap.IsSymmetricBoundedBy
