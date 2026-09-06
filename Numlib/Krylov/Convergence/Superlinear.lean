import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Numlib.Analysis.InnerProductSpace.CompactSpectral
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Krylov.CG
import Numlib.Krylov.Convergence.CG
import Numlib.Krylov.Convergence.Polynomial
import Numlib.Krylov.Iterate

/-!
# Superlinear convergence of conjugate gradients for `A = 1 - K`

Winther's theorem: for a compact perturbation `A = 1 - K` of the identity on a Hilbert space,
with `K` self-adjoint and `A` positive definite, the conjugate gradient method converges
*superlinearly* — the error after `k` steps is at most `c_k^k` times the initial error, with
`c_k → 0`. No Chebyshev bound can do this: the rate of
`Krylov.IsGalerkinIterate.energyNorm_error_le` depends only on the enclosing interval `[δ, Δ]` of
the spectrum, and does not improve with `k`. What drives the improvement here is that the
eigenvalues of `K` accumulate only at `0`, so a polynomial of degree `k` can annihilate the `k`
largest of them and still be small at all the others.

The classical proof ([Atkinson–Han][han2009theoretical] Thm 5.6.2, after [Winther][winther1980some])
reads the eigen-decomposition of `K` off the spectral theorem for compact self-adjoint operators.
What the argument actually consumes is one step further on — the *enumeration* of the eigenvalues as
a sequence with `|λ|` decreasing — which rests on the eigenvalues accumulating only at `0` and needs
the index type to be `ℕ`. That enumeration is `ContinuousLinearMap.IsSymmetric.eigenvalueSeq`, with
the matching orthonormal basis `ContinuousLinearMap.IsSymmetric.eigenvectorHilbertBasis`.

The statements here take the *enumerated* decomposition as data: a Hilbert basis
`φ : HilbertBasis ℕ 𝕜 E` of eigenvectors of `K` with real eigenvalues `λ`, ordered so that `|λ|`
is antitone, together with the enclosure `0 < δ ≤ 1 - λ j ≤ Δ`. Compactness of `K` is then never
used — it is what produces the data, not what the proof needs, and
`Krylov.winther_of_isCompactOperator` is the same theorem with the data discharged, proved without
changing a line above it. Everything else is proved: the
quadratic-form bounds `LinearMap.IsSymmetricBoundedBy δ Δ` follow from the decomposition by
Parseval (`Krylov.isSymmetricBoundedBy_of_eq_one_sub`), and so does the operator bound
`LinearMap.IsSymmetric.norm_aeval_map_apply_le_of_hilbertBasis`, the discrete counterpart of the
interval bound `LinearMap.IsSymmetricBoundedBy.norm_aeval_map_apply_le`. Once the decreasing
enumeration is available the data become a conclusion and these statements specialize to the
book's.

The competitor polynomial is `Krylov.wintherPoly`, `Q_k(t) = ∏_{j < k} (1 - λ_j - t)/(1 - λ_j)`,
which is `1` at `0` and vanishes at the `k` leading eigenvalues `1 - λ_j` of `A`; at the
remaining ones `|Q_k| ≤ ∏_{j < k} 2 |λ_j|/(1 - λ_j)`, because `|λ_i - λ_j| ≤ 2 |λ_j|` once
`|λ_i| ≤ |λ_j|`. Galerkin optimality turns this into
`Krylov.IsGalerkinIterate.norm_error_le_prod`, and the arithmetic–geometric mean inequality turns
the product into the `k`-th power of `Krylov.wintherRate`, which tends to `0` by Cesàro
convergence (`Krylov.winther_rate_tendsto_zero`).

## Implementation notes

`Krylov.winther` is proved with `c_k = (Δ/δ)^{1/(2k)} (2/k) ∑_{j < k} |λ_j|/(1 - λ_j)`, where
Atkinson–Han state `(Δ/δ)^{3/(2k)}` in their (5.6.21). The exponent `3/2` is the price of their
route through the residual, `‖x* - x_k‖ ≤ ‖A⁻¹‖ ‖r̃_k‖` and `‖r₀‖ ≤ ‖A‖ ‖x* - x₀‖`; measuring the
error directly in the energy norm at both ends costs only the one conversion
`√δ ‖v‖ ≤ ‖v‖_A ≤ √Δ ‖v‖`. Since `δ ≤ Δ`, the constant proved here is the smaller one, and the
book's form follows from it.
-/

open Filter Polynomial Topology

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ### Parseval's identity -/

namespace HilbertBasis

/-- **Parseval's identity** in the summable form the eigenvector estimates use:
`∑ᵢ |⟪φᵢ, v⟫|² = ‖v‖²`. -/
theorem hasSum_norm_inner_sq (φ : HilbertBasis ι 𝕜 E) (v : E) :
    HasSum (fun i => ‖inner 𝕜 (φ i) v‖ ^ 2) (‖v‖ ^ 2) := by
  have key : (fun i => ‖inner 𝕜 (φ i) v‖ ^ 2)
      = fun i => RCLike.re (inner 𝕜 v (φ i) * inner 𝕜 (φ i) v) := by
    funext i
    rw [← inner_conj_symm v (φ i), RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  rw [key, ← inner_self_eq_norm_sq (𝕜 := 𝕜) v]
  exact (φ.hasSum_inner_mul_inner v v).map (RCLike.re : 𝕜 →+ ℝ) RCLike.continuous_re

end HilbertBasis

/-! ### Operators diagonal in a Hilbert basis -/

namespace LinearMap.IsSymmetric

variable {A : E →ₗ[𝕜] E} {ν : ι → ℝ}

/-- A symmetric operator diagonal in `φ` multiplies the `i`-th coefficient by `νᵢ`. -/
theorem inner_apply_of_apply_eq_smul (hA : A.IsSymmetric) (φ : HilbertBasis ι 𝕜 E)
    (hν : ∀ i, A (φ i) = ((ν i : ℝ) : 𝕜) • φ i) (v : E) (i : ι) :
    inner 𝕜 (φ i) (A v) = ((ν i : ℝ) : 𝕜) * inner 𝕜 (φ i) v := by
  rw [← hA (φ i) v, hν i, inner_smul_left, RCLike.conj_ofReal]

/-- The quadratic form of an operator diagonal in `φ` is `∑ᵢ νᵢ |⟪φᵢ, v⟫|²`. -/
theorem hasSum_re_inner_apply_self (hA : A.IsSymmetric) (φ : HilbertBasis ι 𝕜 E)
    (hν : ∀ i, A (φ i) = ((ν i : ℝ) : 𝕜) • φ i) (v : E) :
    HasSum (fun i => ν i * ‖inner 𝕜 (φ i) v‖ ^ 2) (RCLike.re (inner 𝕜 (A v) v)) := by
  have key : (fun i => ν i * ‖inner 𝕜 (φ i) v‖ ^ 2)
      = fun i => RCLike.re (inner 𝕜 (A v) (φ i) * inner 𝕜 (φ i) v) := by
    funext i
    have h1 : inner 𝕜 (A v) (φ i) * inner 𝕜 (φ i) v
        = ((ν i : ℝ) : 𝕜) * ((‖inner 𝕜 (φ i) v‖ ^ 2 : ℝ) : 𝕜) := by
      rw [← inner_conj_symm (A v) (φ i), hA.inner_apply_of_apply_eq_smul φ hν v i,
        map_mul (starRingEnd 𝕜), RCLike.conj_ofReal, mul_assoc, RCLike.conj_mul,
        ← RCLike.ofReal_pow]
    rw [h1, RCLike.re_ofReal_mul, RCLike.ofReal_re]
  rw [key]
  exact (φ.hasSum_inner_mul_inner (A v) v).map (RCLike.re : 𝕜 →+ ℝ) RCLike.continuous_re

/-- Eigenvalue bounds are quadratic-form bounds, in any Hilbert space: an operator diagonal in a
Hilbert basis with `a ≤ νᵢ ≤ b` satisfies `LinearMap.IsSymmetricBoundedBy a b`. This is the
infinite-dimensional counterpart of
`LinearMap.IsSymmetric.isSymmetricBoundedBy_iff_forall_hasEigenvalue`, which goes through the
Rayleigh quotient and needs finite dimension. -/
theorem isSymmetricBoundedBy_of_hilbertBasis (hA : A.IsSymmetric) (φ : HilbertBasis ι 𝕜 E)
    (hν : ∀ i, A (φ i) = ((ν i : ℝ) : 𝕜) • φ i) {a b : ℝ} (ha : ∀ i, a ≤ ν i)
    (hb : ∀ i, ν i ≤ b) : A.IsSymmetricBoundedBy a b := by
  refine ⟨hA, fun v => ?_, fun v => ?_⟩
  · exact hasSum_le (fun i => mul_le_mul_of_nonneg_right (ha i) (sq_nonneg _))
      ((φ.hasSum_norm_inner_sq v).mul_left a) (hA.hasSum_re_inner_apply_self φ hν v)
  · exact hasSum_le (fun i => mul_le_mul_of_nonneg_right (hb i) (sq_nonneg _))
      (hA.hasSum_re_inner_apply_self φ hν v) ((φ.hasSum_norm_inner_sq v).mul_left b)

/-- An operator diagonal in a Hilbert basis is bounded by the supremum of the absolute values of
its diagonal entries. The bound is not assumed nonnegative: when the index type is empty the
space is trivial and the inequality reads `0 ≤ 0`. -/
theorem norm_apply_le_of_hilbertBasis (hA : A.IsSymmetric) (φ : HilbertBasis ι 𝕜 E)
    (hν : ∀ i, A (φ i) = ((ν i : ℝ) : 𝕜) • φ i) {C : ℝ} (hC : ∀ i, |ν i| ≤ C) (v : E) :
    ‖A v‖ ≤ C * ‖v‖ := by
  rcases isEmpty_or_nonempty ι with _ | hι
  · have hv : ‖v‖ ^ 2 = 0 := (φ.hasSum_norm_inner_sq v).unique hasSum_empty
    have hAv : ‖A v‖ ^ 2 = 0 := (φ.hasSum_norm_inner_sq (A v)).unique hasSum_empty
    have h1 : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
    have h2 : ‖A v‖ = 0 := by nlinarith [norm_nonneg (A v)]
    rw [h1, h2, mul_zero]
  · have hterm : ∀ i, ‖inner 𝕜 (φ i) (A v)‖ ^ 2 ≤ C ^ 2 * ‖inner 𝕜 (φ i) v‖ ^ 2 := by
      intro i
      rw [hA.inner_apply_of_apply_eq_smul φ hν v i, norm_mul, RCLike.norm_ofReal, mul_pow]
      have h1 : |ν i| ^ 2 ≤ C ^ 2 := by nlinarith [abs_nonneg (ν i), hC i]
      exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (Classical.arbitrary ι))
    have hle : ‖A v‖ ^ 2 ≤ (C * ‖v‖) ^ 2 := by
      rw [mul_pow]
      exact hasSum_le hterm (φ.hasSum_norm_inner_sq (A v))
        ((φ.hasSum_norm_inner_sq v).mul_left (C ^ 2))
    have h := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h

/-- A polynomial with real coefficients in a symmetric operator is symmetric. -/
theorem aeval_map (hA : A.IsSymmetric) (p : ℝ[X]) :
    (aeval A (p.map (algebraMap ℝ 𝕜))).IsSymmetric := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [Polynomial.map_add] using hp.add hq
  | monomial n c =>
      have h : aeval A ((monomial n c : ℝ[X]).map (algebraMap ℝ 𝕜)) = ((c : ℝ) : 𝕜) • A ^ n := by
        rw [Polynomial.map_monomial, aeval_monomial, RCLike.algebraMap_eq_ofReal, Algebra.smul_def]
      rw [h]
      exact (hA.pow n).smul (RCLike.conj_ofReal c)

/-- The discrete counterpart of `LinearMap.IsSymmetricBoundedBy.norm_aeval_map_apply_le`:
`‖p(A) v‖ ≤ C ‖v‖` whenever `|p|` is bounded by `C` at every eigenvalue of an operator diagonal
in a Hilbert basis. Unlike the interval form, this sees the individual eigenvalues, which is
exactly what makes a superlinear rate possible. -/
theorem norm_aeval_map_apply_le_of_hilbertBasis (hA : A.IsSymmetric) (φ : HilbertBasis ι 𝕜 E)
    (hν : ∀ i, A (φ i) = ((ν i : ℝ) : 𝕜) • φ i) (p : ℝ[X]) {C : ℝ}
    (hC : ∀ i, |p.eval (ν i)| ≤ C) (v : E) :
    ‖aeval A (p.map (algebraMap ℝ 𝕜)) v‖ ≤ C * ‖v‖ := by
  refine (hA.aeval_map p).norm_apply_le_of_hilbertBasis φ (ν := fun i => p.eval (ν i)) ?_ hC v
  intro i
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul (hν i), eval_map, eval₂_at_apply,
    RCLike.algebraMap_eq_ofReal]

end LinearMap.IsSymmetric

/-- Upper norm equivalence from the quadratic-form bounds, `‖v‖_A ≤ √b ‖v‖`: the companion of
`LinearMap.IsCoerciveWith.norm_le_energyNorm`, which is the lower half. -/
theorem LinearMap.IsSymmetricBoundedBy.energyNorm_le_sqrt_mul_norm {A : E →ₗ[𝕜] E} {a b : ℝ}
    (hA : A.IsSymmetricBoundedBy a b) (v : E) : energyNorm A v ≤ Real.sqrt b * ‖v‖ := by
  have h := Real.sqrt_le_sqrt (hA.re_inner_le v)
  rwa [Real.sqrt_mul' b (sq_nonneg _), Real.sqrt_sq (norm_nonneg v)] at h

namespace Krylov

/-! ### The operator `A = 1 - K` -/

/-- `A = 1 - K` acts on an eigenvector of `K` by `1 - λ`. -/
theorem apply_eq_smul_of_eq_one_sub {A K : E →ₗ[𝕜] E} (hAK : A = 1 - K)
    (φ : HilbertBasis ι 𝕜 E) {lam : ι → ℝ} (hlam : ∀ j, K (φ j) = ((lam j : ℝ) : 𝕜) • φ j)
    (j : ι) : A (φ j) = (((1 - lam j : ℝ)) : 𝕜) • φ j := by
  rw [hAK, LinearMap.sub_apply, Module.End.one_apply, hlam j, RCLike.ofReal_sub,
    RCLike.ofReal_one, sub_smul, one_smul]

/-- The enclosure `δ ≤ 1 - λ_j ≤ Δ` of the eigenvalues of `A = 1 - K` is the quadratic-form
enclosure `LinearMap.IsSymmetricBoundedBy δ Δ`, by Parseval in the eigenbasis. -/
theorem isSymmetricBoundedBy_of_eq_one_sub {A K : E →ₗ[𝕜] E} (hAK : A = 1 - K)
    (hK : K.IsSymmetric) (φ : HilbertBasis ι 𝕜 E) {lam : ι → ℝ}
    (hlam : ∀ j, K (φ j) = ((lam j : ℝ) : 𝕜) • φ j) {δ Δ : ℝ} (hlow : ∀ j, δ ≤ 1 - lam j)
    (hupp : ∀ j, 1 - lam j ≤ Δ) : A.IsSymmetricBoundedBy δ Δ := by
  have hAsym : A.IsSymmetric := by
    rw [hAK]; exact LinearMap.IsSymmetric.sub LinearMap.IsSymmetric.one hK
  exact hAsym.isSymmetricBoundedBy_of_hilbertBasis φ
    (apply_eq_smul_of_eq_one_sub hAK φ hlam) hlow hupp

/-! ### The competitor polynomial -/

/-- The competitor polynomial of Winther's theorem, `Q_k(t) = ∏_{j < k} (1 - λ_j - t)/(1 - λ_j)`:
it is `1` at `0` and vanishes at the `k` leading eigenvalues `1 - λ_j` of `A = 1 - K`. -/
noncomputable def wintherPoly (lam : ℕ → ℝ) (k : ℕ) : ℝ[X] :=
  ∏ j ∈ Finset.range k, C (1 - lam j)⁻¹ * (C (1 - lam j) - X)

/-- The values of `Q_k`, the form every estimate on it starts from. -/
theorem wintherPoly_eval (lam : ℕ → ℝ) (k : ℕ) (t : ℝ) :
    (wintherPoly lam k).eval t = ∏ j ∈ Finset.range k, (1 - lam j)⁻¹ * (1 - lam j - t) := by
  simp [wintherPoly, eval_prod]

/-- `Q_k` has degree at most `k`, so it is a competitor at step `k`. -/
theorem wintherPoly_natDegree_le (lam : ℕ → ℝ) (k : ℕ) : (wintherPoly lam k).natDegree ≤ k := by
  refine (natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ 1 fun j _ => ?_).trans (by simp)
  refine natDegree_mul_le.trans ?_
  simp only [natDegree_C, zero_add]
  exact (natDegree_sub_le _ _).trans (by simp)

/-- `Q_k(0) = 1`, the normalization every residual polynomial must satisfy. -/
theorem wintherPoly_eval_zero {lam : ℕ → ℝ} (h : ∀ j, 1 - lam j ≠ 0) (k : ℕ) :
    (wintherPoly lam k).eval 0 = 1 := by
  rw [wintherPoly_eval]
  exact Finset.prod_eq_one fun j _ => by rw [sub_zero, inv_mul_cancel₀ (h j)]

/-- The key estimate on the competitor polynomial: at *every* eigenvalue `1 - λ_i` of `A`,
`|Q_k(1 - λ_i)| ≤ ∏_{j < k} 2 |λ_j|/(1 - λ_j)`. For `i < k` the value is `0`; for `k ≤ i` each
factor is bounded by `2 |λ_j|/(1 - λ_j)` because `|λ_i| ≤ |λ_j|`, which is where the antitone
enumeration of the eigenvalues is used. -/
theorem abs_eval_wintherPoly_le {lam : ℕ → ℝ} (hpos : ∀ j, 0 < 1 - lam j)
    (hanti : Antitone fun j => |lam j|) (k i : ℕ) :
    |(wintherPoly lam k).eval (1 - lam i)| ≤
      ∏ j ∈ Finset.range k, 2 * |lam j| / (1 - lam j) := by
  have hnn : ∀ j, 0 ≤ 2 * |lam j| / (1 - lam j) := fun j =>
    div_nonneg (by positivity) (hpos j).le
  rcases lt_or_ge i k with hik | hik
  · have hz : (wintherPoly lam k).eval (1 - lam i) = 0 := by
      rw [wintherPoly_eval]
      exact Finset.prod_eq_zero (Finset.mem_range.2 hik) (by ring)
    rw [hz, abs_zero]
    exact Finset.prod_nonneg fun j _ => hnn j
  · rw [wintherPoly_eval, Finset.abs_prod]
    refine Finset.prod_le_prod (fun j _ => abs_nonneg _) fun j hj => ?_
    have hjk : j < k := Finset.mem_range.1 hj
    have habs : |lam i| ≤ |lam j| := hanti (hjk.le.trans hik)
    have hstep : |lam i - lam j| ≤ 2 * |lam j| := by
      have h1 : |lam i - lam j| ≤ |lam i| + |lam j| := by
        simpa using abs_sub_le (lam i) 0 (lam j)
      linarith
    have hinv : (0 : ℝ) ≤ (1 - lam j)⁻¹ := inv_nonneg.2 (hpos j).le
    calc |(1 - lam j)⁻¹ * (1 - lam j - (1 - lam i))|
        = (1 - lam j)⁻¹ * |lam i - lam j| := by
          rw [abs_mul, abs_inv, abs_of_pos (hpos j),
            show 1 - lam j - (1 - lam i) = lam i - lam j from by ring]
      _ ≤ (1 - lam j)⁻¹ * (2 * |lam j|) := mul_le_mul_of_nonneg_left hstep hinv
      _ = 2 * |lam j| / (1 - lam j) := by rw [inv_mul_eq_div]

/-! ### The rate -/

/-- Winther's rate `c_k = (Δ/δ)^{1/(2k)} (2/k) ∑_{j < k} |λ_j|/(1 - λ_j)`. Its `k`-th power
bounds the relative error of the `k`-th conjugate gradient iterate (`Krylov.winther`), and
`c_k → 0` (`Krylov.winther_rate_tendsto_zero`), which is superlinear convergence. -/
noncomputable def wintherRate (lam : ℕ → ℝ) (δ Δ : ℝ) (k : ℕ) : ℝ :=
  (Δ / δ) ^ (1 / (2 * k : ℝ)) * (2 / k * ∑ j ∈ Finset.range k, |lam j| / (1 - lam j))

/-- **AM–GM** in the form the rate needs: a product of `k` nonnegative reals is at most the
`k`-th power of their arithmetic mean. -/
theorem prod_range_le_pow_inv_mul_sum {b : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j) {k : ℕ} (hk : k ≠ 0) :
    ∏ j ∈ Finset.range k, b j ≤ ((k : ℝ)⁻¹ * ∑ j ∈ Finset.range k, b j) ^ k := by
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)
  have hprod : 0 ≤ ∏ j ∈ Finset.range k, b j := Finset.prod_nonneg fun j _ => hb j
  have hw : ∑ _j ∈ Finset.range k, (1 : ℝ) = k := by simp
  have h := Real.geom_mean_le_arith_mean (Finset.range k) (fun _ => (1 : ℝ)) b
    (fun _ _ => zero_le_one) (by rw [hw]; exact hk0) fun j _ => hb j
  rw [hw] at h
  simp only [Real.rpow_one, one_mul] at h
  calc ∏ j ∈ Finset.range k, b j
      = ((∏ j ∈ Finset.range k, b j) ^ ((k : ℝ)⁻¹)) ^ k :=
        (Real.rpow_inv_natCast_pow hprod hk).symm
    _ ≤ ((∑ j ∈ Finset.range k, b j) / k) ^ k := by gcongr
    _ = ((k : ℝ)⁻¹ * ∑ j ∈ Finset.range k, b j) ^ k := by rw [div_eq_inv_mul]

/-- The rate tends to `0`: the Cesàro means of `|λ_j|/(1 - λ_j) → 0` tend to `0`, and the
correction `(Δ/δ)^{1/(2k)}` tends to `1`. This is what makes the bound of `Krylov.winther`
superlinear; it is the only place where `λ → 0` is used. -/
theorem winther_rate_tendsto_zero {lam : ℕ → ℝ} {δ Δ : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hlim : Tendsto lam atTop (𝓝 0)) : Tendsto (wintherRate lam δ Δ) atTop (𝓝 0) := by
  have hden : Tendsto (fun j => 1 - lam j) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hlim
  have hb : Tendsto (fun j => |lam j| / (1 - lam j)) atTop (𝓝 0) := by
    have h := hlim.abs.div hden one_ne_zero
    rw [abs_zero, zero_div] at h
    exact h
  have hsum : Tendsto
      (fun k : ℕ => 2 / (k : ℝ) * ∑ j ∈ Finset.range k, |lam j| / (1 - lam j)) atTop (𝓝 0) := by
    have h : Tendsto (fun k : ℕ =>
        2 * ((k : ℝ)⁻¹ * ∑ j ∈ Finset.range k, |lam j| / (1 - lam j))) atTop (𝓝 (2 * 0)) :=
      tendsto_const_nhds.mul hb.cesaro
    rw [mul_zero] at h
    exact h.congr fun k => by rw [← mul_assoc, ← div_eq_mul_inv]
  have hexp : Tendsto (fun k : ℕ => 1 / (2 * k : ℝ)) atTop (𝓝 0) := by
    have h : Tendsto (fun k : ℕ => (2⁻¹ : ℝ) * (1 / (k : ℝ))) atTop (𝓝 ((2⁻¹ : ℝ) * 0)) :=
      tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat
    rw [mul_zero] at h
    exact h.congr fun k => by rw [one_div, one_div, ← mul_inv]
  have hpow : Tendsto (fun k : ℕ => (Δ / δ) ^ (1 / (2 * k : ℝ))) atTop (𝓝 1) := by
    have h := ((Real.continuous_const_rpow (ne_of_gt (div_pos hΔ hδ))).tendsto 0).comp hexp
    rwa [Real.rpow_zero] at h
  have h := hpow.mul hsum
  rw [one_mul] at h
  exact h

/-! ### Winther's theorem -/

/-- The sharp form of Winther's theorem, for any Galerkin iterate (in particular for conjugate
gradients): `‖x* - x_k‖ ≤ √(Δ/δ) ∏_{j < k} 2 |λ_j|/(1 - λ_j) ‖x* - x₀‖`.

The competitor `Krylov.wintherPoly` annihilates the `k` leading eigencomponents, its remaining
values are bounded by the product (`Krylov.abs_eval_wintherPoly_le`), and Parseval turns that
into an operator bound (`LinearMap.IsSymmetric.norm_aeval_map_apply_le_of_hilbertBasis`).
Galerkin optimality is used in the energy norm, so the passage between the two norms is paid for
exactly twice, once at each end: `√δ ‖v‖ ≤ ‖v‖_A ≤ √Δ ‖v‖`. -/
theorem IsGalerkinIterate.norm_error_le_prod {A K : E →ₗ[𝕜] E} (hAK : A = 1 - K)
    (hK : K.IsSymmetric) (φ : HilbertBasis ℕ 𝕜 E) {lam : ℕ → ℝ}
    (hlam : ∀ j, K (φ j) = ((lam j : ℝ) : 𝕜) • φ j) (hanti : Antitone fun j => |lam j|)
    {δ Δ : ℝ} (hδ : 0 < δ) (hlow : ∀ j, δ ≤ 1 - lam j) (hupp : ∀ j, 1 - lam j ≤ Δ)
    {b x₀ x xstar : E} {k : ℕ} (hx : IsGalerkinIterate A b x₀ k x) (hstar : A xstar = b) :
    ‖xstar - x‖ ≤
      Real.sqrt (Δ / δ) * (∏ j ∈ Finset.range k, 2 * |lam j| / (1 - lam j)) * ‖xstar - x₀‖ := by
  have hpos : ∀ j, 0 < 1 - lam j := fun j => hδ.trans_le (hlow j)
  have hΔnn : (0 : ℝ) ≤ Δ := hδ.le.trans ((hlow 0).trans (hupp 0))
  have hAφ := apply_eq_smul_of_eq_one_sub hAK φ hlam
  have hAsym : A.IsSymmetric := by
    rw [hAK]; exact LinearMap.IsSymmetric.sub LinearMap.IsSymmetric.one hK
  have hbdd : A.IsSymmetricBoundedBy δ Δ :=
    isSymmetricBoundedBy_of_eq_one_sub hAK hK φ hlam hlow hupp
  set q : 𝕜[X] := (wintherPoly lam k).map (algebraMap ℝ 𝕜) with hq
  have hdeg : q.degree ≤ (k : WithBot ℕ) :=
    degree_map_le.trans (natDegree_le_iff_degree_le.1 (wintherPoly_natDegree_le lam k))
  have hzero : q.eval 0 = 1 := by
    rw [hq, eval_zero_map, wintherPoly_eval_zero (fun j => (hpos j).ne') k, map_one]
  have h1 := hx.energyNorm_error_le_energyNorm_aeval (hbdd.isSymmetricCoercive hδ) hstar q hdeg
    hzero
  have h2 := hbdd.energyNorm_le_sqrt_mul_norm (aeval A q (xstar - x₀))
  have h3 : ‖aeval A q (xstar - x₀)‖ ≤
      (∏ j ∈ Finset.range k, 2 * |lam j| / (1 - lam j)) * ‖xstar - x₀‖ :=
    hAsym.norm_aeval_map_apply_le_of_hilbertBasis φ hAφ (wintherPoly lam k)
      (fun i => abs_eval_wintherPoly_le hpos hanti k i) _
  have h4 := hbdd.isCoerciveWith.norm_le_energyNorm hδ.le (xstar - x)
  have hchain : Real.sqrt δ * ‖xstar - x‖ ≤
      Real.sqrt Δ * ((∏ j ∈ Finset.range k, 2 * |lam j| / (1 - lam j)) * ‖xstar - x₀‖) :=
    h4.trans (h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg Δ))))
  rw [Real.sqrt_div hΔnn δ, div_mul_eq_mul_div, div_mul_eq_mul_div,
    le_div_iff₀ (Real.sqrt_pos.2 hδ)]
  calc ‖xstar - x‖ * Real.sqrt δ = Real.sqrt δ * ‖xstar - x‖ := mul_comm _ _
    _ ≤ Real.sqrt Δ * ((∏ j ∈ Finset.range k, 2 * |lam j| / (1 - lam j)) * ‖xstar - x₀‖) :=
        hchain
    _ = Real.sqrt Δ * (∏ j ∈ Finset.range k, 2 * |lam j| / (1 - lam j)) * ‖xstar - x₀‖ :=
        (mul_assoc _ _ _).symm

/-- **Winther's theorem** (Atkinson–Han, *Theoretical Numerical Analysis*, Thm 5.6.2), with the
eigen-decomposition of the compact part taken as data: for `A = 1 - K` with `K` self-adjoint and
diagonal in the Hilbert basis `φ` with eigenvalues `λ` enumerated so that `|λ|` is antitone, and
with `0 < δ ≤ 1 - λ_j ≤ Δ`, the conjugate gradient iterates for `A x = b` started at `x₀` satisfy
`‖x* - x_k‖ ≤ c_k^k ‖x* - x₀‖` with `c_k = Krylov.wintherRate λ δ Δ k`.

Together with `Krylov.winther_rate_tendsto_zero`, which needs `λ → 0`, this is superlinear
convergence: the rate improves without bound as the iteration proceeds, because a degree-`k`
polynomial can annihilate the `k` largest eigenvalues of `K` and the rest are small. See the
module documentation for the comparison of `c_k` with the book's constant. -/
theorem winther {A K : E →ₗ[𝕜] E} (hAK : A = 1 - K) (hK : K.IsSymmetric)
    (φ : HilbertBasis ℕ 𝕜 E) {lam : ℕ → ℝ} (hlam : ∀ j, K (φ j) = ((lam j : ℝ) : 𝕜) • φ j)
    (hanti : Antitone fun j => |lam j|) {δ Δ : ℝ} (hδ : 0 < δ) (hlow : ∀ j, δ ≤ 1 - lam j)
    (hupp : ∀ j, 1 - lam j ≤ Δ) {b x₀ xstar : E} (hstar : A xstar = b) (k : ℕ) :
    ‖xstar - (CG.iterate A b x₀ k).x‖ ≤ wintherRate lam δ Δ k ^ k * ‖xstar - x₀‖ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hpos : ∀ j, 0 < 1 - lam j := fun j => hδ.trans_le (hlow j)
  have hΔnn : (0 : ℝ) ≤ Δ := hδ.le.trans ((hlow 0).trans (hupp 0))
  have hk0 : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hbdd : A.IsSymmetricBoundedBy δ Δ :=
    isSymmetricBoundedBy_of_eq_one_sub hAK hK φ hlam hlow hupp
  have hmain := IsGalerkinIterate.norm_error_le_prod hAK hK φ hlam hanti hδ hlow hupp
    (CG.isGalerkinIterate b x₀ (hbdd.isSymmetricCoercive hδ) k) hstar
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have hamgm : (∏ j ∈ Finset.range k, 2 * |lam j| / (1 - lam j))
      ≤ (2 / (k : ℝ) * ∑ j ∈ Finset.range k, |lam j| / (1 - lam j)) ^ k := by
    have h := prod_range_le_pow_inv_mul_sum (b := fun j => 2 * |lam j| / (1 - lam j))
      (fun j => div_nonneg (by positivity) (hpos j).le) hk.ne'
    have hs : ∑ j ∈ Finset.range k, 2 * |lam j| / (1 - lam j)
        = 2 * ∑ j ∈ Finset.range k, |lam j| / (1 - lam j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_div_assoc 2 _ _
    rw [hs] at h
    refine h.trans_eq ?_
    congr 1
    field_simp
  have hrpow : ((Δ / δ) ^ (1 / (2 * k : ℝ))) ^ k = Real.sqrt (Δ / δ) := by
    rw [← Real.rpow_natCast ((Δ / δ) ^ (1 / (2 * k : ℝ))) k,
      ← Real.rpow_mul (div_nonneg hΔnn hδ.le), Real.sqrt_eq_rpow]
    congr 1
    field_simp
  calc Real.sqrt (Δ / δ) * ∏ j ∈ Finset.range k, 2 * |lam j| / (1 - lam j)
      ≤ Real.sqrt (Δ / δ) * (2 / (k : ℝ) * ∑ j ∈ Finset.range k, |lam j| / (1 - lam j)) ^ k := by
        gcongr
    _ = wintherRate lam δ Δ k ^ k := by
        rw [wintherRate, mul_pow ((Δ / δ) ^ (1 / (2 * (k : ℝ))))
          (2 / (k : ℝ) * ∑ j ∈ Finset.range k, |lam j| / (1 - lam j)) k, hrpow]

open ContinuousLinearMap in
/-- **Winther's theorem with no eigen-decomposition supplied.** For an injective compact
self-adjoint `K` on an infinite-dimensional Hilbert space and `A = 1 - K` with
`0 < δ ≤ 1 - λ_j ≤ Δ` for the eigenvalues `λ` of `K`, the conjugate gradient iterates for
`A x = b` satisfy `‖x* - x_k‖ ≤ c_k^k ‖x* - x₀‖` with `c_k = Krylov.wintherRate λ δ Δ k`, and
`c_k → 0`: convergence is superlinear.

This is `Krylov.winther` and `Krylov.winther_rate_tendsto_zero` with their three data hypotheses
discharged by `ContinuousLinearMap.IsSymmetric.eigenvectorHilbertBasis` and its companions. The
proof of `Krylov.winther` is unchanged and still never uses compactness: compactness is what
*produces* the enumerated eigen-decomposition, not what the estimate needs. The two hypotheses
beyond compactness and symmetry, injectivity of `K` and infinite-dimensionality of `E`, are what
make an antitone enumeration by `ℕ` possible at all; see
`Numlib/Analysis/InnerProductSpace/CompactSpectral`. -/
theorem winther_of_isCompactOperator [CompleteSpace E] {A : E →ₗ[𝕜] E} {K : E →L[𝕜] E}
    (hAK : A = 1 - (K : E →ₗ[𝕜] E)) (hKs : (K : E →ₗ[𝕜] E).IsSymmetric)
    (hKc : IsCompactOperator K) (hKinj : LinearMap.ker (K : E →ₗ[𝕜] E) = ⊥)
    (hfin : ¬ FiniteDimensional 𝕜 E) {δ Δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ j, δ ≤ 1 - IsSymmetric.eigenvalueSeq hKs hKc j)
    (hupp : ∀ j, 1 - IsSymmetric.eigenvalueSeq hKs hKc j ≤ Δ)
    {b x₀ xstar : E} (hstar : A xstar = b) :
    (∀ k, ‖xstar - (CG.iterate A b x₀ k).x‖
        ≤ wintherRate (IsSymmetric.eigenvalueSeq hKs hKc) δ Δ k ^ k * ‖xstar - x₀‖) ∧
      Tendsto (wintherRate (IsSymmetric.eigenvalueSeq hKs hKc) δ Δ) atTop (𝓝 0) := by
  refine ⟨fun k => winther hAK hKs (IsSymmetric.eigenvectorHilbertBasis hKs hKc hKinj hfin)
    (fun j => IsSymmetric.apply_eigenvectorHilbertBasis hKs hKc hKinj hfin j)
    (IsSymmetric.eigenvalueSeq_antitone hKs hKc) hδ hlow hupp hstar k, ?_⟩
  exact winther_rate_tendsto_zero hδ (hδ.trans_le ((hlow 0).trans (hupp 0)))
    (IsSymmetric.tendsto_eigenvalueSeq_zero hKs hKc)

end Krylov
