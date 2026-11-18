import Mathlib.Analysis.Subadditive
import Mathlib.Basic.Real.Pointwise
import Numlib.Krylov.Convergence.CG
import Numlib.Krylov.Convergence.GMRESCurve
import Numlib.Krylov.Convergence.MinRes
import Numlib.LinearAlgebra.Matrix.WeightedAdjoint
import NumlibSurface.BenziGolubLiesen.Section09

/-!
# Benzi, Golub and Liesen, Section 9: Krylov convergence

The terminal Krylov dimension bounds the step at which the projections in §9.1 are exact.
Before termination, residual polynomials give bounds that depend on the spectrum and on the
conditioning of the eigenvector matrix. Chebyshev polynomials give concrete bounds for a positive
interval and for two equal-length intervals on opposite sides of zero.

## Main definitions

* `BenziGolubLiesen.residualMinimax`: the polynomial minimax value (9.10).
* `BenziGolubLiesen.asymptoticResidualFactor`: the asymptotic root factor in (9.13).

## Main results

* `BenziGolubLiesen.minResidual_finiteTermination`, `BenziGolubLiesen.galerkin_finiteTermination`
  and `BenziGolubLiesen.symmlq_finiteTermination`: exactness at the terminal Krylov dimension.
* `BenziGolubLiesen.minResidual_norm_le_of_diagonalizable`: the eigenvector conditioning
  bound (9.9).
* `BenziGolubLiesen.galerkin_chebyshev_bound` and
  `BenziGolubLiesen.minResidual_equalLengthIntervals_bound`: (9.8) and (9.11).
* `BenziGolubLiesen.tendsto_asymptoticResidualFactor`: existence of the limit in (9.13).
-/

namespace BenziGolubLiesen

open Matrix Polynomial Krylov
open scoped Matrix.Norms.L2Operator Pointwise Topology

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

private theorem finrank_terminalSubspace (A : Matrix ι ι 𝕜) (r : EuclideanSpace 𝕜 ι) :
    Module.finrank 𝕜 (subspace A.toEuclideanLin r (Fintype.card ι)) =
      grade A.toEuclideanLin r := by
  rw [finrank_subspace, min_eq_right]
  simpa using grade_le_finrank A.toEuclideanLin r

/-- **Section 9.2** of [benzi2005numerical]. For a nonsingular matrix, the minimal-residual
projection is exact at the dimension of the terminal Krylov space. -/
theorem minResidual_finiteTermination {A : Matrix ι ι ℝ} (hA : IsUnit A)
    {b x₀ x : EuclideanSpace ℝ ι}
    (hx : IsMinResidualIterate A.toEuclideanLin b x₀
      (Module.finrank ℝ (krylovSubspace A (b - A.toEuclideanLin x₀) (Fintype.card ι))) x) :
    A.toEuclideanLin x = b := by
  dsimp only [krylovSubspace] at hx
  rw [finrank_terminalSubspace] at hx
  exact hx.apply_eq_of_grade_le le_rfl
    (Function.LeftInverse.injective (A.toEuclideanLin_nonsing_inv_mul_apply hA)).injOn

/-- **Section 9.2** of [benzi2005numerical]. The Galerkin projection, when it exists, is exact at
the dimension of the terminal Krylov space. This includes case (C) in Theorem 9.1. -/
theorem galerkin_finiteTermination {A : Matrix ι ι ℝ} {b x₀ x : EuclideanSpace ℝ ι}
    (hx : IsGalerkinIterate A.toEuclideanLin b x₀
      (Module.finrank ℝ (krylovSubspace A (b - A.toEuclideanLin x₀) (Fintype.card ι))) x) :
    A.toEuclideanLin x = b := by
  dsimp only [krylovSubspace] at hx
  rw [finrank_terminalSubspace] at hx
  exact hx.apply_eq_of_grade_le le_rfl

/-- **Section 9.2** of [benzi2005numerical]. The iterate (9.4) is exact at the dimension of
the terminal Krylov space because its trial space is then contained in its test space. -/
theorem symmlq_finiteTermination {A : Matrix ι ι ℝ} {b x₀ x : EuclideanSpace ℝ ι}
    (hx : IsSYMMLQIterate A b x₀
      (Module.finrank ℝ (krylovSubspace A (b - A.toEuclideanLin x₀) (Fintype.card ι))) x) :
    A.toEuclideanLin x = b := by
  let T := A.toEuclideanLin
  let r := b - T x₀
  let K := subspace T r (grade T r)
  have hdim := finrank_terminalSubspace A r
  change IsPetrovGalerkin T b x₀ ((subspace T r (Module.finrank ℝ
    (subspace T r (Fintype.card ι)))).map T) (subspace T r (Module.finrank ℝ
      (subspace T r (Fintype.card ι)))) x at hx
  rw [hdim] at hx
  have hinv := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem T).mp
    (subspace_grade_mem_invtSubmodule T r)
  obtain ⟨z, hz, hzx⟩ := hx.mem
  have hmem : x - x₀ ∈ K := hzx ▸ hinv z hz
  have hg : IsGalerkinIterate T b x₀ (grade T r) x := ⟨hmem, hx.orth⟩
  exact hg.apply_eq_of_grade_le le_rfl

/-- **Equation (9.9)** of [benzi2005numerical], first equality. The minimal-residual norm is an
attained minimum over the normalized polynomials of degree at most $k$. -/
theorem minResidual_residualPolynomial {A : Matrix ι ι 𝕜}
    {b x₀ x : EuclideanSpace 𝕜 ι} {k : ℕ}
    (hx : IsMinResidualIterate A.toEuclideanLin b x₀ k x) :
    let r₀ := b - A.toEuclideanLin x₀
    ∃ p : 𝕜[X], p.degree ≤ k ∧ p.eval 0 = 1 ∧
      b - A.toEuclideanLin x = aeval A.toEuclideanLin p r₀ ∧
      ∀ q : 𝕜[X], q.degree ≤ k → q.eval 0 = 1 →
        ‖aeval A.toEuclideanLin p r₀‖ ≤ ‖aeval A.toEuclideanLin q r₀‖ := by
  obtain ⟨p, hp, hp0, hres⟩ := exists_residual_poly hx.mem
  refine ⟨p, hp, hp0, hres, fun q hq hq0 => ?_⟩
  rw [← hres]
  exact hx.norm_residual_le_norm_aeval q hq hq0

/-- **Equation (9.9)** of [benzi2005numerical]. For $A=X\operatorname{diag}(d)X^{-1}$, the
relative minimal-residual norm is bounded by $\kappa_2(X)$ times the infimum over normalized
polynomials of the maximum modulus on the diagonal entries $d_i$. The norm on `ι → 𝕜` is the
supremum norm; the matrix norms are the Euclidean operator norms. -/
theorem minResidual_norm_le_of_diagonalizable {A X : Matrix ι ι 𝕜} {d : ι → 𝕜}
    (hX : IsUnit X) (hA : A = X * diagonal d * X⁻¹) {b x₀ x : EuclideanSpace 𝕜 ι} {k : ℕ}
    (hr : b - A.toEuclideanLin x₀ ≠ 0) (hx : IsMinResidualIterate A.toEuclideanLin b x₀ k x) :
    ‖b - A.toEuclideanLin x‖ / ‖b - A.toEuclideanLin x₀‖ ≤
      ‖X‖ * ‖X⁻¹‖ *
        (⨅ p : {p : 𝕜[X] // p.degree ≤ k ∧ p.eval 0 = 1}, ‖fun i => p.1.eval (d i)‖) := by
  have : Nonempty {p : 𝕜[X] // p.degree ≤ (k : WithBot ℕ) ∧ p.eval 0 = 1} :=
    ⟨⟨1, by simp, by simp⟩⟩
  rw [Real.mul_iInf_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  refine le_ciInf fun p => ?_
  let D := diagonal d
  let e := (similarityAlgEquiv X hX).symm
  have hconj : A = e D := hA.trans (similarityAlgEquiv_symm_apply X hX D).symm
  have hdiag : aeval D p.1 = diagonal (fun i => p.1.eval (d i)) := by
    change aeval (diagonal d) p.1 = _
    rw [← diagonalAlgHom_apply 𝕜, aeval_algHom_apply, aeval_pi_apply]
    simp [aeval_def]
  let Dp : Matrix ι ι 𝕜 := diagonal (fun i => p.1.eval (d i))
  have hpol : aeval A p.1 = X * Dp * X⁻¹ := by
    rw [hconj, aeval_algHom_apply e D p.1, hdiag]
    exact similarityAlgEquiv_symm_apply X hX Dp
  have hnorm : ‖aeval A p.1‖ ≤ ‖X‖ * ‖X⁻¹‖ * ‖fun i => p.1.eval (d i)‖ := by
    rw [hpol, ← l2_opNorm_diagonal (n := ι)]
    calc
      ‖X * Dp * X⁻¹‖ ≤ ‖X * Dp‖ * ‖X⁻¹‖ := l2_opNorm_mul (X * Dp) X⁻¹
      _ ≤ (‖X‖ * ‖Dp‖) * ‖X⁻¹‖ :=
        mul_le_mul_of_nonneg_right (l2_opNorm_mul X Dp) (norm_nonneg X⁻¹)
      _ = ‖X‖ * ‖X⁻¹‖ * ‖Dp‖ := by ring
  let r : EuclideanSpace 𝕜 ι := b - A.toEuclideanLin x₀
  have hres := hx.norm_residual_le_norm_aeval p.1 p.2.1 p.2.2
  rw [← toEuclideanLin_aeval, toEuclideanLin_apply] at hres
  have hmul := l2_opNorm_mulVec (aeval A p.1) r
  exact (div_le_iff₀ (norm_pos_iff.mpr hr)).2
    (hres.trans (hmul.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg r))))

/-- **Equation (9.8)** of [benzi2005numerical]. For a symmetric positive definite operator
with Rayleigh quotients in $[l,u]$, the CG energy error decreases at the Chebyshev rate for
the ratio $u/l$. -/
theorem galerkin_chebyshev_bound {A : Matrix ι ι ℝ} {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hA : A.toEuclideanLin.IsSymmetricBoundedBy l u) {b x₀ x xstar : EuclideanSpace ℝ ι}
    {k : ℕ} (hx : IsGalerkinIterate A.toEuclideanLin b x₀ k x)
    (hstar : A.toEuclideanLin xstar = b) :
    energyNorm A.toEuclideanLin (xstar - x) ≤
      2 * ((Real.sqrt (u / l) - 1) / (Real.sqrt (u / l) + 1)) ^ k *
        energyNorm A.toEuclideanLin (xstar - x₀) :=
  hx.energyNorm_error_le hl hlu hA hstar

/-- **Equation (9.11)** of [benzi2005numerical]. If the spectrum of a symmetric matrix is in
two nondegenerate equal-length intervals excluding zero, the MINRES norm is bounded at step $k$
by the two-interval Chebyshev factor with exponent $\lfloor k/2\rfloor$. -/
theorem minResidual_equalLengthIntervals_bound {A : Matrix ι ι ℝ} (hA : A.IsSymm)
    {a₁ b₁ a₂ b₂ : ℝ} (h₁ : a₁ < b₁) (hb₁ : b₁ < 0) (ha₂ : 0 < a₂) (h₂ : a₂ < b₂)
    (hlen : b₁ - a₁ = b₂ - a₂)
    (hspec : ∀ μ : ℝ, Module.End.HasEigenvalue A.toEuclideanLin μ →
      μ ∈ Set.Icc a₁ b₁ ∪ Set.Icc a₂ b₂) {b x₀ x : EuclideanSpace ℝ ι} {k : ℕ}
    (hx : IsMinResidualIterate A.toEuclideanLin b x₀ k x) :
    ‖b - A.toEuclideanLin x‖ ≤
      2 * ((Real.sqrt |a₁ * b₂| - Real.sqrt |b₁ * a₂|) /
        (Real.sqrt |a₁ * b₂| + Real.sqrt |b₁ * a₂|)) ^ (k / 2) * ‖b - A.toEuclideanLin x₀‖ := by
  obtain ⟨z, hz⟩ := exists_isMinResidualIterate A.toEuclideanLin b x₀ (2 * (k / 2))
  apply (IsMinResidual.norm_residual_le hz hx ?_).trans
    (hz.norm_residual_le_of_eigenvalues_mem_union_Icc hA.isSymmetric_toEuclideanLin
      h₁ hb₁ ha₂ h₂ hlen (by simpa using hspec))
  exact subspace_mono _ _ (by omega)

private def residualMinimaxBounds (E : Set ℝ) (k : ℕ) : Set ℝ :=
  {c : ℝ | 0 ≤ c ∧ ∃ p : ℝ[X], p.degree ≤ k ∧ p.eval 0 = 1 ∧ ∀ t ∈ E, |p.eval t| ≤ c}

private theorem residualMinimaxBounds_nonempty (E : Set ℝ) (k : ℕ) :
    (residualMinimaxBounds E k).Nonempty :=
  ⟨1, zero_le_one, 1, by simp, eval_one, fun _ _ => by simp⟩

private theorem residualMinimaxBounds_bddBelow (E : Set ℝ) (k : ℕ) :
    BddBelow (residualMinimaxBounds E k) :=
  ⟨0, fun _ ht => ht.1⟩

/-- **Equation (9.10)** of [benzi2005numerical]. The residual minimax value on $E$ is the
infimum of uniform nonnegative upper bounds for $|p(t)|$, where $\deg p\le k$ and $p(0)=1$.
The infimum definition does not presume an optimizer. -/
noncomputable def residualMinimax (E : Set ℝ) (k : ℕ) : ℝ :=
  sInf (residualMinimaxBounds E k)

private theorem residualMinimax_nonneg (E : Set ℝ) (k : ℕ) : 0 ≤ residualMinimax E k :=
  le_csInf (residualMinimaxBounds_nonempty E k) fun _ ht => ht.1

/-- **Section 9.2** of [benzi2005numerical]. Multiplying normalized residual polynomials
shows that the minimax values (9.10) are submultiplicative in the degree. -/
theorem submultiplicative_residualMinimax (E : Set ℝ) : Submultiplicative (residualMinimax E) := by
  intro j k
  have hmul {a b : ℝ} (ha : a ∈ residualMinimaxBounds E j) (hb : b ∈ residualMinimaxBounds E k) :
      residualMinimax E (j + k) ≤ a * b := by
    obtain ⟨ha₀, p, hp, hp₀, hpa⟩ := ha
    obtain ⟨hb₀, q, hq, hq₀, hqb⟩ := hb
    refine csInf_le (residualMinimaxBounds_bddBelow E (j + k))
      ⟨mul_nonneg ha₀ hb₀, p * q, ?_, by simp [hp₀, hq₀], ?_⟩
    · exact degree_mul_le_of_le hp hq
    · intro t ht
      rw [eval_mul, abs_mul]
      exact mul_le_mul (hpa t ht) (hqb t ht) (abs_nonneg _) ha₀
  have ha_mul (a : ℝ) (ha : a ∈ residualMinimaxBounds E j) :
      residualMinimax E (j + k) ≤ a * residualMinimax E k := by
    change residualMinimax E (j + k) ≤ a • sInf (residualMinimaxBounds E k)
    rw [← Real.sInf_smul_of_nonneg ha.1]
    refine le_csInf ((residualMinimaxBounds_nonempty E k).smul_set) ?_
    rintro _ ⟨b, hb, rfl⟩
    exact hmul ha hb
  change residualMinimax E (j + k) ≤ residualMinimax E j * residualMinimax E k
  rw [mul_comm]
  change residualMinimax E (j + k) ≤ residualMinimax E k • sInf (residualMinimaxBounds E j)
  rw [← Real.sInf_smul_of_nonneg (residualMinimax_nonneg E k)]
  refine le_csInf ((residualMinimaxBounds_nonempty E j).smul_set) ?_
  rintro _ ⟨a, ha, rfl⟩
  exact (ha_mul a ha).trans_eq (mul_comm _ _)

/-- **Equation (9.11)** of [benzi2005numerical]. The two-interval Chebyshev estimate is a
uniform bound on the whole pair of equal-length intervals, hence on any subset of the pair. -/
theorem residualMinimax_le_of_equalLengthIntervals {E : Set ℝ} {a b c d : ℝ}
    (hab : a < b) (hb : b < 0) (hc : 0 < c) (hcd : c < d) (hlen : b - a = d - c)
    (hE : E ⊆ Set.Icc a b ∪ Set.Icc c d) (k : ℕ) :
    residualMinimax E k ≤ 2 * ((Real.sqrt |a * d| - Real.sqrt |b * c|) /
      (Real.sqrt |a * d| + Real.sqrt |b * c|)) ^ (k / 2) := by
  obtain ⟨p, hp, hp0, hbound⟩ :=
    Chebyshev.exists_eval_zero_eq_one_abs_le_of_union_Icc hab hb hc hcd hlen (k / 2)
  have hd : 2 * (k / 2) ≤ k := by omega
  refine csInf_le (residualMinimaxBounds_bddBelow E k) ?_
  exact ⟨(abs_nonneg _).trans (hbound a (Or.inl ⟨le_rfl, hab.le⟩)), p,
    hp.trans (WithBot.coe_le_coe.mpr hd), hp0, fun t ht => hbound t (hE ht)⟩

/-- **Equation (9.12)** of [benzi2005numerical]. For intervals $[-1,-a]$ and $[a,1]$ with
$0<a<1$, the bound has condition-number parameter $1/a$. -/
theorem residualMinimax_le_of_symmetricIntervals {E : Set ℝ} {a : ℝ} (ha : 0 < a) (ha₁ : a < 1)
    (hE : E ⊆ Set.Icc (-1) (-a) ∪ Set.Icc a 1) (k : ℕ) :
    residualMinimax E k ≤ 2 * ((1 / a - 1) / (1 / a + 1)) ^ (k / 2) := by
  have h := residualMinimax_le_of_equalLengthIntervals
    (neg_lt_neg ha₁) (neg_lt_zero.mpr ha) ha ha₁ (by ring) hE k
  have hroot : Real.sqrt |(-a) * a| = a := by
    rw [neg_mul, abs_neg, abs_of_nonneg (mul_nonneg ha.le ha.le), ← pow_two, Real.sqrt_sq ha.le]
  simp only [mul_one, abs_neg, abs_one, Real.sqrt_one, hroot] at h
  have hf : (1 - a) / (1 + a) = (1 / a - 1) / (1 / a + 1) := by
    have hden : 1 / a + 1 ≠ 0 := (by positivity : 0 < 1 / a + 1).ne'
    apply (div_eq_div_iff (by positivity) hden).mpr
    field_simp
  rwa [hf] at h

/-- **Equation (9.13)** of [benzi2005numerical]. The asymptotic convergence factor is the
infimum of the $k$-th roots of the polynomial minimax values over positive $k$. -/
noncomputable def asymptoticResidualFactor (E : Set ℝ) : ℝ :=
  (submultiplicative_residualMinimax E).lim

/-- **Equation (9.13)** of [benzi2005numerical]. The roots of the minimax values converge to
the asymptotic convergence factor by Fekete's lemma. -/
theorem tendsto_asymptoticResidualFactor (E : Set ℝ) :
    Filter.Tendsto (fun k : ℕ => residualMinimax E k ^ (1 / (k : ℝ))) Filter.atTop
      (𝓝 (asymptoticResidualFactor E)) := by
  simpa only [one_div, asymptoticResidualFactor] using
    (submultiplicative_residualMinimax E).tendsto_lim (residualMinimax_nonneg E)

/-- **Section 9.2** of [benzi2005numerical]. Any positive nonincreasing relative GMRES
residual curve before the last step, normalized to start at one, can be realized with any
prescribed multiset of nonzero complex eigenvalues. -/
theorem exists_minResidual_curve_and_charpoly (n : ℕ) (f : Fin (n + 1) → ℝ)
    (hf : Antitone f) (hpos : 0 < f (Fin.last n)) (hstart : f 0 = 1)
    (μ : Fin (n + 1) → ℂ) (hμ : ∀ i, μ i ≠ 0) :
    ∃ (A : Module.End ℂ (EuclideanSpace ℂ (Fin (n + 1))))
      (b : EuclideanSpace ℂ (Fin (n + 1))) (x : ℕ → EuclideanSpace ℂ (Fin (n + 1))),
      A.charpoly = (∏ i, (X - C (μ i))) ∧ Function.Injective A ∧ ‖b‖ = 1 ∧
      (∀ k, IsMinResidualIterate A b 0 k (x k)) ∧
      ∀ k : Fin (n + 1), ‖b - A (x k.val)‖ / ‖b‖ = f k := by
  obtain ⟨A, b, x, hchar, hinj, hb, hiter, hcurve⟩ :=
    exists_gmres_curve_and_charpoly n f hf hpos μ hμ
  rw [hstart] at hb
  exact ⟨A, b, x, hchar, hinj, hb, hiter, fun k => by rw [hb, div_one, hcurve k]⟩

end BenziGolubLiesen
