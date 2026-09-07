import Numlib.Analysis.InnerProductSpace.Projection.Angle
import Numlib.Eigen.RayleighRitz
import Numlib.Krylov.Convergence.Polynomial
import Numlib.RingTheory.Polynomial.ChebyshevEllipse
import Numlib.RingTheory.Polynomial.ChebyshevMinimax

/-!
# Convergence of the Krylov subspace towards an eigenvector

For a symmetric operator `A` with eigenvalues `λ_1 ≥ … ≥ λ_n` and orthonormal eigenvectors `u_1, …,
u_n`, this file bounds the angle between `u_i` and the Krylov subspace `𝒦_m(A, v)`, and through it
the error of the Ritz values computed on that subspace.  These are the convergence estimates of the
symmetric Lanczos process due to Kaniel, Paige and [saad2011numerical], stated in the angle
vocabulary of `Numlib.Analysis.InnerProductSpace.Projection.Angle` and following
[saad2011numerical], §6.6.  The three ingredients are the ones that also prove the conjugate
gradient error bound of `Numlib.Krylov.Convergence.CG`: a variational characterization, a polynomial
norm bound and a Chebyshev min–max.

## Main results

* `Lanczos.tan_angle_eq_iInf`: the tangent of the angle between an eigenvector `u` and `𝒦_m(A, v)`
  is a minimum over polynomials, `min { ‖p(A) w‖ / ‖⟪u, v⟫‖ : deg p < m, p μ = 1 }`, where `w = v -
  ⟪u, v⟫ u` is the part of `v` orthogonal to `u`.  This is what turns the geometry into a polynomial
  approximation problem. It needs one eigenpair rather than a full eigenbasis, and no finite
  dimension. `Lanczos.tan_angle_eq_iInf_mul` is the same statement with `w` normalized, which is how
  the source writes it, and `Lanczos.exists_norm_aeval_div_eq_tan_angle` says the minimum is
  attained.
* `Lanczos.tan_angle_le_of_forall_abs_eval_le`: every real polynomial that takes the value `1` at
  `λ_i` and is bounded by `M` at the other eigenvalues gives `tan θ(u_i, 𝒦_m) ≤ M tan θ(u_i, v)`.
  Everything below is this lemma together with a choice of polynomial.
* `Polynomial.exists_deflated_chebyshev`: the choice.  The polynomial with prescribed roots
  `Polynomial.deflator` removes finitely many points from the min–max problem at the cost of a
  factor, and the Chebyshev polynomial of an interval, normalized at a point outside it, is optimal
  for what remains.
* `Lanczos.tan_angle_le`: `tan θ(u_i, 𝒦_m) ≤ κ_i tan θ(u_i, v) / T_k(1 + 2 γ_i)`, where `T_k` is the
  Chebyshev polynomial of the first kind, `γ_i = (λ_i - λ_{i+1}) / (λ_{i+1} - λ_n)` and `κ_i = ∏_{j
  < i} (λ_j - λ_n) / (λ_j - λ_i)`.
* `Lanczos.kaniel_paige_saad`: the Kaniel–Paige–[saad2011numerical] bound on the error of the Ritz
  values `θ_i`, the eigenvalues of the compression of `A` to `𝒦_m(A, v)`: `0 ≤ λ_i - θ_i ≤ (λ_1 -
  λ_n) (κ_i tan θ(u_i, v) / T_k(1 + 2 γ_i))²`, where the deflation constant is now built from the
  Ritz values, `κ_i = ∏_{j < i} (θ_j - λ_n) / (θ_j - λ_i)`.  The lower bound is Cauchy interlacing;
  the upper bound is Courant–Fischer for the compression, the competitor vector being orthogonal to
  the first `i` Ritz vectors because the competitor polynomial vanishes at the corresponding Ritz
  values.

* `Arnoldi.norm_sub_starProjection_le_iInf`: the same variational idea without symmetry.  For a
  diagonalizable `A` with unit eigenvectors `u_k` and `v = ∑ α_k u_k`, the distance from `u_i` to
  `𝒦_m(A, v)` is bounded by a minimum over the same polynomials, now weighted by the expansion
  coefficients; `Arnoldi.norm_sub_starProjection_le_of_mem_closedBall` is the geometric decay
  `ξ_i (ρ/‖λ_i - c‖)^(m-1)` that a disc enclosing the rest of the spectrum gives, with `ξ_i = ∑_{k ≠
  i} ‖α_k‖/‖α_i‖`.  The triangle inequality replaces Pythagoras, which is why the factor `ξ_i`
  appears where the symmetric bounds have none.
* `Arnoldi.norm_sub_starProjection_le_of_mem_ellipse` is the same estimate for an *ellipse*
  enclosing the rest of the spectrum, with the Chebyshev ratio `C_{m-1}(a/d)/|C_{m-1}((λ_i - c)/d)|`
  in place of the geometric factor.  Its competitor is the shifted, normalized Chebyshev polynomial
  of `Numlib/RingTheory/Polynomial/ChebyshevEllipse`, whose maximum on the boundary ellipse is known
  and travels into the region the ellipse encloses by the maximum modulus principle there.

The angle bound and the Ritz value bound each come in two forms: one taking as data an interval
`[lo, hi]` enclosing the eigenvalues after the `i`-th (`…_of_mem_Icc`), which is the general
statement and carries the sharper constant `λ_i - lo` in place of `λ_1 - λ_n`, and one specializing
it to `[λ_n, λ_{i+1}]`, which is the form the literature states.

## Implementation notes

The source states the first lemma with the spectral projector onto the whole eigenspace of `λ_i`.
Here the projector is onto the line through the single eigenvector `u_i`, which is what keeps the
statement true at a multiple eigenvalue: the components of `v` along the other eigenvectors for
`λ_i` then belong to `w`, as they must, no Krylov subspace being able to separate them from `u_i`.
What the proof uses is that for symmetric `A` both `𝕜 ∙ u_i` and its orthogonal complement are
invariant.

Neighbouring and extreme indices are passed as data with their defining properties — `iS` with `i +
1 = iS`, and `first`, `last` characterized by `first ≤ j` and `j ≤ last` for all `j` — rather than
computed.  This keeps `Fin` arithmetic out of the statements, and lets a consumer that knows only
part of the spectrum still apply them.
-/

open Polynomial Polynomial.Chebyshev Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ### The angle to a line -/

namespace Submodule

/-- The tangent of the angle between a unit vector `u` and the line through `x`, computed from the
component of `x` along `u`.  Both sides are the junk value `0` when `x` is orthogonal to `u`, so no
hypothesis is needed. -/
theorem tanAngle_span_singleton {u : E} (hu : ‖u‖ = 1) (x : E) :
    (𝕜 ∙ x).tanAngle u = ‖x - (inner 𝕜 u x : 𝕜) • u‖ / ‖(inner 𝕜 u x : 𝕜)‖ := by
  have hconj : (inner 𝕜 x u : 𝕜) = starRingEnd 𝕜 (inner 𝕜 u x) := (inner_conj_symm x u).symm
  rcases eq_or_ne (inner 𝕜 u x : 𝕜) 0 with h | h
  · have hp : (𝕜 ∙ x).starProjection u = 0 := by
      rw [starProjection_singleton, hconj, h, map_zero, zero_div, zero_smul]
    rw [tanAngle, hp, norm_zero, div_zero, h, norm_zero, div_zero]
  · have hx0 : x ≠ 0 := by
      rintro rfl
      exact h (inner_zero_right u)
    have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx0
    have hnormxu : ‖(inner 𝕜 x u : 𝕜)‖ = ‖(inner 𝕜 u x : 𝕜)‖ := by
      rw [hconj, RCLike.norm_conj]
    have hproj : ‖(𝕜 ∙ x).starProjection u‖ = ‖(inner 𝕜 u x : 𝕜)‖ / ‖x‖ := by
      rw [starProjection_singleton, norm_smul, norm_div, hnormxu, RCLike.norm_ofReal,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2)]
      field_simp
    have hpyth1 : ‖(𝕜 ∙ x).starProjection u‖ ^ 2 + ‖u - (𝕜 ∙ x).starProjection u‖ ^ 2 = 1 := by
      rw [norm_starProjection_sq_add_norm_sub_sq, hu, one_pow]
    have hpyth2 : ‖(inner 𝕜 u x : 𝕜)‖ ^ 2 + ‖x - (inner 𝕜 u x : 𝕜) • u‖ ^ 2 = ‖x‖ ^ 2 := by
      have h2 := (𝕜 ∙ u).norm_starProjection_sq_add_norm_sub_sq x
      rw [starProjection_unit_singleton 𝕜 hu x, norm_smul, hu, mul_one] at h2
      exact h2
    have hsq : ‖u - (𝕜 ∙ x).starProjection u‖ ^ 2 = (‖x - (inner 𝕜 u x : 𝕜) • u‖ / ‖x‖) ^ 2 := by
      rw [div_pow, eq_div_iff (by positivity)]
      rw [hproj, div_pow] at hpyth1
      field_simp at hpyth1 ⊢
      nlinarith [hpyth1, hpyth2]
    have hnum : ‖u - (𝕜 ∙ x).starProjection u‖ = ‖x - (inner 𝕜 u x : 𝕜) • u‖ / ‖x‖ :=
      (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
    rw [tanAngle, hnum, hproj, div_div_div_cancel_right₀ hxn.ne']

/-- The tangent of the angle depends only on the subspace, so two spellings of the same subspace
give the same value even when their `HasOrthogonalProjection` instances are found by different
routes.  Rewriting a subspace under `tanAngle` directly fails, the instance argument depending on
it. -/
theorem tanAngle_congr {K L : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] (h : K = L) (u : E) : K.tanAngle u = L.tanAngle u := by
  subst h
  rfl

/-- The line through the orthogonal projection of `u` onto `K` makes the same angle with `u` as `K`
does: the projection of `u` onto that line is again `K.starProjection u`. -/
theorem starProjection_span_singleton_starProjection (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (u : E) :
    (𝕜 ∙ K.starProjection u).starProjection u = K.starProjection u := by
  refine starProjection_span_singleton_eq_self ?_
  have h0 := K.starProjection_inner_eq_zero u _ (K.starProjection_apply_mem u)
  rw [inner_sub_left, sub_eq_zero] at h0
  rw [← inner_conj_symm (K.starProjection u) u, h0, inner_conj_symm]

/-- The tangent of the angle between `u` and `K` is the tangent of the angle between `u` and the
line through its projection: the projection realizes the angle. -/
theorem tanAngle_span_singleton_starProjection (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (u : E) : (𝕜 ∙ K.starProjection u).tanAngle u = K.tanAngle u := by
  rw [tanAngle, tanAngle, starProjection_span_singleton_starProjection]

/-- A vector whose inner product with `u` does not vanish spans a line that captures part of `u`. -/
theorem starProjection_span_singleton_ne_zero {u x : E} (h : (inner 𝕜 u x : 𝕜) ≠ 0) :
    (𝕜 ∙ x).starProjection u ≠ 0 := by
  intro h0
  refine h ?_
  have hx : x ∈ (𝕜 ∙ x) := mem_span_singleton_self x
  have h1 := (𝕜 ∙ x).starProjection_inner_eq_zero u x hx
  rw [inner_sub_left, h0, sub_eq_zero] at h1
  rw [h1, inner_zero_left]

end Submodule

/-! ### Polynomials in a symmetric operator, tested against an eigenvector -/

/-- A polynomial in `A` acts on an eigenvector by the value of the polynomial at the eigenvalue. -/
theorem Polynomial.aeval_apply_of_apply_eq_smul {A : E →ₗ[𝕜] E} {u : E} {c : 𝕜} (h : A u = c • u)
    (p : 𝕜[X]) : aeval A p u = p.eval c • u := by
  have hpow : ∀ k : ℕ, (A ^ k) u = c ^ k • u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Module.End.mul_apply, h, map_smul, ih, smul_smul, ← pow_succ']
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply, hp, hq, eval_add, add_smul]
  | monomial k a =>
      have hmon : aeval A (monomial k a) u = a • (A ^ k) u := by simp [aeval_monomial]
      rw [hmon, hpow, smul_smul, eval_monomial]

namespace LinearMap.IsSymmetric

variable {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
include hA

/-- Testing a polynomial in a symmetric `A` against an eigenvector of `A` with real eigenvalue `μ`
scales the inner product by `p μ`.  This is the identity that turns the geometry of the Krylov
subspace into a polynomial approximation problem. -/
theorem inner_aeval_apply_of_apply_eq_smul {u : E} {μ : ℝ} (hu : A u = (μ : 𝕜) • u) (p : 𝕜[X])
    (x : E) : (inner 𝕜 u (aeval A p x) : 𝕜) = p.eval (μ : 𝕜) * inner 𝕜 u x := by
  have hpow : ∀ k : ℕ, (inner 𝕜 u ((A ^ k) x) : 𝕜) = (μ : 𝕜) ^ k * inner 𝕜 u x := by
    intro k
    induction k generalizing x with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, ← hA u, hu, inner_smul_left, RCLike.conj_ofReal, ih]
        ring
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply, inner_add_right, hp, hq, eval_add, add_mul]
  | monomial k a =>
      have hmon : aeval A (monomial k a) x = a • (A ^ k) x := by simp [aeval_monomial]
      rw [hmon, inner_smul_right, hpow, eval_monomial]
      ring

variable {n : ℕ} [FiniteDimensional 𝕜 E] (hn : Module.finrank 𝕜 E = n)
include hn

/-- A polynomial in a symmetric operator is bounded by the values of the polynomial at those
eigenvalues whose eigenvector actually occurs in `x`.  This refinement of
`LinearMap.IsSymmetric.norm_aeval_apply_le` is what lets a competitor polynomial be chosen with
roots at the eigenvalues that the vector misses. -/
theorem norm_aeval_apply_le_of_forall_repr (p : 𝕜[X]) {M : ℝ} (hM : 0 ≤ M) {x : E}
    (hp : ∀ j : Fin n, (hA.eigenvectorBasis hn).repr x j ≠ 0 →
      ‖p.eval (hA.eigenvalues hn j : 𝕜)‖ ≤ M) :
    ‖aeval A p x‖ ≤ M * ‖x‖ := by
  have key : ‖aeval A p x‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
    rw [hA.norm_sq_eq_sum_norm_repr_sq hn (aeval A p x), mul_pow,
      hA.norm_sq_eq_sum_norm_repr_sq hn x, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [hA.repr_aeval_apply hn, norm_mul, mul_pow]
    rcases eq_or_ne ((hA.eigenvectorBasis hn).repr x j) 0 with hz | hz
    · rw [hz]
      simp
    · gcongr
      exact hp j hz
  nlinarith [norm_nonneg (aeval A p x), mul_nonneg hM (norm_nonneg x)]

end LinearMap.IsSymmetric

/-! ### The deflating polynomial

`deflator s r c` is `∏_{j ∈ s} (r j - X) / (r j - c)`: it vanishes at each `r j` and takes the value
`1` at `c`.  Multiplying a competitor polynomial by it removes the eigenvalues indexed by `s` from a
min–max problem, at the price of the factor `∏_{j ∈ s} (r j - lo) / (r j - c)` on the interval `[lo,
hi]` to the left of `c`. -/

section Deflator

variable {ι : Type*}

/-- `∏_{j ∈ s} (r j - X) / (r j - c)`, the polynomial of degree `s.card` vanishing at every `r j`
and normalized to `1` at `c`. -/
noncomputable def Polynomial.deflator (s : Finset ι) (r : ι → ℝ) (c : ℝ) : ℝ[X] :=
  ∏ j ∈ s, C (r j - c)⁻¹ * (C (r j) - X)

namespace Polynomial

variable (s : Finset ι) (r : ι → ℝ) (c : ℝ)

/-- The value of the deflating polynomial, as the product it is defined by. -/
theorem deflator_eval (t : ℝ) :
    (deflator s r c).eval t = ∏ j ∈ s, (r j - t) / (r j - c) := by
  rw [deflator, eval_prod]
  exact Finset.prod_congr rfl fun j _ => by rw [eval_mul, eval_C, eval_sub, eval_C, eval_X,
    div_eq_inv_mul]

/-- The deflating polynomial has degree at most the number of roots it prescribes: this is what it
costs in the degree budget of the min–max problem. -/
theorem deflator_degree_le : (deflator s r c).degree ≤ s.card := by
  rw [deflator]
  refine degree_le_of_natDegree_le (le_trans (natDegree_prod_le s _) ?_)
  refine le_trans (Finset.sum_le_sum (g := fun _ => 1) fun j _ => ?_) (by simp)
  compute_degree

/-- The deflating polynomial is normalized to `1` at `c`, as the min–max problem requires. -/
theorem deflator_eval_self (h : ∀ j ∈ s, r j ≠ c) : (deflator s r c).eval c = 1 := by
  rw [deflator_eval]
  exact Finset.prod_eq_one fun j hj => div_self (sub_ne_zero.2 (h j hj))

/-- The deflating polynomial vanishes at each prescribed root, which is what removes that point from
the min–max problem. -/
theorem deflator_eval_eq_zero {j : ι} (hj : j ∈ s) : (deflator s r c).eval (r j) = 0 := by
  rw [deflator_eval]
  exact Finset.prod_eq_zero hj (by rw [sub_self, zero_div])

/-- On an interval `[lo, hi]` lying to the left of `c`, which in turn lies to the left of every `r
j`, the deflating polynomial is bounded by its value at `lo`. -/
theorem abs_deflator_eval_le (h : ∀ j ∈ s, c < r j) {lo hi t : ℝ} (hhi : hi < c) (hlo : lo ≤ t)
    (ht : t ≤ hi) : |(deflator s r c).eval t| ≤ ∏ j ∈ s, (r j - lo) / (r j - c) := by
  have hfac : ∀ j ∈ s, 0 ≤ (r j - t) / (r j - c) := fun j hj =>
    div_nonneg (by linarith [h j hj]) (by linarith [h j hj])
  rw [deflator_eval, abs_of_nonneg (Finset.prod_nonneg hfac)]
  refine Finset.prod_le_prod hfac fun j hj => ?_
  exact div_le_div_of_nonneg_right (by linarith) (by linarith [h j hj])

/-- **The competitor polynomial of the Krylov eigenvalue bounds.**  For an interval `[lo, hi]` lying
to the left of `c`, which in turn lies to the left of every `r j`, there is a polynomial of degree
at most `s.card + k` that takes the value `1` at `c`, vanishes at every `r j`, and on `[lo, hi]` is
bounded by `(∏_{j ∈ s} (r j - lo) / (r j - c)) / T_k((2 c - hi - lo) / (hi - lo))`, where `T_k` is
the Chebyshev polynomial of the first kind.

It is the deflating polynomial for `s` times the Chebyshev polynomial of `[lo, hi]` normalized to
`1` at `c`, and the bound is the product of the two bounds: `∏ (r j - lo) / (r j - c)` is what the
deflation costs and `1 / T_k` is the Chebyshev min–max value. -/
theorem exists_deflated_chebyshev (hr : ∀ j ∈ s, c < r j) {lo hi : ℝ} (hlohi : lo < hi)
    (hhi : hi < c) (k : ℕ) :
    ∃ q : ℝ[X], q.degree ≤ ((s.card + k : ℕ) : WithBot ℕ) ∧ q.eval c = 1 ∧
      (∀ j ∈ s, q.eval (r j) = 0) ∧
      ∀ t ∈ Set.Icc lo hi, |q.eval t| ≤
        (∏ j ∈ s, (r j - lo) / (r j - c)) /
          (T ℝ k).eval ((2 * c - hi - lo) / (hi - lo)) := by
  have hd : (0 : ℝ) < hi - lo := by linarith
  have hnotmem : c ∉ Set.Icc lo hi := fun hc => absurd hc.2 (not_le.2 hhi)
  have hz1 : (1 : ℝ) ≤ (2 * c - hi - lo) / (hi - lo) := by
    rw [le_div_iff₀ hd]
    linarith
  have hT : (1 : ℝ) ≤ (T ℝ k).eval ((2 * c - hi - lo) / (hi - lo)) := one_le_eval_T hz1 k
  have hkappa : (0 : ℝ) ≤ ∏ j ∈ s, (r j - lo) / (r j - c) :=
    Finset.prod_nonneg fun j hj => div_nonneg (by linarith [hr j hj]) (by linarith [hr j hj])
  have habsT : |(T ℝ k).eval ((hi + lo - 2 * c) / (hi - lo))| =
      (T ℝ k).eval ((2 * c - hi - lo) / (hi - lo)) := by
    have hneg : (hi + lo - 2 * c) / (hi - lo) = -((2 * c - hi - lo) / (hi - lo)) := by
      rw [← neg_div]
      congr 1
      ring
    have h1 : |(T ℝ k).eval (-((2 * c - hi - lo) / (hi - lo)))| =
        |(T ℝ k).eval ((2 * c - hi - lo) / (hi - lo))| := by simp [T_eval_neg, abs_mul]
    rw [hneg, h1, abs_of_nonneg (by linarith)]
  refine ⟨deflator s r c * shifted k lo hi c, ?_, ?_, ?_, ?_⟩
  · refine le_trans (degree_mul_le _ _) ?_
    calc (deflator s r c).degree + (shifted k lo hi c).degree
        ≤ ((s.card : ℕ) : WithBot ℕ) + ((k : ℕ) : WithBot ℕ) :=
          add_le_add (deflator_degree_le s r c) (shifted_degree_le k lo hi c)
      _ = ((s.card + k : ℕ) : WithBot ℕ) := by push_cast; ring
  · rw [eval_mul, deflator_eval_self _ _ _ fun j hj => (hr j hj).ne',
      shifted_eval_self _ hlohi hnotmem, one_mul]
  · intro j hj
    rw [eval_mul, deflator_eval_eq_zero _ _ _ hj, zero_mul]
  · intro t ht
    have hbdd : BddAbove ((fun t' => |(shifted k lo hi c).eval t'|) '' Set.Icc lo hi) :=
      (isCompact_Icc.image (shifted k lo hi c).continuous.abs).bddAbove
    have h2 := le_csSup hbdd ⟨t, ht, rfl⟩
    rw [sSup_abs_eval_shifted _ hlohi hnotmem, habsT] at h2
    rw [eval_mul, abs_mul, ← mul_one_div]
    exact mul_le_mul (abs_deflator_eval_le s r c hr hhi ht.1 ht.2) h2 (abs_nonneg _) hkappa

end Polynomial

end Deflator

/-! ### The angle between an eigenvector and the Krylov subspace -/

namespace Lanczos

section Lemma

variable {A : E →ₗ[𝕜] E} {u v : E} {μ : ℝ} (hA : A.IsSymmetric) (hu : ‖u‖ = 1)
  (hAu : A u = (μ : 𝕜) • u)
include hA hu hAu

/-- The line through `p(A) v` makes with the eigenvector `u` the angle whose tangent is `‖p(A) w‖ /
‖⟪u, v⟫‖`, where `w = v - ⟪u, v⟫ u` is the part of `v` orthogonal to `u`. -/
private theorem tanAngle_span_singleton_aeval (p : 𝕜[X]) (hp : p.eval (μ : 𝕜) = 1) :
    (𝕜 ∙ aeval A p v).tanAngle u =
      ‖aeval A p (v - (inner 𝕜 u v : 𝕜) • u)‖ / ‖(inner 𝕜 u v : 𝕜)‖ := by
  have h1 : (inner 𝕜 u (aeval A p v) : 𝕜) = inner 𝕜 u v := by
    rw [hA.inner_aeval_apply_of_apply_eq_smul hAu, hp, one_mul]
  have h2 : aeval A p (v - (inner 𝕜 u v : 𝕜) • u) = aeval A p v - (inner 𝕜 u v : 𝕜) • u := by
    rw [map_sub, map_smul, Polynomial.aeval_apply_of_apply_eq_smul hAu, hp, one_smul]
  rw [Submodule.tanAngle_span_singleton hu, h1, h2]

variable (hv : (inner 𝕜 u v : 𝕜) ≠ 0)
include hv

/-- Every polynomial of degree below `m` normalized to `1` at the eigenvalue gives an upper bound
for the tangent of the angle between the eigenvector and the Krylov subspace: the vector `p(A) v`
lies in the subspace and the angle to a line of the subspace is at least the angle to the subspace.
-/
theorem tan_angle_le_norm_aeval_div {m : ℕ} (p : 𝕜[X]) (hdeg : p.degree < m)
    (hp : p.eval (μ : 𝕜) = 1) :
    (Krylov.subspace A v m).tanAngle u ≤
      ‖aeval A p (v - (inner 𝕜 u v : 𝕜) • u)‖ / ‖(inner 𝕜 u v : 𝕜)‖ := by
  have hinner : (inner 𝕜 u (aeval A p v) : 𝕜) ≠ 0 := by
    rw [hA.inner_aeval_apply_of_apply_eq_smul hAu, hp, one_mul]
    exact hv
  rw [← tanAngle_span_singleton_aeval hA hu hAu p hp]
  exact Submodule.tanAngle_le_of_le
    ((Submodule.span_singleton_le_iff_mem _ _).2 (Krylov.aeval_apply_mem_subspace A v hdeg))
    (Submodule.starProjection_span_singleton_ne_zero hinner)

/-- The bound of `Lanczos.tan_angle_le_norm_aeval_div` is attained: the polynomial that carries `v`
to the orthogonal projection of `u` onto the Krylov subspace realizes the angle.  This is what makes
the infimum of `Lanczos.tan_angle_eq_iInf` a minimum. -/
theorem exists_norm_aeval_div_eq_tan_angle {m : ℕ} (hm : 0 < m) :
    ∃ p : 𝕜[X], p.degree < m ∧ p.eval (μ : 𝕜) = 1 ∧
      ‖aeval A p (v - (inner 𝕜 u v : 𝕜) • u)‖ / ‖(inner 𝕜 u v : 𝕜)‖ =
        (Krylov.subspace A v m).tanAngle u := by
  have hvK : v ∈ Krylov.subspace A v m := Krylov.self_mem_subspace A v hm
  have hproj : (Krylov.subspace A v m).starProjection u ≠ 0 := by
    intro h0
    refine hv ?_
    have h1 := (Krylov.subspace A v m).starProjection_inner_eq_zero u v hvK
    rw [inner_sub_left, h0, sub_eq_zero] at h1
    rw [h1, inner_zero_left]
  have hinner : (inner 𝕜 u ((Krylov.subspace A v m).starProjection u) : 𝕜) ≠ 0 := by
    have h1 := (Krylov.subspace A v m).starProjection_inner_eq_zero u _
      ((Krylov.subspace A v m).starProjection_apply_mem u)
    rw [inner_sub_left, sub_eq_zero] at h1
    rw [h1]
    exact inner_self_ne_zero.2 hproj
  obtain ⟨q, hqdeg, hq⟩ := (Krylov.mem_subspace_iff_exists_aeval A v).1
    ((Krylov.subspace A v m).starProjection_apply_mem u)
  have hd : q.eval (μ : 𝕜) ≠ 0 := by
    intro h0
    rw [← hq, hA.inner_aeval_apply_of_apply_eq_smul hAu, h0, zero_mul] at hinner
    exact hinner rfl
  have hp' : ((q.eval (μ : 𝕜))⁻¹ • q).eval (μ : 𝕜) = 1 := by
    rw [eval_smul, smul_eq_mul, inv_mul_cancel₀ hd]
  have hsm : aeval A ((q.eval (μ : 𝕜))⁻¹ • q) v =
      (q.eval (μ : 𝕜))⁻¹ • (Krylov.subspace A v m).starProjection u := by
    rw [map_smul, LinearMap.smul_apply, hq]
  refine ⟨(q.eval (μ : 𝕜))⁻¹ • q, lt_of_le_of_lt (degree_smul_le _ q) hqdeg, hp', ?_⟩
  rw [← tanAngle_span_singleton_aeval hA hu hAu _ hp', hsm,
    Submodule.tanAngle_congr (Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero hd)) _) u,
    Submodule.tanAngle_span_singleton_starProjection]

/-- **The tangent of the angle between an eigenvector and the Krylov subspace as a polynomial
minimum.**  For a symmetric `A` with eigenpair `(μ, u)`, `u` a unit vector, and a starting vector
`v` not orthogonal to `u`,

`tan θ(u, 𝒦_m(A, v)) = min { ‖p(A) w‖ / ‖⟪u, v⟫‖ : deg p < m, p μ = 1 }`,

where `w = v - ⟪u, v⟫ u` is the part of `v` orthogonal to `u`.  The infimum is attained
(`Lanczos.exists_norm_aeval_div_eq_tan_angle`), and at `m = 0` both sides are `0`: the index type is
empty there and `𝒦_0 = ⊥`.

Only the eigenpair is needed, not a full eigenbasis: for symmetric `A` the line `𝕜 ∙ u` and its
orthogonal complement are both invariant, which is what splits `p(A) v` into its component along `u`
and the rest.  In particular `u` is a *single* eigenvector, not the whole eigenspace of `μ`; with a
multiple eigenvalue the components of `v` along the other eigenvectors for `μ` are counted in `w`,
as they must be — no Krylov subspace can separate them from `u`. -/
theorem tan_angle_eq_iInf (m : ℕ) :
    (Krylov.subspace A v m).tanAngle u =
      ⨅ p : {p : 𝕜[X] // p.degree < m ∧ p.eval (μ : 𝕜) = 1},
        ‖aeval A (p : 𝕜[X]) (v - (inner 𝕜 u v : 𝕜) • u)‖ / ‖(inner 𝕜 u v : 𝕜)‖ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hempty : IsEmpty {p : 𝕜[X] // p.degree < (0 : ℕ) ∧ p.eval (μ : 𝕜) = 1} := by
      refine ⟨fun p => ?_⟩
      have hne : (p : 𝕜[X]) ≠ 0 := by
        intro h0
        have h1 := p.2.2
        rw [h0, eval_zero] at h1
        exact zero_ne_one h1
      have h1 : (p : 𝕜[X]).degree < 0 := by exact_mod_cast p.2.1
      exact absurd h1 (not_lt.2 (zero_le_degree_iff.2 hne))
    rw [Submodule.tanAngle_congr (Krylov.subspace_zero A v) u, Submodule.tanAngle_bot,
      Real.iInf_of_isEmpty]
  · have hbdd : BddBelow (Set.range fun p : {p : 𝕜[X] // p.degree < m ∧ p.eval (μ : 𝕜) = 1} =>
        ‖aeval A (p : 𝕜[X]) (v - (inner 𝕜 u v : 𝕜) • u)‖ / ‖(inner 𝕜 u v : 𝕜)‖) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨p, rfl⟩
      positivity
    obtain ⟨p, hdeg, hp, hval⟩ := exists_norm_aeval_div_eq_tan_angle hA hu hAu hv hm
    have hnonempty : Nonempty {p : 𝕜[X] // p.degree < m ∧ p.eval (μ : 𝕜) = 1} :=
      ⟨⟨p, hdeg, hp⟩⟩
    refine le_antisymm
      (le_ciInf fun q => tan_angle_le_norm_aeval_div hA hu hAu hv (q : 𝕜[X]) q.2.1 q.2.2) ?_
    rw [← hval]
    exact ciInf_le hbdd ⟨p, hdeg, hp⟩

/-- `Lanczos.tan_angle_eq_iInf` in the normalized form the source states it in: with `y = w / ‖w‖`
the normalized part of `v` orthogonal to the eigenvector `u`,

`tan θ(u, 𝒦_m(A, v)) = min { ‖p(A) y‖ : deg p < m, p μ = 1 } · tan θ(u, v)`.

At `w = 0` — that is, when `v` is already a multiple of `u` — the normalization has the junk value
`y = 0` and both sides are `0`, which is the convention the source adopts explicitly. -/
theorem tan_angle_eq_iInf_mul (m : ℕ) :
    (Krylov.subspace A v m).tanAngle u =
      ⨅ p : {p : 𝕜[X] // p.degree < m ∧ p.eval (μ : 𝕜) = 1},
        ‖aeval A (p : 𝕜[X]) (((‖v - (inner 𝕜 u v : 𝕜) • u‖ : ℝ) : 𝕜)⁻¹ •
            (v - (inner 𝕜 u v : 𝕜) • u))‖ * (𝕜 ∙ v).tanAngle u := by
  rw [tan_angle_eq_iInf hA hu hAu hv m, Submodule.tanAngle_span_singleton hu v]
  refine iInf_congr fun p => ?_
  rcases eq_or_ne (v - (inner 𝕜 u v : 𝕜) • u) 0 with h0 | h0
  · rw [h0]
    simp
  · have hw : (0 : ℝ) < ‖v - (inner 𝕜 u v : 𝕜) • u‖ := norm_pos_iff.2 h0
    rw [map_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg hw.le]
    field_simp

end Lemma

/-! ### From a polynomial estimate to an angle bound -/

section Eigenbasis

/-- The value of a real polynomial mapped into `𝕜`, at a real point. -/
private theorem eval_map_ofReal (p : ℝ[X]) (t : ℝ) :
    (p.map (algebraMap ℝ 𝕜)).eval ((t : ℝ) : 𝕜) = ((p.eval t : ℝ) : 𝕜) := by
  rw [← RCLike.algebraMap_eq_ofReal, eval_map, eval₂_at_apply, RCLike.algebraMap_eq_ofReal]

variable {A : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E] {n : ℕ} (hA : A.IsSymmetric)
  (hn : Module.finrank 𝕜 E = n)
include hA hn

/-- **Every competitor polynomial gives an angle bound.**  If a real polynomial `p` of degree below
`m` takes the value `1` at the `i`-th eigenvalue and is bounded by `M` at all the others, then `tan
θ(u_i, 𝒦_m(A, v)) ≤ M tan θ(u_i, v)`.

This is the half of the Krylov eigenvector estimate that does not depend on which polynomial is
chosen: the whole content of Chebyshev bounds such as `Lanczos.tan_angle_le` is the choice of `p`
and the estimate of `M`. -/
theorem tan_angle_le_of_forall_abs_eval_le (i : Fin n) {v : E}
    (hv : (inner 𝕜 (hA.eigenvectorBasis hn i) v : 𝕜) ≠ 0) {m : ℕ} (p : ℝ[X])
    (hdeg : p.degree < m) (hp : p.eval (hA.eigenvalues hn i) = 1) {M : ℝ} (hM : 0 ≤ M)
    (hbnd : ∀ j : Fin n, j ≠ i → |p.eval (hA.eigenvalues hn j)| ≤ M) :
    (Krylov.subspace A v m).tanAngle (hA.eigenvectorBasis hn i) ≤
      M * (𝕜 ∙ v).tanAngle (hA.eigenvectorBasis hn i) := by
  have hu : ‖hA.eigenvectorBasis hn i‖ = 1 := (hA.eigenvectorBasis hn).norm_eq_one i
  have hAu : A (hA.eigenvectorBasis hn i) =
      ((hA.eigenvalues hn i : ℝ) : 𝕜) • hA.eigenvectorBasis hn i :=
    hA.apply_eigenvectorBasis hn i
  have hdeg' : (p.map (algebraMap ℝ 𝕜)).degree < (m : ℕ) := lt_of_le_of_lt degree_map_le hdeg
  have hp' : (p.map (algebraMap ℝ 𝕜)).eval ((hA.eigenvalues hn i : ℝ) : 𝕜) = 1 := by
    rw [eval_map_ofReal, hp, RCLike.ofReal_one]
  have hwi : (hA.eigenvectorBasis hn).repr
      (v - (inner 𝕜 (hA.eigenvectorBasis hn i) v : 𝕜) • hA.eigenvectorBasis hn i) i = 0 := by
    rw [OrthonormalBasis.repr_apply_apply, inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hu]
    simp
  have hbnd' : ∀ j : Fin n, (hA.eigenvectorBasis hn).repr
      (v - (inner 𝕜 (hA.eigenvectorBasis hn i) v : 𝕜) • hA.eigenvectorBasis hn i) j ≠ 0 →
      ‖(p.map (algebraMap ℝ 𝕜)).eval ((hA.eigenvalues hn j : ℝ) : 𝕜)‖ ≤ M := by
    intro j hj
    rw [eval_map_ofReal, RCLike.norm_ofReal]
    refine hbnd j fun hji => hj ?_
    rw [hji, hwi]
  have h1 := tan_angle_le_norm_aeval_div hA hu hAu hv (p.map (algebraMap ℝ 𝕜)) hdeg' hp'
  have h2 := hA.norm_aeval_apply_le_of_forall_repr hn (p.map (algebraMap ℝ 𝕜)) hM hbnd'
  refine h1.trans ?_
  rw [Submodule.tanAngle_span_singleton hu v, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right h2 (norm_nonneg _)

/-! ### The Chebyshev bound on the angle -/

/-- **The Chebyshev bound on the angle between an eigenvector and the Krylov subspace**, in the form
that takes the enclosing interval as data.  Let `λ` be the eigenvalues of a symmetric `A` in
decreasing order, `u_i` the `i`-th eigenvector and `v` a starting vector not orthogonal to it.
Suppose the eigenvalues after the `i`-th all lie in an interval `[lo, hi]` that stays to the left of
`λ_i`, and that the eigenvalues before the `i`-th are all strictly larger than `λ_i`.  Then

`tan θ(u_i, 𝒦_m(A, v)) ≤ (κ / T_{m-1-i}((2 λ_i - hi - lo) / (hi - lo))) tan θ(u_i, v)`,

where `T_k` is the Chebyshev polynomial of the first kind and `κ = ∏_{j < i} (λ_j - lo) / (λ_j -
λ_i)`.

The competitor is the product of the polynomial with roots at the `i` eigenvalues before `λ_i`,
which removes them from the problem at the cost of the factor `κ`, with the Chebyshev polynomial of
`[lo, hi]` normalized to `1` at `λ_i`, which is the minimax choice for what remains. -/
theorem tan_angle_le_of_mem_Icc (i : Fin n) {v : E}
    (hv : (inner 𝕜 (hA.eigenvectorBasis hn i) v : 𝕜) ≠ 0) {lo hi : ℝ} (hlohi : lo < hi)
    (hhi : hi < hA.eigenvalues hn i)
    (hmem : ∀ j : Fin n, i < j → hA.eigenvalues hn j ∈ Set.Icc lo hi)
    (hsep : ∀ j : Fin n, j < i → hA.eigenvalues hn i < hA.eigenvalues hn j)
    {m k : ℕ} (hm : (i : ℕ) + k < m) :
    (Krylov.subspace A v m).tanAngle (hA.eigenvectorBasis hn i) ≤
      (∏ j ∈ Finset.Iio i,
          (hA.eigenvalues hn j - lo) / (hA.eigenvalues hn j - hA.eigenvalues hn i)) /
        (T ℝ k).eval
          ((2 * hA.eigenvalues hn i - hi - lo) / (hi - lo)) *
        (𝕜 ∙ v).tanAngle (hA.eigenvectorBasis hn i) := by
  have hsep' : ∀ j ∈ Finset.Iio i, hA.eigenvalues hn i < hA.eigenvalues hn j := fun j hj =>
    hsep j (Finset.mem_Iio.1 hj)
  have hT : (1 : ℝ) ≤ (T ℝ k).eval ((2 * hA.eigenvalues hn i - hi - lo) / (hi - lo)) :=
    one_le_eval_T (by rw [le_div_iff₀ (by linarith : (0 : ℝ) < hi - lo)]; linarith) k
  have hM : (0 : ℝ) ≤ (∏ j ∈ Finset.Iio i,
      (hA.eigenvalues hn j - lo) / (hA.eigenvalues hn j - hA.eigenvalues hn i)) /
      (T ℝ k).eval ((2 * hA.eigenvalues hn i - hi - lo) / (hi - lo)) :=
    div_nonneg (Finset.prod_nonneg fun j hj =>
      div_nonneg (by linarith [hsep' j hj]) (by linarith [hsep' j hj])) (by linarith)
  obtain ⟨q, hqdeg, hq1, hqz, hqb⟩ := exists_deflated_chebyshev (Finset.Iio i)
    (hA.eigenvalues hn) (hA.eigenvalues hn i) hsep' hlohi hhi k
  refine tan_angle_le_of_forall_abs_eval_le hA hn i hv q ?_ hq1 hM ?_
  · refine lt_of_le_of_lt hqdeg ?_
    rw [Nat.cast_lt, Fin.card_Iio]
    omega
  · intro j hj
    rcases lt_or_gt_of_ne hj with hji | hji
    · rw [hqz j (Finset.mem_Iio.2 hji), abs_zero]
      exact hM
    · exact hqb _ (hmem j hji)


/-! ### The Kaniel–Paige–[saad2011numerical] bound on the Ritz values -/

/-- **The Kaniel–Paige–[saad2011numerical] bound**, upper half, in the form that takes the enclosing
interval as data.  Write `λ` for the eigenvalues of a symmetric `A` in decreasing order and `θ` for
the eigenvalues of its compression to `𝒦_m(A, v)` — the Ritz values — again in decreasing order.
Suppose the eigenvalues after the `i'`-th all lie in an interval `[lo, hi]` to the left of `λ_{i'}`,
and that the `i` Ritz values before the `i`-th are all larger than `λ_{i'}`.  Then

`λ_{i'} - θ_i ≤ (λ_{i'} - lo) (κ tan θ(u_{i'}, v) / T_k((2 λ_{i'} - hi - lo) / (hi - lo)))²`

with `κ = ∏_{j < i} (θ_j - lo) / (θ_j - λ_{i'})`, provided `i + k < m`.

The two indices are unrelated by any hypothesis, but the intended reading pairs them: with `i' = i`
this is the Kaniel–Paige–[saad2011numerical] estimate.  The proof is Courant–Fischer for the
compression: the competitor `q(A) v` of `Lanczos.exists_deflated_chebyshev` is orthogonal to the
first `i` Ritz vectors because `q` vanishes at the corresponding Ritz values, so its Rayleigh
quotient is at most `θ_i`, and the deflation cost `κ` is paid in the Ritz values rather than in the
eigenvalues.

Both `λ_{i'} - lo` and, in the intended application, `λ_1 - λ_n` bound the spread that turns the
angle into an eigenvalue error; the form here is the sharper one. -/
theorem eigenvalues_sub_eigenvalues_compression_le_of_mem_Icc {v : E} {m : ℕ}
    (hm : Module.finrank 𝕜 (Krylov.subspace A v m) = m) (i : Fin m) (i' : Fin n)
    (hv : (inner 𝕜 (hA.eigenvectorBasis hn i') v : 𝕜) ≠ 0) {lo hi : ℝ} (hlohi : lo < hi)
    (hhi : hi < hA.eigenvalues hn i')
    (hmem : ∀ j : Fin n, i' < j → hA.eigenvalues hn j ∈ Set.Icc lo hi)
    (hθ : ∀ j : Fin m, j < i → hA.eigenvalues hn i' <
      (compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j)
    {k : ℕ} (hk : (i : ℕ) + k < m) :
    hA.eigenvalues hn i' -
        (compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm i ≤
      (hA.eigenvalues hn i' - lo) *
        ((∏ j ∈ Finset.Iio i,
            ((compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j - lo) /
              ((compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j -
                hA.eigenvalues hn i')) /
            (T ℝ k).eval ((2 * hA.eigenvalues hn i' - hi - lo) / (hi - lo)) *
          (𝕜 ∙ v).tanAngle (hA.eigenvectorBasis hn i')) ^ 2 := by
  have hvK : v ∈ Krylov.subspace A v m := Krylov.self_mem_subspace A v i.pos
  have hu : ‖hA.eigenvectorBasis hn i'‖ = 1 := (hA.eigenvectorBasis hn).norm_eq_one i'
  obtain ⟨q, hqdeg, hq1, hqz, hqb⟩ := exists_deflated_chebyshev (Finset.Iio i)
    ((compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm)
    (hA.eigenvalues hn i') (fun j hj => hθ j (Finset.mem_Iio.1 hj)) hlohi hhi k
  set M : ℝ := (∏ j ∈ Finset.Iio i,
      ((compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j - lo) /
        ((compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j -
          hA.eigenvalues hn i')) /
    (T ℝ k).eval ((2 * hA.eigenvalues hn i' - hi - lo) / (hi - lo)) with hMdef
  have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hqb lo ⟨le_rfl, hlohi.le⟩)
  -- the competitor vector and its eigenbasis coordinates
  have hqq : (q.map (algebraMap ℝ 𝕜)).degree < (m : ℕ) := by
    refine lt_of_le_of_lt degree_map_le (lt_of_le_of_lt hqdeg ?_)
    rw [Nat.cast_lt, Fin.card_Iio]
    omega
  have hxK : aeval A (q.map (algebraMap ℝ 𝕜)) v ∈ Krylov.subspace A v m :=
    Krylov.aeval_apply_mem_subspace A v hqq
  have hrepr : ∀ j : Fin n,
      (hA.eigenvectorBasis hn).repr (aeval A (q.map (algebraMap ℝ 𝕜)) v) j =
        ((q.eval (hA.eigenvalues hn j) : ℝ) : 𝕜) * (hA.eigenvectorBasis hn).repr v j := fun j => by
    rw [hA.repr_aeval_apply hn, eval_map_ofReal]
  have hcv : (hA.eigenvectorBasis hn).repr v i' = (inner 𝕜 (hA.eigenvectorBasis hn i') v : 𝕜) :=
    OrthonormalBasis.repr_apply_apply _ _ _
  have hxi : (hA.eigenvectorBasis hn).repr (aeval A (q.map (algebraMap ℝ 𝕜)) v) i' =
      (hA.eigenvectorBasis hn).repr v i' := by
    rw [hrepr, hq1, RCLike.ofReal_one, one_mul]
  have hx0 : aeval A (q.map (algebraMap ℝ 𝕜)) v ≠ 0 := by
    intro h0
    refine hv ?_
    rw [← hcv, ← hxi, h0]
    simp
  -- orthogonality to the first `i` Ritz vectors
  have hqne : q.map (algebraMap ℝ 𝕜) ≠ 0 := by
    intro h0
    have h1 : ((q.eval (hA.eigenvalues hn i') : ℝ) : 𝕜) = 0 := by
      rw [← eval_map_ofReal q (hA.eigenvalues hn i'), h0, eval_zero]
    rw [hq1] at h1
    simp at h1
  have hnd : (q.map (algebraMap ℝ 𝕜)).natDegree < m :=
    (Polynomial.natDegree_lt_iff_degree_lt hqne).2 hqq
  have hy : (⟨aeval A (q.map (algebraMap ℝ 𝕜)) v, hxK⟩ : Krylov.subspace A v m) =
      aeval (compression A (Krylov.subspace A v m)) (q.map (algebraMap ℝ 𝕜)) ⟨v, hvK⟩ :=
    Subtype.ext (compression.aeval_apply_of_forall_pow_mem A (Krylov.subspace A v m)
      (q.map (algebraMap ℝ 𝕜)) (x := ⟨v, hvK⟩)
      (fun l hl => Krylov.pow_apply_mem_subspace A v (lt_of_le_of_lt hl hnd))).symm
  have horth : ∀ j : Fin m, j < i → (inner 𝕜
      ((compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvectorBasis hm j)
      (⟨aeval A (q.map (algebraMap ℝ 𝕜)) v, hxK⟩ : Krylov.subspace A v m) : 𝕜) = 0 := by
    intro j hj
    rw [← OrthonormalBasis.repr_apply_apply, hy,
      (compression.isSymmetric A (Krylov.subspace A v m) hA).repr_aeval_apply hm,
      eval_map_ofReal, hqz j (Finset.mem_Iio.2 hj), RCLike.ofReal_zero, zero_mul]
  -- Courant–Fischer for the compression
  have hrq : (compression A (Krylov.subspace A v m)).rayleighQuotient
      (⟨aeval A (q.map (algebraMap ℝ 𝕜)) v, hxK⟩ : Krylov.subspace A v m) =
      A.rayleighQuotient (aeval A (q.map (algebraMap ℝ 𝕜)) v) :=
    Krylov.rayleighQuotient_compression A _ _
  have hle : A.rayleighQuotient (aeval A (q.map (algebraMap ℝ 𝕜)) v) ≤
      (compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm i :=
    ((compression.isSymmetric A (Krylov.subspace A v m) hA).isGreatest_rayleighQuotient_orthogonal
      hm i).2 ⟨_, fun h0 => hx0 (Submodule.coe_eq_zero.2 h0), horth, hrq⟩
  -- the numerator, in eigenbasis coordinates
  have hnum := hA.mul_norm_sq_sub_re_inner_eq_sum hn (hA.eigenvalues hn i')
    (aeval A (q.map (algebraMap ℝ 𝕜)) v)
  -- the part of `v` orthogonal to the eigenvector
  have hwrepr : ∀ j : Fin n, j ≠ i' →
      (hA.eigenvectorBasis hn).repr
          (v - (inner 𝕜 (hA.eigenvectorBasis hn i') v : 𝕜) • hA.eigenvectorBasis hn i') j =
        (hA.eigenvectorBasis hn).repr v j := by
    intro j hj
    rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply, inner_sub_right,
      inner_smul_right, (hA.eigenvectorBasis hn).inner_eq_zero hj, mul_zero, sub_zero]
  have hwnorm : ∑ j ∈ Finset.Ioi i', ‖(hA.eigenvectorBasis hn).repr v j‖ ^ 2 ≤
      ‖v - (inner 𝕜 (hA.eigenvectorBasis hn i') v : 𝕜) • hA.eigenvectorBasis hn i'‖ ^ 2 := by
    rw [hA.norm_sq_eq_sum_norm_repr_sq hn]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun j hj => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity)
    rw [hwrepr j (ne_of_gt (Finset.mem_Ioi.1 hj))]
  -- the numerator estimate
  have hN : hA.eigenvalues hn i' * ‖aeval A (q.map (algebraMap ℝ 𝕜)) v‖ ^ 2 -
      RCLike.re (inner 𝕜 (A (aeval A (q.map (algebraMap ℝ 𝕜)) v))
        (aeval A (q.map (algebraMap ℝ 𝕜)) v)) ≤
      (hA.eigenvalues hn i' - lo) * (M ^ 2 *
        ‖v - (inner 𝕜 (hA.eigenvectorBasis hn i') v : 𝕜) • hA.eigenvectorBasis hn i'‖ ^ 2) := by
    rw [hnum, ← Finset.sum_add_sum_compl (Finset.Ioi i')]
    have hcompl : ∑ j ∈ (Finset.Ioi i')ᶜ, (hA.eigenvalues hn i' - hA.eigenvalues hn j) *
        ‖(hA.eigenvectorBasis hn).repr (aeval A (q.map (algebraMap ℝ 𝕜)) v) j‖ ^ 2 ≤ 0 := by
      refine Finset.sum_nonpos fun j hj => ?_
      have hji : j ≤ i' := not_lt.1 (by simpa using Finset.mem_compl.1 hj)
      have := hA.eigenvalues_antitone hn hji
      nlinarith [sq_nonneg ‖(hA.eigenvectorBasis hn).repr (aeval A (q.map (algebraMap ℝ 𝕜)) v) j‖]
    have hIoi : ∑ j ∈ Finset.Ioi i', (hA.eigenvalues hn i' - hA.eigenvalues hn j) *
        ‖(hA.eigenvectorBasis hn).repr (aeval A (q.map (algebraMap ℝ 𝕜)) v) j‖ ^ 2 ≤
        (hA.eigenvalues hn i' - lo) * (M ^ 2 *
          ‖v - (inner 𝕜 (hA.eigenvectorBasis hn i') v : 𝕜) • hA.eigenvectorBasis hn i'‖ ^ 2) := by
      have hbound : ∀ j ∈ Finset.Ioi i',
          (hA.eigenvalues hn i' - hA.eigenvalues hn j) *
            ‖(hA.eigenvectorBasis hn).repr (aeval A (q.map (algebraMap ℝ 𝕜)) v) j‖ ^ 2 ≤
          (hA.eigenvalues hn i' - lo) * (M ^ 2 * ‖(hA.eigenvectorBasis hn).repr v j‖ ^ 2) := by
        intro j hj
        have hj' := hmem j (Finset.mem_Ioi.1 hj)
        have h1 : ‖(hA.eigenvectorBasis hn).repr (aeval A (q.map (algebraMap ℝ 𝕜)) v) j‖ ≤
            M * ‖(hA.eigenvectorBasis hn).repr v j‖ := by
          rw [hrepr, norm_mul, RCLike.norm_ofReal]
          exact mul_le_mul_of_nonneg_right (hqb _ hj') (norm_nonneg _)
        have h2 : ‖(hA.eigenvectorBasis hn).repr (aeval A (q.map (algebraMap ℝ 𝕜)) v) j‖ ^ 2 ≤
            M ^ 2 * ‖(hA.eigenvectorBasis hn).repr v j‖ ^ 2 := by
          calc ‖(hA.eigenvectorBasis hn).repr (aeval A (q.map (algebraMap ℝ 𝕜)) v) j‖ ^ 2
              ≤ (M * ‖(hA.eigenvectorBasis hn).repr v j‖) ^ 2 := by
                gcongr
            _ = M ^ 2 * ‖(hA.eigenvectorBasis hn).repr v j‖ ^ 2 := by ring
        refine mul_le_mul ?_ h2 (sq_nonneg _) (by linarith)
        linarith [hj'.1]
      refine le_trans (Finset.sum_le_sum hbound) ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hwnorm (sq_nonneg M)) (by linarith)
    linarith
  -- the denominator
  have hDge : ‖(inner 𝕜 (hA.eigenvectorBasis hn i') v : 𝕜)‖ ^ 2 ≤
      ‖aeval A (q.map (algebraMap ℝ 𝕜)) v‖ ^ 2 := by
    rw [hA.norm_sq_eq_sum_norm_repr_sq hn, ← hcv, ← hxi]
    exact Finset.single_le_sum (f := fun j =>
      ‖(hA.eigenvectorBasis hn).repr (aeval A (q.map (algebraMap ℝ 𝕜)) v) j‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i')
  have hcpos : (0 : ℝ) < ‖(inner 𝕜 (hA.eigenvectorBasis hn i') v : 𝕜)‖ ^ 2 := by
    have := norm_pos_iff.2 hv
    positivity
  have hDpos : (0 : ℝ) < ‖aeval A (q.map (algebraMap ℝ 𝕜)) v‖ ^ 2 := lt_of_lt_of_le hcpos hDge
  -- assemble
  rw [Submodule.tanAngle_span_singleton hu v]
  have hgoal : hA.eigenvalues hn i' -
      A.rayleighQuotient (aeval A (q.map (algebraMap ℝ 𝕜)) v) ≤
      (hA.eigenvalues hn i' - lo) *
        (M * (‖v - (inner 𝕜 (hA.eigenvectorBasis hn i') v : 𝕜) • hA.eigenvectorBasis hn i'‖ /
          ‖(inner 𝕜 (hA.eigenvectorBasis hn i') v : 𝕜)‖)) ^ 2 := by
    have hC : (0 : ℝ) ≤ (hA.eigenvalues hn i' - lo) * (M ^ 2 *
        ‖v - (inner 𝕜 (hA.eigenvectorBasis hn i') v : 𝕜) • hA.eigenvectorBasis hn i'‖ ^ 2) := by
      have : lo < hA.eigenvalues hn i' := lt_trans hlohi hhi
      positivity
    have hsplit : hA.eigenvalues hn i' -
        A.rayleighQuotient (aeval A (q.map (algebraMap ℝ 𝕜)) v) =
        (hA.eigenvalues hn i' * ‖aeval A (q.map (algebraMap ℝ 𝕜)) v‖ ^ 2 -
          RCLike.re (inner 𝕜 (A (aeval A (q.map (algebraMap ℝ 𝕜)) v))
            (aeval A (q.map (algebraMap ℝ 𝕜)) v))) /
          ‖aeval A (q.map (algebraMap ℝ 𝕜)) v‖ ^ 2 := by
      rw [LinearMap.rayleighQuotient, sub_div, mul_div_assoc, div_self hDpos.ne', mul_one]
    have hrhs : (hA.eigenvalues hn i' - lo) *
        (M * (‖v - (inner 𝕜 (hA.eigenvectorBasis hn i') v : 𝕜) • hA.eigenvectorBasis hn i'‖ /
          ‖(inner 𝕜 (hA.eigenvectorBasis hn i') v : 𝕜)‖)) ^ 2 =
        ((hA.eigenvalues hn i' - lo) * (M ^ 2 *
          ‖v - (inner 𝕜 (hA.eigenvectorBasis hn i') v : 𝕜) • hA.eigenvectorBasis hn i'‖ ^ 2)) /
          ‖(inner 𝕜 (hA.eigenvectorBasis hn i') v : 𝕜)‖ ^ 2 := by
      field_simp
    rw [hsplit, hrhs]
    rcases le_or_gt (hA.eigenvalues hn i' * ‖aeval A (q.map (algebraMap ℝ 𝕜)) v‖ ^ 2 -
      RCLike.re (inner 𝕜 (A (aeval A (q.map (algebraMap ℝ 𝕜)) v))
        (aeval A (q.map (algebraMap ℝ 𝕜)) v))) 0 with hsign | hsign
    · exact le_trans (div_nonpos_of_nonpos_of_nonneg hsign (le_of_lt hDpos))
        (div_nonneg hC (le_of_lt hcpos))
    · refine le_trans (div_le_div_of_nonneg_left hsign.le hcpos hDge) ?_
      exact div_le_div_of_nonneg_right hN hcpos.le
  linarith

/-! ### The bounds in the form the numerical analysis literature states them

Here `iS` is the successor of `i`, and `first` and `last` are the extreme indices, so that `[λ_last,
λ_iS]` is the smallest interval enclosing the eigenvalues after the `i`-th and `λ_first - λ_last` is
the spread of the spectrum.  Passing the indices as data with their defining properties avoids `Fin`
arithmetic and keeps the statements usable when only part of the spectrum is known. -/

/-- **The Chebyshev bound on the angle between an eigenvector and the Krylov subspace.**  With the
eigenvalues `λ` of a symmetric `A` in decreasing order and `u_i` the `i`-th eigenvector,

`tan θ(u_i, 𝒦_m(A, v)) ≤ κ_i tan θ(u_i, v) / T_k(1 + 2 γ_i)`,

where `γ_i = (λ_i - λ_{i+1}) / (λ_{i+1} - λ_n)`, `κ_i = ∏_{j < i} (λ_j - λ_n) / (λ_j - λ_i)` and
`T_k` is the Chebyshev polynomial of the first kind, valid whenever `i + k < m`.

The hypotheses are the ones that make the constants finite: the `i`-th eigenvalue is separated from
the ones before it and from the one after it, and the spectrum below it is not a single point.  This
is `Lanczos.tan_angle_le_of_mem_Icc` with the interval `[λ_n, λ_{i+1}]`, which is the smallest one
containing the eigenvalues after the `i`-th. -/
theorem tan_angle_le (i iS last : Fin n) (hiS : (i : ℕ) + 1 = (iS : ℕ))
    (hlast : ∀ j : Fin n, j ≤ last) {v : E}
    (hv : (inner 𝕜 (hA.eigenvectorBasis hn i) v : 𝕜) ≠ 0)
    (hgap : hA.eigenvalues hn iS < hA.eigenvalues hn i)
    (hspread : hA.eigenvalues hn last < hA.eigenvalues hn iS)
    (hsep : ∀ j : Fin n, j < i → hA.eigenvalues hn i < hA.eigenvalues hn j)
    {m k : ℕ} (hm : (i : ℕ) + k < m) :
    (Krylov.subspace A v m).tanAngle (hA.eigenvectorBasis hn i) ≤
      (∏ j ∈ Finset.Iio i, (hA.eigenvalues hn j - hA.eigenvalues hn last) /
          (hA.eigenvalues hn j - hA.eigenvalues hn i)) *
        (𝕜 ∙ v).tanAngle (hA.eigenvectorBasis hn i) /
        (T ℝ k).eval (1 + 2 * ((hA.eigenvalues hn i - hA.eigenvalues hn iS) /
          (hA.eigenvalues hn iS - hA.eigenvalues hn last))) := by
  have harg : 1 + 2 * ((hA.eigenvalues hn i - hA.eigenvalues hn iS) /
      (hA.eigenvalues hn iS - hA.eigenvalues hn last)) =
      (2 * hA.eigenvalues hn i - hA.eigenvalues hn iS - hA.eigenvalues hn last) /
        (hA.eigenvalues hn iS - hA.eigenvalues hn last) := by
    have hne : hA.eigenvalues hn iS - hA.eigenvalues hn last ≠ 0 := by linarith
    field_simp
    ring
  rw [harg, ← div_mul_eq_mul_div]
  refine tan_angle_le_of_mem_Icc hA hn i hv hspread hgap (fun j hj => ⟨?_, ?_⟩) hsep hm
  · exact hA.eigenvalues_antitone hn (hlast j)
  · refine hA.eigenvalues_antitone hn ?_
    have h1 := Fin.lt_def.1 hj
    rw [Fin.le_def, ← hiS]
    omega

/-- **The Kaniel–Paige–[saad2011numerical] bound**, upper half, in [saad2011numerical] form: with
`λ` the eigenvalues of a symmetric `A` in decreasing order and `θ` the eigenvalues of its
compression to `𝒦_m(A, v)` — the Ritz values — again in decreasing order,

`λ_i - θ_i ≤ (λ_1 - λ_n) (κ_i tan θ(u_i, v) / T_k(1 + 2 γ_i))²`

with `γ_i = (λ_i - λ_{i+1}) / (λ_{i+1} - λ_n)` and `κ_i = ∏_{j < i} (θ_j - λ_n) / (θ_j - λ_i)`,
valid whenever `i + k < m`.  Note that the deflation constant `κ_i` here is built from the *Ritz*
values, unlike the one in `Lanczos.tan_angle_le`.

The matching lower bound `0 ≤ λ_i - θ_i` is Cauchy interlacing, a statement about the compression
alone that has nothing to do with the Krylov structure.

This is `Lanczos.eigenvalues_sub_eigenvalues_compression_le_of_mem_Icc` with the interval `[λ_n,
λ_{i+1}]`, weakened from the sharper spread `λ_i - λ_n` to `λ_1 - λ_n`. -/
theorem eigenvalues_sub_eigenvalues_compression_le {v : E} {m : ℕ}
    (hm : Module.finrank 𝕜 (Krylov.subspace A v m) = m) (i : Fin m) (i' iS first last : Fin n)
    (hiS : (i' : ℕ) + 1 = (iS : ℕ)) (hfirst : ∀ j : Fin n, first ≤ j)
    (hlast : ∀ j : Fin n, j ≤ last)
    (hv : (inner 𝕜 (hA.eigenvectorBasis hn i') v : 𝕜) ≠ 0)
    (hgap : hA.eigenvalues hn iS < hA.eigenvalues hn i')
    (hspread : hA.eigenvalues hn last < hA.eigenvalues hn iS)
    (hθ : ∀ j : Fin m, j < i → hA.eigenvalues hn i' <
      (compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j)
    {k : ℕ} (hk : (i : ℕ) + k < m) :
    hA.eigenvalues hn i' -
        (compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm i ≤
      (hA.eigenvalues hn first - hA.eigenvalues hn last) *
        ((∏ j ∈ Finset.Iio i,
            ((compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j -
                hA.eigenvalues hn last) /
              ((compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j -
                hA.eigenvalues hn i')) *
            (𝕜 ∙ v).tanAngle (hA.eigenvectorBasis hn i') /
          (T ℝ k).eval (1 + 2 * ((hA.eigenvalues hn i' - hA.eigenvalues hn iS) /
            (hA.eigenvalues hn iS - hA.eigenvalues hn last)))) ^ 2 := by
  have harg : 1 + 2 * ((hA.eigenvalues hn i' - hA.eigenvalues hn iS) /
      (hA.eigenvalues hn iS - hA.eigenvalues hn last)) =
      (2 * hA.eigenvalues hn i' - hA.eigenvalues hn iS - hA.eigenvalues hn last) /
        (hA.eigenvalues hn iS - hA.eigenvalues hn last) := by
    have hne : hA.eigenvalues hn iS - hA.eigenvalues hn last ≠ 0 := by linarith
    field_simp
    ring
  rw [harg, ← div_mul_eq_mul_div]
  refine le_trans (eigenvalues_sub_eigenvalues_compression_le_of_mem_Icc hA hn hm i i' hv hspread
    hgap (fun j hj => ⟨?_, ?_⟩) hθ hk) ?_
  · exact hA.eigenvalues_antitone hn (hlast j)
  · refine hA.eigenvalues_antitone hn ?_
    have h1 := Fin.lt_def.1 hj
    rw [Fin.le_def, ← hiS]
    omega
  · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have h1 := hA.eigenvalues_antitone hn (hfirst i')
    linarith

/-- **The Kaniel–Paige–[saad2011numerical] theorem.**  With `λ` the eigenvalues of a symmetric `A`
in decreasing order and `θ` the eigenvalues of its compression to the Krylov subspace `𝒦_m(A, v)` —
the Ritz values — again in decreasing order,

`0 ≤ λ_i - θ_i ≤ (λ_1 - λ_n) (κ_i tan θ(u_i, v) / T_k(1 + 2 γ_i))²`

with `γ_i = (λ_i - λ_{i+1}) / (λ_{i+1} - λ_n)` and `κ_i = ∏_{j < i} (θ_j - λ_n) / (θ_j - λ_i)`,
valid whenever `i + k < m`.  So the Ritz values of the symmetric Lanczos process approach the
extreme eigenvalues of `A` from below, at a rate governed by the Chebyshev polynomial of the part of
the spectrum below the sought eigenvalue.

The lower bound is Cauchy interlacing, `LinearMap.IsSymmetric.eigenvalues_compression_le`, which has
nothing to do with the Krylov structure; the upper bound is
`Lanczos.eigenvalues_sub_eigenvalues_compression_le`.  The hypothesis `hm` is that `𝒦_m(A, v)`
really has dimension `m`, that is, that the Lanczos process has not yet broken down. -/
theorem kaniel_paige_saad {v : E} {m : ℕ}
    (hm : Module.finrank 𝕜 (Krylov.subspace A v m) = m) (i : Fin m) (i' iS first last : Fin n)
    (hii : (i : ℕ) = (i' : ℕ)) (hiS : (i' : ℕ) + 1 = (iS : ℕ)) (hfirst : ∀ j : Fin n, first ≤ j)
    (hlast : ∀ j : Fin n, j ≤ last)
    (hv : (inner 𝕜 (hA.eigenvectorBasis hn i') v : 𝕜) ≠ 0)
    (hgap : hA.eigenvalues hn iS < hA.eigenvalues hn i')
    (hspread : hA.eigenvalues hn last < hA.eigenvalues hn iS)
    (hθ : ∀ j : Fin m, j < i → hA.eigenvalues hn i' <
      (compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j)
    {k : ℕ} (hk : (i : ℕ) + k < m) :
    hA.eigenvalues hn i' -
        (compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm i ∈
      Set.Icc 0 ((hA.eigenvalues hn first - hA.eigenvalues hn last) *
        ((∏ j ∈ Finset.Iio i,
            ((compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j -
                hA.eigenvalues hn last) /
              ((compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j -
                hA.eigenvalues hn i')) *
            (𝕜 ∙ v).tanAngle (hA.eigenvectorBasis hn i') /
          (T ℝ k).eval (1 + 2 * ((hA.eigenvalues hn i' - hA.eigenvalues hn iS) /
            (hA.eigenvalues hn iS - hA.eigenvalues hn last)))) ^ 2) := by
  have hmn : m ≤ n := by
    rw [← hm, ← hn]
    exact Submodule.finrank_le _
  refine ⟨?_, eigenvalues_sub_eigenvalues_compression_le hA hn hm i i' iS first last hiS hfirst
    hlast hv hgap hspread hθ hk⟩
  have h := hA.eigenvalues_compression_le (Krylov.subspace A v m) hn hm hmn i
  rw [show Fin.castLE hmn i = i' from Fin.ext (by simpa using hii)] at h
  linarith

end Eigenbasis

end Lanczos

/-! ### The Arnoldi residual operator on a Krylov subspace -/

namespace Arnoldi

variable (A : E →ₗ[𝕜] E) (b : E)

/-- The part of `A y` outside `𝒦_m`, as a linear map: `(1 - P_m) A`. -/
private noncomputable def outside (m : ℕ) : E →ₗ[𝕜] E :=
  (LinearMap.id - ((subspace A b m).starProjection : E →ₗ[𝕜] E)) ∘ₗ A

/-- `outside` unfolded: the residual of `A x` against `𝒦_m`. -/
private theorem outside_apply (m : ℕ) (x : E) :
    outside A b m x = A x - (subspace A b m).starProjection (A x) := rfl

/-- Below the last Arnoldi vector of `𝒦_m` the image stays inside `𝒦_m`. -/
private theorem outside_vec_eq_zero {m j : ℕ} (h : j + 2 ≤ m) : outside A b m (vec A b j) = 0 := by
  have hmem : A (vec A b j) ∈ subspace A b m :=
    subspace_mono A b h (map_subspace_le A b (j + 1) ⟨_, vec_mem_subspace A b j, rfl⟩)
  rw [outside_apply, Submodule.starProjection_eq_self_iff.2 hmem, sub_self]

/-- At the last Arnoldi vector of `𝒦_m` the image leaves `𝒦_m` along `v_m`, with the subdiagonal
Hessenberg coefficient as its size: `(1 - P_m) A v_{m-1} = h_{m+1,m} v_m` ([saad2011numerical],
Proposition 6.6). -/
theorem sub_starProjection_apply_vec_last {m : ℕ} (hm : 0 < m) :
    A (vec A b (m - 1)) - (subspace A b m).starProjection (A (vec A b (m - 1)))
      = coeff A b m (m - 1) • vec A b m := by
  have h := starProjection_apply_vec A b (m - 1)
  rw [show m - 1 + 1 = m from by omega] at h
  exact h

/-- The Arnoldi vectors have norm at most one: `1` before breakdown and `0` after. -/
private theorem norm_vec_le_one (j : ℕ) : ‖vec A b j‖ ≤ 1 := by
  rcases eq_or_ne (vec A b j) 0 with h | h
  · rw [h, norm_zero]; norm_num
  · rw [norm_vec_eq_one_of_ne_zero A b h]

/-- **[saad2011numerical], Proposition 6.6**: on `𝒦_m` the operator `(1 - P_m) A` is bounded by the
subdiagonal Hessenberg coefficient `h_{m+1,m}`.

Only the last Arnoldi vector contributes, `(1 - P_m) A v_j` vanishing for `j + 2 ≤ m`, and there `(1
- P_m) A v_{m-1} = h_{m+1,m} v_m`. -/
theorem norm_sub_starProjection_apply_le {m : ℕ} (hm : 0 < m) {y : E} (hy : y ∈ subspace A b m) :
    ‖A y - (subspace A b m).starProjection (A y)‖ ≤ ‖coeff A b m (m - 1)‖ * ‖y‖ := by
  have hval : outside A b m y
      = (inner 𝕜 (vec A b (m - 1)) y : 𝕜) • coeff A b m (m - 1) • vec A b m := by
    conv_lhs => rw [eq_sum_inner_smul_vec A b hy]
    rw [map_sum, Finset.sum_eq_single (m - 1)]
    · rw [map_smul, outside_apply, sub_starProjection_apply_vec_last A b hm]
    · intro j hj hjne
      have hjlt : j < m := Finset.mem_range.1 hj
      rw [map_smul, outside_vec_eq_zero A b (by omega), smul_zero]
    · intro hc
      exact absurd (Finset.mem_range.2 (by omega)) hc
  rw [← outside_apply, hval, norm_smul, norm_smul]
  have h1 : ‖(inner 𝕜 (vec A b (m - 1)) y : 𝕜)‖ ≤ ‖y‖ :=
    (norm_inner_le_norm _ _).trans
      (by simpa using mul_le_mul_of_nonneg_right (norm_vec_le_one A b (m - 1)) (norm_nonneg y))
  have h2 : ‖coeff A b m (m - 1)‖ * ‖vec A b m‖ ≤ ‖coeff A b m (m - 1)‖ := by
    simpa using mul_le_mul_of_nonneg_left (norm_vec_le_one A b m) (norm_nonneg _)
  calc ‖(inner 𝕜 (vec A b (m - 1)) y : 𝕜)‖ * (‖coeff A b m (m - 1)‖ * ‖vec A b m‖)
      ≤ ‖y‖ * ‖coeff A b m (m - 1)‖ := mul_le_mul h1 h2 (by positivity) (norm_nonneg y)
    _ = ‖coeff A b m (m - 1)‖ * ‖y‖ := mul_comm _ _

/-- **The dual half of [saad2011numerical], Proposition 6.6**: for a symmetric operator the norm of
`P_m A (1 - P_m)` is bounded by the same subdiagonal coefficient, because `P_m A (1 - P_m)` is the
adjoint of `(1 - P_m) A P_m`.

This is the hypothesis `γ` of `LinearMap.IsSymmetric.sin_angle_ritzVector_le`, so it is the form in
which Proposition 6.6 enters the Ritz bounds of `Numlib/Eigen/RayleighRitz`. -/
theorem norm_starProjection_apply_le_of_mem_orthogonal (hA : A.IsSymmetric) {m : ℕ} (hm : 0 < m)
    {x : E} (hx : x ∈ (subspace A b m)ᗮ) :
    ‖(subspace A b m).starProjection (A x)‖ ≤ ‖coeff A b m (m - 1)‖ * ‖x‖ := by
  set K := subspace A b m with hK
  set p := K.starProjection (A x) with hp
  rcases eq_or_lt_of_le (norm_nonneg p) with h0 | hpos
  · rw [← h0]
    positivity
  have hpK : p ∈ K := Submodule.starProjection_apply_mem _ _
  -- `⟪p, p⟫ = ⟪x, A p - P_K (A p)⟫`
  have h1 : (inner 𝕜 (A x) p : 𝕜) = inner 𝕜 p p := by
    have h := Submodule.inner_left_of_mem_orthogonal (𝕜 := 𝕜) hpK
      (Submodule.sub_starProjection_mem_orthogonal (K := K) (A x))
    rw [inner_sub_left, sub_eq_zero] at h
    exact h
  have h2 : (inner 𝕜 x (A p - K.starProjection (A p)) : 𝕜) = inner 𝕜 p p := by
    rw [inner_sub_right, Submodule.inner_left_of_mem_orthogonal
      (Submodule.starProjection_apply_mem K (A p)) hx, sub_zero, ← hA x p, h1]
  have h3 : ‖p‖ ^ 2 ≤ ‖x‖ * (‖coeff A b m (m - 1)‖ * ‖p‖) := by
    have hcs : ‖(inner 𝕜 x (A p - K.starProjection (A p)) : 𝕜)‖
        ≤ ‖x‖ * ‖A p - K.starProjection (A p)‖ := norm_inner_le_norm _ _
    rw [h2] at hcs
    have hsq : ‖(inner 𝕜 p p : 𝕜)‖ = ‖p‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg p)]
    rw [hsq] at hcs
    exact hcs.trans (mul_le_mul_of_nonneg_left
      (norm_sub_starProjection_apply_le A b hm hpK) (norm_nonneg x))
  have h4 : ‖p‖ * ‖p‖ ≤ ‖coeff A b m (m - 1)‖ * ‖x‖ * ‖p‖ := by nlinarith [h3]
  exact le_of_mul_le_mul_right h4 hpos

/-- **[saad2011numerical], Proposition 6.6**, in the form the Ritz bounds of
`Numlib/Eigen/RayleighRitz` consume: for `0 < m ≤ grade A b` the norm of `(1 - P_m) A` on the unit
sphere of `𝒦_m` is exactly the subdiagonal Hessenberg coefficient `h_{m+1,m} = Arnoldi.coeff A b m
(m - 1)`, the `β_m` of the Lanczos process.

The bound is `Arnoldi.norm_sub_starProjection_apply_le` and it is attained at the last Arnoldi
vector `v_{m-1}`, where `(1 - P_m) A v_{m-1} = h_{m+1,m} v_m` and `v_m` is a unit vector unless the
process has terminated, in which case `h_{m+1,m}` vanishes too. -/
theorem norm_starProjection_comp_orthogonal_eq_coeff [FiniteDimensional 𝕜 (fullSubspace A b)]
    {m : ℕ} (hm : 0 < m) (hgr : m ≤ grade A b) :
    IsGreatest {r : ℝ | ∃ y ∈ subspace A b m, ‖y‖ = 1 ∧
        ‖A y - (subspace A b m).starProjection (A y)‖ = r} ‖coeff A b m (m - 1)‖ := by
  constructor
  · refine ⟨vec A b (m - 1), vec_mem_subspace_of_lt A b (by omega),
      norm_vec_eq_one_of_lt_grade A b (by omega), ?_⟩
    rw [sub_starProjection_apply_vec_last A b hm, norm_smul]
    rcases lt_or_eq_of_le hgr with hlt | heq
    · rw [norm_vec_eq_one_of_lt_grade A b hlt, mul_one]
    · have h0 : vec A b m = 0 := (vec_eq_zero_iff A b m).2 heq.ge
      have hw : w A b (m - 1) = 0 := by
        have hv := vec_succ_eq A b (m - 1)
        rw [show m - 1 + 1 = m from by omega, h0] at hv
        rcases smul_eq_zero.1 hv.symm with hc | hc
        · have : ‖w A b (m - 1)‖ = 0 := by
            simpa using congrArg RCLike.re (inv_eq_zero.1 hc)
          exact norm_eq_zero.1 this
        · exact hc
      have hcoeff : coeff A b m (m - 1) = 0 := by
        have hcs := coeff_succ_self A b (m - 1)
        rw [show m - 1 + 1 = m from by omega] at hcs
        rw [hcs, hw, norm_zero, RCLike.ofReal_zero]
      rw [hcoeff, norm_zero, zero_mul]
  · rintro r ⟨y, hy, hy1, rfl⟩
    simpa [hy1] using norm_sub_starProjection_apply_le A b hm hy

end Arnoldi

namespace Lanczos

/-- **The Ritz-vector bound of the Lanczos process** ([saad2011numerical], §6.6.3): on a Krylov
subspace the constant `γ` of the Ritz-vector bound `LinearMap.IsSymmetric.sin_angle_ritzVector_le`
is the subdiagonal Hessenberg coefficient `β_m = h_{m+1,m}`, so a Ritz pair at a well-separated Ritz
value `θ` has

`sin ∠(u, ũ) ≤ √(1 + β_m² / δ²) sin ∠(u, 𝒦_m)`,

and `Krylov.Lanczos.tan_angle_le` bounds the right-hand side by a Chebyshev quotient. -/
theorem sin_angle_ritzVector_le {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (v : E) {m : ℕ} (hm : 0 < m)
    {δ θ lam : ℝ} (hδ0 : 0 < δ)
    (hθ : Module.End.HasEigenvalue (compression A (subspace A v m)) (θ : 𝕜))
    (hδ : ∀ z ∈ (Module.End.eigenspace (compression A (subspace A v m)) (θ : 𝕜))ᗮ,
      δ * ‖z‖ ≤ ‖compression A (subspace A v m) z - (lam : 𝕜) • z‖)
    {u : E} (hu : A u = (lam : 𝕜) • u) (hu0 : u ≠ 0) :
    ∃ w : E, IsRitzPair A (subspace A v m) (θ : 𝕜) w ∧
      (𝕜 ∙ w).sinAngle u ≤
        Real.sqrt (1 + ‖Arnoldi.coeff A v m (m - 1)‖ ^ 2 / δ ^ 2) *
          (subspace A v m).sinAngle u :=
  hA.sin_angle_ritzVector_le hδ0
    (fun _x hx => Arnoldi.norm_starProjection_apply_le_of_mem_orthogonal A v hA hm hx) hθ hδ hu hu0

end Lanczos

/-! ### The distance to a Krylov subspace without symmetry

For a diagonalizable operator the variational argument still gives a one-sided bound, with the
triangle inequality in place of the Pythagoras of the symmetric case.  The price is the factor
`ξ_i = ∑_{k ≠ i} ‖α_k‖ / ‖α_i‖`, which measures how much of the starting vector lies away from the
eigenvector being approximated. -/

namespace Arnoldi

section Diagonalizable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : E →ₗ[𝕜] E} {u : ι → E} {lam α : ι → 𝕜}
  {v : E} {i : ι} {m : ℕ}

/-- **The distance from an eigenvector to a Krylov subspace, for one competitor polynomial.**  If
`A u_k = λ_k u_k` for a family of vectors `u_k` and the starting vector expands as `v = ∑ α_k u_k`,
then every polynomial `p` of degree less than `m` normalized by `p λ_i = 1` gives

`‖u_i - P_m u_i‖ ≤ (∑_{k ≠ i} ‖α_k‖ ‖p λ_k‖ ‖u_k‖) / ‖α_i‖`,

`P_m` being the orthogonal projection onto `𝒦_m(A, v)`.

The competitor vector is `α_i⁻¹ p(A) v`, whose `u_i`-component is exactly `u_i`; what is left over
is the combination of the other `u_k` weighted by `p` at their eigenvalues.  Neither linear
independence of the family, nor invertibility of `A`, nor any symmetry is used: only that `v` is the
stated combination of eigenvectors, so the family may repeat an eigenvalue or omit part of the
spectrum. -/
theorem norm_sub_starProjection_le_of_eval_eq_one (hu : ∀ k, A (u k) = lam k • u k)
    (hv : v = ∑ k, α k • u k) (hα : α i ≠ 0) {p : 𝕜[X]} (hdeg : p.degree < m)
    (hp : p.eval (lam i) = 1) :
    ‖u i - (subspace A v m).starProjection (u i)‖ ≤
      (∑ k ∈ Finset.univ.erase i, ‖α k‖ * ‖p.eval (lam k)‖ * ‖u k‖) / ‖α i‖ := by
  have hmem : (aeval A p) v ∈ subspace A v m :=
    (Krylov.mem_subspace_iff_exists_aeval A v).2 ⟨p, hdeg, rfl⟩
  refine ((isBestApprox_starProjection _ (u i)).2 _ (Submodule.smul_mem _ (α i)⁻¹ hmem)).trans ?_
  have hexp : (α i)⁻¹ • (aeval A p) v
      = ∑ k, ((α i)⁻¹ * α k * p.eval (lam k)) • u k := by
    rw [hv, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Polynomial.aeval_apply_of_apply_eq_smul (hu k), smul_smul, smul_smul]
  have hsplit : ∑ k, ((α i)⁻¹ * α k * p.eval (lam k)) • u k
      = u i + ∑ k ∈ Finset.univ.erase i, ((α i)⁻¹ * α k * p.eval (lam k)) • u k := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hp, mul_one, inv_mul_cancel₀ hα, one_smul]
  have hdiff : u i - (α i)⁻¹ • (aeval A p) v
      = -∑ k ∈ Finset.univ.erase i, ((α i)⁻¹ * α k * p.eval (lam k)) • u k := by
    rw [hexp, hsplit]; abel
  rw [hdiff, norm_neg, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => le_of_eq ?_)
  rw [norm_smul, norm_mul, norm_mul, norm_inv]
  ring

/-- **[saad2011numerical], Lemma 6.2**: for a diagonalizable `A` with unit eigenvectors `u_k` and a
starting vector `v = ∑ α_k u_k` with `α_i ≠ 0`, the distance from `u_i` to the Krylov subspace
`𝒦_m(A, v)` is at most `ξ_i M`, where `ξ_i = ∑_{k ≠ i} ‖α_k‖ / ‖α_i‖` and `M` bounds a competitor
polynomial `p` of degree less than `m` with `p λ_i = 1` at the other eigenvalues.

The bound `M` is supplied rather than computed, in the manner of this library's other polynomial
estimates; `Arnoldi.norm_sub_starProjection_le_iInf` is the form that takes the best `p`, and
`Arnoldi.norm_sub_starProjection_le_of_mem_closedBall` is the explicit estimate that follows from a
disc enclosing the rest of the spectrum. -/
theorem norm_sub_starProjection_le_mul (hu : ∀ k, A (u k) = lam k • u k) (hu1 : ∀ k, ‖u k‖ = 1)
    (hv : v = ∑ k, α k • u k) (hα : α i ≠ 0) {p : 𝕜[X]} (hdeg : p.degree < m)
    (hp : p.eval (lam i) = 1) {M : ℝ} (hM : ∀ k ≠ i, ‖p.eval (lam k)‖ ≤ M) :
    ‖u i - (subspace A v m).starProjection (u i)‖ ≤
      (∑ k ∈ Finset.univ.erase i, ‖α k‖ / ‖α i‖) * M := by
  refine (norm_sub_starProjection_le_of_eval_eq_one hu hv hα hdeg hp).trans ?_
  rw [Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [hu1 k, mul_one]
  calc ‖α k‖ * ‖p.eval (lam k)‖ / ‖α i‖
      = ‖α k‖ / ‖α i‖ * ‖p.eval (lam k)‖ := by ring
    _ ≤ ‖α k‖ / ‖α i‖ * M :=
        mul_le_mul_of_nonneg_left (hM k (Finset.ne_of_mem_erase hk)) (by positivity)

/-- **[saad2011numerical], Lemma 6.2 with the optimal polynomial.**  The distance from `u_i` to
`𝒦_m(A, v)` is at most the minimum, over the polynomials `p` of degree less than `m` normalized by
`p λ_i = 1`, of `(∑_{k ≠ i} ‖α_k‖ ‖p λ_k‖ ‖u_k‖) / ‖α_i‖`.

The source bounds each `‖p λ_k‖` by their maximum `ε_i^{(m)}` and states the result as
`ξ_i ε_i^{(m)}` with `ξ_i = ∑_{k ≠ i} ‖α_k‖ / ‖α_i‖`; keeping the weights inside the sum is sharper
and is what `Arnoldi.norm_sub_starProjection_le_mul` coarsens to the printed form.

Some step must be taken: at `m = 0` the Krylov subspace is trivial, the left-hand side is `‖u_i‖`,
and the index type is empty, so the infimum has the junk value `0`. -/
theorem norm_sub_starProjection_le_iInf (hu : ∀ k, A (u k) = lam k • u k)
    (hv : v = ∑ k, α k • u k) (hα : α i ≠ 0) (hm : 0 < m) :
    ‖u i - (subspace A v m).starProjection (u i)‖ ≤
      ⨅ p : {p : 𝕜[X] // p.degree < m ∧ p.eval (lam i) = 1},
        (∑ k ∈ Finset.univ.erase i, ‖α k‖ * ‖(p : 𝕜[X]).eval (lam k)‖ * ‖u k‖) / ‖α i‖ := by
  have hone : (1 : 𝕜[X]).degree < (m : ℕ) := by
    rw [Polynomial.degree_one]
    exact_mod_cast hm
  have : Nonempty {p : 𝕜[X] // p.degree < m ∧ p.eval (lam i) = 1} := ⟨⟨1, hone, by simp⟩⟩
  exact le_ciInf fun p => norm_sub_starProjection_le_of_eval_eq_one hu hv hα p.2.1 p.2.2

/-- **[saad2011numerical], Proposition 6.10**: if every eigenvalue other than `λ_i` lies in the
closed disc of centre `c` and radius `ρ`, then the distance from `u_i` to `𝒦_m(A, v)` decays
geometrically,

`‖u_i - P_m u_i‖ ≤ ξ_i (ρ / ‖λ_i - c‖)^(m-1)`,

with `ξ_i = ∑_{k ≠ i} ‖α_k‖ / ‖α_i‖`.  The competitor is `p(z) = ((z - c)/(λ_i - c))^(m-1)`, which
`Polynomial.zarantonello` shows to be optimal on a circle.

The bound is informative exactly when `ρ < ‖λ_i - c‖`, that is when the disc separates `λ_i` from
the rest of the spectrum; no hypothesis enforces that, since the inequality holds regardless. -/
theorem norm_sub_starProjection_le_of_mem_closedBall (hu : ∀ k, A (u k) = lam k • u k)
    (hu1 : ∀ k, ‖u k‖ = 1) (hv : v = ∑ k, α k • u k) (hα : α i ≠ 0) (hm : 0 < m) {c : 𝕜} {ρ : ℝ}
    (hc : lam i ≠ c) (hρ : ∀ k ≠ i, ‖lam k - c‖ ≤ ρ) :
    ‖u i - (subspace A v m).starProjection (u i)‖ ≤
      (∑ k ∈ Finset.univ.erase i, ‖α k‖ / ‖α i‖) * (ρ / ‖lam i - c‖) ^ (m - 1) := by
  have hci : lam i - c ≠ 0 := sub_ne_zero.2 hc
  have hcnorm : (0 : ℝ) < ‖lam i - c‖ := norm_pos_iff.2 hci
  have hev : ∀ z : 𝕜, ((C (lam i - c)⁻¹ * (X - C c)) ^ (m - 1) : 𝕜[X]).eval z
      = ((lam i - c)⁻¹ * (z - c)) ^ (m - 1) := by
    intro z; simp
  have hdeg : ((C (lam i - c)⁻¹ * (X - C c)) ^ (m - 1) : 𝕜[X]).degree < (m : ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le (n := m - 1) ?_) ?_
    · have h1 : (C (lam i - c)⁻¹ * (X - C c) : 𝕜[X]).natDegree ≤ 1 := by compute_degree
      calc ((C (lam i - c)⁻¹ * (X - C c)) ^ (m - 1) : 𝕜[X]).natDegree
          ≤ (m - 1) * (C (lam i - c)⁻¹ * (X - C c) : 𝕜[X]).natDegree :=
            Polynomial.natDegree_pow_le
        _ ≤ (m - 1) * 1 := by gcongr
        _ = m - 1 := by ring
    · exact_mod_cast Nat.sub_lt hm one_pos
  refine norm_sub_starProjection_le_mul hu hu1 hv hα hdeg ?_ ?_
  · rw [hev, inv_mul_cancel₀ hci, one_pow]
  · intro k hk
    rw [hev, norm_pow, norm_mul, norm_inv, ← div_eq_inv_mul]
    gcongr
    exact hρ k hk

end Diagonalizable

section Ellipse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : E →ₗ[ℂ] E} {u : ι → E} {lam α : ι → ℂ}
  {v : E} {i : ι} {m : ℕ}

/-- **[saad2011numerical], Theorem 6.8**, the ellipse counterpart of
`Arnoldi.norm_sub_starProjection_le_of_mem_closedBall`: if every eigenvalue other than `λ_i` lies in
the region bounded by the ellipse with centre `c`, focal semi-distance `d` and parameter `ρ`, and
`λ_i` lies outside it, then

`‖u_i - P_m u_i‖ ≤ ξ_i C_{m-1}(a/d) / |C_{m-1}((λ_i - c)/d)|`,

with `ξ_i = ∑_{k ≠ i} ‖α_k‖/‖α_i‖` and `a/d = (ρ + ρ⁻¹)/2` the ratio of the semi-major axis to the
focal semi-distance.  The competitor is the shifted, normalized Chebyshev polynomial
`Polynomial.Chebyshev.shiftedComplex (m - 1) c d λ_i`, whose maximum on the ellipse is computed by
`Polynomial.Chebyshev.sSup_norm_eval_shiftedComplex_ellipse` and carried into the enclosed region by
the maximum modulus principle
`Polynomial.Chebyshev.norm_eval_shiftedComplex_le_of_mem_filledEllipse`.

The source writes `T_k` for the real Chebyshev polynomial in the numerator and for the complex one
in the denominator; both appear here, over `ℝ` and over `ℂ`.  Being outside the region is what makes
the denominator nonzero, by
`Polynomial.Chebyshev.eval_T_sub_div_ne_zero_of_notMem_filledEllipse`. -/
theorem norm_sub_starProjection_le_of_mem_ellipse (hu : ∀ k, A (u k) = lam k • u k)
    (hu1 : ∀ k, ‖u k‖ = 1) (hv : v = ∑ k, α k • u k) (hα : α i ≠ 0) (hm : 0 < m) {c d : ℂ}
    {ρ : ℝ} (hρ : 1 ≤ ρ) (hd : d ≠ 0) (hi : lam i ∉ Set.filledEllipse c d ρ)
    (hlam : ∀ k ≠ i, lam k ∈ Set.filledEllipse c d ρ) :
    ‖u i - (subspace A v m).starProjection (u i)‖
      ≤ (∑ k ∈ Finset.univ.erase i, ‖α k‖ / ‖α i‖) *
        ((T ℝ ((m - 1 : ℕ) : ℤ)).eval ((ρ + ρ⁻¹) / 2)
          / ‖(T ℂ ((m - 1 : ℕ) : ℤ)).eval ((c - lam i) / d)‖) := by
  have hγ : (T ℂ ((m - 1 : ℕ) : ℤ)).eval ((c - lam i) / d) ≠ 0 :=
    Polynomial.Chebyshev.eval_T_sub_div_ne_zero_of_notMem_filledEllipse (m - 1) hρ hd hi
  have hdeg : (Polynomial.Chebyshev.shiftedComplex (m - 1) c d (lam i)).degree < (m : ℕ) := by
    refine lt_of_le_of_lt (Polynomial.Chebyshev.shiftedComplex_degree_le (m - 1) c d (lam i)) ?_
    exact_mod_cast Nat.sub_lt hm one_pos
  refine norm_sub_starProjection_le_mul hu hu1 hv hα hdeg
    (Polynomial.Chebyshev.shiftedComplex_eval_self (m - 1) hd hγ) fun k hk => ?_
  exact Polynomial.Chebyshev.norm_eval_shiftedComplex_le_of_mem_filledEllipse (m - 1) hρ hd hγ
    (hlam k hk)

end Ellipse

end Arnoldi
