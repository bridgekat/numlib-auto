/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Basic` for the affine-hyperplane lemma and a
new `Mathlib.RingTheory.Polynomial.KernelPolynomial` for the rest.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.Compact

/-!
# Kernel polynomials

The least-squares counterpart of the Chebyshev min–max problem of
`Numlib/RingTheory/Polynomial/ChebyshevMinimax`. Both minimize over `{p : deg p ≤ k, p γ = 1}`;
Chebyshev minimizes the sup norm on an interval, the kernel polynomial minimizes the quadratic
form of a symmetric bilinear form `B` on `ℝ[X]`.

Everything is stated for a family `q : ℕ → ℝ[X]` with `deg (q i) = i` which is orthonormal for
`B`, so that `q 0, …, q k` is a basis of the polynomials of degree at most `k`. No measure theory
appears: the weighted form `B p r = ∫ p r w` is one instance, but nothing in the proofs uses the
integral, and the discrete forms arising from a spectral measure are covered by the same
statements. Positive semidefiniteness is not assumed: on the polynomials of degree at most `k` it
is a consequence of orthonormality (`Polynomial.bilinForm_self_nonneg_of_degree_le`).

The mathematical content is Cauchy–Schwarz: minimizing `‖x‖` over the affine hyperplane
`{⟪y, x⟫ = 1}` of an inner product space gives `x = ‖y‖⁻² • y` and the value `1 / ‖y‖`
(`isLeast_of_inner_eq_one`). With `y` the vector of values `q i γ`, that is the kernel polynomial
formula.

## Main results

* `isLeast_of_inner_eq_one`: the minimum-norm point of an affine hyperplane.
* `Polynomial.kernelPolynomial`: `(∑_{i ≤ k} q i γ ^ 2)⁻¹ • ∑_{i ≤ k} q i γ • q i`.
* `Polynomial.bilinForm_kernelPolynomial_le`: it minimizes `B p p` over the admissible `p`.
* `Polynomial.bilinForm_kernelPolynomial_mul_X`: the residual polynomials are orthogonal for the
  form `(p, r) ↦ B (X * p) r`.
* `Polynomial.bilinForm_kernelPolynomial_le_pow`: geometric decay of the minimum value for a form
  supported on `[α, β]` with `0 < α < β`.

The material follows Saad, *Iterative Methods for Sparse Linear Systems*[^saad-iterative], §12.3.3.
Saad's explicit Jacobi-weight formula and the Gamma-function evaluation of the minimum are not
here: they need Jacobi polynomials.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
-/

open Polynomial

/-- The minimum-norm point of the affine hyperplane `{x : ⟪y, x⟫ = 1}` of an inner product space:
the least norm of such an `x` is `1 / ‖y‖`, attained at `x = ‖y‖⁻² • y`. Cauchy–Schwarz gives the
bound and a direct computation gives the witness. -/
theorem isLeast_of_inner_eq_one {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {y : E} (hy : y ≠ 0) :
    IsLeast {r : ℝ | ∃ x : E, inner 𝕜 y x = 1 ∧ ‖x‖ = r} (1 / ‖y‖) := by
  have hy0 : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  have hyK : ((‖y‖ : 𝕜)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (RCLike.ofReal_ne_zero.mpr hy0.ne')
  refine ⟨⟨(((‖y‖ : 𝕜)) ^ 2)⁻¹ • y, ?_, ?_⟩, ?_⟩
  · rw [inner_smul_right, inner_self_eq_norm_sq_to_K, inv_mul_cancel₀ hyK]
  · rw [norm_smul, norm_inv, norm_pow, RCLike.norm_ofReal, abs_of_pos hy0, pow_two, mul_inv,
      mul_assoc, inv_mul_cancel₀ hy0.ne', mul_one, one_div]
  · rintro r ⟨x, hx, rfl⟩
    rw [div_le_iff₀ hy0]
    calc (1 : ℝ) = ‖inner 𝕜 y x‖ := by rw [hx, norm_one]
      _ ≤ ‖y‖ * ‖x‖ := norm_inner_le_norm y x
      _ = ‖x‖ * ‖y‖ := mul_comm _ _

namespace Polynomial

/-! ### A family of polynomials with all degrees spans -/

/-- A family of polynomials with `deg (q i) = i` spans the polynomials of degree at most `k`:
every such `p` is a linear combination of `q 0, …, q k`. This is what makes an orthonormal family
of that shape a basis of the competitors in the minimization problems below. -/
theorem exists_sum_smul_of_degree_le {K : Type*} [Field K] {q : ℕ → K[X]}
    (hdeg : ∀ i, (q i).degree = i) :
    ∀ (k : ℕ) {p : K[X]}, p.degree ≤ k →
      ∃ c : ℕ → K, p = ∑ i ∈ Finset.range (k + 1), c i • q i := by
  have hne : ∀ i : ℕ, q i ≠ 0 := fun i h => by
    have := hdeg i
    rw [h, degree_zero] at this
    exact absurd this (by simp)
  have hcoeff : ∀ i : ℕ, (q i).coeff i ≠ 0 := fun i => by
    have hlc : (q i).leadingCoeff ≠ 0 := mt leadingCoeff_eq_zero.mp (hne i)
    rwa [leadingCoeff, natDegree_eq_of_degree_eq_some (hdeg i)] at hlc
  intro k
  induction k with
  | zero =>
    intro p hp
    refine ⟨fun _ => p.coeff 0 / (q 0).coeff 0, ?_⟩
    rw [Finset.sum_range_one]
    refine Polynomial.ext fun m => ?_
    rw [coeff_smul, smul_eq_mul]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [div_mul_cancel₀ _ (hcoeff 0)]
    · have hm' : (0 : WithBot ℕ) < (m : WithBot ℕ) := by exact_mod_cast hm
      rw [coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hp hm'),
        coeff_eq_zero_of_degree_lt (lt_of_le_of_lt (hdeg 0).le hm'), mul_zero]
  | succ k ih =>
    intro p hp
    have hrdeg : (p - (p.coeff (k + 1) / (q (k + 1)).coeff (k + 1)) • q (k + 1)).degree ≤
        (k : WithBot ℕ) := by
      refine (degree_le_iff_coeff_zero _ _).2 fun m hm => ?_
      have hm0 : k < m := by exact_mod_cast hm
      have hm' : k + 1 ≤ m := hm0
      rw [coeff_sub, coeff_smul, smul_eq_mul]
      rcases eq_or_lt_of_le hm' with rfl | hlt
      · rw [div_mul_cancel₀ _ (hcoeff (k + 1)), sub_self]
      · have hlt' : ((k + 1 : ℕ) : WithBot ℕ) < (m : WithBot ℕ) := by exact_mod_cast hlt
        rw [coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hp hlt'),
          coeff_eq_zero_of_degree_lt (lt_of_le_of_lt (hdeg (k + 1)).le hlt'), mul_zero, sub_self]
    obtain ⟨c, hc⟩ := ih hrdeg
    refine ⟨Function.update c (k + 1) (p.coeff (k + 1) / (q (k + 1)).coeff (k + 1)), ?_⟩
    have hsum : ∑ i ∈ Finset.range (k + 1),
        Function.update c (k + 1) (p.coeff (k + 1) / (q (k + 1)).coeff (k + 1)) i • q i =
          ∑ i ∈ Finset.range (k + 1), c i • q i :=
      Finset.sum_congr rfl fun i hi => by
        rw [Function.update_of_ne (Nat.ne_of_lt (Finset.mem_range.mp hi))]
    rw [Finset.sum_range_succ, hsum, Function.update_self, ← hc]
    abel

/-! ### The kernel polynomial -/

/-- The kernel polynomial `(∑_{i ≤ k} q i γ ^ 2)⁻¹ • ∑_{i ≤ k} q i γ • q i` of a family `q`
orthonormal for a bilinear form, normalized to `1` at `γ`. It is the least-squares analogue of the
shifted Chebyshev polynomial `Polynomial.Chebyshev.shifted`. -/
noncomputable def kernelPolynomial (q : ℕ → ℝ[X]) (γ : ℝ) (k : ℕ) : ℝ[X] :=
  (∑ i ∈ Finset.range (k + 1), (q i).eval γ ^ 2)⁻¹ •
    ∑ i ∈ Finset.range (k + 1), (q i).eval γ • q i

section Bilin

variable {B : LinearMap.BilinForm ℝ ℝ[X]} {q : ℕ → ℝ[X]}

/-- The quadratic form of `B` on the span of an orthonormal family is a sum of products of the
coefficients. -/
private theorem bilinForm_sum_smul (horth : ∀ i j, B (q i) (q j) = if i = j then 1 else 0)
    (k : ℕ) (c d : ℕ → ℝ) :
    B (∑ i ∈ Finset.range (k + 1), c i • q i) (∑ j ∈ Finset.range (k + 1), d j • q j) =
      ∑ i ∈ Finset.range (k + 1), c i * d i := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, horth,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.mp hi, mul_comm]

/-- Evaluating a combination of the family. -/
private theorem eval_sum_smul (γ : ℝ) (k : ℕ) (c : ℕ → ℝ) :
    (∑ i ∈ Finset.range (k + 1), c i • q i).eval γ =
      ∑ i ∈ Finset.range (k + 1), c i * (q i).eval γ := by
  simp [eval_finsetSum]

/-- On the polynomials of degree at most `k`, orthonormality of `q 0, …, q k` already makes `B`
positive semidefinite: the quadratic form is a sum of squares. This is why no positivity
hypothesis on `B` appears anywhere in this file. -/
theorem bilinForm_self_nonneg_of_degree_le
    (horth : ∀ i j, B (q i) (q j) = if i = j then 1 else 0) (hdeg : ∀ i, (q i).degree = i)
    {k : ℕ} {p : ℝ[X]} (hp : p.degree ≤ k) : 0 ≤ B p p := by
  obtain ⟨c, rfl⟩ := exists_sum_smul_of_degree_le hdeg k hp
  rw [bilinForm_sum_smul horth]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (c i)

/-- The kernel polynomial written as a combination of `q 0, …, q k`. -/
private theorem kernelPolynomial_eq (q : ℕ → ℝ[X]) (γ : ℝ) (k : ℕ) :
    kernelPolynomial q γ k =
      ∑ i ∈ Finset.range (k + 1),
        ((∑ j ∈ Finset.range (k + 1), (q j).eval γ ^ 2)⁻¹ * (q i).eval γ) • q i := by
  rw [kernelPolynomial, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _

private theorem sum_inv_mul_mul {S : ℝ} {k : ℕ} {y : ℕ → ℝ}
    (hy : ∑ i ∈ Finset.range (k + 1), y i ^ 2 = S) (hS : S ≠ 0) :
    ∑ i ∈ Finset.range (k + 1), S⁻¹ * y i * (S⁻¹ * y i) = S⁻¹ := by
  rw [Finset.sum_congr rfl fun i _ => (by ring :
      S⁻¹ * y i * (S⁻¹ * y i) = S⁻¹ * S⁻¹ * y i ^ 2), ← Finset.mul_sum, hy, mul_assoc,
    inv_mul_cancel₀ hS, mul_one]

private theorem sum_inv_mul_self {S : ℝ} {k : ℕ} {y : ℕ → ℝ}
    (hy : ∑ i ∈ Finset.range (k + 1), y i ^ 2 = S) (hS : S ≠ 0) :
    ∑ i ∈ Finset.range (k + 1), S⁻¹ * y i * y i = 1 := by
  rw [Finset.sum_congr rfl fun i _ => (by ring : S⁻¹ * y i * y i = S⁻¹ * y i ^ 2),
    ← Finset.mul_sum, hy, inv_mul_cancel₀ hS]

/-- The kernel polynomial has degree at most `k`, one of the two conditions making it an
admissible competitor. -/
theorem kernelPolynomial_degree_le (hdeg : ∀ i, (q i).degree = i) (γ : ℝ) (k : ℕ) :
    (kernelPolynomial q γ k).degree ≤ k := by
  refine (degree_smul_le _ _).trans ((degree_sum_le _ _).trans (Finset.sup_le fun i hi => ?_))
  refine (degree_smul_le _ _).trans ?_
  rw [hdeg i]
  exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)

/-- The kernel polynomial takes the value `1` at `γ`, the other condition making it admissible.
The normalizing sum must be nonzero, which says exactly that some `q i` with `i ≤ k` does not
vanish at `γ`. -/
theorem kernelPolynomial_eval {γ : ℝ} {k : ℕ}
    (hS : ∑ i ∈ Finset.range (k + 1), (q i).eval γ ^ 2 ≠ 0) :
    (kernelPolynomial q γ k).eval γ = 1 := by
  rw [kernelPolynomial_eq, eval_sum_smul]
  exact sum_inv_mul_self rfl hS

/-- The quadratic form at the kernel polynomial is the reciprocal of the normalizing sum, which
is Saad's minimum value. -/
theorem bilinForm_kernelPolynomial_self
    (horth : ∀ i j, B (q i) (q j) = if i = j then 1 else 0) {γ : ℝ} {k : ℕ}
    (hS : ∑ i ∈ Finset.range (k + 1), (q i).eval γ ^ 2 ≠ 0) :
    B (kernelPolynomial q γ k) (kernelPolynomial q γ k) =
      (∑ i ∈ Finset.range (k + 1), (q i).eval γ ^ 2)⁻¹ := by
  rw [kernelPolynomial_eq, bilinForm_sum_smul horth]
  exact sum_inv_mul_mul rfl hS

/-! ### The minimization -/

private theorem norm_sq_toLp {n : ℕ} (f : ℕ → ℝ) :
    ‖(WithLp.toLp 2 (fun i : Fin n => f i) : EuclideanSpace ℝ (Fin n))‖ ^ 2 =
      ∑ i ∈ Finset.range n, f i ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, ← Fin.sum_univ_eq_sum_range (fun i => f i ^ 2) n]

private theorem inner_toLp {n : ℕ} (f g : ℕ → ℝ) :
    inner ℝ (WithLp.toLp 2 (fun i : Fin n => f i) : EuclideanSpace ℝ (Fin n))
        (WithLp.toLp 2 (fun i : Fin n => g i)) = ∑ i ∈ Finset.range n, g i * f i := by
  rw [PiLp.inner_apply, ← Fin.sum_univ_eq_sum_range (fun i => g i * f i) n]
  exact Finset.sum_congr rfl fun i _ => by simp [RCLike.inner_apply]

/-- Saad's optimality claim for the kernel polynomial: among the polynomials of degree at most
`k` taking the value `1` at `γ`, it minimizes the quadratic form of `B`, and the minimum value is
`(∑_{i ≤ k} q i γ ^ 2)⁻¹`. Expand a competitor in the orthonormal family and apply
`isLeast_of_inner_eq_one` to the vector of values `q i γ`. -/
theorem bilinForm_kernelPolynomial_le
    (horth : ∀ i j, B (q i) (q j) = if i = j then 1 else 0) (hdeg : ∀ i, (q i).degree = i)
    {γ : ℝ} {k : ℕ} (hS : ∑ i ∈ Finset.range (k + 1), (q i).eval γ ^ 2 ≠ 0) :
    IsLeast {r : ℝ | ∃ p : ℝ[X], p.degree ≤ k ∧ p.eval γ = 1 ∧ B p p = r}
      (∑ i ∈ Finset.range (k + 1), (q i).eval γ ^ 2)⁻¹ := by
  have hynorm := norm_sq_toLp (n := k + 1) (fun i => (q i).eval γ)
  have hy0 : (WithLp.toLp 2 (fun i : Fin (k + 1) => (q i).eval γ) :
      EuclideanSpace ℝ (Fin (k + 1))) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hynorm
    exact hS (by simpa using hynorm.symm)
  refine ⟨⟨kernelPolynomial q γ k, kernelPolynomial_degree_le hdeg γ k,
    kernelPolynomial_eval hS, bilinForm_kernelPolynomial_self horth hS⟩, ?_⟩
  rintro r ⟨p, hpdeg, hpγ, rfl⟩
  obtain ⟨c, rfl⟩ := exists_sum_smul_of_degree_le hdeg k hpdeg
  have hxnorm := norm_sq_toLp (n := k + 1) c
  have hinner := (inner_toLp (n := k + 1) (fun i => (q i).eval γ) c).trans
    ((eval_sum_smul (q := q) γ k c).symm.trans hpγ)
  have hle := (isLeast_of_inner_eq_one hy0).2 ⟨_, hinner, rfl⟩
  rw [bilinForm_sum_smul horth]
  have hsq : ∑ i ∈ Finset.range (k + 1), c i * c i = ∑ i ∈ Finset.range (k + 1), c i ^ 2 :=
    Finset.sum_congr rfl fun i _ => sq (c i) ▸ rfl
  rw [hsq, ← hxnorm, ← hynorm]
  calc (‖(WithLp.toLp 2 (fun i : Fin (k + 1) => (q i).eval γ) :
        EuclideanSpace ℝ (Fin (k + 1)))‖ ^ 2)⁻¹
      = (1 / ‖(WithLp.toLp 2 (fun i : Fin (k + 1) => (q i).eval γ) :
        EuclideanSpace ℝ (Fin (k + 1)))‖) ^ 2 := by rw [div_pow, one_pow, one_div]
    _ ≤ ‖(WithLp.toLp 2 (fun i : Fin (k + 1) => c i) :
        EuclideanSpace ℝ (Fin (k + 1)))‖ ^ 2 := by gcongr

/-! ### The normal equations -/

/-- If `0 ≤ 2 t a + t ^ 2 c` for every real `t` and `0 ≤ c`, then `a = 0`: the first-order
condition at an interior minimum of a real quadratic. -/
private theorem eq_zero_of_forall_nonneg {a c : ℝ} (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 ≤ 2 * t * a + t ^ 2 * c) : a = 0 := by
  have key : ∀ a' : ℝ, (∀ t : ℝ, 0 ≤ 2 * t * a' + t ^ 2 * c) → a' ≤ 0 := by
    intro a' h'
    by_contra hpos
    rw [not_le] at hpos
    have hc1 : (0 : ℝ) < c + 1 := by linarith
    have hs : 0 < a' / (c + 1) := div_pos hpos hc1
    have h1 := h' (-(a' / (c + 1)))
    have h2 : 2 * a' ≤ a' / (c + 1) * c := by nlinarith
    have h3 : a' / (c + 1) * c < a' := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hc1]
      nlinarith
    linarith
  refine le_antisymm (key a h) (neg_nonpos.mp (key (-a) fun t => ?_))
  have h' := h (-t)
  nlinarith [h']

/-- The residual polynomials are orthogonal for the shifted form: with `R = kernelPolynomial q 0 k`,
`B (X * p) R = 0` for every `p` of degree less than `k`. These are the normal equations of the
least-squares problem, read off the optimality of `R` by varying along the admissible directions
`X * p`, which are exactly the directions preserving both `deg ≤ k` and the value `1` at `0`. -/
theorem bilinForm_kernelPolynomial_mul_X (hsymm : B.IsSymm)
    (horth : ∀ i j, B (q i) (q j) = if i = j then 1 else 0) (hdeg : ∀ i, (q i).degree = i)
    {k : ℕ} (hS : ∑ i ∈ Finset.range (k + 1), (q i).eval 0 ^ 2 ≠ 0)
    {p : ℝ[X]} (hp : p.degree < (k : WithBot ℕ)) :
    B (X * p) (kernelPolynomial q 0 k) = 0 := by
  have hddeg : (X * p).degree ≤ (k : WithBot ℕ) := by
    rcases eq_or_ne p 0 with rfl | h0
    · simp
    rw [degree_eq_natDegree h0] at hp
    have hn : p.natDegree < k := by exact_mod_cast hp
    rw [degree_mul, degree_X, degree_eq_natDegree h0,
      show (1 : WithBot ℕ) + (p.natDegree : WithBot ℕ) = ((1 + p.natDegree : ℕ) : WithBot ℕ) by
        push_cast; ring]
    exact_mod_cast (by omega : 1 + p.natDegree ≤ k)
  have hdeval : (X * p).eval 0 = 0 := by rw [eval_mul, eval_X, zero_mul]
  have hmin := (bilinForm_kernelPolynomial_le horth hdeg hS).2
  refine eq_zero_of_forall_nonneg
    (bilinForm_self_nonneg_of_degree_le horth hdeg hddeg) fun t => ?_
  have hadm : (kernelPolynomial q 0 k + t • (X * p)).degree ≤ (k : WithBot ℕ) :=
    (degree_add_le _ _).trans
      (max_le (kernelPolynomial_degree_le hdeg 0 k) ((degree_smul_le _ _).trans hddeg))
  have hev : (kernelPolynomial q 0 k + t • (X * p)).eval 0 = 1 := by
    rw [eval_add, eval_smul, kernelPolynomial_eval hS, hdeval, smul_zero, add_zero]
  have hexp : B (kernelPolynomial q 0 k + t • (X * p)) (kernelPolynomial q 0 k + t • (X * p)) =
      B (kernelPolynomial q 0 k) (kernelPolynomial q 0 k) +
        (2 * t * B (X * p) (kernelPolynomial q 0 k) + t ^ 2 * B (X * p) (X * p)) := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hsymm.eq (kernelPolynomial q 0 k) (X * p)]
    ring
  have hle := hmin ⟨kernelPolynomial q 0 k + t • (X * p), hadm, hev, rfl⟩
  rw [hexp, bilinForm_kernelPolynomial_self horth hS] at hle
  linarith

/-! ### The geometric bound -/

/-- The image of a compact interval under `|p|` is bounded above. -/
private theorem bddAbove_image_abs_eval (p : ℝ[X]) (a b : ℝ) :
    BddAbove ((fun t => |p.eval t|) '' Set.Icc a b) :=
  (isCompact_Icc.image p.continuous.abs).bddAbove

/-- The geometric bound of Saad §12.3.3 for `0 < α < β`. A form "supported on `[α, β]`" — meaning
`B p p ≤ (sup_{[α,β]} |p|) ^ 2 * B 1 1`, which the weighted form `B p r = ∫_α^β p r w` with
`w ≥ 0` satisfies by monotonicity of the integral — makes the least-squares residual polynomial
decay geometrically, because `(1 - X / θ) ^ k` with `θ = (α + β) / 2` is an admissible competitor
whose sup on `[α, β]` is at most `((β - α) / (β + α)) ^ k`. -/
theorem bilinForm_kernelPolynomial_le_pow
    (horth : ∀ i j, B (q i) (q j) = if i = j then 1 else 0) (hdeg : ∀ i, (q i).degree = i)
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hB : ∀ p : ℝ[X], B p p ≤ sSup ((fun t => |p.eval t|) '' Set.Icc α β) ^ 2 * B 1 1)
    {k : ℕ} (hS : ∑ i ∈ Finset.range (k + 1), (q i).eval 0 ^ 2 ≠ 0) :
    B (kernelPolynomial q 0 k) (kernelPolynomial q 0 k) ≤
      ((β - α) / (β + α)) ^ (2 * k) * B 1 1 := by
  have hθpos : (0 : ℝ) < (α + β) / 2 := by linarith
  have hsum : (0 : ℝ) < β + α := by linarith
  set P : ℝ[X] := (1 - C ((α + β) / 2)⁻¹ * X) ^ k with hP
  have hPdeg : P.degree ≤ (k : WithBot ℕ) := by
    refine degree_le_of_natDegree_le (natDegree_pow_le.trans ?_)
    have h1 : (1 - C ((α + β) / 2)⁻¹ * X : ℝ[X]).natDegree ≤ 1 := by compute_degree
    simpa using Nat.mul_le_mul_left k h1
  have hPeval : ∀ t : ℝ, P.eval t = (1 - ((α + β) / 2)⁻¹ * t) ^ k := by
    intro t; rw [hP]; simp
  have hP0 : P.eval 0 = 1 := by rw [hPeval]; simp
  have hsuple : sSup ((fun t => |P.eval t|) '' Set.Icc α β) ≤ ((β - α) / (β + α)) ^ k := by
    refine csSup_le ((Set.nonempty_Icc.mpr hαβ.le).image _) ?_
    rintro _ ⟨t, ht, rfl⟩
    dsimp only
    rw [hPeval, abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ k
    have hform : 1 - ((α + β) / 2)⁻¹ * t = ((α + β) / 2 - t) / ((α + β) / 2) := by
      rw [sub_div, div_self hθpos.ne', inv_mul_eq_div]
    have hprod : (β - α) / (β + α) * ((α + β) / 2) = (β - α) / 2 := by
      field_simp; ring
    rw [hform, abs_div, abs_of_pos hθpos, div_le_iff₀ hθpos, hprod, abs_le]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hsupnonneg : 0 ≤ sSup ((fun t => |P.eval t|) '' Set.Icc α β) :=
    le_csSup_of_le (bddAbove_image_abs_eval P α β)
      ⟨α, Set.left_mem_Icc.mpr hαβ.le, rfl⟩ (abs_nonneg _)
  have hB11 : 0 ≤ B 1 1 :=
    bilinForm_self_nonneg_of_degree_le horth hdeg
      (degree_one_le.trans (by exact_mod_cast Nat.zero_le k))
  have hmin := (bilinForm_kernelPolynomial_le horth hdeg hS).2 ⟨P, hPdeg, hP0, rfl⟩
  rw [bilinForm_kernelPolynomial_self horth hS]
  calc (∑ i ∈ Finset.range (k + 1), (q i).eval 0 ^ 2)⁻¹ ≤ B P P := hmin
    _ ≤ sSup ((fun t => |P.eval t|) '' Set.Icc α β) ^ 2 * B 1 1 := hB P
    _ ≤ (((β - α) / (β + α)) ^ k) ^ 2 * B 1 1 := by gcongr
    _ = ((β - α) / (β + α)) ^ (2 * k) * B 1 1 := by rw [← pow_mul, mul_comm k 2]

end Bilin

end Polynomial
