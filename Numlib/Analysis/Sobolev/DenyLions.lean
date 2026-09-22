/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Compactness.lean`; the polynomial lemmas belong in
`Mathlib.Algebra.MvPolynomial.PDeriv` and `Mathlib.Analysis.Calculus.FDeriv`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Basic
import Numlib.Analysis.Sobolev.Compactness
import Numlib.Analysis.Sobolev.Friedrichs
import Numlib.Approximation.MvPolynomial

/-!
# The Deny–Lions norm equivalences

Atkinson and Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd
edition, §7.3.5 (`[han2009theoretical]` Theorems 7.3.12, 7.3.13 and 7.3.14): on a bounded
extension domain `Ω ⊆ ℝ^N`, `k ≥ 1` and `1 ≤ p < ∞`, for seminorms `f_j` on `W^{k,p}(Ω)`
bounded by the norm (H1) and vanishing simultaneously only on `0` among the polynomials of
degree `< k` (H2), the quantities

`|v|_{k,p,Ω} + ∑_j f_j(v)` (7.3.3) and `(|v|_{k,p,Ω}^p + ∑_j f_j(v)^p)^{1/p}` (7.3.4)

are norms on `W^{k,p}(Ω)` equivalent to `‖v‖_{k,p,Ω}`, where
`|v|_{k,p,Ω} = (∑_{|α| = k} ‖∂^α v‖_{L^p(Ω)}^p)^{1/p}` is the top-order seminorm. The
consequences are the Poincaré–Friedrichs inequalities and the Bramble–Hilbert lemma.

## Main definitions

* `SobolevMultiIndex.topDeriv`, `SobolevMultiIndex.topSeminorm`: the tuple of the weak
  derivatives of top order `|α| = k` of `u ∈ W^{k,p}(Ω)`, and its `ℓ^p` norm, the seminorm
  `|u|_{k,p,Ω}` of the book, bundled as a `Seminorm`.

## Main results

* `SobolevMultiIndex.norm_rpow_eq_norm_toLowerOrder_rpow_add`: `‖u‖^p = ‖u‖_{k−1,p}^p + |u|_{k,p}^p`
  for `p < ∞`, the splitting of the norm into its lower-order part and the top seminorm.
* `MvPolynomial.hasFDerivAt_eval`: the derivative of the polynomial function `x ↦ eval x q`
  in the direction `e_i` is `eval x (pderiv i q)`.
* `MvPolynomial.exists_forall_pderiv_eq`: **the Poincaré lemma for polynomials**: a family
  `q_i` with `∂_j q_i = ∂_i q_j` is a gradient, `q_i = ∂_i Q`, with `Q` of degree one more.
* `SobolevMultiIndex.exists_mvPolynomial_ae_eq_of_forall_weakDeriv_eq_zero`: **on a connected
  open set, `|u|_{k,p,Ω} = 0` forces `u` to be a polynomial of degree `< k`** almost everywhere
  (the sentence preceding Theorem 7.3.12 of `[han2009theoretical]`), by induction on `k` from
  the first-order case `HasWeakFDerivOn.ae_eq_const_of_isPreconnected`.
* `SobolevMultiIndex.exists_norm_le_topSeminorm_add_sum_of_isCompactEmbedding`: **the abstract
  Deny–Lions theorem**: with the compact embedding `W^{k+1,p}(Ω) ⊂⊂ W^{k,p}(Ω)` as a
  hypothesis, seminorms satisfying (H1) and (H2)′ — `|v|_{k+1,p} = 0` and all `f_j(v) = 0`
  force `v = 0` — give `‖v‖ ≤ c (|v|_{k+1,p} + ∑_j f_j(v))`; the book's compactness
  contradiction.
* `absIntegralSeminorm L s`, the seminorm `v ↦ ∫_s |L v| dσ` of a bounded map `L` into the `L^q`
  space of a finite measure, with its bound `exists_absIntegralSeminorm_le` — the boundary
  seminorms `∫_Γ |γ v| ds` to which the theorem below is applied.
* `SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_forall_eq_zero`,
  `…_of_isPreconnected`, `…_of_iSup`: the theorem on a bounded extension domain of `ℝ^N` under
  (H2)′ (`[han2009theoretical]` Theorem 7.3.13), under (H2) on a connected domain (Theorem
  7.3.12) and under (H2) on a disjoint union of connected open sets (Theorem 7.3.14), for the
  norm (7.3.3); `SobolevEuclidean.exists_norm_le_lp_topSeminorm_sum_of_forall_eq_zero` and
  its companions for the norm (7.3.4), and `SobolevMultiIndex.topSeminorm_add_sum_le_norm` for
  the reverse inequality.
* `SobolevEuclidean.exists_norm_le_topSeminorm_add_abs_of_isPreconnected` and `…_sum_abs_…`: the
  theorem with the seminorms `|ℓ_j(v)|` of bounded linear functionals, and
  `Seminorm.le_ciInf_norm_add_smul`, `Seminorm.ciInf_norm_add_smul_le_mul`: the quotient norm
  `inf_α ‖v + α • w‖` is equivalent to a seminorm `N` with `N w = 0` under the Deny–Lions
  inequality for `N` and one functional `ℓ` with `ℓ w ≠ 0` (Lemma 8.4.1 of `[han2009theoretical]`).
* `SobolevEuclidean.polynomialSubmodule`: **`ℙ_k(Ω)` inside `W^{k+1,p}(Ω)`**, the elements whose
  function is a polynomial of degree at most `k` (bounded `Ω`), finite-dimensional; the top
  seminorm vanishes exactly on it for connected `Ω`
  (`SobolevEuclidean.topSeminorm_eq_zero_iff_mem_polynomialSubmodule`, from
  `MvPolynomial.iteratedFDeriv_evalBasis_eq_zero`), and
  `SobolevEuclidean.exists_ciInf_norm_add_le_mul_topSeminorm` is **Theorem 7.3.17 of
  `[han2009theoretical]`**: the quotient norm of `W^{k+1,p}(Ω)/ℙ_k(Ω)` is bounded by
  `C |v|_{k+1,p,Ω}` (Hahn–Banach extensions of the coordinate functionals of a basis of `ℙ_k(Ω)`,
  through `Seminorm.ciInf_norm_add_le_mul`).
* `SobolevMultiIndex.topSeminorm_one_eq_gradNorm`: at order one the top seminorm is the gradient
  norm, which connects the Poincaré inequality of `Numlib/Analysis/Sobolev/Poincare.lean` with
  the Deny–Lions vocabulary.

## References

`[han2009theoretical]` §7.3.5; the polynomial step is the classical fact that a distribution
all of whose derivatives of order `k` vanish on a connected open set is a polynomial of degree
`< k`.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal NNReal Topology

noncomputable section

/-! ### The top-order seminorm `|u|_{k,p,Ω}` -/

section TopSeminorm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

/-- **The top-order derivatives of `u ∈ W^{k,p}(Ω)`**, the tuple `(∂^α u)_{|α| = k}` of its weak
derivatives of order exactly `k`, as an element of the `ℓ^p` product of copies of `L^p(Ω)`
indexed by `MultiIndexEq ι k`. -/
def topDeriv (u : SobolevMultiIndex F b k p Ω μ) :
    PiLp p fun _ : MultiIndexEq ι k ↦ Lp F p (μ.restrict (Ω : Set E)) :=
  WithLp.toLp p fun α ↦ weakDeriv u α.1

omit [Fact (1 ≤ p)] in
/-- The entry at `α` of the top-order tuple is `∂^α u`. -/
@[simp]
theorem topDeriv_apply (u : SobolevMultiIndex F b k p Ω μ) (α : MultiIndexEq ι k) :
    topDeriv u α = weakDeriv u α.1 :=
  rfl

omit [Fact (1 ≤ p)] in
/-- The top-order tuple is additive. -/
theorem topDeriv_add (u v : SobolevMultiIndex F b k p Ω μ) :
    topDeriv (u + v) = topDeriv u + topDeriv v :=
  rfl

omit [Fact (1 ≤ p)] in
/-- The top-order tuple commutes with scalar multiplication. -/
theorem topDeriv_smul (c : ℝ) (u : SobolevMultiIndex F b k p Ω μ) :
    topDeriv (c • u) = c • topDeriv u :=
  rfl

variable (F b k p Ω μ) in
/-- The top-order derivatives as a linear map `W^{k,p}(Ω) →ₗ ℓ^p(L^p(Ω))`. -/
def topDerivₗ : SobolevMultiIndex F b k p Ω μ →ₗ[ℝ]
    PiLp p fun _ : MultiIndexEq ι k ↦ Lp F p (μ.restrict (Ω : Set E)) where
  toFun := topDeriv
  map_add' := topDeriv_add
  map_smul' := topDeriv_smul

variable (F b k p Ω μ) in
/-- **The top-order seminorm `|u|_{k,p,Ω}` on `W^{k,p}(Ω)`** of `[han2009theoretical]` §7.3.5:
`|u|_{k,p,Ω} = (∑_{|α| = k} ‖∂^α u‖_{L^p(Ω)}^p)^{1/p}` for `p < ∞` (`topSeminorm_eq_sum`), and
`⨆_{|α| = k} ‖∂^α u‖_{L^∞(Ω)}` at `p = ∞`. It is the norm of the top-order tuple
`SobolevMultiIndex.topDeriv u` in the `ℓ^p` product of copies of `L^p(Ω)`, bundled as a
`Seminorm`, and it is bounded by the norm of `W^{k,p}(Ω)` (`topSeminorm_le_norm`); at `k = 1` it
is the gradient norm `SobolevMultiIndex.gradNorm`. -/
def topSeminorm : Seminorm ℝ (SobolevMultiIndex F b k p Ω μ) :=
  (normSeminorm ℝ (PiLp p fun _ : MultiIndexEq ι k ↦ Lp F p (μ.restrict (Ω : Set E)))).comp
    (topDerivₗ F b k p Ω μ)

/-- The top-order seminorm is the norm of the top-order tuple. -/
theorem topSeminorm_apply (u : SobolevMultiIndex F b k p Ω μ) :
    topSeminorm F b k p Ω μ u = ‖topDeriv u‖ :=
  rfl

/-- **The top-order seminorm for `p < ∞`**: `|u|_{k,p,Ω} = (∑_{|α| = k} ‖∂^α u‖_p^p)^{1/p}`. -/
theorem topSeminorm_eq_sum (hp : p ≠ ⊤) (u : SobolevMultiIndex F b k p Ω μ) :
    topSeminorm F b k p Ω μ u
      = (∑ α : MultiIndexEq ι k, ‖weakDeriv u α.1‖ ^ p.toReal) ^ (1 / p.toReal) := by
  rw [topSeminorm_apply, topDeriv, PiLp.norm_eq_sum
    (ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp)]

/-- **The top-order seminorm vanishes exactly when every top-order derivative does.** -/
theorem topSeminorm_eq_zero_iff (u : SobolevMultiIndex F b k p Ω μ) :
    topSeminorm F b k p Ω μ u = 0 ↔ ∀ α : MultiIndexEq ι k, weakDeriv u α.1 = 0 := by
  rw [topSeminorm_apply, norm_eq_zero, topDeriv, WithLp.ext_iff, WithLp.ofLp_toLp,
    WithLp.ofLp_zero, funext_iff]
  rfl

/-- **The top-order seminorm is bounded by the norm**: `|u|_{k,p,Ω} ≤ ‖u‖_{k,p,Ω}`, the sum
over the multi-indices of order exactly `k` being part of the sum over those of order at
most `k`. -/
theorem topSeminorm_le_norm (u : SobolevMultiIndex F b k p Ω μ) :
    topSeminorm F b k p Ω μ u ≤ ‖u‖ := by
  classical
  rw [topSeminorm_apply, topDeriv, ← Submodule.norm_coe]
  rcases eq_or_ne p ⊤ with rfl | hp
  · rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_ciSup]
    refine Real.iSup_le (fun α ↦ ?_) (Real.iSup_nonneg fun _ ↦ norm_nonneg _)
    exact le_ciSup (Finite.bddAbove_range fun β : MultiIndexLE ι k ↦
      ‖(u : SobolevMultiIndexTuple F ι k ⊤ Ω μ) β‖) α.1
  · have hP : 0 < p.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
    rw [PiLp.norm_eq_sum hP, PiLp.norm_eq_sum hP]
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
      ?_ (by positivity)
    calc ∑ α : MultiIndexEq ι k, ‖(u : SobolevMultiIndexTuple F ι k p Ω μ) α.1‖ ^ p.toReal
        = ∑ β ∈ Finset.univ.image (fun α : MultiIndexEq ι k ↦ α.1),
            ‖(u : SobolevMultiIndexTuple F ι k p Ω μ) β‖ ^ p.toReal := by
          rw [Finset.sum_image Subtype.val_injective.injOn]
      _ ≤ ∑ β : MultiIndexLE ι k, ‖(u : SobolevMultiIndexTuple F ι k p Ω μ) β‖ ^ p.toReal :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _

/-- The top-order seminorm is `1`-Lipschitz for the norm. -/
theorem abs_topSeminorm_sub_le (u v : SobolevMultiIndex F b k p Ω μ) :
    |topSeminorm F b k p Ω μ u - topSeminorm F b k p Ω μ v| ≤ ‖u - v‖ :=
  (abs_sub_map_le_sub _ u v).trans (topSeminorm_le_norm _)

/-- The top-order seminorm is continuous. -/
theorem continuous_topSeminorm : Continuous (topSeminorm F b k p Ω μ) :=
  Seminorm.continuous_of_le (q := normSeminorm ℝ (SobolevMultiIndex F b k p Ω μ)) continuous_norm
    (Seminorm.le_def.2 fun u ↦ by simpa using topSeminorm_le_norm u)

omit [LinearOrder ι] in
/-- **A sum over the multi-indices of order at most `k + 1` splits** into the sum over those of
order at most `k` and the sum over those of order exactly `k + 1`. -/
theorem _root_.MultiIndexLE.sum_univ_succ {M : Type*} [AddCommMonoid M]
    (f : MultiIndexLE ι (k + 1) → M) :
    ∑ α, f α = ∑ α : MultiIndexLE ι k, f ⟨α.1, α.2.trans (Nat.le_succ k)⟩
      + ∑ α : MultiIndexEq ι (k + 1), f α.1 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun α : MultiIndexLE ι (k + 1) ↦ ∑ i, α.1 i = k + 1) f, add_comm]
  congr 1
  · have himage : Finset.univ.image
        (fun α : MultiIndexLE ι k ↦ (⟨α.1, α.2.trans (Nat.le_succ k)⟩ : MultiIndexLE ι (k + 1)))
        = Finset.univ.filter fun α : MultiIndexLE ι (k + 1) ↦ ¬ ∑ i, α.1 i = k + 1 := by
      ext α
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
      constructor
      · rintro ⟨β, rfl⟩
        intro h
        change ∑ i, β.1 i = k + 1 at h
        have := β.2
        omega
      · intro h
        exact ⟨⟨α.1, by have := α.2; omega⟩, rfl⟩
    rw [← himage, Finset.sum_image (MultiIndexLE.castLE_injective (Nat.le_succ k)).injOn]
  · exact Finset.sum_subtype (p := fun α : MultiIndexLE ι (k + 1) ↦ ∑ i, α.1 i = k + 1) _
      (fun _ ↦ by simp) f

/-- **The splitting of the norm of `W^{k+1,p}(Ω)`, `p < ∞`**: `‖u‖^p = ‖u‖_{k,p}^p + |u|_{k+1,p}^p`,
the lower-order part being `SobolevMultiIndex.toLowerOrder u` and the top part the seminorm. -/
theorem norm_rpow_eq_norm_toLowerOrder_rpow_add (hp : p ≠ ⊤)
    (u : SobolevMultiIndex F b (k + 1) p Ω μ) :
    ‖u‖ ^ p.toReal = ‖toLowerOrder F b p Ω μ (Nat.le_succ k) u‖ ^ p.toReal
      + topSeminorm F b (k + 1) p Ω μ u ^ p.toReal := by
  have hP : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
  have key : ∀ {n : ℕ} (v : SobolevMultiIndex F b n p Ω μ),
      ‖v‖ ^ p.toReal = ∑ α : MultiIndexLE ι n, ‖weakDeriv v α‖ ^ p.toReal := fun v ↦ by
    rw [norm_eq_sum hp, ← Real.rpow_mul
      (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _), one_div_mul_cancel hP.ne',
      Real.rpow_one]
  rw [key, key, topSeminorm_eq_sum hp, ← Real.rpow_mul
    (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _), one_div_mul_cancel hP.ne',
    Real.rpow_one, MultiIndexLE.sum_univ_succ]
  rfl

end SobolevMultiIndex

end TopSeminorm

/-! ### Polynomial functions: derivatives, and the Poincaré lemma for polynomials -/

section Polynomial

namespace MvPolynomial

variable {ι : Type*} [Fintype ι]

/-- Evaluating `∑ i, c i • proj i` at `v` gives `∑ i, c i * v i`. -/
theorem _root_.ContinuousLinearMap.sum_smul_proj_apply (c : ι → ℝ) (v : ι → ℝ) :
    (∑ i, c i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i) v = ∑ i, c i * v i := by
  simp

/-- The polynomial function `x ↦ eval x q` on `ι → ℝ` is smooth. -/
theorem contDiff_eval (q : MvPolynomial ι ℝ) : ContDiff ℝ ∞ (fun x : ι → ℝ ↦ eval x q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const (c := a)
  | add p q hp hq => simpa [map_add] using hp.add hq
  | mul_X p i hp => simpa [map_mul, eval_X] using hp.mul (contDiff_apply ℝ ℝ i)

/-- **The derivative of a polynomial function**: `D(eval · q)(x) = ∑ i, eval x (∂_i q) • proj i`,
so that the derivative in the direction `e_i` is `eval x (pderiv i q)`. -/
theorem hasFDerivAt_eval (q : MvPolynomial ι ℝ) (x : ι → ℝ) :
    HasFDerivAt (fun y : ι → ℝ ↦ eval y q)
      (∑ i, eval x (pderiv i q) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i) x := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a => simpa [pderiv_C] using hasFDerivAt_const (eval x (C a)) x
  | add p q hp hq =>
    have h := hp.add hq
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    exact h
  | mul_X p i hp =>
    have hX : HasFDerivAt (fun y : ι → ℝ ↦ y i)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i) x := hasFDerivAt_apply i x
    have h := hp.mul hX
    have hsum : ∀ j, eval x (pderiv j (p * X i))
        = eval x (pderiv j p) * x i + if j = i then eval x p else 0 := by
      intro j
      rw [pderiv_mul, map_add, map_mul, map_mul, eval_X]
      split_ifs with hji
      · subst hji
        rw [pderiv_X_self, map_one, mul_one]
      · rw [pderiv_X_of_ne (Ne.symm hji), map_zero, mul_zero]
    convert h using 1
    · funext y
      simp [map_mul, eval_X]
    · ext v
      rw [ContinuousLinearMap.sum_smul_proj_apply, add_apply, smul_apply, smul_apply,
        ContinuousLinearMap.sum_smul_proj_apply, ContinuousLinearMap.proj_apply]
      simp only [hsum, smul_eq_mul, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.mul_sum]
      rw [add_comm]
      congr 1
      exact Finset.sum_congr rfl fun j _ ↦ by ring

omit [Fintype ι] in
/-- The derivative of `eval · q` in the direction `Pi.single i 1` is `eval x (pderiv i q)`. -/
theorem fderiv_eval_single [Finite ι] [DecidableEq ι] (q : MvPolynomial ι ℝ) (x : ι → ℝ)
    (i : ι) :
    fderiv ℝ (fun y : ι → ℝ ↦ eval y q) x (Pi.single i 1) = eval x (pderiv i q) := by
  have := Fintype.ofFinite ι
  rw [(hasFDerivAt_eval q x).fderiv, ContinuousLinearMap.sum_smul_proj_apply]
  simp [Pi.single_apply]

end MvPolynomial

end Polynomial

section Poincare

namespace MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coefficient of `X^n` in the polynomial antiderivative of a compatible family
`q_i`: `(∑_j coeff_{n − e_j}(q_j) n_j) / (∑_j n_j²)`. Every `j` with `n_j ≥ 1` gives the same
quotient `coeff_{n − e_j}(q_j) / n_j` when the family is compatible, and this symmetric average
avoids choosing one. -/
def gradientCoeff (q : ι → MvPolynomial ι ℝ) (n : ι →₀ ℕ) : ℝ :=
  (∑ j, (q j).coeff (n - Finsupp.single j 1) * (n j : ℝ)) / ∑ j, (n j : ℝ) ^ 2

/-- The candidate support of the antiderivative: the monomials `m + e_j` for `m` in the support
of `q_j`. -/
def gradientSupport (q : ι → MvPolynomial ι ℝ) : Finset (ι →₀ ℕ) :=
  Finset.univ.biUnion fun j ↦ (q j).support.image (· + Finsupp.single j 1)

theorem gradientCoeff_ne_zero {q : ι → MvPolynomial ι ℝ} {n : ι →₀ ℕ}
    (h : gradientCoeff q n ≠ 0) : n ∈ gradientSupport q := by
  classical
  rw [gradientCoeff, div_ne_zero_iff] at h
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.1
  rw [mul_ne_zero_iff] at hj
  have hnj : 1 ≤ n j := Nat.one_le_iff_ne_zero.2 (by exact_mod_cast hj.2)
  refine Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_image.2
    ⟨n - Finsupp.single j 1, mem_support_iff.2 hj.1, ?_⟩⟩
  exact tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hnj)

/-- **The polynomial antiderivative of a compatible family** `q_i`, `i : ι`, of polynomials: the
polynomial whose coefficient at `n` is `gradientCoeff q n`. -/
def gradientAntideriv (q : ι → MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.onFinset (gradientSupport q) (gradientCoeff q) fun _ ↦ gradientCoeff_ne_zero)

theorem coeff_gradientAntideriv (q : ι → MvPolynomial ι ℝ) (n : ι →₀ ℕ) :
    (gradientAntideriv q).coeff n = gradientCoeff q n :=
  rfl

theorem support_gradientAntideriv_subset (q : ι → MvPolynomial ι ℝ) :
    (gradientAntideriv q).support ⊆ gradientSupport q :=
  Finsupp.support_onFinset_subset (hf := fun _ ↦ gradientCoeff_ne_zero)

/-- The degree of every monomial of the antiderivative is one more than the degree of a monomial
of one of the `q_j`. -/
theorem degree_le_of_mem_support_gradientAntideriv {q : ι → MvPolynomial ι ℝ} {D : ℕ}
    (hq : ∀ j, ∀ m ∈ (q j).support, m.degree ≤ D) {n : ι →₀ ℕ}
    (hn : n ∈ (gradientAntideriv q).support) : n.degree ≤ D + 1 := by
  classical
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (support_gradientAntideriv_subset q hn)
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hj
  rw [map_add, Finsupp.degree_single]
  have := hq j m hm
  omega

omit [Fintype ι] [DecidableEq ι] in
/-- The compatibility `∂_j q_i = ∂_i q_j` read on coefficients, at a multi-index `n` with
`n_i ≥ 1` and `n_j ≥ 1`: `coeff_{n − e_j}(q_j) · n_i = coeff_{n − e_i}(q_i) · n_j`. -/
theorem coeff_sub_single_mul_eq_of_pderiv_eq {q : ι → MvPolynomial ι ℝ}
    (hq : ∀ i j, pderiv j (q i) = pderiv i (q j)) {n : ι →₀ ℕ} {i j : ι} (hi : 1 ≤ n i)
    (hj : 1 ≤ n j) :
    (q j).coeff (n - Finsupp.single j 1) * (n i : ℝ)
      = (q i).coeff (n - Finsupp.single i 1) * (n j : ℝ) := by
  classical
  rcases eq_or_ne i j with rfl | hij
  · rfl
  have key : (pderiv j (q i)).coeff (n - Finsupp.single i 1 - Finsupp.single j 1)
      = (pderiv i (q j)).coeff (n - Finsupp.single i 1 - Finsupp.single j 1) := by
    rw [hq i j]
  rw [coeff_pderiv, coeff_pderiv] at key
  have e1 : n - Finsupp.single i 1 - Finsupp.single j 1 + Finsupp.single j 1
      = n - Finsupp.single i 1 := by
    refine tsub_add_cancel_of_le (Finsupp.single_le_iff.2 ?_)
    simp [Ne.symm hij, hj]
  have e2 : n - Finsupp.single i 1 - Finsupp.single j 1 + Finsupp.single i 1
      = n - Finsupp.single j 1 := by
    rw [tsub_tsub, add_comm (Finsupp.single i 1), ← tsub_tsub]
    refine tsub_add_cancel_of_le (Finsupp.single_le_iff.2 ?_)
    simp [hij, hi]
  have e3 : (((n - Finsupp.single i 1 - Finsupp.single j 1 : ι →₀ ℕ) j : ℕ) : ℝ) + 1
      = (n j : ℝ) := by
    rw [← Nat.cast_succ]
    congr 1
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, hij, ite_false, ite_true]
    omega
  have e4 : (((n - Finsupp.single i 1 - Finsupp.single j 1 : ι →₀ ℕ) i : ℕ) : ℝ) + 1
      = (n i : ℝ) := by
    rw [← Nat.cast_succ]
    congr 1
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, Ne.symm hij, ite_false,
      ite_true]
    omega
  rw [e1, e2, e3, e4] at key
  exact key.symm

/-- **The Poincaré lemma for polynomials**: a family `q_i`, `i : ι`, of polynomials with
`∂_j q_i = ∂_i q_j` for all `i, j` is the gradient of a polynomial, `q_i = ∂_i Q`; the monomials
of `Q` are the `m + e_j` for `m` a monomial of `q_j`, so `deg Q ≤ max_j deg q_j + 1`. -/
theorem pderiv_gradientAntideriv {q : ι → MvPolynomial ι ℝ}
    (hq : ∀ i j, pderiv j (q i) = pderiv i (q j)) (i : ι) :
    pderiv i (gradientAntideriv q) = q i := by
  classical
  refine MvPolynomial.ext _ _ fun m ↦ ?_
  rw [coeff_pderiv, coeff_gradientAntideriv]
  obtain ⟨n, hn⟩ : ∃ n : ι →₀ ℕ, n = m + Finsupp.single i 1 := ⟨_, rfl⟩
  have hni : n i = m i + 1 := by simp [hn]
  have hmi : n - Finsupp.single i 1 = m := by rw [hn, add_tsub_cancel_right]
  have hpos : (0 : ℝ) < ∑ j, (n j : ℝ) ^ 2 :=
    lt_of_lt_of_le (by rw [hni]; positivity)
      (Finset.single_le_sum (f := fun j ↦ (n j : ℝ) ^ 2) (fun _ _ ↦ by positivity)
        (Finset.mem_univ i))
  have hterm : ∀ j, (q j).coeff (n - Finsupp.single j 1) * (n j : ℝ) * (n i : ℝ)
      = (q i).coeff m * ((n j : ℝ) ^ 2) := by
    intro j
    rcases Nat.eq_zero_or_pos (n j) with hj | hj
    · simp [hj]
    · rw [mul_right_comm, coeff_sub_single_mul_eq_of_pderiv_eq hq (by omega) hj, hmi, sq,
        mul_assoc]
  have hcast : ((m i : ℝ) + 1) = (n i : ℝ) := by rw [hni]; push_cast; ring
  rw [← hn, gradientCoeff, div_mul_eq_mul_div, div_eq_iff hpos.ne', Finset.sum_mul, hcast]
  simp_rw [hterm]
  rw [← Finset.mul_sum]

omit [Fintype ι] [DecidableEq ι] in
/-- A polynomial with no monomial of degree `< 0` is zero. -/
theorem eq_zero_of_forall_degree_lt_zero {q : MvPolynomial ι ℝ}
    (h : ∀ m ∈ q.support, m.degree < 0) : q = 0 := by
  rw [← MvPolynomial.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
  exact fun m hm ↦ absurd (h m hm) (Nat.not_lt_zero _)

/-- The monomials of the polynomial antiderivative have degree `< k + 1` when those of the
family have degree `< k`. -/
theorem degree_lt_of_mem_support_gradientAntideriv
    {q : ι → MvPolynomial ι ℝ} {k : ℕ} (hq : ∀ j, ∀ m ∈ (q j).support, m.degree < k)
    {n : ι →₀ ℕ} (hn : n ∈ (gradientAntideriv q).support) : n.degree < k + 1 := by
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (support_gradientAntideriv_subset q hn)
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hj
  rw [map_add, Finsupp.degree_single]
  have := hq j m hm
  omega

end MvPolynomial

end Poincare

/-! ### Polynomial functions on a finite-dimensional space, in the coordinates of a basis -/

section EvalBasis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι]

namespace MvPolynomial

/-- **The polynomial function on `E` of a polynomial in the coordinates of a basis `b`**:
`x ↦ q(b.repr x)`. On `ℝ^N` with its standard basis this is `x ↦ eval x q`; the polynomials of
degree at most `k` on an open set `Ω` (`ℙ_k(Ω)` of Atkinson–Han) are the restrictions to `Ω`
of the `evalBasis b q` with `q` of total degree at most `k`. -/
def evalBasis (b : Basis ι ℝ E) (q : MvPolynomial ι ℝ) (x : E) : ℝ :=
  eval (b.equivFun x) q

variable (b : Basis ι ℝ E)

@[simp]
theorem evalBasis_add (q r : MvPolynomial ι ℝ) :
    evalBasis b (q + r) = evalBasis b q + evalBasis b r := by
  funext x
  simp [evalBasis]

@[simp]
theorem evalBasis_sub (q r : MvPolynomial ι ℝ) :
    evalBasis b (q - r) = evalBasis b q - evalBasis b r := by
  funext x
  simp [evalBasis]

@[simp]
theorem evalBasis_zero : evalBasis b (0 : MvPolynomial ι ℝ) = 0 := by
  funext x
  simp [evalBasis]

@[simp]
theorem evalBasis_C (c : ℝ) (x : E) : evalBasis b (C c) x = c := by
  simp [evalBasis]

omit [Fintype ι] in
/-- The coordinates of a basis vector are `Pi.single i 1`. -/
theorem _root_.Module.Basis.equivFunL_self [Finite ι] [DecidableEq ι] (i : ι) :
    b.equivFunL (b i) = Pi.single i 1 := by
  funext j
  rw [Basis.equivFunL_apply, Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

/-- A polynomial function is smooth. -/
theorem contDiff_evalBasis (q : MvPolynomial ι ℝ) : ContDiff ℝ ∞ (evalBasis b q) :=
  (contDiff_eval q).comp b.equivFunL.contDiff

/-- The derivative of a polynomial function. -/
theorem hasFDerivAt_evalBasis (q : MvPolynomial ι ℝ) (x : E) :
    HasFDerivAt (evalBasis b q)
      ((∑ i, eval (b.equivFun x) (pderiv i q) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).comp
          (b.equivFunL : E →L[ℝ] (ι → ℝ))) x :=
  (hasFDerivAt_eval q (b.equivFun x)).comp x b.equivFunL.hasFDerivAt

/-- **The derivative of a polynomial function in the direction of a basis vector** is the
polynomial function of the partial derivative:
`D(evalBasis b q)(x)(b i) = evalBasis b (∂_i q) x`. -/
theorem fderiv_evalBasis_apply_basis (q : MvPolynomial ι ℝ) (x : E) (i : ι) :
    fderiv ℝ (evalBasis b q) x (b i) = evalBasis b (pderiv i q) x := by
  classical
  rw [(hasFDerivAt_evalBasis b q x).fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, Basis.equivFunL_self, ContinuousLinearMap.sum_smul_proj_apply]
  simp [evalBasis, Pi.single_apply]

/-- **Two polynomials whose functions agree almost everywhere on a nonempty open set are equal.**
The functions are continuous, so they agree on the open set, whose image under the coordinate
map has nonempty interior. -/
theorem eq_of_evalBasis_ae_eq [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsOpenPosMeasure] {Ω : Opens E} (hΩ : (Ω : Set E).Nonempty) {q r : MvPolynomial ι ℝ}
    (h : evalBasis b q =ᵐ[μ.restrict (Ω : Set E)] evalBasis b r) : q = r := by
  have heq : EqOn (evalBasis b q) (evalBasis b r) Ω :=
    Measure.eqOn_open_of_ae_eq h Ω.isOpen (contDiff_evalBasis b q).continuous.continuousOn
      (contDiff_evalBasis b r).continuous.continuousOn
  have hopen : IsOpen (b.equivFunL '' (Ω : Set E)) := b.equivFunL.isOpenMap _ Ω.isOpen
  refine sub_eq_zero.1 (eq_zero_of_eval_eq_zero_of_mem_interior (D := b.equivFunL '' Ω)
    (by rw [hopen.interior_eq]; exact hΩ.image _) fun y hy ↦ ?_)
  rw [hopen.interior_eq] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have := heq hx
  simp only [evalBasis] at this
  change eval (b.equivFun x) (q - r) = 0
  rw [map_sub, this, sub_self]

end MvPolynomial

end EvalBasis

/-! ### Vanishing top-order derivatives on a connected open set force a polynomial -/

section VanishingTop

open MvPolynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]

namespace SobolevMultiIndex

omit [μ.IsAddHaarMeasure] in
/-- **The first-order weak derivative tensor of `u ∈ W^{k+1,p}(Ω)`** has the partial
derivatives `∂_i u` as its components in the basis `b`:
`SobolevMultiIndex.exists_hasWeakFDerivOn_fn` read on `W^{k+1,p}(Ω) ⊆ W^{1,p}(Ω)`. -/
theorem exists_hasWeakFDerivOn_fn_of_succ {k : ℕ} (u : SobolevMultiIndex ℝ b (k + 1) p Ω μ) :
    ∃ w : E → E →L[ℝ] ℝ, HasWeakFDerivOn (fn u) w Ω μ ∧
      ∀ i, (fun x ↦ w x (b i)) =ᵐ[μ.restrict (Ω : Set E)]
        weakDeriv u (MultiIndexLE.singleLE i) := by
  obtain ⟨w, hw, -, hwi, -⟩ :=
    exists_hasWeakFDerivOn_fn (toLowerOrder ℝ b p Ω μ (Nat.succ_le_succ (Nat.zero_le k)) u)
  exact ⟨w, hw, hwi⟩

/-- **A Sobolev function whose partial derivatives are those of a smooth function is, on a
connected open set, that function plus a constant** almost everywhere. -/
theorem exists_ae_eq_add_const_of_forall_fderiv_apply_ae_eq {k : ℕ}
    (hΩ : IsPreconnected (Ω : Set E)) (u : SobolevMultiIndex ℝ b (k + 1) p Ω μ) {g : E → ℝ}
    (hg : ContDiff ℝ ∞ g)
    (hgi : ∀ i, (fun x ↦ fderiv ℝ g x (b i)) =ᵐ[μ.restrict (Ω : Set E)]
      weakDeriv u (MultiIndexLE.singleLE i)) :
    ∃ c : ℝ, fn u =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ g x + c := by
  obtain ⟨w, hw, hwi⟩ := exists_hasWeakFDerivOn_fn_of_succ u
  have hsub : HasWeakFDerivOn (fn u - g) (w - fderiv ℝ g) Ω μ := by
    have h := hw.sub (hg.of_le (by simp)).hasWeakFDerivOn
    exact h.congr_ae (Filter.EventuallyEq.refl _ _) (Eventually.of_forall fun x ↦ by
      simp [map_sub])
  have hzero : (w - fderiv ℝ g) =ᵐ[μ.restrict (Ω : Set E)] 0 := by
    have hall : ∀ᵐ x ∂μ.restrict (Ω : Set E), ∀ i, w x (b i) = fderiv ℝ g x (b i) :=
      ae_all_iff.2 fun i ↦ (hwi i).trans (hgi i).symm
    filter_upwards [hall] with x hx
    rw [Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
    exact ContinuousLinearMap.coe_injective (b.ext fun i ↦ hx i)
  obtain ⟨c, hc⟩ := hsub.ae_eq_const_of_isPreconnected hzero hΩ
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  rw [Pi.sub_apply] at hx
  linarith

omit [LinearOrder ι] in
/-- The zero multi-index has order zero, as an element of `MultiIndexEq ι 0`. -/
theorem _root_.MultiIndexEq.zero_mem : ∑ i, ((0 : MultiIndexLE ι 0) : ι → ℕ) i = 0 := by simp

/-- The order of `α + e_i` is `|α| + 1`. -/
theorem _root_.MultiIndexLE.sum_addSingle {k : ℕ} (i : ι) (α : MultiIndexLE ι k) :
    ∑ j, ((MultiIndexLE.addSingle i α : MultiIndexLE ι (k + 1)) : ι → ℕ) j = ∑ j, α.1 j + 1 := by
  simp [MultiIndexLE.coe_addSingle, Finset.sum_add_distrib]

/-- `e_i + e_j = e_j + e_i` as multi-indices of order at most `k + 2`. -/
theorem _root_.MultiIndexLE.addSingle_singleLE_comm {k : ℕ} (i j : ι) :
    (MultiIndexLE.addSingle j (MultiIndexLE.singleLE i : MultiIndexLE ι (k + 1)) :
        MultiIndexLE ι (k + 1 + 1))
      = MultiIndexLE.addSingle i (MultiIndexLE.singleLE j) :=
  Subtype.ext (add_comm _ _)

/-- **On a connected open set, a function of `W^{k,p}(Ω)` all of whose weak derivatives of
order `k` vanish is almost everywhere a polynomial of degree `< k`** (the sentence preceding
`[han2009theoretical]` Theorem 7.3.12): there is `q : MvPolynomial ι ℝ`, every monomial of which
has degree `< k`, with `u = q(b.repr ·)` almost everywhere on `Ω`. Induction on `k`: the partial
derivatives `∂_i u ∈ W^{k−1,p}(Ω)` are polynomials `q_i` by the inductive hypothesis, compatible
(`∂_j q_i = ∂_i q_j`, both being the weak derivative `∂_i ∂_j u`), hence the gradient of a
polynomial `Q` (`MvPolynomial.pderiv_gradientAntideriv`); `u − Q` has vanishing weak gradient, so
it is constant on the connected `Ω` (`HasWeakFDerivOn.ae_eq_const_of_isPreconnected`). -/
theorem exists_mvPolynomial_ae_eq_of_forall_weakDeriv_eq_zero (hΩ : IsPreconnected (Ω : Set E)) :
    ∀ (k : ℕ) (u : SobolevMultiIndex ℝ b k p Ω μ),
      (∀ α : MultiIndexEq ι k, weakDeriv u α.1 = 0) →
      ∃ q : MvPolynomial ι ℝ, (∀ m ∈ q.support, m.degree < k) ∧
        fn u =ᵐ[μ.restrict (Ω : Set E)] evalBasis b q := by
  classical
  intro k
  induction k with
  | zero =>
    intro u hu
    refine ⟨0, by simp, ?_⟩
    have h0 := hu ⟨0, MultiIndexEq.zero_mem⟩
    rw [evalBasis_zero, ← weakDeriv_zero u, h0]
    exact Lp.coeFn_zero _ _ _
  | succ k ih =>
    intro u hu
    rcases (Ω : Set E).eq_empty_or_nonempty with hemp | hne
    · refine ⟨0, by simp, ?_⟩
      unfold Filter.EventuallyEq
      rw [hemp, Measure.restrict_empty, ae_zero]
      exact Filter.eventually_bot
    -- the partial derivatives are polynomials
    have hv : ∀ (i : ι) (α : MultiIndexEq ι k),
        weakDeriv (partialDeriv ℝ b p Ω μ i u) α.1 = 0 := fun i α ↦
      hu ⟨MultiIndexLE.addSingle i α.1, by rw [MultiIndexLE.sum_addSingle, α.2]⟩
    choose q hqdeg hqae using fun i ↦ ih (partialDeriv ℝ b p Ω μ i u) (hv i)
    have hqae' : ∀ i, (weakDeriv u (MultiIndexLE.singleLE i) : E → ℝ)
        =ᵐ[μ.restrict (Ω : Set E)] evalBasis b (q i) := fun i ↦ by
      rw [← fn_partialDeriv]
      exact hqae i
    -- compatibility of the family
    have hcomp : ∀ i j, pderiv j (q i) = pderiv i (q j) := by
      rcases k with _ | k
      · intro i j
        have h0 : ∀ i, q i = 0 := fun i ↦ MvPolynomial.eq_zero_of_forall_degree_lt_zero (hqdeg i)
        simp [h0]
      · intro i j
        have key : ∀ i j, evalBasis b (pderiv j (q i)) =ᵐ[μ.restrict (Ω : Set E)]
            (weakDeriv u (MultiIndexLE.addSingle i (MultiIndexLE.singleLE j)) : E → ℝ) := by
          intro i j
          have h1 : HasWeakIteratedLineDerivOn ![b j] (weakDeriv u (MultiIndexLE.singleLE i))
              (weakDeriv u (MultiIndexLE.addSingle i (MultiIndexLE.singleLE j))) Ω μ :=
            (hasWeakIteratedLineDerivOn_addSingle u i (MultiIndexLE.singleLE j)).of_perm
              (multiIndexTuple_single_perm (b : ι → E) j)
          have h2 : HasWeakIteratedLineDerivOn ![b j] (weakDeriv u (MultiIndexLE.singleLE i))
              (evalBasis b (pderiv j (q i))) Ω μ := by
            have h := ((contDiff_evalBasis b (q i)).contDiffOn.hasWeakIteratedFDerivOn
              (Ω := Ω) (μ := μ) (m := 1) (by simp)).lineDeriv ![b j]
            refine h.congr_ae (hqae' i).symm (Eventually.of_forall fun x ↦ ?_)
            simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero]
            exact fderiv_evalBasis_apply_basis b (q i) x j
          exact (ae_restrict_iff' Ω.isOpen.measurableSet).2 (h2.ae_eq h1)
        refine eq_of_evalBasis_ae_eq b hne ((key i j).trans ?_)
        rw [MultiIndexLE.addSingle_singleLE_comm]
        exact (key j i).symm
    -- the antiderivative
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = gradientAntideriv q := ⟨_, rfl⟩
    have hQi : ∀ i, pderiv i Q = q i := fun i ↦ hQ ▸ pderiv_gradientAntideriv hcomp i
    have hQdeg : ∀ n ∈ Q.support, n.degree < k + 1 := fun n hn ↦
      degree_lt_of_mem_support_gradientAntideriv hqdeg (hQ ▸ hn)
    obtain ⟨c, hc⟩ := exists_ae_eq_add_const_of_forall_fderiv_apply_ae_eq hΩ u
      (contDiff_evalBasis b Q) fun i ↦ by
        refine Filter.EventuallyEq.trans (Eventually.of_forall fun x ↦ ?_) (hqae' i).symm
        change fderiv ℝ (evalBasis b Q) x (b i) = evalBasis b (q i) x
        rw [fderiv_evalBasis_apply_basis, hQi]
    refine ⟨Q + C c, fun m hm ↦ ?_, ?_⟩
    · rcases Finset.mem_union.1 (support_add hm) with h | h
      · exact hQdeg m h
      · rw [support_C] at h
        split_ifs at h with hc0
        · exact absurd h (Finset.notMem_empty _)
        · rw [Finset.mem_singleton.1 h, map_zero]
          exact Nat.succ_pos _
    · filter_upwards [hc] with x hx
      rw [hx, evalBasis_add, Pi.add_apply, evalBasis_C]

end SobolevMultiIndex

end VanishingTop

/-! ### The abstract Deny–Lions theorem -/

section Abstract

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E} [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ]

/-- A seminorm bounded by a multiple of the norm is continuous. -/
theorem Seminorm.continuous_of_forall_le_mul_norm {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (f : Seminorm ℝ V) {c : ℝ} (hf : ∀ v, f v ≤ c * ‖v‖) : Continuous f := by
  refine Seminorm.continuous_of_le (q := c.toNNReal • normSeminorm ℝ V) ?_ (Seminorm.le_def.2
    fun v ↦ ?_)
  · have : ⇑(c.toNNReal • normSeminorm ℝ V) = fun v ↦ (c.toNNReal : ℝ) * ‖v‖ := by
      funext v
      simp [NNReal.smul_def]
    rw [this]
    exact continuous_const.mul continuous_norm
  · simp only [smul_apply, NNReal.smul_def, smul_eq_mul, coe_normSeminorm]
    exact (hf v).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal c) (norm_nonneg _))

namespace SobolevMultiIndex

omit [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ] in
/-- `‖u‖ ≤ ‖u‖_{k,p} + |u|_{k+1,p}` for `u ∈ W^{k+1,p}(Ω)`, `p < ∞`: the `ℓ^p` sum is at most the
sum. -/
theorem norm_le_norm_toLowerOrder_add_topSeminorm (hp : p ≠ ⊤)
    (u : SobolevMultiIndex F b (k + 1) p Ω μ) :
    ‖u‖ ≤ ‖toLowerOrder F b p Ω μ (Nat.le_succ k) u‖ + topSeminorm F b (k + 1) p Ω μ u := by
  have hP : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hp Fact.out
  have h := norm_rpow_eq_norm_toLowerOrder_rpow_add hp u
  rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (add_nonneg (norm_nonneg _) (apply_nonneg _ _))
    (zero_lt_one.trans_le hP), h]
  exact Real.add_rpow_le_rpow_add (norm_nonneg _) (apply_nonneg _ _) hP

/-- **The abstract Deny–Lions theorem** (`[han2009theoretical]` Theorem 7.3.13, the proof of
Theorem 7.3.12): let `W^{k+1,p}(Ω) ⊂⊂ W^{k,p}(Ω)` be compact (`1 ≤ p < ∞`), and let
`f_j`, `j : J` finite, be continuous seminorms on `W^{k+1,p}(Ω)` such that `|v|_{k+1,p,Ω} = 0`
and `f_j(v) = 0` for all `j` force `v = 0` ((H2)′). Then
`‖v‖_{k+1,p,Ω} ≤ C (|v|_{k+1,p,Ω} + ∑_j f_j(v))` for some `C > 0` and all `v`. The book's
argument by contradiction: a sequence with `‖v_n‖ = 1` and `|v_n| + ∑_j f_j(v_n) ≤ 1/n` is
bounded, so a subsequence converges in `W^{k,p}(Ω)`; the top seminorms tend to zero, so the
subsequence is Cauchy in `W^{k+1,p}(Ω)` (`norm_le_norm_toLowerOrder_add_topSeminorm`) and
converges to some `v` with `‖v‖ = 1`, `|v| = 0` and `f_j(v) = 0` — impossible by (H2)′. -/
theorem exists_norm_le_topSeminorm_add_sum_of_isCompactEmbedding (hp : p ≠ ⊤)
    (hc : IsCompactEmbedding (toLowerOrderL F b p Ω μ (Nat.le_succ k)).toLinearMap)
    {J : Type*} [Fintype J] (f : J → Seminorm ℝ (SobolevMultiIndex F b (k + 1) p Ω μ))
    (hf : ∀ j, Continuous (f j))
    (h2 : ∀ v, topSeminorm F b (k + 1) p Ω μ v = 0 → (∀ j, f j v = 0) → v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevMultiIndex F b (k + 1) p Ω μ,
      ‖v‖ ≤ C * (topSeminorm F b (k + 1) p Ω μ v + ∑ j, f j v) := by
  obtain ⟨N, hN⟩ : ∃ N : Seminorm ℝ (SobolevMultiIndex F b (k + 1) p Ω μ),
      N = topSeminorm F b (k + 1) p Ω μ + ∑ j, f j := ⟨_, rfl⟩
  have hNapply : ∀ v, N v = topSeminorm F b (k + 1) p Ω μ v + ∑ j, f j v := fun v ↦ by
    rw [hN, add_apply]
    congr 1
    change (FunLike.coeAddMonoidHom _ _ _ (∑ j, f j)) v = _
    rw [map_sum, Finset.sum_apply]
    rfl
  have htopN : ∀ v, topSeminorm F b (k + 1) p Ω μ v ≤ N v := fun v ↦ by
    rw [hNapply]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ ↦ apply_nonneg _ _)
  have hfN : ∀ j v, f j v ≤ N v := fun j v ↦ by
    rw [hNapply]
    exact le_add_of_nonneg_left (apply_nonneg _ _) |>.trans' (Finset.single_le_sum
      (f := fun j ↦ f j v) (fun j _ ↦ apply_nonneg _ _) (Finset.mem_univ j))
  by_contra hcon
  push Not at hcon
  simp_rw [← hNapply] at hcon
  -- the normalized sequence
  have hseq : ∀ n : ℕ, ∃ v : SobolevMultiIndex F b (k + 1) p Ω μ,
      ‖v‖ = 1 ∧ N v ≤ 1 / (n + 1) := by
    intro n
    obtain ⟨v, hv⟩ := hcon (n + 1) (by positivity)
    have hv0 : ‖v‖ ≠ 0 := fun h ↦ by
      rw [norm_eq_zero] at h
      subst h
      simp at hv
    refine ⟨‖v‖⁻¹ • v, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv0], ?_⟩
    have hn0 : (0 : ℝ) < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv0)
    rw [map_smul_eq_mul, norm_inv, norm_norm, inv_mul_le_iff₀ hn0, mul_one_div,
      le_div_iff₀ (by positivity), mul_comm]
    exact hv.le
  choose v hv1 hvN using hseq
  -- a subsequence converging in `W^{k,p}(Ω)`
  obtain ⟨φ, w, hφ, hw⟩ := hc.exists_subseq_tendsto v ⟨1, fun n ↦ (hv1 n).le⟩
  have hNlim : Tendsto (fun n ↦ N (v (φ n))) atTop (𝓝 0) := by
    refine squeeze_zero (fun n ↦ apply_nonneg _ _) (fun n ↦ hvN (φ n)) ?_
    have h1 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) h1
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.succ_le_succ (hφ.id_le n))
  have htop : Tendsto (fun n ↦ topSeminorm F b (k + 1) p Ω μ (v (φ n))) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ apply_nonneg _ _) (fun n ↦ htopN _) hNlim
  have hfj : ∀ j, Tendsto (fun n ↦ f j (v (φ n))) atTop (𝓝 0) := fun j ↦
    squeeze_zero (fun n ↦ apply_nonneg _ _) (fun n ↦ hfN j _) hNlim
  -- the subsequence is Cauchy in `W^{k+1,p}(Ω)`
  have hcauchy : CauchySeq (fun n ↦ v (φ n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff.1 hw.cauchySeq (ε / 3) (by positivity)
    obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.1 htop) (ε / 3) (by positivity)
    refine ⟨max N₁ N₂, fun m hm n hn ↦ ?_⟩
    have h1 := hN₁ m (le_of_max_le_left hm) n (le_of_max_le_left hn)
    have h2 := hN₂ m (le_of_max_le_right hm)
    have h3 := hN₂ n (le_of_max_le_right hn)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg _ _)] at h2 h3
    rw [dist_eq_norm] at h1 ⊢
    calc ‖v (φ m) - v (φ n)‖
        ≤ ‖toLowerOrder F b p Ω μ (Nat.le_succ k) (v (φ m) - v (φ n))‖
          + topSeminorm F b (k + 1) p Ω μ (v (φ m) - v (φ n)) :=
          norm_le_norm_toLowerOrder_add_topSeminorm hp _
      _ ≤ ‖toLowerOrder F b p Ω μ (Nat.le_succ k) (v (φ m) - v (φ n))‖
          + (topSeminorm F b (k + 1) p Ω μ (v (φ m))
            + topSeminorm F b (k + 1) p Ω μ (v (φ n))) :=
          add_le_add le_rfl (map_sub_le_add _ _ _)
      _ < ε / 3 + (ε / 3 + ε / 3) := by
          refine add_lt_add ?_ (add_lt_add h2 h3)
          rw [← map_sub] at h1
          exact h1
      _ = ε := by ring
  obtain ⟨vlim, hvlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- the limit has norm one, vanishing top seminorm and vanishing `f_j`
  have hnorm : ‖vlim‖ = 1 := by
    have h := (continuous_norm.tendsto vlim).comp hvlim
    simp only [Function.comp_def, hv1] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have htoplim : topSeminorm F b (k + 1) p Ω μ vlim = 0 :=
    tendsto_nhds_unique ((continuous_topSeminorm.tendsto vlim).comp hvlim) htop
  have hflim : ∀ j, f j vlim = 0 := fun j ↦
    tendsto_nhds_unique (((hf j).tendsto vlim).comp hvlim) (hfj j)
  have := h2 vlim htoplim hflim
  rw [this, norm_zero] at hnorm
  exact zero_ne_one hnorm

end SobolevMultiIndex

end Abstract

/-! ### The seminorm `v ↦ ∫_s |L v| dσ` of a bounded map into `L^q` of a finite measure -/

section AbsIntegralSeminorm

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {X : Type*} [MeasurableSpace X]
  {σ : Measure X} [IsFiniteMeasure σ] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- **The seminorm `v ↦ ∫_s |L v| dσ`** on `W`, for a bounded linear `L : W → L^q(σ)` into the
`L^q` space of a finite measure (so that `L^q(σ) ⊆ L¹(σ)`). With `L` a trace operator it is the
boundary seminorm `f(v) = ∫_Γ |γ v| ds` that the Deny–Lions norm equivalences are applied to
([han2009theoretical] Examples 7.3.15 and 7.3.16). -/
def absIntegralSeminorm (L : W →L[ℝ] Lp ℝ q σ) (s : Set X) : Seminorm ℝ W where
  toFun v := ∫ x in s, |(L v : X → ℝ) x| ∂σ
  map_zero' := by
    rw [map_zero]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_zero ℝ q σ)] with x hx
    rw [hx, Pi.zero_apply, abs_zero]
  add_le' v w := by
    have hi : ∀ u : W, Integrable (fun x ↦ |(L u : X → ℝ) x|) (σ.restrict s) := fun u ↦
      ((Lp.memLp (L u)).integrable Fact.out).abs.integrableOn
    rw [← integral_add (hi v) (hi w)]
    refine integral_mono_ae (hi (v + w)) ((hi v).add (hi w)) ?_
    rw [map_add]
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_add (L v) (L w))] with x hx
    rw [hx, Pi.add_apply]
    exact abs_add_le _ _
  neg' v := by
    rw [map_neg]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_neg (L v))] with x hx
    rw [hx, Pi.neg_apply, abs_neg]
  smul' c v := by
    rw [map_smul, Real.norm_eq_abs, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul c (L v))] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul, abs_mul]

/-- The seminorm `absIntegralSeminorm L s` is `v ↦ ∫_s |L v| dσ`. -/
theorem absIntegralSeminorm_apply (L : W →L[ℝ] Lp ℝ q σ) (s : Set X) (v : W) :
    absIntegralSeminorm L s v = ∫ x in s, |(L v : X → ℝ) x| ∂σ :=
  rfl

/-- **The hypothesis (H1) for the seminorm `∫_s |L v| dσ`**: it is bounded by a multiple of `‖v‖`,
through the inclusion `L^q(σ) ⊆ L¹(σ)` of the finite measure (`MeasureTheory.Lp.monoExponentL`).
With `Seminorm.continuous_of_forall_le_mul_norm` it is therefore continuous. -/
theorem exists_absIntegralSeminorm_le (L : W →L[ℝ] Lp ℝ q σ) (s : Set X) :
    ∃ c : ℝ, ∀ v, absIntegralSeminorm L s v ≤ c * ‖v‖ := by
  refine ⟨‖(Lp.monoExponentL ℝ σ q 1 Fact.out).comp L‖, fun v ↦ ?_⟩
  rw [absIntegralSeminorm_apply]
  have hi : Integrable (fun x ↦ |(L v : X → ℝ) x|) σ :=
    ((Lp.memLp (L v)).integrable Fact.out).abs
  calc ∫ x in s, |(L v : X → ℝ) x| ∂σ
      ≤ ∫ x, |(L v : X → ℝ) x| ∂σ :=
        setIntegral_le_integral hi (Eventually.of_forall fun x ↦ abs_nonneg _)
    _ = ‖((Lp.monoExponentL ℝ σ q 1 Fact.out).comp L) v‖ := by
        rw [ContinuousLinearMap.comp_apply, L1.norm_eq_integral_norm]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_monoExponentL (G := ℝ) (μ := σ) (p := q) (q := 1) Fact.out
          (L v)] with x hx
        rw [hx, Real.norm_eq_abs]
    _ ≤ _ := ContinuousLinearMap.le_opNorm _ v

end AbsIntegralSeminorm
/-! ### The two norms (7.3.3) and (7.3.4) -/

section TwoNorms

/-- For a nonnegative vector, `(∑ i, z i ^ p)^{1/p} ≤ ∑ i, z i` when `1 ≤ p < ∞`. -/
theorem Real.rpow_sum_rpow_le_sum {ι : Type*} [Fintype ι] {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    (∑ i, z i ^ p.toReal) ^ (1 / p.toReal) ≤ ∑ i, z i := by
  have hP : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
  have h := PiLp.norm_le_sum_norm (p := p) (WithLp.toLp p z)
  rw [PiLp.norm_eq_sum hP] at h
  refine le_of_le_of_eq (le_of_eq_of_le ?_ h) ?_
  · congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by simp [Real.norm_eq_abs, abs_of_nonneg (hz i)]
  · exact Finset.sum_congr rfl fun i _ ↦ by simp [Real.norm_eq_abs, abs_of_nonneg (hz i)]

/-- For a nonnegative vector, `∑ i, z i ≤ card ι * (∑ i, z i ^ p)^{1/p}` when `1 ≤ p < ∞`. -/
theorem Real.sum_le_card_mul_rpow_sum_rpow {ι : Type*} [Fintype ι] {z : ι → ℝ}
    (hz : ∀ i, 0 ≤ z i) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    ∑ i, z i ≤ Fintype.card ι * (∑ i, z i ^ p.toReal) ^ (1 / p.toReal) := by
  have hP : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
  have hle : ∀ i, z i ≤ (∑ i, z i ^ p.toReal) ^ (1 / p.toReal) := fun i ↦ by
    have h := PiLp.norm_apply_le (p := p) (WithLp.toLp p z) i
    rw [PiLp.norm_eq_sum hP] at h
    simp only [Real.norm_eq_abs, abs_of_nonneg (hz _)] at h
    exact h
  calc ∑ i, z i ≤ ∑ _i : ι, (∑ i, z i ^ p.toReal) ^ (1 / p.toReal) :=
        Finset.sum_le_sum fun i _ ↦ hle i
    _ = Fintype.card ι * (∑ i, z i ^ p.toReal) ^ (1 / p.toReal) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end TwoNorms

/-! ### The reverse inequality, and the norm (7.3.4) -/

section Reverse

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

/-- **The easy half of the Deny–Lions equivalences**: for seminorms `f_j` with
`f_j(v) ≤ c ‖v‖` ((H1)), `|v|_{k,p,Ω} + ∑_j f_j(v) ≤ (1 + J c) ‖v‖`. -/
theorem topSeminorm_add_sum_le_norm {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevMultiIndex F b k p Ω μ)) {c : ℝ} (hf : ∀ j v, f j v ≤ c * ‖v‖)
    (v : SobolevMultiIndex F b k p Ω μ) :
    topSeminorm F b k p Ω μ v + ∑ j, f j v ≤ (1 + Fintype.card J * c) * ‖v‖ := by
  calc topSeminorm F b k p Ω μ v + ∑ j, f j v ≤ ‖v‖ + ∑ _j : J, c * ‖v‖ :=
        add_le_add (topSeminorm_le_norm v) (Finset.sum_le_sum fun j _ ↦ hf j v)
    _ = (1 + Fintype.card J * c) * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- The vector `(|v|_{k,p,Ω}, f_j(v))_j` whose `ℓ^p` norm is the quantity (7.3.4). -/
theorem lp_topSeminorm_sum_eq {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevMultiIndex F b k p Ω μ)) (v : SobolevMultiIndex F b k p Ω μ) :
    (topSeminorm F b k p Ω μ v ^ p.toReal + ∑ j, f j v ^ p.toReal) ^ (1 / p.toReal)
      = (∑ o : Option J, (o.elim (topSeminorm F b k p Ω μ v) fun j ↦ f j v) ^ p.toReal)
          ^ (1 / p.toReal) := by
  rw [Fintype.sum_option]
  rfl

/-- **The quantity (7.3.4) is at most the quantity (7.3.3)**:
`(|v|^p + ∑_j f_j(v)^p)^{1/p} ≤ |v| + ∑_j f_j(v)` for `1 ≤ p < ∞`. -/
theorem lp_topSeminorm_sum_le_add (hp : p ≠ ⊤) {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevMultiIndex F b k p Ω μ)) (v : SobolevMultiIndex F b k p Ω μ) :
    (topSeminorm F b k p Ω μ v ^ p.toReal + ∑ j, f j v ^ p.toReal) ^ (1 / p.toReal)
      ≤ topSeminorm F b k p Ω μ v + ∑ j, f j v := by
  rw [lp_topSeminorm_sum_eq]
  refine (Real.rpow_sum_rpow_le_sum (fun o ↦ ?_) hp).trans (le_of_eq ?_)
  · cases o <;> exact apply_nonneg _ _
  · rw [Fintype.sum_option]
    rfl

/-- **The quantity (7.3.3) is at most `(J + 1)` times the quantity (7.3.4)**:
`|v| + ∑_j f_j(v) ≤ (J + 1) (|v|^p + ∑_j f_j(v)^p)^{1/p}` for `1 ≤ p < ∞`. -/
theorem add_le_card_mul_lp_topSeminorm_sum (hp : p ≠ ⊤) {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevMultiIndex F b k p Ω μ)) (v : SobolevMultiIndex F b k p Ω μ) :
    topSeminorm F b k p Ω μ v + ∑ j, f j v
      ≤ (Fintype.card J + 1)
        * (topSeminorm F b k p Ω μ v ^ p.toReal + ∑ j, f j v ^ p.toReal) ^ (1 / p.toReal) := by
  rw [lp_topSeminorm_sum_eq]
  have h := Real.sum_le_card_mul_rpow_sum_rpow
    (z := fun o : Option J ↦ o.elim (topSeminorm F b k p Ω μ v) fun j ↦ f j v)
    (fun o ↦ by cases o <;> exact apply_nonneg _ _) hp
  rw [Fintype.sum_option, Fintype.card_option] at h
  push_cast at h
  exact h

end SobolevMultiIndex

end Reverse

/-! ### The Deny–Lions theorems on an extension domain of `ℝ^N` -/

section Euclidean

open MvPolynomial SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))} {k : ℕ}

/-- The polynomial function of the standard basis of `ℝ^N` is `x ↦ q(x)`. -/
theorem MvPolynomial.evalBasis_basisFun (q : MvPolynomial (Fin N) ℝ)
    (x : EuclideanSpace ℝ (Fin N)) :
    evalBasis (EuclideanSpace.basisFun (Fin N) ℝ).toBasis q x = eval (fun i ↦ x i) q := by
  unfold evalBasis
  congr 1

/-- A polynomial all of whose monomials have degree `< k + 1` has total degree at most `k`. -/
theorem MvPolynomial.mem_restrictTotalDegree_of_forall_degree_lt {ι : Type*}
    {q : MvPolynomial ι ℝ} (h : ∀ m ∈ q.support, m.degree < k + 1) :
    q ∈ restrictTotalDegree ι ℝ k := by
  rw [mem_restrictTotalDegree, totalDegree]
  exact Finset.sup_le fun m hm ↦ Nat.lt_succ_iff.1 (h m hm)

/-- **`|v|_{k+1,p,Ω} = 0` on a connected open set means `v ∈ ℙ_k(Ω)`** (the sentence preceding
`[han2009theoretical]` Theorem 7.3.12, on `ℝ^N`): `v` agrees almost everywhere on `Ω` with a
polynomial of total degree at most `k`. -/
theorem SobolevEuclidean.exists_mem_restrictTotalDegree_ae_eq_of_topSeminorm_eq_zero
    (hΩ : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin N))))
    {v : SobolevEuclidean N (k + 1) p Ω}
    (hv : topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v = 0) :
    ∃ q ∈ restrictTotalDegree (Fin N) ℝ k,
      fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ eval (fun i ↦ x i) q := by
  obtain ⟨q, hq, hvq⟩ := exists_mvPolynomial_ae_eq_of_forall_weakDeriv_eq_zero hΩ (k + 1) v
    ((topSeminorm_eq_zero_iff v).1 hv)
  refine ⟨q, mem_restrictTotalDegree_of_forall_degree_lt hq, hvq.trans ?_⟩
  exact Eventually.of_forall fun x ↦ evalBasis_basisFun q x

/-- **Theorem 7.3.13 of `[han2009theoretical]`, the norm (7.3.3)**: on an extension domain
`Ω ⊆ ℝ^N` of finite measure (the book's bounded Lipschitz domain), `k ≥ 1` and `1 ≤ p < ∞`,
for seminorms `f_j` on `W^{k,p}(Ω)` with (H1) `f_j(v) ≤ c ‖v‖` and (H2)′ "`|v|_{k,p,Ω} = 0` and
all `f_j(v) = 0` force `v = 0`", there is `C > 0` with `‖v‖_{k,p,Ω} ≤ C (|v|_{k,p,Ω} + ∑_j f_j(v))`
for all `v`; with `SobolevMultiIndex.topSeminorm_add_sum_le_norm` this is the equivalence of the
norm (7.3.3) with `‖·‖_{k,p,Ω}`. The order is written `k + 1`. -/
theorem SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_forall_eq_zero
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevEuclidean N (k + 1) p Ω)) {c : ℝ} (hf : ∀ j v, f j v ≤ c * ‖v‖)
    (h2 : ∀ v : SobolevEuclidean N (k + 1) p Ω,
      topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v = 0 →
        (∀ j, f j v = 0) → v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevEuclidean N (k + 1) p Ω,
      ‖v‖ ≤ C * (topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v
        + ∑ j, f j v) :=
  exists_norm_le_topSeminorm_add_sum_of_isCompactEmbedding (by simp)
    (SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_isSobolevExtensionDomain hΩ hμ k) f
    (fun j ↦ (f j).continuous_of_forall_le_mul_norm (hf j)) h2

/-- **Theorem 7.3.12 of `[han2009theoretical]`, the norm (7.3.3)**: on a connected extension
domain `Ω ⊆ ℝ^N` of finite measure (the book's Lipschitz domain), `k ≥ 1` and `1 ≤ p < ∞`, for
seminorms `f_j` on `W^{k,p}(Ω)` with (H1) `f_j(v) ≤ c ‖v‖` and (H2) "`v ∈ ℙ_{k−1}(Ω)` and all
`f_j(v) = 0` force `v = 0`", there is `C > 0` with `‖v‖_{k,p,Ω} ≤ C (|v|_{k,p,Ω} + ∑_j f_j(v))`
for all `v`. (H2) gives (H2)′ because `|v|_{k,p,Ω} = 0` forces `v ∈ ℙ_{k−1}(Ω)` on a connected
`Ω` (`SobolevEuclidean.exists_mem_restrictTotalDegree_ae_eq_of_topSeminorm_eq_zero`). The
order is written `k + 1`, so `ℙ_{k−1}` is `MvPolynomial.restrictTotalDegree (Fin N) ℝ k`. -/
theorem SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_isPreconnected
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    (hΩc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin N)))) {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevEuclidean N (k + 1) p Ω)) {c : ℝ} (hf : ∀ j v, f j v ≤ c * ‖v‖)
    (h2 : ∀ v : SobolevEuclidean N (k + 1) p Ω,
      (∃ q ∈ restrictTotalDegree (Fin N) ℝ k, fn v
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fun x ↦ eval (fun i ↦ x i) q) →
        (∀ j, f j v = 0) → v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevEuclidean N (k + 1) p Ω,
      ‖v‖ ≤ C * (topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v
        + ∑ j, f j v) :=
  SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_forall_eq_zero hΩ hμ f hf fun v hv hfv ↦
    h2 v (SobolevEuclidean.exists_mem_restrictTotalDegree_ae_eq_of_topSeminorm_eq_zero hΩc hv) hfv

/-- **Theorem 7.3.12 of `[han2009theoretical]` with the seminorms `f_j(v) = |ℓ_j(v)|` of bounded
linear functionals `ℓ_j`** (the form in which the theorem enters the Bramble–Hilbert lemma and
Lemma 8.4.1 of the book): on a connected extension domain of finite measure, if `v ∈ ℙ_k(Ω)` and
`ℓ_j(v) = 0` for all `j` force `v = 0`, then `‖v‖_{k+1,p,Ω} ≤ C (|v|_{k+1,p,Ω} + ∑_j |ℓ_j(v)|)`
for some `C > 0`. -/
theorem SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_abs_of_isPreconnected
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    (hΩc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin N)))) {J : Type*} [Fintype J]
    (ℓ : J → SobolevEuclidean N (k + 1) p Ω →L[ℝ] ℝ)
    (h2 : ∀ v : SobolevEuclidean N (k + 1) p Ω,
      (∃ q ∈ restrictTotalDegree (Fin N) ℝ k, fn v
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fun x ↦ eval (fun i ↦ x i) q) →
        (∀ j, ℓ j v = 0) → v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevEuclidean N (k + 1) p Ω,
      ‖v‖ ≤ C * (topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v
        + ∑ j, |ℓ j v|) := by
  have hf : ∀ j v, ((normSeminorm ℝ ℝ).comp (ℓ j).toLinearMap) v ≤ (∑ i, ‖ℓ i‖) * ‖v‖ :=
    fun j v ↦ ((ℓ j).le_opNorm v).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun i _ ↦ norm_nonneg (ℓ i)) (Finset.mem_univ j)) (norm_nonneg v))
  obtain ⟨C, hC, hle⟩ := SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_isPreconnected
    hΩ hμ hΩc (fun j ↦ (normSeminorm ℝ ℝ).comp (ℓ j).toLinearMap) hf fun v hv hℓ ↦
      h2 v hv fun j ↦ by
        simpa only [Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
          norm_eq_zero] using hℓ j
  refine ⟨C, hC, fun v ↦ ?_⟩
  simpa only [Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
    Real.norm_eq_abs] using hle v

/-- **Theorem 7.3.12 of `[han2009theoretical]` with one bounded linear functional `ℓ`**: on a
connected extension domain of finite measure, if `v ∈ ℙ_k(Ω)` and `ℓ(v) = 0` force `v = 0`, then
`‖v‖_{k+1,p,Ω} ≤ C (|v|_{k+1,p,Ω} + |ℓ(v)|)` for some `C > 0`. -/
theorem SobolevEuclidean.exists_norm_le_topSeminorm_add_abs_of_isPreconnected
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    (hΩc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (ℓ : SobolevEuclidean N (k + 1) p Ω →L[ℝ] ℝ)
    (h2 : ∀ v : SobolevEuclidean N (k + 1) p Ω,
      (∃ q ∈ restrictTotalDegree (Fin N) ℝ k, fn v
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fun x ↦ eval (fun i ↦ x i) q) →
        ℓ v = 0 → v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevEuclidean N (k + 1) p Ω,
      ‖v‖ ≤ C * (topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v
        + |ℓ v|) := by
  obtain ⟨C, hC, hle⟩ := SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_abs_of_isPreconnected
    hΩ hμ hΩc (fun _ : Unit ↦ ℓ) fun v hv hℓ ↦ h2 v hv (hℓ ())
  exact ⟨C, hC, fun v ↦ by simpa only [Fintype.sum_unique] using hle v⟩

/-- The restriction to an open subset of an element with vanishing top-order derivatives has
vanishing top-order derivatives. -/
theorem SobolevMultiIndex.topSeminorm_restrictL_eq_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω Ω' : Opens E} {μ : Measure E} (h : Ω' ≤ Ω)
    {v : SobolevMultiIndex F b k p Ω μ} (hv : topSeminorm F b k p Ω μ v = 0) :
    topSeminorm F b k p Ω' μ (restrictL F b k p μ h v) = 0 := by
  rw [topSeminorm_eq_zero_iff] at hv ⊢
  intro α
  refine Lp.ext ((weakDeriv_restrictL h v α).trans ?_)
  rw [hv α]
  refine Filter.EventuallyEq.trans (ae_mono (Measure.restrict_mono h le_rfl)
    (Lp.coeFn_zero F p (μ.restrict (Ω : Set E)))) ?_
  exact (Lp.coeFn_zero F p _).symm

/-- **Theorem 7.3.14 of `[han2009theoretical]`, the norm (7.3.3)**: on an extension domain
`Ω ⊆ ℝ^N` of finite measure which is the union `Ω = ⋃_λ Ω_λ` of connected open sets (the book's
disjoint union of Lipschitz domains — disjointness is not needed), `k ≥ 1` and `1 ≤ p < ∞`, for
seminorms `f_j` on `W^{k,p}(Ω)` with (H1) `f_j(v) ≤ c ‖v‖` and (H2) "`v|_{Ω_λ} ∈ ℙ_{k−1}(Ω_λ)` for
every `λ` and all `f_j(v) = 0` force `v = 0`", there is `C > 0` with
`‖v‖_{k,p,Ω} ≤ C (|v|_{k,p,Ω} + ∑_j f_j(v))` for all `v`. The order is written `k + 1`. -/
theorem SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_iSup
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {Λ : Type*}
    {Ω' : Λ → Opens (EuclideanSpace ℝ (Fin N))} (hΩ' : Ω = ⨆ l, Ω' l)
    (hc : ∀ l, IsPreconnected (Ω' l : Set (EuclideanSpace ℝ (Fin N)))) {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevEuclidean N (k + 1) p Ω)) {c : ℝ} (hf : ∀ j v, f j v ≤ c * ‖v‖)
    (h2 : ∀ v : SobolevEuclidean N (k + 1) p Ω,
      (∀ l, ∃ q ∈ restrictTotalDegree (Fin N) ℝ k, fn v
        =ᵐ[volume.restrict (Ω' l : Set (EuclideanSpace ℝ (Fin N)))]
          fun x ↦ eval (fun i ↦ x i) q) →
        (∀ j, f j v = 0) → v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevEuclidean N (k + 1) p Ω,
      ‖v‖ ≤ C * (topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v
        + ∑ j, f j v) := by
  refine SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_forall_eq_zero hΩ hμ f hf
    fun v hv hfv ↦ h2 v (fun l ↦ ?_) hfv
  have hle : Ω' l ≤ Ω := hΩ' ▸ le_iSup Ω' l
  obtain ⟨q, hq, hvq⟩ :=
    SobolevEuclidean.exists_mem_restrictTotalDegree_ae_eq_of_topSeminorm_eq_zero (hc l)
      (SobolevMultiIndex.topSeminorm_restrictL_eq_zero hle hv)
  exact ⟨q, hq, (fn_restrictL hle v).symm.trans hvq⟩

/-- **Theorem 7.3.13 of `[han2009theoretical]`, the norm (7.3.4)**: under the hypotheses of
`SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_forall_eq_zero`,
`‖v‖_{k,p,Ω} ≤ C (|v|_{k,p,Ω}^p + ∑_j f_j(v)^p)^{1/p}` for some `C > 0`. -/
theorem SobolevEuclidean.exists_norm_le_lp_topSeminorm_sum_of_forall_eq_zero
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevEuclidean N (k + 1) p Ω)) {c : ℝ} (hf : ∀ j v, f j v ≤ c * ‖v‖)
    (h2 : ∀ v : SobolevEuclidean N (k + 1) p Ω,
      topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v = 0 →
        (∀ j, f j v = 0) → v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevEuclidean N (k + 1) p Ω,
      ‖v‖ ≤ C * (topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v
          ^ (p : ℝ≥0∞).toReal + ∑ j, f j v ^ (p : ℝ≥0∞).toReal) ^ (1 / (p : ℝ≥0∞).toReal) := by
  obtain ⟨C, hC, h⟩ :=
    SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_forall_eq_zero hΩ hμ f hf h2
  refine ⟨C * (Fintype.card J + 1), by positivity, fun v ↦ (h v).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (add_le_card_mul_lp_topSeminorm_sum (by simp) f v) hC.le

end Euclidean

/-! ### The top-order seminorm at order one is the gradient norm -/

section OrderOneSeminorm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E}

/-- The multi-indices of order exactly one are the `e_i`. -/
theorem MultiIndexLE.single_bijective :
    Function.Bijective fun i : ι ↦ (⟨MultiIndexLE.single i, by simp⟩ : MultiIndexEq ι 1) := by
  refine ⟨fun i j h ↦ MultiIndexLE.single_injective (Subtype.mk.inj h), fun α ↦ ?_⟩
  rcases MultiIndexLE.eq_zero_or_exists_eq_single α.1 with h0 | ⟨i, hi⟩
  · have := α.2
    rw [h0] at this
    simp at this
  · exact ⟨i, Subtype.ext hi.symm⟩

namespace SobolevMultiIndex

/-- **The top-order seminorm of `W^{1,p}(Ω)` is the gradient norm**: `|u|_{1,p,Ω} = ‖∇u‖_p`. -/
theorem topSeminorm_one_eq_gradNorm (u : SobolevMultiIndex F b 1 p Ω μ) :
    topSeminorm F b 1 p Ω μ u = gradNorm u := by
  rw [topSeminorm_apply, gradNorm]
  rcases eq_or_ne p ⊤ with rfl | hp
  · rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_ciSup]
    exact ((Equiv.ofBijective _ MultiIndexLE.single_bijective).iSup_comp
      (g := fun α : MultiIndexEq ι 1 ↦ ‖topDeriv u α‖)).symm
  · have hP : 0 < p.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
    rw [PiLp.norm_eq_sum hP, PiLp.norm_eq_sum hP]
    congr 1
    exact (Fintype.sum_bijective _ MultiIndexLE.single_bijective _ _ fun i ↦ rfl).symm

end SobolevMultiIndex

end OrderOneSeminorm

section Conclusion

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

/-- **The two Deny–Lions norms, from the one inequality**: if `‖v‖ ≤ C (|v|_{k,p} + ∑_j f_j(v))`
for some `C > 0` and `f_j(v) ≤ c ‖v‖` for all `j`, then both `|v|_{k,p} + ∑_j f_j(v)` (the
quantity (7.3.3) of Atkinson–Han) and `(|v|_{k,p}^p + ∑_j f_j(v)^p)^{1/p}` (their (7.3.4)) vanish
only at `v = 0` and are bounded above and below by positive multiples of `‖v‖`: they are norms on
`W^{k,p}(Ω)` equivalent to its norm. -/
theorem norm_equiv_of_exists_norm_le_topSeminorm_add_sum (hp' : p ≠ ⊤) {J : Type*} [Fintype J]
    {f : J → Seminorm ℝ (SobolevMultiIndex F b k p Ω μ)} {c : ℝ} (hf : ∀ j v, f j v ≤ c * ‖v‖)
    (h : ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevMultiIndex F b k p Ω μ,
      ‖v‖ ≤ C * (topSeminorm F b k p Ω μ v + ∑ j, f j v)) :
    ((∀ v, topSeminorm F b k p Ω μ v + ∑ j, f j v = 0 → v = 0) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ v : SobolevMultiIndex F b k p Ω μ,
        c₁ * ‖v‖ ≤ topSeminorm F b k p Ω μ v + ∑ j, f j v ∧
        topSeminorm F b k p Ω μ v + ∑ j, f j v ≤ c₂ * ‖v‖) ∧
    ((∀ v, (topSeminorm F b k p Ω μ v ^ p.toReal + ∑ j, f j v ^ p.toReal) ^ (1 / p.toReal) = 0 →
        v = 0) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ v : SobolevMultiIndex F b k p Ω μ,
        c₁ * ‖v‖ ≤ (topSeminorm F b k p Ω μ v ^ p.toReal + ∑ j, f j v ^ p.toReal) ^ (1 / p.toReal) ∧
        (topSeminorm F b k p Ω μ v ^ p.toReal + ∑ j, f j v ^ p.toReal) ^ (1 / p.toReal)
          ≤ c₂ * ‖v‖) := by
  obtain ⟨C, hC, hle⟩ := h
  have hf' : ∀ j v, f j v ≤ max c 0 * ‖v‖ := fun j v ↦
    (hf j v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hupper := fun v ↦ topSeminorm_add_sum_le_norm f hf' v
  have hc₂ : (0 : ℝ) < 1 + Fintype.card J * max c 0 := by positivity
  have hlow : ∀ v, C⁻¹ * ‖v‖ ≤ topSeminorm F b k p Ω μ v + ∑ j, f j v := fun v ↦ by
    rw [inv_mul_le_iff₀ hC]
    exact hle v
  have hJ : (0 : ℝ) < Fintype.card J + 1 := by positivity
  refine ⟨⟨fun v hv ↦ ?_, C⁻¹, 1 + Fintype.card J * max c 0, inv_pos.2 hC, hc₂, fun v ↦
    ⟨hlow v, hupper v⟩⟩, ⟨fun v hv ↦ ?_, C⁻¹ * ((Fintype.card J : ℝ) + 1)⁻¹,
      1 + Fintype.card J * max c 0, mul_pos (inv_pos.2 hC) (inv_pos.2 hJ), hc₂,
      fun v ↦ ⟨?_, ?_⟩⟩⟩
  · have := hlow v
    rw [hv] at this
    exact norm_eq_zero.1 (le_antisymm (by nlinarith [norm_nonneg v, inv_pos.2 hC])
      (norm_nonneg _))
  · have h1 := add_le_card_mul_lp_topSeminorm_sum hp' f v
    rw [hv, mul_zero] at h1
    have h2 := (hle v).trans (mul_le_mul_of_nonneg_left h1 hC.le)
    rw [mul_zero] at h2
    exact norm_eq_zero.1 (le_antisymm h2 (norm_nonneg _))
  · have h1 := add_le_card_mul_lp_topSeminorm_sum hp' f v
    rw [mul_assoc, inv_mul_le_iff₀ hC, inv_mul_le_iff₀ hJ, mul_left_comm]
    exact (hle v).trans (mul_le_mul_of_nonneg_left h1 hC.le)
  · exact (lp_topSeminorm_sum_le_add hp' f v).trans (hupper v)

end SobolevMultiIndex

end Conclusion

/-! ### The quotient norm

The norm of `V/ℝw` at a class `[v]` is `inf_α ‖v + α • w‖`. A seminorm `N ≤ ‖·‖` with `N w = 0`
is bounded by it, and it is bounded by `C N v` when `‖v‖ ≤ C (N v + |ℓ v|)` for a linear
functional `ℓ` with `ℓ w ≠ 0` (Lemma 8.4.1 of `[han2009theoretical]`, `V = H¹(Ω)`, `w = 1`,
`N = |·|_{1,Ω}` and `ℓ v = ∫_Ω v`). -/

section Quotient

namespace Seminorm

/-- A seminorm does not see a vector on which it vanishes: `N (v + α w) = N v` when `N w = 0`. -/
theorem apply_add_smul_of_eq_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    (N : Seminorm ℝ V) {w : V} (hw : N w = 0) (v : V) (α : ℝ) : N (v + α • w) = N v := by
  refine le_antisymm ?_ ?_
  · calc N (v + α • w) ≤ N v + N (α • w) := map_add_le_add _ _ _
      _ = N v := by rw [map_smul_eq_mul, hw, mul_zero, add_zero]
  · calc N v = N ((v + α • w) + (-α) • w) := by
          rw [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
      _ ≤ N (v + α • w) + N ((-α) • w) := map_add_le_add _ _ _
      _ = N (v + α • w) := by rw [map_smul_eq_mul, hw, mul_zero, add_zero]

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]

/-- **A seminorm bounded by the norm and vanishing at `w` is bounded by the quotient norm**:
`N v ≤ inf_α ‖v + α • w‖` when `N ≤ ‖·‖` and `N w = 0`. -/
theorem le_ciInf_norm_add_smul (N : Seminorm ℝ V) (hN : ∀ v, N v ≤ ‖v‖) {w : V} (hw : N w = 0)
    (v : V) : N v ≤ ⨅ α : ℝ, ‖v + α • w‖ :=
  le_ciInf fun α ↦ (N.apply_add_smul_of_eq_zero hw v α).symm.trans_le (hN _)

/-- **The quotient norm is bounded by a seminorm `N` with `N w = 0`** as soon as
`‖v‖ ≤ C (N v + |ℓ v|)` for a bounded linear functional `ℓ` with `ℓ w ≠ 0`: the representative
`v + α • w` with `α = -ℓ v / ℓ w` has `ℓ (v + α • w) = 0`, so `inf_α ‖v + α • w‖ ≤ C N v`. -/
theorem ciInf_norm_add_smul_le_mul (N : Seminorm ℝ V) (ℓ : V →L[ℝ] ℝ) {w : V} (hw : N w = 0)
    (hℓw : ℓ w ≠ 0) {C : ℝ} (hle : ∀ v, ‖v‖ ≤ C * (N v + |ℓ v|)) (v : V) :
    ⨅ α : ℝ, ‖v + α • w‖ ≤ C * N v := by
  have hbdd : BddBelow (Set.range fun α : ℝ ↦ ‖v + α • w‖) :=
    ⟨0, by rintro _ ⟨α, rfl⟩; exact norm_nonneg _⟩
  have hℓ0 : ℓ (v + (-(ℓ v) / ℓ w) • w) = 0 := by
    rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hℓw, add_neg_cancel]
  calc ⨅ α : ℝ, ‖v + α • w‖ ≤ ‖v + (-(ℓ v) / ℓ w) • w‖ := ciInf_le hbdd _
    _ ≤ C * (N (v + (-(ℓ v) / ℓ w) • w) + |ℓ (v + (-(ℓ v) / ℓ w) • w)|) := hle _
    _ = C * N v := by rw [hℓ0, abs_zero, add_zero, N.apply_add_smul_of_eq_zero hw]

end Seminorm

end Quotient

/-! ### The quotient by a finite-dimensional subspace -/

section QuotientSubspace

namespace Seminorm

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]

/-- A seminorm does not see a vector on which it vanishes: `N (v + q) = N v` when `N q = 0`. -/
theorem apply_add_of_eq_zero (N : Seminorm ℝ V) {q : V} (hq : N q = 0) (v : V) :
    N (v + q) = N v := by
  simpa using N.apply_add_smul_of_eq_zero hq v 1

/-- **A seminorm bounded by the norm and vanishing on a subspace `P` is bounded by the quotient
norm of `V/P`**: `N v ≤ inf_{q ∈ P} ‖v + q‖` when `N ≤ ‖·‖` and `N` vanishes on `P`. -/
theorem le_ciInf_norm_add (N : Seminorm ℝ V) (hN : ∀ v, N v ≤ ‖v‖) (P : Submodule ℝ V)
    (hP : ∀ q ∈ P, N q = 0) (v : V) : N v ≤ ⨅ q : P, ‖v + q‖ :=
  le_ciInf fun q ↦ (N.apply_add_of_eq_zero (hP q q.2) v).symm.trans_le (hN _)

/-- **The quotient norm of `V/P` is bounded by a seminorm `N` vanishing on `P`** under the
Deny–Lions inequality `‖v‖ ≤ C (N v + ∑_j |ℓ_j v|)` for functionals `ℓ_j` extending the
coordinate functionals of a basis `b` of `P`: the representative `v + q` with
`q = -∑_j ℓ_j(v) b_j` has all `ℓ_j (v + q) = 0`, so `inf_{q ∈ P} ‖v + q‖ ≤ C N v`. -/
theorem ciInf_norm_add_le_mul (N : Seminorm ℝ V) (P : Submodule ℝ V) (hP : ∀ q ∈ P, N q = 0)
    {J : Type*} [Fintype J] (b : Basis J ℝ P) {ℓ : J → V →L[ℝ] ℝ}
    (hℓ : ∀ j (x : P), ℓ j x = b.coord j x) {C : ℝ}
    (hle : ∀ v, ‖v‖ ≤ C * (N v + ∑ j, |ℓ j v|)) (v : V) : ⨅ q : P, ‖v + q‖ ≤ C * N v := by
  have hbdd : BddBelow (Set.range fun q : P ↦ ‖v + q‖) :=
    ⟨0, by rintro _ ⟨q, rfl⟩; exact norm_nonneg _⟩
  obtain ⟨q, hq⟩ : ∃ q : P, q = -∑ j, ℓ j v • b j := ⟨_, rfl⟩
  have hℓ0 : ∀ i, ℓ i (v + q) = 0 := fun i ↦ by
    rw [map_add, hℓ i q, Basis.coord_apply, hq, map_neg, Finsupp.neg_apply, Basis.repr_sum_self,
      add_neg_cancel]
  calc ⨅ q : P, ‖v + q‖ ≤ ‖v + q‖ := ciInf_le hbdd q
    _ ≤ C * (N (v + q) + ∑ j, |ℓ j (v + q)|) := hle _
    _ = C * N v := by
      simp only [hℓ0, abs_zero, Finset.sum_const_zero, add_zero,
        N.apply_add_of_eq_zero (hP q q.2)]

end Seminorm

namespace Submodule

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The coordinate functionals of a basis of a finite-dimensional subspace extend to bounded
linear functionals on the whole space** (the Hahn–Banach theorem). -/
theorem exists_continuousLinearMap_forall_apply_eq_coord (P : Submodule ℝ V)
    [FiniteDimensional ℝ P] {J : Type*} (b : Basis J ℝ P) :
    ∃ ℓ : J → V →L[ℝ] ℝ, ∀ j (x : P), ℓ j x = b.coord j x := by
  have h : ∀ j, ∃ g : V →L[ℝ] ℝ, ∀ x : P, g x = b.coord j x := fun j ↦
    (exists_extension_norm_eq P (LinearMap.toContinuousLinearMap (b.coord j))).imp
      fun g hg x ↦ hg.1 x
  choose ℓ hℓ using h
  exact ⟨ℓ, hℓ⟩

/-- A vector of `P` on which functionals extending the coordinate functionals of a basis of `P`
all vanish is zero. -/
theorem eq_zero_of_forall_apply_eq_zero {P : Submodule ℝ V} {J : Type*} (b : Basis J ℝ P)
    {ℓ : J → V →L[ℝ] ℝ} (hℓ : ∀ j (x : P), ℓ j x = b.coord j x) {q : V} (hq : q ∈ P)
    (h : ∀ j, ℓ j q = 0) : q = 0 := by
  have : (⟨q, hq⟩ : P) = 0 :=
    b.forall_coord_eq_zero_iff.1 fun j ↦ (hℓ j ⟨q, hq⟩).symm.trans (h j)
  exact congrArg Subtype.val this

end Submodule

end QuotientSubspace

/-! ### Higher derivatives of polynomial functions -/

section PolynomialDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι]

namespace MvPolynomial

omit [Fintype ι] in
/-- The monomials of `∂_i q` come from those of `q`: `m ∈ supp (∂_i q)` gives
`m + e_i ∈ supp q`. -/
theorem add_single_mem_support_of_mem_support_pderiv {q : MvPolynomial ι ℝ} {i : ι}
    {m : ι →₀ ℕ} (hm : m ∈ (pderiv i q).support) : m + Finsupp.single i 1 ∈ q.support := by
  rw [mem_support_iff] at hm ⊢
  rw [coeff_pderiv] at hm
  exact left_ne_zero_of_mul hm

omit [Fintype ι] in
/-- The monomials of `∂_i q` have degree at most `k` when those of `q` have degree at most
`k + 1`. -/
theorem degree_le_of_mem_support_pderiv {q : MvPolynomial ι ℝ} {k : ℕ}
    (hq : ∀ m ∈ q.support, m.degree ≤ k + 1) {i : ι} {m : ι →₀ ℕ}
    (hm : m ∈ (pderiv i q).support) : m.degree ≤ k := by
  have := hq _ (add_single_mem_support_of_mem_support_pderiv hm)
  rw [map_add, Finsupp.degree_single] at this
  omega

variable (b : Basis ι ℝ E)

/-- The derivative of a polynomial function, as a function: `∑ i, evalBasis b (∂_i q) • e_i^*`,
with `e_i^*` the coordinate functionals of the basis. -/
theorem fderiv_evalBasis (q : MvPolynomial ι ℝ) :
    fderiv ℝ (evalBasis b q) = fun x ↦ ∑ i, evalBasis b (pderiv i q) x •
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).comp
        (b.equivFunL : E →L[ℝ] (ι → ℝ)) := by
  funext x
  rw [(hasFDerivAt_evalBasis b q x).fderiv, ContinuousLinearMap.finsetSum_comp]
  simp only [ContinuousLinearMap.smul_comp, evalBasis]

omit [Fintype ι] in
/-- The `n`-th derivative of `g • c`, `c` a constant vector, vanishes with that of `g`. -/
theorem _root_.iteratedFDeriv_smul_const_eq_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : E → ℝ} {n : ℕ} (hg : ContDiff ℝ ∞ g)
    (h : iteratedFDeriv ℝ n g = 0) (c : F) : iteratedFDeriv ℝ n (fun y ↦ g y • c) = 0 := by
  have hgc : (fun y ↦ g y • c) = (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c) ∘ g := by
    funext y
    simp
  rw [hgc]
  funext x
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left _ hg.contDiffAt (by simp), h]
  ext m
  simp

/-- **The `(k+1)`-st derivative of a polynomial function of degree at most `k` vanishes.** -/
theorem iteratedFDeriv_evalBasis_eq_zero {k : ℕ} :
    ∀ q : MvPolynomial ι ℝ, (∀ m ∈ q.support, m.degree ≤ k) →
      iteratedFDeriv ℝ (k + 1) (evalBasis b q) = 0 := by
  induction k with
  | zero =>
    intro q hq
    have hdeg : q.totalDegree ≤ 0 := (mem_restrictTotalDegree _ _ _).1
      (mem_restrictTotalDegree_of_forall_degree_lt fun m hm ↦ Nat.lt_succ_of_le (hq m hm))
    have hqC : q = C (q.coeff 0) := totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hdeg)
    have hconst : evalBasis b q = fun _ ↦ q.coeff 0 := by
      funext x
      conv_lhs => rw [hqC]
      exact evalBasis_C b _ x
    rw [hconst]
    exact iteratedFDeriv_succ_const 0 _
  | succ k ih =>
    intro q hq
    have hd : ∀ i, ∀ m ∈ (pderiv i q).support, m.degree ≤ k := fun i m hm ↦
      degree_le_of_mem_support_pderiv hq hm
    have hf0 : iteratedFDeriv ℝ (k + 1) (fun y ↦ fderiv ℝ (evalBasis b q) y) = 0 := by
      simp only [fderiv_evalBasis]
      rw [iteratedFDeriv_sum (f := fun i y ↦ evalBasis b (pderiv i q) y •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).comp
          (b.equivFunL : E →L[ℝ] (ι → ℝ)))
        fun i _ ↦ ((contDiff_evalBasis b _).smul contDiff_const).of_le (by simp)]
      exact Finset.sum_eq_zero fun i _ ↦
        iteratedFDeriv_smul_const_eq_zero (contDiff_evalBasis b _) (ih _ (hd i)) _
    funext x
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, hf0, Pi.zero_apply, map_zero,
      Pi.zero_apply]

/-- The `n`-th derivative of a polynomial function of degree at most `k` vanishes for every
`n ≥ k + 1`. -/
theorem iteratedFDeriv_evalBasis_eq_zero_of_le {k : ℕ} {q : MvPolynomial ι ℝ}
    (hq : ∀ m ∈ q.support, m.degree ≤ k) {n : ℕ} (hn : k + 1 ≤ n) :
    iteratedFDeriv ℝ n (evalBasis b q) = 0 := by
  induction n, hn using Nat.le_induction with
  | base => exact iteratedFDeriv_evalBasis_eq_zero b q hq
  | succ n _ ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, ih, fderiv_zero]
    funext x
    simp

end MvPolynomial

end PolynomialDeriv

/-! ### The top seminorm vanishes on polynomials -/

section TopPolynomial

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

open MvPolynomial

/-- **The top seminorm vanishes on the polynomials of degree at most `k`**: an element of
`W^{k+1,p}(Ω)` whose function is a polynomial of degree at most `k` almost everywhere has
vanishing weak derivatives of order `k + 1`. -/
theorem topSeminorm_eq_zero_of_fn_ae_eq_evalBasis [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] (u : SobolevMultiIndex ℝ b (k + 1) p Ω μ) {q : MvPolynomial ι ℝ}
    (hq : ∀ m ∈ q.support, m.degree ≤ k)
    (hu : fn u =ᵐ[μ.restrict (Ω : Set E)] evalBasis b q) :
    topSeminorm ℝ b (k + 1) p Ω μ u = 0 := by
  rw [topSeminorm_eq_zero_iff]
  intro α
  have h := weakDeriv_ae_eq_iteratedFDeriv_of_fn_ae_eq u (contDiff_evalBasis b q) hu α.1
  rw [iteratedFDeriv_evalBasis_eq_zero_of_le b hq α.2.ge] at h
  simp only [Pi.zero_apply, zero_apply] at h
  exact Lp.ext (h.trans (Lp.coeFn_zero ℝ p _).symm)

end SobolevMultiIndex

end TopPolynomial

/-! ### The polynomials of degree at most `k` inside `W^{k+1,p}(Ω)`, and the Sobolev quotient -/

section SobolevQuotient

open MvPolynomial SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))} {k : ℕ}

namespace SobolevEuclidean

/-- The polynomial function `x ↦ q(x)` is the function of an element of `W^{k,p}(Ω)`, `Ω`
bounded. -/
theorem exists_fn_ae_eq_eval (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (q : MvPolynomial (Fin N) ℝ) :
    ∃ u : SobolevEuclidean N k p Ω,
      fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ eval (fun i ↦ x i) q := by
  have h : (fun x : EuclideanSpace ℝ (Fin N) ↦ eval (fun i ↦ x i) q)
      = evalBasis (EuclideanSpace.basisFun (Fin N) ℝ).toBasis q :=
    funext fun x ↦ (evalBasis_basisFun q x).symm
  rw [h]
  exact exists_fn_ae_eq_of_contDiff hb (contDiff_evalBasis _ q)

/-- **The polynomial `q` as an element of `W^{k,p}(Ω)`**, `Ω` bounded: an element whose
function is `x ↦ q(x)` almost everywhere on `Ω`. -/
def ofPolynomial (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (q : MvPolynomial (Fin N) ℝ) : SobolevEuclidean N k p Ω :=
  (exists_fn_ae_eq_eval (k := k) (p := p) hb q).choose

/-- The function of `ofPolynomial hb q` is `x ↦ q(x)` almost everywhere on `Ω`. -/
theorem fn_ofPolynomial (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (q : MvPolynomial (Fin N) ℝ) :
    fn (ofPolynomial (k := k) (p := p) hb q)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fun x ↦ eval (fun i ↦ x i) q :=
  (exists_fn_ae_eq_eval (k := k) (p := p) hb q).choose_spec

/-- `ofPolynomial` is additive: the elements are determined by their functions. -/
theorem ofPolynomial_add (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (q r : MvPolynomial (Fin N) ℝ) :
    ofPolynomial (k := k) (p := p) hb (q + r)
      = ofPolynomial (k := k) (p := p) hb q + ofPolynomial (k := k) (p := p) hb r :=
  ext_of_fn_ae_eq <| by
    filter_upwards [fn_ofPolynomial (k := k) (p := p) hb (q + r),
      fn_ofPolynomial (k := k) (p := p) hb q, fn_ofPolynomial (k := k) (p := p) hb r,
      fn_add (ofPolynomial (k := k) (p := p) hb q) (ofPolynomial (k := k) (p := p) hb r)]
      with x h1 h2 h3 h4
    rw [h1, h4, Pi.add_apply, h2, h3, map_add]

/-- `ofPolynomial` is homogeneous. -/
theorem ofPolynomial_smul (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (c : ℝ) (q : MvPolynomial (Fin N) ℝ) :
    ofPolynomial (k := k) (p := p) hb (c • q) = c • ofPolynomial (k := k) (p := p) hb q :=
  ext_of_fn_ae_eq <| by
    filter_upwards [fn_ofPolynomial (k := k) (p := p) hb (c • q),
      fn_ofPolynomial (k := k) (p := p) hb q,
      fn_smul c (ofPolynomial (k := k) (p := p) hb q)] with x h1 h2 h3
    rw [h1, h3, Pi.smul_apply, h2, smul_eval, smul_eq_mul]

/-- **`ℙ_k → W^{k+1,p}(Ω)`**, the linear map sending a polynomial of degree at most `k` to its
polynomial function on the bounded open set `Ω`. -/
def polynomialToSobolevₗ (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) :
    restrictTotalDegree (Fin N) ℝ k →ₗ[ℝ] SobolevEuclidean N (k + 1) p Ω where
  toFun q := ofPolynomial (k := k + 1) (p := p) hb q.1
  map_add' q r := ofPolynomial_add (k := k + 1) (p := p) hb q.1 r.1
  map_smul' c q := ofPolynomial_smul (k := k + 1) (p := p) hb c q.1

/-- **`ℙ_k(Ω)` inside `W^{k+1,p}(Ω)`**: the subspace of the elements whose function is a
polynomial of degree at most `k` almost everywhere on the bounded open set `Ω`, the range of
`polynomialToSobolevₗ`; the quotient `W^{k+1,p}(Ω)/ℙ_k(Ω)` of §7.3.6 of `[han2009theoretical]` is
the quotient by it. -/
def polynomialSubmodule (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) :
    Submodule ℝ (SobolevEuclidean N (k + 1) p Ω) :=
  LinearMap.range (polynomialToSobolevₗ (k := k) (p := p) hb)

/-- `ℙ_k(Ω)` is finite-dimensional, as the image of `ℙ_k`. -/
instance instFiniteDimensionalPolynomialSubmodule
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) :
    FiniteDimensional ℝ (polynomialSubmodule (k := k) (p := p) hb) :=
  Module.Finite.range _

/-- **Membership in `ℙ_k(Ω)`**: the function is a polynomial of degree at most `k` almost
everywhere on `Ω`. -/
theorem mem_polynomialSubmodule_iff
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    {u : SobolevEuclidean N (k + 1) p Ω} :
    u ∈ polynomialSubmodule hb ↔ ∃ q ∈ restrictTotalDegree (Fin N) ℝ k,
      fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ eval (fun i ↦ x i) q := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.1, q.2, fn_ofPolynomial (k := k + 1) (p := p) hb q.1⟩
  · rintro ⟨q, hq, hu⟩
    exact ⟨⟨q, hq⟩,
      ext_of_fn_ae_eq ((fn_ofPolynomial (k := k + 1) (p := p) hb q).trans hu.symm)⟩

/-- The top seminorm `|·|_{k+1,p,Ω}` vanishes on `ℙ_k(Ω)`. -/
theorem topSeminorm_eq_zero_of_mem_polynomialSubmodule
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    {u : SobolevEuclidean N (k + 1) p Ω} (hu : u ∈ polynomialSubmodule hb) :
    topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume u = 0 := by
  obtain ⟨q, hq, hu⟩ := (mem_polynomialSubmodule_iff hb).1 hu
  refine topSeminorm_eq_zero_of_fn_ae_eq_evalBasis u (q := q) (fun m hm ↦ ?_)
    (hu.trans (Eventually.of_forall fun x ↦ (evalBasis_basisFun q x).symm))
  exact (le_totalDegree hm).trans ((mem_restrictTotalDegree _ _ _).1 hq)

/-- The top seminorm is constant on the classes of `W^{k+1,p}(Ω)/ℙ_k(Ω)`. -/
theorem topSeminorm_add_of_mem_polynomialSubmodule
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (v : SobolevEuclidean N (k + 1) p Ω) {q : SobolevEuclidean N (k + 1) p Ω}
    (hq : q ∈ polynomialSubmodule hb) :
    topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume (v + q)
      = topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v :=
  Seminorm.apply_add_of_eq_zero
    (topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume)
    (topSeminorm_eq_zero_of_mem_polynomialSubmodule hb hq) v

/-- **The top seminorm is bounded by the quotient norm**: `|v|_{k+1,p,Ω} ≤ inf_{q ∈ ℙ_k} ‖v + q‖`
(the first inequality in the proof of `[han2009theoretical]` Theorem 7.3.17). -/
theorem topSeminorm_le_ciInf_norm_add
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (v : SobolevEuclidean N (k + 1) p Ω) :
    topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v
      ≤ ⨅ q : polynomialSubmodule (k := k) (p := p) hb, ‖v + q‖ :=
  Seminorm.le_ciInf_norm_add (topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω
    volume) topSeminorm_le_norm (polynomialSubmodule (k := k) (p := p) hb)
    (fun _ hq ↦ topSeminorm_eq_zero_of_mem_polynomialSubmodule hb hq) v

end SobolevEuclidean

end SobolevQuotient

section SobolevQuotientMain

open MvPolynomial SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))} {k : ℕ}

/-- **`|v|_{k+1,p,Ω} = 0` exactly on `ℙ_k(Ω)`** for a connected bounded `Ω`: the top seminorm
descends to a norm on the quotient `W^{k+1,p}(Ω)/ℙ_k(Ω)` (`[han2009theoretical]`, Theorem
7.3.17, "is a norm on `V`"). -/
theorem SobolevEuclidean.topSeminorm_eq_zero_iff_mem_polynomialSubmodule
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hΩc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin N))))
    {u : SobolevEuclidean N (k + 1) p Ω} :
    topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume u = 0 ↔
      u ∈ SobolevEuclidean.polynomialSubmodule hb :=
  ⟨fun h ↦ (SobolevEuclidean.mem_polynomialSubmodule_iff hb).2
    (SobolevEuclidean.exists_mem_restrictTotalDegree_ae_eq_of_topSeminorm_eq_zero hΩc h),
    SobolevEuclidean.topSeminorm_eq_zero_of_mem_polynomialSubmodule hb⟩

/-- **Theorem 7.3.17 of `[han2009theoretical]`, the inequality (7.3.13)**: on a connected
bounded extension domain `Ω ⊆ ℝ^N` (the book's Lipschitz domain) and for `1 ≤ p < ∞`, the
quotient norm of `W^{k+1,p}(Ω)/ℙ_k(Ω)` is bounded by the top seminorm,
`inf_{q ∈ ℙ_k} ‖v + q‖_{k+1,p,Ω} ≤ C |v|_{k+1,p,Ω}`; with
`SobolevEuclidean.topSeminorm_le_ciInf_norm_add` this is the equivalence of the two. The book's
first proof: the coordinate functionals of a basis of `ℙ_k(Ω)` extend by Hahn–Banach to bounded
functionals `ℓ_j` on `W^{k+1,p}(Ω)`, the seminorms `|ℓ_j|` satisfy (H2) of Theorem 7.3.12, and
the representative `v + q` with all `ℓ_j(v + q) = 0` gives the bound. -/
theorem SobolevEuclidean.exists_ciInf_norm_add_le_mul_topSeminorm
    (hΩ : IsSobolevExtensionDomain N p Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hΩc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin N)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevEuclidean N (k + 1) p Ω,
      ⨅ q : SobolevEuclidean.polynomialSubmodule (k := k) (p := p) hb, ‖v + q‖
        ≤ C * topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume v := by
  have hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤ :=
    (hb.measure_lt_top (μ := volume)).ne
  obtain ⟨ℓ, hℓ⟩ := (SobolevEuclidean.polynomialSubmodule (k := k) (p := p)
    hb).exists_continuousLinearMap_forall_apply_eq_coord
      (Module.finBasis ℝ (SobolevEuclidean.polynomialSubmodule (k := k) (p := p) hb))
  obtain ⟨C, hC, hle⟩ := SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_abs_of_isPreconnected
    hΩ hμ hΩc ℓ fun v hv h ↦ Submodule.eq_zero_of_forall_apply_eq_zero _ hℓ
      ((SobolevEuclidean.mem_polynomialSubmodule_iff hb).2 hv) h
  refine ⟨C, hC, fun v ↦ ?_⟩
  exact Seminorm.ciInf_norm_add_le_mul
    (topSeminorm ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (k + 1) p Ω volume)
    (SobolevEuclidean.polynomialSubmodule (k := k) (p := p) hb)
    (fun _ hq ↦ SobolevEuclidean.topSeminorm_eq_zero_of_mem_polynomialSubmodule hb hq)
    (Module.finBasis ℝ (SobolevEuclidean.polynomialSubmodule (k := k) (p := p) hb)) hℓ hle v

end SobolevQuotientMain
