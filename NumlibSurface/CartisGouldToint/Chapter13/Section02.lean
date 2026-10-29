import Numlib.Approximation.MvLagrange
import Numlib.FiniteDifference.Gradient
import Numlib.FiniteDifference.MixedPartial
import NumlibSurface.CartisGouldToint.Chapter13.Section01

/-!
# Cartis–Gould–Toint §13.2: Fast convergence using low-degree oracles

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §13.2. Inexact derivatives of
degrees `o + 1, …, r` (`r = q` for TRqIDA, `p` for ARqpIDA) may be produced by a *finite
derivative-approximation scheme* from oracles of degree at most `o` (finite differences,
multivariate interpolation), with errors of the IDA form (13.1.2). Theorem 13.2.1 then follows from
Theorems 13.1.8 and 13.1.19 once oracle calls are counted: each function value costs one oracle
call and each derivative estimate `c` calls, so the number of oracle calls before the first
approximately optimal iterate is at most `#F + c · #D`.

## Modelling

A scheme (`FiniteDerivativeApproxScheme`) is a deterministic map from a point and requested
accuracies to an inexact jet satisfying `Optimization.JetApprox` (13.1.2), exact in the degrees
`≤ o` (computed by the oracles), with a declared number `cost` of oracle calls per estimate. The
oracle-call semantics are a counting convention, as for all evaluation counts of the book. The
forward-difference gradient (`o = 0`, `r = 1`, `n` function values) and Hessian (`o = 1`,
`r = 2`, `n` gradients) of `FiniteDifference` are schemes (`fdGradientScheme`,
`fdHessianScheme`).

## Stencils and interpolation

* (13.2.1), stated without proof in the book (footnote 93), is `eq_13_2_1`: for `o < i ≤ p` and
  directions `e_{j_1}, …, e_{j_i}`, a fixed stencil with integer points (in units of the step `h`)
  and coefficients `c_k / h^{i-o}` approximates `∇^i f(x)[e_{j_1}, …, e_{j_i}]` from values of
  `∇^o f[e_{j_1}, …, e_{j_o}]` with error `K L_{f,p} h^{p-i+1}`; `eq_13_2_1_ida` gives the IDA
  form `K L_{f,p} h` for `h ≤ 1`. The stencil is a tensor product of one-dimensional derivative
  weights (`FiniteDifference.isMixedStencil_tensor`), and the proof is Taylor's theorem for
  `∇^o f` (`FiniteDifference.abs_sum_iteratedFDeriv_sub_le`).
* Interpolation uses `Approximation.IsLagrangeBasis`: polynomial functions of total degree at most
  `p` on `ℝⁿ` (`Approximation.polyFunLE`, from `MvPolynomial`) with `ℓ_i(y_j) = δ_ij` at poised
  points. `eq_13_2_4` is (13.2.4), `eq_13_2_4_scaled` its scaled form with error
  `L m/(p+1)! Λ_i δ^{p-i+1}`, and `interpolationScheme` packages it as a scheme from function values
  (`o = 0`, `m` values per estimate, interpolation radius `δ = min_i h_i^{1/(p-i+1)}`).
* `stencilScheme` packages (13.2.1) as a scheme: the derivative tensors of degrees `o < i ≤ r` are
  assembled from their entries (`stencilTensor`, `eq_sum_coordProd`), with step
  `h_i^{1/(p-i+1)}` (`accuracyStep`), and satisfy (13.1.2) in the tensor norm.

## Deviations from the book

* (13.2.5)–(13.2.7) print `O(min_j ε_j^{-…})`; the bounds are `O(max_j ε_j^{-…})`, i.e.
  `O(ε_min^{-(q+1)})` for TRqIDA and `O(1/min_j ε_j^{π_j})` for ARqpIDA (with `π_j` as in
  Lemma 13.1.18), consistent with Theorems 13.1.8 and 13.1.19.
* (13.2.2) sets `d = ∑_{i=0}^p C(n+i-1, i)` and interpolates at `d + 1` points `y_0, …, y_d`;
  the sum is the dimension `C(n+p, p)` of the polynomials of degree at most `p`, which is the
  number of points (`eq_13_2_2_card`), so the points are `y_1, …, y_d`. The scaled bound after
  (13.2.4) correspondingly has the factor `m = d` (written `d + 1` in the book).
* (13.2.1) is proved for every step `h > 0` (the book takes `h ∈ (0, 1]`), with coefficients
  `c_k / h^{i-o}` where the book's `c_{i,j}` absorb the power of `h`.
* In the scaled interpolation bound only `‖∇^i ℓ̂_j(0)‖ ≤ Λ_i` is used (the book's `Λ_i` is a
  maximum over the unit ball), and the points need only lie in the closed unit ball.
* The derivative-free discussion is not formalized.
-/

open Set Finset Optimization
open scoped Nat

namespace CartisGouldToint.Chapter13

variable {n : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A **finite derivative-approximation scheme** ([cartis2022evaluation], §13.2) for `f` from
oracles of degree at most `o`, producing inexact derivatives up to degree `r` with the errors
(13.1.2): `est x h` is the inexact jet at `x` for requested accuracies `h > 0`, exact in the degrees
`≤ o`, and each estimate costs `cost` oracle calls (of degree `≤ o`). -/
structure FiniteDerivativeApproxScheme (f : ℝⁿ → ℝ) (o r : ℕ) (κg : ℕ → ℝ) where
  /-- The inexact jet at a point for given requested accuracies. -/
  est : ℝⁿ → (ℕ → ℝ) → FormalMultilinearSeries ℝ ℝⁿ ℝ
  /-- The number of oracle calls per estimate. -/
  cost : ℕ
  /-- The error model (13.1.2). -/
  approx : ∀ x h, (∀ i ∈ Finset.Icc 1 r, 0 < h i) →
    JetApprox (ftaylorSeries ℝ f x) (est x h) r (fun i => κg i * h i)
  /-- The degrees available from the oracles are exact. -/
  exact_low : ∀ x h, ∀ i ≤ o, est x h i = iteratedFDeriv ℝ i f x

/-- **Forward-difference gradients form a scheme** with `o = 0`, `r = 1` and `n` function values
per estimate, `κ_{∇,1} = √n L/2`, when `∇f` is `L`-Lipschitz (§13.2, first display). -/
noncomputable def fdGradientScheme (f : ℝⁿ → ℝ) {L : ℝ} (hf : ContDiff ℝ 1 f)
    (hL : ∀ y z, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖) :
    FiniteDerivativeApproxScheme f 0 1 (fun _ => √n * L / 2) where
  est x h := gradientJet (ftaylorSeries ℝ f x) (FiniteDifference.fdGradient f (h 1) x)
  cost := n
  approx x h hh := by
    refine (FiniteDifference.jetApprox_fdGradient hf hL (hh 1 (by simp)) x).mono_err ?_
    intro i hi
    obtain rfl : i = 1 := by simpa using hi
    exact le_rfl
  exact_low x h i hi := by
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    rw [gradientJet_apply_of_ne _ _ (by norm_num)]
    rfl

/-- **Forward-difference Hessians form a scheme** with `o = 1`, `r = 2` and `n` gradient values
per estimate, `κ_{∇,2} = √n L/2` (`κ_{∇,1} = 0`, the gradient is exact), when the Hessian is
`L`-Lipschitz (§13.2, fourth display). -/
noncomputable def fdHessianScheme (f : ℝⁿ → ℝ) {L : ℝ} (hf : ContDiff ℝ 2 f)
    (hL : ∀ y z, ‖hessianOperator f y - hessianOperator f z‖ ≤ L * ‖y - z‖) :
    FiniteDerivativeApproxScheme f 1 2 (fun i => if i = 2 then √n * L / 2 else 0) where
  est x h := hessianJet (ftaylorSeries ℝ f x) (FiniteDifference.fdHessian f (h 2) x)
  cost := n
  approx x h hh := by
    refine (FiniteDifference.jetApprox_fdHessian hf hL (hh 2 (by simp)) x).mono_err ?_
    intro i hi
    by_cases h2 : i = 2 <;> simp [h2]
  exact_low x h i hi := by
    rw [hessianJet_apply_of_ne _ _ (by omega)]
    rfl

/-! ### Stencil formulas (13.2.1) -/

section Stencil

/-- The stencil points `∑_ℓ (h k_ℓ) e_ℓ` with integer coordinates `k_ℓ` (in units of `h`) are
`h` times the tensor-product stencil points. -/
private theorem sum_mul_int_smul_single {r K : ℕ} (h : ℝ) (j' : Fin r → Fin n)
    (l : Fin r → Fin (K + 1)) :
    ∑ m, (h * ((∑ t, if j' t = m then ((l t : ℕ) : ℤ) else 0 : ℤ) : ℝ)) •
        EuclideanSpace.single m (1 : ℝ) =
      h • FiniteDifference.tensorPoint (fun t => EuclideanSpace.single (j' t) (1 : ℝ)) l := by
  ext q
  simp only [FiniteDifference.tensorPoint, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, PiLp.single_apply, Int.cast_sum, Int.cast_ite, Int.cast_natCast,
    Int.cast_zero]
  simp_rw [mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  simp [mul_ite, eq_comm]

/-- (13.2.1) with `i = o + r` and the stencil indexed by a finite type. -/
private theorem eq_13_2_1_aux {p o r : ℕ} (hor : o + r ≤ p) (j : Fin (o + r) → Fin n) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℝ) (z : ι → Fin n → ℤ) (K : ℝ), 0 ≤ K ∧
      ∀ (f : ℝⁿ → ℝ) (L h : ℝ) (C : Set ℝⁿ) (x : ℝⁿ), Convex ℝ C →
        (∀ y ∈ C, ContDiffAt ℝ p f y) → IteratedFDerivLipschitzOn f p L C → x ∈ C → 0 < h →
        (∀ k, x + ∑ ℓ, (h * z k ℓ) • EuclideanSpace.single ℓ (1 : ℝ) ∈ C) →
        |∑ k, c k / h ^ r * iteratedFDeriv ℝ o f
              (x + ∑ ℓ, (h * z k ℓ) • EuclideanSpace.single ℓ (1 : ℝ))
              (fun t => EuclideanSpace.single (j (Fin.castAdd r t)) 1) -
            iteratedFDeriv ℝ (o + r) f x (fun t => EuclideanSpace.single (j t) 1)| ≤
          K * L * h ^ (p - (o + r) + 1) := by
  let u : Fin r → ℝⁿ := fun t => EuclideanSpace.single (j (Fin.natAdd o t)) (1 : ℝ)
  let v : Fin o → ℝⁿ := fun t => EuclideanSpace.single (j (Fin.castAdd r t)) (1 : ℝ)
  refine ⟨Fin r → Fin (p - o + 1 - r + 1), inferInstance,
    FiniteDifference.tensorWeight (p - o + 1 - r) r,
    fun l ℓ => ∑ t, if j (Fin.natAdd o t) = ℓ then ((l t : ℕ) : ℤ) else 0,
    (∑ l, |FiniteDifference.tensorWeight (p - o + 1 - r) r l| *
      ‖FiniteDifference.tensorPoint u l‖ ^ (p - o + 1)) / ((p - o + 1)! : ℝ), by positivity, ?_⟩
  intro f L h C x hC hf hL hx hh hz
  simp only [sum_mul_int_smul_single] at hz ⊢
  have hb := FiniteDifference.abs_sum_iteratedFDeriv_sub_le hC hf hL hx hor
    (FiniteDifference.isMixedStencil_tensor (q := p - o) (by omega) u) v hh hz
  have hdir : (fun t => EuclideanSpace.single (j t) (1 : ℝ)) = Fin.append v u :=
    Fin.append_castAdd_natAdd.symm
  have hv : ∏ t, ‖v t‖ = 1 := by simp [v]
  rw [hv, mul_one, ← hdir] at hb
  refine hb.trans (le_of_eq ?_)
  ring

/-- **Stencil formulas for derivative tensors** ([cartis2022evaluation], (13.2.1); the book could
not find this result in the literature, footnote 93). Let `0 ≤ o < i ≤ p` and
`j_1, …, j_i ∈ [1 : n]`. There are finitely many coefficients `c_k` and integer vectors `z_k`
(independent of `h` and of `f`) and a constant `K ≥ 0` such that for every `f` that is `C^p` on a
convex set `C` with `∇^p f` `L`-Lipschitz on `C`, every `x ∈ C` and every step `h > 0` with the
stencil points `x + s_k`, `s_k = ∑_ℓ (h z_{k,ℓ}) e_ℓ`, in `C`,
`|∑_k (c_k / h^{i-o}) ∇^o f(x + s_k)[e_{j_1}, …, e_{j_o}] - ∇^i f(x)[e_{j_1}, …, e_{j_i}]| ≤
  K L h^{p-i+1}`.
The book writes the coefficients as `c_{i,j}` (here `c_k / h^{i-o}`) and asks that each
`h_{i,j,ℓ} = h z_{k,ℓ}` be an integer multiple of `h`; it states the error as `O(h^{p-i+1})` for
`h ∈ (0, 1]`; the bound here holds for every `h > 0`. The stencil is the tensor product, over the
`i - o` differentiated directions, of the one-dimensional weights on the nodes
`0, 1, …, p - i + 1` exact on polynomials of degree `p - i + 1`
(`FiniteDifference.isMixedStencil_tensor`); the error comes from Taylor's theorem for `∇^o f`
(`FiniteDifference.abs_sum_iteratedFDeriv_sub_le`). -/
theorem eq_13_2_1 {p o i : ℕ} (hoi : o < i) (hip : i ≤ p) (j : Fin i → Fin n) :
    ∃ (N : ℕ) (c : Fin N → ℝ) (z : Fin N → Fin n → ℤ) (K : ℝ), 0 ≤ K ∧
      ∀ (f : ℝⁿ → ℝ) (L h : ℝ) (C : Set ℝⁿ) (x : ℝⁿ), Convex ℝ C →
        (∀ y ∈ C, ContDiffAt ℝ p f y) → IteratedFDerivLipschitzOn f p L C → x ∈ C → 0 < h →
        (∀ k, x + ∑ ℓ, (h * z k ℓ) • EuclideanSpace.single ℓ (1 : ℝ) ∈ C) →
        |∑ k, c k / h ^ (i - o) * iteratedFDeriv ℝ o f
              (x + ∑ ℓ, (h * z k ℓ) • EuclideanSpace.single ℓ (1 : ℝ))
              (fun t => EuclideanSpace.single (j (Fin.castLE hoi.le t)) 1) -
            iteratedFDeriv ℝ i f x (fun t => EuclideanSpace.single (j t) 1)| ≤
          K * L * h ^ (p - i + 1) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hoi.le
  obtain ⟨ι, _, c, z, K, hK, H⟩ := eq_13_2_1_aux hip j
  let F := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun k => c (F.symm k), fun k => z (F.symm k), K, hK,
    fun f L h C x hC hf hL hx hh hz => ?_⟩
  have := H f L h C x hC hf hL hx hh fun k => by simpa using hz (F k)
  rw [Nat.add_sub_cancel_left]
  convert this using 3
  exact F.symm.sum_comp (fun k => c k / h ^ r * iteratedFDeriv ℝ o f
    (x + ∑ ℓ, (h * z k ℓ) • EuclideanSpace.single ℓ (1 : ℝ))
    (fun t => EuclideanSpace.single (j (Fin.castAdd r t)) 1))

/-- **(13.2.1) componentwise in the IDA form**: with the stencil of `eq_13_2_1`, for steps
`h ∈ (0, 1]` and `L ≥ 0` the error in each entry is at most `K L h`, the componentwise analogue of
(13.1.2) with identical accuracies `h_i = h`. The tensor-norm form is `stencilScheme`. -/
theorem eq_13_2_1_ida {p o i : ℕ} (hoi : o < i) (hip : i ≤ p) (j : Fin i → Fin n) :
    ∃ (N : ℕ) (c : Fin N → ℝ) (z : Fin N → Fin n → ℤ) (K : ℝ), 0 ≤ K ∧
      ∀ (f : ℝⁿ → ℝ) (L h : ℝ) (C : Set ℝⁿ) (x : ℝⁿ), Convex ℝ C →
        (∀ y ∈ C, ContDiffAt ℝ p f y) → IteratedFDerivLipschitzOn f p L C → 0 ≤ L → x ∈ C →
        0 < h → h ≤ 1 → (∀ k, x + ∑ ℓ, (h * z k ℓ) • EuclideanSpace.single ℓ (1 : ℝ) ∈ C) →
        |∑ k, c k / h ^ (i - o) * iteratedFDeriv ℝ o f
              (x + ∑ ℓ, (h * z k ℓ) • EuclideanSpace.single ℓ (1 : ℝ))
              (fun t => EuclideanSpace.single (j (Fin.castLE hoi.le t)) 1) -
            iteratedFDeriv ℝ i f x (fun t => EuclideanSpace.single (j t) 1)| ≤ K * L * h := by
  obtain ⟨N, c, z, K, hK, H⟩ := eq_13_2_1 (p := p) hoi hip j
  refine ⟨N, c, z, K, hK, fun f L h C x hC hf hL hL0 hx hh hh1 hz => ?_⟩
  refine (H f L h C x hC hf hL hx hh hz).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_of_le_one hh.le hh1 (by omega)) (by positivity)

/-- The step `t^{1/(p-i+1)}`, whose `(p - i + 1)`-st power is `t`: the step (or interpolation
radius) at which an error `O(step^{p-i+1})` becomes `O(t)`, the form (13.1.2) with accuracy `t`. -/
noncomputable def accuracyStep (p i : ℕ) (t : ℝ) : ℝ :=
  t ^ (((p - i + 1 : ℕ) : ℝ)⁻¹)

/-- `(t^{1/(p-i+1)})^{p-i+1} = t` for `t ≥ 0`. -/
theorem accuracyStep_pow (p i : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    accuracyStep p i t ^ (p - i + 1) = t :=
  Real.rpow_inv_natCast_pow ht (by omega)

/-- The step of a positive accuracy is positive. -/
theorem accuracyStep_pos (p i : ℕ) {t : ℝ} (ht : 0 < t) : 0 < accuracyStep p i t :=
  Real.rpow_pos_of_pos ht _

/-- The coordinate form `v ↦ ∏_t [v_t]_{j_t}`, dual to `e_{j_1} ⊗ ⋯ ⊗ e_{j_i}`: a tensor is the sum
of its entries `A[e_{j_1}, …, e_{j_i}]` times these forms (`eq_sum_coordProd`). -/
noncomputable def coordProd {i : ℕ} (j : Fin i → Fin n) :
    ContinuousMultilinearMap ℝ (fun _ : Fin i => ℝⁿ) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin i) ℝ).compContinuousLinearMap
    fun t => EuclideanSpace.proj (j t)

/-- Unfolding lemma for `coordProd`. -/
theorem coordProd_apply {i : ℕ} (j : Fin i → Fin n) (v : Fin i → ℝⁿ) :
    coordProd j v = ∏ t, v t (j t) := by
  simp [coordProd]

/-- The coordinate forms have norm at most one. -/
theorem norm_coordProd_le {i : ℕ} (j : Fin i → Fin n) : ‖coordProd j‖ ≤ 1 := by
  refine ContinuousMultilinearMap.opNorm_le_bound zero_le_one fun v => ?_
  rw [coordProd_apply, one_mul, norm_prod]
  gcongr with t
  exact PiLp.norm_apply_le (v t) (j t)

/-- A continuous multilinear form on `ℝⁿ` is determined by its entries:
`A = ∑_j A[e_{j_1}, …, e_{j_i}] · coordProd j`. -/
theorem eq_sum_coordProd {i : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin i => ℝⁿ) ℝ) :
    A = ∑ j : Fin i → Fin n, A (fun t => EuclideanSpace.single (j t) 1) • coordProd j := by
  ext v
  have hv : v = fun t => ∑ k, v t k • EuclideanSpace.single k (1 : ℝ) :=
    funext fun t => (FiniteDifference.sum_smul_single (v t)).symm
  conv_lhs => rw [hv, A.map_sum (fun t k => v t k • EuclideanSpace.single k (1 : ℝ))]
  simp only [_root_.sum_apply, smul_apply, coordProd_apply, smul_eq_mul]
  refine sum_congr rfl fun j _ => ?_
  rw [show (fun t => v t (j t) • EuclideanSpace.single (j t) (1 : ℝ)) =
    fun t => (fun t => v t (j t)) t • (fun t => EuclideanSpace.single (j t) (1 : ℝ)) t from rfl,
    A.map_smul_univ, smul_eq_mul, mul_comm]

/-- The number of points of the stencil of `eq_13_2_1` for the entry `j` (`0` unless
`o < i ≤ p`). -/
noncomputable def stencilSize (p o : ℕ) {i : ℕ} (j : Fin i → Fin n) : ℕ :=
  if hij : o < i ∧ i ≤ p then (eq_13_2_1 hij.1 hij.2 j).choose else 0

/-- The error constant `K` of the stencil of `eq_13_2_1` for the entry `j` (`0` unless
`o < i ≤ p`). -/
noncomputable def stencilConst (p o : ℕ) {i : ℕ} (j : Fin i → Fin n) : ℝ :=
  if hij : o < i ∧ i ≤ p then
    (eq_13_2_1 hij.1 hij.2 j).choose_spec.choose_spec.choose_spec.choose else 0

/-- The stencil error constants are nonnegative. -/
theorem stencilConst_nonneg (p o : ℕ) {i : ℕ} (j : Fin i → Fin n) : 0 ≤ stencilConst p o j := by
  unfold stencilConst
  split_ifs with hij
  · exact (eq_13_2_1 hij.1 hij.2 j).choose_spec.choose_spec.choose_spec.choose_spec.1
  · exact le_rfl

/-- The stencil estimate (13.2.1) of the entry `∇^i f(x)[e_{j_1}, …, e_{j_i}]` with step `h`,
computed from `stencilSize p o j` values of `∇^o f[e_{j_1}, …, e_{j_o}]` (`0` unless
`o < i ≤ p`). -/
noncomputable def stencilEntry (f : ℝⁿ → ℝ) (p o : ℕ) {i : ℕ} (j : Fin i → Fin n) (x : ℝⁿ)
    (h : ℝ) : ℝ :=
  if hij : o < i ∧ i ≤ p then
    ∑ k, (eq_13_2_1 hij.1 hij.2 j).choose_spec.choose k / h ^ (i - o) * iteratedFDeriv ℝ o f
      (x + ∑ ℓ, (h * (eq_13_2_1 hij.1 hij.2 j).choose_spec.choose_spec.choose k ℓ) •
        EuclideanSpace.single ℓ (1 : ℝ))
      (fun t => EuclideanSpace.single (j (Fin.castLE hij.1.le t)) 1)
  else 0

/-- The error of `stencilEntry` for `f` globally `C^p` with `∇^p f` `L`-Lipschitz. -/
theorem abs_stencilEntry_sub_le {f : ℝⁿ → ℝ} {p o i : ℕ} {L h : ℝ} (hoi : o < i) (hip : i ≤ p)
    (hf : ContDiff ℝ p f) (hL : IteratedFDerivLipschitzOn f p L univ) (j : Fin i → Fin n)
    (x : ℝⁿ) (hh : 0 < h) :
    |stencilEntry f p o j x h - iteratedFDeriv ℝ i f x (fun t => EuclideanSpace.single (j t) 1)| ≤
      stencilConst p o j * L * h ^ (p - i + 1) := by
  have hij : o < i ∧ i ≤ p := ⟨hoi, hip⟩
  rw [stencilEntry, dite_eq_left hij, stencilConst, dite_eq_left hij]
  exact (eq_13_2_1 hij.1 hij.2 j).choose_spec.choose_spec.choose_spec.choose_spec.2 f L h univ x
    convex_univ (fun _ _ => hf.contDiffAt) hL (mem_univ x) hh fun _ => mem_univ _

/-- The **stencil estimate of the derivative tensor** `∇^i f(x)`, assembled from its entries
`stencilEntry`: `∑_j (estimate of the entry j) · coordProd j`. -/
noncomputable def stencilTensor (f : ℝⁿ → ℝ) (p o i : ℕ) (x : ℝⁿ) (h : ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin i => ℝⁿ) ℝ :=
  ∑ j : Fin i → Fin n, stencilEntry f p o j x h • coordProd j

/-- **Tensor-norm error of the stencil estimate**: `‖∇̄^i f(x) - ∇^i f(x)‖ ≤ K_i L h^{p-i+1}` with
`K_i = ∑_j K_{i,j}` the sum of the entrywise constants. -/
theorem norm_stencilTensor_sub_le {f : ℝⁿ → ℝ} {p o i : ℕ} {L h : ℝ} (hoi : o < i) (hip : i ≤ p)
    (hf : ContDiff ℝ p f) (hL : IteratedFDerivLipschitzOn f p L univ) (x : ℝⁿ) (hh : 0 < h) :
    ‖stencilTensor f p o i x h - iteratedFDeriv ℝ i f x‖ ≤
      (∑ j : Fin i → Fin n, stencilConst p o j) * L * h ^ (p - i + 1) := by
  have hA := eq_sum_coordProd (iteratedFDeriv ℝ i f x)
  calc ‖stencilTensor f p o i x h - iteratedFDeriv ℝ i f x‖
      = ‖∑ j : Fin i → Fin n, (stencilEntry f p o j x h -
          iteratedFDeriv ℝ i f x (fun t => EuclideanSpace.single (j t) 1)) • coordProd j‖ := by
        conv_lhs => rw [hA]
        rw [stencilTensor, ← sum_sub_distrib]
        exact congrArg norm (Finset.sum_congr rfl fun j _ =>
          (sub_smul (stencilEntry f p o j x h) _ (coordProd j)).symm)
    _ ≤ ∑ j : Fin i → Fin n, stencilConst p o j * L * h ^ (p - i + 1) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
        rw [norm_smul, Real.norm_eq_abs]
        calc _ ≤ |stencilEntry f p o j x h -
              iteratedFDeriv ℝ i f x (fun t => EuclideanSpace.single (j t) 1)| * 1 :=
              mul_le_mul_of_nonneg_left (norm_coordProd_le j) (abs_nonneg _)
          _ ≤ _ := by rw [mul_one]; exact abs_stencilEntry_sub_le hoi hip hf hL j x hh
    _ = _ := by rw [← sum_mul, ← sum_mul]

/-- **Finite differences (13.2.1) form a finite derivative-approximation scheme**
([cartis2022evaluation], §13.2): for `f` globally `C^p` with `∇^p f` `L`-Lipschitz (`L ≥ 0`) and
`r ≤ p`, the derivative tensors of degrees `o < i ≤ r` estimated entrywise by the stencils of
`eq_13_2_1`, with step `h_i^{1/(p-i+1)}` for the requested accuracy `h_i` (`accuracyStep`), and
the exact derivatives of degrees `i ≤ o`, satisfy (13.1.2) in the tensor norm with
`κ_{∇,i} = (∑_j K_{i,j}) L`; each estimate costs `∑_{o<i≤r} ∑_j (stencil size)` evaluations of
derivatives of degree `o`. -/
noncomputable def stencilScheme (f : ℝⁿ → ℝ) {p o r : ℕ} {L : ℝ} (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) (hL0 : 0 ≤ L) (hrp : r ≤ p) :
    FiniteDerivativeApproxScheme f o r
      (fun i => (∑ j : Fin i → Fin n, stencilConst p o j) * L) where
  est x h i := if o < i then stencilTensor f p o i x (accuracyStep p i (h i)) else
    iteratedFDeriv ℝ i f x
  cost := ∑ i ∈ Finset.Ioc o r, ∑ j : Fin i → Fin n, stencilSize p o j
  approx x h hh i hi := by
    obtain ⟨hi1, hir⟩ := Finset.mem_Icc.1 hi
    have hK : 0 ≤ (∑ j : Fin i → Fin n, stencilConst p o j) * L :=
      mul_nonneg (sum_nonneg fun j _ => stencilConst_nonneg p o j) hL0
    by_cases hoi : o < i
    · simp only [hoi, ↓reduceIte]
      refine (norm_stencilTensor_sub_le hoi (by omega) hf hL x
        (accuracyStep_pos p i (hh i hi))).trans (le_of_eq ?_)
      rw [accuracyStep_pow p i (hh i hi).le]
    · simp only [hoi, ↓reduceIte]
      rw [show ftaylorSeries ℝ f x i = iteratedFDeriv ℝ i f x from rfl, sub_self, norm_zero]
      exact mul_nonneg hK (hh i hi).le
  exact_low x h i hi := by
    simp [show ¬ o < i by omega]

end Stencil

/-! ### Multivariate interpolation (13.2.2)–(13.2.4) -/

section Interpolation

open Approximation

/-- **The number of interpolation points in (13.2.2)**: if `ℓ_j` are the Lagrange polynomials of
degree `p` of `m` poised points in `ℝⁿ`, then `m = d = ∑_{i=0}^p C(n+i-1, i)` (`= C(n+p, p)`, the
dimension of the polynomials of degree at most `p`; the Lagrange polynomials form a basis). The
book indexes the points as `y_0, …, y_d`, i.e. `d + 1` of them: the number of points is `d`
(e.g. `n = p = 1` gives `d = 2`, yet linear interpolation on the line uses two points). -/
theorem eq_13_2_2_card {p m : ℕ} {y : Fin m → ℝⁿ} {ℓ : Fin m → ℝⁿ → ℝ}
    (hℓ : IsLagrangeBasis n p y ℓ) : m = ∑ i ∈ range (p + 1), (n + i - 1).choose i :=
  hℓ.card_eq_sum_choose

/-- **The interpolation error bound (13.2.4)** ([cartis2022evaluation]; there quoted from the
literature): if `ℓ_j` are the Lagrange polynomials of degree `p` of the poised points `y_j`
((13.2.2)), `w = ∑_j f(y_j) ℓ_j` is the interpolation model (13.2.3), and `f` is `C^p` on a
convex set `C` containing `x` and the `y_j` with `∇^p f` `L_{f,p}`-Lipschitz on `C`, then for
`i ∈ [0 : p]`, `‖∇^i w(x) - ∇^i f(x)‖ ≤ L_{f,p}/(p+1)! ∑_j ‖y_j - x‖^{p+1} ‖∇^i ℓ_j(x)‖`. -/
theorem eq_13_2_4 {p m : ℕ} {y : Fin m → ℝⁿ} {ℓ : Fin m → ℝⁿ → ℝ}
    (hℓ : IsLagrangeBasis n p y ℓ) {f : ℝⁿ → ℝ} {L : ℝ} {C : Set ℝⁿ} {x : ℝⁿ} (hC : Convex ℝ C)
    (hf : ∀ z ∈ C, ContDiffAt ℝ p f z) (hL : IteratedFDerivLipschitzOn f p L C) (hx : x ∈ C)
    (hy : ∀ j, y j ∈ C) {i : ℕ} (hi : i ≤ p) :
    ‖iteratedFDeriv ℝ i (fun v => ∑ j, f (y j) * ℓ j v) x - iteratedFDeriv ℝ i f x‖ ≤
      L / ((p + 1)! : ℝ) * ∑ j, ‖y j - x‖ ^ (p + 1) * ‖iteratedFDeriv ℝ i (ℓ j) x‖ :=
  hℓ.norm_iteratedFDeriv_sub_le hC hf hL hx hy hi

/-- **The interpolation error with scaled points has the IDA form** ([cartis2022evaluation], §13.2,
the display after (13.2.4)): for Lagrange polynomials `ℓ̂_j` of `m` poised points `ŷ_j` in the
unit ball with `‖∇^i ℓ̂_j(0)‖ ≤ Λ_i`, the model `w` interpolating `f` at `x + δ ŷ_j` (Lagrange
polynomials `v ↦ ℓ̂_j((v - x)/δ)`) satisfies `‖∇^i w(x) - ∇^i f(x)‖ ≤ L m/(p+1)! Λ_i δ^{p-i+1}`,
i.e. (13.1.2) with `κ_{∇,i} = L m Λ_i/(p+1)!` and `h_i = δ^{p-i+1}`. The book writes `d + 1`
for the number `m` of points (see `eq_13_2_2_card`) and takes `Λ_i` as a maximum over the unit
ball; only its value at the centre is used. -/
theorem eq_13_2_4_scaled {p m : ℕ} {y : Fin m → ℝⁿ} {ℓ : Fin m → ℝⁿ → ℝ}
    (hℓ : IsLagrangeBasis n p y ℓ) (hy1 : ∀ j, ‖y j‖ ≤ 1) {i : ℕ} (hi : i ≤ p) {Λ : ℝ}
    (hΛ : ∀ j, ‖iteratedFDeriv ℝ i (ℓ j) 0‖ ≤ Λ) {f : ℝⁿ → ℝ} {L δ : ℝ} {C : Set ℝⁿ} {x : ℝⁿ}
    (hδ : 0 < δ) (hC : Convex ℝ C) (hf : ∀ z ∈ C, ContDiffAt ℝ p f z)
    (hL : IteratedFDerivLipschitzOn f p L C) (hL0 : 0 ≤ L) (hx : x ∈ C)
    (hyC : ∀ j, x + δ • y j ∈ C) :
    ‖iteratedFDeriv ℝ i (fun v => ∑ j, f (x + δ • y j) * ℓ j (δ⁻¹ • (v - x))) x -
        iteratedFDeriv ℝ i f x‖ ≤ L * m / ((p + 1)! : ℝ) * Λ * δ ^ (p - i + 1) :=
  hℓ.norm_iteratedFDeriv_sub_le_of_scaled hy1 hi hΛ hδ hC hf hL hL0 hx hyC

/-- The interpolation radius `δ = min_{i ∈ [1, r]} h_i^{1/(p-i+1)}` used by
`interpolationScheme`: the largest radius with `δ^{p-i+1} ≤ h_i` for all `i ∈ [1, r]`, as in the
book's choice `h_i = δ^{p-i+1}` with one interpolation set for all degrees. -/
noncomputable def interpRadius (p r : ℕ) (h : ℕ → ℝ) : ℝ :=
  epsMin r fun i => accuracyStep p i (h i)

/-- **Interpolation is a finite derivative-approximation scheme** ([cartis2022evaluation], §13.2):
given Lagrange polynomials `ℓ̂_j` of degree `p` of `m` poised reference points `ŷ_j` in the unit
ball with `‖∇^i ℓ̂_j(0)‖ ≤ Λ_i`, and `f` globally `C^p` with `∇^p f` `L`-Lipschitz, the derivatives
`∇^i w(x)`, `1 ≤ i ≤ r ≤ p`, of the model interpolating `f` at `x + δ ŷ_j` with
`δ = min_i h_i^{1/(p-i+1)}` (`interpRadius`) form a scheme from function values only (`o = 0`,
`m` values per estimate) with `κ_{∇,i} = L m Λ_i/(p+1)!`: the error `κ_{∇,i} δ^{p-i+1}` is at
most `κ_{∇,i} h_i`, with equality of `δ^{p-i+1}` and `h_i` for the degree attaining the minimum. -/
noncomputable def interpolationScheme (f : ℝⁿ → ℝ) {p m r : ℕ} {L : ℝ} {y : Fin m → ℝⁿ}
    {ℓ : Fin m → ℝⁿ → ℝ} {Λ : ℕ → ℝ} (hℓ : IsLagrangeBasis n p y ℓ) (hy1 : ∀ j, ‖y j‖ ≤ 1)
    (hΛ : ∀ i j, ‖iteratedFDeriv ℝ i (ℓ j) 0‖ ≤ Λ i) (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) (hL0 : 0 ≤ L) (hr : 1 ≤ r) (hrp : r ≤ p) :
    FiniteDerivativeApproxScheme f 0 r (fun i => L * m / ((p + 1)! : ℝ) * Λ i) where
  est x h i := if i = 0 then iteratedFDeriv ℝ i f x else
    iteratedFDeriv ℝ i (fun v => ∑ j, f (x + interpRadius p r h • y j) *
      ℓ j ((interpRadius p r h)⁻¹ • (v - x))) x
  cost := m
  approx x h hh i hi := by
    obtain ⟨hi1, hir⟩ := Finset.mem_Icc.1 hi
    have hδ : 0 < interpRadius p r h :=
      epsMin_pos hr fun k hk => accuracyStep_pos p k (hh k hk)
    have hδh : interpRadius p r h ≤ accuracyStep p i (h i) := epsMin_le hi
    simp only [show i ≠ 0 by omega, ↓reduceIte]
    refine (hℓ.norm_iteratedFDeriv_sub_le_of_scaled hy1 (by omega) (hΛ i) hδ convex_univ
      (fun z _ => hf.contDiffAt) hL hL0 (mem_univ x) fun _ => mem_univ _).trans ?_
    have hm : 0 < m := by
      rw [hℓ.card_eq]
      exact Nat.choose_pos (by omega)
    have hΛ0 : 0 ≤ Λ i := (norm_nonneg _).trans (hΛ i ⟨0, hm⟩)
    have hpow : interpRadius p r h ^ (p - i + 1) ≤ h i := by
      rw [← accuracyStep_pow p i (hh i hi).le]
      exact pow_le_pow_left₀ hδ.le hδh _
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  exact_low x h i hi := by
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    simp

end Interpolation

/-- `|log t| ≤ 1/t` for `t ∈ (0, 1]`. -/
theorem abs_log_le_inv {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : |Real.log t| ≤ 1 / t := by
  rw [abs_of_nonpos (Real.log_nonpos ht.le ht1), ← Real.log_inv, one_div]
  have := Real.log_le_sub_one_of_pos (inv_pos.2 ht)
  linarith

/-- `a + b |log t| + c ≤ (a' + b + c)/t^m` for `t ∈ (0, 1]`, `m ≥ 1`, `b, c ≥ 0` and
`a ≤ a'/t^m`. -/
private theorem le_div_pow_of_log {a a' b c t : ℝ} {m : ℕ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hm : 1 ≤ m) (hb : 0 ≤ b) (hc : 0 ≤ c) (ha : a ≤ a' / t ^ m) :
    a + b * |Real.log t| + c ≤ (a' + b + c) / t ^ m := by
  have htm : 0 < t ^ m := pow_pos ht m
  have htm1 : t ^ m ≤ t := by
    calc t ^ m ≤ t ^ 1 := pow_le_pow_of_le_one ht.le ht1 hm
      _ = t := pow_one t
  have h1 : |Real.log t| ≤ 1 / t ^ m :=
    (abs_log_le_inv ht ht1).trans (one_div_le_one_div_of_le htm htm1)
  have h2 : c ≤ c / t ^ m := le_div_self hc htm (pow_le_one₀ ht.le ht1)
  rw [add_div, add_div]
  have := mul_le_mul_of_nonneg_left h1 hb
  rw [mul_one_div] at this
  linarith

section TR

variable {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : TRqIDAParams} {L : ℕ → ℝ} {x₀ : ℝⁿ}

/-- **Theorem 13.2.1, trust-region part** ([cartis2022evaluation], corrected): let f.D0qL and f.Bb
hold, `o ≤ q`, `S` a finite derivative-approximation scheme for `f` from oracles of degree `≤ o`
producing inexact derivatives up to degree `q`. There is a constant `C`
(independent of the tolerances) such that every TRqIDA run whose derivatives are those of the
scheme (`D_k = S.est x_k h_k`) reaches a first iterate that is an `(ε, δ)`-approximate `q`-th
order minimizer (`trTest`) after at most `C/ε_min^{q+1} = C max_j ε_j^{-(q+1)}` calls to the
oracles of degree `≤ o` (one per function value, `S.cost` per derivative estimate). The book
prints `O(min_j ε_j^{-(q+1)})`. -/
theorem theorem_13_2_1_i (hf : AssumptionD0qL f P.q L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow) {o : ℕ} (S : FiniteDerivativeApproxScheme f o P.q κg) :
    ∃ C, ∀ (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ)
      (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
      (acc : ℕ → Prop), algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc →
      (∀ k, D k = S.est (x k) (h k)) →
      ∃ kε, IsFirstHit (trTest f P ε x Δ) kε ∧
        (derivEvalCount (fun i => ¬ acc i) kε : ℝ) + S.cost *
          derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i)) kε ≤
        C / epsMin P.q ε ^ (P.q + 1) := by
  set κΔ := min 1 (P.γ₁ * ((1 - P.η₂) /
    (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg)))
  set A := trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow)
  set B := 1 / |Real.log P.γ₂|
  set Cc := |Real.log (P.ς * (κΔ / 2) / P.Δ₀)| / |Real.log P.γ₂| + 1
  set E := P.q * (P.q + 1) / |Real.log P.γh|
  set F := |Real.log (trKappaAcc P κΔ (lipMax L P.q + ordMax P.q κg * P.κh) (ordMax P.q κg) /
    P.κh)| / |Real.log P.γh| + 2 with hF_def
  refine ⟨(A + B + Cc) + S.cost * (A + E + F), fun ε x Δ h D dd jk s acc hrun _ => ?_⟩
  have hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ := by
    have := hf.one_le_lipMax; have := hrun.kappaMax_nonneg; have := P.κs_pos
    exact ⟨lt_min one_pos (mul_pos P.γ₁_pos (div_pos P.one_sub_η₂_pos (by positivity))),
      min_le_left _ _, min_le_right _ _⟩
  obtain ⟨kε, hk, -, -, h1, h2⟩ := theorem_13_1_8 hf hb hrun hκΔ
  refine ⟨kε, hk, ?_⟩
  have hε := hrun.epsMin_pos
  have hε1 := hrun.epsMin_le_one
  have hq : 1 ≤ P.q + 1 := by omega
  have hB : 0 ≤ B := by positivity
  have hC : 0 ≤ Cc := by positivity
  have hE : 0 ≤ E := by positivity
  have hF : 0 ≤ F := by positivity
  have h1' := h1.trans (le_div_pow_of_log hε hε1 hq hB hC le_rfl)
  have h2' := (h2.trans (le_of_eq (by rw [hF_def]; ring))).trans
    (le_div_pow_of_log hε hε1 hq hE hF (le_refl (A / epsMin P.q ε ^ (P.q + 1))))
  have hcost : (0 : ℝ) ≤ S.cost := Nat.cast_nonneg _
  calc (derivEvalCount (fun i => ¬ acc i) kε : ℝ) + S.cost *
        derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i)) kε
      ≤ (A + B + Cc) / epsMin P.q ε ^ (P.q + 1) +
          S.cost * ((A + E + F) / epsMin P.q ε ^ (P.q + 1)) :=
        add_le_add h1' (mul_le_mul_of_nonneg_left h2' hcost)
    _ = ((A + B + Cc) + S.cost * (A + E + F)) / epsMin P.q ε ^ (P.q + 1) := by ring

end TR

section AR

variable {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : ARqpIDAParams} {L : ℕ → ℝ} {x₀ : ℝⁿ}

/-- `min_j ε_j^{π_j} ≤ ε_min` for `ε ∈ (0, 1]^q` (the exponents `π_j ≥ 1`). -/
theorem epsMin_rpow_arPi_le {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) :
    epsMin P.q (fun j => ε j ^ arPi P.q P.p j) ≤ epsMin P.q ε := by
  obtain ⟨j, hj, he⟩ := exists_epsMin_eq (ε := ε) P.one_le_q
  rw [he]
  refine (epsMin_le hj).trans ?_
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hp := P.one_le_p
  have hπ : 1 ≤ arPi P.q P.p j := by
    unfold arPi arPiOf
    split_ifs
    · rw [le_div_iff₀ (by exact_mod_cast (show 0 < P.p - j + 1 by omega)), one_mul]
      have : P.p - j + 1 ≤ P.p + 1 := by omega
      exact_mod_cast this
    · rw [le_div_iff₀ (by exact_mod_cast (show 0 < P.p by omega)), one_mul]
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      nlinarith
  calc ε j ^ arPi P.q P.p j ≤ ε j ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (hε j hj).1 (hε j hj).2 hπ
    _ = ε j := Real.rpow_one _

/-- **Theorem 13.2.1, regularization part** ([cartis2022evaluation], corrected): let f.D0pL and
f.Bb hold, and `S` a finite derivative-approximation scheme for `f` from
oracles of degree `≤ o` producing inexact derivatives up to degree `p`. There is a constant `C`
(independent of the tolerances) such that every ARqpIDA run with the radii control
(13.1.69)–(13.1.70) whose derivatives are those of the scheme reaches a first iterate that is
approximately optimal (`arTest`) after at most `C / min_j ε_j^{π_j}` oracle calls, with
`π_j = (p+1)/(p-j+1)` if `q ≤ 2` and `π_j = j(p+1)/p` if `q > 2` (`arPi`), i.e.
`O(max_j ε_j^{-π_j})`. The book prints `min_j` for `max_j`. -/
theorem theorem_13_2_1_ii (hf : AssumptionD0pL f P.p L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow) {o : ℕ}
    (S : FiniteDerivativeApproxScheme f o P.p κg) :
    ∃ C, ∀ (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
      (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
      (acc : ℕ → Prop), algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc →
      (∀ i, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) →
      (∀ k, D k = S.est (x k) (h k)) →
      ∃ kε, IsFirstHit (arTest f P ε x) kε ∧
        (derivEvalCount (fun i => ¬ acc i) kε : ℝ) + S.cost *
          derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε ≤
        C / epsMin P.q (fun j => ε j ^ arPi P.q P.p j) := by
  set κΔm := P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (1 - P.θ)
    (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
      (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))
  set cT := 1 + |Real.log P.γ₁| / Real.log P.γ₂
  set A := (f x₀ - flow) / (P.η₁ * κΔm / 2)
  set Cc := Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
    |Real.log P.γ₁| / Real.log P.γ₂
  set E := P.p * (P.q + 1) / |Real.log P.γh|
  set F := |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
    (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
    (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| / |Real.log P.γh| + 3
  refine ⟨(cT * A + |Cc|) + S.cost * (A + E + F),
    fun ε x σ δ δ₁ δs h D dd jk s acc hrun hrc _ => ?_⟩
  set m := epsMin P.q (fun j => ε j ^ arPi P.q P.p j)
  have hm : 0 < m := Optimization.epsMin_pos P.one_le_q fun j hj =>
    Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _
  have hmε : m ≤ epsMin P.q ε := epsMin_rpow_arPi_le hrun.eps_mem
  have hε := hrun.epsMin_pos
  have hε1 := hrun.epsMin_le_one
  have hm1 : m ≤ 1 := hmε.trans hε1
  have hA := one_le_arConstA (hf.one_le le_rfl) hrun.kappaMax_nonneg (P := P) (L := L)
  have hLb := hrun.one_le_Lbar hf.normalized
  have hκpos : 0 < κΔm := by
    have hk0 : 0 < arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
        (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) :=
      lt_min (arKappaDelta1_pos (by linarith))
        (div_pos (sub_pos.2 P.θ_lt_one) (by positivity))
    have hC : 0 < arStepConst P.q P.p (1 - P.θ) (arConstA P L (ordMax P.p κg))
        (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) := by
      have := sub_pos.2 P.θ_lt_one
      unfold arStepConst arStepConstOf
      split_ifs <;> positivity
    have := P.σmin_pos
    positivity
  have hc : 0 < P.η₁ * κΔm / 2 * m := by have := P.η₁_pos; positivity
  obtain ⟨kε, hk, h1, h2⟩ := arqpIDA_complexity hf hb hrun hrc hc fun k hk hρ hnot =>
    (lemma_13_1_18 hf hrun (hrc k) hk hρ hnot).2
  refine ⟨kε, hk, ?_⟩
  have hdiv : (f x₀ - flow) / (P.η₁ * κΔm / 2 * m) = A / m := (div_div _ _ _).symm
  rw [hdiv] at h1 h2
  have hlog : |Real.log (epsMin P.q ε)| ≤ 1 / m :=
    (abs_log_le_inv hε hε1).trans (one_div_le_one_div_of_le hm hmε)
  have hcT : 0 ≤ cT := by have := P.log_γ₂_pos; positivity
  have hE : 0 ≤ E := by positivity
  have hF : 0 ≤ F := by positivity
  have hdivm : ∀ {c : ℝ}, 0 ≤ c → c ≤ c / m := fun hc => le_div_self hc hm hm1
  have h1' : (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤ (cT * A + |Cc|) / m := by
    calc _ ≤ cT * (A / m) + Cc := h1
      _ ≤ cT * (A / m) + |Cc| / m :=
          add_le_add le_rfl ((le_abs_self _).trans (hdivm (abs_nonneg _)))
      _ = (cT * A + |Cc|) / m := by ring
  have h2' : (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε :
      ℝ) ≤ (A + E + F) / m := by
    calc _ ≤ A / m + E * |Real.log (epsMin P.q ε)| + F := by
          have := h2; simp only [E, F] at this ⊢; linarith
      _ ≤ A / m + E * (1 / m) + F / m :=
          add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog hE)) (hdivm hF)
      _ = (A + E + F) / m := by ring
  have hcost : (0 : ℝ) ≤ S.cost := Nat.cast_nonneg _
  calc (derivEvalCount (fun i => ¬ acc i) kε : ℝ) + S.cost *
        derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε
      ≤ (cT * A + |Cc|) / m + S.cost * ((A + E + F) / m) :=
        add_le_add h1' (mul_le_mul_of_nonneg_left h2' hcost)
    _ = ((cT * A + |Cc|) + S.cost * (A + E + F)) / m := by ring

end AR

/-! ### Runs driven by a scheme -/

section Existence

/-- **TRqIDA runs driven by a scheme exist**: for every finite derivative-approximation scheme `S`
producing derivatives up to degree `q`, there is a TRqIDA run with `D_k = S.est x_k h_k`
(the hypothesis of `theorem_13_2_1_i`). -/
theorem exists_algorithm_13_1_1_of_scheme {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : TRqIDAParams}
    {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hϑ : epsMin P.q ε ≤ P.ϑ)
    (hκg : ∀ i ∈ Finset.Icc 1 P.q, 0 ≤ κg i) {o : ℕ} (S : FiniteDerivativeApproxScheme f o P.q κg)
    (x₀ : ℝⁿ) :
    ∃ (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
      (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ) (acc : ℕ → Prop),
      algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc ∧ ∀ k, D k = S.est (x k) (h k) :=
  exists_algorithm_13_1_1 hε hϑ hκg x₀ S.est S.approx

/-- **ARqpIDA runs driven by a scheme exist**: for every finite derivative-approximation scheme
`S` producing derivatives up to degree `p` and positive initial accuracies, there is an ARqpIDA
run with `D_k = S.est x_k h_k` and the radii control (the hypotheses of `theorem_13_2_1_ii`). -/
theorem exists_algorithm_13_1_2_of_scheme {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : ARqpIDAParams}
    {ε : ℕ → ℝ} {L : ℕ → ℝ} (hf : AssumptionD0pL f P.p L)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hεδ : ∀ j ∈ Finset.Icc 1 P.q, ε j ≤ P.δ₀ j)
    (hκg : ∀ i ∈ Finset.Icc 1 P.p, 0 ≤ κg i) (hh₀ : ∀ i ∈ Finset.Icc 1 P.p, 0 < P.h₀ i) {o : ℕ}
    (S : FiniteDerivativeApproxScheme f o P.p κg) (x₀ : ℝⁿ) :
    ∃ (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
      (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
      (acc : ℕ → Prop), algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc ∧
        (∀ k, D k = S.est (x k) (h k)) ∧
        ∀ k, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k :=
  exists_algorithm_13_1_2 S.est hf hε hεδ hκg hh₀ x₀ fun y h' hh =>
    S.approx y h' fun i hi => (hh i hi).1

/-- **TRqIDA with forward-difference gradients** (`q = 1`, function values only): runs exist with
`D_k = gradientJet (∇ f(x_k) estimated by forward differences with step h_{k,1})`, for `∇f`
`L`-Lipschitz (`κ_{∇,1} = √n L/2`). -/
theorem exists_algorithm_13_1_1_fdGradient {f : ℝⁿ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ}
    {L : ℝ} (hq : P.q = 1) (hf : ContDiff ℝ 1 f)
    (hL : ∀ y z, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖) (hL0 : 0 ≤ L)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hϑ : epsMin P.q ε ≤ P.ϑ) (x₀ : ℝⁿ) :
    ∃ (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
      (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ) (acc : ℕ → Prop),
      algorithm_13_1_1 f (fun _ => √n * L / 2) P ε x₀ x Δ h D dd jk s acc ∧
        ∀ k, D k = gradientJet (ftaylorSeries ℝ f (x k))
          (FiniteDifference.fdGradient f (h k 1) (x k)) :=
  exists_algorithm_13_1_1 hε hϑ (fun _ _ => by positivity) x₀
    (fdGradientScheme f hf hL).est fun y h' hh => by
      rw [hq]; exact (fdGradientScheme f hf hL).approx y h' (hq ▸ hh)

end Existence

end CartisGouldToint.Chapter13
