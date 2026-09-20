import Mathlib.LinearAlgebra.Vandermonde
import Numlib.Approximation.Chebyshev
import Numlib.Approximation.Interpolation
import Numlib.Approximation.NewtonForm
import Numlib.Approximation.RungePhenomenon

/-!
# Quarteroni–Sacco–Saleri §8.1: polynomial interpolation

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §8.1: Lagrange interpolation — existence and uniqueness (Theorem 8.1),
the Lagrange form and the nodal polynomial ((8.3)–(8.6)), the error formula (Theorem 8.2), the
interpolation matrix, the Lebesgue constant and the comparison with the best approximation
(Property 8.1), the growth of Lebesgue constants, Runge's counterexample (Example 8.1), and the
stability estimate of §8.1.3; with the cited Exercises 1–3.

Everything is Mathlib's `Lagrange.interpolate`, `Lagrange.basis` and `Lagrange.nodal`, the backbone
`Numlib/Approximation/Interpolation` (the error formula
`Lagrange.exists_sub_interpolate_eq_of_contDiffOn`, the interpolation operator
`Lagrange.interpolateCLM` with its norm `Lagrange.norm_interpolateCLM`) and the Lebesgue lemma
`norm_sub_apply_le_of_isIdempotentElem` of `Numlib/Analysis/Normed/Module/BestApprox`; Runge's
counterexample is `Numlib/Approximation/RungePhenomenon`.

## Main definitions

* `IsInterpMatrix X` — an interpolation matrix on `[a, b]` (§8.1.2): a doubly indexed family of
  points of `[a, b]` whose `(n + 1)`-st row `X n 0, …, X n n` consists of distinct points.
* `interpRow X n` — the interpolation operator `Π_n` at the nodes of the `(n + 1)`-st row.
* `lebesgueConstant X n` — the Lebesgue constant `Λ_n(X)` of (8.11), the maximum over `[a, b]` of
  the Lebesgue function `∑_j |l_j^{(n)}|`, stated as in §10.8.

## Main results

* `theorem_8_1`, `theorem_8_1_isUnisolvent` — existence and uniqueness of the interpolant, and its
  abstract form as a unisolvent interpolation problem over `𝒫_n`.
* `equation_8_3`, `equation_8_4`, `equation_8_5`, `equation_8_6`, with `exercise_8_1`,
  `exercise_8_2`, `exercise_8_2_det`, `exercise_8_3` — the characteristic polynomials, the Lagrange
  form, the barycentric-type form and the nodal polynomial.
* `theorem_8_2` — the interpolation error `f(x) - Π_n f(x) = f^{(n+1)}(ξ) ω_{n+1}(x)/(n+1)!`.
* `lebesgueConstant_eq_norm`, `property_8_1`, `property_8_1_bestApprox` — the Lebesgue constant is
  the operator norm of `Π_n`, and `E_{n,∞}(X) ≤ E_n^*(1 + Λ_n(X))`.
* `interpRow_sub_le_lebesgueConstant` — the stability estimate of §8.1.3.

* `example_8_1`, `example_8_1_one_le` — Runge's counterexample: at `x = 4.9` the equispaced
  interpolants of `1/(1 + x²)` on `[-5, 5]` do not converge, the error being `≥ 1` for every odd
  `n ≥ 401` (`Numlib/Approximation/RungePhenomenon`).

## Not formalized

The Erdős lower bound `Λ_n(X) > (2/π) log(n + 1) - C` (`erdos_lebesgueConstant`), Faber's theorem
(`faber`) and the equispaced asymptotics `Λ_n ≃ 2^{n+1}/(e n log n)`
(`lebesgueConstant_equispaced`) are stated in the plan and left open there; the book quotes all
three without proof.

## Conventions

Nodes are `x : Fin (n + 1) → ℝ`, injective (the book's "distinct"); the interpolant of data `y`
is `Lagrange.interpolate Finset.univ x y : ℝ[X]`, of a function `f` it is
`Lagrange.interpolate Finset.univ x (fun i => f (x i))`; `𝒫_n` on `[a, b]` is
`polyLE (Icc a b) n`; the interpolation operator on `C(Icc a b, ℝ)` is `Lagrange.interpolateCLM`,
whose nodes are points of the subtype `Icc a b`. The smallest interval `I_x` containing the nodes
and a point `t` is `Icc (min t (⨅ i, x i)) (max t (⨆ i, x i))`; Theorem 8.2's `f ∈ C^{n+1}(I_x)` is
read as `ContDiffOn` on an open set containing `I_x`.
-/

open Polynomial Set

namespace QuarteroniSaccoSaleri.Chapter08

variable {n : ℕ}

/-! ### Theorem 8.1 and the Lagrange form -/

/-- **Theorem 8.1.** Given `n + 1` distinct points `x₀, …, x_n` and `n + 1` corresponding values
`y₀, …, y_n`, there exists a unique polynomial `Π_n ∈ 𝒫_n` such that `Π_n(x_i) = y_i` for
`i = 0, …, n`. Existence is Mathlib's `Lagrange.interpolate`, uniqueness
`Lagrange.eq_interpolate_of_eval_eq`. -/
theorem theorem_8_1 {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (y : Fin (n + 1) → ℝ) :
    ∃! p : ℝ[X], p.degree ≤ n ∧ ∀ i, p.eval (x i) = y i := by
  have hcard : (Finset.univ : Finset (Fin (n + 1))).card = n + 1 := by simp
  refine ⟨Lagrange.interpolate Finset.univ x y, ⟨?_, fun i =>
    Lagrange.eval_interpolate_at_node y hx.injOn (Finset.mem_univ i)⟩, ?_⟩
  · have := Lagrange.degree_interpolate_le (s := Finset.univ) y hx.injOn
    rwa [hcard, Nat.add_sub_cancel] at this
  · rintro p ⟨hdeg, hval⟩
    refine Lagrange.eq_interpolate_of_eval_eq y hx.injOn ?_ fun i _ => hval i
    rw [hcard]
    exact hdeg.trans_lt (by exact_mod_cast Nat.lt_succ_self n)

/-- **Theorem 8.1** in the abstract form of the backbone: for distinct nodes in `[a, b]`, the point
evaluations at the nodes are unisolvent over `𝒫_n` — the interpolation problem of
`Numlib/Approximation/Unisolvent`, `Lagrange.isUnisolvent_polyLE`. -/
theorem theorem_8_1_isUnisolvent {a b : ℝ} {x : Fin (n + 1) → Icc a b}
    (hx : Function.Injective x) :
    Approximation.IsUnisolvent (polyLE (Icc a b) n) fun i => ContinuousMap.evalCLM ℝ (x i) :=
  Lagrange.isUnisolvent_polyLE hx

/-- **(8.3).** The characteristic polynomials `l_i(x) = ∏_{j ≠ i} (x - x_j)/(x_i - x_j)` — Mathlib's
`Lagrange.basis Finset.univ x i` — satisfy `l_i(x_j) = δ_ij`. -/
theorem equation_8_3 {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (i j : Fin (n + 1)) :
    (Lagrange.basis Finset.univ x i).eval (x j) = if i = j then 1 else 0 := by
  split_ifs with h
  · subst h
    exact Lagrange.eval_basis_self hx.injOn (Finset.mem_univ i)
  · exact Lagrange.eval_basis_of_ne h (Finset.mem_univ j)

/-- **(8.4), the Lagrange form** of the interpolating polynomial: `Π_n(x) = ∑_i y_i l_i(x)`. -/
theorem equation_8_4 (x y : Fin (n + 1) → ℝ) :
    Lagrange.interpolate Finset.univ x y = ∑ i, C (y i) * Lagrange.basis Finset.univ x i :=
  Lagrange.interpolate_apply _ _ _

/-- **Exercise 8.1.** The characteristic polynomials `l_i ∈ 𝒫_n` of (8.3) form a basis of `𝒫_n`,
here `Polynomial.degreeLT ℝ (n + 1)`: they are linearly independent, a vanishing combination being
evaluated at the nodes, and there are `n + 1 = dim 𝒫_n` of them. -/
theorem exercise_8_1 {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) :
    ∃ B : Module.Basis (Fin (n + 1)) ℝ (Polynomial.degreeLT ℝ (n + 1)),
      ∀ i, (B i : ℝ[X]) = Lagrange.basis Finset.univ x i := by
  have hcard : (Finset.univ : Finset (Fin (n + 1))).card = n + 1 := by simp
  have hmem : ∀ i, Lagrange.basis Finset.univ x i ∈ Polynomial.degreeLT ℝ (n + 1) := fun i => by
    rw [Polynomial.mem_degreeLT, Lagrange.degree_basis hx.injOn (Finset.mem_univ i), hcard,
      Nat.add_sub_cancel]
    exact_mod_cast Nat.lt_succ_self n
  set v : Fin (n + 1) → Polynomial.degreeLT ℝ (n + 1) := fun i =>
    ⟨Lagrange.basis Finset.univ x i, hmem i⟩ with hv
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have := congrArg (fun p : Polynomial.degreeLT ℝ (n + 1) => (p : ℝ[X]).eval (x j)) hc
    simp only [hv, Submodule.coe_sum, Submodule.coe_smul, Polynomial.eval_finsetSum,
      Polynomial.eval_smul, smul_eq_mul, equation_8_3 hx, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Submodule.coe_zero, Polynomial.eval_zero]
      at this
    exact this
  have hrank : Fintype.card (Fin (n + 1)) = Module.finrank ℝ (Polynomial.degreeLT ℝ (n + 1)) := by
    rw [Fintype.card_fin, LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv ℝ (n + 1)),
      Module.finrank_fin_fun]
  exact ⟨basisOfLinearIndependentOfCardEqFinrank hli hrank, fun i => by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]⟩

/-- **Exercise 8.2.** The Vandermonde matrix `X = [x_i^j]` of the nodes is nonsingular exactly when
the nodes are distinct: Mathlib's `Matrix.det_vandermonde_ne_zero_iff`. -/
theorem exercise_8_2 (x : Fin (n + 1) → ℝ) :
    (Matrix.vandermonde x).det ≠ 0 ↔ Function.Injective x :=
  Matrix.det_vandermonde_ne_zero_iff

/-- **Exercise 8.2, the hint.** `det X = ∏_{0 ≤ j < i ≤ n} (x_i - x_j)`: Mathlib's
`Matrix.det_vandermonde`. -/
theorem exercise_8_2_det (x : Fin (n + 1) → ℝ) :
    (Matrix.vandermonde x).det = ∏ j, ∏ i ∈ Finset.Ioi j, (x i - x j) :=
  Matrix.det_vandermonde x

/-- **(8.6).** The nodal polynomial `ω_{n+1}(x) = ∏_{i=0}^n (x - x_i)` — Mathlib's
`Lagrange.nodal Finset.univ x` — has that value at every `t`. -/
theorem equation_8_6 (x : Fin (n + 1) → ℝ) (t : ℝ) :
    (Lagrange.nodal Finset.univ x).eval t = ∏ i, (t - x i) :=
  Lagrange.eval_nodal

/-- **Exercise 8.3.** `ω'_{n+1}(x_i) = ∏_{j ≠ i} (x_i - x_j)`. -/
theorem exercise_8_3 (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (derivative (Lagrange.nodal Finset.univ x)).eval (x i)
      = ∏ j ∈ Finset.univ.erase i, (x i - x j) := by
  rw [Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i), Lagrange.eval_nodal]

/-- **(8.5).** For `t` distinct from every node,
`Π_n(t) = ∑_i ω_{n+1}(t) / ((t - x_i) ω'_{n+1}(x_i)) · y_i`: Mathlib's first barycentric form
`Lagrange.eval_interpolate_not_at_node`. -/
theorem equation_8_5 (x y : Fin (n + 1) → ℝ) {t : ℝ} (ht : ∀ i, t ≠ x i) :
    (Lagrange.interpolate Finset.univ x y).eval t
      = ∑ i, (Lagrange.nodal Finset.univ x).eval t
          / ((t - x i) * (derivative (Lagrange.nodal Finset.univ x)).eval (x i)) * y i := by
  rw [Lagrange.eval_interpolate_not_at_node y fun i _ => ht i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ i)]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-! ### Theorem 8.2: the interpolation error -/

/-- **Theorem 8.2.** Let `x₀, …, x_n` be `n + 1` distinct nodes and `t` a point; let `I_t` be the
smallest interval containing the nodes and `t`, and assume `f ∈ C^{n+1}` on an open set containing
`I_t`. Then the interpolation error at `t` is

`E_n(t) = f(t) - Π_n f(t) = f^{(n+1)}(ξ)/(n+1)! · ω_{n+1}(t)`

for some `ξ ∈ I_t`. The backbone's `Lagrange.exists_sub_interpolate_eq_of_contDiffOn` when `I_t`
has nonempty interior; when `I_t` is a single point, `t` is the node `x₀` and both sides vanish. -/
theorem theorem_8_2 {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (t : ℝ) {f : ℝ → ℝ}
    {U : Set ℝ} (hU : IsOpen U) (hUsub : Icc (min t (⨅ i, x i)) (max t (⨆ i, x i)) ⊆ U)
    (hf : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f U) :
    ∃ ξ ∈ Icc (min t (⨅ i, x i)) (max t (⨆ i, x i)),
      f t - (Lagrange.interpolate Finset.univ x fun i => f (x i)).eval t
        = iteratedDeriv (n + 1) f ξ / (n + 1).factorial * ∏ i, (t - x i) := by
  set a := min t (⨅ i, x i) with ha
  set b := max t (⨆ i, x i) with hb
  have hxmem : ∀ i, x i ∈ Icc a b := fun i =>
    ⟨(min_le_right _ _).trans (ciInf_le (Set.finite_range x).bddBelow i),
      (le_ciSup (Set.finite_range x).bddAbove i).trans (le_max_right _ _)⟩
  have htmem : t ∈ Icc a b := ⟨min_le_left _ _, le_max_left _ _⟩
  rcases lt_or_ge a b with hab | hab
  · obtain ⟨ξ, hξ, h⟩ :=
      Lagrange.exists_sub_interpolate_eq_of_contDiffOn hab hU hUsub hf hx hxmem htmem
    exact ⟨ξ, Ioo_subset_Icc_self hξ, h⟩
  · -- the degenerate case: `t` is the node `x 0`
    have ht0 : t = x 0 := by
      have h1 := hxmem 0
      have h2 := htmem
      rw [mem_Icc] at h1 h2
      linarith
    refine ⟨t, htmem, ?_⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ 0) (by rw [ht0, sub_self]), mul_zero, ht0,
      Lagrange.eval_interpolate_at_node _ hx.injOn (Finset.mem_univ 0), sub_self]

/-! ### The interpolation matrix, the Lebesgue constant and Property 8.1 -/

variable {a b : ℝ}

/-- **The interpolation matrix on `[a, b]`** (§8.1.2): a lower triangular matrix `X` of infinite
size whose entries are points of `[a, b]`, such that on each row the entries are all distinct. The
`(n + 1)`-st row is `X n 0, …, X n n`; the entries beyond the diagonal are unused. -/
def IsInterpMatrix (X : ℕ → ℕ → Icc a b) : Prop :=
  ∀ n, Function.Injective fun j : Fin (n + 1) => X n j

/-- **`Π_n`** (§8.1.2): the interpolation operator on `C([a, b], ℝ)` at the nodes of the
`(n + 1)`-st row of the interpolation matrix `X`. -/
noncomputable def interpRow (X : ℕ → ℕ → Icc a b) (n : ℕ) : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ) :=
  Lagrange.interpolateCLM fun j : Fin (n + 1) => X n j

/-- **(8.11), the Lebesgue constant** `Λ_n(X) = ‖∑_{j=0}^n |l_j^{(n)}|‖_∞` of the interpolation
matrix `X`, with `l_j^{(n)}` the characteristic polynomials of the `(n + 1)`-st row: the maximum
over `[a, b]` of the Lebesgue function, written as the supremum of its range. -/
noncomputable def lebesgueConstant (X : ℕ → ℕ → Icc a b) (n : ℕ) : ℝ :=
  sSup (Set.range fun t : Icc a b =>
    ∑ j, |Lagrange.basisCM (fun j : Fin (n + 1) => X n j) j t|)

/-- The Lebesgue constant is the operator norm of `Π_n` on `C([a, b], ℝ)`:
`Lagrange.norm_interpolateCLM`. -/
theorem lebesgueConstant_eq_norm {X : ℕ → ℕ → Icc a b} (hX : IsInterpMatrix X) (n : ℕ) :
    lebesgueConstant X n = ‖interpRow X n‖ :=
  have : Nonempty (Icc a b) := ⟨X 0 0⟩
  (Lagrange.norm_interpolateCLM (hX n)).symm

/-- The Lebesgue function is bounded by the Lebesgue constant at every point. -/
theorem sum_abs_basisCM_le_lebesgueConstant {X : ℕ → ℕ → Icc a b} (hX : IsInterpMatrix X)
    (n : ℕ) (t : Icc a b) :
    ∑ j, |Lagrange.basisCM (fun j : Fin (n + 1) => X n j) j t| ≤ lebesgueConstant X n :=
  have : Nonempty (Icc a b) := ⟨X 0 0⟩
  (lebesgueConstant_eq_norm hX n).symm ▸ (Lagrange.isGreatest_norm_interpolateCLM (hX n)).2 ⟨t, rfl⟩

/-- **Property 8.1.** Let `f ∈ C⁰([a, b])` and `X` be an interpolation matrix on `[a, b]`. Then

`E_{n,∞}(X) ≤ E_n^* (1 + Λ_n(X))`, `n = 0, 1, …`,

where `E_{n,∞}(X) = ‖f - Π_n f‖_∞` is the interpolation error (8.9) and
`E_n^* = ‖f - p_n^*‖_∞ = inf_{q ∈ 𝒫_n} ‖f - q‖_∞` the best approximation error. This is the
Lebesgue lemma `norm_sub_apply_le_of_isIdempotentElem` for the projection `Π_n`, whose range is
`𝒫_n` and whose norm is `Λ_n(X)`. -/
theorem property_8_1 {X : ℕ → ℕ → Icc a b} (hX : IsInterpMatrix X) (f : C(Icc a b, ℝ)) (n : ℕ) :
    ‖f - interpRow X n f‖
      ≤ (1 + lebesgueConstant X n) * Metric.infDist f (polyLE (Icc a b) n : Set C(Icc a b, ℝ)) := by
  have h := norm_sub_apply_le_of_isIdempotentElem (interpRow X n)
    (Lagrange.isIdempotentElem_interpolateCLM (hX n)) f
  rw [lebesgueConstant_eq_norm hX n]
  rwa [interpRow, Lagrange.range_interpolateCLM (hX n)] at h

/-- **Property 8.1**, with the best approximation polynomial: if `p_n^* ∈ 𝒫_n` is the polynomial of
best approximation of `f` (which exists and is unique for `a < b`,
`existsUnique_isBestApprox_polyLE`), then `‖f - Π_n f‖_∞ ≤ (1 + Λ_n(X)) ‖f - p_n^*‖_∞`. -/
theorem property_8_1_bestApprox {X : ℕ → ℕ → Icc a b} (hX : IsInterpMatrix X)
    {f p : C(Icc a b, ℝ)} (hp : IsBestApprox (polyLE (Icc a b) n : Set C(Icc a b, ℝ)) f p) :
    ‖f - interpRow X n f‖ ≤ (1 + lebesgueConstant X n) * ‖f - p‖ := by
  rw [hp.norm_sub_eq_infDist]
  exact property_8_1 hX f n

/-! ### §8.1.3: stability -/

/-- **The stability estimate of §8.1.3.** For a perturbation `f̃` of the data `f`,

`‖Π_n f - Π_n f̃‖_∞ ≤ Λ_n(X) max_{i=0,…,n} |f(x_i) - f̃(x_i)|`:

small changes of the data give small changes of the interpolating polynomial only if the Lebesgue
constant is small, which "plays the role of the condition number for the interpolation problem".
The maximum over the nodes is written as a supremum over `Fin (n + 1)`. -/
theorem interpRow_sub_le_lebesgueConstant {X : ℕ → ℕ → Icc a b} (hX : IsInterpMatrix X) (n : ℕ)
    (f g : C(Icc a b, ℝ)) :
    ‖interpRow X n f - interpRow X n g‖
      ≤ lebesgueConstant X n * ⨆ i : Fin (n + 1), |f (X n i) - g (X n i)| := by
  set M : ℝ := ⨆ i : Fin (n + 1), |f (X n i) - g (X n i)| with hM
  have hM0 : 0 ≤ M := Real.iSup_nonneg fun i => abs_nonneg _
  have hMi : ∀ i : Fin (n + 1), |f (X n i) - g (X n i)| ≤ M := fun i =>
    le_ciSup (f := fun i : Fin (n + 1) => |f (X n i) - g (X n i)|) (Set.finite_range _).bddAbove i
  have hΛ0 : 0 ≤ lebesgueConstant X n :=
    Real.sSup_nonneg fun y ⟨t, ht⟩ => ht ▸ Finset.sum_nonneg fun j _ => abs_nonneg _
  rw [← map_sub, ContinuousMap.norm_le _ (mul_nonneg hΛ0 hM0)]
  intro t
  rw [interpRow, Lagrange.interpolateCLM_apply, Real.norm_eq_abs]
  calc |∑ i, (f - g) ((fun j : Fin (n + 1) => X n j) i)
          * Lagrange.basisCM (fun j : Fin (n + 1) => X n j) i t|
      ≤ ∑ i, |(f - g) ((fun j : Fin (n + 1) => X n j) i)|
          * |Lagrange.basisCM (fun j : Fin (n + 1) => X n j) i t| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun i _ => abs_mul _ _
    _ ≤ ∑ i, M * |Lagrange.basisCM (fun j : Fin (n + 1) => X n j) i t| := by
        gcongr with i
        exact hMi i
    _ = M * ∑ i, |Lagrange.basisCM (fun j : Fin (n + 1) => X n j) i t| := by
        rw [Finset.mul_sum]
    _ ≤ M * lebesgueConstant X n := by
        gcongr
        exact sum_abs_basisCM_le_lebesgueConstant hX n t
    _ = lebesgueConstant X n * M := mul_comm _ _

/-! ### Example 8.1: Runge's counterexample -/

/-- **Example 8.1, the equally spaced nodes** `x_j^{(n)} = -5 + 10j/n`, `j = 0, …, n`, on
`[-5, 5]`. -/
noncomputable def example_8_1_nodes (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  -5 + 10 * (j : ℝ) / n

/-- **Example 8.1, a quantitative form.** For the function `f(x) = 1/(1 + x²)` of (8.12) and the
equally spaced nodes on `[-5, 5]`, the interpolation error at `x = 4.9` is at least `1` for every
odd `n ≥ 401`: `Runge.one_le_abs_sub_interpolate`. -/
theorem example_8_1_one_le {n : ℕ} (hn : Odd n) (hn400 : 400 ≤ n) :
    1 ≤ |1 / (1 + (49 / 10 : ℝ) ^ 2)
      - (Lagrange.interpolate Finset.univ (example_8_1_nodes n)
          fun j => 1 / (1 + (example_8_1_nodes n j) ^ 2)).eval (49 / 10)| :=
  Runge.one_le_abs_sub_interpolate hn hn400

/-- **Example 8.1 (Runge's counterexample).** Approximating `f(x) = 1/(1 + x²)`, `-5 ≤ x ≤ 5`
(8.12), by Lagrange interpolation on equally spaced nodes, "some points `x` exist within the
interpolation interval such that `lim_{n→∞} |f(x) - Π_n f(x)| ≠ 0`": at `x = 4.9` the sequence
`Π_n f(x)` does not converge to `f(x)`, because along the odd `n` the error stays `≥ 1`
(`example_8_1_one_le`). The backbone's `Runge.not_tendsto_interpolate`: the error is
`ω_{n+1}(x) f[x_0, …, x_n, x]` with the divided difference computed exactly through the partial
fraction `1/(1 + s²) = Re (i/(i - s))`, and the products are estimated by Riemann sums of
logarithms. The book's threshold `|x| > 3.63…` is not part of the statement. -/
theorem example_8_1 :
    ∃ t ∈ Icc (-5 : ℝ) 5, ¬ Filter.Tendsto
      (fun n => (Lagrange.interpolate Finset.univ (example_8_1_nodes n)
        fun j => 1 / (1 + (example_8_1_nodes n j) ^ 2)).eval t)
      Filter.atTop (nhds (1 / (1 + t ^ 2))) :=
  ⟨49 / 10, by norm_num, Runge.not_tendsto_interpolate⟩

end QuarteroniSaccoSaleri.Chapter08
