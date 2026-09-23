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
stability estimate of §8.1.3 together with a lower bound on the equispaced Lebesgue constants;
with the cited Exercises 1–3.

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
* `equispacedMatrix hab` — the equispaced interpolation matrix `x_j^{(n)} = a + j (b - a)/n` of
  §8.1.3, with `coe_equispacedMatrix` and `isInterpMatrix_equispacedMatrix`.

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
* `lebesgueConstant_equispaced_lower` — §8.1.3, the Schönhage lower bound
  `Λ_n ≥ 2^n/(8 n²) = 2^{n-3}/n²` for the equispaced nodes: the one-sided half of the asymptotics
  `Λ_n ≃ 2^{n+1}/(e n log n)` that the book quotes from Turetskii without proof.

* `example_8_1`, `example_8_1_one_le` — Runge's counterexample: at `x = 4.9` the equispaced
  interpolants of `1/(1 + x²)` on `[-5, 5]` do not converge, the error being `≥ 1` for every odd
  `n ≥ 401` (`Numlib/Approximation/RungePhenomenon`).

## Not formalized here

Three results of §8.1.2–8.1.3, all quoted by the book without proof. They form one cluster: the
first blocks the second, and the third is a sharpening of a fact about one particular scheme —
the one-sided half of which is proved here, as `lebesgueConstant_equispaced_lower`.

* **§8.1.2, Erdős's lower bound on Lebesgue constants.** For every interpolation matrix `X` on
  `[a, b]` there is a constant `C > 0` with `Λ_n(X) > (2/π) log(n + 1) − C` for all `n`; in
  particular no choice of nodes keeps the Lebesgue constants bounded, and the Chebyshev nodes,
  whose `Λ_n` grows like `(2/π) log n`, are optimal up to an additive constant. This is Erdős,
  *Problems and results on the theory of interpolation II*, Acta Math. Acad. Sci. Hungar. 12
  (1961) — several pages of hard analysis on the Lebesgue function. It is the blocker of the
  whole cluster.

  Nothing in the library helps. Every bound on a Lagrange interpolation operator in `Numlib/` is
  an **upper** one — `Lagrange.norm_interpolateCLM`, `Lagrange.norm_interpolateCLM_chebyshev_le`
  and the logarithmic estimate `SineSum.sum_term_le` of
  `Numlib/Analysis/SpecialFunctions/SineSum` that the Chebyshev bound runs on — and every step of
  those proofs is an upper estimate, so none of them can be turned around. The one lower bound in
  the corpus, `Runge.one_le_abs_sub_interpolate` of `Numlib/Approximation/RungePhenomenon`, is a
  bound on one *error* at one point for one node scheme, not on a Lebesgue constant. The
  backbone's `PeriodicCont.log_le_lebesgueConstant` is the *trigonometric* Lebesgue constant,
  whose proof is an explicit Dirichlet-kernel integral with no algebraic analogue. Estimate: a
  week, for Erdős's argument itself or for Bernstein's weaker `Λ_n ≥ c log n`.

* **§8.1.2, Faber's theorem.** For every interpolation matrix `X` on `[a, b]` (`a < b`) there is
  an `f ∈ C([a, b])` whose interpolants `Π_n f` do not converge uniformly to `f`: no node scheme
  works for every continuous function. The dependency structure here is worth stating exactly.
  Faber's theorem is **five lines** from what is already proved — `lebesgueConstant_eq_norm`
  above identifies `Λ_n(X)` with `‖Π_n‖`, and
  `ContinuousLinearMap.exists_not_tendsto_of_not_bddAbove` of
  `Numlib/Analysis/Normed/Operator/BanachSteinhaus`, applied to `Π_n` with `L` the identity of
  `C(Icc a b, ℝ)`, turns an unbounded family of operator norms into a function on which the
  family diverges. So Faber is blocked on
  `¬ BddAbove (Set.range (Λ_· (X)))` and on nothing else, that is, on Erdős's bound (or
  Bernstein's weaker one) alone. It is *not* blocked on any missing machinery.

  Note also what does **not** give it: Runge's counterexample, proved above as `example_8_1`, is
  one node scheme (equispaced on `[−5, 5]`) and one explicit function (`1/(1 + x²)`). Faber's
  statement quantifies over all interpolation matrices, so the Runge example is not a special
  case of it in any usable direction and cannot be promoted.

* **§8.1.3, the equispaced asymptotics.** For the equispaced matrix `X n j = a + j (b − a)/n`,
  `Λ_n(X) ≃ 2^{n+1}/(e n log n)` — precisely, `Λ_n(X) · e n log n / 2^{n+1} → 1`. This is
  Turetskii's theorem (1940; Natanson, *Constructive Function Theory*), and the asymptotic
  equivalence needs the precise evaluation of the Lebesgue function near the ends of the
  interval; a few pages of Natanson, not bounded work.

  The one-sided half is proved here: `lebesgueConstant_equispaced_lower` is Schönhage's
  `Λ_n ≥ 2^{n−3}/n²`, obtained by evaluating the Lebesgue function at the midpoint of the first
  panel, where the node spacing cancels and the basis products telescope into ratios of
  factorials. It is enough to show that equispaced interpolation is unstable, and it is the only
  lower bound on an algebraic Lebesgue constant in the corpus. But it bounds a *single*
  interpolation matrix, so it refutes nothing about Erdős's theorem or Faber's theorem as those
  are stated — both quantify over *all* matrices — and the book states neither it nor the
  exponent `2^{n−3}`; only the two-sided asymptotics are quoted, and those remain open.

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

/-! ### §8.1.3: a lower bound for the equispaced Lebesgue constants -/

section Equispaced

open Finset
open scoped Nat

/-- `∏_{j<m} (m − j) = m !`, over `ℝ`. -/
private theorem prod_range_sub_cast (m : ℕ) : ∏ j ∈ range m, ((m : ℝ) - j) = (m ! : ℝ) := by
  have h : ∀ j ∈ range m, ((m : ℝ) - (j : ℝ)) = ((m - j : ℕ) : ℝ) := fun j hj => by
    rw [Nat.cast_sub (le_of_lt (mem_range.mp hj))]
  rw [Finset.prod_congr rfl h, ← Nat.cast_prod, ← Nat.descFactorial_eq_prod_range,
    Nat.descFactorial_self]

/-- `∏_{i<k} (i + 1) = k !`, over `ℝ`. -/
private theorem prod_range_add_one_cast (k : ℕ) : ∏ i ∈ range k, ((i : ℝ) + 1) = (k ! : ℝ) := by
  rw [← Finset.prod_range_add_one_eq_factorial k, Nat.cast_prod]
  exact Finset.prod_congr rfl fun i _ => by push_cast; ring

/-- `∏_{m < j ≤ n} (j − m) = (n − m)!`, over `ℝ`. -/
private theorem prod_Ico_sub_cast {m n : ℕ} :
    ∏ j ∈ Ico (m + 1) (n + 1), ((j : ℝ) - m) = ((n - m)! : ℝ) := by
  rw [Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_add_right]
  rw [← prod_range_add_one_cast (n - m)]
  exact Finset.prod_congr rfl fun i _ => by push_cast; ring

/-- The product of the distances from `m` to the other integers `0, …, n`, with the vanishing
factor at `k = m` replaced by `1`: it is `m ! (n − m)!`. -/
private theorem prod_range_ite_abs_sub {m n : ℕ} (hmn : m ≤ n) :
    ∏ k ∈ range (n + 1), (if k = m then (1 : ℝ) else |(m : ℝ) - (k : ℝ)|)
      = (m ! : ℝ) * ((n - m)! : ℝ) := by
  rw [Finset.range_eq_Ico,
    ← Finset.prod_Ico_consecutive _ (Nat.zero_le m) (Nat.le_succ_of_le hmn),
    ← Finset.prod_Ico_consecutive _ (Nat.le_succ m) (Nat.succ_le_succ hmn)]
  have h1 : ∏ k ∈ Ico 0 m, (if k = m then (1 : ℝ) else |(m : ℝ) - (k : ℝ)|) = (m ! : ℝ) := by
    rw [← Finset.range_eq_Ico, ← prod_range_sub_cast m]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : k < m := mem_range.mp hk
    have hkm : (k : ℝ) < (m : ℝ) := by exact_mod_cast hk'
    rw [ite_eq_right (Nat.ne_of_lt hk')]
    exact abs_of_nonneg (by linarith)
  have h2 : ∏ k ∈ Ico m (m + 1), (if k = m then (1 : ℝ) else |(m : ℝ) - (k : ℝ)|) = 1 := by
    rw [Finset.prod_Ico_succ_top (le_refl m), Finset.Ico_self, Finset.prod_empty, one_mul]
    simp
  have h3 : ∏ k ∈ Ico (m + 1) (n + 1), (if k = m then (1 : ℝ) else |(m : ℝ) - (k : ℝ)|)
      = ((n - m)! : ℝ) := by
    rw [← prod_Ico_sub_cast (m := m) (n := n)]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : m + 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkm : (m : ℝ) < (k : ℝ) := by
      have h : ((m : ℝ) + 1) ≤ (k : ℝ) := by exact_mod_cast hk'
      linarith
    rw [ite_eq_right (by omega : k ≠ m), abs_sub_comm]
    exact abs_of_nonneg (by linarith)
  rw [h1, h2, h3, one_mul]

/-- The denominator of the `i`-th characteristic polynomial at equispaced nodes, with the node
spacing scaled away: `∏_{j ≠ i} |i − j| = i ! (n − i)!`. -/
private theorem prod_erase_abs_sub (n : ℕ) (i : Fin (n + 1)) :
    ∏ j ∈ (univ : Finset (Fin (n + 1))).erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|
      = ((i : ℕ)! : ℝ) * (((n - (i : ℕ))! : ℝ)) := by
  have hmn : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
  have hstep : ∏ j ∈ (univ : Finset (Fin (n + 1))).erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|
      = ∏ j ∈ (univ : Finset (Fin (n + 1))),
          (if (j : ℕ) = (i : ℕ) then (1 : ℝ) else |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|) := by
    rw [← Finset.prod_erase (univ : Finset (Fin (n + 1)))
      (f := fun j : Fin (n + 1) =>
        if (j : ℕ) = (i : ℕ) then (1 : ℝ) else |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)
      (a := i) (by simp)]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hne : (j : ℕ) ≠ (i : ℕ) := fun hc => (Finset.mem_erase.mp hj).1 (Fin.ext hc)
    rw [ite_eq_right hne]
  rw [hstep, Fin.prod_univ_eq_prod_range
    (fun k => if k = (i : ℕ) then (1 : ℝ) else |((i : ℕ) : ℝ) - (k : ℝ)|) (n + 1),
    prod_range_ite_abs_sub hmn]

/-- The numerator of the Lebesgue function at the midpoint of the first panel, before the node
`i` is removed: `∏_{j=0}^{n} |1/2 − j| = (2n)! / (2^{2n+1} n !)`. -/
private theorem prod_range_abs_half (n : ℕ) :
    ∏ j ∈ range (n + 1), |1 / 2 - (j : ℝ)| = ((2 * n)! : ℝ) / (2 ^ (2 * n + 1) * (n ! : ℝ)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hfn : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
    have habs : |1 / 2 - ((n + 1 : ℕ) : ℝ)| = (n : ℝ) + 1 / 2 := by
      push_cast
      rw [abs_of_nonpos (by linarith)]
      ring
    have hfac2 : (((2 * (n + 1))! : ℕ) : ℝ)
        = (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1) * (((2 * n)! : ℕ) : ℝ) := by
      have h : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [h, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have hfac1 : (((n + 1)! : ℕ) : ℝ) = ((n : ℝ) + 1) * (n ! : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [Finset.prod_range_succ, ih, habs, hfac2, hfac1]
    have hmul : 2 * (n + 1) + 1 = 2 * n + 1 + 2 := by ring
    rw [hmul, pow_add]
    field_simp
    ring

/-- `∑_{i=0}^{n} 1/(i ! (n − i)!) = 2^n / n !`, the binomial theorem in the form the Lebesgue
function needs. -/
private theorem sum_inv_factorial_mul (n : ℕ) :
    ∑ i ∈ range (n + 1), 1 / ((i ! : ℝ) * ((n - i)! : ℝ)) = 2 ^ n / (n ! : ℝ) := by
  have hfn : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
  have key : ∀ i ∈ range (n + 1),
      1 / ((i ! : ℝ) * ((n - i)! : ℝ)) = (n.choose i : ℝ) / (n ! : ℝ) := by
    intro i hi
    have hle : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have h : ((n.choose i : ℝ)) * (i ! : ℝ) * ((n - i)! : ℝ) = (n ! : ℝ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ))
        (Nat.choose_mul_factorial_mul_factorial hle)
    have hfi : (0 : ℝ) < (i ! : ℝ) := by exact_mod_cast i.factorial_pos
    have hfni : (0 : ℝ) < ((n - i)! : ℝ) := by exact_mod_cast (n - i).factorial_pos
    rw [div_eq_div_iff (by positivity) (ne_of_gt hfn)]
    linarith [h]
  rw [Finset.sum_congr rfl key, ← Finset.sum_div, ← Nat.cast_sum, Nat.sum_range_choose]
  norm_num

/-- Every factor `|1/2 − k|` of the Lebesgue function at the midpoint of the first panel is at
least `1/2`; in particular it is positive. -/
private theorem half_le_abs_half_sub (k : ℕ) : (1 : ℝ) / 2 ≤ |1 / 2 - (k : ℝ)| := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num
  · have h : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- The largest factor `|1/2 − k|`, `k ≤ n`, is the one at `k = n`: it is `(2n − 1)/2`. -/
private theorem abs_half_sub_le {k n : ℕ} (hk : k ≤ n) (hn : 1 ≤ n) :
    |1 / 2 - (k : ℝ)| ≤ (2 * (n : ℝ) - 1) / 2 := by
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [abs_le]
  constructor <;> linarith

/-- The arithmetic of the Schönhage bound: the value `2 (2n)! 2^n / ((2n − 1) 2^{2n+1} (n !)²)`
that the Lebesgue function reaches at the midpoint of the first panel is
`C(2n, n) 2^n / (4^n (2n − 1))`, and `C(2n, n) ≥ 4^n/(2n)`
(`Nat.four_pow_le_two_mul_self_mul_centralBinom`) makes it at least `2^n/(8n²)`. -/
private theorem two_pow_div_le_of_centralBinom {n : ℕ} (hn : 1 ≤ n) :
    (2 : ℝ) ^ n / (8 * (n : ℝ) ^ 2)
      ≤ 2 * (((2 * n)! : ℝ) / (2 ^ (2 * n + 1) * (n ! : ℝ))) / (2 * (n : ℝ) - 1)
          * ((2 : ℝ) ^ n / (n ! : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hfn : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
  have hcb : ((Nat.centralBinom n : ℕ) : ℝ) * (n ! : ℝ) * (n ! : ℝ) = (((2 * n)! : ℕ) : ℝ) := by
    have hle : n ≤ 2 * n := Nat.le_mul_of_pos_left n (by norm_num)
    have h := Nat.choose_mul_factorial_mul_factorial hle
    have h2 : 2 * n - n = n := by omega
    rw [h2] at h
    rw [Nat.centralBinom_eq_two_mul_choose]
    exact_mod_cast h
  have hcb2 : (4 : ℝ) ^ n ≤ 2 * (n : ℝ) * ((Nat.centralBinom n : ℕ) : ℝ) := by
    have h := Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
    have h' : ((4 ^ n : ℕ) : ℝ) ≤ ((2 * n * Nat.centralBinom n : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hpow : (2 : ℝ) ^ (2 * n + 1) = 2 * 4 ^ n := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  have hc0 : (0 : ℝ) ≤ ((Nat.centralBinom n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have h2p : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have h2n1 : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have key : 2 * (((2 * n)! : ℝ) / (2 ^ (2 * n + 1) * (n ! : ℝ))) / (2 * (n : ℝ) - 1)
      * ((2 : ℝ) ^ n / (n ! : ℝ))
      = ((Nat.centralBinom n : ℕ) : ℝ) * 2 ^ n / (4 ^ n * (2 * (n : ℝ) - 1)) := by
    rw [hpow, ← hcb]
    field_simp
  have h8n : (0 : ℝ) < 8 * (n : ℝ) ^ 2 := by nlinarith
  rw [key, div_le_div_iff₀ h8n (mul_pos h4 h2n1)]
  have e1 : (4 : ℝ) ^ n * (2 * (n : ℝ) - 1)
      ≤ (2 * (n : ℝ) * ((Nat.centralBinom n : ℕ) : ℝ)) * (2 * (n : ℝ) - 1) :=
    mul_le_mul_of_nonneg_right hcb2 h2n1.le
  have e2 : (2 * (n : ℝ) * ((Nat.centralBinom n : ℕ) : ℝ)) * (2 * (n : ℝ) - 1)
      ≤ ((Nat.centralBinom n : ℕ) : ℝ) * (8 * (n : ℝ) ^ 2) := by nlinarith [hc0, hn0]
  nlinarith [e1, e2, h2p]

/-- **§8.1.3, the equispaced interpolation matrix** on `[a, b]`: the `(n + 1)`-st row is the
equally spaced nodes `x_j^{(n)} = a + j (b − a)/n`, `j = 0, …, n`, of Runge's example and of the
asymptotics `Λ_n ≃ 2^{n+1}/(e n log n)`. Entries with `j > n` are unused and are clamped into
`[a, b]` by `Set.projIcc`. -/
noncomputable def equispacedMatrix (hab : a < b) (n j : ℕ) : Icc a b :=
  projIcc a b hab.le (a + j * (b - a) / n)

/-- The nodes actually used by the `(n + 1)`-st row of `equispacedMatrix` are the equally spaced
points `a + j (b − a)/n`: the clamping of the definition is inert for `j ≤ n`. -/
theorem coe_equispacedMatrix (hab : a < b) {n j : ℕ} (hj : j ≤ n) :
    ((equispacedMatrix hab n j : Icc a b) : ℝ) = a + j * (b - a) / n := by
  have hmem : a + (j : ℝ) * (b - a) / n ∈ Icc a b := by
    rw [Set.mem_Icc]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hj0 : j = 0 := Nat.le_zero.mp hj
      subst hj0
      norm_num
      exact hab.le
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj
      have hba : (0 : ℝ) < b - a := by linarith
      have h1 : (0 : ℝ) ≤ (j : ℝ) * (b - a) / n := by positivity
      have h2 : (j : ℝ) * (b - a) / n ≤ b - a := by
        rw [div_le_iff₀ hn0]
        nlinarith
      exact ⟨by linarith, by linarith⟩
  rw [equispacedMatrix, Set.projIcc_of_mem hab.le hmem]

/-- The equally spaced points form an interpolation matrix: on each row the nodes are distinct. -/
theorem isInterpMatrix_equispacedMatrix (hab : a < b) :
    IsInterpMatrix (equispacedMatrix hab) := by
  intro n j k hjk
  have hjk' : equispacedMatrix hab n (j : ℕ) = equispacedMatrix hab n (k : ℕ) := hjk
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hj0 : (j : ℕ) = 0 := by have := j.isLt; omega
    have hk0 : (k : ℕ) = 0 := by have := k.isLt; omega
    exact Fin.ext (by rw [hj0, hk0])
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hba : (0 : ℝ) < b - a := by linarith
    have hcoe : ((equispacedMatrix hab n (j : ℕ) : Icc a b) : ℝ)
        = ((equispacedMatrix hab n (k : ℕ) : Icc a b) : ℝ) := by rw [hjk']
    rw [coe_equispacedMatrix hab (Nat.lt_succ_iff.mp j.isLt),
      coe_equispacedMatrix hab (Nat.lt_succ_iff.mp k.isLt)] at hcoe
    have key : ((j : ℕ) : ℝ) * ((b - a) / n) = ((k : ℕ) : ℝ) * ((b - a) / n) := by
      have e1 : ((j : ℕ) : ℝ) * (b - a) / n = ((j : ℕ) : ℝ) * ((b - a) / n) := by ring
      have e2 : ((k : ℕ) : ℝ) * (b - a) / n = ((k : ℕ) : ℝ) * ((b - a) / n) := by ring
      rw [← e1, ← e2]
      linarith
    have hne : (b - a) / (n : ℝ) ≠ 0 := ne_of_gt (by positivity)
    exact Fin.ext (by exact_mod_cast mul_right_cancel₀ hne key)

/-- **§8.1.3, a lower bound for the equispaced Lebesgue constants** (Schönhage): for the equally
spaced nodes on `[a, b]` and `n ≥ 1`,

`Λ_n(X) ≥ 2^n/(8 n²)`, that is, `Λ_n(X) ≥ 2^{n−3}/n²`,

so the equispaced Lebesgue constants grow exponentially and equispaced interpolation is unstable.
This is the one-sided half of the asymptotics `Λ_n ≃ 2^{n+1}/(e n log n)` that §8.1.3 quotes from
Turetskii without proof; the asymptotic equivalence itself is not formalized (see the module
doc), and this bound concerns a single interpolation matrix, so it says nothing about Erdős's or
Faber's theorems, which quantify over all of them.

The proof evaluates the Lebesgue function at the midpoint `t = a + (b − a)/(2n)` of the first
panel. There the node spacing cancels from every characteristic polynomial,
`ℓ_i(t) = ∏_{j ≠ i} (1/2 − j)/(i − j)`, the denominators telescope into `i ! (n − i)!`
(`prod_erase_abs_sub`) and the common numerator into `(2n)!/(2^{2n+1} n !)`
(`prod_range_abs_half`); the largest omitted factor is `(2n − 1)/2`, and summing
`∑_i 1/(i ! (n − i)!) = 2^n/n !` gives `C(2n, n) 2^n/(4^n (2n − 1))`, which
`Nat.four_pow_le_two_mul_self_mul_centralBinom` bounds below by `2^n/(8n²)`. -/
theorem lebesgueConstant_equispaced_lower (hab : a < b) {n : ℕ} (hn : 1 ≤ n) :
    (2 : ℝ) ^ n / (8 * (n : ℝ) ^ 2) ≤ lebesgueConstant (equispacedMatrix hab) n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hba : (0 : ℝ) < b - a := by linarith
  have hc : (b - a) / (n : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hX := isInterpMatrix_equispacedMatrix hab
  have hmem : a + (b - a) / (2 * n) ∈ Icc a b := by
    rw [Set.mem_Icc]
    have h1 : (0 : ℝ) < (b - a) / (2 * n) := by positivity
    have h2 : (b - a) / (2 * n) ≤ b - a := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    exact ⟨by linarith, by linarith⟩
  refine le_trans ?_ (sum_abs_basisCM_le_lebesgueConstant hX n ⟨a + (b - a) / (2 * n), hmem⟩)
  have hval : ∀ i : Fin (n + 1),
      |Lagrange.basisCM (fun j : Fin (n + 1) => equispacedMatrix hab n (j : ℕ)) i
          ⟨a + (b - a) / (2 * n), hmem⟩|
        = (∏ j ∈ (univ : Finset (Fin (n + 1))).erase i, |1 / 2 - ((j : ℕ) : ℝ)|)
            / (((i : ℕ)! : ℝ) * ((n - (i : ℕ))! : ℝ)) := by
    intro i
    have hprod : Lagrange.basisCM (fun j : Fin (n + 1) => equispacedMatrix hab n (j : ℕ)) i
          ⟨a + (b - a) / (2 * n), hmem⟩
        = ∏ j ∈ (univ : Finset (Fin (n + 1))).erase i,
            (1 / 2 - ((j : ℕ) : ℝ)) / (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) := by
      rw [Lagrange.basisCM_apply, Lagrange.eval_basis_eq_prod]
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [coe_equispacedMatrix hab (Nat.lt_succ_iff.mp j.isLt),
        coe_equispacedMatrix hab (Nat.lt_succ_iff.mp i.isLt)]
      have e1 : (⟨a + (b - a) / (2 * n), hmem⟩ : Icc a b) - (a + ((j : ℕ) : ℝ) * (b - a) / n)
          = ((b - a) / n) * (1 / 2 - ((j : ℕ) : ℝ)) := by
        change a + (b - a) / (2 * n) - (a + ((j : ℕ) : ℝ) * (b - a) / n) = _
        field_simp
        ring
      have e2 : a + ((i : ℕ) : ℝ) * (b - a) / n - (a + ((j : ℕ) : ℝ) * (b - a) / n)
          = ((b - a) / n) * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) := by
        field_simp
        ring
      rw [e1, e2, mul_div_mul_left _ _ hc]
    have hsplit : (∏ j ∈ (univ : Finset (Fin (n + 1))).erase i,
        |(1 / 2 - ((j : ℕ) : ℝ)) / (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ))|)
        = (∏ j ∈ (univ : Finset (Fin (n + 1))).erase i, |1 / 2 - ((j : ℕ) : ℝ)|)
          / ∏ j ∈ (univ : Finset (Fin (n + 1))).erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
      rw [← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun j _ => abs_div _ _
    rw [hprod, Finset.abs_prod, hsplit, prod_erase_abs_sub]
  have hPeq : ∏ j ∈ (univ : Finset (Fin (n + 1))), |1 / 2 - ((j : ℕ) : ℝ)|
      = ((2 * n)! : ℝ) / (2 ^ (2 * n + 1) * (n ! : ℝ)) := by
    rw [← prod_range_abs_half n]
    exact Fin.prod_univ_eq_prod_range (fun k => |1 / 2 - (k : ℝ)|) (n + 1)
  have h2n1 : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have hlower : ∀ i : Fin (n + 1),
      2 * (((2 * n)! : ℝ) / (2 ^ (2 * n + 1) * (n ! : ℝ))) / (2 * (n : ℝ) - 1)
        ≤ ∏ j ∈ (univ : Finset (Fin (n + 1))).erase i, |1 / 2 - ((j : ℕ) : ℝ)| := by
    intro i
    have hprodpos : (0 : ℝ) < ∏ j ∈ (univ : Finset (Fin (n + 1))).erase i,
        |1 / 2 - ((j : ℕ) : ℝ)| :=
      Finset.prod_pos fun j _ => lt_of_lt_of_le (by norm_num) (half_le_abs_half_sub _)
    have hmul : |1 / 2 - ((i : ℕ) : ℝ)|
        * (∏ j ∈ (univ : Finset (Fin (n + 1))).erase i, |1 / 2 - ((j : ℕ) : ℝ)|)
        = ((2 * n)! : ℝ) / (2 ^ (2 * n + 1) * (n ! : ℝ)) := by
      rw [← hPeq]
      exact Finset.mul_prod_erase (univ : Finset (Fin (n + 1)))
        (fun j : Fin (n + 1) => |1 / 2 - ((j : ℕ) : ℝ)|) (Finset.mem_univ i)
    have hub := abs_half_sub_le (Nat.lt_succ_iff.mp i.isLt) hn
    have step : ((2 * n)! : ℝ) / (2 ^ (2 * n + 1) * (n ! : ℝ))
        ≤ ((2 * (n : ℝ) - 1) / 2)
          * (∏ j ∈ (univ : Finset (Fin (n + 1))).erase i, |1 / 2 - ((j : ℕ) : ℝ)|) := by
      rw [← hmul]
      exact mul_le_mul_of_nonneg_right hub hprodpos.le
    rw [div_le_iff₀ h2n1]
    linarith
  have hsum1 : ∑ i : Fin (n + 1), (1 : ℝ) / (((i : ℕ)! : ℝ) * ((n - (i : ℕ))! : ℝ))
      = 2 ^ n / (n ! : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => (1 : ℝ) / ((k ! : ℝ) * ((n - k)! : ℝ))) (n + 1)]
    exact sum_inv_factorial_mul n
  refine le_trans (two_pow_div_le_of_centralBinom hn) ?_
  calc 2 * (((2 * n)! : ℝ) / (2 ^ (2 * n + 1) * (n ! : ℝ))) / (2 * (n : ℝ) - 1)
        * ((2 : ℝ) ^ n / (n ! : ℝ))
      = ∑ i : Fin (n + 1), 2 * (((2 * n)! : ℝ) / (2 ^ (2 * n + 1) * (n ! : ℝ)))
            / (2 * (n : ℝ) - 1) * ((1 : ℝ) / (((i : ℕ)! : ℝ) * ((n - (i : ℕ))! : ℝ))) := by
        rw [← Finset.mul_sum, hsum1]
    _ ≤ ∑ i : Fin (n + 1), |Lagrange.basisCM
            (fun j : Fin (n + 1) => equispacedMatrix hab n (j : ℕ)) i
            ⟨a + (b - a) / (2 * n), hmem⟩| := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hfi : (0 : ℝ) < ((i : ℕ)! : ℝ) := by exact_mod_cast (i : ℕ).factorial_pos
        have hfni : (0 : ℝ) < ((n - (i : ℕ))! : ℝ) := by
          exact_mod_cast (n - (i : ℕ)).factorial_pos
        rw [hval i, mul_one_div, div_le_div_iff_of_pos_right (mul_pos hfi hfni)]
        exact hlower i

end Equispaced

end QuarteroniSaccoSaleri.Chapter08
