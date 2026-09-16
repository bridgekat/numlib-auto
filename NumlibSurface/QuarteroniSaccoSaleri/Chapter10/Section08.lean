import Numlib.Approximation.Chebyshev
import Numlib.Approximation.Interpolation

/-!
# Quarteroni–Sacco–Saleri §10.8: the polynomial of best approximation

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §10.8.

For `f ∈ C⁰([a, b])`, the *polynomial of best approximation* `p_n^* ∈ ℙ_n` is the one realizing
`‖f - p_n^*‖_∞ = min_{p ∈ ℙ_n} ‖f - p‖_∞` (10.47), the *minimax* approximation, and
`E_n^*(f) = ‖f - p_n^*‖_∞` is its error. The section quotes three results without proof: the
Chebyshev equioscillation theorem (Property 10.1: `p_n^*` exists, is unique, and `f - p_n^*`
alternates `n + 2` times between `±E_n^*(f)`), with the consequence that `p_n^*` interpolates `f`
at `n + 1` points interlacing the alternation points; the de la Vallée Poussin theorem (Property
10.2: an alternation of any competitor bounds `E_n^*(f)` from below); and the comparison of the
interpolation error with the best approximation error through the Lebesgue constant,
`‖f - Π_n f‖_∞ ≤ (1 + Λ_n) E_n^*(f)`.

Everything is the backbone `Numlib/Approximation/Chebyshev` on `X = Icc a b` with the subspace
`polyLE (Icc a b) n` of `C([a, b], ℝ)`: the book's `p_n^*` is `IsBestApprox`, `E_n^*(f)` is the
distance `Metric.infDist f (polyLE (Icc a b) n)`, Property 10.1 is
`existsUnique_isBestApprox_polyLE` with `IsBestApprox.equioscillates_of_polyLE`, Property 10.2 is
`le_infDist_of_alternates`, and the Lebesgue bound is the Lebesgue lemma
`norm_sub_apply_le_of_isIdempotentElem` of `Numlib/Analysis/Normed/Module/BestApprox` for the
interpolation projection `Lagrange.interpolateCLM`, whose norm is `Λ_n` by
`Lagrange.norm_interpolateCLM`. The interpolation consequence is the intermediate value theorem
applied between consecutive alternation points, which the backbone does not state on its own.

## Main definitions

* `equation_10_47 a b n f p` — `p` is a polynomial of best approximation of `f` in `ℙ_n` on
  `[a, b]`, (10.47); `equation_10_47_iff` reads it as the book's minimum.
* `bestApproximationError a b n f` — `E_n^*(f)`, the error of best approximation;
  `bestApproximationError_eq` is the book's `E_n^*(f) = ‖f - p_n^*‖_∞`.

## Main results

* `property_10_1_existsUnique`, `property_10_1_equioscillates` — the two clauses of the Chebyshev
  equioscillation theorem.
* `property_10_1_interpolates` — the consequence drawn after it: `p_n^*` interpolates `f` at
  `n + 1` points `x̃₀ < ⋯ < x̃ₙ` with `x_k < x̃_k < x_{k+1}`.
* `property_10_2` — the de la Vallée Poussin theorem.
* `interpolation_error_le_lebesgue` — `‖f - Π_n f‖_∞ ≤ (1 + Λ_n) E_n^*(f)`, with `Λ_n` the
  Lebesgue constant (8.11) of the nodes, written as the maximum of the Lebesgue function
  `∑ᵢ |lᵢ|` over `[a, b]`.

## Conventions

Functions live in `C(Icc a b, ℝ)` with the maximum norm `‖·‖`, the book's `‖·‖_∞`; `ℙ_n` on
`[a, b]` is `polyLE (Icc a b) n`. Points `x₀ < ⋯ < x_{n+1}` of `[a, b]` are a strictly monotone
`x : Fin (n + 2) → Icc a b`, and the interpolation operator `Π_n` at nodes
`x : Fin (n + 1) → Icc a b` is `Lagrange.interpolateCLM x`, with the Lagrange basis functions
`lᵢ = Lagrange.basisCM x i`. Property 10.1 needs `a < b`: on a one-point interval the best
approximation is not unique.
-/

open Set

namespace QuarteroniSaccoSaleri.Chapter10

variable {a b : ℝ} {n : ℕ}

/-! ### (10.47): the polynomial of best approximation and its error -/

/-- **(10.47).** For `f ∈ C⁰([a, b])`, a polynomial `p_n^* ∈ ℙ_n` is *the polynomial of best
approximation* of `f` when `‖f - p_n^*‖_∞ = min_{p_n ∈ ℙ_n} ‖f - p_n‖_∞`, the *minimax*
approximation of `f`. This is the backbone's `IsBestApprox` for the subspace `polyLE (Icc a b) n`
of `C([a, b], ℝ)`; `equation_10_47_iff` spells the minimum out. -/
def equation_10_47 (a b : ℝ) (n : ℕ) (f p : C(Icc a b, ℝ)) : Prop :=
  IsBestApprox (polyLE (Icc a b) n : Set C(Icc a b, ℝ)) f p

/-- (10.47) written out: `p` lies in `ℙ_n` and `‖f - p‖_∞` is the least of the numbers `‖f - q‖_∞`,
`q ∈ ℙ_n`. -/
theorem equation_10_47_iff (f p : C(Icc a b, ℝ)) :
    equation_10_47 a b n f p ↔ p ∈ polyLE (Icc a b) n ∧
      IsLeast (Set.range fun q : polyLE (Icc a b) n => ‖f - (q : C(Icc a b, ℝ))‖) ‖f - p‖ := by
  constructor
  · rintro ⟨hp, hmin⟩
    exact ⟨hp, ⟨⟨p, hp⟩, rfl⟩, by rintro _ ⟨q, rfl⟩; exact hmin q q.2⟩
  · rintro ⟨hp, -, hmin⟩
    exact ⟨hp, fun q hq => hmin ⟨⟨q, hq⟩, rfl⟩⟩

/-- **`E_n^*(f)`**, the error of best approximation of `f ∈ C⁰([a, b])` from `ℙ_n`: the distance
`inf_{p ∈ ℙ_n} ‖f - p‖_∞` from `f` to `ℙ_n`, which `bestApproximationError_eq` identifies with the
book's `‖f - p_n^*‖_∞` for the polynomial of best approximation `p_n^*`. -/
noncomputable def bestApproximationError (a b : ℝ) (n : ℕ) (f : C(Icc a b, ℝ)) : ℝ :=
  Metric.infDist f (polyLE (Icc a b) n : Set C(Icc a b, ℝ))

/-- `E_n^*(f) = ‖f - p_n^*‖_∞` for a polynomial of best approximation `p_n^*` of `f`. -/
theorem bestApproximationError_eq {f p : C(Icc a b, ℝ)} (hp : equation_10_47 a b n f p) :
    bestApproximationError a b n f = ‖f - p‖ :=
  hp.norm_sub_eq_infDist.symm

/-! ### Property 10.1: the Chebyshev equioscillation theorem -/

/-- **Property 10.1 (Chebyshev equioscillation theorem), first clause.** For `a < b`,
`f ∈ C⁰([a, b])` and any `n ≥ 0`, the polynomial of best approximation `p_n^*` of `f` exists and
is unique. The backbone's `existsUnique_isBestApprox_polyLE`. -/
theorem property_10_1_existsUnique (hab : a < b) (n : ℕ) (f : C(Icc a b, ℝ)) :
    ∃! p, equation_10_47 a b n f p :=
  have : Infinite (Icc a b) := Set.Icc.infinite hab
  existsUnique_isBestApprox_polyLE n f

/-- **Property 10.1 (Chebyshev equioscillation theorem), second clause.** For `a < b` and the
polynomial of best approximation `p_n^*` of `f ∈ C⁰([a, b])`, there exist `n + 2` points
`x₀ < x₁ < ⋯ < x_{n+1}` in `[a, b]` such that

`f(x_j) - p_n^*(x_j) = σ (-1)^j E_n^*(f)`, `j = 0, …, n + 1`,

with `σ = 1` or `σ = -1` depending on `f` and `n`, and `E_n^*(f) = ‖f - p_n^*‖_∞`. The backbone's
`IsBestApprox.equioscillates_of_polyLE`, whose converse `isBestApprox_of_equioscillates` the book
does not state. -/
theorem property_10_1_equioscillates (hab : a < b) {f p : C(Icc a b, ℝ)}
    (hp : equation_10_47 a b n f p) :
    ∃ (σ : ℝ) (x : Fin (n + 2) → Icc a b), (σ = 1 ∨ σ = -1) ∧
      StrictMono (fun i => (x i : ℝ)) ∧
      ∀ j : Fin (n + 2),
        f (x j) - p (x j) = σ * (-1) ^ (j : ℕ) * bestApproximationError a b n f := by
  have : Infinite (Icc a b) := Set.Icc.infinite hab
  obtain ⟨σ, x, hσ, hmono, hval⟩ := hp.equioscillates_of_polyLE
  refine ⟨σ, x, hσ, hmono, fun j => ?_⟩
  rw [bestApproximationError_eq hp]
  simpa using hval j

/-- **The consequence drawn after Property 10.1.** For the polynomial of best approximation
`p_n^*` of `f ∈ C⁰([a, b])` with alternation points `x₀ < ⋯ < x_{n+1}` and sign
`σ = ±1` as in Property 10.1, there exist `n + 1` points `x̃₀ < x̃₁ < ⋯ < x̃ₙ` in `[a, b]`, with
`x_k < x̃_k < x_{k+1}` for `k = 0, …, n`, such that

`p_n^*(x̃_j) = f(x̃_j)`, `j = 0, 1, …, n`,

so that the best approximation polynomial is a polynomial of degree `n` that interpolates `f` at
`n + 1` unknown nodes. The intermediate value theorem for `f - p_n^*` between two consecutive
alternation points, where it takes the values `±E_n^*(f)`; when `E_n^*(f) = 0` the function `f`
is itself the polynomial `p_n^*` and any point between two alternation points serves. Unlike
Property 10.1 this needs no `a < b`: the alternation points already are `n + 2` distinct points
of `[a, b]`. -/
theorem property_10_1_interpolates {f p : C(Icc a b, ℝ)}
    (hp : equation_10_47 a b n f p) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {x : Fin (n + 2) → Icc a b}
    (hmono : StrictMono fun i => (x i : ℝ))
    (hval : ∀ j : Fin (n + 2),
      f (x j) - p (x j) = σ * (-1) ^ (j : ℕ) * bestApproximationError a b n f) :
    ∃ y : Fin (n + 1) → Icc a b, StrictMono (fun i => (y i : ℝ)) ∧
      (∀ k : Fin (n + 1), (x k.castSucc : ℝ) < y k ∧ (y k : ℝ) < x k.succ) ∧
      ∀ j : Fin (n + 1), p (y j) = f (y j) := by
  have hlt : ∀ k : Fin (n + 1), (x k.castSucc : ℝ) < x k.succ := fun k =>
    hmono Fin.castSucc_lt_succ
  have hE : bestApproximationError a b n f = ‖f - p‖ := bestApproximationError_eq hp
  -- a root of `f - p` strictly between two consecutive alternation points
  have hroot : ∀ k : Fin (n + 1), ∃ z : Icc a b,
      (x k.castSucc : ℝ) < z ∧ (z : ℝ) < x k.succ ∧ (f - p) z = 0 := by
    intro k
    rcases eq_or_lt_of_le (norm_nonneg (f - p)) with h0 | hpos
    · -- `f = p`: the midpoint serves
      have hfp : f - p = 0 := norm_eq_zero.mp h0.symm
      have hmem : ((x k.castSucc : ℝ) + x k.succ) / 2 ∈ Icc a b :=
        ⟨by linarith [(x k.castSucc).2.1, (x k.succ).2.1],
          by linarith [(x k.castSucc).2.2, (x k.succ).2.2]⟩
      refine ⟨⟨((x k.castSucc : ℝ) + x k.succ) / 2, hmem⟩, ?_, ?_, ?_⟩
      · dsimp only
        linarith [hlt k]
      · dsimp only
        linarith [hlt k]
      · rw [hfp]
        rfl
    · refine ContinuousMap.exists_mem_Ioo_eq_zero_of_mul_neg (hlt k) ?_
      have hsq : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
      have hpow : ((-1 : ℝ) ^ (k : ℕ)) * (-1) ^ (k : ℕ) = 1 := by
        rw [← mul_pow]
        norm_num
      rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply, hval k.castSucc, hval k.succ, hE,
        Fin.val_castSucc, Fin.val_succ, pow_succ]
      have hprod : σ * (-1) ^ (k : ℕ) * ‖f - p‖ * (σ * ((-1) ^ (k : ℕ) * -1) * ‖f - p‖)
          = -((σ * σ) * ((-1) ^ (k : ℕ) * (-1) ^ (k : ℕ)) * (‖f - p‖ * ‖f - p‖)) := by ring
      rw [hprod, hsq, hpow, one_mul, one_mul, neg_lt_zero]
      exact mul_pos hpos hpos
  choose y hy₁ hy₂ hy₃ using hroot
  refine ⟨y, ?_, fun k => ⟨hy₁ k, hy₂ k⟩, fun j => ?_⟩
  · refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    calc (y i.castSucc : ℝ) < x i.castSucc.succ := hy₂ i.castSucc
      _ = x i.succ.castSucc := by rw [Fin.succ_castSucc]
      _ < y i.succ := hy₁ i.succ
  · have h := hy₃ j
    rw [ContinuousMap.sub_apply, sub_eq_zero] at h
    exact h.symm

/-! ### Property 10.2: the de la Vallée Poussin theorem -/

/-- **Property 10.2 (de la Vallée Poussin theorem).** Let `n ≥ 0` and let `x₀ < x₁ < ⋯ < x_{n+1}`
be `n + 2` points in `[a, b]`. If there exists a polynomial `q_n` of degree `≤ n` such that

`f(x_j) - q_n(x_j) = (-1)^j e_j`, `j = 0, 1, …, n + 1`,

where all the `e_j` have the same sign and are non null, then `min_{0 ≤ j ≤ n+1} |e_j| ≤ E_n^*(f)`.
The backbone's `le_infDist_of_alternates` with `ε = min_j |e_j|` and `σ` the common sign. -/
theorem property_10_2 {f q : C(Icc a b, ℝ)} (hq : q ∈ polyLE (Icc a b) n)
    {x : Fin (n + 2) → Icc a b} (hmono : StrictMono fun i => (x i : ℝ)) {e : Fin (n + 2) → ℝ}
    (hval : ∀ j : Fin (n + 2), f (x j) - q (x j) = (-1) ^ (j : ℕ) * e j)
    (hsign : (∀ j, 0 < e j) ∨ ∀ j, e j < 0) :
    ⨅ j, |e j| ≤ bestApproximationError a b n f := by
  have hbdd : BddBelow (Set.range fun j => |e j|) := (Set.finite_range _).bddBelow
  have hpow : ∀ j : Fin (n + 2), ((-1 : ℝ) ^ (j : ℕ)) * (-1) ^ (j : ℕ) = 1 := fun j => by
    rw [← mul_pow]
    norm_num
  rcases hsign with hpos | hneg
  · refine le_infDist_of_alternates hq (Or.inl rfl) hmono fun j => ?_
    calc ⨅ j, |e j| ≤ |e j| := ciInf_le hbdd j
      _ = 1 * (-1) ^ (j : ℕ) * (f (x j) - q (x j)) := by
          rw [hval j, abs_of_pos (hpos j), one_mul, ← mul_assoc, hpow j, one_mul]
  · refine le_infDist_of_alternates hq (Or.inr rfl) hmono fun j => ?_
    calc ⨅ j, |e j| ≤ |e j| := ciInf_le hbdd j
      _ = -1 * (-1) ^ (j : ℕ) * (f (x j) - q (x j)) := by
          rw [hval j, abs_of_neg (hneg j), mul_assoc, ← mul_assoc ((-1 : ℝ) ^ (j : ℕ)), hpow j,
            one_mul, neg_one_mul]

/-! ### The interpolation error and the Lebesgue constant -/

/-- **§10.8, the bound `‖f - Π_n f‖_∞ ≤ (1 + Λ_n) E_n^*(f)`.** For `n + 1` distinct nodes in
`[a, b]` and the Lagrange interpolation operator `Π_n` at those nodes, the interpolation error of
`f ∈ C⁰([a, b])` exceeds the best approximation error by at most the factor `1 + Λ_n`, where
`Λ_n = ‖∑ᵢ |lᵢ|‖_∞` is the Lebesgue constant (8.11) of the nodes. The book's argument — the
triangle inequality through `p_n^*` and the Lagrange representation of `p_n^* - Π_n f = Π_n (p_n^* -
f)` — is the Lebesgue lemma `norm_sub_apply_le_of_isIdempotentElem` for the projection
`Lagrange.interpolateCLM x`, whose range is `ℙ_n` (`Lagrange.range_interpolateCLM`) and whose
norm is `Λ_n` (`Lagrange.norm_interpolateCLM`). -/
theorem interpolation_error_le_lebesgue {x : Fin (n + 1) → Icc a b} (hx : Function.Injective x)
    (f : C(Icc a b, ℝ)) :
    ‖f - Lagrange.interpolateCLM x f‖
      ≤ (1 + sSup (Set.range fun t : Icc a b => ∑ i, |Lagrange.basisCM x i t|))
        * bestApproximationError a b n f := by
  have : Nonempty (Icc a b) := ⟨x 0⟩
  have h := norm_sub_apply_le_of_isIdempotentElem (Lagrange.interpolateCLM x)
    (Lagrange.isIdempotentElem_interpolateCLM hx) f
  rw [Lagrange.range_interpolateCLM hx, Lagrange.norm_interpolateCLM hx] at h
  exact h

end QuarteroniSaccoSaleri.Chapter10
