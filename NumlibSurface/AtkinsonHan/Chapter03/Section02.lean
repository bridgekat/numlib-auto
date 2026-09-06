import Mathlib.LinearAlgebra.Vandermonde
import Numlib.Approximation.DividedDifference
import Numlib.Approximation.Hermite

/-!
# Atkinson–Han §3.2: interpolation theory

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §3.2.

The section poses the interpolation problem abstractly — find `uₙ` in an `n`-dimensional subspace
`Vₙ` of a normed space with `Lᵢ uₙ = bᵢ` for `n` bounded functionals `Lᵢ` — and then instantiates it
four times: Lagrange polynomial interpolation, Hermite interpolation, piecewise linear interpolation
and trigonometric interpolation.

## Main results

* `definition_3_2_1`, `lemma_3_2_2`, `theorem_3_2_3` — the abstract problem: linear independence of
  the functionals over `Vₙ`, the determinant criterion `det (Lᵢ vⱼ) ≠ 0`, and the four equivalent
  forms of unique solvability.
* `equation_3_2_1`, `equation_3_2_2`, `equation_3_2_3` — Lagrange interpolation: unique solvability
  in `𝒫ₙ`, the Vandermonde determinant `∏_{j > i} (xⱼ − xᵢ)`, and Lagrange's formula with its
  cardinal basis `φᵢ (xⱼ) = δᵢⱼ`.
* `proposition_3_2_4` — the error formula `f(x) − pₙ(x) = ωₙ(x) f⁽ⁿ⁺¹⁾(ξₓ) / (n + 1)!`, and
  `equation_3_2_5` its divided-difference form `f(x) − pₙ(x) = ωₙ(x) f[x₀, …, xₙ, x]`.
* `equation_3_2_6`, `exercise_3_2_6`, `equation_3_2_6_general` and
  `equation_3_2_6_general_error` — Hermite interpolation at simple nodes and with multiplicities,
  with the error formula in both forms.
* `equation_3_2_7`, `equation_3_2_8`, `equation_3_2_9` — piecewise linear interpolation: the local
  formula, the modulus-of-continuity bound `ω(f, h)`, and the bound `h²‖f''‖_∞ / 8`.
* `equation_3_2_13`, `equation_3_2_16`, `equation_3_2_17` — trigonometric interpolation: `𝕋ₙ` in the
  book's cosine–sine form, the equispaced nodes `xⱼ = j h` with `h = 2π / (2n + 1)`, and unique
  solvability at any `2n + 1` distinct nodes of a period.

## The backbone behind them

The abstract framework is `Numlib/Approximation/Unisolvent`: the book's "the interpolation problem
has a unique solution" is `Approximation.IsUnisolvent Vₙ L`, and Definition 3.2.1, Lemma 3.2.2 and
Theorem 3.2.3 are its `isUnisolvent_iff_linearIndependent`, `isUnisolvent_iff_det_ne_zero` and
`isUnisolvent_tfae`. Lagrange interpolation and the piecewise linear operator are
`Numlib/Approximation/Interpolation`, Hermite interpolation is `Numlib/Approximation/Hermite`, and
trigonometric interpolation is `trigInterpCLM` of the first of those, which gets its unique
solvability from the Haar condition for `trigPolyLE` — the substitution `z = e^{ix}` of (3.2.15),
carried out once and for all in `Numlib/Approximation/Chebyshev`.

## Conventions

* `𝒫ₙ` on a compact `X ⊆ ℝ` is `polyLE X n`, the subspace of `C(X, ℝ)` of restrictions of real
  polynomials of degree at most `n`; `𝕋ₙ` is `trigPolyLE (2π) n` inside `C_p(2π) = C(AddCircle
  (2π), ℝ)`, as everywhere in this surface.
* The book indexes the Lagrange nodes `x₀ < ⋯ < xₙ` from `0` and the Hermite nodes `x₁ < ⋯ < xₙ`
  from `1`; both are indexed from `0` here, so the `n` nodes of (3.2.6) become `n + 1` nodes and its
  degree bound `2n − 1` becomes `2(n + 1) − 1`.
* Where the book writes a maximum over `[a, b]` of `|f − Π f|`, the statements here are pointwise
  bounds, which is the same thing on a compact interval and does not need a supremum to exist.

## Not formalized here

* The `H²(a, b)` estimates (3.2.10)–(3.2.12) for piecewise linear interpolation, which need Sobolev
  spaces; they are out of scope with the rest of that material.
* The Newton form of the interpolant, which the book only cites; (3.2.5), the divided-difference
  form of the error, is `equation_3_2_5` above and rests on `DividedDifference.newton`.
* Example 3.2.5 and Table 3.1, which are numerical illustrations.
-/

open scoped Polynomial Real

namespace AtkinsonHan.Chapter03

/-! ### The abstract interpolation problem -/

section Abstract

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {n : ℕ} {Vₙ : Submodule 𝕜 V} {L : Fin n → StrongDual 𝕜 V}

/-- **Definition 3.2.1.** The functionals `L₁, …, Lₙ` are *linearly independent over `Vₙ`* when
`∑ᵢ cᵢ Lᵢ(v) = 0` for every `v ∈ Vₙ` forces `cᵢ = 0`. For `n` functionals on an `n`-dimensional
subspace that condition is exactly unique solvability of the interpolation problem, which is the
backbone's `Approximation.IsUnisolvent`; this is the bridge naming the book's condition. -/
theorem definition_3_2_1 (v : Module.Basis (Fin n) 𝕜 Vₙ) :
    Approximation.IsUnisolvent Vₙ L ↔
      ∀ c : Fin n → 𝕜, (∀ w ∈ Vₙ, ∑ i, c i * L i w = 0) → ∀ i, c i = 0 := by
  rw [Approximation.isUnisolvent_iff_linearIndependent v, Fintype.linearIndependent_iff]
  refine forall_congr' fun c => imp_congr_left ?_
  constructor
  · intro hsum w hw
    have := congrArg (fun g : Vₙ →ₗ[𝕜] 𝕜 => g ⟨w, hw⟩) hsum
    simpa using this
  · intro hsum
    refine LinearMap.ext fun u => ?_
    simpa using hsum (u : V) u.2

/-- **Lemma 3.2.2.** The functionals `L₁, …, Lₙ` are linearly independent over `Vₙ` if and only if
`det (Lᵢ vⱼ) ≠ 0` for a basis `v₁, …, vₙ` of `Vₙ`. Since the left-hand side does not mention the
basis, neither does the nonvanishing of the determinant. -/
theorem lemma_3_2_2 (v : Module.Basis (Fin n) 𝕜 Vₙ) :
    (∀ c : Fin n → 𝕜, (∀ w ∈ Vₙ, ∑ i, c i * L i w = 0) → ∀ i, c i = 0) ↔
      (Matrix.of fun i j => L i (v j : V)).det ≠ 0 :=
  (definition_3_2_1 v).symm.trans (Approximation.isUnisolvent_iff_det_ne_zero v)

/-- **Theorem 3.2.3.** For `n` bounded functionals on an `n`-dimensional subspace `Vₙ` the following
are equivalent: the interpolation problem has a unique solution for every datum; the functionals are
linearly independent over `Vₙ`; the only `uₙ ∈ Vₙ` with `Lᵢ uₙ = 0` for all `i` is `uₙ = 0`; and for
every datum the problem has at least one solution. -/
theorem theorem_3_2_3 (v : Module.Basis (Fin n) 𝕜 Vₙ) :
    List.TFAE
      [∀ b : Fin n → 𝕜, ∃! u : Vₙ, ∀ i, L i (u : V) = b i,
        ∀ c : Fin n → 𝕜, (∀ w ∈ Vₙ, ∑ i, c i * L i w = 0) → ∀ i, c i = 0,
        ∀ u : Vₙ, (∀ i, L i (u : V) = 0) → u = 0,
        ∀ b : Fin n → 𝕜, ∃ u : Vₙ, ∀ i, L i (u : V) = b i] := by
  tfae_have 1 ↔ 2 := definition_3_2_1 v
  tfae_have 1 ↔ 3 := Approximation.isUnisolvent_iff_forall_eq_zero v
  tfae_have 1 ↔ 4 := Approximation.isUnisolvent_iff_forall_exists v
  tfae_finish

end Abstract

/-! ### Lagrange polynomial interpolation -/

section Lagrange

variable {a b : ℝ} {n : ℕ}

/-- The Lagrange basis function `φᵢ` of (3.2.3), in the product form the book prints. -/
private theorem basisCM_eq_prod (x : Fin (n + 1) → Set.Icc a b) (i : Fin (n + 1))
    (t : Set.Icc a b) :
    Lagrange.basisCM x i t
      = ∏ j ∈ Finset.univ.erase i, ((t : ℝ) - (x j : ℝ)) / ((x i : ℝ) - (x j : ℝ)) := by
  rw [Lagrange.basisCM_apply, Lagrange.basis, Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun j _ => by simp [Lagrange.basisDivisor, div_eq_inv_mul]

/-- **(3.2.1).** The Lagrange interpolation problem — find `pₙ ∈ 𝒫ₙ` with `pₙ(xᵢ) = f(xᵢ)` at
`n + 1` distinct nodes of `[a, b]` — has exactly one solution. -/
theorem equation_3_2_1 {x : Fin (n + 1) → Set.Icc a b} (hx : Function.Injective x)
    (f : C(Set.Icc a b, ℝ)) :
    ∃! p : polyLE (Set.Icc a b) n, ∀ i, (p : C(Set.Icc a b, ℝ)) (x i) = f (x i) :=
  Lagrange.isUnisolvent_polyLE hx fun i => f (x i)

/-- **(3.2.2).** In the monomial basis `vⱼ(x) = xʲ` of `𝒫ₙ` the matrix `(Lᵢ vⱼ)` of the Lagrange
interpolation problem is the Vandermonde matrix of the nodes, whose determinant is
`∏_{j > i} (xⱼ − xᵢ)`. -/
theorem equation_3_2_2 (x : Fin (n + 1) → ℝ) :
    (Matrix.of fun i j : Fin (n + 1) => ((Polynomial.X : ℝ[X]) ^ (j : ℕ)).eval (x i)).det
      = ∏ i, ∏ j ∈ Finset.Ioi i, (x j - x i) := by
  have h : (Matrix.of fun i j : Fin (n + 1) => ((Polynomial.X : ℝ[X]) ^ (j : ℕ)).eval (x i))
      = Matrix.vandermonde x := by
    ext i j
    simp [Matrix.vandermonde]
  rw [h, Matrix.det_vandermonde]

/-- **(3.2.2), the nonvanishing.** At distinct nodes every factor of the Vandermonde determinant is
nonzero, so the determinant is, and Lemma 3.2.2 gives unique solvability again. -/
theorem equation_3_2_2_ne_zero {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) :
    (Matrix.of fun i j : Fin (n + 1) => ((Polynomial.X : ℝ[X]) ^ (j : ℕ)).eval (x i)).det ≠ 0 := by
  rw [equation_3_2_2]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  exact sub_ne_zero.mpr fun h => absurd (hx h) (Finset.mem_Ioi.mp hj).ne'

/-- **(3.2.3), Lagrange's formula.** The interpolant is `pₙ(x) = ∑ᵢ f(xᵢ) φᵢ(x)` with
`φᵢ(x) = ∏_{j ≠ i} (x − xⱼ)/(xᵢ − xⱼ)`. -/
theorem equation_3_2_3 (x : Fin (n + 1) → Set.Icc a b) (f : C(Set.Icc a b, ℝ))
    (t : Set.Icc a b) :
    Lagrange.interpolateCLM x f t
      = ∑ i, f (x i) * ∏ j ∈ Finset.univ.erase i,
          ((t : ℝ) - (x j : ℝ)) / ((x i : ℝ) - (x j : ℝ)) := by
  rw [Lagrange.interpolateCLM_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [basisCM_eq_prod]

/-- **(3.2.3), the cardinal property.** The Lagrange basis functions satisfy `φᵢ(xⱼ) = δᵢⱼ`, which
is what makes (3.2.3) an interpolant and the `φᵢ` a basis of `𝒫ₙ`. -/
theorem equation_3_2_3_delta {x : Fin (n + 1) → Set.Icc a b} (hx : Function.Injective x)
    (i j : Fin (n + 1)) :
    (∏ k ∈ Finset.univ.erase i, ((x j : ℝ) - (x k : ℝ)) / ((x i : ℝ) - (x k : ℝ)))
      = if i = j then 1 else 0 := by
  rw [← basisCM_eq_prod]
  by_cases hij : i = j
  · subst hij
    simp [Lagrange.basisCM_apply_node_self hx]
  · simp [Lagrange.basisCM_apply_node_ne hij, hij]

/-- **Proposition 3.2.4 with (3.2.4).** For `f` of class `C^{n+1}` and increasing nodes
`x₀ < ⋯ < xₙ`, the error of the Lagrange interpolant at a point `t` is
`ωₙ(t) f⁽ⁿ⁺¹⁾(ξ)/(n + 1)!` with `ωₙ(t) = ∏ᵢ (t − xᵢ)`, for some `ξ` between `minᵢ {xᵢ, t}` and
`maxᵢ {xᵢ, t}`.

The backbone `Lagrange.exists_sub_interpolate_eq` places `ξ` strictly inside any interval containing
the nodes and `t`, so taking that interval to be `[minᵢ {xᵢ, t}, maxᵢ {xᵢ, t}]` gives the book's
localization. The conclusion is stated with the closed interval because it degenerates to a point
when `t` is the only node, and there the identity holds with both sides zero. -/
theorem proposition_3_2_4 {f : ℝ → ℝ} (hf : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f)
    {x : Fin (n + 1) → ℝ} (hx : StrictMono x) (t : ℝ) :
    ∃ ξ ∈ Set.Icc (min t (x 0)) (max t (x (Fin.last n))),
      f t - (Lagrange.interpolate Finset.univ x fun i => f (x i)).eval t
        = (∏ i, (t - x i)) / (n + 1).factorial * iteratedDeriv (n + 1) f ξ := by
  set lo := min t (x 0) with hlo
  set hi := max t (x (Fin.last n)) with hhi
  have hxlo : ∀ i, lo ≤ x i := fun i =>
    le_trans (min_le_right _ _) (hx.monotone (Fin.zero_le i))
  have hxhi : ∀ i, x i ≤ hi := fun i =>
    le_trans (hx.monotone (Fin.le_last i)) (le_max_right _ _)
  have htmem : t ∈ Set.Icc lo hi := ⟨min_le_left _ _, le_max_left _ _⟩
  rcases lt_or_ge lo hi with hlt | hge
  · obtain ⟨ξ, hξ, hval⟩ := Lagrange.exists_sub_interpolate_eq hlt hf hx.injective
      (fun i => ⟨hxlo i, hxhi i⟩) htmem
    exact ⟨ξ, Set.Ioo_subset_Icc_self hξ, by rw [hval]; ring⟩
  · -- the degenerate case: the interval collapses, so every node equals `t`
    have hlot : lo = t := le_antisymm htmem.1 (htmem.2.trans hge)
    have hxt : ∀ i, x i = t :=
      fun i => le_antisymm ((hxhi i).trans (hge.trans hlot.le)) (hlot ▸ hxlo i)
    refine ⟨t, htmem, ?_⟩
    have hev : (Lagrange.interpolate Finset.univ x fun i => f (x i)).eval t = f t := by
      rw [← hxt 0, Lagrange.eval_interpolate_at_node _ hx.injective.injOn (Finset.mem_univ 0)]
    rw [hev, sub_self, Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (n + 1)))
      (by rw [hxt 0, sub_self])]
    simp

/-- **(3.2.5).** The divided-difference form of the Lagrange interpolation error: with `pₙ` the
interpolant of `f` at the `n + 1` distinct nodes `x₀, …, xₙ` and `x` none of them,

`f(x) - pₙ(x) = ωₙ(x) f[x₀, …, xₙ, x]`,   `ωₙ(x) = ∏ᵢ (x - xᵢ)`,

with `f[·]` the Newton divided difference of order `n + 1`. Unlike Proposition 3.2.4 it asks nothing
of `f` beyond its values at the nodes and at `x`; the book states it in passing and uses it for the
Newton form of the interpolant. -/
theorem equation_3_2_5 {f : ℝ → ℝ} {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) {t : ℝ}
    (ht : ∀ i, x i ≠ t) :
    f t - (Lagrange.interpolate Finset.univ x fun i => f (x i)).eval t
      = (∏ i, (t - x i)) * DividedDifference.newton f (Fin.snoc x t) :=
  DividedDifference.sub_eval_interpolate_eq_newton f hx ht

end Lagrange

/-! ### Hermite polynomial interpolation -/

section Hermite

/-- **(3.2.6).** At `n` distinct nodes there is exactly one polynomial of degree at most `2n − 1`
matching `f` and `f'` at every node.

No smoothness of `f` is assumed: the statement is about the prescribed data `f(xᵢ)` and `f'(xᵢ)`,
and holds whatever those numbers are. -/
theorem equation_3_2_6 {n : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x) (f : ℝ → ℝ) :
    ∃! p : ℝ[X], p.degree < ((2 * n : ℕ) : WithBot ℕ) ∧
      (∀ i, p.eval (x i) = f (x i)) ∧
      (∀ i, (Polynomial.derivative p).eval (x i) = deriv f (x i)) := by
  have hM : ∑ _i : Fin n, ((1 : ℕ) + 1) = 2 * n := by
    simp [Finset.sum_const, mul_comm]
  have key := Hermite.isUnisolvent hx (m := fun _ => 1) hM fun i j => iteratedDeriv j f (x i)
  have hiff : ∀ p : ℝ[X],
      (∀ i, ∀ j ≤ 1, (Polynomial.derivative^[j] p).eval (x i) = iteratedDeriv j f (x i))
        ↔ ((∀ i, p.eval (x i) = f (x i)) ∧
            ∀ i, (Polynomial.derivative p).eval (x i) = deriv f (x i)) := by
    intro p
    constructor
    · refine fun h => ⟨fun i => by simpa using h i 0 (by omega), fun i => ?_⟩
      simpa [iteratedDeriv_one] using h i 1 le_rfl
    · rintro ⟨h0, h1⟩ i j hj
      interval_cases j
      · simpa using h0 i
      · simpa [iteratedDeriv_one] using h1 i
  simpa only [hiff] using key

/-- **Exercise 3.2.6, the error of (3.2.6).** For `f` of class `C^{2n}` the Hermite interpolant at
`n` increasing nodes satisfies `f(t) − p(t) = f⁽²ⁿ⁾(ξ) ∏ᵢ (t − xᵢ)² / (2n)!` for some `ξ` between
`minᵢ {xᵢ, t}` and `maxᵢ {xᵢ, t}`. The nodes are indexed by `Fin (n + 1)`, so the book's `n` is
`n + 1` here. -/
theorem exercise_3_2_6 {n : ℕ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((2 * (n + 1) : ℕ) : WithTop ℕ∞) f) {x : Fin (n + 1) → ℝ}
    (hx : StrictMono x) (t : ℝ) :
    ∃ ξ ∈ Set.Icc (min t (x 0)) (max t (x (Fin.last n))),
      f t - (Hermite.interpolate x (fun _ => 1) f).eval t
        = (∏ i, (t - x i) ^ 2) / (2 * (n + 1)).factorial * iteratedDeriv (2 * (n + 1)) f ξ := by
  have hxlo : ∀ i, min t (x 0) ≤ x i := fun i =>
    le_trans (min_le_right _ _) (hx.monotone (Fin.zero_le i))
  have hxhi : ∀ i, x i ≤ max t (x (Fin.last n)) := fun i =>
    le_trans (hx.monotone (Fin.le_last i)) (le_max_right _ _)
  have hsum : ∑ _i : Fin (n + 1), ((1 : ℕ) + 1) = 2 * n + 1 + 1 := by
    simp [Finset.sum_const]
    ring
  have hf' : ContDiff ℝ ((2 * n + 1 + 1 : ℕ) : WithTop ℕ∞) f := by
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring]
    exact hf
  obtain ⟨ξ, hξ, hval⟩ := Hermite.exists_sub_interpolate_eq (N := 2 * n + 1)
    hf' hx.injective (fun i => ⟨hxlo i, hxhi i⟩) hsum
    (⟨min_le_left _ _, le_max_left _ _⟩ : t ∈ Set.Icc _ _)
  refine ⟨ξ, hξ, ?_⟩
  rw [hval, show 2 * n + 1 + 1 = 2 * (n + 1) by ring]
  ring

/-- **The general Hermite interpolation problem.** For distinct nodes `xᵢ` and multiplicities `mᵢ`
summing to `N + 1 = ∑ᵢ (mᵢ + 1)` there is exactly one `p ∈ 𝒫_N` with `p⁽ʲ⁾(xᵢ) = f⁽ʲ⁾(xᵢ)` for
`j ≤ mᵢ`. -/
theorem equation_3_2_6_general {n N : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x)
    {m : Fin n → ℕ} (hN : ∑ i, (m i + 1) = N + 1) (f : ℝ → ℝ) :
    ∃! p : ℝ[X], p.degree < ((N + 1 : ℕ) : WithBot ℕ) ∧
      ∀ i, ∀ j ≤ m i, (Polynomial.derivative^[j] p).eval (x i) = iteratedDeriv j f (x i) :=
  Hermite.isUnisolvent hx hN fun i j => iteratedDeriv j f (x i)

/-- **The error of the general Hermite interpolation problem.** For `f ∈ C^{N+1}[a, b]` the error is
`f⁽ᴺ⁺¹⁾(ξ) ∏ᵢ (t − xᵢ)^{mᵢ+1} / (N + 1)!` for some `ξ ∈ [a, b]`. -/
theorem equation_3_2_6_general_error {n N : ℕ} {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) f) {x : Fin n → ℝ} (hx : Function.Injective x)
    (hxmem : ∀ i, x i ∈ Set.Icc a b) {m : Fin n → ℕ} (hN : ∑ i, (m i + 1) = N + 1) {t : ℝ}
    (ht : t ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Icc a b, f t - (Hermite.interpolate x m f).eval t
      = (∏ i, (t - x i) ^ (m i + 1)) / (N + 1).factorial * iteratedDeriv (N + 1) f ξ := by
  obtain ⟨ξ, hξ, hval⟩ := Hermite.exists_sub_interpolate_eq hf hx hxmem hN ht
  exact ⟨ξ, hξ, by rw [hval]; ring⟩

end Hermite

/-! ### Piecewise linear interpolation -/

section PiecewiseLinear

variable {a b : ℝ} {n : ℕ} {x : ℕ → Set.Icc a b}

/-- **(3.2.7).** On the subinterval `[xⱼ, xⱼ₊₁]` of the partition the piecewise linear interpolant
is the affine function `((xⱼ₊₁ − t) f(xⱼ) + (t − xⱼ) f(xⱼ₊₁)) / hⱼ` through the two node values. -/
theorem equation_3_2_7 (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) (f : C(Set.Icc a b, ℝ))
    {j : ℕ} (hj : j ≤ n) {t : Set.Icc a b} (h1 : (x j : ℝ) ≤ (t : ℝ))
    (h2 : (t : ℝ) ≤ (x (j + 1) : ℝ)) :
    piecewiseLinearInterpCLM n x f t
      = ((x (j + 1) : ℝ) - (t : ℝ)) / ((x (j + 1) : ℝ) - (x j : ℝ)) * f (x j)
        + ((t : ℝ) - (x j : ℝ)) / ((x (j + 1) : ℝ) - (x j : ℝ)) * f (x (j + 1)) := by
  have hd : ((x (j + 1) : ℝ) - (x j : ℝ)) ≠ 0 := sub_ne_zero.mpr (hstep j hj).ne'
  rw [piecewiseLinearInterpCLM_apply_of_mem hstep f hj h1 h2]
  field_simp
  ring

/-- **(3.2.7), uniqueness.** A continuous function that agrees with `f` at every node and is affine
on every subinterval — in the sense of (3.2.7) applied to itself — is the piecewise linear
interpolant of `f`. -/
theorem equation_3_2_7_unique (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ))
    (hfirst : (x 0 : ℝ) = a) (hlast : (x (n + 1) : ℝ) = b) (f g : C(Set.Icc a b, ℝ))
    (hnode : ∀ j ≤ n + 1, g (x j) = f (x j))
    (haffine : ∀ j ≤ n, ∀ t : Set.Icc a b, (x j : ℝ) ≤ (t : ℝ) → (t : ℝ) ≤ (x (j + 1) : ℝ) →
      g t = ((x (j + 1) : ℝ) - (t : ℝ)) / ((x (j + 1) : ℝ) - (x j : ℝ)) * g (x j)
        + ((t : ℝ) - (x j : ℝ)) / ((x (j + 1) : ℝ) - (x j : ℝ)) * g (x (j + 1))) :
    g = piecewiseLinearInterpCLM n x f := by
  refine ContinuousMap.ext fun t => ?_
  obtain ⟨j, hj, h1, h2⟩ := exists_mem_subinterval hfirst hlast t
  rw [haffine j hj t h1 h2, equation_3_2_7 hstep f hj h1 h2, hnode j (by omega),
    hnode (j + 1) (by omega)]

/-- **(3.2.8).** For a merely continuous `f`, the piecewise linear interpolant on a partition of
mesh at most `h` differs from `f` by at most the modulus of continuity `ω(f, h)`. -/
theorem equation_3_2_8 (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) (hfirst : (x 0 : ℝ) = a)
    (hlast : (x (n + 1) : ℝ) = b) (f : C(Set.Icc a b, ℝ)) {h : ℝ}
    (hmesh : ∀ i ≤ n, (x (i + 1) : ℝ) - (x i : ℝ) ≤ h) (t : Set.Icc a b) :
    |f t - piecewiseLinearInterpCLM n x f t| ≤ f.modulusOfContinuity h :=
  calc |f t - piecewiseLinearInterpCLM n x f t|
      = ‖(f - piecewiseLinearInterpCLM n x f) t‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖f - piecewiseLinearInterpCLM n x f‖ := ContinuousMap.norm_coe_le_norm _ t
    _ ≤ f.modulusOfContinuity h :=
        norm_sub_piecewiseLinearInterpCLM_le_modulus hstep hfirst hlast f hmesh

/-- **(3.2.9).** For `f ∈ C²[a, b]` the piecewise linear interpolant on a partition of mesh at most
`h` differs from `f` by at most `h² max |f''| / 8`.

`f` is given as a `C²` map `ℝ → ℝ` agreeing with the continuous function on `[a, b]`, since
`C([a, b], ℝ)` carries no derivative of its own. -/
theorem equation_3_2_9 (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) (hfirst : (x 0 : ℝ) = a)
    (hlast : (x (n + 1) : ℝ) = b) {g : ℝ → ℝ} (hg : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) g)
    {f : C(Set.Icc a b, ℝ)} (hf : ∀ t : Set.Icc a b, f t = g (t : ℝ)) {h M : ℝ}
    (hmesh : ∀ i ≤ n, (x (i + 1) : ℝ) - (x i : ℝ) ≤ h)
    (hM : ∀ t ∈ Set.Icc a b, |iteratedDeriv 2 g t| ≤ M) (t : Set.Icc a b) :
    |f t - piecewiseLinearInterpCLM n x f t| ≤ h ^ 2 / 8 * M :=
  calc |f t - piecewiseLinearInterpCLM n x f t|
      = ‖(f - piecewiseLinearInterpCLM n x f) t‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖f - piecewiseLinearInterpCLM n x f‖ := ContinuousMap.norm_coe_le_norm _ t
    _ ≤ h ^ 2 / 8 * M :=
        norm_sub_piecewiseLinearInterpCLM_le hstep hfirst hlast hg hf hmesh hM

end PiecewiseLinear

/-! ### Trigonometric interpolation -/

section Trigonometric

local instance instTwoPiPos : Fact (0 < 2 * π) := Fact.mk Real.two_pi_pos

/-- A sum over the symmetric range `Icc (-n) n` in `ℤ`, split into its middle term and the pairs
`± j`. -/
private theorem sum_Icc_neg (g : ℤ → ℝ) (n : ℕ) :
    ∑ m ∈ Finset.Icc (-(n : ℤ)) n, g m = g 0 + ∑ j ∈ Finset.Icc 1 n, (g j + g (-j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : Finset.Icc (-((n : ℤ) + 1)) ((n : ℤ) + 1)
        = insert ((n : ℤ) + 1) (insert (-((n : ℤ) + 1)) (Finset.Icc (-(n : ℤ)) (n : ℤ))) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have h2 : ((n : ℤ) + 1) ∉ insert (-((n : ℤ) + 1)) (Finset.Icc (-(n : ℤ)) (n : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have h3 : (-((n : ℤ) + 1)) ∉ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    push_cast
    rw [h1, Finset.sum_insert h2, Finset.sum_insert h3, ih,
      Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n))]
    push_cast
    abel

/-- On the circle of circumference `2 π` the member of index `j ≥ 1` of the real trigonometric
system is `√2 cos (j t)`. -/
private theorem trigFun_two_pi_cos {j : ℕ} (hj : 1 ≤ j) (t : ℝ) :
    trigFun (2 * π) (j : ℤ) (↑t : AddCircle (2 * π)) = √2 * Real.cos (j * t) := by
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  have hjpos : (0 : ℤ) < (j : ℤ) := by exact_mod_cast hj
  rw [trigFun_coe_apply_of_pos hjpos]
  congr 2
  rw [show 2 * π * ((j : ℤ) : ℝ) * t = 2 * π * (((j : ℕ) : ℝ) * t) by push_cast; ring,
    mul_div_cancel_left₀ _ h2pi]

/-- On the circle of circumference `2 π` the member of index `-j` for `j ≥ 1` is `√2 sin (j t)`. -/
private theorem trigFun_two_pi_sin {j : ℕ} (hj : 1 ≤ j) (t : ℝ) :
    trigFun (2 * π) (-(j : ℤ)) (↑t : AddCircle (2 * π)) = √2 * Real.sin (j * t) := by
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  have hjneg : (-(j : ℤ)) < 0 := by omega
  rw [trigFun_coe_apply_of_neg hjneg]
  congr 2
  rw [show -(2 * π * ((-(j : ℤ) : ℤ) : ℝ) * t / (2 * π))
      = 2 * π * (((j : ℕ) : ℝ) * t) / (2 * π) by push_cast; ring,
    mul_div_cancel_left₀ _ h2pi]

/-- The value at `↑t` of a combination of the real trigonometric system of degree at most `n`. -/
private theorem sum_trigFun_two_pi_coe (d : ℤ → ℝ) (n : ℕ) (t : ℝ) :
    (∑ m ∈ Finset.Icc (-(n : ℤ)) n, d m • trigFun (2 * π) m) (↑t : AddCircle (2 * π))
      = d 0 + ∑ j ∈ Finset.Icc 1 n,
          (√2 * d j * Real.cos (j * t) + √2 * d (-j) * Real.sin (j * t)) := by
  rw [ContinuousMap.sum_apply]
  have hval : ∀ m : ℤ, (d m • trigFun (2 * π) m) (↑t : AddCircle (2 * π))
      = d m * trigFun (2 * π) m ↑t := fun _ => rfl
  simp only [hval]
  rw [sum_Icc_neg fun m => d m * trigFun (2 * π) m (↑t : AddCircle (2 * π))]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    rw [trigFun_two_pi_cos hj1, trigFun_two_pi_sin hj1]
    ring

/-- **(3.2.13).** The trigonometric polynomials of degree at most `n` are exactly the functions
`a₀ + ∑_{j=1}^{n} (aⱼ cos (j x) + bⱼ sin (j x))`. -/
theorem equation_3_2_13 {n : ℕ} {p : C(AddCircle (2 * π), ℝ)} :
    p ∈ trigPolyLE (2 * π) n ↔
      ∃ a b : ℕ → ℝ, ∀ t : ℝ,
        p (↑t : AddCircle (2 * π))
          = a 0 + ∑ j ∈ Finset.Icc 1 n, (a j * Real.cos (j * t) + b j * Real.sin (j * t)) := by
  have h2 : (√2 : ℝ) ≠ 0 := by positivity
  constructor
  · rintro hp
    obtain ⟨d, rfl⟩ := mem_trigPolyLE_iff.mp hp
    refine ⟨Function.update (fun j : ℕ => √2 * d j) 0 (d 0), fun j => √2 * d (-j), fun t => ?_⟩
    rw [sum_trigFun_two_pi_coe d n t, Function.update_self]
    refine congrArg _ (Finset.sum_congr rfl fun j hj => ?_)
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    rw [Function.update_of_ne (by omega : j ≠ 0)]
  · rintro ⟨a, b, hab⟩
    set d : ℤ → ℝ := fun m => if m = 0 then a 0
      else if 0 < m then (√2)⁻¹ * a m.toNat else (√2)⁻¹ * b (-m).toNat with hd
    have hd0 : d 0 = a 0 := by simp [hd]
    have hdval : ∀ j : ℕ, 1 ≤ j →
        d (j : ℤ) = (√2)⁻¹ * a j ∧ d (-(j : ℤ)) = (√2)⁻¹ * b j := by
      intro j hj
      have hjne : j ≠ 0 := by omega
      have hjpos : 0 < j := by omega
      exact ⟨by simp [hd, hjne, hjpos], by simp [hd, hjne]⟩
    refine mem_trigPolyLE_iff.mpr ⟨d, ContinuousMap.ext fun z => ?_⟩
    induction z using QuotientAddGroup.induction_on with
    | H t =>
      rw [hab t, sum_trigFun_two_pi_coe d n t, hd0]
      refine congrArg _ (Finset.sum_congr rfl fun j hj => ?_)
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      rw [(hdval j hj1).1, (hdval j hj1).2]
      field_simp

/-- **(3.2.16).** The evenly spaced nodes of a period are `xⱼ = j h` with `h = 2π / (2n + 1)`. -/
theorem equation_3_2_16 (n : ℕ) (j : Fin (2 * n + 1)) :
    trigInterpNode (2 * π) n j
      = (((j : ℕ) * (2 * π / (2 * (n : ℝ) + 1)) : ℝ) : AddCircle (2 * π)) := by
  rw [trigInterpNode, mul_div_assoc]

/-- **(3.2.17).** At `2n + 1` distinct nodes `0 ≤ x₀ < x₁ < ⋯ < x_{2n} < 2π` of a period, the
trigonometric interpolation problem `pₙ(xⱼ) = fⱼ` has exactly one solution `pₙ ∈ 𝕋ₙ`.

This is the substitution `z = e^{ix}` of (3.2.15), which turns the problem into complex Lagrange
interpolation at the distinct points `zⱼ = e^{ixⱼ}`; the backbone carries it out once, as the Haar
condition for `trigPolyLE`. -/
theorem equation_3_2_17 {n : ℕ} {x : Fin (2 * n + 1) → ℝ} (hmono : StrictMono x)
    (hmem : ∀ j, x j ∈ Set.Ico 0 (2 * π)) (c : Fin (2 * n + 1) → ℝ) :
    ∃! p : trigPolyLE (2 * π) n,
      ∀ j, (p : C(AddCircle (2 * π), ℝ)) ((x j : ℝ) : AddCircle (2 * π)) = c j := by
  have hmem' : ∀ j, x j ∈ Set.Ico (0 : ℝ) (0 + 2 * π) := by simpa using hmem
  have hinj : Function.Injective fun j => ((x j : ℝ) : AddCircle (2 * π)) := by
    intro i j hij
    exact hmono.injective ((AddCircle.coe_eq_coe_iff_of_mem_Ico (hmem' i) (hmem' j)).mp hij)
  exact isUnisolvent_trigPolyLE (2 * π) hinj c

/-- **(3.2.17) at the evenly spaced nodes (3.2.16).** The trigonometric interpolation operator
`trigInterpCLM` sends a continuous `2π`-periodic `f` to the trigonometric polynomial of degree at
most `n` agreeing with it at the `2n + 1` evenly spaced nodes. -/
theorem equation_3_2_17_equispaced (n : ℕ) (f : C(AddCircle (2 * π), ℝ)) :
    trigInterpCLM (2 * π) n f ∈ trigPolyLE (2 * π) n ∧
      ∀ j, trigInterpCLM (2 * π) n f (trigInterpNode (2 * π) n j)
        = f (trigInterpNode (2 * π) n j) :=
  ⟨trigInterpCLM_mem f, fun j => trigInterpCLM_apply_node f j⟩

end Trigonometric

end AtkinsonHan.Chapter03
