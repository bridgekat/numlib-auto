import Mathlib.LinearAlgebra.Matrix.PosDef
import Numlib.Analysis.Matrix.SpectralNorm
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Approximation.Hermite
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz

/-!
# Atkinson–Han §10.1: one-dimensional finite element examples

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §10.1.

The section solves the two-point boundary value problem `−u'' + u = f` on `(0,1)` by piecewise
linear and piecewise quadratic elements, and sketches the cubic Hermite element for the beam
problem (10.1.16). The finite element method itself needs `V = {v ∈ H¹(0,1) : v(0) = 0}` and
`H¹₀(0,1)`. The spaces themselves exist — `Chapter07.definition_7_2_2_multiIndex` and
`Chapter07.definition_7_2_9`, over an `Opens` of `EuclideanSpace ℝ (Fin 1)` here — but the
one-sided boundary condition cutting out `V` needs a trace (AH Theorem 7.3.10) and the ellipticity
needs the Poincaré inequality (`Chapter07.example_7_3_15`), neither of which is proved, so the
displays (10.1.1)–(10.1.6) and (10.1.13)–(10.1.15) and Exercise 10.1.1 are out of scope. What the
section says that is *not* about that space is finite-dimensional algebra, and it is what this file
holds.

## Main definitions

* `hermiteShape` — the four cubic Hermite shape functions of §10.1.3 on the reference interval
  `[0, 1]`, indexed by the node (`0` or `1`) and by the order of the derivative they are dual to.
* `hermiteShapeBasis` — those four polynomials as a basis of `ℙ₃`.

## Main results

* `exercise_10_1_2` — static condensation: the Schur complement of a symmetric positive definite
  block matrix is symmetric positive definite, so the condensed system (10.1.15) inherits the
  property of the full one.
* `eval_iterate_derivative_hermiteShape` — the sixteen interpolation conditions of §10.1.3 in one
  statement.
* `eq_hermiteShape_combination` — the Hermite representation `p = Σ p⁽ʲ⁾(i) · hermiteShape i j` of a
  cubic, which is what makes the four shape functions a basis.
* `exercise_10_1_3` — a `C¹` piecewise quadratic supported on two neighbouring elements is zero, so
  a conforming finite element method for the beam problem needs degree at least `3`.
* `stiffnessMatrix` and `equation_10_1_9` — the stiffness matrix `h⁻¹ tridiag(−1, 2, −1)` of the
  piecewise linear element, and its spectral condition number `(1 + cos πh)/(1 − cos πh)`.

## Deviations from the book

Exercise 10.1.2 is stated for an arbitrary symmetric positive definite block matrix over an
arbitrary pair of index types, since neither the finite element origin of the blocks nor their size
plays any part. The book writes the off-diagonal blocks as `M₁₂` and `M₂₁ = M₁₂ᵀ`; over `ℝ` the
conjugate transpose `ᴴ` of Mathlib's `Matrix.fromBlocks` lemmas *is* the transpose, and it is what
the statement uses.

Exercise 10.1.3 is stated as the two-element fact its proof turns on rather than as a claim about a
space of piecewise polynomials: two quadratics on `[a, b]` and `[b, c]` that vanish to second order
at the outer ends and match in value and slope at `b` are both zero. The surrounding claim
`dim V_h = (p − 1)N − 2` is a count in a function space and is not formalized.

## Not formalized here

**The finite element systems** (10.1.1)–(10.1.6), (10.1.13)–(10.1.15) and Exercise 10.1.1, whose
space is `V = {v ∈ H¹(0,1) : v(0) = 0}`.  This is the softest of the chapter's Sobolev skips, and
the space is no longer what is missing: membership of `H¹(0,1)` is
`Chapter07.definition_7_2_2_multiIndex` over an `Opens` of `EuclideanSpace ℝ (Fin 1)`, and the
backbone's `SobolevMultiIndex` (`Numlib/Analysis/Sobolev/MultiIndex.lean`) is that space as a
type, complete and, at `p = 2`, carrying the inner product of Corollary 7.2.4.  What `V` needs on
top of it is the one-dimensional reading the book uses: the embedding `H¹(0,1) ↪ C[0,1]` that
gives `v(0)` a meaning (AH Theorem 7.3.7) and the Poincaré inequality that makes the seminorm a
norm (AH Theorem 7.3.13), both of them open, together with the density of the continuous piecewise
linears in `V`.  The classical route to the embedding is the converse half of the fundamental
theorem of calculus — `f(b) − f(a) = ∫ f'` for an absolutely continuous `f` whose derivative is
only an a.e. one — which Mathlib does not have: it has `AbsolutelyContinuousOnInterval` with its
almost-everywhere differentiability and the direction "an interval integral is absolutely
continuous", and not the converse.

**(10.1.9)** needs none of that: it is stated and proved below, from the eigenvalues
`λ_k = 2 − 2 cos(k π h)` (`Matrix.symmTridiagonalToeplitz_hasEigenvalue_iff`) and the backbone's
spectral-norm bridge `Matrix.IsHermitian.l2_opNorm_eq`.
-/

open Polynomial Real
open scoped Matrix Matrix.Norms.L2Operator NormedRing

namespace AtkinsonHan.Chapter10

/-! ### Exercise 10.1.2: static condensation -/

/-- **Exercise 10.1.2.**  If the block matrix `[[M₁₁, M₁₂], [M₁₂ᵀ, D₂₂]]` is symmetric positive
definite, so is its Schur complement `M₁₁ − M₁₂ D₂₂⁻¹ M₁₂ᵀ`, the coefficient matrix of the condensed
system (10.1.15) that remains after the interior unknowns are eliminated.

Positive definiteness is the identity `Matrix.schur_complement_eq₂₂` read at
`y = −D₂₂⁻¹ M₁₂ᵀ x`, which annihilates the first summand and leaves the Schur complement's quadratic
form at `x`; the vector `(x, y)` is nonzero as soon as `x` is. Mathlib's
`Matrix.PosSemidef.fromBlocks₂₂` is the corresponding statement for positive *semi*definiteness. -/
theorem exercise_10_1_2 {m n : Type*} [Finite m] [Fintype n] [DecidableEq n]
    {M₁₁ : Matrix m m ℝ} {M₁₂ : Matrix m n ℝ} {D₂₂ : Matrix n n ℝ} [Invertible D₂₂]
    (h : (Matrix.fromBlocks M₁₁ M₁₂ M₁₂ᴴ D₂₂).PosDef) :
    (M₁₁ - M₁₂ * D₂₂⁻¹ * M₁₂ᴴ).PosDef := by
  have : Fintype m := Fintype.ofFinite m
  have hblocks := Matrix.isHermitian_fromBlocks_iff.mp h.isHermitian
  have hD : D₂₂.IsHermitian := hblocks.2.2.2
  have hherm : (M₁₁ - M₁₂ * D₂₂⁻¹ * M₁₂ᴴ).IsHermitian :=
    hblocks.1.sub (Matrix.isHermitian_mul_mul_conjTranspose _ hD.inv)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hherm fun x hx => ?_
  set y : n → ℝ := -((D₂₂⁻¹ * M₁₂ᴴ) *ᵥ x) with hy
  have hkey := Matrix.schur_complement_eq₂₂ M₁₁ M₁₂ x y hD
  have hzero : (D₂₂⁻¹ * M₁₂ᴴ) *ᵥ x + y = 0 := by rw [hy]; abel
  rw [hzero] at hkey
  simp only [dotProduct_zero, zero_add, star_zero, Matrix.zero_vecMul] at hkey
  have hne : (Sum.elim x y) ≠ 0 := fun hc => hx (funext fun i => by
    simpa using congrFun hc (Sum.inl i))
  have hpos := h.dotProduct_mulVec_pos hne
  rw [Matrix.dotProduct_mulVec, hkey] at hpos
  rwa [Matrix.dotProduct_mulVec]

/-! ### The cubic Hermite element of §10.1.3 -/

/-- **The cubic Hermite shape functions** on the reference interval `[0, 1]` of §10.1.3:

  `Φ₀ = (1 + 2x)(1 − x)²`,  `Φ₁ = (3 − 2x)x²`,  `Ψ₀ = x(1 − x)²`,  `Ψ₁ = −(1 − x)x²`.

`hermiteShape i j` is the function dual to the functional "`j`-th derivative at the node `i`", so
`hermiteShape i 0` is the book's `Φᵢ` and `hermiteShape i 1` its `Ψᵢ`, for `i = 0, 1`. -/
noncomputable def hermiteShape (i j : Fin 2) : ℝ[X] :=
  ![![(1 + 2 * X) * (1 - X) ^ 2, X * (1 - X) ^ 2],
    ![(3 - 2 * X) * X ^ 2, -((1 - X) * X ^ 2)]] i j

/-- **The sixteen interpolation conditions of §10.1.3**, in one statement: the `j'`-th derivative of
`hermiteShape i j` at the node `i'` is `1` when `(i', j') = (i, j)` and `0` otherwise. Reading the
four cases of `j = j' = 0` gives `Φ₀(0) = 1, Φ₀(1) = 0, Φ₁(0) = 0, Φ₁(1) = 1`, and so on. -/
theorem eval_iterate_derivative_hermiteShape (i j i' j' : Fin 2) :
    (derivative^[(j' : ℕ)] (hermiteShape i j)).eval ((i' : ℕ) : ℝ)
      = if i = i' ∧ j = j' then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp [hermiteShape, derivative_pow] <;> ring_nf

/-- Every cubic Hermite shape function is a cubic: it lies in `ℙ₃ = Polynomial.degreeLT ℝ 4`. -/
theorem hermiteShape_mem_degreeLT (i j : Fin 2) : hermiteShape i j ∈ degreeLT ℝ 4 := by
  rw [mem_degreeLT]
  have h : (hermiteShape i j).degree < 4 := by
    fin_cases i <;> fin_cases j <;>
      · simp only [hermiteShape, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
          Fin.zero_eta, Fin.mk_one]
        compute_degree!
  exact_mod_cast h

/-- The two nodes `0` and `1` of the reference interval are distinct. -/
private theorem injective_node : Function.Injective (fun i : Fin 2 => ((i : ℕ) : ℝ)) := by
  intro i i'
  fin_cases i <;> fin_cases i' <;> simp_all

/-- **The Hermite representation of a cubic**: every `p ∈ ℙ₃` is recovered from its value and slope
at the two ends of the reference interval,

  `p = Σᵢ p(i) Φᵢ + Σᵢ p'(i) Ψᵢ`.

It is the unisolvence of two-point Hermite interpolation on `[0, 1]`: the difference between `p` and
the right-hand side is a cubic all four of whose Hermite data vanish, and a nonzero one cannot have
four roots counted with multiplicity
(`Hermite.eq_zero_of_forall_eval_iterate_derivative_eq_zero`). -/
theorem eq_hermiteShape_combination {p : ℝ[X]} (hp : p ∈ degreeLT ℝ 4) :
    p = ∑ i : Fin 2, ∑ j : Fin 2,
      C ((derivative^[(j : ℕ)] p).eval ((i : ℕ) : ℝ)) * hermiteShape i j := by
  set r : ℝ[X] := ∑ i : Fin 2, ∑ j : Fin 2,
    C ((derivative^[(j : ℕ)] p).eval ((i : ℕ) : ℝ)) * hermiteShape i j with hr
  have hmem : r ∈ degreeLT ℝ 4 := by
    rw [hr]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (hermiteShape_mem_degreeLT i j)
  have hdata : ∀ i' : Fin 2, ∀ j' : Fin 2,
      (derivative^[(j' : ℕ)] r).eval ((i' : ℕ) : ℝ)
        = (derivative^[(j' : ℕ)] p).eval ((i' : ℕ) : ℝ) := by
    intro i' j'
    rw [hr]
    simp only [iterate_derivative_sum, eval_finsetSum, iterate_derivative_C_mul, eval_mul, eval_C,
      eval_iterate_derivative_hermiteShape]
    rw [Finset.sum_eq_single i']
    · rw [Finset.sum_eq_single j']
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    · intro i _ hi
      exact Finset.sum_eq_zero fun j _ => by simp [hi]
    · simp
  have hzero : p - r = 0 := by
    refine Hermite.eq_zero_of_forall_eval_iterate_derivative_eq_zero (n := 2) (M := 4)
      (x := fun i : Fin 2 => ((i : ℕ) : ℝ)) injective_node (m := fun _ => 1) (by decide) ?_ ?_
    · exact lt_of_le_of_lt (degree_sub_le _ _)
        (max_lt (mem_degreeLT.mp hp) (mem_degreeLT.mp hmem))
    · intro i j hj
      rw [iterate_derivative_sub, eval_sub, sub_eq_zero]
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · simpa using (hdata i 0).symm
      · simpa using (hdata i 1).symm
  exact sub_eq_zero.mp hzero

/-- **The cubic Hermite shape functions form a basis of `ℙ₃`.**  Spanning is
`eq_hermiteShape_combination`; independence is the sixteen conditions read backwards, since applying
the functional "`j`-th derivative at `i`" to a vanishing combination picks out its `(i, j)`
coefficient. -/
noncomputable def hermiteShapeBasis : Module.Basis (Fin 2 × Fin 2) ℝ (degreeLT ℝ 4) :=
  Module.Basis.mk (v := fun k => ⟨hermiteShape k.1 k.2, hermiteShape_mem_degreeLT k.1 k.2⟩)
    (by
      rw [Fintype.linearIndependent_iff]
      intro c hc k
      have hc' : ∑ k' : Fin 2 × Fin 2, c k' • hermiteShape k'.1 k'.2 = 0 := by
        simpa [Submodule.coe_sum] using congrArg Subtype.val hc
      have h := congrArg (fun q : ℝ[X] => (derivative^[(k.2 : ℕ)] q).eval ((k.1 : ℕ) : ℝ)) hc'
      simpa [smul_eq_C_mul, iterate_derivative_sum, eval_finsetSum, iterate_derivative_C_mul,
        eval_iterate_derivative_hermiteShape, ← Prod.ext_iff, Finset.sum_ite_eq'] using h)
    (by
      rintro ⟨p, hp⟩ -
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun k => (derivative^[(k.2 : ℕ)] p).eval ((k.1 : ℕ) : ℝ), Subtype.ext ?_⟩
      simp only [Submodule.coe_sum, SetLike.val_smul, smul_eq_C_mul, Fintype.sum_prod_type]
      exact (eq_hermiteShape_combination hp).symm)

/-! ### Exercise 10.1.3: no two-element `C¹` piecewise quadratic bump -/

/-- A quadratic with a double root at `a` is `α (x − a)²`. The difference between `p` and
`p₂ (x − a)²` has degree less than `2` and still vanishes to second order at `a`, hence is zero. -/
private theorem exists_eq_C_mul_sq {p : ℝ[X]} (hp : p ∈ degreeLT ℝ 3) {a : ℝ}
    (h0 : p.eval a = 0) (h1 : (derivative p).eval a = 0) :
    ∃ α : ℝ, p = C α * (X - C a) ^ 2 := by
  refine ⟨p.coeff 2, ?_⟩
  set q : ℝ[X] := p - C (p.coeff 2) * (X - C a) ^ 2 with hq
  have hcoeff2 : ((X - C a) ^ 2 : ℝ[X]).coeff 2 = 1 := by
    have h := ((monic_X_sub_C a).pow 2).coeff_natDegree
    rwa [natDegree_pow, natDegree_X_sub_C] at h
  have hqdeg : q ∈ degreeLT ℝ 2 := by
    rw [mem_degreeLT, degree_lt_iff_coeff_zero]
    intro m hm
    rw [hq, coeff_sub, coeff_C_mul]
    rcases eq_or_lt_of_le (show (2 : ℕ) ≤ m by exact_mod_cast hm) with rfl | hm2
    · rw [hcoeff2, mul_one, sub_self]
    · have hp2 : p.coeff m = 0 := by
        have h := mem_degreeLT.mp hp
        rw [degree_lt_iff_coeff_zero] at h
        exact h m (by exact_mod_cast (by omega : 3 ≤ m))
      rw [hp2, coeff_eq_zero_of_natDegree_lt (n := m) (by simp; omega), mul_zero, sub_zero]
  have hq0 : q.eval a = 0 := by simp [hq, h0]
  have hq1 : (derivative q).eval a = 0 := by simp [hq, derivative_pow, h1]
  have hqz : q = 0 := by
    refine Hermite.eq_zero_of_forall_eval_iterate_derivative_eq_zero (n := 1) (M := 2)
      (x := fun _ : Fin 1 => a) (fun i j _ => Subsingleton.elim i j) (m := fun _ => 1)
      (by decide) (mem_degreeLT.mp hqdeg) fun i j hj => ?_
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · simpa using hq0
    · simpa using hq1
  rw [hq] at hqz
  exact sub_eq_zero.mp hqz

/-- **Exercise 10.1.3.**  A `C¹` piecewise quadratic on a partition of `[0, 1]` has no basis
function whose support is exactly two neighbouring elements: two quadratics `p` on `[a, b]` and `q`
on `[b, c]` that vanish together with their derivatives at the outer ends `a` and `c`, and that
match in value and in slope at the shared node `b`, are both zero.

Consequently a conforming finite element method for the beam problem (10.1.16), whose space sits
inside `H²(0,1)` and so needs `C¹` elements, cannot use piecewise quadratics: it needs degree at
least `3`, which is what the cubic Hermite element of `hermiteShape` supplies.

By `exists_eq_C_mul_sq`, `p = α (x − a)²` and `q = β (x − c)²`. Matching the values at `b` gives
`α (b − a)² = β (b − c)²` and matching the slopes gives `α (b − a) = β (b − c)`; eliminating `α`
leaves `β (b − c)(c − a) = 0`, and neither factor vanishes. -/
theorem exercise_10_1_3 {a b c : ℝ} (hab : a < b) (hbc : b < c) {p q : ℝ[X]}
    (hp : p ∈ degreeLT ℝ 3) (hq : q ∈ degreeLT ℝ 3)
    (hpa : p.eval a = 0) (hpa' : (derivative p).eval a = 0)
    (hqc : q.eval c = 0) (hqc' : (derivative q).eval c = 0)
    (hval : p.eval b = q.eval b) (hslope : (derivative p).eval b = (derivative q).eval b) :
    p = 0 ∧ q = 0 := by
  obtain ⟨α, rfl⟩ := exists_eq_C_mul_sq hp hpa hpa'
  obtain ⟨β, rfl⟩ := exists_eq_C_mul_sq hq hqc hqc'
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, derivative_mul, derivative_C,
    derivative_pow, derivative_sub, derivative_X, zero_mul, zero_add, Nat.cast_ofNat,
    Nat.add_one_sub_one, pow_one, sub_zero, mul_one] at hval hslope
  -- matching the slopes at `b`, with the common factor `2` cancelled
  have h1 : α * (b - a) = β * (b - c) := by linarith
  -- eliminating `α` between the two matching conditions
  have h2 : β * (b - c) * (c - a) = 0 := by linear_combination (-(b - a)) * h1 + hval
  have hβ : β = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h (sub_ne_zero.mpr hbc.ne)
    · exact absurd h (sub_ne_zero.mpr (by linarith : c ≠ a))
  have hα : α = 0 := by
    rw [hβ, zero_mul] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h (sub_ne_zero.mpr hab.ne')
  rw [hα, hβ]
  simp

/-! ### (10.1.9): the condition number of the stiffness matrix -/

/-- **(10.1.9)**, the stiffness matrix of the piecewise linear element for the two-point boundary
value problem on `(0, 1)` with `N` uniform elements of length `h = 1/N`:

  `A = h⁻¹ tridiag(−1, 2, −1)` of order `N − 1`.

It is indexed here by its order `n = N − 1`, so that `h = 1/(n + 1)` and `h⁻¹ = n + 1`; the entry
`A i j = h⁻¹ ∫₀¹ φ_i' φ_j'` of the book is the same matrix. -/
noncomputable def stiffnessMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  ((n : ℝ) + 1) • Matrix.symmTridiagonalToeplitz n (-1) 2

/-- **(10.1.9)**: the spectral condition number of the stiffness matrix is

  `Cond₂(A) = ‖A‖₂ ‖A⁻¹‖₂ = (1 + cos πh) / (1 − cos πh)`,

which is `O(h⁻²)` as `h = 1/(n + 1) → 0`.

The eigenvalues of `tridiag(−1, 2, −1)` are `2 − 2 cos(kπh)` for `1 ≤ k ≤ n`, extreme at `k = 1`
and `k = n`, so the spectrum is enclosed in `[2 − 2 cos πh, 2 + 2 cos πh]` with both ends attained.
`Matrix.IsHermitian.l2_opNorm_eq` and `Matrix.IsHermitian.l2_opNorm_inv_eq` turn that into the two
norms, and the factor `h⁻¹` cancels from the ratio by `NormedRing.condNumber_smul`. -/
theorem equation_10_1_9 (n : ℕ) (hn : 0 < n) :
    κ (stiffnessMatrix n)
      = (1 + Real.cos (π / ((n : ℝ) + 1))) / (1 - Real.cos (π / ((n : ℝ) + 1))) := by
  rw [stiffnessMatrix]
  set c : ℝ := Real.cos (π / ((n : ℝ) + 1)) with hc
  set B : Matrix (Fin n) (Fin n) ℝ := Matrix.symmTridiagonalToeplitz n (-1) 2 with hB
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hhalf : 0 < Real.sin (π / (2 * ((n : ℝ) + 1))) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hcos : c = 1 - 2 * Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2 := by
    rw [hc, ← Real.cos_two_mul_eq_one_sub]
    congr 1
    field_simp
  have hclt : c < 1 := by rw [hcos]; nlinarith
  have hcpos : 0 ≤ c := by
    rw [hc]
    have hpi := Real.pi_pos
    refine Real.cos_nonneg_of_mem_Icc ⟨by linarith [div_pos hpi hn1], ?_⟩
    rw [div_le_iff₀ hn1]
    nlinarith [Nat.one_le_cast (α := ℝ) |>.2 hn]
  have hm : (0 : ℝ) < 2 - 2 * c := by linarith
  have hbdd := Matrix.isSymmetricBoundedBy_symmTridiagonalToeplitz n (-1) 2
  simp only [abs_neg, abs_one, mul_one] at hbdd
  rw [← hc, ← hB] at hbdd
  have hHerm : B.IsHermitian := Matrix.symmTridiagonalToeplitz_isHermitian (-1) 2
  have hIcc : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toEuclideanLin B) μ →
      μ ∈ Set.Icc (2 - 2 * c) (2 + 2 * c) := fun μ hμ => by
    simpa using hbdd.re_mem_Icc_of_hasEigenvalue hμ
  have hmin : Module.End.HasEigenvalue (Matrix.toEuclideanLin B) (2 - 2 * c) := by
    rw [hB, Matrix.symmTridiagonalToeplitz_hasEigenvalue_iff]
    refine ⟨⟨0, hn⟩, ?_⟩
    push_cast
    rw [hc]
    ring_nf
  have hmax : Module.End.HasEigenvalue (Matrix.toEuclideanLin B) (2 + 2 * c) := by
    rw [hB, Matrix.symmTridiagonalToeplitz_hasEigenvalue_iff]
    refine ⟨⟨n - 1, Nat.sub_lt hn one_pos⟩, ?_⟩
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      have h1 : (1 : ℕ) ≤ n := hn
      push_cast [Nat.cast_sub h1]
      ring
    have hsub : (n : ℝ) * π / ((n : ℝ) + 1) = π - π / ((n : ℝ) + 1) := by field_simp; ring
    rw [hcast, hc, hsub, Real.cos_pi_sub]
    ring
  have hnormB : ‖B‖ = 2 + 2 * c := by
    refine hHerm.l2_opNorm_eq (fun μ hμ => ?_) ⟨2 + 2 * c, hmax, by
      rw [RCLike.re_to_real, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 + 2 * c)]⟩
    obtain ⟨h1, h2⟩ := hIcc μ hμ
    rw [RCLike.re_to_real, abs_le]
    constructor <;> linarith
  have hnormBinv : ‖B⁻¹‖ = (2 - 2 * c)⁻¹ := by
    refine hHerm.l2_opNorm_inv_eq hm (fun μ hμ => ?_)
      ⟨2 - 2 * c, hmin, by
        rw [RCLike.re_to_real, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 - 2 * c)]⟩
    obtain ⟨h1, h2⟩ := hIcc μ hμ
    rw [RCLike.re_to_real, abs_of_nonneg (by linarith)]
    linarith
  rw [NormedRing.condNumber_smul hn1.ne' B, NormedRing.condNumber,
    ← Matrix.nonsing_inv_eq_ringInverse, hnormB, hnormBinv]
  have h2 : (2 : ℝ) - 2 * c ≠ 0 := by linarith
  have h1 : (1 : ℝ) - c ≠ 0 := by linarith
  field_simp

end AtkinsonHan.Chapter10
