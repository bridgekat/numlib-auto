import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Numlib.Approximation.BestApprox
import NumlibSurface.AtkinsonHan.Chapter14.Section01

/-!
# Atkinson–Han §14.2: orthogonal polynomials in several variables

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §14.2.

The section works in `L²` of the unit ball for the weighted inner product (14.2.11), so everything
here is stated for a measure `μ` on `ℝ^d` satisfying `Approximation.IsMvWeight` — every polynomial
square integrable, and no nonzero polynomial vanishing almost everywhere — and instantiated at the
volume of the unit ball by `isMvWeight_ballVolume`. The book's standard case is the weight `w = 1`;
a positive weight `w` gives the measure `w dx`, which is another such `μ`, so (14.2.11) needs no
separate treatment.

`V_n^d` is `orthPolySpace`, the `n`-th orthogonal component of the chain `Π_0^d ⊆ Π_1^d ⊆ ⋯` inside
`L²(μ)`, and Lemma 14.2.1 and the dimension count are the backbone's
`Numlib.Approximation.OrthogonalDecomposition` applied to that chain. Theorem 14.2.3 is stated as
the membership `x_j φ ∈ V_{n−1} ⊔ V_n ⊔ V_{n+1}` together with the uniqueness of the resulting
three-term decomposition, which is the coordinate-free content of "there are unique matrices
`A_{n,j}`, `B_{n,j}` and `C_{n,j}`"; the matrices themselves are the expansions of the three
components in a basis of each, and are not written.

## Main results

* `isMvWeight_ballVolume` — (14.2.11): the volume of `𝔹_d` is a weight in the sense above.
* `lemma_14_2_1` — Lemma 14.2.1: `Π_n^d = V_0^d ⊕ ⋯ ⊕ V_n^d`, orthogonally.
* `finrank_orthPolySpace`, `finrank_orthPolySpace_two` — `dim V_n^d = C(n + d − 1, d − 1)`, and
  `dim V_n^2 = n + 1`.
* `theorem_14_2_3`, `theorem_14_2_3_unique` — the triple recursion relation.
* `exercise_14_2_1` — (14.2.9)–(14.2.10): `(x_j p, q) = (p, x_j q)`, which is
  `C_{n+1,j} = A_{n,j}^T` for an orthonormal basis.
* `equation_14_2_12` — the orthogonal projection `P_n` as a sum over the components, and as the
  best `L²` approximation from `Π_n^d`.
* `equation_14_2_13` — the Lebesgue lemma for a bounded projection of `C(𝔹_d)` onto `Π_n^d`.

## Not formalized here

* **Example 14.2.2**, the ridge polynomials `φ_{n,k}(x, y) = (1/√π) U_n(x cos kh + y sin kh)` as an
  orthonormal basis of `V_n^2`. The book gives no proof, citing Logan and Shepp. Nothing is missing
  but the proof — `Polynomial.Chebyshev.U` and polar-coordinate integration are both in Mathlib —
  and every result below is stated without a basis, so nothing waits on it.
* **(14.2.14)–(14.2.15)**, the closed form of the reproducing kernel `G_n` as an integral of a
  Jacobi polynomial `P_n^{(3/2,1/2)}`. Mathlib has neither Jacobi nor Gegenbauer polynomials.
* **Theorem 14.2.4**, `‖P_n‖_{C(𝔹₂)→C(𝔹₂)} = O(n)`, and **Theorem 14.2.5**, which is (14.2.13)
  combined with 14.2.4 and Theorem 14.1.1. The book quotes 14.2.4 from Xu; the estimate is on the
  Jacobi polynomials above, and 14.1.1 is quoted from Ragozin and needs spherical harmonics.
* **Exercise 14.2.4**, the sphere–disk integral identity, which needs the surface measure on `S²`.
-/

open Approximation MeasureTheory Module

namespace AtkinsonHan.Chapter14

section Ball

variable (d : ℕ)

/-- `𝔹_d`, the closed unit ball of `ℝ^d`, written as a set of coordinate vectors so that
`MvPolynomial.eval` applies to its elements directly. -/
def unitBall : Set (Fin d → ℝ) := {x | ∑ i, x i ^ 2 ≤ 1}

theorem mem_unitBall_iff {x : Fin d → ℝ} : x ∈ unitBall d ↔ ∑ i, x i ^ 2 ≤ 1 := Iff.rfl

theorem isClosed_unitBall : IsClosed (unitBall d) :=
  isClosed_le (by fun_prop) continuous_const

theorem unitBall_subset_closedBall : unitBall d ⊆ Metric.closedBall 0 1 := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have h : x i ^ 2 ≤ 1 :=
    le_trans (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)) hx
  rw [Real.norm_eq_abs]
  nlinarith [abs_nonneg (x i), sq_abs (x i)]

/-- The unit ball is compact: it is closed, and contained in the cube of side two. -/
theorem isCompact_unitBall : IsCompact (unitBall d) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_unitBall d)
    (Metric.isBounded_closedBall.subset (unitBall_subset_closedBall d))

/-- The unit ball has nonempty interior, which is what makes the `L²` inner product of §14.2
definite on polynomials. -/
theorem zero_mem_interior_unitBall : (0 : Fin d → ℝ) ∈ interior (unitBall d) := by
  have hopen : IsOpen {x : Fin d → ℝ | ∑ i, x i ^ 2 < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hsub : {x : Fin d → ℝ | ∑ i, x i ^ 2 < 1} ⊆ interior (unitBall d) :=
    interior_maximal (fun _ hx => le_of_lt (Set.mem_ofPred_eq ▸ hx)) hopen
  exact hsub (by simp)

/-- **(14.2.11)** for the standard weight: the volume of the unit ball is a measure for which the
`L²` theory of polynomials is faithful, so the inner product `(f, g) = ∫_{𝔹_d} f g` of §14.2 is
definite on `Π_n^d`. The weighted inner product `(f, g)_w = ∫_{𝔹_d} w f g` of (14.2.11) is the same
statement for the measure `w dx`, which is why every result below is stated for an arbitrary
`Approximation.IsMvWeight`. -/
theorem isMvWeight_ballVolume : IsMvWeight (volume.restrict (unitBall d)) :=
  isMvWeight_restrict (isCompact_unitBall d) (isClosed_unitBall d).measurableSet
    (isCompact_unitBall d).measure_lt_top.ne ⟨0, zero_mem_interior_unitBall d⟩

end Ball

variable {d : ℕ} {μ : Measure (Fin d → ℝ)}

/-- `V_n^d`, the polynomials of degree at most `n` that are `L²(μ)`-orthogonal to those of degree at
most `n − 1`, with `V_0^d` the constants: the `n`-th orthogonal component of the chain `Π_0^d ⊆
Π_1^d ⊆ ⋯`. -/
noncomputable abbrev orthPolySpace (hw : IsMvWeight μ) (n : ℕ) : Submodule ℝ (Lp ℝ 2 μ) :=
  orthogonalComponent hw.polyLE n

variable (hw : IsMvWeight μ)

/-- `V_0^d` is the space of constants. -/
theorem orthPolySpace_zero : orthPolySpace hw 0 = hw.polyLE 0 := rfl

/-- The book's defining property of `V_n^d`: it consists of the elements of `Π_n^d` orthogonal to
every element of `Π_{n−1}^d`. -/
theorem mem_orthPolySpace_succ_iff {n : ℕ} {f : Lp ℝ 2 μ} :
    f ∈ orthPolySpace hw (n + 1) ↔ f ∈ hw.polyLE (n + 1) ∧ ∀ g ∈ hw.polyLE n, inner ℝ g f = 0 := by
  rw [orthPolySpace, orthogonalComponent_succ, Submodule.mem_inf, and_comm,
    Submodule.mem_orthogonal]

theorem orthPolySpace_le (n : ℕ) : orthPolySpace hw n ≤ hw.polyLE n :=
  orthogonalComponent_le _ n

/-- **Lemma 14.2.1**: `Π_n^d = V_0^d ⊕ V_1^d ⊕ ⋯ ⊕ V_n^d`. This clause is the spanning half, that
`Π_n^d` is the sup of the components of index at most `n`; `lemma_14_2_1_isOrtho` and
`lemma_14_2_1_iSupIndep` are the two halves that make the sum direct and orthogonal. -/
theorem lemma_14_2_1 (n : ℕ) :
    (Finset.range (n + 1)).sup (orthPolySpace hw) = hw.polyLE n :=
  finsetSup_orthogonalComponent hw.monotone_polyLE (fun _ => inferInstance) n

/-- **Lemma 14.2.1**, the orthogonality half: `V_m^d ⟂ V_n^d` for `m ≠ n`. -/
theorem lemma_14_2_1_isOrtho {m n : ℕ} (h : m ≠ n) : orthPolySpace hw m ⟂ orthPolySpace hw n :=
  orthogonalComponent_isOrtho hw.monotone_polyLE h

/-- **Lemma 14.2.1**, the directness half: the components are independent. -/
theorem lemma_14_2_1_iSupIndep : iSupIndep (orthPolySpace hw) :=
  iSupIndep_orthogonalComponent hw.monotone_polyLE

/-- §14.2: `dim V_n^d = dim P_n^d = C(n + d − 1, d − 1)`, the dimension of the space of homogeneous
polynomials of degree `n` in `d` variables. Proved from Lemma 14.2.1 and the two dimension counts by
Pascal's rule, without exhibiting a basis; the case `n = 0` is `dim V_0^d = dim Π_0^d = 1`. -/
theorem finrank_orthPolySpace (hd : 1 ≤ d) (n : ℕ) :
    finrank ℝ (orthPolySpace hw (n + 1)) = (n + d).choose (d - 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hadd : finrank ℝ (orthPolySpace hw (n + 1)) +
      (n + Fintype.card (Fin (e + 1))).choose (Fintype.card (Fin (e + 1))) =
      (n + 1 + Fintype.card (Fin (e + 1))).choose (Fintype.card (Fin (e + 1))) :=
    hw.finrank_orthogonalComponent_add n
  have hpascal : (n + e + 1 + 1).choose (e + 1)
      = (n + e + 1).choose e + (n + e + 1).choose (e + 1) := Nat.choose_succ_succ (n + e + 1) e
  simp only [Fintype.card_fin] at hadd
  rw [show n + 1 + (e + 1) = n + e + 1 + 1 by omega, show n + (e + 1) = n + e + 1 by omega] at hadd
  rw [show n + (e + 1) = n + e + 1 by omega, Nat.add_sub_cancel]
  omega

/-- §14.2 in the plane: `dim V_n^2 = n + 1`. -/
theorem finrank_orthPolySpace_two {μ : Measure (Fin 2 → ℝ)} (hw : IsMvWeight μ) (n : ℕ) :
    finrank ℝ (orthPolySpace hw n) = n + 1 := by
  cases n with
  | zero =>
    rw [show orthPolySpace hw 0 = hw.polyLE 0 from rfl, hw.finrank_polyLE 0]
    simp
  | succ n => simpa using finrank_orthPolySpace hw one_le_two n

/-- (14.2.9)–(14.2.10), and **Exercise 14.2.1**, coordinate-free: multiplication by a coordinate is
symmetric for the inner product, `(x_j p, q) = (p, x_j q)`. Taking `p ∈ V_n^d` and `q ∈ V_{n+1}^d`
and expanding both sides in a basis of each is `A_{n,j} H_{n+1} = H_n C_{n+1,j}^T`, which for an
orthonormal basis reads `C_{n+1,j} = A_{n,j}^T`. -/
theorem exercise_14_2_1 (j : Fin d) (p q : MvPolynomial (Fin d) ℝ) :
    inner ℝ (hw.toL2 (MvPolynomial.X j * p)) (hw.toL2 q) =
      inner ℝ (hw.toL2 p) (hw.toL2 (MvPolynomial.X j * q)) :=
  hw.inner_toL2_mul_left _ p q

/-- **Theorem 14.2.3**, the triple recursion relation, in membership form: multiplication by the
coordinate `x_j` carries `V_n^d` into `V_{n−1}^d ⊔ V_n^d ⊔ V_{n+1}^d`. The only analytic input is
`exercise_14_2_1`, the symmetry of multiplication: for `q` of degree at most `n − 2` one has
`(x_j p, q) = (p, x_j q) = 0` because `x_j q` still has degree at most `n − 1`. This is the
multivariate form of the three-term recursion for orthogonal polynomials in one variable. -/
theorem theorem_14_2_3 {n : ℕ} {j : Fin d} {p : MvPolynomial (Fin d) ℝ}
    (hp : hw.toL2 p ∈ orthPolySpace hw n) :
    hw.toL2 (MvPolynomial.X j * p) ∈ (Finset.Icc (n - 1) (n + 1)).sup (orthPolySpace hw) := by
  have hdeg : p.totalDegree ≤ n := by
    obtain ⟨r, hr, hre⟩ := hw.mem_polyLE_iff.1 (orthPolySpace_le hw n hp)
    rwa [hw.toL2_injective hre] at hr
  have hmul : ∀ r : MvPolynomial (Fin d) ℝ,
      (MvPolynomial.X j * r).totalDegree ≤ 1 + r.totalDegree :=
    fun r => le_trans (MvPolynomial.totalDegree_mul _ _) (by simp)
  refine mem_finsetSup_Icc_of_mem hw.monotone_polyLE (fun _ => inferInstance)
    (hw.toL2_mem_polyLE ((hmul p).trans (by omega))) fun k hk g hg => ?_
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨q, hq, rfl⟩ := hw.mem_polyLE_iff.1 hg
  rw [← exercise_14_2_1 hw j q p]
  exact ((mem_orthPolySpace_succ_iff hw).1 hp).2 _
    (hw.toL2_mem_polyLE ((hmul q).trans (by omega)))

/-- **Theorem 14.2.3**, uniqueness: the three-term decomposition of `x_j φ` is unique. This is the
coordinate-free content of "there are unique matrices `A_{n,j}`, `B_{n,j}` and `C_{n,j}`" — the
matrices are the expansions of the three components in a basis of each — and it holds for any
element of `V_m^d ⊔ V_{m+1}^d ⊔ V_{m+2}^d`, being nothing but the orthogonality of distinct
components. -/
theorem theorem_14_2_3_unique {m : ℕ} {a b c a' b' c' : Lp ℝ 2 μ}
    (ha : a ∈ orthPolySpace hw m) (hb : b ∈ orthPolySpace hw (m + 1))
    (hc : c ∈ orthPolySpace hw (m + 2)) (ha' : a' ∈ orthPolySpace hw m)
    (hb' : b' ∈ orthPolySpace hw (m + 1)) (hc' : c' ∈ orthPolySpace hw (m + 2))
    (h : a + b + c = a' + b' + c') : a = a' ∧ b = b' ∧ c = c' := by
  have hz : (a - a') + (b - b') + (c - c') = 0 := by
    rw [show a - a' + (b - b') + (c - c') = a + b + c - (a' + b' + c') by abel, h, sub_self]
  have key : ∀ {i k : ℕ} {u v : Lp ℝ 2 μ}, i ≠ k → u ∈ orthPolySpace hw i →
      v ∈ orthPolySpace hw k → inner ℝ u v = 0 := fun hik hu hv =>
    (Submodule.mem_orthogonal' _ _).1 (Submodule.isOrtho_iff_le.1 (lemma_14_2_1_isOrtho hw hik) hu)
      _ hv
  have hsub : ∀ {i : ℕ} {u v : Lp ℝ 2 μ}, u ∈ orthPolySpace hw i → v ∈ orthPolySpace hw i →
      u - v ∈ orthPolySpace hw i := fun hu hv => Submodule.sub_mem _ hu hv
  have hda := hsub ha ha'
  have hdb := hsub hb hb'
  have hdc := hsub hc hc'
  refine ⟨sub_eq_zero.1 ?_, sub_eq_zero.1 ?_, sub_eq_zero.1 ?_⟩ <;>
    rw [← inner_self_eq_zero (𝕜 := ℝ)]
  · have := congrArg (fun v => inner ℝ (a - a') v) hz
    simpa [inner_add_right, key (by omega) hda hdb, key (by omega) hda hdc] using this
  · have := congrArg (fun v => inner ℝ (b - b') v) hz
    simpa [inner_add_right, key (by omega) hdb hda, key (by omega) hdb hdc] using this
  · have := congrArg (fun v => inner ℝ (c - c') v) hz
    simpa [inner_add_right, key (by omega) hdc hda, key (by omega) hdc hdb] using this

/-- **(14.2.12)**: the orthogonal projection `P_n` of `L²(μ)` onto `Π_n^d` is the sum of the
projections onto the components. In an orthonormal basis `{φ_{m,ℓ}}_ℓ` of each `V_m^d` the `m`-th
summand is `Σ_ℓ (f, φ_{m,ℓ}) φ_{m,ℓ}`, so this is the book's expansion with no basis chosen. -/
theorem equation_14_2_12 (n : ℕ) (f : Lp ℝ 2 μ) :
    (hw.polyLE n).starProjection f =
      ∑ m ∈ Finset.range (n + 1), (orthPolySpace hw m).starProjection f :=
  starProjection_eq_sum_orthogonalComponent hw.monotone_polyLE n f

/-- **(14.2.12)**: `P_n f` is the best `L²(μ)` approximation to `f` from `Π_n^d`. -/
theorem equation_14_2_12_isBestApprox (n : ℕ) (f : Lp ℝ 2 μ) :
    IsBestApprox (hw.polyLE n : Set (Lp ℝ 2 μ)) f ((hw.polyLE n).starProjection f) :=
  isBestApprox_starProjection _ f

/-- **(14.2.13)**, the Lebesgue lemma: a bounded projection `P` of `C(𝔹_d)` onto `Π_n^d` satisfies
`‖f − P f‖_∞ ≤ (1 + ‖P‖) E_n(f)`, so it is a quasi-best approximation with `1 + ‖P‖` for constant.
The statement is general — it is the backbone's
`norm_sub_apply_le_of_isIdempotentElem` — and what is specialized here is the subspace, `Π_n^d`
inside `C(D, ℝ)`. Combined with Theorem 14.2.4, which is not formalized, it gives Theorem 14.2.5. -/
theorem equation_14_2_13 {D : Set (Fin d → ℝ)} [CompactSpace D] (n : ℕ) (P : C(D, ℝ) →L[ℝ] C(D, ℝ))
    (hP : IsIdempotentElem P)
    (hr : LinearMap.range (P : C(D, ℝ) →ₗ[ℝ] C(D, ℝ)) = mvPolyLE D n) (f : C(D, ℝ)) :
    ‖f - P f‖ ≤ (1 + ‖P‖) * minimaxError n f := by
  rw [minimaxError, ← hr]
  exact norm_sub_apply_le_of_isIdempotentElem P hP f

end AtkinsonHan.Chapter14
