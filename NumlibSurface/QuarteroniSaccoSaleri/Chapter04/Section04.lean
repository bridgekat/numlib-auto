import Numlib.Krylov.CR
import Numlib.Krylov.Hessenberg
import Numlib.Krylov.Lanczos
import Numlib.Stationary.Block
import NumlibSurface.QuarteroniSaccoSaleri.Chapter04.Section03

/-!
# Quarteroni–Sacco–Saleri §4.4: methods based on Krylov subspace iterations

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §4.4, over the backbone `Numlib/Krylov/Subspace` (Krylov subspaces,
the grade), `Numlib/Krylov/Arnoldi` (the Arnoldi process as Gram–Schmidt on the Krylov sequence),
`Numlib/Krylov/Iterate` and `Numlib/Krylov/Hessenberg` (the Galerkin and minimal-residual
specifications, their coordinates in the Arnoldi basis, the Givens rotations),
`Numlib/Krylov/Lanczos` (the symmetric case), `Numlib/Krylov/CR` (the conjugate residual method),
`Numlib/Projection/Basic` (projection methods) and `Numlib/Stationary/Block` (Gauss–Seidel as a
multiplicative projection process).

## Conventions

Vectors are `EuclideanSpace ℝ (Fin n)`, on which a matrix acts as `Matrix.toEuclideanLin A`, as in
§4.3. The book's `K_m(A; v)` is `krylovSubspace A v m`, the span of `v, A v, …, A^{m-1} v`, which is
the backbone's `Krylov.subspace (toEuclideanLin A) v m` (`krylovSubspace_eq`); its `deg_A(v)` is
`degree A v`, the least degree of a monic polynomial annihilating `v`, which is the backbone's
`Krylov.grade` (`degree_eq_grade`). The Arnoldi algorithm (4.55) is written as the book writes it
(`arnoldi`, `arnoldiH`, `arnoldiW`), `0`-based — `arnoldi A v₁ (k - 1)` is the book's `v_k` and
`arnoldiH A v₁ (i - 1) (k - 1)` its `h_ik` — and identified with the backbone's Gram–Schmidt
vectors `Arnoldi.vec` for a unit starting vector (`arnoldi_eq_vec`) and for the start
`v₁ = r⁽⁰⁾/‖r⁽⁰⁾‖` of the Krylov methods (`arnoldi_normalize`); its matrices `V_m`, `H_m`, `Ĥ_m`
are `V`, `H`, `Hhat`. The two Krylov methods are the specifications `equation_4_57` (4.57) and
`equation_4_58` (4.58), which are the backbone's `Krylov.IsGalerkinIterate` and
`Krylov.IsMinResidualIterate`; a breakdown of the Arnoldi process is a vanishing `w_k`.

## Contents

* `toEuclideanLin_aeval`, `equation_4_51`, `krylovSubspace`, `krylovSubspace_eq`,
  `mem_krylovSubspace_iff`, `equation_4_53`, `degree`, `degree_eq_grade`, `degree_le`,
  `property_4_7`, `example_4_8` — Krylov subspaces and the degree.
* `arnoldi`, `arnoldiH`, `arnoldiW`, `arnoldi_zero`, `arnoldi_succ`, `arnoldi_eq_vec`,
  `arnoldi_normalize`, `arnoldi_basis`, `V`, `H`, `Hhat`, `equation_4_56`,
  `arnoldi_breakdown_iff` — the Arnoldi algorithm (4.55)–(4.56).
* `toEuclideanLin_injective_of_isUnit`, `equation_4_57`, `equation_4_57_iff`, `equation_4_58`,
  `equation_4_58_iff`, `e₁`, `smul_e₁_eq_firstVec`, `V_mulVec`, `equation_4_62`, `theorem_4_13`,
  `equation_4_63` — §4.4.1.
* `equation_4_65`, `equation_4_66`, `property_4_8`, `gmres_norm_residual_eq_norm_gamma` — §4.4.2.
* `remark_4_4`, `remark_4_4_iff`, `remark_4_4_krylov`, `remark_4_4_gaussSeidel` — Remark 4.4.
* `lanczos_tridiagonal`, `lanczos_residual_eq_smul`, `remark_4_5`, `cr_residual_conjugate` —
  §4.4.3.

Example 4.9 is a numerical run and Programs 21–24 are code; FOM(m), IOM, GMRES(m), QGMRES, GCR and
ORTHOMIN are named without any result; none is a node.

## Readings

Remark 4.4 writes `x⁽ᵏ⁾ ∈ Y_k`; for the Krylov instances the correct statement is
`x⁽ᵏ⁾ ∈ x⁽⁰⁾ + Y_k`, the book's own (4.59), and `remark_4_4` carries the translate. The
proof of Theorem 4.13 inverts `H_m` at a breakdown without justification; `H_m` is nonsingular at
the grade because `A` is (the book's standing assumption), which is the backbone's
`Krylov.existsUnique_isGalerkinIterate_of_grade_le`. Property 4.8 is stated for `m < n`; the
equivalence holds for every `m`, and at `m = n` both sides are true.
-/

open Filter Finset Matrix Polynomial Topology WithLp

namespace QuarteroniSaccoSaleri.Chapter04

variable {n : ℕ}

/-! ### (4.51)–(4.54): Krylov subspaces -/

section Krylov

-- TODO(backbone): belongs in `Numlib/Analysis/Matrix/ToEuclideanLin`; the Saad surface proves the
-- same lemma as `SaadSparse.Chapter06.toEuclideanLin_aeval`.
/-- `p(A)` as an operator is `p` of the operator: `Matrix.toEuclideanLin` is an algebra map. -/
theorem toEuclideanLin_aeval (A : Matrix (Fin n) (Fin n) ℝ) (p : ℝ[X]) :
    toEuclideanLin (aeval A p) = aeval (toEuclideanLin A) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial k c =>
    rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def, map_smul,
      toEuclideanLin_pow]

variable (A : Matrix (Fin n) (Fin n) ℝ)

/-- **(4.51).** For the non preconditioned Richardson method (4.24), `P = I`, the residual at the
`k`-th step is `r⁽ᵏ⁾ = ∏_{j<k} (I - α_j A) r⁽⁰⁾ = p_k(A) r⁽⁰⁾`, with `p_k = ∏_{j<k} (1 - α_j X)` a
polynomial of degree `≤ k` with `p_k(0) = 1` (backbone `Richardson.residual_iterate_eq_prod`). -/
theorem equation_4_51 (α : ℕ → ℝ) (b x₀ : Fin n → ℝ) (k : ℕ) :
    b - A *ᵥ nonstationaryRichardson A 1 α b x₀ k =
        aeval A (∏ j ∈ range k, (1 - C (α j) * X)) *ᵥ (b - A *ᵥ x₀) ∧
      (∏ j ∈ range k, (1 - C (α j) * X : ℝ[X])).degree ≤ k ∧
      (∏ j ∈ range k, (1 - C (α j) * X : ℝ[X])).eval 0 = 1 := by
  refine ⟨?_, degree_le_of_natDegree_le (Richardson.natDegree_residualPoly_le α k),
    Richardson.residualPoly_eval_zero α k⟩
  have h := Richardson.residual_iterate_eq_prod (toEuclideanLin A) α (toLp 2 b) (toLp 2 x₀) k
  have h2 := toLp_nonstationaryRichardson A 1 α b x₀ k
  rw [inv_one, toEuclideanLin_one] at h2
  rw [← h2, Richardson.residualPoly, ← toEuclideanLin_aeval, toEuclideanLin_toLp, ← toLp_sub,
    toEuclideanLin_toLp, ← toLp_sub, toEuclideanLin_toLp] at h
  exact toLp_injective 2 h

/-- **(4.52).** The Krylov subspace of order `m`, `K_m(A; v) = span {v, A v, …, A^{m-1} v}`. It is
the backbone's `Krylov.subspace (toEuclideanLin A) v m` (`krylovSubspace_eq`). -/
def krylovSubspace (v : EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ (Set.range fun i : Fin m => toEuclideanLin (A ^ (i : ℕ)) v)

/-- The book's Krylov subspace is the backbone's (`Matrix.krylov_subspace_toEuclideanLin`). -/
theorem krylovSubspace_eq (v : EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    krylovSubspace A v m = Krylov.subspace (toEuclideanLin A) v m :=
  (krylov_subspace_toEuclideanLin A v m).symm

/-- **The sentence after (4.52).** `K_m(A; v)` is the set of vectors `u = p_{m-1}(A) v` with
`p_{m-1}` a polynomial of degree `≤ m - 1` (backbone `Krylov.mem_subspace_iff_exists_aeval`). -/
theorem mem_krylovSubspace_iff (v u : EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    u ∈ krylovSubspace A v m ↔ ∃ p : ℝ[X], p.degree < m ∧ aeval (toEuclideanLin A) p v = u := by
  rw [krylovSubspace_eq, Krylov.mem_subspace_iff_exists_aeval]

/-- **(4.53)–(4.54).** The iterate `x⁽ᵏ⁾` of the non preconditioned Richardson method belongs to
`W_k = {x⁽⁰⁾ + y : y ∈ K_k(A; r⁽⁰⁾)}` (backbone `Richardson.iterate_sub_mem_subspace`), and the
elements of `W_k` are exactly the vectors `x⁽⁰⁾ + q_{k-1}(A) r⁽⁰⁾` with `q_{k-1}` of degree
`≤ k - 1`: a Krylov method looks for its iterate in that form. -/
theorem equation_4_53 (α : ℕ → ℝ) (b x₀ : Fin n → ℝ) (k : ℕ) :
    (toLp 2 (nonstationaryRichardson A 1 α b x₀ k) : EuclideanSpace ℝ (Fin n)) - toLp 2 x₀ ∈
        krylovSubspace A (toLp 2 (b - A *ᵥ x₀)) k ∧
      ∀ x : EuclideanSpace ℝ (Fin n),
        x - toLp 2 x₀ ∈ krylovSubspace A (toLp 2 (b - A *ᵥ x₀)) k ↔
          ∃ q : ℝ[X], q.degree < k ∧
            x = toLp 2 x₀ + aeval (toEuclideanLin A) q (toLp 2 (b - A *ᵥ x₀)) := by
  constructor
  · rw [toLp_nonstationaryRichardson, inv_one, toEuclideanLin_one, krylovSubspace_eq, toLp_sub,
      ← toEuclideanLin_toLp]
    exact Richardson.iterate_sub_mem_subspace (toEuclideanLin A) α (toLp 2 b) (toLp 2 x₀) k
  · intro x
    rw [mem_krylovSubspace_iff]
    constructor
    · rintro ⟨q, hq, hqx⟩
      exact ⟨q, hq, by rw [hqx, add_sub_cancel]⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, by rw [add_sub_cancel_left]⟩

/-- **The degree of `v` with respect to `A`**, `deg_A(v)` (Property 4.7): the minimum degree of a
monic (nonzero) polynomial `p` with `p(A) v = 0`. It is the backbone's `Krylov.grade`
(`degree_eq_grade`). -/
noncomputable def degree (v : EuclideanSpace ℝ (Fin n)) : ℕ :=
  sInf {d | ∃ p : ℝ[X], p.Monic ∧ p.natDegree = d ∧ aeval (toEuclideanLin A) p v = 0}

/-- The degree of `v` is the grade of `v`, the dimension of the full Krylov space: the backbone's
`Krylov.grade_eq_sInf` with `Krylov.pow_apply_mem_subspace_iff_exists_monic`. -/
theorem degree_eq_grade (v : EuclideanSpace ℝ (Fin n)) :
    degree A v = Krylov.grade (toEuclideanLin A) v := by
  rw [degree, Krylov.grade_eq_sInf]
  congr 1
  ext m
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Krylov.pow_apply_mem_subspace_iff_exists_monic]

/-- **The sentence after Property 4.7.** The degree of `v` cannot be greater than `n`
(Cayley–Hamilton; backbone `Krylov.grade_le_finrank`). -/
theorem degree_le (v : EuclideanSpace ℝ (Fin n)) : degree A v ≤ n := by
  rw [degree_eq_grade]
  have := Krylov.grade_le_finrank (toEuclideanLin A) v
  rwa [finrank_euclideanSpace_fin] at this

/-- **Property 4.7** and the sentence after it. `K_m(A; v)` has dimension `m` iff `deg_A(v) ≥ m`;
in general its dimension is `min(m, deg_A(v))`, a nondecreasing function of `m` (backbone
`Krylov.finrank_subspace`). -/
theorem property_4_7 (v : EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    (Module.finrank ℝ (krylovSubspace A v m) = m ↔ m ≤ degree A v) ∧
      Module.finrank ℝ (krylovSubspace A v m) = min m (degree A v) := by
  rw [krylovSubspace_eq, degree_eq_grade, Krylov.finrank_subspace]
  exact ⟨min_eq_left_iff, rfl⟩

end Krylov

/-! ### Example 4.8 -/

section Example

/-- The matrix `tridiag₄(-1, 2, -1)` of Example 4.8. -/
def example_4_8_matrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2, -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 2]

/-- The grade of `v` is at most `m` when `A^m v` is a combination of `v, …, A^{m-1} v`. -/
private theorem grade_le_of_exists_fun {A : Matrix (Fin n) (Fin n) ℝ}
    {v : EuclideanSpace ℝ (Fin n)} {m : ℕ} (c : Fin m → ℝ)
    (h : ∑ i, c i • toEuclideanLin (A ^ (i : ℕ)) v = toEuclideanLin (A ^ m) v) :
    Krylov.grade (toEuclideanLin A) v ≤ m := by
  rw [Krylov.grade_le_iff, ← toEuclideanLin_pow, krylov_subspace_toEuclideanLin,
    Submodule.mem_span_range_iff_exists_fun]
  exact ⟨c, h⟩

/-- The grade of `v` exceeds `m` when `A^m v` is not a combination of `v, …, A^{m-1} v`. -/
private theorem lt_grade_of_forall_fun {A : Matrix (Fin n) (Fin n) ℝ}
    {v : EuclideanSpace ℝ (Fin n)} {m : ℕ}
    (h : ∀ c : Fin m → ℝ, ∑ i, c i • toEuclideanLin (A ^ (i : ℕ)) v ≠ toEuclideanLin (A ^ m) v) :
    m < Krylov.grade (toEuclideanLin A) v := by
  by_contra hle
  rw [not_lt, Krylov.grade_le_iff, ← toEuclideanLin_pow, krylov_subspace_toEuclideanLin,
    Submodule.mem_span_range_iff_exists_fun] at hle
  obtain ⟨c, hc⟩ := hle
  exact h c hc

/-- **Example 4.8.** For `A = tridiag₄(-1, 2, -1)`, the vector `v = (1, 1, 1, 1)ᵀ` has degree `2`
with respect to `A` — `p₂(A) v = 0` for `p₂(A) = I - 3A + A²`, while no monic polynomial of degree
`1` annihilates `v` — so that every Krylov subspace `K_m(A; v)` with `m ≥ 2` has dimension `2`;
the vector `w = (1, 1, -1, 1)ᵀ` has degree `4`. Finite computations on the explicit Krylov vectors,
through `degree_eq_grade` and `property_4_7`. -/
theorem example_4_8 :
    degree example_4_8_matrix (toLp 2 ![1, 1, 1, 1]) = 2 ∧
      (∀ m, 2 ≤ m → Module.finrank ℝ (krylovSubspace example_4_8_matrix (toLp 2 ![1, 1, 1, 1]) m)
        = 2) ∧
      degree example_4_8_matrix (toLp 2 ![1, 1, -1, 1]) = 4 := by
  have e1 : example_4_8_matrix *ᵥ ![1, 1, 1, 1] = ![1, 0, 0, 1] := by
    ext i
    fin_cases i <;> simp [example_4_8_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      norm_num
  have e2 : example_4_8_matrix *ᵥ ![1, 0, 0, 1] = ![2, -1, -1, 2] := by
    ext i
    fin_cases i <;> simp [example_4_8_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  have f1 : example_4_8_matrix *ᵥ ![1, 1, -1, 1] = ![1, 2, -4, 3] := by
    ext i
    fin_cases i <;> simp [example_4_8_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      norm_num
  have f2 : example_4_8_matrix *ᵥ ![1, 2, -4, 3] = ![0, 7, -13, 10] := by
    ext i
    fin_cases i <;> simp [example_4_8_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      norm_num
  have f3 : example_4_8_matrix *ᵥ ![0, 7, -13, 10] = ![-7, 27, -43, 33] := by
    ext i
    fin_cases i <;> simp [example_4_8_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      norm_num
  have hv : degree example_4_8_matrix (toLp 2 ![1, 1, 1, 1]) = 2 := by
    rw [degree_eq_grade]
    refine le_antisymm (grade_le_of_exists_fun ![-1, 3] ?_) (lt_grade_of_forall_fun fun c hc => ?_)
    · simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, toEuclideanLin_toLp,
        ← toLp_smul, ← toLp_add, one_mulVec, pow_succ, ← mulVec_mulVec, Matrix.one_mul, e1, e2,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      congr 1
      ext i
      fin_cases i <;> simp <;> norm_num
    · simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, toEuclideanLin_toLp, ← toLp_smul,
        one_mulVec, pow_succ, Matrix.one_mul, e1] at hc
      have h := congrArg ofLp hc
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp at h0 h1
      linarith
  refine ⟨hv, fun m hm => ?_, ?_⟩
  · rw [(property_4_7 _ _ _).2, hv, min_eq_right hm]
  · rw [degree_eq_grade]
    refine le_antisymm ?_ (lt_grade_of_forall_fun fun c hc => ?_)
    · have := Krylov.grade_le_finrank (toEuclideanLin example_4_8_matrix) (toLp 2 ![1, 1, -1, 1])
      rwa [finrank_euclideanSpace_fin] at this
    · simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero,
        toEuclideanLin_toLp, ← toLp_smul, ← toLp_add, one_mulVec, pow_succ, ← mulVec_mulVec,
        Matrix.one_mul, f1, f2, f3] at hc
      have h := congrArg ofLp hc
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      have h3 := congrFun h 3
      simp at h0 h1 h2 h3
      linarith

end Example

/-! ### (4.55)–(4.56): the Arnoldi algorithm -/

section Arnoldi

variable (A : Matrix (Fin n) (Fin n) ℝ) (v₁ : EuclideanSpace ℝ (Fin n))

/-- **(4.55), the Arnoldi algorithm**, `0`-based: `arnoldi A v₁ 0 = v₁` and, for `k = 0, 1, …`,
`h_ik = v_iᵀ A v_k` for `i ≤ k`, `w_k = A v_k - ∑_{i ≤ k} h_ik v_i`, `h_{k+1,k} = ‖w_k‖₂` and
`arnoldi A v₁ (k + 1) = w_k / ‖w_k‖₂`. The book's "if `w_k = 0` the process terminates (breakdown)"
is Lean's `0⁻¹ = 0`: all later vectors are `0`. `arnoldi A v₁ (k - 1)` is the book's `v_k`. -/
noncomputable def arnoldi : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => v₁
  | k + 1 =>
    let v : Fin (k + 1) → EuclideanSpace ℝ (Fin n) := fun i => arnoldi (i : ℕ)
    let Av := toEuclideanLin A (v (Fin.last k))
    let w := Av - ∑ i : Fin (k + 1), inner ℝ (v i) Av • v i
    ((‖w‖ : ℝ)⁻¹) • w
  termination_by k => k
  decreasing_by exact i.isLt

/-- The Arnoldi coefficients `h_ik = v_iᵀ A v_k` of (4.55), `0`-based (`arnoldiH A v₁ (i - 1)
(k - 1)` is the book's `h_ik`), defined for all `i`, `k`; they vanish for `i > k + 1`
(`equation_4_56`). -/
noncomputable def arnoldiH (i k : ℕ) : ℝ :=
  inner ℝ (arnoldi A v₁ i) (toEuclideanLin A (arnoldi A v₁ k))

/-- The vector `w_k = A v_k - ∑_{i ≤ k} h_ik v_i` of (4.55). -/
noncomputable def arnoldiW (k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  toEuclideanLin A (arnoldi A v₁ k) - ∑ i ∈ range (k + 1), arnoldiH A v₁ i k • arnoldi A v₁ i

@[simp]
theorem arnoldi_zero : arnoldi A v₁ 0 = v₁ := by rw [arnoldi]

/-- (4.55): `v_{k+1} = w_k / ‖w_k‖₂`. -/
theorem arnoldi_succ (k : ℕ) :
    arnoldi A v₁ (k + 1) = ((‖arnoldiW A v₁ k‖ : ℝ)⁻¹) • arnoldiW A v₁ k := by
  rw [arnoldi, arnoldiW]
  simp only [arnoldiH, Fin.val_last]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => inner ℝ (arnoldi A v₁ i) (toEuclideanLin A (arnoldi A v₁ k)) • arnoldi A v₁ i)
    (k + 1)]

/-- `w_k` agrees with the backbone's `Arnoldi.w` as soon as the vectors up to `v_k` do. -/
private theorem arnoldiW_eq_of_forall {r : EuclideanSpace ℝ (Fin n)} {k : ℕ}
    (ih : ∀ i ≤ k, arnoldi A v₁ i = Arnoldi.vec (toEuclideanLin A) r i) :
    arnoldiW A v₁ k = Arnoldi.w (toEuclideanLin A) r k := by
  have hsum : ∑ i ∈ range (k + 1), arnoldiH A v₁ i k • arnoldi A v₁ i =
      ∑ i ∈ range (k + 1),
        Arnoldi.coeff (toEuclideanLin A) r i k • Arnoldi.vec (toEuclideanLin A) r i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [arnoldiH, ih i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)), ih k le_rfl]
    rfl
  rw [arnoldiW, Arnoldi.w, hsum, ih k le_rfl]

/-- The algorithm (4.55) started at `v₁` computes the backbone's Arnoldi vectors of any `r` whose
normalization is `v₁`: the two instances are a unit `v₁` (`arnoldi_eq_vec`) and `v₁ = r/‖r‖`
(`arnoldi_normalize`). -/
theorem arnoldi_eq_vec_of_vec_zero {r : EuclideanSpace ℝ (Fin n)}
    (h0 : Arnoldi.vec (toEuclideanLin A) r 0 = v₁) (k : ℕ) :
    arnoldi A v₁ k = Arnoldi.vec (toEuclideanLin A) r k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [arnoldi_zero, h0]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [arnoldi_succ, Arnoldi.vec_succ_eq,
        arnoldiW_eq_of_forall A v₁ fun i hi => ih i (Nat.lt_succ_of_le hi)]
      rfl

/-- **The bridge to the backbone.** For a unit starting vector `v₁`, the Arnoldi algorithm (4.55)
computes the Gram–Schmidt orthonormalization `Arnoldi.vec` of the Krylov sequence
`v₁, A v₁, A² v₁, …`, its coefficients are `Arnoldi.coeff` and its `w_k` are `Arnoldi.w`. -/
theorem arnoldi_eq_vec (hv : ‖v₁‖ = 1) :
    (∀ k, arnoldi A v₁ k = Arnoldi.vec (toEuclideanLin A) v₁ k) ∧
      (∀ i k, arnoldiH A v₁ i k = Arnoldi.coeff (toEuclideanLin A) v₁ i k) ∧
      ∀ k, arnoldiW A v₁ k = Arnoldi.w (toEuclideanLin A) v₁ k := by
  have hv0 : v₁ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv
    exact zero_ne_one hv
  have hvec : ∀ k, arnoldi A v₁ k = Arnoldi.vec (toEuclideanLin A) v₁ k := by
    refine arnoldi_eq_vec_of_vec_zero A v₁ ?_
    rw [Arnoldi.vec_zero (toEuclideanLin A) v₁ hv0, hv]
    simp
  refine ⟨hvec, fun i k => ?_, fun k => arnoldiW_eq_of_forall A v₁ fun i _ => hvec i⟩
  rw [arnoldiH, hvec, hvec]
  rfl

/-- The Arnoldi algorithm started at `v₁ = r/‖r‖₂`, the start of the Krylov methods for the
residual `r = r⁽⁰⁾`, computes the backbone's Arnoldi vectors and coefficients of `r`. -/
theorem arnoldi_normalize {r : EuclideanSpace ℝ (Fin n)} (hr : r ≠ 0) :
    (∀ k, arnoldi A ((‖r‖ : ℝ)⁻¹ • r) k = Arnoldi.vec (toEuclideanLin A) r k) ∧
      ∀ i k, arnoldiH A ((‖r‖ : ℝ)⁻¹ • r) i k = Arnoldi.coeff (toEuclideanLin A) r i k := by
  have hvec := arnoldi_eq_vec_of_vec_zero A ((‖r‖ : ℝ)⁻¹ • r)
    (Arnoldi.vec_zero (toEuclideanLin A) r hr)
  refine ⟨hvec, fun i k => ?_⟩
  rw [arnoldiH, hvec, hvec]
  rfl

/-- The range of a `Fin m`-indexed family is the image of `Set.Iio m`. -/
private theorem range_fin_eq_image_Iio {α : Type*} (f : ℕ → α) (m : ℕ) :
    Set.range (fun i : Fin m => f (i : ℕ)) = f '' Set.Iio m := by
  ext x
  simp only [Set.mem_range, Set.mem_image, Set.mem_Iio, Fin.exists_iff]
  tauto

/-- **The sentence before (4.56).** If the method has not terminated before step `m`
(`m ≤ deg_A(v₁)`), the vectors `v_1, …, v_m` are orthonormal and form a basis of `K_m(A; v₁)`
(backbone `Arnoldi.orthonormal`, `Arnoldi.span_vec`). -/
theorem arnoldi_basis (hv : ‖v₁‖ = 1) {m : ℕ} (hm : m ≤ degree A v₁) :
    Orthonormal ℝ (fun i : Fin m => arnoldi A v₁ i) ∧
      Submodule.span ℝ (Set.range fun i : Fin m => arnoldi A v₁ i) = krylovSubspace A v₁ m := by
  obtain ⟨hvec, -, -⟩ := arnoldi_eq_vec A v₁ hv
  rw [degree_eq_grade] at hm
  simp only [hvec]
  refine ⟨?_, ?_⟩
  · have h := Arnoldi.orthonormal (toEuclideanLin A) v₁
    exact h.comp (fun i : Fin m => Fin.castLE hm i) (Fin.castLE_injective hm)
  · rw [range_fin_eq_image_Iio, Arnoldi.span_vec, krylovSubspace_eq]

/-- The matrix `V_m ∈ ℝ^{n×m}` whose columns are the Arnoldi vectors `v_1, …, v_m`. -/
noncomputable def V (m : ℕ) : Matrix (Fin n) (Fin m) ℝ := Matrix.of fun i j => arnoldi A v₁ j i

/-- The matrix `H_m ∈ ℝ^{m×m}` of the Arnoldi coefficients, the restriction of `Ĥ_m` to its first
`m` rows. -/
noncomputable def H (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => arnoldiH A v₁ i j

/-- The matrix `Ĥ_m ∈ ℝ^{(m+1)×m}` of the Arnoldi coefficients `h_ij`, upper Hessenberg. -/
noncomputable def Hhat (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) ℝ :=
  Matrix.of fun i j => arnoldiH A v₁ i j

/-- The entry `(i, j)` of `V_pᵀ A V_m` is `v_iᵀ A v_j = h_ij`, for every `p`, `m`. -/
private theorem transpose_V_mul_mul_V_apply (p m : ℕ) (i : Fin p) (j : Fin m) :
    ((V A v₁ p)ᵀ * A * V A v₁ m) i j = arnoldiH A v₁ i j := by
  simp only [arnoldiH, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, ofLp_toEuclideanLin,
    Matrix.mul_apply, Matrix.transpose_apply, V, Matrix.of_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **(4.56).** `V_mᵀ A V_m = H_m` and `V_{m+1}ᵀ A V_m = Ĥ_m`, where `Ĥ_m` is upper Hessenberg —
its entries `h_ij` vanish for `i > j + 1` (backbone `Arnoldi.coeff_eq_zero_of_lt`) — and `H_m` is
its restriction to the first `m` rows; the products are the definition of the coefficients, the
Hessenberg structure needs `v₁` to be a unit vector. `H_m` and `Ĥ_m` are the backbone's
`Arnoldi.hessenbergSq` and `Arnoldi.hessenberg`. -/
theorem equation_4_56 (hv : ‖v₁‖ = 1) (m : ℕ) :
    (V A v₁ m)ᵀ * A * V A v₁ m = H A v₁ m ∧ (V A v₁ (m + 1))ᵀ * A * V A v₁ m = Hhat A v₁ m ∧
      (Hhat A v₁ m).IsUpperHessenbergRect ∧
      (∀ i j : Fin m, H A v₁ m i j = Hhat A v₁ m (Fin.castSucc i) j) ∧
      H A v₁ m = Arnoldi.hessenbergSq (toEuclideanLin A) v₁ m ∧
      Hhat A v₁ m = Arnoldi.hessenberg (toEuclideanLin A) v₁ m := by
  obtain ⟨-, hH, -⟩ := arnoldi_eq_vec A v₁ hv
  have hHhat : Hhat A v₁ m = Arnoldi.hessenberg (toEuclideanLin A) v₁ m := by
    ext i j
    simp only [Hhat, Arnoldi.hessenberg, Matrix.of_apply, hH]
  refine ⟨?_, ?_, ?_, fun i j => rfl, ?_, hHhat⟩
  · ext i j
    rw [transpose_V_mul_mul_V_apply]
    rfl
  · ext i j
    rw [transpose_V_mul_mul_V_apply]
    rfl
  · rw [hHhat]
    exact Arnoldi.hessenberg_isUpperHessenbergRect _ _ m
  · ext i j
    simp only [H, Arnoldi.hessenbergSq, Matrix.of_apply, hH]

/-- **The sentence after (4.56).** The algorithm terminates at an intermediate step exactly at
the degree of `v₁`: for a unit `v₁`, `w_k = 0` iff `h_{k+1,k} = 0` iff `deg_A(v₁) ≤ k + 1`, and
the vector `v_{k+1}` computed by the algorithm vanishes iff `deg_A(v₁) ≤ k` (`0`-based; the book's
first vector that cannot be formed is `v_{k+1}` with `k = deg_A(v₁)`). Backbone
`Arnoldi.coeff_succ_self_eq_zero_iff`, `Arnoldi.vec_eq_zero_iff`. -/
theorem arnoldi_breakdown_iff (hv : ‖v₁‖ = 1) (k : ℕ) :
    (arnoldiW A v₁ k = 0 ↔ degree A v₁ ≤ k + 1) ∧
      (arnoldiH A v₁ (k + 1) k = 0 ↔ degree A v₁ ≤ k + 1) ∧
      (arnoldi A v₁ k = 0 ↔ degree A v₁ ≤ k) := by
  obtain ⟨hvec, hH, hW⟩ := arnoldi_eq_vec A v₁ hv
  rw [degree_eq_grade, hvec, hH, hW, Arnoldi.coeff_succ_self_eq_zero_iff, Arnoldi.vec_eq_zero_iff,
    ← Arnoldi.coeff_succ_self_eq_zero_iff, Arnoldi.coeff_succ_self, RCLike.ofReal_real_eq_id, id_eq,
    norm_eq_zero]
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

end Arnoldi

/-! ### (4.57)–(4.58): the two Krylov methods -/

section Specifications

/-- A nonsingular matrix acts injectively on `EuclideanSpace`
(`Matrix.mulVec_injective_iff_isUnit`). -/
theorem toEuclideanLin_injective_of_isUnit {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) :
    Function.Injective (toEuclideanLin A) := by
  intro x y hxy
  have h := congrArg ofLp hxy
  rw [ofLp_toEuclideanLin, ofLp_toEuclideanLin] at h
  exact ofLp_injective 2 (mulVec_injective_iff_isUnit.mpr hA h)

variable (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))

/-- **(4.57), the Arnoldi method for linear systems (FOM).** The iterate `x⁽ᵏ⁾ ∈ W_k` is chosen so
that the residual `r⁽ᵏ⁾ = b - A x⁽ᵏ⁾` is orthogonal to every vector of `K_k(A; r⁽⁰⁾)`. It is the
backbone's Galerkin specification `Krylov.IsGalerkinIterate` (`equation_4_57_iff`). -/
def equation_4_57 (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x - x₀ ∈ krylovSubspace A (b - toEuclideanLin A x₀) k ∧
    ∀ v ∈ krylovSubspace A (b - toEuclideanLin A x₀) k, inner ℝ v (b - toEuclideanLin A x) = 0

/-- The FOM specification is the backbone's `Krylov.IsGalerkinIterate`. -/
theorem equation_4_57_iff (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    equation_4_57 A b x₀ k x ↔ Krylov.IsGalerkinIterate (toEuclideanLin A) b x₀ k x := by
  rw [equation_4_57, krylovSubspace_eq]
  constructor
  · rintro ⟨hmem, horth⟩
    exact ⟨hmem, (Submodule.mem_orthogonal _ _).2 horth⟩
  · rintro ⟨hmem, horth⟩
    exact ⟨hmem, (Submodule.mem_orthogonal _ _).1 horth⟩

/-- **(4.58), the GMRES method.** The iterate `x⁽ᵏ⁾ ∈ W_k` minimizes the Euclidean norm of the
residual, `‖b - A x⁽ᵏ⁾‖₂ = min_{v ∈ W_k} ‖b - A v‖₂`. It is the backbone's minimal-residual
specification `Krylov.IsMinResidualIterate` (`equation_4_58_iff`). -/
def equation_4_58 (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x - x₀ ∈ krylovSubspace A (b - toEuclideanLin A x₀) k ∧
    ∀ y, y - x₀ ∈ krylovSubspace A (b - toEuclideanLin A x₀) k →
      ‖b - toEuclideanLin A x‖ ≤ ‖b - toEuclideanLin A y‖

/-- The GMRES specification is the backbone's `Krylov.IsMinResidualIterate`; the GMRES iterate
exists at every step (`Krylov.exists_isMinResidualIterate`) and is unique for nonsingular `A`
(`Krylov.existsUnique_isMinResidualIterate_of_injective`). -/
theorem equation_4_58_iff (k : ℕ) :
    (∀ x, equation_4_58 A b x₀ k x ↔ Krylov.IsMinResidualIterate (toEuclideanLin A) b x₀ k x) ∧
      (∃ x, equation_4_58 A b x₀ k x) ∧ (IsUnit A → ∃! x, equation_4_58 A b x₀ k x) := by
  have hiff : ∀ x, equation_4_58 A b x₀ k x ↔
      Krylov.IsMinResidualIterate (toEuclideanLin A) b x₀ k x := by
    intro x
    rw [equation_4_58, krylovSubspace_eq]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mem, h.min⟩⟩
  refine ⟨hiff, ?_, fun hA => ?_⟩
  · simp only [hiff]
    exact Krylov.exists_isMinResidualIterate _ b x₀ k
  · simp only [hiff]
    exact Krylov.existsUnique_isMinResidualIterate_of_injective
      (toEuclideanLin_injective_of_isUnit hA) b x₀ k

/-- The first unit vector `e₁` of `ℝᵐ`. -/
def e₁ (m : ℕ) : Fin m → ℝ := fun i => if (i : ℕ) = 0 then 1 else 0

/-- `β e₁` is the backbone's `Krylov.firstVec β m`. -/
theorem smul_e₁_eq_firstVec (β : ℝ) (m : ℕ) : β • e₁ m = Krylov.firstVec β m := by
  funext i
  simp only [e₁, Krylov.firstVec, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- **(4.59).** `V_k z = ∑_j z_j v_j`: the iterate `x⁽⁰⁾ + V_k z⁽ᵏ⁾` expanded in the Arnoldi
basis. -/
theorem V_mulVec (v₁ : EuclideanSpace ℝ (Fin n)) (k : ℕ) (z : Fin k → ℝ) :
    toEuclideanLin (V A v₁ k) (toLp 2 z) = ∑ j, z j • arnoldi A v₁ j := by
  rw [toEuclideanLin_apply_eq_sum]
  rfl

end Specifications

/-! ### §4.4.1 The Arnoldi method for linear systems -/

section FOM

variable {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ : EuclideanSpace ℝ (Fin n)}

/-- The Arnoldi vectors of the start `v₁ = r⁽⁰⁾/‖r⁽⁰⁾‖₂` are the backbone's Arnoldi vectors of the
residual `r⁽⁰⁾`, and the matrices `H_k`, `Ĥ_k` are `Arnoldi.hessenbergSq`, `Arnoldi.hessenberg`. -/
private theorem arnoldi_residual (hr : b - toEuclideanLin A x₀ ≠ 0) :
    (∀ k, arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k =
        Arnoldi.vec (toEuclideanLin A) (b - toEuclideanLin A x₀) k) ∧
      (∀ k, H A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k =
        Arnoldi.hessenbergSq (toEuclideanLin A) (b - toEuclideanLin A x₀) k) ∧
      ∀ k, Hhat A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k =
        Arnoldi.hessenberg (toEuclideanLin A) (b - toEuclideanLin A x₀) k := by
  obtain ⟨hvec, hH⟩ := arnoldi_normalize A hr
  refine ⟨hvec, fun k => ?_, fun k => ?_⟩
  · ext i j
    simp only [H, Arnoldi.hessenbergSq, Matrix.of_apply, hH]
  · ext i j
    simp only [Hhat, Arnoldi.hessenberg, Matrix.of_apply, hH]

/-- The degree of the residual is the grade the backbone's statements use. -/
private theorem degree_residual :
    degree A (b - toEuclideanLin A x₀) =
      Krylov.grade (toEuclideanLin A) (b - toEuclideanLin A x₀) :=
  degree_eq_grade A _

/-- **(4.59)–(4.62).** Let `k ≤ deg_A(r⁽⁰⁾)` steps of the Arnoldi algorithm be carried out from
`v₁ = r⁽⁰⁾/‖r⁽⁰⁾‖₂`. The vector `x⁽ᵏ⁾ = x⁽⁰⁾ + V_k z⁽ᵏ⁾` is the FOM iterate iff (4.60)–(4.61)
`V_kᵀ r⁽ᵏ⁾ = V_kᵀ r⁽⁰⁾ - V_kᵀ A V_k z⁽ᵏ⁾ = 0`, that is iff `z⁽ᵏ⁾` solves the Hessenberg system
`H_k z⁽ᵏ⁾ = ‖r⁽⁰⁾‖₂ e₁` (4.62), since `V_kᵀ r⁽⁰⁾ = ‖r⁽⁰⁾‖₂ e₁` (backbone
`Krylov.isGalerkinIterate_iff_mulVec_eq`); and the FOM iterate exists uniquely iff `H_k` is
nonsingular (`Krylov.existsUnique_isGalerkinIterate_iff_isUnit`). -/
theorem equation_4_62 (hr : b - toEuclideanLin A x₀ ≠ 0) {k : ℕ}
    (hk : k ≤ degree A (b - toEuclideanLin A x₀)) (z : Fin k → ℝ) :
    (equation_4_57 A b x₀ k (x₀ +
        ∑ j, z j • arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) j) ↔
      H A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k *ᵥ z =
        ‖b - toEuclideanLin A x₀‖ • e₁ k) ∧
      ((∃! x, equation_4_57 A b x₀ k x) ↔
        IsUnit (H A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k)) := by
  obtain ⟨hvec, hH, -⟩ := arnoldi_residual hr
  rw [degree_residual] at hk
  simp only [equation_4_57_iff, hvec, hH, smul_e₁_eq_firstVec]
  exact ⟨Krylov.isGalerkinIterate_iff_mulVec_eq hk z,
    Krylov.existsUnique_isGalerkinIterate_iff_isUnit hk⟩

/-- **Theorem 4.13.** In exact arithmetic the Arnoldi method yields the solution of `A x = b`,
`A` nonsingular, after at most `n` iterations: as soon as `k` reaches `deg_A(r⁽⁰⁾) ≤ n` — at
`k = n` because `K_n(A; r⁽⁰⁾) = ℝⁿ`, or earlier at a breakdown of the Arnoldi algorithm — the
FOM iterate exists uniquely and is the exact solution. The book's proof inverts `H_m` at the
breakdown without justification; nonsingularity of `H_m` at the grade is what
`Krylov.existsUnique_isGalerkinIterate_of_grade_le` supplies from the injectivity of `A`
(`Krylov.IsGalerkinIterate.apply_eq_of_grade_le` gives the exactness). -/
theorem theorem_4_13 (hA : IsUnit A) :
    degree A (b - toEuclideanLin A x₀) ≤ n ∧
      ∀ k, degree A (b - toEuclideanLin A x₀) ≤ k →
        (∃! x, equation_4_57 A b x₀ k x) ∧
          ∀ x, equation_4_57 A b x₀ k x → toEuclideanLin A x = b := by
  have hinj := toEuclideanLin_injective_of_isUnit hA
  refine ⟨degree_le A _, fun k hk => ?_⟩
  rw [degree_residual] at hk
  simp only [equation_4_57_iff]
  exact ⟨Krylov.existsUnique_isGalerkinIterate_of_grade_le hinj hk,
    fun x hx => hx.apply_eq_of_grade_le hk⟩

/-- **The residual formula before (4.63).** If `x⁽ᵏ⁾ = x⁽⁰⁾ + V_k z⁽ᵏ⁾` with
`H_k z⁽ᵏ⁾ = ‖r⁽⁰⁾‖₂ e₁`, `k ≥ 1`, the residual is `-(h_{k+1,k} z⁽ᵏ⁾_k) v_{k+1}` (backbone
`Krylov.residual_galerkin_eq`), so that for `k < deg_A(r⁽⁰⁾)`, where `‖v_{k+1}‖₂ = 1`,
`‖b - A x⁽ᵏ⁾‖₂ = h_{k+1,k} |e_kᵀ z⁽ᵏ⁾|` (`0`-based: `h_{k+1,k}` is `arnoldiH … k (k - 1)` and
`e_kᵀ z⁽ᵏ⁾` is `z ⟨k - 1, _⟩`), the quantity the stopping test (4.63) divides by `‖r⁽⁰⁾‖₂`. -/
theorem equation_4_63 (hr : b - toEuclideanLin A x₀ ≠ 0) {k : ℕ} (hk : 0 < k) (z : Fin k → ℝ)
    (hz : H A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k *ᵥ z =
      ‖b - toEuclideanLin A x₀‖ • e₁ k) :
    b - toEuclideanLin A (x₀ +
        ∑ j, z j • arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) j) =
        -(arnoldiH A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k (k - 1) *
            z ⟨k - 1, Nat.sub_lt hk one_pos⟩) •
          arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k ∧
      (k < degree A (b - toEuclideanLin A x₀) →
        ‖b - toEuclideanLin A (x₀ + ∑ j, z j •
            arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) j)‖ =
          arnoldiH A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k (k - 1) *
            |z ⟨k - 1, Nat.sub_lt hk one_pos⟩|) := by
  obtain ⟨hvec, hH, -⟩ := arnoldi_residual hr
  obtain ⟨-, hcoeff⟩ := arnoldi_normalize A hr
  rw [hH, smul_e₁_eq_firstVec] at hz
  have hres := Krylov.residual_galerkin_eq hk z hz
  simp only [hvec, hcoeff]
  refine ⟨hres, fun hlt => ?_⟩
  rw [degree_residual] at hlt
  have hnonneg : 0 ≤ Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀) k (k - 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, Arnoldi.coeff_succ_self, RCLike.ofReal_real_eq_id, id_eq]
    exact norm_nonneg _
  rw [hres, norm_smul, norm_neg, Real.norm_eq_abs, abs_mul, abs_of_nonneg hnonneg,
    Arnoldi.norm_vec_eq_one_of_lt_grade _ _ hlt, mul_one]

end FOM

/-! ### §4.4.2 The GMRES method -/

section GMRES

variable {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ : EuclideanSpace ℝ (Fin n)}

/-- **(4.64)–(4.65).** With `x⁽ᵏ⁾ = x⁽⁰⁾ + V_k z⁽ᵏ⁾`, the residual is
`r⁽ᵏ⁾ = r⁽⁰⁾ - A V_k z⁽ᵏ⁾ = V_{k+1} (‖r⁽⁰⁾‖₂ e₁ - Ĥ_k z⁽ᵏ⁾)`, because `r⁽⁰⁾ = ‖r⁽⁰⁾‖₂ v₁` and
(4.56) holds (backbone `Krylov.HessenbergRelation₂.residual_eq` for
`Arnoldi.hessenbergRelation`). -/
theorem equation_4_65 (hr : b - toEuclideanLin A x₀ ≠ 0) (k : ℕ) (z : Fin k → ℝ) :
    b - toEuclideanLin A (x₀ +
        ∑ j, z j • arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) j) =
      (b - toEuclideanLin A x₀) - toEuclideanLin A
        (∑ j, z j • arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) j) ∧
      b - toEuclideanLin A (x₀ +
        ∑ j, z j • arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) j) =
      ∑ i : Fin (k + 1), (‖b - toEuclideanLin A x₀‖ • e₁ (k + 1) -
          Hhat A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k *ᵥ z) i •
        arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) i := by
  obtain ⟨hvec, -, hHhat⟩ := arnoldi_residual hr
  refine ⟨by rw [map_add, sub_add_eq_sub_sub], ?_⟩
  simp only [hvec, hHhat, smul_e₁_eq_firstVec]
  exact (Arnoldi.hessenbergRelation (toEuclideanLin A) (b - toEuclideanLin A x₀)).residual_eq
    (Arnoldi.smul_vec_zero _ _).symm k z

/-- **(4.66).** For `k ≤ deg_A(r⁽⁰⁾)`, `x⁽⁰⁾ + V_k z⁽ᵏ⁾` is the GMRES iterate iff `z⁽ᵏ⁾` minimizes
`‖‖r⁽⁰⁾‖₂ e₁ - Ĥ_k z‖₂` over `z ∈ ℝᵏ` — the orthogonal `V_{k+1}` in (4.65) does not change the
Euclidean norm, `‖b - A (x⁽⁰⁾ + V_k z)‖₂ = ‖‖r⁽⁰⁾‖₂ e₁ - Ĥ_k z‖₂` (backbone
`Krylov.isMinResidualIterate_iff_isMinOn`, `Krylov.norm_residual_eq_norm_firstVec_sub_mulVec`). -/
theorem equation_4_66 (hr : b - toEuclideanLin A x₀ ≠ 0) {k : ℕ}
    (hk : k ≤ degree A (b - toEuclideanLin A x₀)) (z : Fin k → ℝ) :
    (equation_4_58 A b x₀ k (x₀ +
        ∑ j, z j • arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) j) ↔
      IsMinOn (fun y : Fin k → ℝ => ‖(toLp 2 (‖b - toEuclideanLin A x₀‖ • e₁ (k + 1) -
          Hhat A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k *ᵥ y) :
            EuclideanSpace ℝ (Fin (k + 1)))‖) Set.univ z) ∧
      ‖b - toEuclideanLin A (x₀ +
        ∑ j, z j • arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) j)‖ =
        ‖(toLp 2 (‖b - toEuclideanLin A x₀‖ • e₁ (k + 1) -
          Hhat A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k *ᵥ z) :
            EuclideanSpace ℝ (Fin (k + 1)))‖ := by
  obtain ⟨hvec, -, hHhat⟩ := arnoldi_residual hr
  rw [degree_residual] at hk
  simp only [hvec, hHhat, smul_e₁_eq_firstVec, (equation_4_58_iff A b x₀ k).1]
  exact ⟨Krylov.isMinResidualIterate_iff_isMinOn hk z,
    Krylov.norm_residual_eq_norm_firstVec_sub_mulVec hk z⟩

/-- **Property 4.8.** For `A` nonsingular, a breakdown of the Arnoldi algorithm at step `m` —
`deg_A(r⁽⁰⁾) ≤ m`, that is `h_{m+1,m} = 0` (`arnoldi_breakdown_iff`) — occurs iff the GMRES
iterate `x⁽ᵐ⁾` is the exact solution; the GMRES iterate is then unique. The book states it for
`m < n`; the equivalence holds for every `m`. Backbone
`Krylov.IsMinResidualIterate.apply_eq_of_grade_le` and `Krylov.grade_le_of_apply_eq`. -/
theorem property_4_8 (hA : IsUnit A) (m : ℕ) :
    (degree A (b - toEuclideanLin A x₀) ≤ m ↔
        ∀ x, equation_4_58 A b x₀ m x → toEuclideanLin A x = b) ∧
      ∃! x, equation_4_58 A b x₀ m x := by
  have hinj := toEuclideanLin_injective_of_isUnit hA
  obtain ⟨hiff, hex, hu⟩ := equation_4_58_iff A b x₀ m
  refine ⟨?_, hu hA⟩
  rw [degree_residual]
  simp only [hiff]
  constructor
  · intro hm x hx
    exact hx.apply_eq_of_grade_le hm hinj.injOn
  · intro h
    obtain ⟨x, hx⟩ := hex
    rw [hiff] at hx
    exact Krylov.grade_le_of_apply_eq hx.mem (h x hx)

/-- **The Givens paragraph after Program 23.** `Ĥ_k` is factored by `k` plane rotations into
`Q_k Ĥ_k = R_k`, upper triangular with a zero last row (backbone `Krylov.givensQ_mul_hessenbergOf`,
with `Q_k` the product of the rotations), the rotated right-hand side is
`f_k = Q_k (‖r⁽⁰⁾‖₂ e₁)` (`Krylov.givensQ_mulVec_firstVec`), and, for `k < deg_A(r⁽⁰⁾)`, the
`(k+1)`-th component of `f_k` — the backbone's `Krylov.gamma … k` — is, in absolute value, the
Euclidean norm of the residual of the GMRES iterate
(`Krylov.IsMinResidualIterate.norm_residual_eq_norm_gamma`), which is what makes the residual
available without forming `x⁽ᵏ⁾`. -/
theorem gmres_norm_residual_eq_norm_gamma (hr : b - toEuclideanLin A x₀ ≠ 0) (k : ℕ) :
    Krylov.givensQ (arnoldiH A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀))) k *
        Hhat A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k =
      Krylov.hessenbergOf (Krylov.rotated
        (arnoldiH A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀))) k) k ∧
      (Krylov.givensQ (arnoldiH A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)))
          k *ᵥ (‖b - toEuclideanLin A x₀‖ • e₁ (k + 1)) =
        fun i : Fin (k + 1) => if (i : ℕ) < k then
          Krylov.gvec (arnoldiH A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)))
            ‖b - toEuclideanLin A x₀‖ i
        else Krylov.gamma
          (arnoldiH A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)))
            ‖b - toEuclideanLin A x₀‖ k) ∧
      (k < degree A (b - toEuclideanLin A x₀) → ∀ x, equation_4_58 A b x₀ k x →
        ‖b - toEuclideanLin A x‖ = |Krylov.gamma
          (arnoldiH A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)))
            ‖b - toEuclideanLin A x₀‖ k|) := by
  obtain ⟨-, hcoeff⟩ := arnoldi_normalize A hr
  have hfun : arnoldiH A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) =
      Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀) :=
    funext fun i => funext (hcoeff i)
  obtain ⟨-, -, hHhat⟩ := arnoldi_residual hr
  rw [hfun, hHhat, smul_e₁_eq_firstVec]
  refine ⟨Krylov.givensQ_mul_hessenbergOf _ k, Krylov.givensQ_mulVec_firstVec _ _ k,
    fun hk x hx => ?_⟩
  rw [degree_residual] at hk
  rw [(equation_4_58_iff A b x₀ k).1] at hx
  have h := hx.norm_residual_eq_norm_gamma hk
  rwa [Real.norm_eq_abs] at h

end GMRES

/-! ### Remark 4.4: projection methods -/

section ProjectionMethods

variable (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))

/-- **Remark 4.4, projection methods.** For two subspaces `Y`, `L` of `ℝⁿ`, a *projection method*
generates an approximate solution `x` with `x ∈ x⁽⁰⁾ + Y` (the book writes `x ∈ Y`; the Krylov
instances need the affine translate, cf. (4.59)) and with the residual `b - A x` orthogonal to `L`;
*orthogonal* when `L = Y`, *oblique* otherwise. It is the backbone's `IsPetrovGalerkin`
(`remark_4_4_iff`). -/
def remark_4_4 (Y L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x - x₀ ∈ Y ∧ b - toEuclideanLin A x ∈ Lᗮ

/-- A projection method is the backbone's Petrov–Galerkin specification, and an orthogonal one the
Galerkin specification. -/
theorem remark_4_4_iff (Y L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    (remark_4_4 A b x₀ Y L x ↔ IsPetrovGalerkin (toEuclideanLin A) b x₀ Y L x) ∧
      (remark_4_4 A b x₀ Y Y x ↔ IsGalerkin (toEuclideanLin A) b x₀ Y x) :=
  ⟨⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mem, h.orth⟩⟩, ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mem, h.orth⟩⟩⟩

/-- **Remark 4.4, the Krylov instances.** The Arnoldi method (FOM) is the orthogonal projection
method with `L_k = Y_k = K_k(A; r⁽⁰⁾)`, and GMRES is the oblique projection method with
`Y_k = K_k(A; r⁽⁰⁾)` and `L_k = A Y_k` (backbone `IsMinResidual.iff_isPetrovGalerkin`). -/
theorem remark_4_4_krylov (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    (equation_4_57 A b x₀ k x ↔ remark_4_4 A b x₀
        (krylovSubspace A (b - toEuclideanLin A x₀) k)
        (krylovSubspace A (b - toEuclideanLin A x₀) k) x) ∧
      (equation_4_58 A b x₀ k x ↔ remark_4_4 A b x₀
        (krylovSubspace A (b - toEuclideanLin A x₀) k)
        ((krylovSubspace A (b - toEuclideanLin A x₀) k).map (toEuclideanLin A)) x) := by
  constructor
  · exact and_congr Iff.rfl ⟨fun h => (Submodule.mem_orthogonal _ _).2 h,
      fun h => (Submodule.mem_orthogonal _ _).1 h⟩
  · rw [(equation_4_58_iff A b x₀ k).1, (remark_4_4_iff A b x₀ _ _ x).1, krylovSubspace_eq]
    exact IsMinResidual.iff_isPetrovGalerkin

/-- The coordinate subspace of a single index is the line spanned by the corresponding basis
vector. -/
private theorem blockSubspace_id_eq_span (i : Fin n) :
    EuclideanSpace.blockSubspace ℝ (id : Fin n → Fin n) i =
      ℝ ∙ EuclideanSpace.single i (1 : ℝ) := by
  ext v
  rw [EuclideanSpace.mem_blockSubspace, Submodule.mem_span_singleton]
  constructor
  · intro hv
    refine ⟨v i, ?_⟩
    ext j
    by_cases hij : j = i
    · subst hij; simp
    · rw [hv j hij]; simp [hij]
  · rintro ⟨c, rfl⟩ j hj
    have hj' : j ≠ i := hj
    simp [hj']

/-- **Remark 4.4, the Gauss–Seidel method.** "The Gauss–Seidel method is an orthogonal projection
method where at the `k`-th step `K = span(e_k)`, the projection steps being carried out cyclically
from `1` to `n`": for a matrix with nonzero diagonal, one Gauss–Seidel sweep from `x` is the sweep
of the multiplicative projection process (backbone `Projection.multiplicativeStep`) over the pairs
`Y_i = L_i = span(e_i)`, `i = 1, …, n` in increasing order — the backbone's
`Matrix.blockGaussSeidelSplitting_step_eq_multiplicativeStep` at the trivial block labelling
`π = id`, whose blocks are the lines `span(e_i)` (`EuclideanSpace.blockSubspace`); each of its steps
is the one-dimensional orthogonal projection step `Projection.step1` onto `span(e_i)`, a Galerkin
step (`Projection.step1_isGalerkin`). -/
theorem remark_4_4_gaussSeidel (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) :
    (∀ i, EuclideanSpace.blockSubspace ℝ (id : Fin n → Fin n) i =
        ℝ ∙ EuclideanSpace.single i (1 : ℝ)) ∧
      (toLp 2 (sorSweep A 1 b x) : EuclideanSpace ℝ (Fin n)) =
        Projection.multiplicativeStep (toEuclideanLin A) (toLp 2 b)
          (EuclideanSpace.blockSubspace ℝ id) (EuclideanSpace.blockSubspace ℝ id)
          (isNondegeneratePair_blockSubspace ((blockDiagPart_id A).symm ▸ h))
          ((Finset.univ : Finset (Fin n)).sort (· ≤ ·)) (toLp 2 x) ∧
      ∀ (i : Fin n) (y : EuclideanSpace ℝ (Fin n)),
        Projection.pairStep (toEuclideanLin A) (toLp 2 b) (EuclideanSpace.blockSubspace ℝ id i)
            (EuclideanSpace.blockSubspace ℝ id i)
            (isNondegeneratePair_blockSubspace ((blockDiagPart_id A).symm ▸ h) i) y =
          Projection.step1 (toEuclideanLin A) (toLp 2 b) (EuclideanSpace.single i 1)
            (EuclideanSpace.single i 1) y ∧
        IsGalerkin (toEuclideanLin A) (toLp 2 b) y (ℝ ∙ EuclideanSpace.single i (1 : ℝ))
          (Projection.step1 (toEuclideanLin A) (toLp 2 b) (EuclideanSpace.single i 1)
            (EuclideanSpace.single i 1) y) := by
  have h' : IsUnit (blockDiagPart (id : Fin n → Fin n) A) := (blockDiagPart_id A).symm ▸ h
  refine ⟨blockSubspace_id_eq_span, ?_, fun i y => ?_⟩
  · have hm : (gaussSeidelSplitting A h).m = (blockGaussSeidelSplitting id A h').m := by
      rw [(equation_4_13 h b x).2.2.1, D_sub_E]
      change _ = blockDiagPart id A + blockStrictLower id A
      rw [blockDiagPart_id, blockStrictLower_id]
    rw [blockGaussSeidelSplitting_step_eq_multiplicativeStep h', sorSweep_one_eq_mulVecStep A h,
      Stationary.Splitting.mulVecStep_eq_add_inv_mulVec, toLp_add, ← toEuclideanLin_toLp, toLp_sub,
      ← toEuclideanLin_toLp, hm]
  · have hdiag : A i i ≠ 0 := (isUnit_diagPart_iff A).1 h i
    have hinner : inner ℝ (EuclideanSpace.single i (1 : ℝ))
        (toEuclideanLin A (EuclideanSpace.single i (1 : ℝ))) ≠ 0 := by
      rw [EuclideanSpace.inner_single_left, ofLp_toEuclideanLin]
      simp [Matrix.mulVec, dotProduct, EuclideanSpace.single, hdiag]
    have hPG := Projection.step1_isPetrovGalerkin (A := toEuclideanLin A) (b := toLp 2 b)
      (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) y hinner
    refine ⟨?_, hPG⟩
    have hspan := blockSubspace_id_eq_span (n := n) i
    have hu := (existsUnique_isPetrovGalerkin_of_finrank_eq (A := toEuclideanLin A) (toLp 2 b) y
      (EuclideanSpace.blockSubspace ℝ id i) (EuclideanSpace.blockSubspace ℝ id i)
      (isNondegeneratePair_blockSubspace h' i).finrank_eq
      (isNondegeneratePair_blockSubspace h' i).eq_zero_of_mem_orthogonal)
    refine (hu.unique ?_ ?_).symm
    · rw [hspan]; exact hPG
    · exact Projection.pairStep_isPetrovGalerkin _ y

end ProjectionMethods

/-! ### §4.4.3 The Lanczos method for symmetric systems -/

section Lanczos

variable {A : Matrix (Fin n) (Fin n) ℝ} (v₁ : EuclideanSpace ℝ (Fin n))

/-- **§4.4.3, first paragraph.** If `A` is symmetric the Arnoldi matrix `H_m` is symmetric and
tridiagonal, `H_m = T_m` with `α_i = h_ii` and `β_i = h_{i-1,i} = h_{i,i-1}` (backbone
`Lanczos.hessenbergSq_eq_map_tridiag`, `Lanczos.tridiag_isSymm`, `Lanczos.tridiag_isTridiagonal`,
`Lanczos.alpha`, `Lanczos.beta`), and the Arnoldi recurrence reduces to the three-term Lanczos
recurrence `A v_{j+1} = β_j v_j + α_{j+1} v_{j+1} + β_{j+1} v_{j+2}` (`0`-based) that Program 24
computes (`Lanczos.apply_vec`). -/
theorem lanczos_tridiagonal (hA : A.IsSymm) (hv : ‖v₁‖ = 1) (m : ℕ) :
    H A v₁ m = Lanczos.tridiag (toEuclideanLin A) v₁ m ∧ (H A v₁ m).IsSymm ∧
      (H A v₁ m).IsTridiagonal ∧
      (∀ i, Lanczos.alpha (toEuclideanLin A) v₁ i = arnoldiH A v₁ i i) ∧
      (∀ i, Lanczos.beta (toEuclideanLin A) v₁ i = arnoldiH A v₁ (i + 1) i) ∧
      ∀ j, toEuclideanLin A (arnoldi A v₁ (j + 1)) =
        Lanczos.beta (toEuclideanLin A) v₁ j • arnoldi A v₁ j +
          Lanczos.alpha (toEuclideanLin A) v₁ (j + 1) • arnoldi A v₁ (j + 1) +
          Lanczos.beta (toEuclideanLin A) v₁ (j + 1) • arnoldi A v₁ (j + 2) := by
  have hA' := hA.isSymmetric_toEuclideanLin
  obtain ⟨hvec, hH, -⟩ := arnoldi_eq_vec A v₁ hv
  have hHm : H A v₁ m = Lanczos.tridiag (toEuclideanLin A) v₁ m := by
    have h := (equation_4_56 A v₁ hv m).2.2.2.2.1
    rw [h, Lanczos.hessenbergSq_eq_map_tridiag v₁ hA' m, Algebra.algebraMap_self, RingHom.coe_id]
    exact Matrix.map_id _
  refine ⟨hHm, hHm ▸ Lanczos.tridiag_isSymm _ _ _, hHm ▸ Lanczos.tridiag_isTridiagonal _ _ _,
    fun i => ?_, fun i => ?_, fun j => ?_⟩
  · rw [Lanczos.alpha, hH, RCLike.re_to_real]
  · rw [Lanczos.beta, hH, Arnoldi.coeff_succ_self, RCLike.ofReal_real_eq_id, id_eq]
  · simp only [hvec]
    exact Lanczos.apply_vec v₁ hA' j

variable {b x₀ : EuclideanSpace ℝ (Fin n)}

/-- **§4.4.3, the Lanczos method for linear systems.** The residual of the FOM (Lanczos) iterate at
step `k` is a multiple of the next Arnoldi (Lanczos) vector, `r⁽ᵏ⁾ = γ_k v_{k+1}` for a suitable
`γ_k` — the scalar of `equation_4_63` — so that the residuals at different steps are mutually
orthogonal (backbone `Krylov.IsGalerkinIterate.residual_mem_span`,
`Krylov.IsGalerkinIterate.inner_residual_eq_zero`). The statement holds for every `A`; the book
makes it in the symmetric context. -/
theorem lanczos_residual_eq_smul (hr : b - toEuclideanLin A x₀ ≠ 0) {k : ℕ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : equation_4_57 A b x₀ k x) :
    (∃ γ : ℝ, b - toEuclideanLin A x =
        γ • arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k) ∧
      ∀ {k' : ℕ} {x' : EuclideanSpace ℝ (Fin n)}, equation_4_57 A b x₀ k' x' → k ≠ k' →
        inner ℝ (b - toEuclideanLin A x) (b - toEuclideanLin A x') = 0 := by
  obtain ⟨hvec, -, -⟩ := arnoldi_residual hr
  rw [equation_4_57_iff] at hx
  refine ⟨?_, fun hx' hkk' => ?_⟩
  · obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.1 hx.residual_mem_span
    exact ⟨γ, by rw [hvec, hγ]⟩
  · rw [equation_4_57_iff] at hx'
    exact hx.inner_residual_eq_zero hx' hkk'

/-- **Remark 4.5 (the conjugate gradient method).** For `A` symmetric positive definite, the
conjugate gradient iterate of §4.3.4 is the Lanczos-method (FOM) iterate
(`CG.isGalerkinIterate` through `cg_eq_CG`), its residuals are multiples of the Lanczos vectors,
`v_{k+1} = (-1)ᵏ r⁽ᵏ⁾/‖r⁽ᵏ⁾‖₂` while `r⁽ᵏ⁾ ≠ 0` (`CG.arnoldi_vec_eq`), and its descent directions
are mutually `A`-conjugate — the book's `P_kᵀ A P_k` diagonal (`equation_4_42`). The book's route
through the `LU` factorization `H_k = L_k U_k`, `P_k = V_k U_k⁻¹` is not restated: the remark's
content is the identification of the two iterates. -/
theorem remark_4_5 (hA : A.PosDef) (k : ℕ) :
    equation_4_57 A b x₀ k (cgX A b x₀ k) ∧
      (b - toEuclideanLin A x₀ ≠ 0 → cgR A b x₀ k ≠ 0 →
        arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k =
          ((-1) ^ k * ‖cgR A b x₀ k‖⁻¹) • cgR A b x₀ k) ∧
      ∀ i j, i ≠ j → inner ℝ (toEuclideanLin A (cgP A b x₀ i)) (cgP A b x₀ j) = 0 := by
  have hA' := posDef_isSymmetricCoercive_toEuclideanLin hA
  refine ⟨?_, fun hr hk => ?_, (equation_4_42 hA).2⟩
  · rw [equation_4_57_iff, cgX_eq_CG hA]
    exact CG.isGalerkinIterate b x₀ hA' k
  · obtain ⟨hvec, -, -⟩ := arnoldi_residual hr
    rw [hvec, cgR_eq_CG hA] at *
    have h := CG.arnoldi_vec_eq b x₀ hA' k hk
    rwa [RCLike.ofReal_real_eq_id, id_eq] at h

/-- **§4.4.3, last paragraph: the conjugate residual method.** For `A` symmetric positive definite,
the GMRES method simplifies to the conjugate residual (CR) method, whose iterates are the GMRES
iterates (backbone `CR.isMinResidualIterate` for the recurrence `CR.iterate`) and whose residuals
are mutually `A`-conjugate (`CR.inner_residual_apply_residual_eq_zero`). GCR and ORTHOMIN are
named without content and have no node. -/
theorem cr_residual_conjugate (hA : A.PosDef) :
    (∀ k, equation_4_58 A b x₀ k (CR.iterate (toEuclideanLin A) b x₀ k).x) ∧
      ∀ i j, i ≠ j → inner ℝ (CR.iterate (toEuclideanLin A) b x₀ i).r
        (toEuclideanLin A (CR.iterate (toEuclideanLin A) b x₀ j).r) = 0 := by
  have hA' := posDef_isSymmetricCoercive_toEuclideanLin hA
  refine ⟨fun k => ?_, fun i j hij => CR.inner_residual_apply_residual_eq_zero b x₀ hA' hij⟩
  rw [(equation_4_58_iff A b x₀ k).1]
  exact CR.isMinResidualIterate b x₀ hA' k

end Lanczos


end QuarteroniSaccoSaleri.Chapter04
