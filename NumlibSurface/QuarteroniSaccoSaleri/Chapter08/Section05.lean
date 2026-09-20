import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Determinant
import Numlib.Analysis.Calculus.TaylorSegment
import Numlib.Approximation.MvPolynomial
import Numlib.Approximation.NodalInterpolation
import Numlib.Approximation.Unisolvent
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section01

/-!
# Quarteroni–Sacco–Saleri §8.5: extension to the two-dimensional case

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §8.5: tensor-product Lagrange interpolation on a rectangle (§8.5.1),
the ill-posed bilinear example of Remark 8.1, and piecewise interpolation on a triangulation
(§8.5.2): the affine map (8.34) from the reference triangle, the space `𝒫_k` (8.35) with
`dim 𝒫_k(T) = (k+1)(k+2)/2`, the reference-element identity behind (8.38), and the sup-norm
interpolation error (8.39) on a triangle, with the reference Lagrange basis as data. The global
estimate (8.40) needs a triangulation and is stated in the plan and left open there.

The algebra is `Numlib/Approximation/NodalInterpolation` (`Approximation.nodalInterp`,
`Approximation.IsNodalBasis`, `Approximation.nodalInterp_comp`),
`Numlib/Approximation/Unisolvent` (`Approximation.IsUnisolvent`) and
`Numlib/Approximation/MvPolynomial` (`Approximation.mvPolyLE`, `Approximation.finrank_mvPolyLE`);
the analysis behind (8.39) is `Numlib/Analysis/Calculus/TaylorSegment` (Taylor's theorem along a
segment with the Lagrange bound, and the polynomial nature of the Taylor polynomial).
The triangulation itself (admissibility, the global nodes `z_i`, `𝒫_k^c(Ω)`, (8.36)–(8.37)) is a
definition with no numbered result in reach and is not stated; Example 8.7 is a table.

## Main definitions

* `tensorProductInterp x y f` — `Π_{n,m} f(x, y) = ∑_i ∑_j f(x_i, y_j) l_i(x) l_j(y)`.
* `remark_8_1_space`, `remark_8_1_node` — the bilinear polynomials `a₃xy + a₂x + a₁y + a₀` on the
  square `[-1, 1]²` and the four nodes `(-1, 0), (0, -1), (1, 0), (0, 1)` of Remark 8.1.
* `equation_8_34 a₁ a₂ a₃` — the affine map `F_T x̂ = B_T x̂ + b_T` from the reference triangle onto
  the triangle with vertices `a₁, a₂, a₃`, and `equation_8_34_matrix` its matrix `B_T`.
* `referenceTriangle` — the reference triangle `T̂` with vertices `(0, 0), (1, 0), (0, 1)`.

## Main results

* `tensorProductInterp_isNodalBasis`, `tensorProductInterp_apply_node`,
  `tensorProductInterp_mem_span` — the tensor-product interpolant reproduces the data at the grid
  nodes and is a polynomial of degree `≤ n` in `x` and `≤ m` in `y`.
* `remark_8_1`, `remark_8_1_apply_node` — the bilinear interpolation problem at the four nodes is
  not unisolvent: `xy` vanishes at all of them, so the coefficient `a₃` is free.
* `equation_8_34_vertex`, `equation_8_34_bijective` — `F_T` sends the reference vertices to
  `a₁, a₂, a₃` and is a bijection exactly when `det B_T ≠ 0`.
* `equation_8_35_finrank` — `d_k = dim 𝒫_k(T) = (k+1)(k+2)/2`.
* `equation_8_38_comp` — the element interpolant is the reference interpolant read through `F_T`.
* `equation_8_39` — `‖f - Π_T^k f‖_{∞,T} ≤ C h_T^{k+1} ‖f^{(k+1)}‖_{∞,T}` with
  `C = (∑_m ‖l̂_m‖_{∞,T̂} + 1)/(k+1)!`, for a reference Lagrange basis `l̂_m` of `𝒫_k(T̂)` given as
  data; `equation_8_34_segment_mem`, `norm_equation_8_34_sub_vertex_le` and
  `exists_mvPolynomial_taylor_equation_8_34` are its geometric and algebraic ingredients.
* `equation_8_39_linear` — the case `k = 1` with the nodes at the vertices and the barycentric
  coordinates `linearShape` as the reference basis (`linearShape_isNodalBasis`,
  `linearShape_span`): `‖f - Π_T^1 f‖_{∞,T} ≤ 2 h_T² ‖f''‖_{∞,T}`.

## Conventions

Points of the plane are `ℝ × ℝ`; a polynomial space on a set `D ⊆ ℝ²` is `Approximation.mvPolyLE`
on `D : Set (Fin 2 → ℝ)`.
-/

open Polynomial Set
open scoped Nat

namespace QuarteroniSaccoSaleri.Chapter08

variable {n m : ℕ}

/-! ### §8.5.1: tensor-product interpolation -/

/-- **`Π_{n,m} f`** (§8.5.1): the tensor-product interpolant
`Π_{n,m} f(x, y) = ∑_{i=0}^n ∑_{j=0}^m f(x_i, y_j) l_i(x) l_j(y)` on the grid `(x_i, y_j)`, with
`l_i ∈ 𝒫_n` and `l_j ∈ 𝒫_m` the one-dimensional characteristic polynomials in `x` and `y`: the nodal
interpolation operator `Approximation.nodalInterp` with the product shape functions. -/
noncomputable def tensorProductInterp (x : Fin (n + 1) → ℝ) (y : Fin (m + 1) → ℝ)
    (f : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  Approximation.nodalInterp (fun p : Fin (n + 1) × Fin (m + 1) => (x p.1, y p.2))
    (fun p q => (Lagrange.basis Finset.univ x p.1).eval q.1
      * (Lagrange.basis Finset.univ y p.2).eval q.2) f

/-- The product shape functions `l_i(x) l_j(y)` are dual to the grid nodes `(x_i, y_j)`: (8.3) in
each variable. -/
theorem tensorProductInterp_isNodalBasis {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    {y : Fin (m + 1) → ℝ} (hy : Function.Injective y) :
    Approximation.IsNodalBasis (fun p : Fin (n + 1) × Fin (m + 1) => (x p.1, y p.2))
      fun p q => (Lagrange.basis Finset.univ x p.1).eval q.1
        * (Lagrange.basis Finset.univ y p.2).eval q.2 where
  eval_self p := by simp [equation_8_3 hx, equation_8_3 hy]
  eval_of_ne p q hpq := by
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h1 h2)
      simp [equation_8_3 hx, equation_8_3 hy, h2]
    · simp [equation_8_3 hx, equation_8_3 hy, h1]

/-- **§8.5.1.** The tensor-product interpolant takes the values `α_ij = f(x_i, y_j)` at the grid
nodes: `Approximation.IsNodalBasis.nodalInterp_apply_node`. -/
theorem tensorProductInterp_apply_node {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    {y : Fin (m + 1) → ℝ} (hy : Function.Injective y) (f : ℝ × ℝ → ℝ) (i : Fin (n + 1))
    (j : Fin (m + 1)) : tensorProductInterp x y f (x i, y j) = f (x i, y j) :=
  (tensorProductInterp_isNodalBasis hx hy).nodalInterp_apply_node f (i, j)

/-- A polynomial function of degree at most `n` lies in the span of the monomials `s ↦ s^p`,
`p ≤ n`, as a function on any set. -/
private theorem eval_mem_span_monomials {P : ℝ[X]} (hP : P.natDegree ≤ n) :
    (fun s : ℝ => P.eval s)
      ∈ Submodule.span ℝ (Set.range fun p : Fin (n + 1) => fun s : ℝ => s ^ (p : ℕ)) := by
  have : (fun s : ℝ => P.eval s)
      = ∑ p : Fin (n + 1), P.coeff p • fun s : ℝ => s ^ (p : ℕ) := by
    funext s
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP), Finset.sum_apply,
      ← Fin.sum_univ_eq_sum_range (fun p => P.coeff p * s ^ p)]
    simp
  rw [this]
  exact Submodule.sum_mem _ fun p _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

/-- **§8.5.1.** The tensor-product interpolant is a polynomial of degree `≤ n` in `x` and `≤ m` in
`y`: it lies in the span of the monomials `x^p y^q`, `p ≤ n`, `q ≤ m`. -/
theorem tensorProductInterp_mem_span {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    {y : Fin (m + 1) → ℝ} (hy : Function.Injective y) (f : ℝ × ℝ → ℝ) :
    tensorProductInterp x y f ∈ Submodule.span ℝ
      (Set.range fun pq : Fin (n + 1) × Fin (m + 1) =>
        fun q : ℝ × ℝ => q.1 ^ (pq.1 : ℕ) * q.2 ^ (pq.2 : ℕ)) := by
  classical
  have hcard : ∀ k, (Finset.univ : Finset (Fin (k + 1))).card = k + 1 := fun k => by simp
  -- the shape functions lie in the span
  have hshape : ∀ p : Fin (n + 1) × Fin (m + 1),
      (fun q : ℝ × ℝ => (Lagrange.basis Finset.univ x p.1).eval q.1
        * (Lagrange.basis Finset.univ y p.2).eval q.2) ∈ Submodule.span ℝ
          (Set.range fun pq : Fin (n + 1) × Fin (m + 1) =>
            fun q : ℝ × ℝ => q.1 ^ (pq.1 : ℕ) * q.2 ^ (pq.2 : ℕ)) := by
    intro p
    have hdx : (Lagrange.basis Finset.univ x p.1).natDegree ≤ n := by
      rw [Lagrange.natDegree_basis hx.injOn (Finset.mem_univ _), hcard]
      simp
    have hdy : (Lagrange.basis Finset.univ y p.2).natDegree ≤ m := by
      rw [Lagrange.natDegree_basis hy.injOn (Finset.mem_univ _), hcard]
      simp
    have hx' : (fun q : ℝ × ℝ => (Lagrange.basis Finset.univ x p.1).eval q.1)
        = ∑ a : Fin (n + 1), (Lagrange.basis Finset.univ x p.1).coeff a •
            fun q : ℝ × ℝ => q.1 ^ (a : ℕ) := by
      funext q
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdx), Finset.sum_apply,
        ← Fin.sum_univ_eq_sum_range (fun a => (Lagrange.basis Finset.univ x p.1).coeff a * q.1 ^ a)]
      simp
    have hy' : (fun q : ℝ × ℝ => (Lagrange.basis Finset.univ y p.2).eval q.2)
        = ∑ b : Fin (m + 1), (Lagrange.basis Finset.univ y p.2).coeff b •
            fun q : ℝ × ℝ => q.2 ^ (b : ℕ) := by
      funext q
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdy), Finset.sum_apply,
        ← Fin.sum_univ_eq_sum_range (fun b => (Lagrange.basis Finset.univ y p.2).coeff b * q.2 ^ b)]
      simp
    have : (fun q : ℝ × ℝ => (Lagrange.basis Finset.univ x p.1).eval q.1
        * (Lagrange.basis Finset.univ y p.2).eval q.2)
        = ∑ a : Fin (n + 1), ∑ b : Fin (m + 1),
            ((Lagrange.basis Finset.univ x p.1).coeff a
                * (Lagrange.basis Finset.univ y p.2).coeff b)
              • fun q : ℝ × ℝ => q.1 ^ (a : ℕ) * q.2 ^ (b : ℕ) := by
      funext q
      have h1 := congrFun hx' q
      have h2 := congrFun hy' q
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
      rw [h1, h2, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, b), rfl⟩)
  unfold tensorProductInterp Approximation.nodalInterp
  have : (fun q : ℝ × ℝ => ∑ p : Fin (n + 1) × Fin (m + 1),
      ((Lagrange.basis Finset.univ x p.1).eval q.1 * (Lagrange.basis Finset.univ y p.2).eval q.2)
        • f (x p.1, y p.2))
      = ∑ p : Fin (n + 1) × Fin (m + 1), f (x p.1, y p.2) •
          fun q : ℝ × ℝ => (Lagrange.basis Finset.univ x p.1).eval q.1
            * (Lagrange.basis Finset.univ y p.2).eval q.2 := by
    funext q
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun p _ => mul_comm _ _
  rw [this]
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (hshape p)

/-! ### Remark 8.1: the bilinear problem at four nodes -/

/-- The unit square `[-1, 1]²`, as the product of two closed intervals. -/
abbrev remark_8_1_square : Type := Icc (-1 : ℝ) 1 × Icc (-1 : ℝ) 1

/-- The coordinate functions `x` and `y` on the square, as continuous functions. -/
noncomputable def remark_8_1_coord : Fin 2 → C(remark_8_1_square, ℝ) :=
  ![⟨fun q => (q.1 : ℝ), by fun_prop⟩, ⟨fun q => (q.2 : ℝ), by fun_prop⟩]

/-- **Remark 8.1**, the space of the polynomials `p(x, y) = a₃ xy + a₂ x + a₁ y + a₀` of degree `1`
with respect to each of `x` and `y`, on the square `[-1, 1]²`. -/
noncomputable def remark_8_1_space : Submodule ℝ C(remark_8_1_square, ℝ) :=
  Submodule.span ℝ {1, remark_8_1_coord 0, remark_8_1_coord 1,
    remark_8_1_coord 0 * remark_8_1_coord 1}

/-- **Remark 8.1**, the four nodes `(-1, 0), (0, -1), (1, 0), (0, 1)`. -/
noncomputable def remark_8_1_node : Fin 4 → remark_8_1_square :=
  ![(⟨-1, by norm_num⟩, ⟨0, by norm_num⟩), (⟨0, by norm_num⟩, ⟨-1, by norm_num⟩),
    (⟨1, by norm_num⟩, ⟨0, by norm_num⟩), (⟨0, by norm_num⟩, ⟨1, by norm_num⟩)]

/-- **Remark 8.1**, the mechanism: the product `xy` vanishes at each of the four nodes. -/
theorem remark_8_1_apply_node (k : Fin 4) :
    (remark_8_1_coord 0 * remark_8_1_coord 1) (remark_8_1_node k) = 0 := by
  fin_cases k <;> simp [remark_8_1_coord, remark_8_1_node]

/-- **Remark 8.1.** Interpolation by polynomials of degree `1` with respect to `x` and `y`,
`p(x, y) = a₃ xy + a₂ x + a₁ y + a₀`, at the four distinct nodes `(-1, 0), (0, -1), (1, 0), (0, 1)`
does not in general admit a unique solution: the problem is not unisolvent in the sense of
`Numlib/Approximation/Unisolvent`, because `xy` is a nonzero element of the space vanishing at all
four nodes — the interpolation constraints are satisfied by any value of the coefficient `a₃`. -/
theorem remark_8_1 :
    ¬ Approximation.IsUnisolvent remark_8_1_space
      fun k => ContinuousMap.evalCLM ℝ (remark_8_1_node k) := by
  intro h
  obtain ⟨u, -, huniq⟩ := h 0
  have hmem : remark_8_1_coord 0 * remark_8_1_coord 1 ∈ remark_8_1_space :=
    Submodule.subset_span (by simp)
  have h1 := huniq ⟨_, hmem⟩ fun k => by simpa using remark_8_1_apply_node k
  have h2 := huniq 0 fun k => by simp
  have h3 : remark_8_1_coord 0 * remark_8_1_coord 1 = 0 := by
    have := h1.trans h2.symm
    simpa using congrArg Subtype.val this
  have := congrArg (fun g : C(remark_8_1_square, ℝ) =>
    g (⟨1 / 2, by norm_num⟩, ⟨1 / 2, by norm_num⟩)) h3
  norm_num [remark_8_1_coord] at this

/-! ### §8.5.2: the affine map from the reference triangle, and `𝒫_k` -/

/-- **(8.34), the affine map** `F_T ξ = B_T ξ + b_T` from the reference triangle with vertices
`(0, 0), (1, 0), (0, 1)` onto the triangle `T` with vertices `a₁, a₂, a₃`:
`B_T = [a₂ - a₁ | a₃ - a₁]` and `b_T = a₁`, that is
`F_T (ξ, η) = a₁ + ξ (a₂ - a₁) + η (a₃ - a₁)`. -/
noncomputable def equation_8_34 (a₁ a₂ a₃ : ℝ × ℝ) : ℝ × ℝ →ᵃ[ℝ] ℝ × ℝ :=
  ((LinearMap.fst ℝ ℝ ℝ).smulRight (a₂ - a₁)
    + (LinearMap.snd ℝ ℝ ℝ).smulRight (a₃ - a₁)).toAffineMap + AffineMap.const ℝ (ℝ × ℝ) a₁

/-- **(8.34), the matrix** `B_T = [x₂ - x₁, x₃ - x₁; y₂ - y₁, y₃ - y₁]`. -/
def equation_8_34_matrix (a₁ a₂ a₃ : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a₂.1 - a₁.1, a₃.1 - a₁.1; a₂.2 - a₁.2, a₃.2 - a₁.2]

/-- The value of `F_T`. -/
theorem equation_8_34_apply (a₁ a₂ a₃ : ℝ × ℝ) (p : ℝ × ℝ) :
    equation_8_34 a₁ a₂ a₃ p = p.1 • (a₂ - a₁) + p.2 • (a₃ - a₁) + a₁ := by
  simp [equation_8_34]

/-- **(8.34)**: `F_T` sends the vertices `(0, 0), (1, 0), (0, 1)` of the reference triangle to the
vertices `a₁, a₂, a₃` of `T`. -/
theorem equation_8_34_vertex (a₁ a₂ a₃ : ℝ × ℝ) :
    equation_8_34 a₁ a₂ a₃ (0, 0) = a₁ ∧ equation_8_34 a₁ a₂ a₃ (1, 0) = a₂ ∧
      equation_8_34 a₁ a₂ a₃ (0, 1) = a₃ := by
  simp [equation_8_34_apply]

/-- The matrix of the linear part of `F_T` in the standard basis is `B_T`. -/
theorem toMatrix_equation_8_34_linear (a₁ a₂ a₃ : ℝ × ℝ) :
    LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      (equation_8_34 a₁ a₂ a₃).linear = equation_8_34_matrix a₁ a₂ a₃ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, equation_8_34, equation_8_34_matrix,
      Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one, Module.Basis.coe_finTwoProd_repr]

/-- **(8.34)**: `F_T` is a bijection of the plane exactly when `B_T` is invertible, `det B_T ≠ 0`,
that is, when the three vertices are not collinear. -/
theorem equation_8_34_bijective (a₁ a₂ a₃ : ℝ × ℝ) :
    Function.Bijective (equation_8_34 a₁ a₂ a₃) ↔ (equation_8_34_matrix a₁ a₂ a₃).det ≠ 0 := by
  set L := (equation_8_34 a₁ a₂ a₃).linear with hL
  have hF : ⇑(equation_8_34 a₁ a₂ a₃) = (fun v => v + a₁) ∘ ⇑L := by
    funext p
    simp [hL, equation_8_34]
  have hdet : L.det = (equation_8_34_matrix a₁ a₂ a₃).det := by
    rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), toMatrix_equation_8_34_linear]
  rw [hF, Function.Bijective.of_comp_iff' (AddGroup.addRight_bijective a₁), ← hdet,
    Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]
  exact ⟨fun h => h.1, fun h => ⟨h, LinearMap.injective_iff_surjective.mp h⟩⟩

/-- **(8.35), `d_k = dim 𝒫_k(T) = (k+1)(k+2)/2`.** The space `𝒫_k(T)` of polynomials of total
degree `≤ k` in two variables, restricted to a set `T ⊆ ℝ²` with nonempty interior (a triangle),
is `Approximation.mvPolyLE T k`, of dimension `C(k + 2, 2) = (k+1)(k+2)/2`:
`Approximation.finrank_mvPolyLE`. -/
theorem equation_8_35_finrank {T : Set (Fin 2 → ℝ)} (hT : (interior T).Nonempty) (k : ℕ) :
    Module.finrank ℝ (Approximation.mvPolyLE T k) = (k + 1) * (k + 2) / 2 := by
  rw [Approximation.finrank_mvPolyLE hT, Fintype.card_fin, Nat.choose_two_right,
    show k + 2 - 1 = k + 1 from rfl, mul_comm]

/-- **The reference-element identity behind (8.38)**, `l_{j,T} = l̂_j ∘ F_T⁻¹`: for local nodes
`ẑ_m` and basis functions `l̂_m` on the reference triangle and a left inverse `G` of `F_T`, the
element interpolant `Π_T^k f = ∑_m f(F_T ẑ_m) (l̂_m ∘ G)` satisfies
`(Π_T^k f) ∘ F_T = Π̂^k (f ∘ F_T)`: `Approximation.nodalInterp_comp`. -/
theorem equation_8_38_comp {ι : Type*} [Fintype ι] (a₁ a₂ a₃ : ℝ × ℝ) {G : ℝ × ℝ → ℝ × ℝ}
    (hG : Function.LeftInverse G (equation_8_34 a₁ a₂ a₃)) (zhat : ι → ℝ × ℝ)
    (lhat : ι → ℝ × ℝ → ℝ) (f : ℝ × ℝ → ℝ) :
    Approximation.nodalInterp (equation_8_34 a₁ a₂ a₃ ∘ zhat) (fun m => lhat m ∘ G) f
        ∘ equation_8_34 a₁ a₂ a₃
      = Approximation.nodalInterp zhat lhat (f ∘ equation_8_34 a₁ a₂ a₃) :=
  Approximation.nodalInterp_comp zhat lhat f hG

/-! ### (8.39): the interpolation error on a triangle -/

/-- **The reference triangle `T̂`** of §8.5.2, with vertices `(0, 0)`, `(1, 0)` and `(0, 1)`, as a
subset of the plane `ℝ × ℝ` on which the affine map (8.34) acts:
`T̂ = {(x̂, ŷ) : x̂ ≥ 0, ŷ ≥ 0, x̂ + ŷ ≤ 1}`. -/
def referenceTriangle : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + x.2 ≤ 1}

section Triangle

variable {a₁ a₂ a₃ : ℝ × ℝ}

local notation "F_T" => equation_8_34 a₁ a₂ a₃

/-- `F_T x̂ - a₁ = x̂ (a₂ - a₁) + ŷ (a₃ - a₁)`: the affine map (8.34) is `a₁` plus a linear map. -/
theorem equation_8_34_sub_vertex (x : ℝ × ℝ) :
    F_T x - a₁ = x.1 • (a₂ - a₁) + x.2 • (a₃ - a₁) := by
  rw [equation_8_34_apply, add_sub_cancel_right]

/-- **The triangle `T = F_T(T̂)` is star-shaped with respect to its vertex `a₁`**: the segment from
`a₁` to `F_T x̂` is `F_T` of the segment from `(0, 0)` to `x̂`, which stays in `T̂`. -/
theorem equation_8_34_segment_mem {x : ℝ × ℝ} (hx : x ∈ referenceTriangle) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : a₁ + s • (F_T x - a₁) ∈ F_T '' referenceTriangle := by
  refine ⟨s • x, ⟨mul_nonneg hs.1 hx.1, mul_nonneg hs.1 hx.2.1, ?_⟩, ?_⟩
  · calc s * x.1 + s * x.2 = s * (x.1 + x.2) := by ring
      _ ≤ 1 * 1 := mul_le_mul hs.2 hx.2.2 (add_nonneg hx.1 hx.2.1) zero_le_one
      _ = 1 := one_mul 1
  · rw [equation_8_34_apply, equation_8_34_sub_vertex]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_add, smul_smul]
    abel

/-- **The distance from the vertex `a₁` to a point of `T`** is at most any `h` bounding the two
edge lengths `‖a₂ - a₁‖`, `‖a₃ - a₁‖` at `a₁`. -/
theorem norm_equation_8_34_sub_vertex_le {h : ℝ} (hh₂ : ‖a₂ - a₁‖ ≤ h) (hh₃ : ‖a₃ - a₁‖ ≤ h)
    {x : ℝ × ℝ} (hx : x ∈ referenceTriangle) : ‖F_T x - a₁‖ ≤ h := by
  rw [equation_8_34_sub_vertex]
  calc ‖x.1 • (a₂ - a₁) + x.2 • (a₃ - a₁)‖ ≤ ‖x.1 • (a₂ - a₁)‖ + ‖x.2 • (a₃ - a₁)‖ :=
        norm_add_le _ _
    _ = x.1 * ‖a₂ - a₁‖ + x.2 * ‖a₃ - a₁‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hx.1, Real.norm_of_nonneg hx.2.1]
    _ ≤ x.1 * h + x.2 * h :=
        add_le_add (mul_le_mul_of_nonneg_left hh₂ hx.1) (mul_le_mul_of_nonneg_left hh₃ hx.2.1)
    _ = (x.1 + x.2) * h := by ring
    _ ≤ 1 * h := mul_le_mul_of_nonneg_right hx.2.2 ((norm_nonneg _).trans hh₂)
    _ = h := one_mul h

/-- **The Taylor polynomial of `f` at the vertex `a₁`, read through `F_T`, lies in `𝒫_k(T̂)`**:
`x̂ ↦ ∑_{j ≤ k} (1/j!) D^j f(a₁)[F_T x̂ - a₁]^j` is the evaluation at `(x̂, ŷ)` of a polynomial in
two variables of total degree at most `k` (`exists_mvPolynomial_taylorSum`, since
`F_T x̂ - a₁ = x̂ (a₂ - a₁) + ŷ (a₃ - a₁)`). -/
theorem exists_mvPolynomial_taylor_equation_8_34 (f : ℝ × ℝ → ℝ) (k : ℕ) :
    ∃ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k ∧ ∀ x : ℝ × ℝ,
      ∑ j ∈ Finset.range (k + 1), ((j ! : ℝ)⁻¹) • iteratedFDeriv ℝ j f a₁ (fun _ => F_T x - a₁)
        = MvPolynomial.eval ![x.1, x.2] q := by
  obtain ⟨q, hqdeg, hq⟩ := exists_mvPolynomial_taylorSum (f := f) a₁ k ![a₂ - a₁, a₃ - a₁]
  refine ⟨q, hqdeg, fun x => ?_⟩
  rw [← hq ![x.1, x.2]]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    equation_8_34_sub_vertex]

/-- **(8.39), the interpolation error on a triangle.** Let `T = F_T(T̂)` be the image of the
reference triangle under the affine map (8.34) with vertices `a₁, a₂, a₃`, let `G` be a left
inverse of `F_T`, and let `l̂_m`, `m ∈ ι`, be the Lagrange basis of `𝒫_k(T̂)` at the local nodes
`ẑ_m ∈ T̂`: `l̂_m(ẑ_j) = δ_{mj}` and every polynomial of total degree `≤ k` is a combination of the
`l̂_m` on `T̂`. Let `Π_T^k f = ∑_m f(F_T ẑ_m) l̂_m ∘ G` be the element interpolant (8.38). If `f` is
`C^{k+1}` at every point of `T` with `‖f^{(k+1)}‖_{∞,T} ≤ M`, and `h_T ≥ ‖a₂ - a₁‖, ‖a₃ - a₁‖`,
then for every `x ∈ T`

  `|f(x) - Π_T^k f(x)| ≤ C h_T^{k+1} ‖f^{(k+1)}‖_{∞,T}`, `C = (∑_m ‖l̂_m‖_{∞,T̂} + 1)/(k+1)!`,

with `C` independent of `h_T` and `f`. The book quotes Ciarlet–Lions Theorem 16.1 (the
Bramble–Hilbert route through `W^{k+1,∞}`); in the sup norm the proof is elementary: with `P` the
Taylor polynomial of `f` of degree `k` at the vertex `a₁`, `f - Π_T^k f = (f - P) - Π_T^k(f - P)`
because `Π_T^k` reproduces `𝒫_k(T)` (`exists_mvPolynomial_taylor_equation_8_34`), and
`|f - P| ≤ M h_T^{k+1}/(k+1)!` on `T` by Taylor's theorem along the segments from `a₁`
(`norm_sub_taylorSum_segment_le`), `T` being star-shaped with respect to `a₁`
(`equation_8_34_segment_mem`). No shape regularity enters. Conventions: `ℝ × ℝ` carries the sup
norm, `‖f^{(k+1)}(x)‖` is the operator norm of the `(k+1)`-linear map `iteratedFDeriv ℝ (k + 1) f x`
for that norm, and `h_T` is any bound on the two edges at `a₁` (the maximum edge length of `T`, in
any norm dominating the sup norm, qualifies). The reference basis is data: its existence for the
principal lattice of Figure 8.8 is the `𝒫_k`-unisolvence of Ciarlet, Theorem 2.2.1, not
formalized. -/
theorem equation_8_39 {ι : Type*} [Fintype ι] {k : ℕ} {G : ℝ × ℝ → ℝ × ℝ}
    (hG : Function.LeftInverse G F_T)
    {zhat : ι → ℝ × ℝ} (hz : ∀ m, zhat m ∈ referenceTriangle) {lhat : ι → ℝ × ℝ → ℝ}
    (hnodal : Approximation.IsNodalBasis zhat lhat)
    (hspan : ∀ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k → ∃ c : ι → ℝ,
      ∀ x ∈ referenceTriangle, MvPolynomial.eval ![x.1, x.2] q = ∑ m, c m * lhat m x)
    {L : ι → ℝ} (hL : ∀ m, ∀ x ∈ referenceTriangle, |lhat m x| ≤ L m)
    {h : ℝ} (hh₂ : ‖a₂ - a₁‖ ≤ h) (hh₃ : ‖a₃ - a₁‖ ≤ h) {f : ℝ × ℝ → ℝ}
    (hf : ∀ x ∈ F_T '' referenceTriangle, ContDiffAt ℝ (k + 1) f x) {M : ℝ}
    (hM : ∀ x ∈ F_T '' referenceTriangle, ‖iteratedFDeriv ℝ (k + 1) f x‖ ≤ M) :
    ∀ x ∈ F_T '' referenceTriangle,
      |f x - Approximation.nodalInterp (F_T ∘ zhat) (fun m => lhat m ∘ G) f x|
        ≤ (∑ m, L m + 1) / (k + 1)! * h ^ (k + 1) * M := by
  rintro _ ⟨x, hx, rfl⟩
  -- the Taylor polynomial of `f` at the vertex `a₁`
  set P : ℝ × ℝ → ℝ := fun y =>
    ∑ j ∈ Finset.range (k + 1), ((j ! : ℝ)⁻¹) • iteratedFDeriv ℝ j f a₁ (fun _ => y - a₁) with hP
  -- (1) Taylor's theorem along the segments from `a₁`
  have htaylor : ∀ y ∈ referenceTriangle,
      |f (F_T y) - P (F_T y)| ≤ M * h ^ (k + 1) / (k + 1)! := by
    intro y hy
    have key := norm_sub_taylorSum_segment_le (f := f) (n := k) (a := a₁) (w := F_T y - a₁)
      (M := M) (fun s hs => hf _ (equation_8_34_segment_mem hy hs))
      (fun s hs => hM _ (equation_8_34_segment_mem hy hs))
    rw [add_sub_cancel, Real.norm_eq_abs] at key
    refine key.trans ?_
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ ⟨y, hy, rfl⟩)
    gcongr
    exact norm_equation_8_34_sub_vertex_le hh₂ hh₃ hy
  -- (2) the interpolant reproduces `P`, a polynomial of degree `≤ k`
  obtain ⟨q, hqdeg, hq⟩ := exists_mvPolynomial_taylor_equation_8_34 (a₂ := a₂) (a₃ := a₃) f k
  have hPF : ∀ y : ℝ × ℝ, P (F_T y) = MvPolynomial.eval ![y.1, y.2] q := hq
  obtain ⟨c, hc⟩ := hspan q hqdeg
  have hcm : ∀ m, c m = P (F_T (zhat m)) := by
    intro m
    rw [hPF, hc _ (hz m), Finset.sum_eq_single m]
    · rw [hnodal.eval_self, mul_one]
    · intro m' _ hm'
      rw [hnodal.eval_of_ne m' m hm', mul_zero]
    · intro hm
      exact absurd (Finset.mem_univ m) hm
  have hrepr : ∑ m, lhat m x * P (F_T (zhat m)) = P (F_T x) := by
    rw [hPF, hc x hx]
    exact Finset.sum_congr rfl fun m _ => by rw [hcm, mul_comm]
  -- (3) assemble
  have hinterp : Approximation.nodalInterp (F_T ∘ zhat) (fun m => lhat m ∘ G) f (F_T x)
      = ∑ m, lhat m x * f (F_T (zhat m)) := by
    simp only [Approximation.nodalInterp_apply, Function.comp, hG x, smul_eq_mul]
  have hsplit : f (F_T x) - ∑ m, lhat m x * f (F_T (zhat m))
      = (f (F_T x) - P (F_T x)) + ∑ m, lhat m x * (P (F_T (zhat m)) - f (F_T (zhat m))) := by
    simp only [mul_sub, Finset.sum_sub_distrib, hrepr]
    ring
  rw [hinterp, hsplit]
  calc |(f (F_T x) - P (F_T x)) + ∑ m, lhat m x * (P (F_T (zhat m)) - f (F_T (zhat m)))|
      ≤ |f (F_T x) - P (F_T x)| + |∑ m, lhat m x * (P (F_T (zhat m)) - f (F_T (zhat m)))| :=
        abs_add_le _ _
    _ ≤ M * h ^ (k + 1) / (k + 1)! + ∑ m, L m * (M * h ^ (k + 1) / (k + 1)!) := by
        gcongr
        · exact htaylor x hx
        · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
          rw [abs_mul, abs_sub_comm]
          exact mul_le_mul (hL m x hx) (htaylor _ (hz m)) (abs_nonneg _)
            ((abs_nonneg _).trans (hL m x hx))
    _ = (∑ m, L m + 1) / (k + 1)! * h ^ (k + 1) * M := by
        rw [← Finset.sum_mul]
        ring

end Triangle

/-! #### The case `k = 1`: the three vertices -/

/-- **The local nodes for `k = 1`** (§8.5.2, Figure 8.8): the three vertices
`(0, 0), (1, 0), (0, 1)` of the reference triangle. -/
def linearNodes : Fin 3 → ℝ × ℝ :=
  ![(0, 0), (1, 0), (0, 1)]

/-- **The reference Lagrange basis of `𝒫_1(T̂)` at the vertices**: the barycentric coordinates
`λ₀ = 1 - x̂ - ŷ`, `λ₁ = x̂`, `λ₂ = ŷ`. -/
def linearShape : Fin 3 → ℝ × ℝ → ℝ :=
  ![fun x => 1 - x.1 - x.2, fun x => x.1, fun x => x.2]

/-- The vertices lie in the reference triangle. -/
theorem linearNodes_mem (m : Fin 3) : linearNodes m ∈ referenceTriangle := by
  fin_cases m <;> simp [linearNodes, referenceTriangle]

/-- The barycentric coordinates are dual to the vertices, `λ_m(ẑ_j) = δ_{mj}`. -/
theorem linearShape_isNodalBasis : Approximation.IsNodalBasis linearNodes linearShape where
  eval_self m := by fin_cases m <;> simp [linearNodes, linearShape]
  eval_of_ne m j hmj := by
    fin_cases m <;> fin_cases j <;> simp_all [linearNodes, linearShape]

/-- The barycentric coordinates are bounded by `1` on the reference triangle. -/
theorem abs_linearShape_le (m : Fin 3) {x : ℝ × ℝ} (hx : x ∈ referenceTriangle) :
    |linearShape m x| ≤ 1 := by
  obtain ⟨h1, h2, h3⟩ := hx
  rw [abs_le]
  fin_cases m <;> simp [linearShape] <;> constructor <;> linarith

/-- **The barycentric coordinates span `𝒫_1(T̂)`**: a polynomial of total degree at most `1` is
`q(0,0) λ₀ + q(1,0) λ₁ + q(0,1) λ₂`, monomial by monomial. -/
theorem linearShape_span (q : MvPolynomial (Fin 2) ℝ) (hq : q.totalDegree ≤ 1) :
    ∃ c : Fin 3 → ℝ, ∀ x ∈ referenceTriangle,
      MvPolynomial.eval ![x.1, x.2] q = ∑ m, c m * linearShape m x := by
  refine ⟨fun m => MvPolynomial.eval ![(linearNodes m).1, (linearNodes m).2] q, fun x _ => ?_⟩
  -- monomial by monomial
  have hmono : ∀ v ∈ q.support, ∏ i, ![x.1, x.2] i ^ v i
      = ∑ m, (∏ i, ![(linearNodes m).1, (linearNodes m).2] i ^ v i) * linearShape m x := by
    intro v hv
    have hdeg : v 0 + v 1 ≤ 1 := by
      have := MvPolynomial.le_totalDegree hv
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at this
      exact this.trans hq
    simp only [Fin.prod_univ_two, Fin.sum_univ_three, linearNodes, linearShape,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_fin_one]
    rcases Nat.eq_zero_or_pos (v 0) with h0 | h0 <;> rcases Nat.eq_zero_or_pos (v 1) with h1 | h1
    · rw [h0, h1]; ring
    · obtain h1' : v 1 = 1 := by omega
      rw [h0, h1']; ring
    · obtain h0' : v 0 = 1 := by omega
      rw [h0', h1]; ring
    · omega
  simp only [MvPolynomial.eval_eq', Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [hmono v hv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

section Triangle

variable {a₁ a₂ a₃ : ℝ × ℝ}

local notation "F_T" => equation_8_34 a₁ a₂ a₃

/-- **(8.39) for `k = 1`**, with the three local nodes at the vertices of `T` and the constant
made explicit: `‖f - Π_T^1 f‖_{∞,T} ≤ 2 h_T² ‖f''‖_{∞,T}`. `equation_8_39` with the barycentric
coordinates as the reference basis, `‖λ_m‖_{∞,T̂} = 1`, so `C = (3 + 1)/2! = 2`. -/
theorem equation_8_39_linear {G : ℝ × ℝ → ℝ × ℝ} (hG : Function.LeftInverse G F_T)
    {h : ℝ} (hh₂ : ‖a₂ - a₁‖ ≤ h) (hh₃ : ‖a₃ - a₁‖ ≤ h) {f : ℝ × ℝ → ℝ}
    (hf : ∀ x ∈ F_T '' referenceTriangle, ContDiffAt ℝ 2 f x) {M : ℝ}
    (hM : ∀ x ∈ F_T '' referenceTriangle, ‖iteratedFDeriv ℝ 2 f x‖ ≤ M) :
    ∀ x ∈ F_T '' referenceTriangle,
      |f x - Approximation.nodalInterp (F_T ∘ linearNodes) (fun m => linearShape m ∘ G) f x|
        ≤ 2 * h ^ 2 * M := by
  intro x hx
  refine (equation_8_39 (k := 1) hG linearNodes_mem linearShape_isNodalBasis linearShape_span
    (L := fun _ => 1) (fun m x hx => abs_linearShape_le m hx) hh₂ hh₃ hf hM x hx).trans_eq ?_
  simp only [Fin.sum_univ_three, Nat.factorial]
  norm_num

end Triangle

end QuarteroniSaccoSaleri.Chapter08
