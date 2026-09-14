import Numlib.Approximation.BSpline
import Numlib.Approximation.Bezier
import Numlib.Approximation.Spline
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section06

/-!
# Quarteroni–Sacco–Saleri §8.7: splines in parametric form

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §8.7: the parametric cubic spline of a sequence of points of the
plane, the cumulative-length parametrization and its geometric invariance (quoted from Späth);
§8.7.1: the Bernstein polynomials with their recursion and basis property, the Bézier curve
(8.58), de Casteljau's construction, the reversal property, and the two properties of parametric
B-spline curves — locality of a control point and containment in the convex hull of the control
polygon. Programs 68–70 are code and contribute no nodes.

The backbone is `Numlib/Approximation/Spline` (`Spline.cubicInterpVec`, the interpolatory cubic
spline of vector-valued data, and its affine equivariance `Spline.cubicInterpVec_affine`),
`Numlib/Approximation/Bezier` (`Bezier.curve`, `Bezier.casteljau`, the Bernstein lemmas) and
`Numlib/Approximation/BSpline` (`BSpline.curve`).

## Main definitions

* `parametricCubicSpline t n P` — the parametric spline `S₃(t) = (s_{3,x}(t), s_{3,y}(t))` of the
  points `P₀, …, P_n` of the plane, each coordinate the natural cubic spline of §8.6.1
  (`parametricCubicSpline_apply`).
* `cumulativeLength P` — the cumulative-length parametrization `t_i = ∑_{k ≤ i} l_k`,
  `l_k = |P_{k-1} P_k|`.
* `equation_8_58 P` — the Bézier curve `B_n(P₀, …, P_n; t)`.
* `parametricBSpline x k P N` — the parametric B-spline curve.

## Main results

* `cumulativeLengthSpline_invariant` — the cumulative-length spline is geometrically invariant:
  it commutes with the isometries of the plane.
* `bernsteinRecursion_zero`, `bernsteinRecursion`, `bernstein_mem_polyLE`, `bernsteinBasis` — the
  recursion and the basis property of the Bernstein polynomials.
* `equation_8_58_mem_convexHull`, `deCasteljau`, `deCasteljau_succ`, `bezier_reverse`,
  `bezier_reverse_image`, `bezier_endpoints` — Bézier curves.
* `parametricBSpline_local`, `parametricBSpline_mem_convexHull` — properties 1 and 2 of parametric
  B-splines.

## Conventions

Points of the plane are `EuclideanSpace ℝ (Fin 2)`, so that the length of a segment is the
Euclidean distance `dist`; the parametric spline is taken with the natural end conditions, which
the book does not fix, and its parameter partition is `0 = t₀ < t₁ < ⋯ < t_n = T`
(`Spline.IsPartition 0 T n t`). Bézier and B-spline curves take control points in an arbitrary
real vector space `E`, as the backbone does; the book's plane is the case
`E = EuclideanSpace ℝ (Fin 2)`. The Bernstein polynomial `b_{n,k}` is Mathlib's
`bernsteinPolynomial ℝ n k`, and `𝒫_n` on `[0, 1]` is `polyLE (Icc 0 1) n`.
-/

open Polynomial Set

namespace QuarteroniSaccoSaleri.Chapter08

/-! ### Parametric cubic splines and the cumulative-length parametrization -/

/-- **The parametric cubic spline** (§8.7) of the points `P_i = (x_i, y_i)`, `i = 0, …, n`, of the
plane and of a partition `0 = t₀ < t₁ < ⋯ < t_n = T` of `[0, T]`:
`S₃(t) = (s_{3,x}(t), s_{3,y}(t))`, where `s_{3,x}` and `s_{3,y}` are the cubic splines
interpolating the data `{t_i, x_i}` and `{t_i, y_i}` — here with the natural end conditions
(8.45), which the book does not fix. It is the backbone's vector-valued natural spline
`Spline.cubicInterpVec n t P 0 0 0 0`, whose coordinates are the natural splines of the
coordinates (`parametricCubicSpline_apply`). -/
noncomputable def parametricCubicSpline (t : ℕ → ℝ) (n : ℕ) (P : ℕ → EuclideanSpace ℝ (Fin 2)) :
    ℝ → EuclideanSpace ℝ (Fin 2) :=
  Spline.cubicInterpVec n t P 0 0 0 0

/-- **The coordinates of the parametric spline are the natural cubic splines of the coordinates**:
`S₃(τ)_j = s_{3,j}(τ)`, with `s_{3,j}` the natural cubic spline interpolating `{t_i, (P_i)_j}`
(`Spline.naturalInterp`). -/
theorem parametricCubicSpline_apply (t : ℕ → ℝ) (n : ℕ) (P : ℕ → EuclideanSpace ℝ (Fin 2))
    (τ : ℝ) (j : Fin 2) :
    parametricCubicSpline t n P τ j = Spline.naturalInterp n t (fun i => P i j) τ := by
  have := Spline.cubicInterpVec_affine n t P 0 0 0 0 (EuclideanSpace.projₗ j) 0 τ
  simp only [add_zero, map_zero, EuclideanSpace.projₗ, PiLp.projₗ_apply] at this
  rw [parametricCubicSpline, Spline.naturalInterp, ← Spline.cubicInterpVec_real, ← this]

/-- **The parametric spline passes through the points**: `S₃(t_i) = P_i` for `i = 0, …, n`. -/
theorem parametricCubicSpline_apply_node {T : ℝ} {t : ℕ → ℝ} {n : ℕ}
    (ht : Spline.IsPartition 0 T n t) (hn : 1 ≤ n) (P : ℕ → EuclideanSpace ℝ (Fin 2)) {i : ℕ}
    (hi : i ≤ n) :
    parametricCubicSpline t n P (t i) = P i := by
  ext j
  rw [parametricCubicSpline_apply, Spline.naturalInterp, Spline.cubicInterp_apply_node ht hn hi]

/-- **The cumulative-length parametrization** (§8.7): with `l_i = |P_{i-1} P_i|` the length of the
segment from `P_{i-1}` to `P_i`, `t₀ = 0` and `t_i = ∑_{k=1}^{i} l_k` for `i ≥ 1`, "the cumulative
length of the piecewise line that joins the points from `P₀` to `P_i`". -/
noncomputable def cumulativeLength (P : ℕ → EuclideanSpace ℝ (Fin 2)) (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range i, dist (P k) (P (k + 1))

/-- `t₀ = 0`. -/
@[simp]
theorem cumulativeLength_zero (P : ℕ → EuclideanSpace ℝ (Fin 2)) : cumulativeLength P 0 = 0 := by
  simp [cumulativeLength]

/-- `t_i = t_{i-1} + l_i` with `l_i = √((x_i - x_{i-1})² + (y_i - y_{i-1})²)`, the length of the
segment `P_{i-1} P_i`. -/
theorem cumulativeLength_succ (P : ℕ → EuclideanSpace ℝ (Fin 2)) (i : ℕ) :
    cumulativeLength P (i + 1)
      = cumulativeLength P i + √((P (i + 1) 0 - P i 0) ^ 2 + (P (i + 1) 1 - P i 1) ^ 2) := by
  rw [cumulativeLength, Finset.sum_range_succ, dist_comm, EuclideanSpace.dist_eq, Fin.sum_univ_two,
    Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
  rfl

/-- **The cumulative lengths form a partition** `0 = t₀ < t₁ < ⋯ < t_n = T` of `[0, T]`,
`T = t_n`, as soon as consecutive points are distinct (so that every `l_i > 0`). -/
theorem isPartition_cumulativeLength {n : ℕ} {P : ℕ → EuclideanSpace ℝ (Fin 2)}
    (hP : ∀ k < n, P k ≠ P (k + 1)) :
    Spline.IsPartition 0 (cumulativeLength P n) n (cumulativeLength P) where
  step k hk := by
    rw [cumulativeLength, cumulativeLength, Finset.sum_range_succ]
    exact lt_add_of_pos_right _ (dist_pos.mpr (hP k hk))
  first := cumulativeLength_zero P
  last := rfl

/-- **The cumulative lengths are invariant under the isometries of the plane**: for an isometry
`Q` (an affine isometric equivalence of `EuclideanSpace ℝ (Fin 2)`), the cumulative lengths of the
points `Q(P_i)` are those of the `P_i`. -/
theorem cumulativeLength_comp (Q : EuclideanSpace ℝ (Fin 2) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin 2))
    (P : ℕ → EuclideanSpace ℝ (Fin 2)) : cumulativeLength (Q ∘ P) = cumulativeLength P := by
  funext i
  simp only [cumulativeLength, Function.comp_apply, AffineIsometryEquiv.dist_map]

/-- **Geometric invariance of the cumulative-length spline** (§8.7, quoted from Späth): for an
isometry `Q` of the plane, the cumulative-length parametric spline of the points `Q(P_i)` is `Q`
of the cumulative-length parametric spline of the `P_i`, at every parameter value. The cumulative
lengths are preserved (`cumulativeLength_comp`), and the natural cubic spline commutes with affine
maps of the data (`Spline.cubicInterpVec_affine`, the affine map being `Q = Q.linear + Q(0)`). -/
theorem cumulativeLengthSpline_invariant
    (Q : EuclideanSpace ℝ (Fin 2) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin 2)) (n : ℕ)
    (P : ℕ → EuclideanSpace ℝ (Fin 2)) :
    parametricCubicSpline (cumulativeLength (Q ∘ P)) n (Q ∘ P)
      = Q ∘ parametricCubicSpline (cumulativeLength P) n P := by
  have hQ : ∀ v, Q v = Q.linearIsometryEquiv v + Q 0 := fun v => by
    simpa [vadd_eq_add] using Q.map_vadd 0 v
  funext τ
  rw [cumulativeLength_comp, Function.comp_apply, parametricCubicSpline, parametricCubicSpline]
  have := Spline.cubicInterpVec_affine n (cumulativeLength P) P 0 0 0 0
    (Q.linearIsometryEquiv.toLinearEquiv : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (Q 0) τ
  simp only [map_zero, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv] at this
  rw [hQ (Spline.cubicInterpVec n (cumulativeLength P) P 0 0 0 0 τ), ← this]
  congr 1
  funext i
  rw [Function.comp_apply, hQ (P i)]

/-! ### §8.7.1: Bernstein polynomials and Bézier curves -/

/-- **The Bernstein polynomials** over `[0, 1]` (§8.7.1):
`b_{n,k}(t) = (n choose k) t^k (1 - t)^{n-k}` for `n = 0, 1, …` and `k = 0, …, n` — Mathlib's
`bernsteinPolynomial ℝ n k`, evaluated. -/
theorem bernsteinPolynomial_eval (n k : ℕ) (t : ℝ) :
    (bernsteinPolynomial ℝ n k).eval t = n.choose k * t ^ k * (1 - t) ^ (n - k) := by
  simp [bernsteinPolynomial]

/-- **The Bernstein recursion, first line**: `b_{n,0}(t) = (1 - t)^n`. -/
theorem bernsteinRecursion_zero (n : ℕ) (t : ℝ) :
    (bernsteinPolynomial ℝ n 0).eval t = (1 - t) ^ n := by
  simp [bernsteinPolynomial]

/-- **The Bernstein recursion, second line** (§8.7.1):
`b_{n,k}(t) = (1 - t) b_{n-1,k}(t) + t b_{n-1,k-1}(t)` for `k = 1, …, n` — written for `n + 1` and
`k + 1`; it holds for every `k` (both sides vanish when `k + 1 > n + 1`).
`bernsteinPolynomial.succ_succ`. -/
theorem bernsteinRecursion (n k : ℕ) (t : ℝ) :
    (bernsteinPolynomial ℝ (n + 1) (k + 1)).eval t
      = (1 - t) * (bernsteinPolynomial ℝ n (k + 1)).eval t
        + t * (bernsteinPolynomial ℝ n k).eval t := by
  rw [bernsteinPolynomial.succ_succ]
  simp

/-- "It is easily seen that `b_{n,k} ∈ 𝒫_n` for `k = 0, …, n`": as a function on `[0, 1]`, the
Bernstein polynomial is a polynomial of degree at most `n`. `bernsteinPolynomial.degree_le`. -/
theorem bernstein_mem_polyLE (n k : ℕ) :
    (bernsteinPolynomial ℝ n k).toContinuousMapOn (Icc 0 1) ∈ polyLE (Icc (0 : ℝ) 1) n :=
  mem_polyLE_iff.mpr ⟨bernsteinPolynomial ℝ n k, bernsteinPolynomial.degree_le ℝ n k, fun _ => rfl⟩

/-- **The Bernstein basis** (§8.7.1): "`{b_{n,k}, k = 0, …, n}` provides a basis for `𝒫_n`" — a
basis of the polynomials of degree at most `n` on `[0, 1]` whose `k`-th vector is
`t ↦ b_{n,k}(t)`. `bernsteinPolynomial.exists_basis_polyLE`. -/
theorem bernsteinBasis (n : ℕ) :
    ∃ B : Module.Basis (Fin (n + 1)) ℝ (polyLE (Icc (0 : ℝ) 1) n),
      ∀ (k : Fin (n + 1)) (t : Icc (0 : ℝ) 1),
        (B k : C(Icc (0 : ℝ) 1, ℝ)) t = (bernsteinPolynomial ℝ n k).eval (t : ℝ) :=
  bernsteinPolynomial.exists_basis_polyLE (Icc_infinite (by norm_num)) n

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}

/-- **(8.58), the Bézier curve** of the `n + 1` ordered points `P₀, P₁, …, P_n` (the vertices of
the characteristic, or Bézier, polygon):

`B_n(P₀, P₁, …, P_n; t) = ∑_{k=0}^{n} P_k b_{n,k}(t)`, `0 ≤ t ≤ 1`.

The backbone's `Bezier.curve P t`, in an arbitrary real vector space. -/
noncomputable def equation_8_58 (P : Fin (n + 1) → E) (t : ℝ) : E :=
  Bezier.curve P t

/-- **(8.58) unfolded.** -/
theorem equation_8_58_apply (P : Fin (n + 1) → E) (t : ℝ) :
    equation_8_58 P t = ∑ k : Fin (n + 1), (bernsteinPolynomial ℝ n k).eval t • P k :=
  rfl

/-- **The Bézier curve is a weighted average of the points `P_k`** with the weights `b_{n,k}(t)`,
hence lies in their convex hull for `0 ≤ t ≤ 1`. `Bezier.curve_mem_convexHull`. -/
theorem equation_8_58_mem_convexHull (P : Fin (n + 1) → E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    equation_8_58 P t ∈ convexHull ℝ (range P) :=
  Bezier.curve_mem_convexHull P ht

/-- **De Casteljau's construction, one step** (§8.7.1): for fixed `t ∈ [0, 1]`, the new vertices
`P_{i,1}(t) = (1 - t) P_i + t P_{i+1}`, `i = 0, …, n - 1`, of the polygon of `n - 1` edges obtained
from `P₀, …, P_n` — the backbone's `Bezier.casteljauStep`. -/
theorem deCasteljau_step (t : ℝ) (P : Fin (n + 2) → E) (i : Fin (n + 1)) :
    Bezier.casteljauStep t P i = (1 - t) • P i.castSucc + t • P i.succ :=
  rfl

/-- **De Casteljau's construction** (§8.7.1): repeating the step until the polygon comprises a
single vertex `P_{0,n}(t)` gives the value of the Bézier curve, `P_{0,n}(t) = B_n(P₀, …, P_n; t)`.
`Bezier.casteljau_eq_curve`. -/
theorem deCasteljau (t : ℝ) (P : Fin (n + 1) → E) : Bezier.casteljau t P = equation_8_58 P t :=
  Bezier.casteljau_eq_curve P t

/-- **The last step of de Casteljau's construction**:
`P_{0,n}(t) = (1 - t) P_{0,n-1}(t) + t P_{1,n-1}(t)`, where `P_{0,n-1}(t)` and `P_{1,n-1}(t)` are
the Bézier curves of the polygons `P₀, …, P_{n-1}` and `P₁, …, P_n`. `Bezier.curve_succ`. -/
theorem deCasteljau_succ (P : Fin (n + 2) → E) (t : ℝ) :
    equation_8_58 P t = (1 - t) • equation_8_58 (Fin.init P) t + t • equation_8_58 (Fin.tail P) t :=
  Bezier.curve_succ P t

/-- **Reversal** (§8.7.1): "the Bézier curve `B_n(P₀, P₁, …, P_n; t)` coincides with
`B_n(P_n, P_{n-1}, …, P₀; t)`, apart from the orientation": the curve of the reversed polygon at
`t` is the curve of the original polygon at `1 - t`. `Bezier.curve_rev`. -/
theorem bezier_reverse (P : Fin (n + 1) → E) (t : ℝ) :
    equation_8_58 (P ∘ Fin.rev) t = equation_8_58 P (1 - t) :=
  Bezier.curve_rev P t

/-- **Reversal, the traces**: the Bézier curves of the polygon and of the reversed polygon have the
same image on `[0, 1]`. -/
theorem bezier_reverse_image (P : Fin (n + 1) → E) :
    equation_8_58 (P ∘ Fin.rev) '' Icc (0 : ℝ) 1 = equation_8_58 P '' Icc (0 : ℝ) 1 := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, (bezier_reverse P t).symm⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    rw [bezier_reverse, sub_sub_cancel]

/-- **The endpoints of the Bézier curve**: `B_n(P; 0) = P₀` and `B_n(P; 1) = P_n`.
`Bezier.curve_zero`, `Bezier.curve_one`. -/
theorem bezier_endpoints (P : Fin (n + 1) → E) :
    equation_8_58 P 0 = P 0 ∧ equation_8_58 P 1 = P (Fin.last n) :=
  ⟨Bezier.curve_zero P, Bezier.curve_one P⟩

/-! ### Parametric B-splines -/

/-- **The parametric B-spline** (§8.7.1): the B-splines `B_{i,k+1}` on a nondecreasing knot
sequence "are used in (8.58) instead of the Bernstein polynomials" — for control points
`P₀, …, P_{N-1}`, the curve `t ↦ ∑_{i<N} B_{i,k+1}(t) P_i`, the backbone's `BSpline.curve`. -/
noncomputable def parametricBSpline (x : ℕ → ℝ) (k : ℕ) (P : ℕ → E) (N : ℕ) (t : ℝ) : E :=
  BSpline.curve x k P N t

/-- The parametric B-spline unfolded. -/
theorem parametricBSpline_apply (x : ℕ → ℝ) (k : ℕ) (P : ℕ → E) (N : ℕ) (t : ℝ) :
    parametricBSpline x k P N t = ∑ i ∈ Finset.range N, BSpline.bspline x k i t • P i :=
  rfl

/-- **§8.7.1, property 1**: "perturbing a single vertex of the characteristic polygon yields a
local perturbation of the curve only around the vertex itself" — replacing `P_j` by `Q` changes the
curve only for `t ∈ [x_j, x_{j+k+1})`, the support of `B_{j,k+1}`.
`BSpline.curve_update_eq_of_notMem`. -/
theorem parametricBSpline_local {x : ℕ → ℝ} (hx : Monotone x) (k : ℕ) (P : ℕ → E) (j : ℕ) (Q : E)
    (N : ℕ) {t : ℝ} (ht : t ∉ Ico (x j) (x (j + k + 1))) :
    parametricBSpline x k (Function.update P j Q) N t = parametricBSpline x k P N t :=
  BSpline.curve_update_eq_of_notMem hx P j Q ht

/-- **§8.7.1, property 2**: the parametric B-spline "is always contained within the convex hull of
the polygon": on the parameter range `[x_k, x_N)` of a curve with `N ≥ 1` control points, the curve
lies in the convex hull of `P₀, …, P_{N-1}`, its coefficients being nonnegative and summing to one.
(The first half of the book's sentence, that the parametric B-spline "better approximates the
control polygon than the corresponding Bézier curve does", is not a mathematical statement.)
`BSpline.curve_mem_convexHull`. -/
theorem parametricBSpline_mem_convexHull {x : ℕ → ℝ} (hx : Monotone x) (k : ℕ) (P : ℕ → E) {N : ℕ}
    (hN : 1 ≤ N) {t : ℝ} (ht : t ∈ Ico (x k) (x N)) :
    parametricBSpline x k P N t ∈ convexHull ℝ (P '' Iio N) :=
  BSpline.curve_mem_convexHull hx P hN ht

end QuarteroniSaccoSaleri.Chapter08
