import Numlib.Analysis.HarmonicPolynomial
import NumlibSurface.AtkinsonHan.Chapter14.Section02

/-!
# Atkinson–Han §14.4: a Galerkin method for an elliptic equation on the disk

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §14.4.

The section poses `−Δu = f` on `𝔹₂` with `u = 0` on the boundary, takes its weak formulation in
`H¹₀(𝔹₂)`, and runs the Galerkin method on the trial space `X_n = (1 − |x|²) Π_n^2`, whose elements
vanish on the unit circle. What is formalized here is (14.4.8) and Lemma 14.4.1, which mention no
Sobolev space: the Laplacian is a linear bijection of `X_n` onto `Π_n^d`, which is what makes the
Galerkin equations uniquely solvable. The book leaves its proof as a problem.

Well-definedness is a degree count — `(1 − |x|²) p` has degree at most `n + 2` and the Laplacian
drops two — and the two spaces have equal dimension, because multiplication by the nonzero
polynomial `1 − |x|²` is injective. So bijectivity follows from injectivity, which is the backbone's
`MvPolynomial.eq_zero_of_laplacian_one_sub_sumSq_mul_eq_zero`.

## Main results

* `trialSpace` — (14.4.8), the trial space `X_n = (1 − |x|²) Π_n^d`.
* `finrank_trialSpace` — `dim X_n = dim Π_n^d = C(n + d, d)`, which for `d = 2` is
  `(n + 1)(n + 2)/2`.
* `laplacianOn` and `lemma_14_4_1` — Lemma 14.4.1: `Δ : X_n → Π_n^d` is a linear bijection.
* `span_ridgePoly_polySpace` and `example_14_4_2` — (14.4.14): the ridge polynomials `φ_{m,k}` of
  Example 14.2.2 span `Π_n^2`, and multiplying them by `1 − x² − y²` spans the trial space `X_n`,
  which is the basis Example 14.4.2 computes in.

## Not formalized here

* **(14.4.1)–(14.4.7)**, the boundary value problem, its weak formulation, and the boundedness and
  coercivity of the bilinear form; **(14.4.10)–(14.4.11)**, the Galerkin method on `X_n` and its
  Céa estimate; **(14.4.12)–(14.4.13)**, the Green's function of the disk and the resulting
  regularity bound; and **Exercises 14.4.2–14.4.3**, transplanting the problem from an ellipse or a
  smooth simply connected region. All of them quantify over `H¹₀(𝔹₂)`, and Mathlib has no weak
  derivative on an open set, so the space itself does not exist. The abstract halves of the
  argument are formalized elsewhere in this surface: Lax–Milgram is
  `AtkinsonHan.Chapter08.Section03` and Céa's inequality is `AtkinsonHan.Chapter09.Section01`.
* **Example 14.4.2**'s numerical half: the transplantation of `−Δu + e^{s−t} u = g` from the region
  `D` to the disk by `s = x − y + a x²`, `t = x + y`, with the coefficients `A`, `γ`, `f` it
  produces, the test solution (14.4.18), and the error read off Figure 14.3.  The transplantation
  is a change of variables in the *weak* formulation, so it quantifies over `H¹₀` like the rest of
  §14.4; the errors are read off a figure.  What is stated is the example's choice of basis,
  (14.4.14), which needs no Sobolev space: `example_14_4_2`.
-/

open Module MvPolynomial

namespace AtkinsonHan.Chapter14

variable {d : ℕ}

/-- The polynomial `1 − |x|²`, which vanishes exactly on the unit sphere. -/
noncomputable abbrev oneSubSumSq (d : ℕ) : MvPolynomial (Fin d) ℝ := 1 - sumSq (Fin d) ℝ

theorem oneSubSumSq_ne_zero : oneSubSumSq d ≠ 0 := fun hz => by
  have := congrArg (eval (fun _ => (0 : ℝ))) hz
  simp [oneSubSumSq, sumSq] at this

/-- **(14.4.8)**: the trial space `X_n = {(1 − x₁² − ⋯ − x_d²) p : p ∈ Π_n^d}` of the Galerkin
method, a subspace of `H¹₀(𝔹_d)` because its elements vanish on the unit sphere. -/
noncomputable def trialSpace (d n : ℕ) : Submodule ℝ (MvPolynomial (Fin d) ℝ) :=
  (polySpace d n).map (LinearMap.mulLeft ℝ (oneSubSumSq d))

theorem mem_trialSpace_iff {n : ℕ} {q : MvPolynomial (Fin d) ℝ} :
    q ∈ trialSpace d n ↔ ∃ p, p.totalDegree ≤ n ∧ oneSubSumSq d * p = q := by
  simp only [trialSpace, Submodule.mem_map, mem_polySpace_iff, LinearMap.mulLeft_apply]

theorem mulLeft_oneSubSumSq_injective :
    Function.Injective (LinearMap.mulLeft ℝ (oneSubSumSq d)) :=
  mul_right_injective₀ oneSubSumSq_ne_zero

instance finiteDimensional_trialSpace (n : ℕ) : FiniteDimensional ℝ (trialSpace d n) := by
  have : Module.Finite ℝ (polySpace d n) := inferInstance
  exact Module.Finite.map (polySpace d n) (LinearMap.mulLeft ℝ (oneSubSumSq d))

/-- `dim X_n = dim Π_n^d = C(n + d, d)`: multiplication by `1 − |x|²` is injective, so it carries
`Π_n^d` isomorphically onto `X_n`. For `d = 2` this is `(n + 1)(n + 2)/2`, the count of §14.1. -/
theorem finrank_trialSpace (n : ℕ) :
    finrank ℝ (trialSpace d n) = (n + d).choose d := by
  rw [← finrank_polySpace d n]
  exact (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective _ mulLeft_oneSubSumSq_injective _)).symm

theorem totalDegree_le_of_mem_trialSpace {n : ℕ} {q : MvPolynomial (Fin d) ℝ}
    (hq : q ∈ trialSpace d n) : q.totalDegree ≤ n + 2 := by
  obtain ⟨p, hp, rfl⟩ := mem_trialSpace_iff.1 hq
  refine (totalDegree_mul _ _).trans ?_
  have h1 : (oneSubSumSq d).totalDegree ≤ 2 :=
    (totalDegree_sub _ _).trans (by simp [totalDegree_sumSq_le])
  omega

/-- The Laplacian maps `X_n` into `Π_n^d`: an element of `X_n` has degree at most `n + 2`, and the
Laplacian drops the degree by two. -/
theorem laplacian_mem_polySpace {n : ℕ} {q : MvPolynomial (Fin d) ℝ} (hq : q ∈ trialSpace d n) :
    laplacian q ∈ polySpace d n := by
  have h1 := totalDegree_laplacian_le q
  have h2 := totalDegree_le_of_mem_trialSpace hq
  exact mem_polySpace_iff.2 (by omega)

/-- **Lemma 14.4.1**: the Laplacian as a linear map from the trial space `X_n` to `Π_n^d`. -/
noncomputable def laplacianOn (d n : ℕ) : trialSpace d n →ₗ[ℝ] polySpace d n :=
  laplacian.restrict fun _ hq => laplacian_mem_polySpace hq

@[simp]
theorem laplacianOn_coe {n : ℕ} (q : trialSpace d n) :
    (laplacianOn d n q : MvPolynomial (Fin d) ℝ) = laplacian (q : MvPolynomial (Fin d) ℝ) := rfl

/-- **Lemma 14.4.1**, injectivity: a harmonic element of `X_n` is zero. Writing it as
`(1 − |x|²) p`, the backbone's `MvPolynomial.eq_zero_of_laplacian_one_sub_sumSq_mul_eq_zero` gives
`p = 0`. Analytically this is the uniqueness statement for the Dirichlet problem — a harmonic
function on the ball vanishing on the sphere vanishes — but no analysis is used. -/
theorem lemma_14_4_1_injective (hd : 0 < d) (n : ℕ) : Function.Injective (laplacianOn d n) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨q, hq⟩ hker
  obtain ⟨p, hp, rfl⟩ := mem_trialSpace_iff.1 hq
  have hlap : laplacian (oneSubSumSq d * p) = 0 :=
    congrArg Subtype.val (LinearMap.mem_ker.1 hker)
  have hp0 : p = 0 := MvPolynomial.eq_zero_of_laplacian_one_sub_sumSq_mul_eq_zero
    (Fin.pos_iff_nonempty.1 hd) hp hlap
  exact Subtype.ext (by simp [hp0])

/-- **Lemma 14.4.1**: the Laplacian is a linear bijection of `X_n = (1 − |x|²) Π_n^d` onto `Π_n^d`.
Surjectivity needs no separate argument: the two spaces have the same dimension, so an injective
linear map between them is onto. This is what makes the Galerkin equations of §14.4 uniquely
solvable. -/
theorem lemma_14_4_1 (hd : 0 < d) (n : ℕ) : Function.Bijective (laplacianOn d n) := by
  refine ⟨lemma_14_4_1_injective hd n, ?_⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1
    (lemma_14_4_1_injective hd n)
  rw [finrank_trialSpace n, finrank_polySpace]


/-! ### Example 14.4.2: the basis (14.4.14) of the trial space -/

section Basis

open Approximation

open scoped Real

/-- The ridge polynomials of Example 14.2.2 span `Π_n^2` as *polynomials*, and not only as classes
in `L²(𝔹₂)`.  This is `AtkinsonHan.Chapter14.example_14_2_2_polyLE` carried back along
`IsMvWeight.toL2`, which is injective on polynomials because no nonzero polynomial vanishes almost
everywhere on the disk. -/
theorem span_ridgePoly_polySpace (n : ℕ) :
    Submodule.span ℝ {p : MvPolynomial (Fin 2) ℝ |
        ∃ m ≤ n, ∃ k ≤ m, p = ridgePoly m (k * (π / (m + 1)))} = polySpace 2 n := by
  refine Submodule.map_injective_of_injective
    (f := (isMvWeight_ballVolume 2).toL2) (IsMvWeight.toL2_injective _) ?_
  rw [Submodule.map_span]
  have himg : (isMvWeight_ballVolume 2).toL2 ''
      {p : MvPolynomial (Fin 2) ℝ | ∃ m ≤ n, ∃ k ≤ m, p = ridgePoly m (k * (π / (m + 1)))}
      = {f | ∃ m ≤ n, ∃ k ≤ m, f = ridgeL2 m k} := by
    ext f
    constructor
    · rintro ⟨p, ⟨m, hm, k, hk, rfl⟩, rfl⟩
      exact ⟨m, hm, k, hk, rfl⟩
    · rintro ⟨m, hm, k, hk, rfl⟩
      exact ⟨ridgePoly m (k * (π / (m + 1))), ⟨m, hm, k, hk, rfl⟩, rfl⟩
  rw [himg, example_14_2_2_polyLE n]
  rfl

/-- **(14.4.14), the basis of the trial space used in Example 14.4.2.**  With the orthonormal ridge
polynomials `φ_{m,k}` of (14.2.5) as a basis of `Π_n^2`, the functions

`ψ_{m,k}(x, y) = (1 − x² − y²) φ_{m,k}(x, y)`,  `0 ≤ k ≤ m ≤ n`,

span the trial space `X_n` of (14.4.8).  There are `dim Π_n^2 = (n + 1)(n + 2)/2` of them and
`dim X_n` is the same (`finrank_trialSpace`), so they are a basis of `X_n` — which is what makes
the Galerkin equations of §14.4 a square system, uniquely solvable by Lemma 14.4.1.

Everything else in Example 14.4.2 is the numerical run; see the module doc. -/
theorem example_14_4_2 (n : ℕ) :
    Submodule.span ℝ {q : MvPolynomial (Fin 2) ℝ |
        ∃ m ≤ n, ∃ k ≤ m, q = oneSubSumSq 2 * ridgePoly m (k * (π / (m + 1)))}
      = trialSpace 2 n := by
  rw [trialSpace, ← span_ridgePoly_polySpace n, Submodule.map_span]
  congr 1
  ext q
  constructor
  · rintro ⟨m, hm, k, hk, rfl⟩
    exact ⟨_, ⟨m, hm, k, hk, rfl⟩, rfl⟩
  · rintro ⟨p, ⟨m, hm, k, hk, rfl⟩, rfl⟩
    exact ⟨m, hm, k, hk, rfl⟩

end Basis

end AtkinsonHan.Chapter14
