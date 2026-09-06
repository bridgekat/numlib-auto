import Numlib.Approximation.Hyperinterpolation
import NumlibSurface.AtkinsonHan.Chapter14.Section02

/-!
# Atkinson–Han §14.3: hyperinterpolation

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §14.3.

Hyperinterpolation is the orthogonal projection `P_n` of §14.2 with its integrals replaced by a
quadrature rule. The book builds one particular rule on the disk — Gauss–Legendre in the radius,
the trapezoidal rule in the angle — but (14.3.3), (14.3.4) and (14.3.5) use nothing about it beyond
its exactness on `Π_{2n}^d`, which is what `Approximation.IsExactOn` names. The section is therefore
stated over an arbitrary exact rule, as Sloan's construction is; the general statements are in the
backbone `Numlib.Approximation.Hyperinterpolation` and this module is their specialization to the
book's spaces.

The family `{φ_{m,ℓ} : m ≤ n}` the book expands along appears here as a single `L²(μ)`-orthonormal
family `φ` spanning `Π_n^d`, which by Lemma 14.2.1 is what an orthonormal basis of each `V_m^d` with
`m ≤ n` assembles into.

## Main results

* `equation_14_3_3` — a rule exact on `Π_{2n}^d` has `(f, g)_n = (f, g)` for `f, g ∈ Π_n^d`.
* `hyperinterpolation` — (14.3.4), the operator `L_n f = Σ_{m ≤ n} Σ_ℓ (f, φ_{m,ℓ})_n φ_{m,ℓ}`,
  with `hyperinterpolation_mem` and `hyperinterpolation_add`, `hyperinterpolation_smul`.
* `equation_14_3_5` — Exercise 14.3.1: `L_n p = p` for every `p ∈ Π_n^d`, so with the previous
  item `L_n` is a linear projection onto `Π_n^d`; `equation_14_3_5_idem` is idempotence.

## Not formalized here

* **(14.3.1)–(14.3.2)**, the disk rule itself: `∫_{𝔹₂} f ≈ (2π/(2n+1)) Σ_l Σ_m ω_l r_l f(r_l,
  2πm/(2n+1))`, Gauss–Legendre in the radius and the trapezoidal rule in the angle, with positive
  weights and exact on `Π_{2n+1}^2`. Both halves exist — `Quadrature.exists_gauss` gives the
  Gauss–Legendre rule and `integral_comp_polarCoord_symm` converts a disk integral to `r dr dθ` —
  but the exactness of the trapezoidal rule on trigonometric polynomials over equispaced nodes does
  not exist in this library or in Mathlib, and the polar-coordinate bookkeeping that turns a
  multivariate monomial into a product `r^k cos^a θ sin^b θ` is the bulk of the work. Everything
  below takes exactness as a hypothesis, so it applies to that rule the moment it is built, and to
  any other.
* **§14.3.1, (14.3.6)–(14.3.7)**, `‖L_n‖_{C→C} = O(n log n)`. This reduces to the same estimate on
  Jacobi polynomials as Theorem 14.2.4, with a discretization on top, and Mathlib has no Jacobi or
  Gegenbauer polynomials.
-/

open Approximation MeasureTheory MvPolynomial

namespace AtkinsonHan.Chapter14

variable {d N : ℕ} {K : Type*} [Fintype K] {μ : Measure (Fin d → ℝ)} {w : K → ℝ}
  {x : K → (Fin d → ℝ)} {φ : Fin N → MvPolynomial (Fin d) ℝ} {n : ℕ}

/-- **(14.3.3)**: a quadrature rule exact on `Π_{2n}^d` induces a discrete inner product `(f, g)_n`
that agrees with the continuous one on `Π_n^d`, because a product of two elements of `Π_n^d` lies in
`Π_{2n}^d`. Everything in the section rests on this identity. -/
theorem equation_14_3_3 (hw : IsMvWeight μ) (hex : IsExactOn μ w x (2 * n))
    {p q : MvPolynomial (Fin d) ℝ} (hp : p ∈ polySpace d n) (hq : q ∈ polySpace d n) :
    discreteInner w x p q = inner ℝ (hw.toL2 p) (hw.toL2 q) :=
  discreteInner_eq_inner_toL2 hw hex (mem_polySpace_iff.1 hp) (mem_polySpace_iff.1 hq)

/-- **(14.3.4)**: the **hyperinterpolation operator** `L_n f = Σ_{m ≤ n} Σ_ℓ (f, φ_{m,ℓ})_n
φ_{m,ℓ}`, the expansion of `f` along an orthonormal family `φ` spanning `Π_n^d`, with the discrete
inner product of a quadrature rule in place of the continuous one. -/
noncomputable def hyperinterpolation (w : K → ℝ) (x : K → (Fin d → ℝ))
    (φ : Fin N → MvPolynomial (Fin d) ℝ) (f : (Fin d → ℝ) → ℝ) : MvPolynomial (Fin d) ℝ :=
  hyperinterp w x φ f

/-- **(14.3.4)**: `L_n f` lies in `Π_n^d`. -/
theorem hyperinterpolation_mem (hspan : Submodule.span ℝ (Set.range φ) = polySpace d n)
    (f : (Fin d → ℝ) → ℝ) : hyperinterpolation w x φ f ∈ polySpace d n :=
  hspan ▸ hyperinterp_mem_span w x φ f

/-- **(14.3.4)**: `L_n` is additive. -/
theorem hyperinterpolation_add (f g : (Fin d → ℝ) → ℝ) :
    hyperinterpolation w x φ (f + g) = hyperinterpolation w x φ f + hyperinterpolation w x φ g :=
  hyperinterp_add w x φ f g

/-- **(14.3.4)**: `L_n` is homogeneous. -/
theorem hyperinterpolation_smul (c : ℝ) (f : (Fin d → ℝ) → ℝ) :
    hyperinterpolation w x φ (c • f) = c • hyperinterpolation w x φ f :=
  hyperinterp_smul w x φ c f

/-- **(14.3.5)**, which is **Exercise 14.3.1**: `L_n p = p` for every `p ∈ Π_n^d`. On `Π_n^d` the
discrete inner product is the continuous one by (14.3.3), so `L_n` agrees there with the orthogonal
projection `P_n`, which is the identity. With `hyperinterpolation_mem` and the two linearity
clauses, `L_n` is a linear projection of the continuous functions onto `Π_n^d`. -/
theorem equation_14_3_5 (hw : IsMvWeight μ) (hex : IsExactOn μ w x (2 * n))
    (hspan : Submodule.span ℝ (Set.range φ) = polySpace d n)
    (horth : Orthonormal ℝ fun i => hw.toL2 (φ i)) {p : MvPolynomial (Fin d) ℝ}
    (hp : p ∈ polySpace d n) :
    hyperinterpolation w x φ (fun y => eval y p) = p :=
  hyperinterp_eq_self hw hex
    (fun i => mem_polySpace_iff.1 (hspan ▸ Submodule.subset_span ⟨i, rfl⟩))
    horth (mem_polySpace_iff.1 hp) (hspan ▸ hp)

/-- **(14.3.5)**: `L_n` is idempotent, in the form its definition takes — it is applied to the
values of a function, and `L_n f` is a polynomial. -/
theorem equation_14_3_5_idem (hw : IsMvWeight μ) (hex : IsExactOn μ w x (2 * n))
    (hspan : Submodule.span ℝ (Set.range φ) = polySpace d n)
    (horth : Orthonormal ℝ fun i => hw.toL2 (φ i)) (f : (Fin d → ℝ) → ℝ) :
    hyperinterpolation w x φ (fun y => eval y (hyperinterpolation w x φ f)) =
      hyperinterpolation w x φ f :=
  equation_14_3_5 hw hex hspan horth (hyperinterpolation_mem hspan f)

end AtkinsonHan.Chapter14
