import Numlib.Approximation.DiskQuadrature
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
book's spaces. `equation_14_3_1` then supplies the book's own rule, which meets that hypothesis.

The family `{φ_{m,ℓ} : m ≤ n}` the book expands along appears here as a single `L²(μ)`-orthonormal
family `φ` spanning `Π_n^d`, which by Lemma 14.2.1 is what an orthonormal basis of each `V_m^d` with
`m ≤ n` assembles into.

## Main results

* `equation_14_3_1` — (14.3.1), the disk rule: Gauss–Legendre in the radius and the trapezoidal
  rule in the angle, with positive weights, nodes in the open unit disk, and exactness on
  `Π_{2n}^2`.
* `equation_14_3_3` — a rule exact on `Π_{2n}^d` has `(f, g)_n = (f, g)` for `f, g ∈ Π_n^d`.
* `hyperinterpolation` — (14.3.4), the operator `L_n f = Σ_{m ≤ n} Σ_ℓ (f, φ_{m,ℓ})_n φ_{m,ℓ}`,
  with `hyperinterpolation_mem` and `hyperinterpolation_add`, `hyperinterpolation_smul`.
* `equation_14_3_5` — Exercise 14.3.1: `L_n p = p` for every `p ∈ Π_n^d`, so with the previous
  item `L_n` is a linear projection onto `Π_n^d`; `equation_14_3_5_idem` is idempotence.

## Deviations from the book

The book asserts that the rule (14.3.1) is exact on `Π_{2n+1}^2`. **It is not**: it is exact on
`Π_{2n}^2` and no further, and `equation_14_3_1` states that. The counterexample is `n = 1` and
`f = x³`, whose integral over the disk vanishes by symmetry while the rule returns about `0.3055`;
the reason is that `cos^a θ sin^b θ` with `a + b = 2n + 1` carries the frequencies `±(2n + 1)`,
which `2n + 1` equispaced angles cannot annihilate. `Numlib.Approximation.DiskQuadrature` records
the mechanism. Nothing in the chapter is weakened by this: (14.3.3), the only use of (14.3.1) in
the book, applies the rule to products of two elements of `Π_n^2`, and so needs `Π_{2n}^2` alone.

## Not formalized here

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

/-- **(14.3.1)**: the book's quadrature rule on the unit disk,

  `∫ f ≈ (2π/(2n+1)) Σ_{l=0}^{n} Σ_{m=0}^{2n} ω_l r_l f(r_l cos θ_m, r_l sin θ_m)`,
  `θ_m = 2πm/(2n+1)`,

with `(r_l, ω_l)` the `(n+1)`-point Gauss–Legendre rule on `[0, 1]`: the radial nodes lie in
`(0, 1)`, so all `(n+1)(2n+1)` weights `(2π/(2n+1)) ω_l r_l` are positive, and the rule is exact on
`Π_{2n}^2` — not on `Π_{2n+1}^2`, as the book states; see the deviations above. Exactness on
`Π_{2n}^2` is exactly the hypothesis of `equation_14_3_3` and hence of (14.3.4) and (14.3.5), so
this rule instantiates the whole section. -/
theorem equation_14_3_1 (n : ℕ) :
    ∃ ρ ω : Fin (n + 1) → ℝ, (∀ l, ρ l ∈ Set.Ioo (0 : ℝ) 1) ∧ (∀ l, 0 < ω l) ∧
      IsExactOn (MeasureTheory.volume.restrict Quadrature.unitDisk)
        (fun k : Fin (n + 1) × Fin (2 * n + 1) => 2 * Real.pi / (2 * n + 1) * (ω k.1 * ρ k.1))
        (fun k : Fin (n + 1) × Fin (2 * n + 1) =>
          ![ρ k.1 * Real.cos (Quadrature.angleNode (2 * n + 1) k.2),
            ρ k.1 * Real.sin (Quadrature.angleNode (2 * n + 1) k.2)])
        (2 * n) :=
  Quadrature.exists_diskRule n

end AtkinsonHan.Chapter14
