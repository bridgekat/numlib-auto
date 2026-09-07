<!--
The tracker plan (`plans/NumlibSurface/AtkinsonHan/Chapter13.toml` and the group files beside it)
is the authority on which declarations exist, and the source is the authority on what they say.
What is worth reading here is the argument: why the chapter's wholesale exclusion was wrong, what
each section really needs, and how the book's boundary integral becomes an ordinary kernel operator.
The per-result audit is `notes/audit/atkinsonhan-ch13.md`.
-->

# Surface plan: Atkinson–Han — Ch. 13

Scope: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis* (3rd ed.), Chapter 13,
boundary integral equations for the planar Laplace equation. The chapter was previously excluded
whole, here and in `backbone.md` §0.2, "because it needs Sobolev spaces on a boundary". It does not:
that is true of one and a half of its three sections, and the other one and a half are blocked by
something else or by nothing at all.

## 1. The exclusion, corrected

| section | what it needs | verdict |
|---|---|---|
| §13.1 | the divergence theorem on a piecewise smooth multiply connected planar region, Green's identities, the jump relations of the layer potentials | **skip** — planar potential theory, not Sobolev spaces |
| §13.1.2, (13.1.32)–(13.1.37) | harmonicity under inversion; continuity of a quotient of divided differences | **done**, `Chapter13/Section01` |
| §13.2 | Theorem 12.4.4 on `C_p(L)`, with `(−π + K)⁻¹` a hypothesis | **done**, `Chapter13/Section02` |
| §13.2.1, (13.2.14)–(13.2.21) | the jump relations, and the double layer potential on the *region* | **skip** — planar potential theory, as §13.1 |
| Exer 13.2.5, (13.2.20) | a continuous argument along a plane curve, i.e. a turning number | **skip** — planar topology, not analysis |
| §13.2.3, (13.2.27)–(13.2.32) | the Fourier coefficients of `log |2 sin(θ/2)|` | **done**, `Chapter13/Section02` |
| §13.2.2, Exer 13.2.8 | `H¹(2π)`, for one norm identity | **skip** |
| §13.3, (13.3.2)–(13.3.7), (13.3.15) | the periodic Sobolev scale `H^q(2π)` | **skip until that exists** |
| §13.3.1, (13.3.9)–(13.3.14) | `theorem_12_1_2` and `lemma_12_1_4`, plus the Fourier truncation on `L²` | **conditionally reachable**, `Chapter13/Section03` |

`H^q(2π)` is a weighted `ℓ²` space over the Fourier basis of `AddCircle`, needs none of the domain
machinery that blocks Chapters 7 and 10, and `backbone.md` §14.8 already singles it out as the one
Chapter 7 item that is reachable. So Chapter 13 is *not* blocked by the Sobolev obstruction that
blocks those chapters. It is blocked by potential theory in §13.1, and by a module the plans already
call buildable in §13.3.

## 2. How the boundary integral becomes a kernel operator

The book's equation for the interior Dirichlet problem is

`−π ρ(P) + ∫_S ρ(Q) ∂/∂n_Q log |P − Q| dS_Q = f(P)`,

an equation on the boundary curve `S`. Two steps carry it into the library:

* **Parametrize.** `S` is a regular `C²` simple closed curve of length `L`, so `∫_S … dS_Q` is an
  ordinary integral `∫_0^L … ds` of an `L`-periodic integrand. The space `C_p(L)` of continuous
  `L`-periodic functions is `C(AddCircle L, ℝ)`, and `∫_0^L … ds` is integration against the Haar
  measure `volume` of `AddCircle L`, which is finite. So the operator is
  `IntegralOperator.kernelCLM volume k` for the parametrized kernel `k`.
* **Remove the singularity.** The parametrized kernel (13.1.33) is a `0/0` quotient on the diagonal,
  and (13.1.34) says the quotient extends continuously with value minus one half the signed
  curvature. (The book's *prose* there says "one-half the curvature", contradicting its own display;
  the display is the one that agrees with (13.1.33) and with the inner normal `(−η′, ξ′)/|r′|` that
  §13.1 fixes, and it is what is formalized.) That is what makes the operator a
  *continuous*-kernel operator, hence compact by
  `IntegralOperator.isCompactOperator_kernelCLM`, and it is the only genuinely new analysis in the
  reachable part of the chapter. It is `Chapter13/Section01`'s `doubleLayerKernel`, still open; the
  obstruction is recorded there — continuous divided differences of order two, which the library has
  only through the Lagrange error formula, and which need the *integral* form of the second-order
  Taylor remainder that Mathlib does not have.

What is **not** reachable is the identification of that kernel operator with the boundary integral
`∫_S ρ(Q) ∂/∂n_Q log |P − Q| dS_Q` itself, which needs a surface measure and a normal field on `S`.
The surface therefore states the parametrized equation directly, which is what the book computes
with in any case.

## 3. Two things the book itself only quotes

* **`(−π + K)⁻¹` exists on `C_p(L)`.** The book's words are "From this work, `(−π + K)⁻¹` exists as a
  bounded operator from `C_p(L)` to `C_p(L)`", attributed to Colton–Kress and Mikhlin. It is a
  hypothesis of `equation_13_2_7`, and calling it one is faithful rather than weakening: the
  Fredholm alternative reduces it to the injectivity of `−π + K`, which is a uniqueness theorem for
  the interior Dirichlet problem and therefore potential theory again.
* **The sign.** The book writes the equation as `(−π + K) ρ = f`, not as `λ − K`. `equation_13_2_7`
  states it in the book's form and reads Theorem 12.4.4 at `λ = −π` for the kernel `−k`;
  `IntegralOperator.kernelCLM_neg` and `nystromCLM_neg` are what make that a rewrite rather than a
  restatement.

## 4. What §13.2 assumes about the quadrature rule

The book uses the trapezoidal rule with `h = L/n`, which for a periodic integrand is the equal-weight
rule at `n` equally spaced points. `equation_13_2_7` takes the rule's convergence and the bound on
its absolute weight sums as hypotheses, in the form Theorem 12.4.4 asks for, because the library has
no composite quadrature rule and no Riemann-sum convergence theorem — and neither has Mathlib. Both
are planned as `Quadrature.composite` and `Quadrature.tendsto_composite`; the second is short (split
the integral into panels, bound each by the modulus of continuity) and would discharge the
hypothesis. The *rate* is a different matter: spectral accuracy of the trapezoidal rule for a smooth
periodic integrand is AH Proposition 7.5.6 and needs `H^s(2π)`, so only the bound is stated.

## 5. What is left, and why it is topology

(13.2.32), the Fourier diagonalization `A ψ_m = ψ_m / max{1, |m|}` of the logarithmic single layer
operator, was the chapter's highest-leverage open item; it is now
`Numlib/Analysis/Fourier/LogSingleLayer` and `AtkinsonHan.Chapter13.equation_13_2_32`, with
Exercise 13.3.1 as the corollary it was billed to be. Its analytic content turned out *not* to be
the term-by-term integration of `−log |2 sin(θ/2)| = ∑_{m ≥ 1} cos(mθ)/m`, which converges only
conditionally: the identity `cos(u/2) sin(mu) = sin(u/2) (1 − cos(mu) + 2 ∑_{k < m} cos((k+1)u))`
hands over an elementary antiderivative for `log(sin(u/2)) cos(mu)` on `(0, 2π)`, and
`sin(mu) = 2 sin(u/2) ∑_{j < m} cos((2j+1)(u/2))` together with the continuity of `x log x` at `0`
extends it continuously to the closed interval, so the fundamental theorem of calculus crosses the
two logarithmic endpoints and no series is interchanged with an integral at all.

The two items that remain open are both **planar topology or potential theory**, and neither is a
missing piece of numerical analysis:

* **Exercise 13.2.5 and (13.2.20)**, `‖K‖ = π` for a convex region.
  `IntegralOperator.norm_kernelCLM` reduces it to `sup_t ∫_0^L |k(t, s)| ds = π`, and
  `doubleLayerKernel_eq_neg_im_div` identifies the integrand exactly: writing the curve as
  `r(s) = ξ(s) + i η(s)`, off the diagonal `k(t, s) = −Im (r′(s) / (r(s) − r(t)))`, which is minus
  `d/ds arg(r(s) − r(t))`. The row integral is therefore minus the total turning of the chord
  direction seen from the boundary point `r(t)`: `−π` for a regular simple closed curve, whose chord
  direction turns by `+π`, a boundary-point form of Hopf's Umlaufsatz, with the absolute value
  removable exactly when the region is convex. Mathlib
  has neither a continuous argument along a plane curve nor a turning number.
  An earlier note here and in the group file claimed that "the `≤ π` half for a general smooth curve
  follows from the same computation with `|k|`". That is **false**: for a non-convex curve the chord
  direction reverses and `∫_0^L |k(t, s)| ds > |∫_0^L k(t, s) ds| = π`, so `‖K‖ > π`. Convexity is
  used for the whole statement.
* **(13.2.19)** and the rest of §13.2.1. The book derives it from (13.2.16), the maximum principle
  for the harmonic `u − u_n` on `D_i`, and (13.2.17), the jump relation giving the boundary values
  of a double layer potential. The jump relations are precisely what §13.1 is skipped for, and the
  statement also needs the double layer potential as a function on the *region*, an integral over
  the boundary against surface measure. The maximum principle alone is within reach of Mathlib's
  `HarmonicContOnCl`; the jump relation is not. (§13.2.1 contains no singularity subtraction; an
  earlier note describing one had confused it with a scheme in Atkinson's own monograph.)
