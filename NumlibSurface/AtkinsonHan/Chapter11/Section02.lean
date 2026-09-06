import Numlib.Variational.Inequality.Basic
import NumlibSurface.AtkinsonHan.Chapter05.Section03
import NumlibSurface.AtkinsonHan.Chapter08.Section03
import NumlibSurface.AtkinsonHan.Chapter11.Section03

/-!
# Atkinson–Han §11.2: existence and uniqueness based on convex minimization

Surface formalization of §11.2 of Kendall Atkinson and Weimin Han, *Theoretical Numerical
Analysis: A Functional Analysis Framework*, 3rd edition, Springer, 2009.

The section turns a constrained convex minimization problem into an elliptic variational
inequality and back.  Theorem 11.2.1 does it for a general Gâteaux differentiable convex `f` plus
a second, possibly non-differentiable convex term `j`; Theorem 11.2.2 does it for the quadratic
energy `E v = ½ a(v,v) + j(v) - ℓ(v)` of a bounded, symmetric, `V`-elliptic bilinear form on a
real Hilbert space, where the minimizer also exists and is unique.

Theorem 11.2.1 extends Theorem 5.3.19 of `Chapter05/Section03` by the term `j`, and both are
specializations of `isMinOn_add_iff_forall_le` of `Numlib/Analysis/Convex/Gateaux`.  Formula
(11.2.3) — over a subspace and with `j = 0` the variational inequality is the variational equation
`⟨f'(u), v⟩ = 0` — is `AtkinsonHan.Ch05.theorem_5_3_19_submodule` and is not restated here.

The variational inequality of Theorem 11.2.2 is the predicate
`AtkinsonHan.Ch11.IsVariationalInequalitySolution` of §11.3, at `A = a.toOperator` and
`f = rieszRep ℓ`; that is the book's (11.3.12), so §11.2 and §11.3 really do state the same
problem, and the identification is `isVariationalInequalitySolution_toOperator_iff`.

## Deviations from the book

The book obtains the minimizer of Theorem 11.2.2 from its Theorem 3.3.12, which needs the
reflexivity of `V` and weak sequential compactness of its bounded sets.  The proof here stays in
the Hilbert space: the parallelogram law makes every minimizing sequence Cauchy, which is the
route of the backbone's `existsUnique_isMinOn_energy_add`.  The statement is the book's.

## Main results

* `theorem_11_2_1` — the minimization problem (11.2.1) and the variational inequality (11.2.2)
  have the same solutions.
* `theorem_11_2_2` — the energy of a bounded symmetric `V`-elliptic form has exactly one minimizer
  on a nonempty closed convex set, and the minimizers are the solutions of the variational
  inequality.
* `exercise_11_2_1` — the same over a complex Hilbert space, for a Hermitian `V`-elliptic
  sesquilinear form.

Not formalized: Examples 11.2.3 and 11.2.4, the obstacle problem and the simplified friction
problem, both of which name a domain and its Sobolev spaces.
-/

open Filter Set Topology
open scoped InnerProductSpace

namespace AtkinsonHan.Ch11

/-! ### Theorem 11.2.1: minimization and the variational inequality -/

section Gateaux

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {K : Set V} {f j : V → ℝ} {f' : V → V →L[ℝ] ℝ}

/-- **Theorem 11.2.1.**  Let `K` be a convex subset of a real normed space, let `f` be convex on
`K` with Gâteaux derivative `f' u` at every `u ∈ K`, and let `j` be convex on `K`.  Then `u ∈ K`
minimizes `f + j` over `K` — the book's (11.2.1) — if and only if

  `⟨f'(u), v - u⟩ + j(v) - j(u) ≥ 0`  for every `v ∈ K`,

which is (11.2.2).  The convexity of `K` is `hf.1` and is not assumed separately.

The case `j = 0` is `AtkinsonHan.Ch05.theorem_5_3_19`, and (11.2.3) — over a subspace and with
`j = 0` the inequality is the equation `⟨f'(u), v⟩ = 0` — is
`AtkinsonHan.Ch05.theorem_5_3_19_submodule`. -/
theorem theorem_11_2_1 (hf : ConvexOn ℝ K f) (hj : ConvexOn ℝ K j)
    (hG : ∀ u ∈ K, Ch05.HasGateauxDerivAt f (f' u) u) {u : V} (hu : u ∈ K) :
    IsMinOn (f + j) K u ↔ ∀ v ∈ K, 0 ≤ f' u (v - u) + j v - j u :=
  isMinOn_add_iff_forall_le hf hj hG hu

end Gateaux

/-! ### Theorem 11.2.2: the quadratic energy on a real Hilbert space -/

section Real

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {a : BilinForm V} {M α : ℝ}

/-- **Theorem 11.2.2.**  Let `V` be a real Hilbert space, `K` a nonempty closed convex subset,
`a` a bounded symmetric `V`-elliptic bilinear form, `ℓ ∈ V'` and `j` convex and lower
semicontinuous on `K`.  Then the energy

  `E v = ½ a(v,v) + j(v) - ℓ(v)`

has exactly one minimizer on `K`, and a point `u ∈ K` minimizes it if and only if

  `a(u, v - u) + j(v) - j(u) ≥ ℓ(v - u)`  for every `v ∈ K`,

which is the variational inequality (11.3.12) of §11.3.

The book derives the existence clause from its Theorem 3.3.12, using the reflexivity of `V`; the
proof used here is the Hilbert-space one, in which the parallelogram law makes every minimizing
sequence Cauchy and the affine minorant of Lemma 11.3.5 makes the energy bounded below. -/
theorem theorem_11_2_2 (hM : a.IsBoundedWith M) (hα : 0 < α) (ha : a.IsEllipticWith α)
    (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V) {j : V → ℝ} {K : Set V}
    (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : Convex ℝ K) (hj : ConvexOn ℝ K j)
    (hjlsc : LowerSemicontinuousOn j K) :
    (∃! u, u ∈ K ∧ IsMinOn (a.energy ℓ + j) K u) ∧
      ∀ u ∈ K, (IsMinOn (a.energy ℓ + j) K u ↔
        ∀ v ∈ K, a u (v - u) + j v - j u ≥ ℓ (v - u)) := by
  have hh : SesqForm.IsHermitian (𝕜 := ℝ) (a.toCLM hM) :=
    (BilinForm.isSymm_iff_isHermitian hM).mp hs
  have hcoer : SesqForm.IsCoerciveWith (𝕜 := ℝ) (a.toCLM hM) α :=
    (BilinForm.isEllipticWith_iff_isCoerciveWith hM).mp ha
  refine ⟨existsUnique_isMinOn_energy_add hh hα hcoer ℓ hKne hKcl hKcv hj hjlsc,
    fun u hu => (isMinOn_energy_add_iff hh hα.le hcoer ℓ hKcv hj hu).trans ?_⟩
  exact (isVariationalInequalitySolution_toOperator_iff hM j ℓ K u).trans
    ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩

end Real

/-! ### Exercise 11.2.1: the complex case -/

section Complex

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- **Exercise 11.2.1**, the complex case of Theorem 11.2.2.  On a complex Hilbert space, for a
Hermitian `V`-elliptic sesquilinear form `a`, a functional `ℓ ∈ V'` and a `j` convex and lower
semicontinuous on a nonempty closed convex `K`, the energy

  `E v = ½ re a(v,v) + j(v) - re ℓ(v)`

has exactly one minimizer on `K`, and `u ∈ K` minimizes it if and only if

  `re a(u, v - u) + j(v) - j(u) ≥ re ℓ(v - u)`  for every `v ∈ K`.

The real parts are the book's: `a(v,v)` is real for a Hermitian form, and what is minimized is a
real quantity.  Convexity of `K` is convexity for the real scalars, which is what convexity means
on a complex vector space.

The proof is Theorem 11.2.2 for the *real* bilinear form `b(u,v) = re a(u,v)`, which is the form
of the operator of `a` read in the real inner product `⟪·,·⟫_ℝ = re ⟪·,·⟫`: it is Hermitian and
`V`-elliptic with the same constant, and its energy is that of `a`.  The real inner product
structure is introduced inside the proof, as `InnerProductSpace.complexToReal` is deliberately not
an instance. -/
theorem exercise_11_2_1 {a : SesqForm ℂ V} (ha : a.IsHermitian) {α : ℝ} (hα : 0 < α)
    (hcoer : a.IsCoerciveWith α) (ℓ : V →L[ℂ] ℂ) {j : V → ℝ} {K : Set V} (hKne : K.Nonempty)
    (hKcl : IsClosed K) (hKcv : Convex ℝ K) (hj : ConvexOn ℝ K j)
    (hjlsc : LowerSemicontinuousOn j K) :
    (∃! u, u ∈ K ∧ IsMinOn (a.energy ℓ + j) K u) ∧
      ∀ u ∈ K, (IsMinOn (a.energy ℓ + j) K u ↔
        ∀ v ∈ K, RCLike.re (a u (v - u)) + j v - j u ≥ RCLike.re (ℓ (v - u))) := by
  let _ : InnerProductSpace ℝ V := InnerProductSpace.complexToReal
  obtain ⟨b, hbdef⟩ : ∃ b : SesqForm ℝ V,
      b = (innerSL ℝ).comp ((SesqForm.toOperator a : V →L[ℂ] V).restrictScalars ℝ) := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : V →L[ℝ] ℝ, L = RCLike.reCLM.comp (ℓ.restrictScalars ℝ) := ⟨_, rfl⟩
  have hbap : ∀ u v : V, b u v = RCLike.re (a u v) := by
    intro u v
    rw [hbdef]
    change inner ℝ (SesqForm.toOperator a u) v = _
    rw [real_inner_eq_re_inner ℂ, SesqForm.inner_toOperator]
  have hLap : ∀ v : V, L v = RCLike.re (ℓ v) := by
    intro v
    rw [hLdef]
    rfl
  have hherm : b.IsHermitian := by
    intro u v
    simp [hbap, ha v u]
  have hbcoer : b.IsCoerciveWith α := fun v => by simpa [hbap v v] using hcoer v
  have henergy : b.energy L + j = a.energy ℓ + j := by
    funext v
    simp only [Pi.add_apply, SesqForm.energy, hbap v v, hLap v, RCLike.re_to_real]
  rw [← henergy]
  refine ⟨existsUnique_isMinOn_energy_add hherm hα hbcoer L hKne hKcl hKcv hj hjlsc,
    fun u hu => (isMinOn_energy_add_iff hherm hα.le hbcoer L hKcv hj hu).trans ?_⟩
  constructor
  · rintro ⟨-, h⟩ v hv
    have hv' := h v hv
    rwa [SesqForm.inner_toOperator, SesqForm.inner_rieszRep, hbap, hLap] at hv'
  · intro h
    refine ⟨hu, fun v hv => ?_⟩
    rw [SesqForm.inner_toOperator, SesqForm.inner_rieszRep, hbap, hLap]
    exact h v hv

end Complex

end AtkinsonHan.Ch11
