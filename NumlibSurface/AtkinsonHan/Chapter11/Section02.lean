import Mathlib.Analysis.Convex.Strong
import Numlib.Variational.Inequality.Basic
import Numlib.Variational.Minimization
import NumlibSurface.AtkinsonHan.Chapter05.Section03
import NumlibSurface.AtkinsonHan.Chapter08.Section03
import NumlibSurface.AtkinsonHan.Chapter11.Section01

/-!
# Atkinson–Han §11.2: existence and uniqueness based on convex minimization

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §11.2.

The section turns a constrained convex minimization problem into an elliptic variational
inequality and back.  Theorem 11.2.1 does it for a general Gâteaux differentiable convex `f` plus
a second, possibly non-differentiable convex term `j`; Theorem 11.2.2 does it for the quadratic
energy `E v = ½ a(v,v) + j(v) - ℓ(v)` of a bounded, symmetric, `V`-elliptic bilinear form on a
real Hilbert space, where the minimizer also exists and is unique.

Theorem 11.2.1 extends Theorem 5.3.19 of `Chapter05/Section03` by the term `j`, and both are
specializations of `isMinOn_add_iff_forall_le` of `Numlib/Analysis/Convex/Gateaux`.  Formula
(11.2.3) — over a subspace and with `j = 0` the variational inequality is the variational equation
`⟨f'(u), v⟩ = 0` — is `AtkinsonHan.Chapter05.theorem_5_3_19_submodule` and is not restated here.

The variational inequality of Theorem 11.2.2 is written out here in the book's own words, as the
inequality `a(u, v - u) + j(v) - j(u) ≥ ℓ(v - u)`.  It is the book's (11.3.12), so §11.2 and §11.3
really do state the same problem; §11.3, which comes later, names it
`AtkinsonHan.Chapter11.IsVariationalInequalitySolution` at `A = a.toOperator` and `f = rieszRep ℓ`,
and `AtkinsonHan.Chapter11.isVariationalInequalitySolution_toOperator_iff` is the identification.

## Deviations from the book

The book obtains the minimizer of Theorem 11.2.2 from its Theorem 3.3.12, which needs the
reflexivity of `V` and weak sequential compactness of its bounded sets.  The proof here stays in
the Hilbert space: the parallelogram law makes every minimizing sequence Cauchy, which is the
route of the backbone's `existsUnique_isMinOn_energy_add`.  The statement is the book's.

## Main results

* `theorem_11_2_1` — the minimization problem (11.2.1) and the variational inequality (11.2.2)
  have the same solutions.
* `theorem_11_2_2` — the energy of a bounded symmetric `V`-elliptic form has exactly one minimizer
  on a nonempty closed convex set; `theorem_11_2_2_iff` — its minimizers are the solutions of the
  variational inequality.
* `exercise_11_2_1` — both claims at once over a complex Hilbert space, for a Hermitian
  `V`-elliptic sesquilinear form.  They stay bundled there because the two halves share the
  passage to the real form `b(u,v) = re a(u,v)` that is the whole of the proof.

* `example_11_2_3` — the obstacle problem of §11.1 (`Chapter11/Section01`): the admissible set
  `K = {v ∈ H¹₀(Ω) | v ≥ ψ a.e.}` is nonempty, closed and convex, the energy
  `∫_Ω (½ |∇v|² − f v)` is strictly convex, coercive and continuous, and Theorem 11.2.2 gives the
  minimization problem (11.1.6) and the variational inequality (11.1.7) exactly one solution.
  The strong convexity of the quadratic energy of a `V`-elliptic symmetric form,
  `SesqForm.strongConvexOn_energy`, and the coercivity of a continuous strongly convex functional,
  `StrongConvexOn.isCoerciveFunctionalOn_of_continuous`, are proved here on the way and belong in
  the backbone (`Numlib/Variational/LaxMilgram.lean`, `Numlib/Variational/Minimization.lean`);
  `theorem_11_2_2_zero` is Theorem 11.2.2 at `j = 0`.

Not formalized: Example 11.2.4, the simplified friction problem, whose functional
`g ∫_Γ |v| ds` needs the trace of an `H¹(Ω)` function and the surface measure on `Γ`.
-/

open Filter Set TopologicalSpace Topology
open scoped InnerProductSpace

namespace AtkinsonHan.Chapter11

/-! ### Theorem 11.2.1: minimization and the variational inequality -/

section Gateaux

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {K : Set V} {f j : V → ℝ} {f' : V → V →L[ℝ] ℝ}

/-- **Theorem 11.2.1.**  Let `K` be a convex subset of a real normed space, let `f` be convex on
`K` with Gâteaux derivative `f' u` at every `u ∈ K`, and let `j` be convex on `K`.  Then `u ∈ K`
minimizes `f + j` over `K` — the book's (11.2.1) — if and only if

  `⟨f'(u), v - u⟩ + j(v) - j(u) ≥ 0`  for every `v ∈ K`,

which is (11.2.2).  The convexity of `K` is `hf.1` and is not assumed separately.

The case `j = 0` is `AtkinsonHan.Chapter05.theorem_5_3_19`, and (11.2.3) — over a subspace and with
`j = 0` the inequality is the equation `⟨f'(u), v⟩ = 0` — is
`AtkinsonHan.Chapter05.theorem_5_3_19_submodule`. -/
theorem theorem_11_2_1 (hf : ConvexOn ℝ K f) (hj : ConvexOn ℝ K j)
    (hG : ∀ u ∈ K, Chapter05.HasGateauxDerivAt f (f' u) u) {u : V} (hu : u ∈ K) :
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

has exactly one minimizer on `K`.  That the minimizers are the solutions of the variational
inequality (11.3.12) is `theorem_11_2_2_iff`.

The book derives the existence clause from its Theorem 3.3.12, using the reflexivity of `V`; the
proof used here is the Hilbert-space one, in which the parallelogram law makes every minimizing
sequence Cauchy and the affine minorant of Lemma 11.3.5 makes the energy bounded below. -/
theorem theorem_11_2_2 (hM : a.IsBoundedWith M) (hα : 0 < α) (ha : a.IsEllipticWith α)
    (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V) {j : V → ℝ} {K : Set V}
    (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : Convex ℝ K) (hj : ConvexOn ℝ K j)
    (hjlsc : LowerSemicontinuousOn j K) : ∃! u, u ∈ K ∧ IsMinOn (a.energy ℓ + j) K u :=
  existsUnique_isMinOn_energy_add ((BilinForm.isSymm_iff_isHermitian hM).mp hs) hα
    ((BilinForm.isEllipticWith_iff_isCoerciveWith hM).mp ha) ℓ hKne hKcl hKcv hj hjlsc

/-- **Theorem 11.2.2**, characterization: `u ∈ K` minimizes `E v = ½ a(v,v) + j(v) - ℓ(v)` over
`K` if and only if

  `a(u, v - u) + j(v) - j(u) ≥ ℓ(v - u)`  for every `v ∈ K`,

which is the variational inequality (11.3.12) of §11.3, in the `≥` spelling §11.3 uses throughout.
Neither closedness of `K` nor lower semicontinuity of `j` is needed here; they are what make a
minimizer exist. -/
theorem theorem_11_2_2_iff (hM : a.IsBoundedWith M) (hα : 0 < α) (ha : a.IsEllipticWith α)
    (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V) {j : V → ℝ} {K : Set V}
    (hKcv : Convex ℝ K) (hj : ConvexOn ℝ K j) {u : V} (hu : u ∈ K) :
    IsMinOn (a.energy ℓ + j) K u ↔ ∀ v ∈ K, a u (v - u) + j v - j u ≥ ℓ (v - u) := by
  have hh : SesqForm.IsHermitian (𝕜 := ℝ) (a.toCLM hM) :=
    (BilinForm.isSymm_iff_isHermitian hM).mp hs
  have hcoer : SesqForm.IsCoerciveWith (𝕜 := ℝ) (a.toCLM hM) α :=
    (BilinForm.isEllipticWith_iff_isCoerciveWith hM).mp ha
  refine (isMinOn_energy_add_iff hh hα.le hcoer ℓ hKcv hj hu).trans ?_
  simp only [_root_.IsVariationalInequalitySolution, BilinForm.inner_toOperator,
    BilinForm.inner_rieszRep, ge_iff_le]
  exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩

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

/-! ### Example 11.2.3: the obstacle problem -/

section Obstacle

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The energy `E(v) = ½ a(v, v) − ℓ(v)` of a symmetric form coercive with constant `c` is
`c`-strongly convex: `E(s x + t y) = s E(x) + t E(y) − (s t / 2) a(x − y, x − y)`.  Belongs beside
`SesqForm.convexOn_energy` in `Numlib/Variational/LaxMilgram.lean`. -/
theorem _root_.SesqForm.strongConvexOn_energy {a : SesqForm ℝ V} (ha : a.IsHermitian) {c : ℝ}
    (hc : a.IsCoerciveWith c) (ℓ : V →L[ℝ] ℝ) : StrongConvexOn univ c (a.energy ℓ) := by
  refine ⟨convex_univ, fun x _ y _ s t hs ht hst ↦ ?_⟩
  have hsym : a y x = a x y := by simpa using ha y x
  have hcoer := hc (x - y)
  have hsub : a (x - y) (x - y) = a x x - (a x y + a y x) + a y y := by
    simp only [map_sub, sub_apply]
    ring
  rw [RCLike.re_to_real, hsub, hsym] at hcoer
  simp only [SesqForm.energy, RCLike.re_to_real, map_smulₛₗ, map_add, add_apply, smul_apply,
    smul_eq_mul, RingHom.id_apply, starRingEnd_apply, star_trivial, hsym]
  obtain rfl : t = 1 - s := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hcoer (mul_nonneg hs ht)]

/-- A strongly convex continuous functional is coercive on any nonempty set: the local lower
bound that `StrongConvexOn.isCoerciveFunctionalOn` asks for comes from continuity at a point.
Belongs beside it in `Numlib/Variational/Minimization.lean`. -/
theorem _root_.StrongConvexOn.isCoerciveFunctionalOn_of_continuous {K : Set V} {f : V → ℝ} {m : ℝ}
    (hf : StrongConvexOn K m f) (hm : 0 < m) (hne : K.Nonempty) (hc : Continuous f) :
    IsCoerciveFunctionalOn f K := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ∀ x ∈ Metric.ball x₀ r, f x₀ - 1 < f x := by
    have h := (hc.tendsto x₀).eventually (lt_mem_nhds (show f x₀ - 1 < f x₀ by linarith))
    rw [Metric.eventually_nhds_iff_ball] at h
    exact h
  refine hf.isCoerciveFunctionalOn hm hx₀ hr ⟨f x₀ - 1, ?_⟩
  rintro _ ⟨x, ⟨-, hxb⟩, rfl⟩
  exact (hball x hxb).le

/-- Strong convexity on the whole space restricts to any convex set.  Belongs in
`Mathlib/Analysis/Convex/Strong.lean`. -/
theorem _root_.StrongConvexOn.mono_of_univ {K : Set V} {f : V → ℝ} {m : ℝ}
    (hf : StrongConvexOn univ m f) (hK : Convex ℝ K) : StrongConvexOn K m f :=
  ⟨hK, fun x _ y _ _ _ hs ht hst ↦ hf.2 (mem_univ x) (mem_univ y) hs ht hst⟩

variable [CompleteSpace V] {a : BilinForm V} {M α : ℝ}

/-- **Theorem 11.2.2 with `j = 0`**: the energy of a bounded symmetric `V`-elliptic form has
exactly one minimizer on a nonempty closed convex set, and that minimizer is the unique solution
of the variational inequality `a(u, v − u) ≥ ℓ(v − u)`, the book's (11.3.13).  The instantiation
of `theorem_11_2_2` and `theorem_11_2_2_iff` at `j = 0`, kept abstract so that the concrete
Sobolev instance of Example 11.2.3 is a single application (the typed Sobolev context makes every
unification step expensive). -/
theorem theorem_11_2_2_zero (hM : a.IsBoundedWith M) (hα : 0 < α) (ha : a.IsEllipticWith α)
    (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V) {K : Set V}
    (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : Convex ℝ K) :
    (∃! u, u ∈ K ∧ IsMinOn (a.energy ℓ) K u) ∧
      ∃! u, u ∈ K ∧ ∀ v ∈ K, a u (v - u) ≥ ℓ (v - u) := by
  have hmin := theorem_11_2_2 hM hα ha hs ℓ (j := fun _ ↦ (0 : ℝ)) hKne hKcl hKcv
    (convexOn_const _ hKcv) (lowerSemicontinuous_const.lowerSemicontinuousOn _)
  have e0 : a.energy ℓ + (fun _ ↦ (0 : ℝ)) = a.energy ℓ := funext fun v ↦ add_zero _
  rw [e0] at hmin
  refine ⟨hmin, ?_⟩
  have hiff : ∀ u ∈ K, IsMinOn (a.energy ℓ) K u ↔ ∀ v ∈ K, a u (v - u) ≥ ℓ (v - u) :=
    fun u hu ↦ by
      have h := theorem_11_2_2_iff hM hα ha hs ℓ (j := fun _ ↦ (0 : ℝ)) hKcv (convexOn_const _ hKcv)
        hu
      rw [e0] at h
      simp only [sub_zero, add_zero] at h
      exact h
  obtain ⟨u, ⟨hu, humin⟩, huniq⟩ := hmin
  refine ⟨u, ⟨hu, (hiff u hu).1 humin⟩, ?_⟩
  rintro y ⟨hy, hyvi⟩
  exact huniq y ⟨hy, (hiff y hy).2 hyvi⟩

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))

/-- **Example 11.2.3 (the obstacle problem, continued)**: on a bounded open `Ω ⊆ B(0, R)`, for an
obstacle `ψ ∈ H¹(Ω)` whose positive part `max (ψ, 0)` is the function of an element of `H¹₀(Ω)`
(the reading of "`ψ ≤ 0` on `Γ`", see `Chapter11/Section01`) and a load `f ∈ L²(Ω)`, the set
`K = {v ∈ H¹₀(Ω) | v ≥ ψ a.e.}` is nonempty (it contains `max (0, ψ)`), closed and convex, and the
energy `E(v) = ∫_Ω (½ |∇v|² − f v)` is strictly convex, coercive and continuous on it.  Hence, by
Theorem 11.2.2, the minimization problem (11.1.6) has exactly one solution `u ∈ K`, and so has the
equivalent variational inequality (11.1.7),
`∫_Ω ∇u · ∇(v − u) ≥ ∫_Ω f (v − u)` for all `v ∈ K`.

Strict convexity and coercivity come from the strong convexity of the quadratic energy of a
`V`-elliptic symmetric form (`SesqForm.strongConvexOn_energy`, with Poincaré's constant
`(1 + (2R)²)⁻¹`), continuity from `SesqForm.continuous_energy`; the minimizer is
`theorem_11_2_2` at `j = 0` (`theorem_11_2_2_zero`), and the inequality is its
characterization, Example 11.1.1.  The set-theoretic clauses are `obstacleSet_nonempty`,
`isClosed_obstacleSet` and `convex_obstacleSet` of `Chapter11/Section01`. -/
theorem example_11_2_3 {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ Metric.ball 0 R)
    {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    (hψ : ∃ w ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, SobolevMultiIndex.fn w
      =ᵐ[MeasureTheory.volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ max (SobolevMultiIndex.fn ψ x) 0)
    (f : MeasureTheory.Lp ℝ 2
      (MeasureTheory.volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (obstacleSet Ω ψ).Nonempty ∧ IsClosed (obstacleSet Ω ψ) ∧ Convex ℝ (obstacleSet Ω ψ) ∧
    StrictConvexOn ℝ (obstacleSet Ω ψ) (obstacleEnergy Ω f) ∧
    IsCoerciveFunctionalOn (obstacleEnergy Ω f) (obstacleSet Ω ψ) ∧
    Continuous (obstacleEnergy Ω f) ∧
    (∃! u, u ∈ obstacleSet Ω ψ ∧ IsMinOn (obstacleEnergy Ω f) (obstacleSet Ω ψ) u) ∧
    ∃! u, u ∈ obstacleSet Ω ψ ∧ ∀ v ∈ obstacleSet Ω ψ,
      ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        f x * SobolevMultiIndex.fn ((v - u : SobolevEuclideanZero (d + 1) 1 2 Ω) :
          SobolevEuclidean (d + 1) 1 2 Ω) x
      ≤ ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        ∑ i, SobolevMultiIndex.weakDeriv (u : SobolevEuclidean (d + 1) 1 2 Ω)
          (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv ((v - u : SobolevEuclideanZero (d + 1) 1 2 Ω) :
            SobolevEuclidean (d + 1) 1 2 Ω) (MultiIndexLE.single i) x := by
  have hM := dirichletBilinForm_isBoundedWith Ω
  have hα := dirichletBilinForm_isEllipticWith Ω hR hΩ
  have hs := dirichletBilinForm_isSymm Ω
  have hpos : (0 : ℝ) < (1 + (2 * R) ^ 2)⁻¹ := by positivity
  have hne := obstacleSet_nonempty Ω hψ
  have hcl := isClosed_obstacleSet Ω ψ
  have hcv := convex_obstacleSet Ω ψ
  have hstrong : StrongConvexOn (obstacleSet Ω ψ) (1 + (2 * R) ^ 2)⁻¹ (obstacleEnergy Ω f) :=
    (SesqForm.strongConvexOn_energy ((BilinForm.isSymm_iff_isHermitian hM).mp hs)
      ((BilinForm.isEllipticWith_iff_isCoerciveWith hM).mp hα) (loadZero Ω f)).mono_of_univ hcv
  have hcont : Continuous (obstacleEnergy Ω f) :=
    SesqForm.continuous_energy ((dirichletBilinForm Ω).toCLM hM) (loadZero Ω f)
  obtain ⟨hmin, hvi⟩ := theorem_11_2_2_zero hM hpos hα hs (loadZero Ω f) hne hcl hcv
  refine ⟨hne, hcl, hcv, hstrong.strictConvexOn hpos,
    hstrong.isCoerciveFunctionalOn_of_continuous hpos hne hcont, hcont, hmin, ?_⟩
  have e : ∀ v w : SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletBilinForm Ω v w
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        ∑ i, SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 2 Ω)
          (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv (w : SobolevEuclidean (d + 1) 1 2 Ω)
            (MultiIndexLE.single i) x := fun v w ↦
    Elliptic.dirichletForm_apply Ω v w
  simp only [e, loadZero_apply, ge_iff_le] at hvi
  exact hvi

end Obstacle

end AtkinsonHan.Chapter11
