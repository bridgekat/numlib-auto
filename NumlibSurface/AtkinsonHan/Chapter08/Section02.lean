import Numlib.Analysis.Normed.Operator.Unbounded.ClosedRange
import Numlib.Analysis.PDE.DirichletLaplacian
import Numlib.Analysis.PDE.Elliptic.Spectral
import Numlib.Variational.Forms
import Numlib.Variational.LaxMilgram

/-!
# Atkinson–Han §8.2: general existence and uniqueness for operator equations

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §8.2.

The section proves that a linear operator `L : D(L) ⊂ V → W` which is closed (Definition 8.2.2)
and satisfies the a priori stability estimate (8.2.2) `‖L v‖ ≥ c ‖v‖` has closed range, so that
`L u = f` is uniquely solvable as soon as `R(L)^⊥ = {0}` (Theorems 8.2.1 and 8.2.4).  Partial
operators are `LinearPMap` (`V →ₗ.[ℝ] W`), whose `domain` is the book's `D(L)`; the book's
closedness is Mathlib's `LinearPMap.IsClosed` (`isClosed_iff_seq` records the equivalence with the
book's sequential phrasing) and the stability estimate is used unbundled, exactly as the backbone
states it.

Theorem 8.2.7, Banach's closed range theorem, is `theorem_8_2_7` in the book's generality —
densely defined closed operators between Banach spaces, with the dual operator
`LinearPMap.strongDualAdjoint` of `Numlib/Analysis/Normed/Operator/Unbounded/Adjoint.lean` and
the theorem itself from `Unbounded/ClosedRange.lean`; its Hilbert-space bounded case, which was
all that could be stated before the Banach adjoint existed, is kept as `theorem_8_2_7_hilbert`.

The two examples that name a domain are here as well.  Example 8.2.3, the Laplacian `−Δ` on
`L²(Ω)` as a closed unbounded operator, is `example_8_2_3` on the backbone's Dirichlet Laplacian
`dirichletLaplacian Ω` (`Numlib/Analysis/PDE/DirichletLaplacian.lean`), its non-continuity
witnessed by the Dirichlet eigenfunctions of `Numlib/Analysis/PDE/Elliptic/Spectral.lean`.
Example 8.2.6, the model Dirichlet problem read through Example 8.2.5, is `example_8_2_6` on the
operator `modelOperator Ω`, the Dirichlet form `∫_Ω ∇u · ∇v` restricted to
`V = H¹₀(Ω) = SobolevEuclideanZero (d + 1) 1 2 Ω` as a map into `V' = H^{-1}(Ω)`; the seminorm
`|·|_{H¹}` the book takes as the norm of `V` is `SobolevMultiIndex.gradNorm`, a norm on `V`
equivalent to the `H¹` norm by Poincaré's inequality (`Numlib/Analysis/Sobolev/Poincare.lean`).
Both examples are set on bounded open sets `Ω ⊆ ℝ^{d+1}`; the book's Lipschitz boundary is not
needed.  The AH surface's own `H¹₀(Ω)` and `H^{-1}(Ω)` (`AtkinsonHan.Chapter07.definition_7_2_9`,
`definition_7_2_12_hMinusOne`) are the same spaces in the tensor formulation of `W^{1,2}(Ω)`,
whose norm is equivalent but not equal; the examples are stated on the multi-index formulation,
where the backbone's Dirichlet form and Poincaré inequality live.

Exercise 8.2.1 closes the file with the finite-dimensional instance the book asks for: on
`ℝ^d = EuclideanSpace ℝ (Fin d)` every range is closed, so Theorem 8.2.1 alone turns uniqueness of
a solution of `A x = b` into existence for every `b`.
-/

open Filter MeasureTheory Metric Set TopologicalSpace Topology
open scoped ContDiff Distributions ENNReal InnerProductSpace

namespace AtkinsonHan.Chapter08

/-- The uniqueness step of §8.2: the stability estimate applied to a difference of two solutions
leaves `c ‖v‖ ≤ 0`, and a positive `c` then forces `v = 0`. -/
private theorem eq_zero_of_mul_norm_nonpos {V : Type*} [NormedAddCommGroup V] {c : ℝ} (hc : 0 < c)
    {v : V} (h : c * ‖v‖ ≤ 0) : v = 0 :=
  norm_le_zero_iff.mp (by nlinarith [norm_nonneg v])

section Normed

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Definition 8.2.2 in the book's sequential form: `T` is closed iff whenever `v_n ∈ D(T)`,
`v_n → v` and `T v_n → w`, then `v ∈ D(T)` and `T v = w`.  Mathlib's `LinearPMap.IsClosed` is
closedness of the graph, which on a metric space is the same thing; the backbone's
`LinearPMap.isClosed_iff_seq` (`Numlib/Analysis/Normed/Operator/Unbounded/Basic.lean`) is the
statement over any nontrivially normed field. -/
theorem isClosed_iff_seq (T : V →ₗ.[ℝ] W) :
    T.IsClosed ↔ ∀ (v : ℕ → T.domain) (x : V) (w : W),
      Tendsto (fun n => (v n : V)) atTop (𝓝 x) → Tendsto (fun n => T (v n)) atTop (𝓝 w) →
        ∃ hx : x ∈ T.domain, T ⟨x, hx⟩ = w :=
  LinearPMap.isClosed_iff_seq T

/-- The remark after Definition 8.2.2: a continuous linear operator defined on all of `V` is
closed. -/
theorem isClosed_toPMap_top (f : V →L[ℝ] W) : ((f : V →ₗ[ℝ] W).toPMap ⊤).IsClosed := by
  rw [isClosed_iff_seq]
  intro v x w hv hw
  refine ⟨Submodule.mem_top, ?_⟩
  have hfx : Tendsto (fun n => f (v n : V)) atTop (𝓝 (f x)) := (f.continuous.tendsto x).comp hv
  exact tendsto_nhds_unique hfx hw

/-- The stability estimate (8.2.2) `c ‖v‖ ≤ ‖L v‖` is Mathlib's `AntilipschitzWith` with constant
`c⁻¹`; the equivalence is recorded so that Mathlib's antilipschitz API is available, while the
backbone's §8.2 theorems take the unbundled form directly. -/
theorem stabilityEstimate_iff_antilipschitz (L : V →L[ℝ] W) {c : ℝ} (hc : 0 < c) :
    (∀ v, c * ‖v‖ ≤ ‖L v‖) ↔ AntilipschitzWith (Real.toNNReal c⁻¹) L := by
  have hcoe : ((Real.toNNReal c⁻¹ : NNReal) : ℝ) = c⁻¹ := Real.coe_toNNReal _ (by positivity)
  constructor
  · intro h
    refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
    have hxy := h (x - y)
    rw [hcoe, dist_eq_norm, dist_eq_norm, ← map_sub, inv_mul_eq_div, le_div_iff₀ hc]
    linarith
  · intro h v
    have hd := h.le_mul_dist v 0
    simp only [hcoe, dist_zero_right, map_zero] at hd
    rw [inv_mul_eq_div, le_div_iff₀ hc] at hd
    linarith

/-- The linear case of Theorem 8.2.8 (a) *is* the stability estimate (8.2.2). -/
theorem theorem_8_2_8a_linear (L : V →L[ℝ] W) {c : ℝ} :
    (∀ u v : V, c * ‖u - v‖ ≤ ‖L u - L v‖) ↔ ∀ v, c * ‖v‖ ≤ ‖L v‖ := by
  constructor
  · intro h v
    simpa using h v 0
  · intro h u v
    rw [← map_sub]
    exact h (u - v)

end Normed

section Metric

variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]

/-- Theorem 8.2.8 (a): if `‖T u − T v‖ ≥ c ‖u − v‖` on `D(T)` with `c > 0`, the (possibly
nonlinear) equation `T u = w` has at most one solution in `D(T)`. -/
theorem theorem_8_2_8a {D : Set V} (T : V → W) {c : ℝ} (hc : 0 < c)
    (hstab : ∀ u ∈ D, ∀ v ∈ D, c * ‖u - v‖ ≤ ‖T u - T v‖) {w : W} {u₁ u₂ : V} (h₁ : u₁ ∈ D)
    (h₂ : u₂ ∈ D) (hw₁ : T u₁ = w) (hw₂ : T u₂ = w) : u₁ = u₂ := by
  have h := hstab u₁ h₁ u₂ h₂
  rw [hw₁, hw₂, sub_self, norm_zero] at h
  exact sub_eq_zero.mp (eq_zero_of_mul_norm_nonpos hc h)

/-- Theorem 8.2.8 (b): if `‖(T u − u) − (T v − v)‖ < ‖u − v‖` for distinct `u, v ∈ D(T)`, the
equation `T u = w` has at most one solution in `D(T)`. -/
theorem theorem_8_2_8b {D : Set V} (T : V → V)
    (hstab : ∀ u ∈ D, ∀ v ∈ D, u ≠ v → ‖(T u - u) - (T v - v)‖ < ‖u - v‖) {w : V} {u₁ u₂ : V}
    (h₁ : u₁ ∈ D) (h₂ : u₂ ∈ D) (hw₁ : T u₁ = w) (hw₂ : T u₂ = w) : u₁ = u₂ := by
  by_contra hne
  have h := hstab u₁ h₁ u₂ h₂ hne
  rw [hw₁, hw₂] at h
  have heq : w - u₁ - (w - u₂) = -(u₁ - u₂) := by abel
  rw [heq, norm_neg] at h
  exact absurd h (lt_irrefl _)

end Metric

section Hilbert

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Theorem 8.2.1: for a linear operator into a Hilbert space `W`, the range is all of `W` iff it
is closed and its orthogonal complement is trivial.  (The book separates the two directions with
the Hahn–Banach theorem; the proof here uses orthogonal projections, and needs completeness only
of `W`.) -/
theorem theorem_8_2_1 [CompleteSpace W] (L : V →ₗ.[ℝ] W) :
    LinearMap.range L.toFun = ⊤ ↔
      IsClosed (LinearMap.range L.toFun : Set W) ∧ (LinearMap.range L.toFun)ᗮ = ⊥ := by
  constructor
  · intro h
    rw [h]
    exact ⟨by simp, Submodule.top_orthogonal_eq_bot⟩
  · rintro ⟨hc, ho⟩
    rw [← hc.submodule_topologicalClosure_eq]
    exact Submodule.topologicalClosure_eq_top_iff.mpr ho

/-- Theorem 8.2.4: a closed operator satisfying the stability estimate (8.2.2) and with dense
range is uniquely solvable.  The closed-range half is the backbone's
`LinearPMap.isClosed_range_of_isClosed_of_le_norm`; Theorem 8.2.1 turns it into surjectivity, and
(8.2.2) gives uniqueness. -/
theorem theorem_8_2_4 [CompleteSpace V] [CompleteSpace W] (L : V →ₗ.[ℝ] W) (hL : L.IsClosed) {c : ℝ}
    (hc : 0 < c) (hstab : ∀ v : L.domain, c * ‖(v : V)‖ ≤ ‖L v‖)
    (horth : (LinearMap.range L.toFun)ᗮ = ⊥) (f : W) : ∃! u : L.domain, L u = f := by
  have hclosed := LinearPMap.isClosed_range_of_isClosed_of_le_norm L hL hc hstab
  have htop : LinearMap.range L.toFun = ⊤ := (theorem_8_2_1 L).mpr ⟨hclosed, horth⟩
  have hmem : f ∈ LinearMap.range L.toFun := htop ▸ Submodule.mem_top
  obtain ⟨u, hu⟩ := hmem
  refine ⟨u, hu, fun y hy => ?_⟩
  have hy' : L.toFun y = f := hy
  have hd : L.toFun (y - u) = 0 := by rw [map_sub, hy', hu, sub_self]
  have h : c * ‖((y - u : L.domain) : V)‖ ≤ ‖L.toFun (y - u)‖ := hstab (y - u)
  rw [hd, norm_zero] at h
  have hz : ((y : V) - (u : V)) = 0 := by simpa using eq_zero_of_mul_norm_nonpos hc h
  exact Subtype.ext (sub_eq_zero.mp hz)

/-- The remark after Theorem 8.2.4: for a *continuous* operator, closedness is automatic, and the
stability estimate together with dense range gives bijectivity. -/
theorem theorem_8_2_4_continuous [CompleteSpace V] [CompleteSpace W] (L : V →L[ℝ] W) {c : ℝ}
    (hc : 0 < c) (hstab : ∀ v, c * ‖v‖ ≤ ‖L v‖)
    (horth : (LinearMap.range (L : V →ₗ[ℝ] W))ᗮ = ⊥) : Function.Bijective L :=
  ContinuousLinearMap.bijective_of_le_norm_of_orthogonal_range_eq_bot L hc hstab horth

/-- The quantitative form of (8.2.2): the solution of `L u = f` obeys `‖u‖ ≤ ‖f‖ / c`. -/
theorem norm_le_of_stabilityEstimate [CompleteSpace V] [CompleteSpace W] (L : V →L[ℝ] W) {c : ℝ}
    (hc : 0 < c) (hstab : ∀ v, c * ‖v‖ ≤ ‖L v‖) {v : V} {w : W} (hv : L v = w) :
    ‖v‖ ≤ ‖w‖ / c :=
  ContinuousLinearMap.norm_le_of_le_norm L hc hstab hv

end Hilbert

section StronglyMonotone

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Example 8.2.5: a strongly monotone `L ∈ L(V, V')`, that is one with `⟨L v, v⟩ ≥ c ‖v‖²`,
satisfies the stability estimate (8.2.2) with the same constant `c`, has `R(L)^⊥ = {0}` in the
duality sense, and is therefore a bijection of `V` onto `V'`.

Over `ℝ` such an `L` *is* a bounded sesquilinear form, and the hypothesis is the backbone's
`SesqForm.IsCoerciveWith`, so the three conclusions are `IsCoerciveWith.norm_le_norm_apply`,
a one-line computation, and `SesqForm.laxMilgram`. -/
theorem example_8_2_5 (L : V →L[ℝ] StrongDual ℝ V) {c : ℝ} (hc : 0 < c)
    (hmono : ∀ v, c * ‖v‖ ^ 2 ≤ L v v) :
    (∀ v, c * ‖v‖ ≤ ‖L v‖) ∧ (∀ v, (∀ w, L w v = 0) → v = 0) ∧ Function.Bijective L := by
  have hcoer : SesqForm.IsCoerciveWith (𝕜 := ℝ) L c := hmono
  have hker : ∀ v : V, L v v ≤ 0 → v = 0 := by
    intro v hv
    have h1 : c * ‖v‖ ^ 2 ≤ 0 := (hmono v).trans hv
    have h2 : ‖v‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖v‖]
    exact norm_le_zero_iff.mp (by nlinarith [norm_nonneg v])
  refine ⟨fun v => SesqForm.IsCoerciveWith.norm_le_norm_apply L hcoer v,
    fun v hv => hker v (le_of_eq (hv v)), ?_, ?_⟩
  · intro u₁ u₂ h
    have hL0 : L (u₁ - u₂) = 0 := by rw [map_sub, h, sub_self]
    have hz : L (u₁ - u₂) (u₁ - u₂) = 0 := by rw [hL0]; rfl
    exact sub_eq_zero.mp (hker _ (le_of_eq hz))
  · intro ℓ
    obtain ⟨u, hu, -⟩ := SesqForm.laxMilgram L ℓ hc hcoer
    exact ⟨u, ContinuousLinearMap.ext hu⟩

end StronglyMonotone

section ClosedRange

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-- The Hilbert-space, bounded case of Theorem 8.2.7 (the closed range theorem): if `R(T)` is
closed then `R(T) = N(T*)^⊥`, so `T u = f` is solvable exactly when `f` is orthogonal to the
kernel of the adjoint.  The book's statement, for densely defined closed operators between
Banach spaces, is `theorem_8_2_7`. -/
theorem theorem_8_2_7_hilbert (T : V →L[ℝ] W)
    (hclosed : IsClosed (LinearMap.range (T : V →ₗ[ℝ] W) : Set W)) (f : W) :
    f ∈ LinearMap.range (T : V →ₗ[ℝ] W) ↔
      ∀ w, ContinuousLinearMap.adjoint T w = 0 → ⟪w, f⟫_ℝ = 0 := by
  have hrange : LinearMap.range (T : V →ₗ[ℝ] W)
      = (LinearMap.ker (ContinuousLinearMap.adjoint T : W →ₗ[ℝ] V))ᗮ := by
    rw [← ContinuousLinearMap.orthogonal_range T, Submodule.orthogonal_orthogonal_eq_closure,
      hclosed.submodule_topologicalClosure_eq]
  rw [hrange, Submodule.mem_orthogonal]
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]

end ClosedRange

section ClosedRangeBanach

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- **Theorem 8.2.7** (Banach's closed range theorem), in the book's generality: for Banach
spaces `V`, `W` and a densely defined closed linear operator `L : D(L) ⊂ V → W` with dual
operator `L* : D(L*) ⊂ W' → V'`, `⟨L* w*, v⟩ = ⟨w*, L v⟩`, the following are equivalent:
(a) `R(L)` is closed in `W`; (b) `R(L) = N(L*)^⊥ = {w ∈ W | ⟨w*, w⟩ = 0 ∀ w* ∈ N(L*)}`;
(c) `R(L*)` is closed in `V'`; (d) `R(L*) = N(L)^⊥ = {v* ∈ V' | ⟨v*, v⟩ = 0 ∀ v ∈ N(L)}`.

The dual operator is the backbone's Banach adjoint `LinearPMap.strongDualAdjoint`
(`Numlib/Analysis/Normed/Operator/Unbounded/Adjoint.lean`), and the theorem is
`LinearPMap.IsClosed.isClosed_range_tfae` of `Unbounded/ClosedRange.lean`, with the two
annihilators written out as the sets the book displays.  The abstract Fredholm alternative
the book draws from it, (a) ⇒ (b), is
`LinearPMap.range_eq_strongDualCoannihilator_ker_strongDualAdjoint_of_isClosed_range`.
The Hilbert-space bounded case is `theorem_8_2_7_hilbert`. -/
theorem theorem_8_2_7 (L : V →ₗ.[ℝ] W) (hd : Dense (L.domain : Set V)) (hc : L.IsClosed) :
    [IsClosed (LinearMap.range L.toFun : Set W),
      (LinearMap.range L.toFun : Set W) = {w | ∀ w' ∈ L.strongDualAdjoint.ker, w' w = 0},
      IsClosed (LinearMap.range L.strongDualAdjoint.toFun : Set (StrongDual ℝ V)),
      (LinearMap.range L.strongDualAdjoint.toFun : Set (StrongDual ℝ V))
        = {v' | ∀ v ∈ L.ker, v' v = 0}].TFAE := by
  have key := hc.isClosed_range_tfae hd
  have e2 : LinearMap.range L.toFun = L.strongDualAdjoint.ker.strongDualCoannihilator ↔
      (LinearMap.range L.toFun : Set W) = {w | ∀ w' ∈ L.strongDualAdjoint.ker, w' w = 0} := by
    rw [← SetLike.coe_set_eq]
    have : (L.strongDualAdjoint.ker.strongDualCoannihilator : Set W)
        = {w | ∀ w' ∈ L.strongDualAdjoint.ker, w' w = 0} := by
      ext w
      simp
    rw [this]
  have e4 : LinearMap.range L.strongDualAdjoint.toFun = L.ker.strongDualAnnihilator ↔
      (LinearMap.range L.strongDualAdjoint.toFun : Set (StrongDual ℝ V))
        = {v' | ∀ v ∈ L.ker, v' v = 0} := by
    rw [← SetLike.coe_set_eq]
    have : (L.ker.strongDualAnnihilator : Set (StrongDual ℝ V))
        = {v' | ∀ v ∈ L.ker, v' v = 0} := by
      ext v'
      simp
    rw [this]
  tfae_have 1 ↔ 2 := (key.out 1 3).trans e2
  tfae_have 1 ↔ 3 := key.out 1 2
  tfae_have 1 ↔ 4 := (key.out 1 4).trans e4
  tfae_finish

end ClosedRangeBanach

section Laplacian

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))

/-- The Dirichlet eigenfunctions `e_n` of `−Δ` on a bounded nonempty `Ω` (Brezis's Theorem 9.31,
`Elliptic.dirichletEigenbasis`) lie in the domain of the Dirichlet Laplacian, with
`(−Δ) e_n = λ_n e_n`: the weak eigenvalue equation `∫ ∇e_n · ∇φ = λ_n ∫ e_n φ` on `H¹₀(Ω)` is the
defining identity of the domain with the datum `λ_n e_n`. -/
theorem dirichletEigenbasis_mem_dirichletLaplacian_domain
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty) (n : ℕ) :
    ∃ h : Elliptic.dirichletEigenbasis Ω hΩ hne n ∈ (dirichletLaplacian Ω).domain,
      dirichletLaplacian Ω ⟨Elliptic.dirichletEigenbasis Ω hΩ hne n, h⟩
        = Elliptic.dirichletEigenvalue Ω hΩ n • Elliptic.dirichletEigenbasis Ω hΩ hne n := by
  obtain ⟨u, hu, hfn, heq⟩ := Elliptic.dirichletEigenbasis_mem_sobolevZero Ω hΩ hne n
  have key : ∀ φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, Elliptic.dirichletForm Ω u φ
      = Elliptic.load Ω (Elliptic.dirichletEigenvalue Ω hΩ n
        • Elliptic.dirichletEigenbasis Ω hΩ hne n) φ := fun φ hφ ↦ by
    rw [heq φ hφ, Elliptic.load_smul]
    rfl
  exact ⟨⟨u, hu, hfn, _, key⟩, dirichletLaplacian_apply_unique _ hu hfn key⟩

/-- **Example 8.2.3**: the differential operator `L v = −Δv` on `L²(Ω)`, for a bounded nonempty
open `Ω ⊆ ℝ^{d+1}`, is a closed operator that is not continuous — so the converse of the remark
after Definition 8.2.2 fails.

The operator is the backbone's Dirichlet Laplacian `dirichletLaplacian Ω`
(`Numlib/Analysis/PDE/DirichletLaplacian.lean`), the unbounded operator on `L²(Ω)` with domain
`{v ∈ H¹₀(Ω) : Δv ∈ L²(Ω)}` and `L v = −Δv` in the weak sense; the four clauses are:

* `L` is closed (Definition 8.2.2; `dirichletLaplacian_isClosed`, and `isClosed_iff_seq` turns it
  into the book's sequential phrasing);
* every `φ ∈ C₀^∞(Ω)` lies in `D(L)` with `L φ = −Δφ` computed classically
  (`testFunction_mem_dirichletLaplacianDomain`);
* the identity `∫_Ω (−Δv) φ = −∫_Ω v Δφ` for `v ∈ D(L)` and `φ ∈ C₀^∞(Ω)` that the book's proof
  of closedness passes to the limit in — here `⟪L v, φ⟫ = ⟪v, −Δφ⟫`, the symmetry of `L`
  (`dirichletLaplacian_isFormalAdjoint`);
* `L` is not continuous: no `C` has `‖L v‖ ≤ C ‖v‖` on `D(L)`.  The book gives no argument for
  this clause; here the Dirichlet eigenfunctions `e_n` of Brezis's Theorem 9.31
  (`Elliptic.dirichletEigenbasis`, unit vectors of `L²(Ω)` with `L e_n = λ_n e_n`) witness it,
  since `λ_n → +∞` (`Elliptic.tendsto_dirichletEigenvalue_atTop`).

The book's closedness argument — the limit passage in the distributional identity — is how the
backbone proves the weak derivative closed under `L^p` limits
(`hasWeakIteratedLineDerivOn_of_tendsto_eLpNorm`); the closedness of `dirichletLaplacian` itself
is proved there from its maximal monotonicity, which is the same fact in Hilbert-space dress. -/
theorem example_8_2_3 (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty) :
    (dirichletLaplacian Ω).IsClosed ∧
    (∀ φ : 𝓓(Ω, ℝ), ∃ h : φ.toL2 ∈ (dirichletLaplacian Ω).domain,
      dirichletLaplacian Ω ⟨φ.toL2, h⟩ = φ.negLaplacian.toL2) ∧
    (∀ (f : (dirichletLaplacian Ω).domain) (φ : 𝓓(Ω, ℝ)),
      ⟪dirichletLaplacian Ω f, φ.toL2⟫_ℝ
        = ⟪(f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))),
            φ.negLaplacian.toL2⟫_ℝ) ∧
    ¬ ∃ C : ℝ, ∀ f : (dirichletLaplacian Ω).domain,
      ‖dirichletLaplacian Ω f‖
        ≤ C * ‖(f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))‖ := by
  have hφ : ∀ φ : 𝓓(Ω, ℝ), ∃ h : φ.toL2 ∈ (dirichletLaplacian Ω).domain,
      dirichletLaplacian Ω ⟨φ.toL2, h⟩ = φ.negLaplacian.toL2 := fun φ ↦
    ⟨(testFunction_mem_dirichletLaplacianDomain φ).1,
      (testFunction_mem_dirichletLaplacianDomain φ).2⟩
  refine ⟨dirichletLaplacian_isClosed, hφ, fun f φ ↦ ?_, ?_⟩
  · obtain ⟨h, hh⟩ := hφ φ
    rw [← hh]
    exact dirichletLaplacian_isFormalAdjoint f ⟨φ.toL2, h⟩
  · rintro ⟨C, hC⟩
    obtain ⟨n, hn⟩ := (Elliptic.tendsto_dirichletEigenvalue_atTop Ω hΩ hne).eventually_gt_atTop C
      |>.exists
    obtain ⟨hmem, hApp⟩ := dirichletEigenbasis_mem_dirichletLaplacian_domain Ω hΩ hne n
    have h1 := hC ⟨Elliptic.dirichletEigenbasis Ω hΩ hne n, hmem⟩
    have hnorm : ‖Elliptic.dirichletEigenbasis Ω hΩ hne n‖ = 1 :=
      (Elliptic.dirichletEigenbasis Ω hΩ hne).orthonormal.1 n
    rw [hApp, norm_smul, Real.norm_eq_abs, Submodule.coe_mk, hnorm, mul_one, mul_one,
      abs_of_pos (Elliptic.dirichletEigenvalue_pos Ω hΩ hne n)] at h1
    exact absurd h1 (not_le.2 hn)

end Laplacian

section Model

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))

/-- **The operator `L : V → V'` of Example 8.2.6**, `⟨L u, v⟩ = ∫_Ω ∇u · ∇v` for
`u, v ∈ V = H¹₀(Ω)`: the restriction of the backbone's Dirichlet form
(`Elliptic.dirichletForm`, `Numlib/Analysis/PDE/Elliptic/Dirichlet.lean`) to `H¹₀(Ω)`, read as a
bounded linear map into the dual `V' = H^{-1}(Ω)`.

The spaces are the backbone's: `V` is `SobolevEuclideanZero (d + 1) 1 2 Ω`, the closure of
`C₀^∞(Ω)` in `H¹(Ω) = SobolevEuclidean (d + 1) 1 2 Ω` in the multi-index formulation of
Definition 7.2.2, and `V'` is its `StrongDual`.  The AH surface's own
`AtkinsonHan.Chapter07.definition_7_2_9 1 2 Ω` (`H¹₀(Ω)`) and `definition_7_2_12_hMinusOne`
(`H^{-1}(Ω)`) are the same closure and the same dual taken in the tensor formulation
`Sobolev ℝ 1 2 Ω volume`, whose norm is equivalent but not equal; the Poincaré inequality and
the Dirichlet form of the backbone are stated on the multi-index space, which is why the
example is stated there. -/
noncomputable def modelOperator : SobolevEuclideanZero (d + 1) 1 2 Ω →L[ℝ]
    StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 2 Ω) :=
  (Elliptic.dirichletForm Ω).restrict (SobolevEuclideanZero (d + 1) 1 2 Ω)

/-- `⟨L u, v⟩` is the Dirichlet form `∫_Ω ∇u · ∇v`. -/
theorem modelOperator_apply (u v : SobolevEuclideanZero (d + 1) 1 2 Ω) :
    modelOperator Ω u v = Elliptic.dirichletForm Ω u v :=
  rfl

/-- **Example 8.2.6**: the weak formulation of the model problem `−Δu = f` in `Ω`, `u = 0` on
`∂Ω` (8.2.3), on `V = H¹₀(Ω)` with the seminorm `‖v‖_V = |v|_{H¹(Ω)} = ‖∇v‖_{L²(Ω)}` as norm and
`V' = H^{-1}(Ω)`, for a bounded open `Ω ⊆ B(0, R) ⊆ ℝ^{d+1}`.  The operator
`L = modelOperator Ω`, `⟨L u, v⟩ = ∫_Ω ∇u · ∇v`, is linear and continuous with `‖L‖ = 1` and
strongly monotone with `⟨L v, v⟩ = ‖v‖_V²`, so by Example 8.2.5 it is a bijection of `V` onto
`V'`: for every `f ∈ H^{-1}(Ω)` there is exactly one `u ∈ H¹₀(Ω)` with
`∫_Ω ∇u · ∇v = ⟨f, v⟩` for all `v ∈ V`, the unique weak solution of (8.2.3).

The clauses, in order: the formula `⟨L u, v⟩ = ∫_Ω ∑ᵢ ∂ᵢu ∂ᵢv`; the bound
`|⟨L u, v⟩| ≤ ‖∇u‖₂ ‖∇v‖₂`, that is `‖L‖ ≤ 1` for the norm `‖·‖_V`, and the identity
`⟨L v, v⟩ = ‖∇v‖₂² = ‖v‖_V²`, which makes `‖L‖ = 1` exactly; the strong monotonicity
`⟨L v, v⟩ ≥ c ‖v‖²_{H¹}` with `c = (1 + (2R)²)⁻¹`, which is Poincaré's inequality
(`Elliptic.dirichletForm_restrict_isCoerciveWith`, from `SobolevEuclideanZero.norm_le_gradNorm`
of `Numlib/Analysis/Sobolev/Poincare.lean`) and is what makes the seminorm a norm on `V`
equivalent to the `H¹` norm; the bijectivity of `L` (Example 8.2.5); and the unique weak
solution for every `f ∈ V'`.

The book's "`‖L‖ = 1`" and "`⟨L v, v⟩ = ‖v‖_V²`" refer to the seminorm `|·|_{H¹}`, which the
type `SobolevEuclideanZero (d + 1) 1 2 Ω` does not carry as its norm (its norm is the `H¹` norm);
they are therefore stated through `SobolevMultiIndex.gradNorm`, and the strong monotonicity in
the `H¹` norm carries the constant of Poincaré's inequality.  The book asks for a Lipschitz
boundary, which no clause needs. -/
theorem example_8_2_6 {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R) :
    (∀ u v : SobolevEuclideanZero (d + 1) 1 2 Ω,
      modelOperator Ω u v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        ∑ i, SobolevMultiIndex.weakDeriv (u : SobolevEuclidean (d + 1) 1 2 Ω)
          (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 2 Ω)
            (MultiIndexLE.single i) x) ∧
    (∀ u v : SobolevEuclideanZero (d + 1) 1 2 Ω,
      |modelOperator Ω u v| ≤ SobolevMultiIndex.gradNorm (u : SobolevEuclidean (d + 1) 1 2 Ω)
        * SobolevMultiIndex.gradNorm (v : SobolevEuclidean (d + 1) 1 2 Ω)) ∧
    (∀ v : SobolevEuclideanZero (d + 1) 1 2 Ω,
      modelOperator Ω v v = SobolevMultiIndex.gradNorm (v : SobolevEuclidean (d + 1) 1 2 Ω) ^ 2) ∧
    (∀ v : SobolevEuclideanZero (d + 1) 1 2 Ω,
      (1 + (2 * R) ^ 2)⁻¹ * ‖v‖ ^ 2 ≤ modelOperator Ω v v) ∧
    Function.Bijective (modelOperator Ω) ∧
    ∀ f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 2 Ω),
      ∃! u : SobolevEuclideanZero (d + 1) 1 2 Ω, ∀ v, modelOperator Ω u v = f v := by
  have hcoer := Elliptic.dirichletForm_restrict_isCoerciveWith Ω hR hΩ
  have hpos : (0 : ℝ) < (1 + (2 * R) ^ 2)⁻¹ := by positivity
  exact ⟨fun u v ↦ Elliptic.dirichletForm_apply Ω u v,
    fun u v ↦ Elliptic.abs_dirichletForm_le Ω u v,
    fun v ↦ Elliptic.dirichletForm_self_eq_gradNorm_sq Ω v, fun v ↦ hcoer v,
    (example_8_2_5 (modelOperator Ω) hpos hcoer).2.2,
    fun f ↦ SesqForm.laxMilgram (modelOperator Ω) f hpos hcoer⟩

end Model

section FiniteDimensional

/-- Exercise 8.2.1: for a linear system `A x = b` on `ℝ^d`, solvability for every right-hand side
`b` and uniqueness of the solution are equivalent.

The exercise asks for this to be read off Theorem 8.2.1, and that is how it is proved here: over
`ℝ^d = EuclideanSpace ℝ (Fin d)` the range of `A` is a finite-dimensional subspace, hence closed,
and injectivity leaves it no room for a nonzero orthogonal vector, so `R(A)^⊥ = {0}` and Theorem
8.2.1 gives `R(A) = ℝ^d`.  The converse direction is the rank-nullity theorem. -/
theorem exercise_8_2_1 {d : ℕ} (f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Function.Injective f ↔ Function.Surjective f := by
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  have hrange : LinearMap.range (f.toPMap ⊤).toFun = LinearMap.range f := by
    simp [LinearMap.toPMap, LinearMap.range_comp]
  constructor
  · intro hinj
    have hker : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr hinj
    rw [hker, finrank_bot, add_zero] at hrank
    have horth : (LinearMap.range f)ᗮ = ⊥ :=
      Submodule.finrank_eq_zero.mp
        (Submodule.finrank_add_finrank_orthogonal' (by simpa using hrank))
    have hclosed : IsClosed (LinearMap.range (f.toPMap ⊤).toFun :
        Set (EuclideanSpace ℝ (Fin d))) := by
      rw [hrange]
      exact (LinearMap.range f).closed_of_finiteDimensional
    have htop := (theorem_8_2_1 (f.toPMap ⊤)).mpr ⟨hclosed, by rw [hrange]; exact horth⟩
    rw [hrange] at htop
    exact LinearMap.range_eq_top.mp htop
  · intro hsurj
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hrank
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp (by omega))

/-- Exercise 8.2.1, the sufficient condition it asks Theorem 8.2.8 to supply: if `A` obeys the
stability estimate `c ‖x‖ ≤ ‖A x‖` with `c > 0`, then Theorem 8.2.8 (a) makes the solution of
`A x = b` unique, and by the equivalence above `A x = b` is then uniquely solvable for every
`b ∈ ℝ^d`. -/
theorem exercise_8_2_1_stability {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) {c : ℝ} (hc : 0 < c)
    (hstab : ∀ v, c * ‖v‖ ≤ ‖f v‖) (b : EuclideanSpace ℝ (Fin d)) : ∃! x, f x = b := by
  have hinj : Function.Injective f := fun u v huv =>
    theorem_8_2_8a (D := Set.univ) f hc
      (fun u _ v _ => by rw [← map_sub]; exact hstab (u - v)) (Set.mem_univ u) (Set.mem_univ v)
      rfl huv.symm
  obtain ⟨x, hx⟩ := (exercise_8_2_1 f).mp hinj b
  exact ⟨x, hx, fun y hy => hinj (hy.trans hx.symm)⟩

end FiniteDimensional

end AtkinsonHan.Chapter08
