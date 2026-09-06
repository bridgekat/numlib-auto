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

Theorem 8.2.7 is out of scope in the Banach generality of the book (Mathlib has no continuous
Banach dual of an unbounded densely defined operator); its Hilbert-space bounded case is recorded
as `theorem_8_2_7_hilbert`.

Exercise 8.2.1 closes the file with the finite-dimensional instance the book asks for: on
`ℝ^d = EuclideanSpace ℝ (Fin d)` every range is closed, so Theorem 8.2.1 alone turns uniqueness of
a solution of `A x = b` into existence for every `b`.
-/

open Filter Topology
open scoped InnerProductSpace

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
closedness of the graph, which on a metric space is the same thing. -/
theorem isClosed_iff_seq (T : V →ₗ.[ℝ] W) :
    T.IsClosed ↔ ∀ (v : ℕ → T.domain) (x : V) (w : W),
      Tendsto (fun n => (v n : V)) atTop (𝓝 x) → Tendsto (fun n => T (v n)) atTop (𝓝 w) →
        ∃ hx : x ∈ T.domain, T ⟨x, hx⟩ = w := by
  rw [LinearPMap.IsClosed, ← isSeqClosed_iff_isClosed]
  constructor
  · intro h v x w hv hw
    have hmem : ∀ n, ((v n : V), T (v n)) ∈ (T.graph : Set (V × W)) := fun n => T.mem_graph (v n)
    have hg := h hmem (hv.prodMk_nhds hw)
    rw [SetLike.mem_coe, LinearPMap.mem_graph_iff] at hg
    obtain ⟨y, hy1, hy2⟩ := hg
    have hy1' : (y : V) = x := hy1
    have hx : x ∈ T.domain := hy1' ▸ y.2
    refine ⟨hx, ?_⟩
    have hxy : (⟨x, hx⟩ : T.domain) = y := Subtype.ext hy1'.symm
    rw [hxy]
    exact hy2
  · intro h p q hp hq
    choose y hy1 hy2 using fun n => (LinearPMap.mem_graph_iff T).mp (hp n)
    have h1 : Tendsto (fun n => ((y n : V))) atTop (𝓝 q.1) := by
      simpa [hy1, Function.comp_def] using (continuous_fst.tendsto q).comp hq
    have h2 : Tendsto (fun n => T (y n)) atTop (𝓝 q.2) := by
      simpa [hy2, Function.comp_def] using (continuous_snd.tendsto q).comp hq
    obtain ⟨hx, hxv⟩ := h y q.1 q.2 h1 h2
    rw [SetLike.mem_coe, LinearPMap.mem_graph_iff]
    exact ⟨⟨q.1, hx⟩, rfl, hxv⟩

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
kernel of the adjoint.  The book states the theorem for densely defined closed operators between
Banach spaces, which is out of scope here (Mathlib has no continuous Banach dual for unbounded
operators). -/
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
