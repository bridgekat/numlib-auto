import Numlib

/-!
# General existence and uniqueness for operator equations (§8.2)

Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009.

The section proves that a linear operator `L : D(L) ⊂ V → W` which is closed (Definition 8.2.2)
and satisfies the a priori stability estimate (8.2.2) `‖L v‖ ≥ c ‖v‖` has closed range, so that
`L u = f` is uniquely solvable as soon as `R(L)^⊥ = {0}` (Theorems 8.2.1 and 8.2.4).  Partial
operators are `LinearPMap` (`V →ₗ.[ℝ] W`), whose `domain` is the book's `D(L)`; the book's
closedness is Mathlib's `LinearPMap.IsClosed` (`isClosed_iff_seq` records the equivalence with the
book's sequential phrasing) and the stability estimate is used unbundled, exactly as the backbone
states it.

Theorem 8.2.7 is out of scope in the Banach generality of the book (Mathlib has no continuous
Banach dual of an unbounded densely defined operator); its Hilbert-space bounded case is recorded
as `thm_8_2_7_hilbert`.
-/

open Filter Topology
open scoped InnerProductSpace

namespace AtkinsonHan.Ch08

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
theorem thm_8_2_8a_linear (L : V →L[ℝ] W) {c : ℝ} :
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
theorem thm_8_2_8a {D : Set V} (T : V → W) {c : ℝ} (hc : 0 < c)
    (hstab : ∀ u ∈ D, ∀ v ∈ D, c * ‖u - v‖ ≤ ‖T u - T v‖) (w : W) :
    ∀ u₁ ∈ D, ∀ u₂ ∈ D, T u₁ = w → T u₂ = w → u₁ = u₂ := by
  intro u₁ h₁ u₂ h₂ hw₁ hw₂
  have h := hstab u₁ h₁ u₂ h₂
  rw [hw₁, hw₂, sub_self, norm_zero] at h
  have hz : ‖u₁ - u₂‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (u₁ - u₂)]) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Theorem 8.2.8 (b): if `‖(T u − u) − (T v − v)‖ < ‖u − v‖` for distinct `u, v ∈ D(T)`, the
equation `T u = w` has at most one solution in `D(T)`. -/
theorem thm_8_2_8b {D : Set V} (T : V → V)
    (hstab : ∀ u ∈ D, ∀ v ∈ D, u ≠ v → ‖(T u - u) - (T v - v)‖ < ‖u - v‖) (w : V) :
    ∀ u₁ ∈ D, ∀ u₂ ∈ D, T u₁ = w → T u₂ = w → u₁ = u₂ := by
  intro u₁ h₁ u₂ h₂ hw₁ hw₂
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
theorem thm_8_2_1 [CompleteSpace W] (L : V →ₗ.[ℝ] W) :
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
theorem thm_8_2_4 [CompleteSpace V] [CompleteSpace W] (L : V →ₗ.[ℝ] W) (hL : L.IsClosed) {c : ℝ}
    (hc : 0 < c) (hstab : ∀ v : L.domain, c * ‖(v : V)‖ ≤ ‖L v‖)
    (horth : (LinearMap.range L.toFun)ᗮ = ⊥) (f : W) : ∃! u : L.domain, L u = f := by
  have hclosed := LinearPMap.isClosed_range_of_isClosed_of_le_norm L hL hc hstab
  have htop : LinearMap.range L.toFun = ⊤ := (thm_8_2_1 L).mpr ⟨hclosed, horth⟩
  have hmem : f ∈ LinearMap.range L.toFun := htop ▸ Submodule.mem_top
  obtain ⟨u, hu⟩ := hmem
  refine ⟨u, hu, fun y hy => ?_⟩
  have hy' : L.toFun y = f := hy
  have hd : L.toFun (y - u) = 0 := by rw [map_sub, hy', hu, sub_self]
  have h : c * ‖((y - u : L.domain) : V)‖ ≤ ‖L.toFun (y - u)‖ := hstab (y - u)
  rw [hd, norm_zero] at h
  have hz : ‖((y : V) - (u : V))‖ = 0 := by
    have : ‖((y - u : L.domain) : V)‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg ((y - u : L.domain) : V)]) (norm_nonneg _)
    simpa using this
  exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp hz))

/-- The remark after Theorem 8.2.4: for a *continuous* operator, closedness is automatic, and the
stability estimate together with dense range gives bijectivity. -/
theorem thm_8_2_4_continuous [CompleteSpace V] [CompleteSpace W] (L : V →L[ℝ] W) {c : ℝ}
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

/-- Exercise 8.2.5: a strongly monotone `L ∈ L(V, V')`, that is one with `⟨L v, v⟩ ≥ c ‖v‖²`,
satisfies the stability estimate (8.2.2) with the same constant `c`, has `R(L)^⊥ = {0}` in the
duality sense, and is therefore a bijection of `V` onto `V'`.

Over `ℝ` such an `L` *is* a bounded sesquilinear form, and the hypothesis is the backbone's
`SesqForm.IsCoerciveWith`, so the three conclusions are `IsCoerciveWith.norm_le_norm_apply`,
a one-line computation, and `SesqForm.laxMilgram`. -/
theorem ex_8_2_5 (L : V →L[ℝ] StrongDual ℝ V) {c : ℝ} (hc : 0 < c)
    (hmono : ∀ v, c * ‖v‖ ^ 2 ≤ L v v) :
    (∀ v, c * ‖v‖ ≤ ‖L v‖) ∧ (∀ v, (∀ w, L w v = 0) → v = 0) ∧ Function.Bijective L := by
  have hcoer : SesqForm.IsCoerciveWith (𝕜 := ℝ) L c := hmono
  have hker : ∀ v : V, L v v ≤ 0 → v = 0 := by
    intro v hv
    have h1 : c * ‖v‖ ^ 2 ≤ 0 := (hmono v).trans hv
    have h2 : ‖v‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖v‖]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h2 (sq_nonneg _)))
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
theorem thm_8_2_7_hilbert (T : V →L[ℝ] W)
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

end AtkinsonHan.Ch08
