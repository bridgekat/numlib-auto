import Numlib.Analysis.Convex.Polyhedral.Function
import Numlib.Analysis.Convex.Duality.Conjugate

/-!
# Conjugates of polyhedral convex functions

The conjugate of a polyhedral convex function is polyhedral.

The proof uses the Minkowski–Weyl dictionary once in each direction. Write `epi f = conv P + cone D`
with `P` and `D` finite. An affine function `x ↦ ⟨x, y⟩ - c` lies below
`f` exactly when the linear functional `p ↦ ⟨p.1, y⟩ - p.2` is bounded by `c` on `epi f`, and on a
sum of a convex hull and a cone that is two *finite* families of conditions: `⟨p.1, y⟩ - c ≤ p.2`
for the generating points `p ∈ P`, and `⟨d.1, y⟩ ≤ d.2` for the generating directions `d ∈ D`.
Both are linear in `(y, c)`, so they cut `epi (convexConj B f)` out of `F × ℝ` as a polyhedral set.

## Main results

* `mem_epi_convexConj_iff` — the epigraph of `convexConj B f`, read off `epi f`, with no hypothesis
  on `f`. In particular none excluding `f x = ⊥`: in that case both sides are false.
* `PolyhedralFn.convexConj` — the conjugate of a polyhedral convex function is polyhedral
  ([rockafellar1970convex] Theorem 19.2). The case `P = ∅` is separate: then `f ≡ ⊤` and
  `epi (convexConj B f)` is all of `F × ℝ`, whereas the generator argument needs a base point to
  slide along a recession direction.

## References

* [rockafellar1970convex] §19.
-/

open Set
open scoped Pointwise

namespace ConvexAnalysis

section Functionals

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The linear functional `(y, c) ↦ ⟨x, y⟩ - c` on `F × ℝ`, one for each generating *point* `x`
of `epi f`. -/
def epiFunctional (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (x : E) : (F × ℝ) →ₗ[ℝ] ℝ :=
  (B x).comp (LinearMap.fst ℝ F ℝ) - LinearMap.snd ℝ F ℝ

@[simp] theorem epiFunctional_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (x : E) (q : F × ℝ) :
    epiFunctional B x q = B x q.1 - q.2 := by
  simp [epiFunctional]

/-- The linear functional `(y, c) ↦ ⟨x, y⟩` on `F × ℝ`, one for each generating *direction* `x`
of `epi f`. -/
def dirFunctional (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (x : E) : (F × ℝ) →ₗ[ℝ] ℝ :=
  (B x).comp (LinearMap.fst ℝ F ℝ)

@[simp] theorem dirFunctional_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (x : E) (q : F × ℝ) :
    dirFunctional B x q = B x q.1 := by
  simp [dirFunctional]

/-- The linear functional `p ↦ ⟨p.1, y⟩ - p.2` on `E × ℝ`, whose boundedness on `epi f` is what
the conjugate measures. -/
def recFunctional (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (y : F) : (E × ℝ) →ₗ[ℝ] ℝ :=
  (B.flip y).comp (LinearMap.fst ℝ E ℝ) - LinearMap.snd ℝ E ℝ

@[simp] theorem recFunctional_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (y : F) (p : E × ℝ) :
    recFunctional B y p = B p.1 y - p.2 := by
  simp [recFunctional]

end Functionals

section Conj

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- **The epigraph of a conjugate.** `(y, c)` lies over `convexConj B f` exactly when the linear
functional `p ↦ ⟨p.1, y⟩ - p.2` is bounded by `c` on `epi f`. This is `convexConj_le_coe_iff` with
the affine minorant traded for its epigraph, and it holds with no hypothesis on `f`. -/
theorem mem_epi_convexConj_iff {q : F × ℝ} :
    q ∈ epi (convexConj B f) ↔ ∀ p ∈ epi f, B p.1 q.1 - q.2 ≤ p.2 := by
  rw [mem_epi, convexConj_le_coe_iff]
  constructor
  · intro h p hp
    have h₁ : ((B p.1 q.1 - q.2 : ℝ) : EReal) ≤ f p.1 := by
      rw [← affineFn_eq_coe]; exact h p.1
    have h₂ : ((B p.1 q.1 - q.2 : ℝ) : EReal) ≤ ((p.2 : ℝ) : EReal) := h₁.trans hp
    exact_mod_cast h₂
  · intro h x
    rw [affineFn_eq_coe]
    by_contra hcon
    obtain ⟨μ, hμ₁, hμ₂⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hcon)
    have hmem : (x, μ) ∈ epi f := le_of_lt hμ₁
    have hle := h (x, μ) hmem
    exact absurd (by exact_mod_cast hμ₂ : μ < B x q.1 - q.2) (not_lt.2 hle)

variable [FiniteDimensional ℝ E]

/-- The conjugate of a polyhedral convex function is polyhedral.

`epi f = conv P + cone D` turns the condition "`x ↦ ⟨x, y⟩ - c` lies below `f`" into finitely
many linear inequalities on `(y, c)`: one per generating point, one per generating direction. -/
theorem PolyhedralFn.convexConj (hf : PolyhedralFn f) : PolyhedralFn (convexConj B f) := by
  classical
  obtain ⟨P, D, hPD⟩ := Polyhedral.finitelyGenerated hf
  rcases P.eq_empty_or_nonempty with rfl | hPne
  · -- `epi f = ∅`, so `f ≡ ⊤` and every `(y, c)` lies over the conjugate: the empty system
    have hempty : epi f = (∅ : Set (E × ℝ)) := by
      rw [hPD, Finset.coe_empty, convexHull_empty, Set.empty_add]
    refine ⟨∅, ?_⟩
    ext q
    constructor
    · intro _ r hr
      simp at hr
    · intro _
      rw [mem_epi_convexConj_iff, hempty]
      intro p hp
      exact hp.elim
  · refine ⟨P.image (fun p => (epiFunctional B p.1, p.2)) ∪
      D.image (fun d => (dirFunctional B d.1, d.2)), ?_⟩
    ext q
    rw [mem_epi_convexConj_iff, hPD]
    constructor
    · intro h r hr
      rcases Finset.mem_union.1 hr with hr | hr
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hr
        change epiFunctional B p.1 q ≤ p.2
        rw [epiFunctional_apply]
        have hmem : p ∈ convexHull ℝ (P : Set (E × ℝ)) +
            (PointedCone.hull ℝ (D : Set (E × ℝ)) : Set (E × ℝ)) := by
          have h₀ := Set.add_mem_add (subset_convexHull ℝ (P : Set (E × ℝ)) (Finset.mem_coe.2 hp))
            (PointedCone.hull ℝ (D : Set (E × ℝ))).zero_mem
          rwa [add_zero] at h₀
        exact h p hmem
      · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hr
        change dirFunctional B d.1 q ≤ d.2
        rw [dirFunctional_apply]
        by_contra hcon
        have hlam : 0 < B d.1 q.1 - d.2 := by linarith [not_le.1 hcon]
        obtain ⟨p₀, hp₀⟩ := hPne
        set A : ℝ := B p₀.1 q.1 - q.2 - p₀.2 with hA
        set t : ℝ := (|A| + 1) / (B d.1 q.1 - d.2) with ht
        have ht0 : 0 ≤ t := le_of_lt (div_pos (by positivity) hlam)
        have hmem : p₀ + t • d ∈ convexHull ℝ (P : Set (E × ℝ)) +
            (PointedCone.hull ℝ (D : Set (E × ℝ)) : Set (E × ℝ)) :=
          Set.add_mem_add (subset_convexHull ℝ (P : Set (E × ℝ)) (Finset.mem_coe.2 hp₀))
            (Submodule.smul_mem (PointedCone.hull ℝ (D : Set (E × ℝ)))
              (⟨t, ht0⟩ : {c : ℝ // 0 ≤ c}) (PointedCone.subset_hull (Finset.mem_coe.2 hd)))
        have hkey := h _ hmem
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, map_add, map_smul,
          LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hkey
        have hcancel : t * (B d.1 q.1 - d.2) = |A| + 1 := by
          rw [ht, div_mul_cancel₀ _ (ne_of_gt hlam)]
        have hexp : t * (B d.1 q.1 - d.2) = t * B d.1 q.1 - t * d.2 := by ring
        have habs : -A ≤ |A| := neg_le_abs A
        rw [hA] at habs
        linarith
    · intro h p hp
      obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_add.1 hp
      have hsubP : (P : Set (E × ℝ)) ⊆ {x : E × ℝ | recFunctional B q.1 x ≤ q.2} := by
        intro x hx
        have hx' := h (epiFunctional B x.1, x.2)
          (Finset.mem_union_left _ (Finset.mem_image.2 ⟨x, Finset.mem_coe.1 hx, rfl⟩))
        have hx'' : B x.1 q.1 - q.2 ≤ x.2 := by
          have hx₀ : epiFunctional B x.1 q ≤ x.2 := hx'
          rwa [epiFunctional_apply] at hx₀
        have hgoal : recFunctional B q.1 x ≤ q.2 := by rw [recFunctional_apply]; linarith
        exact hgoal
      have hu' : recFunctional B q.1 u ≤ q.2 :=
        convexHull_min hsubP
          (convex_halfSpace_le (LinearMap.isLinear (recFunctional B q.1)) q.2) hu
      have hv' : recFunctional B q.1 v ≤ 0 := by
        refine forall_nonpos_of_mem_hull (fun m hm => ?_) hv
        have hm' := h (dirFunctional B m.1, m.2)
          (Finset.mem_union_right _ (Finset.mem_image.2 ⟨m, Finset.mem_coe.1 hm, rfl⟩))
        have hm'' : B m.1 q.1 ≤ m.2 := by
          have hm₀ : dirFunctional B m.1 q ≤ m.2 := hm'
          rwa [dirFunctional_apply] at hm₀
        rw [recFunctional_apply]
        linarith
      have hsum : recFunctional B q.1 (u + v) ≤ q.2 := by
        rw [map_add]; linarith
      rw [recFunctional_apply] at hsum
      linarith

end Conj

end ConvexAnalysis
