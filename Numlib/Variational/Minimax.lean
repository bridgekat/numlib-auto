/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Topology.Sion` (the weak-topology transfer of Sion's theorem) and
`Mathlib.Analysis.Convex.Saddle` for the coercive existence theorems.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Topology.Sion
import Numlib.Analysis.Normed.Module.Reflexive.Kakutani
import Numlib.Variational.WeakMinimization

/-!
# Saddle points of convex–concave functions on reflexive spaces

Sion's minimax theorem — Mathlib's `Sion.exists_isSaddlePointOn`, by Komiya's elementary proof —
produces a saddle point of `f : E → F → ℝ` on `X × Y` when `X` and `Y` are *compact* convex
subsets of topological vector spaces, `f (·, y)` is lower semicontinuous and quasiconvex on `X` and
`f (x, ·)` is upper semicontinuous and quasiconcave on `Y`. In an infinite-dimensional normed
space a closed bounded convex set is never norm-compact, but in a *reflexive* space it is compact
for the weak topology (Kakutani's theorem,
`Convex.isCompact_image_toWeakSpace_of_isBounded_of_isClosed`), and a lower semicontinuous
function with convex sublevel sets is weakly lower semicontinuous (Mazur's theorem,
`Convex.isClosed_image_toWeakSpace_iff`). So Sion's theorem applies in the weak topologies of the
two spaces, and yields the existence theorem of Ekeland and Temam for saddle points of a
convex–concave function on bounded closed convex subsets of reflexive spaces
(`exists_isSaddlePointOn_of_isBounded`).

Boundedness is then traded for coercivity by truncation: a saddle point of the problem cut down
to a large closed ball whose components lie strictly inside the ball is a saddle point of the
original problem (`IsSaddlePointOn.of_inter_closedBall_left`, `…_right`, an argument along the
segment from the saddle point to a far point), and a coercivity condition keeps the components
of the truncated saddle points inside a fixed ball
(`exists_isSaddlePointOn_of_isCoerciveFunctionalOn`).
The two one-sided variants in which coercivity is asked of `sup_{q ∈ B} L (v, q)` or of
`inf_{v ∈ A} L (v, q)` instead of a single slice are `exists_isSaddlePointOn_of_sup_coercive` and
`exists_isSaddlePointOn_of_inf_coercive`. Asking both at once is **not** enough: `L (v, q) = q - v`
on `ℝ × ℝ` satisfies both (each `sup` is `+∞`, each `inf` is `-∞`) and has no saddle point.

A saddle point is Mathlib's `IsSaddlePointOn X Y f a b`, that is `f a y ≤ f x b` for all `x ∈ X`
and `y ∈ Y`: the first variable is minimized and the second maximized, the convention of
Ekeland–Temam and of Atkinson–Han; Rockafellar's opposite convention is
`ConvexAnalysis.IsSaddlePointOn` of `Numlib.Analysis.Convex.Saddle.Minimax`, for the transposed
kernel. `isSaddlePointOn_swap_neg_iff` exchanges the two variables.

## Main statements

* `exists_isSaddlePointOn_of_isBounded` — **Sion's theorem in a reflexive space**: on bounded
  closed convex sets, a function lower semicontinuous and quasiconvex in its first variable, upper
  semicontinuous and quasiconcave in its second, has a saddle point.
* `IsSaddlePointOn.of_inter_closedBall_left`, `IsSaddlePointOn.of_inter_closedBall_right` — the
  truncation lemmas.
* `exists_isSaddlePointOn_of_isCoerciveFunctionalOn` — **existence of a saddle point under
  coercivity**: closed convex sets, convex lower semicontinuous / concave upper semicontinuous
  slices, some slice `L (·, q₀)` coercive on `A` and some slice `-L (v₀, ·)` coercive on `B`.
  Bounded sets satisfy the coercivity conditions vacuously (`IsCoerciveFunctionalOn.of_isBounded`),
  so this covers the four combinations "bounded or coercive" of the classical statement.
* `exists_isSaddlePointOn_of_sup_coercive`, `exists_isSaddlePointOn_of_inf_coercive` — the
  variants with `sup_{q ∈ B} L (v, q) → ∞` as `‖v‖ → ∞`, respectively `inf_{v ∈ A} L (v, q) → -∞`
  as `‖q‖ → ∞`, the other side keeping its pointwise condition.
* `IsSaddlePointOn.fst_eq_of_strictConvexOn`, `IsSaddlePointOn.snd_eq_of_strictConcaveOn` — the
  first component of a saddle point is unique when `L (·, p)` is strictly convex, the second when
  `L (u, ·)` is strictly concave.

## Implementation notes

The weak topology is Mathlib's `WeakSpace ℝ E`, and a subset of `E` is read there as its image
under the linear equivalence `toWeakSpace ℝ E`, never through the definitional equality
`WeakSpace ℝ E = E`. The bounded theorem is stated with quasiconvexity, as Sion's theorem is; the
coercive theorems need convexity proper, because the truncation lemma does (a quasiconvex
function can have a local minimum in a ball that is not a minimum outside it).

Reflexivity is `NormedSpace.IsReflexive ℝ V`; the sequential class `WeaklySeqCompactSpace` of
`Numlib.Variational.WeakMinimization` is derived from it by instance search where
`exists_isMinOn_of_convexOn` and `exists_isMaxOn_of_concaveOn` are used. The transfer of
semicontinuity and quasiconvexity on a closed set to the weak topology is
`LowerSemicontinuousOn.comp_toWeakSpace_symm_of_quasiconvexOn` and its concave twin
(`Numlib.Analysis.Normed.Module.WeakClosed`).

## References

* [ekeland1999convex] Chapter VI, Propositions 1.2 and 2.1–2.3.
* [sion1958general]; [komiya1988elementary].
* [han2009theoretical] Theorem 8.6.3.
-/

open Bornology Filter Metric Set Topology

/-! ### Saddle points, transposed -/

section Swap

variable {E F β : Type*} [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  {X : Set E} {Y : Set F} {f : E → F → β} {a : E} {b : F}

/-- Exchanging the two variables and negating the function exchanges the minimized and the
maximized variable: `(b, a)` is a saddle point of `(y, x) ↦ -f x y` on `Y × X` iff `(a, b)` is a
saddle point of `f` on `X × Y`. -/
theorem isSaddlePointOn_swap_neg_iff :
    IsSaddlePointOn Y X (fun y x => -f x y) b a ↔ IsSaddlePointOn X Y f a b := by
  constructor
  · intro h x hx y hy
    exact neg_le_neg_iff.1 (h y hy x hx)
  · intro h y hy x hx
    exact neg_le_neg_iff.2 (h x hx y hy)

end Swap

/-! ### Sion's theorem in a reflexive space -/

section Bounded

variable {V Q : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace.IsReflexive ℝ V]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedSpace.IsReflexive ℝ Q]
  {A : Set V} {B : Set Q} {L : V → Q → ℝ}

/-- **Sion's minimax theorem in reflexive spaces** ([ekeland1999convex] Chapter VI,
Proposition 2.1). Let `A ⊆ V` and `B ⊆ Q` be nonempty bounded
closed convex subsets of reflexive real normed spaces, and let `L : V → Q → ℝ` be lower
semicontinuous and quasiconvex in its first variable on `A` for every `q ∈ B`, upper semicontinuous
and quasiconcave in its second variable on `B` for every `v ∈ A`. Then `L` has a saddle point
`(u, p) ∈ A × B`: `L u q ≤ L v p` for all `v ∈ A`, `q ∈ B`.

`A` and `B` are weakly compact by Kakutani's theorem, the semicontinuity hypotheses transfer to the
weak topologies by Mazur's theorem, and Sion's theorem applies in the topological vector spaces
`WeakSpace ℝ V` and `WeakSpace ℝ Q`. -/
theorem exists_isSaddlePointOn_of_isBounded (hAne : A.Nonempty) (hAcl : IsClosed A)
    (hAconv : Convex ℝ A) (hAbd : IsBounded A) (hBne : B.Nonempty) (hBcl : IsClosed B)
    (hBconv : Convex ℝ B) (hBbd : IsBounded B)
    (hLv : ∀ q ∈ B, QuasiconvexOn ℝ A fun v => L v q)
    (hLv' : ∀ q ∈ B, LowerSemicontinuousOn (fun v => L v q) A)
    (hLq : ∀ v ∈ A, QuasiconcaveOn ℝ B (L v)) (hLq' : ∀ v ∈ A, UpperSemicontinuousOn (L v) B) :
    ∃ u ∈ A, ∃ p ∈ B, IsSaddlePointOn A B L u p := by
  set f : WeakSpace ℝ V → WeakSpace ℝ Q → ℝ :=
    fun x y => L ((toWeakSpace ℝ V).symm x) ((toWeakSpace ℝ Q).symm y) with hf
  have hXc : IsCompact (toWeakSpace ℝ V '' A) :=
    hAconv.isCompact_image_toWeakSpace_of_isBounded_of_isClosed hAbd hAcl
  have hYc : IsCompact (toWeakSpace ℝ Q '' B) :=
    hBconv.isCompact_image_toWeakSpace_of_isBounded_of_isClosed hBbd hBcl
  have hfy : ∀ y ∈ toWeakSpace ℝ Q '' B,
      LowerSemicontinuousOn (fun x => f x y) (toWeakSpace ℝ V '' A) := by
    rintro _ ⟨q, hq, rfl⟩
    have := (hLv' q hq).comp_toWeakSpace_symm_of_quasiconvexOn hAcl (hLv q hq)
    simpa [hf, Function.comp_def] using this
  have hfy' : ∀ y ∈ toWeakSpace ℝ Q '' B,
      QuasiconvexOn ℝ (toWeakSpace ℝ V '' A) fun x => f x y := by
    rintro _ ⟨q, hq, rfl⟩
    have := (hLv q hq).comp_toWeakSpace_symm
    simpa [hf, Function.comp_def] using this
  have hfx : ∀ x ∈ toWeakSpace ℝ V '' A,
      UpperSemicontinuousOn (fun y => f x y) (toWeakSpace ℝ Q '' B) := by
    rintro _ ⟨v, hv, rfl⟩
    have := (hLq' v hv).comp_toWeakSpace_symm_of_quasiconcaveOn hBcl (hLq v hv)
    simpa [hf, Function.comp_def] using this
  have hfx' : ∀ x ∈ toWeakSpace ℝ V '' A,
      QuasiconcaveOn ℝ (toWeakSpace ℝ Q '' B) fun y => f x y := by
    rintro _ ⟨v, hv, rfl⟩
    have := (hLq v hv).comp_toWeakSpace_symm
    simpa [hf, Function.comp_def] using this
  obtain ⟨_, ⟨u, hu, rfl⟩, _, ⟨p, hp, rfl⟩, h⟩ :=
    Sion.exists_isSaddlePointOn (hAne.image _) hAconv.image_toWeakSpace hXc hfy hfy'
      hBconv.image_toWeakSpace (hBne.image _) hYc hfx hfx'
  refine ⟨u, hu, p, hp, fun v hv q hq => ?_⟩
  have := h (toWeakSpace ℝ V v) ⟨v, hv, rfl⟩ (toWeakSpace ℝ Q q) ⟨q, hq, rfl⟩
  simpa [hf] using this

end Bounded

/-! ### Truncation to a ball -/

section Truncation

variable {V Q : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Q]
  [NormedSpace ℝ Q] {A : Set V} {B : Set Q} {L : V → Q → ℝ} {u : V} {p : Q} {r : ℝ}

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
/-- **Truncation, first variable.** A saddle point `(u, p)` of `L` on `(A ∩ closedBall 0 r) × B`
with `‖u‖ < r` is a saddle point on `A × B`, provided `A` is convex and `L (·, p)` is convex on
`A`: for `v ∈ A` outside the ball, the point `w` of the segment `[u, v]` on the sphere of radius
`r` lies in the truncated set, so `L u p ≤ L w p ≤ (1 - t) L u p + t L v p`, whence
`L u p ≤ L v p`. -/
theorem IsSaddlePointOn.of_inter_closedBall_left (hAconv : Convex ℝ A)
    (hL : ConvexOn ℝ A fun v => L v p) (hu : u ∈ A) (hp : p ∈ B) (hur : ‖u‖ < r)
    (h : IsSaddlePointOn (A ∩ closedBall 0 r) B L u p) : IsSaddlePointOn A B L u p := by
  have hu' : u ∈ A ∩ closedBall 0 r := ⟨hu, mem_closedBall_zero_iff.2 hur.le⟩
  intro v hv q hq
  by_cases hvr : ‖v‖ ≤ r
  · exact h v ⟨hv, mem_closedBall_zero_iff.2 hvr⟩ q hq
  rw [not_le] at hvr
  have hnorm := norm_sub_norm_le v u
  have hvu : 0 < ‖v - u‖ := by linarith
  set t : ℝ := (r - ‖u‖) / ‖v - u‖ with ht
  have ht0 : 0 < t := div_pos (by linarith) hvu
  have ht1 : t < 1 := by
    rw [ht, div_lt_one hvu]
    linarith
  set w : V := (1 - t) • u + t • v with hw
  have hwA : w ∈ A := hAconv hu hv (by linarith) ht0.le (by ring)
  have hwr : ‖w‖ ≤ r := by
    have hw' : w = u + t • (v - u) := by
      rw [hw, smul_sub, sub_smul, one_smul]
      abel
    calc ‖w‖ = ‖u + t • (v - u)‖ := by rw [hw']
      _ ≤ ‖u‖ + ‖t • (v - u)‖ := norm_add_le _ _
      _ = ‖u‖ + t * ‖v - u‖ := by rw [norm_smul, Real.norm_of_nonneg ht0.le]
      _ = r := by rw [ht, div_mul_cancel₀ _ hvu.ne']; ring
  have h1 : L u p ≤ L w p := h w ⟨hwA, mem_closedBall_zero_iff.2 hwr⟩ p hp
  have h2 : L w p ≤ (1 - t) * L u p + t * L v p := by
    have := hL.2 hu hv (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
    simpa [smul_eq_mul] using this
  have h3 : L u p ≤ L v p := by
    have : t * L u p ≤ t * L v p := by linarith
    exact le_of_mul_le_mul_left this ht0
  exact (h u hu' q hq).trans h3

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- **Truncation, second variable.** A saddle point `(u, p)` of `L` on `A × (B ∩ closedBall 0 r)`
with `‖p‖ < r` is a saddle point on `A × B`, provided `B` is convex and `L (u, ·)` is concave on
`B`. This is `IsSaddlePointOn.of_inter_closedBall_left` for the transposed, negated kernel. -/
theorem IsSaddlePointOn.of_inter_closedBall_right (hBconv : Convex ℝ B)
    (hL : ConcaveOn ℝ B (L u)) (hu : u ∈ A) (hp : p ∈ B) (hpr : ‖p‖ < r)
    (h : IsSaddlePointOn A (B ∩ closedBall 0 r) L u p) : IsSaddlePointOn A B L u p := by
  rw [← isSaddlePointOn_swap_neg_iff] at h ⊢
  exact h.of_inter_closedBall_left hBconv hL.neg hp hu hpr

end Truncation

/-! ### Existence under coercivity -/

section Coercive

variable {V Q : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace.IsReflexive ℝ V]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedSpace.IsReflexive ℝ Q]
  {A : Set V} {B : Set Q} {L : V → Q → ℝ}

/-- **Existence of a saddle point under coercivity** ([ekeland1999convex] Chapter VI,
Proposition 2.2; [han2009theoretical] Theorem 8.6.3). Let
`A ⊆ V` and `B ⊆ Q` be closed convex subsets of reflexive real normed spaces, and let
`L : V → Q → ℝ` be convex and lower semicontinuous in its first variable on `A` for every `q ∈ B`,
concave and upper semicontinuous in its second variable on `B` for every `v ∈ A`. If some slice
`L (·, q₀)`, `q₀ ∈ B`, is coercive on `A` and some slice `-L (v₀, ·)`, `v₀ ∈ A`, is coercive on
`B`, then `L` has a saddle point `(u, p) ∈ A × B`.

A bounded set makes every functional coercive on it (`IsCoerciveFunctionalOn.of_isBounded`), so
the hypotheses cover "`A` bounded or `L (v, q₀) → ∞` as `‖v‖ → ∞` in `A`" and the symmetric
condition on `B`; nonemptiness of `A` and `B` is part of them.

The proof truncates both sets by the closed ball of a radius `r` and takes a saddle point `(u, p)`
of the truncated problem (`exists_isSaddlePointOn_of_isBounded`). With `m = min_A L (·, q₀)` and
`M = max_B L (v₀, ·)` — both attained, by the direct method —
`m ≤ L u q₀ ≤ L v₀ p ≤ M`, so coercivity confines `u` and `p` to fixed balls; for `r` beyond their
radii the truncation lemmas make `(u, p)` a saddle point of the original problem. -/
theorem exists_isSaddlePointOn_of_isCoerciveFunctionalOn (hAcl : IsClosed A)
    (hAconv : Convex ℝ A) (hBcl : IsClosed B) (hBconv : Convex ℝ B)
    (hLv : ∀ q ∈ B, ConvexOn ℝ A fun v => L v q)
    (hLv' : ∀ q ∈ B, LowerSemicontinuousOn (fun v => L v q) A)
    (hLq : ∀ v ∈ A, ConcaveOn ℝ B (L v)) (hLq' : ∀ v ∈ A, UpperSemicontinuousOn (L v) B)
    (hA : ∃ q₀ ∈ B, IsCoerciveFunctionalOn (fun v => L v q₀) A)
    (hB : ∃ v₀ ∈ A, IsCoerciveFunctionalOn (fun q => -L v₀ q) B) :
    ∃ u ∈ A, ∃ p ∈ B, IsSaddlePointOn A B L u p := by
  obtain ⟨q₀, hq₀, hcA⟩ := hA
  obtain ⟨v₀, hv₀, hcB⟩ := hB
  -- the two bounds `m` and `M`
  obtain ⟨u₁, hu₁, hu₁min⟩ :=
    exists_isMinOn_of_convexOn ⟨v₀, hv₀⟩ hAcl hAconv (hLv q₀ hq₀) (hLv' q₀ hq₀) (Or.inr hcA)
  obtain ⟨p₁, hp₁, hp₁max⟩ :=
    exists_isMaxOn_of_concaveOn ⟨q₀, hq₀⟩ hBcl hBconv (hLq v₀ hv₀) (hLq' v₀ hv₀) (Or.inr hcB)
  obtain ⟨R₁, hR₁⟩ := hcA (L v₀ p₁ + 1)
  obtain ⟨R₂, hR₂⟩ := hcB (-L u₁ q₀ + 1)
  -- the truncated problem
  set r : ℝ := |R₁| + |R₂| + ‖v₀‖ + ‖q₀‖ + 1 with hr
  have hR₁r : R₁ < r := by linarith [le_abs_self R₁, abs_nonneg R₂, norm_nonneg v₀, norm_nonneg q₀]
  have hR₂r : R₂ < r := by linarith [le_abs_self R₂, abs_nonneg R₁, norm_nonneg v₀, norm_nonneg q₀]
  have hv₀r : v₀ ∈ A ∩ closedBall 0 r := ⟨hv₀, mem_closedBall_zero_iff.2 (by
    linarith [abs_nonneg R₁, abs_nonneg R₂, norm_nonneg q₀])⟩
  have hq₀r : q₀ ∈ B ∩ closedBall 0 r := ⟨hq₀, mem_closedBall_zero_iff.2 (by
    linarith [abs_nonneg R₁, abs_nonneg R₂, norm_nonneg v₀])⟩
  have hA'conv : Convex ℝ (A ∩ closedBall 0 r) := hAconv.inter (convex_closedBall 0 r)
  have hB'conv : Convex ℝ (B ∩ closedBall 0 r) := hBconv.inter (convex_closedBall 0 r)
  obtain ⟨u, ⟨hu, hur⟩, p, ⟨hp, hpr⟩, h⟩ :=
    exists_isSaddlePointOn_of_isBounded ⟨v₀, hv₀r⟩ (hAcl.inter isClosed_closedBall) hA'conv
      (isBounded_closedBall.subset inter_subset_right) ⟨q₀, hq₀r⟩
      (hBcl.inter isClosed_closedBall) hB'conv (isBounded_closedBall.subset inter_subset_right)
      (fun q hq => ((hLv q hq.1).subset inter_subset_left hA'conv).quasiconvexOn)
      (fun q hq => (hLv' q hq.1).mono inter_subset_left)
      (fun v hv => ((hLq v hv.1).subset inter_subset_left hB'conv).quasiconcaveOn)
      (fun v hv => (hLq' v hv.1).mono inter_subset_left)
  -- the bounds keep `u` and `p` strictly inside the balls
  have hkey : L u q₀ ≤ L v₀ p := h v₀ hv₀r q₀ hq₀r
  have hM : L v₀ p ≤ L v₀ p₁ := isMaxOn_iff.1 hp₁max p hp
  have hm : L u₁ q₀ ≤ L u q₀ := isMinOn_iff.1 hu₁min u hu
  have hur' : ‖u‖ < R₁ := by
    by_contra hcon
    rw [not_lt] at hcon
    have := hR₁ u hu hcon
    linarith
  have hpr' : ‖p‖ < R₂ := by
    by_contra hcon
    rw [not_lt] at hcon
    have := hR₂ p hp hcon
    linarith
  refine ⟨u, hu, p, hp, ?_⟩
  have h' : IsSaddlePointOn (A ∩ closedBall 0 r) B L u p :=
    h.of_inter_closedBall_right hBconv (hLq u hu) ⟨hu, hur⟩ hp (hpr'.trans hR₂r)
  exact h'.of_inter_closedBall_left hAconv (hLv p hp) hu hp (hur'.trans hR₁r)

/-- **Existence of a saddle point, coercivity of the supremum** ([ekeland1999convex] Chapter VI,
Remark after Proposition 2.3; [han2009theoretical] Theorem 8.6.3, condition (f)'). The pointwise
coercivity of a slice `L (·, q₀)` on `A` may be replaced by the coercivity of
`v ↦ sup_{q ∈ B} L (v, q)`, stated without a supremum as: for every `M` there is `R` such that
every `v ∈ A` with `R ≤ ‖v‖` has some `q ∈ B` with `M ≤ L v q` (so the supremum, possibly `+∞`,
tends to `+∞`). The condition on `B` stays pointwise.

Truncating `A` alone, `exists_isSaddlePointOn_of_isCoerciveFunctionalOn` gives a saddle point
`(u, p)` of `L` on `(A ∩ closedBall 0 r) × B`; then `L u q ≤ L v₀ p ≤ max_B L (v₀, ·)` for every
`q ∈ B`, which by the hypothesis confines `u` to a fixed ball, and the truncation lemma applies.
The condition on `B` cannot be replaced by its supremum form at the same time: see the module
documentation. -/
theorem exists_isSaddlePointOn_of_sup_coercive (hAcl : IsClosed A) (hAconv : Convex ℝ A)
    (hBne : B.Nonempty) (hBcl : IsClosed B) (hBconv : Convex ℝ B)
    (hLv : ∀ q ∈ B, ConvexOn ℝ A fun v => L v q)
    (hLv' : ∀ q ∈ B, LowerSemicontinuousOn (fun v => L v q) A)
    (hLq : ∀ v ∈ A, ConcaveOn ℝ B (L v)) (hLq' : ∀ v ∈ A, UpperSemicontinuousOn (L v) B)
    (hA : ∀ M : ℝ, ∃ R : ℝ, ∀ v ∈ A, R ≤ ‖v‖ → ∃ q ∈ B, M ≤ L v q)
    (hB : ∃ v₀ ∈ A, IsCoerciveFunctionalOn (fun q => -L v₀ q) B) :
    ∃ u ∈ A, ∃ p ∈ B, IsSaddlePointOn A B L u p := by
  obtain ⟨q₀, hq₀⟩ := hBne
  obtain ⟨v₀, hv₀, hcB⟩ := hB
  obtain ⟨p₁, hp₁, hp₁max⟩ :=
    exists_isMaxOn_of_concaveOn ⟨q₀, hq₀⟩ hBcl hBconv (hLq v₀ hv₀) (hLq' v₀ hv₀) (Or.inr hcB)
  obtain ⟨R, hR⟩ := hA (L v₀ p₁ + 1)
  set r : ℝ := |R| + ‖v₀‖ + 1 with hr
  have hRr : R < r := by linarith [le_abs_self R, norm_nonneg v₀]
  have hv₀r : v₀ ∈ A ∩ closedBall 0 r :=
    ⟨hv₀, mem_closedBall_zero_iff.2 (by linarith [abs_nonneg R])⟩
  have hA'conv : Convex ℝ (A ∩ closedBall 0 r) := hAconv.inter (convex_closedBall 0 r)
  obtain ⟨u, ⟨hu, hur⟩, p, hp, h⟩ :=
    exists_isSaddlePointOn_of_isCoerciveFunctionalOn (hAcl.inter isClosed_closedBall) hA'conv
      hBcl hBconv (fun q hq => (hLv q hq).subset inter_subset_left hA'conv)
      (fun q hq => (hLv' q hq).mono inter_subset_left) (fun v hv => hLq v hv.1)
      (fun v hv => hLq' v hv.1)
      ⟨q₀, hq₀,
        IsCoerciveFunctionalOn.of_isBounded (isBounded_closedBall.subset inter_subset_right)⟩
      ⟨v₀, hv₀r, hcB⟩
  have hur' : ‖u‖ < R := by
    by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨q, hq, hMq⟩ := hR u hu hcon
    have h1 : L u q ≤ L v₀ p := h v₀ hv₀r q hq
    have h2 : L v₀ p ≤ L v₀ p₁ := isMaxOn_iff.1 hp₁max p hp
    linarith
  exact ⟨u, hu, p, hp, h.of_inter_closedBall_left hAconv (hLv p hp) hu hp (hur'.trans hRr)⟩

/-- **Existence of a saddle point, coercivity of the infimum** ([han2009theoretical]
Theorem 8.6.3, condition (g)'): the pointwise coercivity of a slice `-L (v₀, ·)` on `B` may be
replaced by `inf_{v ∈ A} L (v, q) → -∞` as `‖q‖ → ∞` in `B`, stated as: for every `M` there is
`R` such that every `q ∈ B` with `R ≤ ‖q‖` has some `v ∈ A` with `L v q ≤ M`. The condition on
`A` stays pointwise. This is `exists_isSaddlePointOn_of_sup_coercive` for the transposed, negated
kernel. -/
theorem exists_isSaddlePointOn_of_inf_coercive (hAne : A.Nonempty) (hAcl : IsClosed A)
    (hAconv : Convex ℝ A) (hBcl : IsClosed B) (hBconv : Convex ℝ B)
    (hLv : ∀ q ∈ B, ConvexOn ℝ A fun v => L v q)
    (hLv' : ∀ q ∈ B, LowerSemicontinuousOn (fun v => L v q) A)
    (hLq : ∀ v ∈ A, ConcaveOn ℝ B (L v)) (hLq' : ∀ v ∈ A, UpperSemicontinuousOn (L v) B)
    (hA : ∃ q₀ ∈ B, IsCoerciveFunctionalOn (fun v => L v q₀) A)
    (hB : ∀ M : ℝ, ∃ R : ℝ, ∀ q ∈ B, R ≤ ‖q‖ → ∃ v ∈ A, L v q ≤ M) :
    ∃ u ∈ A, ∃ p ∈ B, IsSaddlePointOn A B L u p := by
  obtain ⟨p, hp, u, hu, h⟩ :=
    exists_isSaddlePointOn_of_sup_coercive (L := fun q v => -L v q) hBcl hBconv hAne hAcl hAconv
      (fun v hv => (hLq v hv).neg)
      (fun v hv =>
        continuous_neg.comp_upperSemicontinuousOn_antitone (hLq' v hv) fun _ _ h => neg_le_neg h)
      (fun q hq => (hLv q hq).neg)
      (fun q hq =>
        continuous_neg.comp_lowerSemicontinuousOn_antitone (hLv' q hq) fun _ _ h => neg_le_neg h)
      (fun M => by
        obtain ⟨R, hR⟩ := hB (-M)
        refine ⟨R, fun q hq hRq => ?_⟩
        obtain ⟨v, hv, hvM⟩ := hR q hq hRq
        exact ⟨v, hv, by linarith⟩)
      (by
        obtain ⟨q₀, hq₀, hc⟩ := hA
        exact ⟨q₀, hq₀, by simpa using hc⟩)
  exact ⟨u, hu, p, hp, isSaddlePointOn_swap_neg_iff.1 h⟩

end Coercive

/-! ### Uniqueness -/

section Uniqueness

variable {V Q : Type*} [AddCommMonoid V] [SMul ℝ V] [AddCommMonoid Q] [SMul ℝ Q]
  {A : Set V} {B : Set Q} {L : V → Q → ℝ} {u u' : V} {p p' : Q}

omit [AddCommMonoid Q] [SMul ℝ Q] in
/-- **Uniqueness of the first component**: if `(u, p)` and `(u', p')` are saddle points of `L` on
`A × B` and `L (·, p)` is strictly convex on `A`, then `u = u'`. Both `u` and `u'` minimize
`L (·, p)` on `A`, the second because `(u', p)` is again a saddle point
(`IsSaddlePointOn.swap_right`). -/
theorem IsSaddlePointOn.fst_eq_of_strictConvexOn (hL : StrictConvexOn ℝ A fun v => L v p)
    (hu : u ∈ A) (hu' : u' ∈ A) (hp : p ∈ B) (hp' : p' ∈ B) (h : IsSaddlePointOn A B L u p)
    (h' : IsSaddlePointOn A B L u' p') : u = u' := by
  have h'' : IsSaddlePointOn A B L u' p := h.swap_right hu hp' h'
  exact hL.eq_of_isMinOn (isMinOn_iff.2 fun v hv => h v hv p hp)
    (isMinOn_iff.2 fun v hv => h'' v hv p hp) hu hu'

omit [AddCommMonoid V] [SMul ℝ V] in
/-- **Uniqueness of the second component**: if `(u, p)` and `(u', p')` are saddle points of `L`
on `A × B` and `L (u, ·)` is strictly concave on `B`, then `p = p'`. -/
theorem IsSaddlePointOn.snd_eq_of_strictConcaveOn (hL : StrictConcaveOn ℝ B (L u))
    (hu : u ∈ A) (hu' : u' ∈ A) (hp : p ∈ B) (hp' : p' ∈ B) (h : IsSaddlePointOn A B L u p)
    (h' : IsSaddlePointOn A B L u' p') : p = p' := by
  have h'' : IsSaddlePointOn A B L u p' := h.swap_left hu' hp h'
  exact hL.eq_of_isMaxOn (isMaxOn_iff.2 fun q hq => h u hu q hq)
    (isMaxOn_iff.2 fun q hq => h'' u hu q hq) hp hp'

end Uniqueness
