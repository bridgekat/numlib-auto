import Numlib.Analysis.Convex.Saddle.Conjugate

/-!
# Subdifferentials of saddle-functions

A saddle-function is concave in one variable and convex in the other, so it has *two* one-sided
subdifferentials: a superdifferential in the concave variable and a subdifferential in the convex
one. Their product is `∂K`. Two facts make it useful: `(u*, x*) ∈ ∂K (u, x)` says exactly that
`(u, x)` is a *saddle-point* of `K` tilted by `⟨·, u*⟩ + ⟨·, x*⟩`, and for a closed proper `K` one
has `ri (dom K) ⊆ dom ∂K ⊆ dom K`.

Moreover `∂K` depends only on the equivalence class of `K`: on `Ω (F)` it is one relation attached
to `F`, and the relations of conjugate classes are inverse. In particular `∂K*(0, 0)` is the set of
saddle-points of `K`, so one exists whenever the origin lies in `ri (dom K*)`.

## Main definitions

* `saddleSubdifferential Bu Bx K p` — `∂K (u, x) = ∂₁K (u, x) × ∂₂K (u, x) ⊆ V × Y`, the concave
  variable being paired against `V` and the convex one against `Y`; `domSaddleSubdifferential` is
  where it is nonempty, and `saddleTilt Bu Bx K q` is `K - ⟨·, u*⟩ - ⟨·, x*⟩`.
* `IsBifunSubgradientPair Bu Bx F p q` — the relation
  `(F u) x - ⟨x, y⟩ = (F* y) v - ⟨u, v⟩`: the subdifferential of a class, without a representative.

## Main results

* `mem_saddleSubdifferential_iff_isSaddlePoint` — subgradients are saddle-points of the tilt, with
  no hypotheses at all ([rockafellar1970convex] Theorem 37.4);
  `kernelSet_subset_domSaddleSubdifferential_subset_domSaddle` — `ri (dom K) ⊆ dom ∂K ⊆ dom K`.
* `mem_saddleSubdifferential_iff_isBifunSubgradientPair`,
  `mem_saddleSubdifferential_upperConjSaddle_iff` — `∂K` is one relation attached to the class, read
  from either side ([rockafellar1970convex] Theorem 37.5).
* `mem_saddleSubdifferential_upperConjSaddle_zero_iff` — `∂K* (0, 0)` is the set of saddle-points;
  `exists_isSaddlePoint_of_zero_mem_kernelSet_upperConjSaddle` — one exists if `0 ∈ ri (dom K*)`.

## Implementation notes

In `Rᵐ × Rⁿ` the four spaces coincide; keeping them apart is what makes `∂K*` land back in `U × Y`.

The variant `(-v, y) ∈ ∂f (u, x)` for the graph function `f` of `F` is *not* equivalent to
`IsBifunSubgradientPair` without properness: where `F u x = (F* y) v = ⊤`, the latter reads
`⊤ - r = ⊤ - s` and holds while the former fails. The customary statements do not record the
restriction; the form used in `Saddle/Monotone.lean` assumes `ProperConvex (graphFn F)`.

## References

* [rockafellar1970convex] §23, §35 and §37.
-/

namespace ConvexAnalysis

/-! ### Cancelling real coercions across an `EReal` inequality -/

section ERealSub

/-- Moving a real subtrahend across an `EReal` inequality: `z - c ≤ w - d ↔ z ≤ w + e` whenever
`c - d = e`. There is no side condition, because `c` and `d` are finite. The difference is passed
as a parameter with its defining equation, so that the caller supplies whatever form it has. -/
theorem sub_coe_le_sub_coe_iff_le_add {z w : EReal} {c d e : ℝ} (he : c - d = e) :
    z - (c : EReal) ≤ w - (d : EReal) ↔ z ≤ w + (e : EReal) := by
  have hw : w - (d : EReal) + (c : EReal) = w + (e : EReal) := by
    induction w with
    | bot => simp
    | top => simp
    | coe t =>
      rw [← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_add,
        EReal.coe_eq_coe_iff]
      linarith
  rw [← (EReal.addLECancellable_coe c).add_le_add_iff_right,
    EReal.sub_add_cancel, hw]

/-- The companion of `sub_coe_le_sub_coe_iff_le_add` with the real moved to the *left*:
`z - c ≤ w - d ↔ z + e ≤ w` whenever `d - c = e`. -/
theorem sub_coe_le_sub_coe_iff_add_le {z w : EReal} {c d e : ℝ} (he : d - c = e) :
    z - (c : EReal) ≤ w - (d : EReal) ↔ z + (e : EReal) ≤ w := by
  have hz : z - (c : EReal) + (d : EReal) = z + (e : EReal) := by
    induction z with
    | bot => simp
    | top => simp
    | coe t =>
      rw [← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_add,
        EReal.coe_eq_coe_iff]
      linarith
  rw [← (EReal.addLECancellable_coe d).add_le_add_iff_right,
    EReal.sub_add_cancel, hz]

/-- Subtracting a real number does not move the effective domain: `z - c < ⊤ ↔ z < ⊤`. -/
theorem sub_coe_lt_top_iff {z : EReal} {c : ℝ} : z - (c : EReal) < ⊤ ↔ z < ⊤ := by
  induction z with
  | bot => simp
  | top => simp
  | coe r =>
    refine iff_of_true ?_ (EReal.coe_lt_top r)
    rw [← EReal.coe_sub]
    exact EReal.coe_lt_top _

/-- Subtracting a real number does not move the concave effective domain:
`⊥ < z - c ↔ ⊥ < z`. -/
theorem bot_lt_sub_coe_iff {z : EReal} {c : ℝ} : ⊥ < z - (c : EReal) ↔ ⊥ < z := by
  induction z with
  | bot => simp
  | top => simp
  | coe r =>
    refine iff_of_true ?_ (EReal.bot_lt_coe r)
    rw [← EReal.coe_sub]
    exact EReal.bot_lt_coe _

/-- Subtracting from a real number is an involution of `EReal`: `r - (r - z) = z`. -/
theorem coe_sub_coe_sub_self (r : ℝ) (z : EReal) : (r : EReal) - ((r : EReal) - z) = z := by
  rw [EReal.coe_sub_coe_sub, sub_self, EReal.coe_zero, zero_add]

/-- Moving an `EReal` across a subtraction from a real number: `z = r - w ↔ r - z = w`. This is
what turns the two conjugate criteria into a common value. -/
theorem eq_coe_sub_iff_coe_sub_eq {z w : EReal} {r : ℝ} :
    z = (r : EReal) - w ↔ (r : EReal) - z = w := by
  constructor
  · intro h
    rw [h, coe_sub_coe_sub_self]
  · intro h
    rw [← h, coe_sub_coe_sub_self]

/-- Negating a subtraction by a real number: `-(z - r) = r - z`. -/
theorem neg_sub_coe (z : EReal) (r : ℝ) : -(z - (r : EReal)) = (r : EReal) - z := by
  induction z with
  | bot => simp
  | top => simp
  | coe t =>
    rw [← EReal.coe_sub, ← EReal.coe_neg, ← EReal.coe_sub,
      EReal.coe_eq_coe_iff]
    ring

/-- Reflecting both sides of an equation between differences by real numbers:
`z - r = w - s ↔ r - z = s - w`. -/
theorem sub_coe_eq_sub_coe_comm {z w : EReal} {r s : ℝ} :
    z - (r : EReal) = w - (s : EReal) ↔ (r : EReal) - z = (s : EReal) - w := by
  rw [← neg_sub_coe z r, ← neg_sub_coe w s, _root_.neg_inj]

/-- Equating two differences by real numbers: `z - r = w - s ↔ z + s = w + r`. -/
theorem sub_coe_eq_sub_coe_iff {z w : EReal} {r s : ℝ} :
    z - (r : EReal) = w - (s : EReal) ↔ z + (s : EReal) = w + (r : EReal) := by
  have hz : z - (r : EReal) + ((r + s : ℝ) : EReal) = z + (s : EReal) := by
    induction z with
    | bot => simp
    | top => simp
    | coe t =>
      rw [← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_add,
        EReal.coe_eq_coe_iff]
      ring
  have hw : w - (s : EReal) + ((r + s : ℝ) : EReal) = w + (r : EReal) := by
    induction w with
    | bot => simp
    | top => simp
    | coe t =>
      rw [← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_add,
        EReal.coe_eq_coe_iff]
      ring
  constructor
  · intro h
    rw [← hz, ← hw, h]
  · intro h
    have h2 : z - (r : EReal) + ((r + s : ℝ) : EReal)
        = w - (s : EReal) + ((r + s : ℝ) : EReal) := by rw [hz, hw, h]
    exact le_antisymm
      ((EReal.addLECancellable_coe (r + s)).add_le_add_iff_right.1 h2.le)
      ((EReal.addLECancellable_coe (r + s)).add_le_add_iff_right.1 h2.ge)

/-- **The reflection that exchanges a class with its conjugate class**:
`z - r = w - s ↔ -w - r = -z - s`. Both say `z + s = w + r`; the right-hand side is the left with
the two `EReal`s negated and exchanged, which is what conjugating a bifunction does. -/
theorem sub_coe_eq_sub_coe_iff_neg {z w : EReal} {r s : ℝ} :
    z - (r : EReal) = w - (s : EReal) ↔ -w - (r : EReal) = -z - (s : EReal) := by
  have hw : -w - (r : EReal) = -(w + (r : EReal)) :=
    (EReal.neg_add (.inr (EReal.coe_ne_top r))
      (.inr (EReal.coe_ne_bot r))).symm
  have hz : -z - (s : EReal) = -(z + (s : EReal)) :=
    (EReal.neg_add (.inr (EReal.coe_ne_top s))
      (.inr (EReal.coe_ne_bot s))).symm
  rw [sub_coe_eq_sub_coe_iff, hw, hz, _root_.neg_inj, eq_comm]

end ERealSub

/-! ### The subdifferential of a saddle-function -/

section SaddleSubdifferential

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The **subdifferential of a saddle-function**: `∂K (u, x) = ∂₁K (u, x) × ∂₂K (u, x)`, the
supergradients of the concave slice through `x` paired with the subgradients of the convex slice
through `u`. -/
def saddleSubdifferential (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (K : U × X → EReal)
    (p : U × X) : Set (V × Y) :=
  superdifferential Bu (fun u => K (u, p.2)) p.1
    ×ˢ subdifferential Bx (fun x => K (p.1, x)) p.2

variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {K : U × X → EReal} {p : U × X}
  {q : V × Y}

@[simp] theorem mem_saddleSubdifferential :
    q ∈ saddleSubdifferential Bu Bx K p ↔
      q.1 ∈ superdifferential Bu (fun u => K (u, p.2)) p.1 ∧
        q.2 ∈ subdifferential Bx (fun x => K (p.1, x)) p.2 := Iff.rfl

/-- `∂K (u, x)` is convex with no hypothesis on `K`; being a product it is even a convex *product*
set, which is what makes the set of saddle-points a convex product set. -/
theorem convex_saddleSubdifferential : Convex ℝ (saddleSubdifferential Bu Bx K p) :=
  Convex.prod convex_superdifferential (convex_subdifferential Bx (fun x => K (p.1, x)) p.2)

/-- The set where the subdifferential of a saddle-function is nonempty, `dom ∂K`. -/
def domSaddleSubdifferential (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × X → EReal) : Set (U × X) :=
  {p | (saddleSubdifferential Bu Bx K p).Nonempty}

@[simp] theorem mem_domSaddleSubdifferential :
    p ∈ domSaddleSubdifferential Bu Bx K ↔ (saddleSubdifferential Bu Bx K p).Nonempty := Iff.rfl

end SaddleSubdifferential

/-! ### Tilting a saddle-function by a linear function -/

section SaddleTilt

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- Rockafellar's `K - ⟨·, u*⟩ - ⟨·, x*⟩`, the tilt of `K` by the linear function determined by
`q = (u*, x*)`. The two pairings are combined into one real coercion, which is what keeps the
`EReal` arithmetic free of side conditions. -/
noncomputable def saddleTilt (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × X → EReal) (q : V × Y) : U × X → EReal :=
  fun p => K p - ((Bu p.1 q.1 + Bx p.2 q.2 : ℝ) : EReal)

theorem saddleTilt_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × X → EReal) (q : V × Y) (p : U × X) :
    saddleTilt Bu Bx K q p = K p - ((Bu p.1 q.1 + Bx p.2 q.2 : ℝ) : EReal) := rfl

@[simp] theorem saddleTilt_zero (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × X → EReal) : saddleTilt Bu Bx K 0 = K := by
  funext p
  rw [saddleTilt_apply]
  norm_num

variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {K : U × X → EReal} {q : V × Y}

@[simp] theorem dom₁_saddleTilt : dom₁ (saddleTilt Bu Bx K q) = dom₁ K := by
  ext u
  exact forall_congr' fun x => bot_lt_sub_coe_iff

@[simp] theorem dom₂_saddleTilt : dom₂ (saddleTilt Bu Bx K q) = dom₂ K := by
  ext x
  exact forall_congr' fun u => sub_coe_lt_top_iff

theorem ProperSaddleFn.saddleTilt (hp : ProperSaddleFn K) :
    ProperSaddleFn (ConvexAnalysis.saddleTilt Bu Bx K q) :=
  ⟨by rw [dom₁_saddleTilt]; exact hp.dom₁_nonempty,
    by rw [dom₂_saddleTilt]; exact hp.dom₂_nonempty⟩

end SaddleTilt

/-! ### Subgradients are saddle-points of the tilted function -/

section TiltCriterion

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {K : U × X → EReal} {p : U × X} {q : V × Y}

/-- `(u*, x*) ∈ ∂K (u, x)` exactly when `(u, x)` is a saddle-point of
`K - ⟨·, u*⟩ - ⟨·, x*⟩`. There are **no hypotheses at all** — not concavity, not
convexity, not properness: both sides are the same pair of inequalities, one in each variable, with
a real number moved across. -/
theorem mem_saddleSubdifferential_iff_isSaddlePoint :
    q ∈ saddleSubdifferential Bu Bx K p ↔ IsSaddlePoint (saddleTilt Bu Bx K q) p := by
  have h₁ : ∀ u : U, ((Bu u q.1 + Bx p.2 q.2 : ℝ) - (Bu p.1 q.1 + Bx p.2 q.2 : ℝ) : ℝ)
      = Bu (u - p.1) q.1 := by
    intro u
    rw [map_sub, LinearMap.sub_apply]
    ring
  have h₂ : ∀ x : X, ((Bu p.1 q.1 + Bx x q.2 : ℝ) - (Bu p.1 q.1 + Bx p.2 q.2 : ℝ) : ℝ)
      = Bx (x - p.2) q.2 := by
    intro x
    rw [map_sub, LinearMap.sub_apply]
    ring
  have hfst : ∀ u : U,
      saddleTilt Bu Bx K q (u, p.2) ≤ saddleTilt Bu Bx K q p ↔
        K (u, p.2) ≤ K p + ((Bu (u - p.1) q.1 : ℝ) : EReal) := by
    intro u
    rw [saddleTilt_apply, saddleTilt_apply, sub_coe_le_sub_coe_iff_le_add (h₁ u)]
  have hsnd : ∀ x : X,
      saddleTilt Bu Bx K q p ≤ saddleTilt Bu Bx K q (p.1, x) ↔
        K p + ((Bx (x - p.2) q.2 : ℝ) : EReal) ≤ K (p.1, x) := by
    intro x
    rw [saddleTilt_apply, saddleTilt_apply, sub_coe_le_sub_coe_iff_add_le (h₂ x)]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨fun u => (hfst u).2 (ha u), fun x => (hsnd x).2 (hb x)⟩
  · rintro ⟨ha, hb⟩
    exact ⟨fun u => (hfst u).1 (ha u), fun x => (hsnd x).1 (hb x)⟩

end TiltCriterion

/-! ### The effective domain of the subdifferential -/

section SubdifferentialDom

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {K : U × X → EReal}

/-- `dom ∂K ⊆ dom K` for a *proper* saddle-function; closedness is not needed. A subgradient pair
at `p` makes `p` a saddle-point of the tilt, and the saddle-points of a proper saddle-function lie
in its effective domain. -/
theorem domSaddleSubdifferential_subset_domSaddle (hp : ProperSaddleFn K) :
    domSaddleSubdifferential Bu Bx K ⊆ domSaddle K := by
  rintro p ⟨q, hq⟩
  have hsp : IsSaddlePoint (saddleTilt Bu Bx K q) p :=
    mem_saddleSubdifferential_iff_isSaddlePoint.1 hq
  have hprop : ProperSaddleFn (saddleTilt Bu Bx K q) := ProperSaddleFn.saddleTilt hp
  have h := IsSaddlePoint.mem_domSaddle hprop hsp
  rw [mem_domSaddle, dom₁_saddleTilt, dom₂_saddleTilt] at h
  exact h

end SubdifferentialDom

section SubdifferentialRelint

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {K : U × X → EReal}

/-- `ri (dom K) ⊆ dom ∂K`. Over `ri (dom₁ K)` the convex slice `K (u, ·)` is proper with effective
domain exactly `dom₂ K`, so it has a subgradient there; the concave half is the same statement for
`saddleSwap K`. -/
theorem kernelSet_subset_domSaddleSubdifferential [IsCompatiblePairing Bu] [IsCompatiblePairing Bx]
    (hK : ConcaveConvexFn K) (hs : SaddleStructure K) :
    kernelSet K ⊆ domSaddleSubdifferential Bu Bx K := by
  rintro ⟨u, x⟩ ⟨hu, hx⟩
  have hudom : u ∈ dom₁ K := intrinsicInterior_subset hu
  have hxdom : x ∈ dom₂ K := intrinsicInterior_subset hx
  have hxr : x ∈ ri (convexDom fun x' => K (u, x')) := by
    rw [hs.1.convexDom_slice u hu]
    exact hx
  obtain ⟨y, hy⟩ := subdifferential_nonempty_of_mem_relint_convexDom (B := Bx) (hK.convex_snd u)
    (hs.1.properConvex_slice u hudom) hxr
  have hswapdom : x ∈ dom₁ (saddleSwap K) := by rw [dom₁_saddleSwap]; exact hxdom
  have hswapri : x ∈ ri (dom₁ (saddleSwap K)) := by rw [dom₁_saddleSwap]; exact hx
  have hdomeq : (convexDom fun u' => -(K (u', x))) = dom₁ K := by
    have h := hs.2.convexDom_slice x hswapri
    rw [dom₂_saddleSwap] at h
    exact h
  have hur : u ∈ ri (concaveDom fun u' => K (u', x)) := by
    rw [concaveDom_eq_convexDom_neg, hdomeq]
    exact hu
  have hpr : ProperConvex fun u' => -(K (u', x)) := hs.2.properConvex_slice x hswapdom
  obtain ⟨v, hv⟩ := superdifferential_nonempty_of_mem_relint_concaveDom (B := Bu)
    (hK.concave_fst x) (properConcave_iff_properConvex_neg.2 hpr) hur
  exact ⟨(v, y), hv, hy⟩

/-- `ri (dom K) ⊆ dom ∂K ⊆ dom K` for a closed proper saddle-function. -/
theorem kernelSet_subset_domSaddleSubdifferential_subset_domSaddle [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bx] (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hcl : ClosedSaddleFn K) :
    kernelSet K ⊆ domSaddleSubdifferential Bu Bx K
      ∧ domSaddleSubdifferential Bu Bx K ⊆ domSaddle K :=
  ⟨kernelSet_subset_domSaddleSubdifferential hK ((closedSaddleFn_iff_saddleStructure hK hp).1 hcl),
    domSaddleSubdifferential_subset_domSaddle hp⟩

end SubdifferentialRelint


/-! ### The subdifferential of an equivalence class -/

section BifunPair

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **The subgradient relation of a bifunction**: the point `p = (u, y)` and the pair
`q = (v, x)` satisfy

`(F u) x - ⟨x, y⟩ = (F* y) v - ⟨u, v⟩`.

It is the equality case of the chain
`⟨x, y⟩ - (F u) x ≤ ⟨F u, y⟩ ≤ ⟨u, F* y⟩ ≤ ⟨u, v⟩ - (F* y) v`, and it turns out to be exactly
membership in `∂K` for *every* `K` in the class `Ω (F)`. -/
def IsBifunSubgradientPair (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (p : U × Y) (q : V × X) : Prop :=
  F p.1 q.2 - ((Bx q.2 p.2 : ℝ) : EReal)
    = convexAdjointBifun Bu Bx F p.2 q.1 - ((Bu p.1 q.1 : ℝ) : EReal)

/-- The relation read through the reflection `z ↦ r - z`: both differences are then the common
value of the squeezed chain, namely `K (u, y)`. -/
theorem isBifunSubgradientPair_iff (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (p : U × Y) (q : V × X) :
    IsBifunSubgradientPair Bu Bx F p q ↔
      ((Bx q.2 p.2 : ℝ) : EReal) - F p.1 q.2
        = ((Bu p.1 q.1 : ℝ) : EReal) - convexAdjointBifun Bu Bx F p.2 q.1 :=
  sub_coe_eq_sub_coe_comm

theorem isBifunSubgradientPair_def (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (p : U × Y) (q : V × X) :
    IsBifunSubgradientPair Bu Bx F p q ↔
      F p.1 q.2 - ((Bx q.2 p.2 : ℝ) : EReal)
        = convexAdjointBifun Bu Bx F p.2 q.1 - ((Bu p.1 q.1 : ℝ) : EReal) := Iff.rfl

end BifunPair

section ClassSubdifferential

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

/-- For *any* `K` in the class `Ω (F)`, the subdifferential `∂K` is the relation
`IsBifunSubgradientPair` attached to `F`. In particular `∂K` depends only on the class.

Each half of `∂K (u, y)` says that a conjugate of a slice is attained — `F u` in the convex
variable, `F* y` in the concave one — so each says that a difference equals `K (u, y)`; together
they say the two differences are equal. Conversely the relation squeezes the chain
`⟨x, y⟩ - (F u) x ≤ ⟨F u, y⟩ ≤ K (u, y) ≤ ⟨u, F* y⟩ ≤ ⟨u, v⟩ - (F* y) v` between equal ends. -/
theorem mem_saddleSubdifferential_iff_isBifunSubgradientPair (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) (p : U × Y) (q : V × X) :
    q ∈ saddleSubdifferential Bu Bx.flip K p ↔ IsBifunSubgradientPair Bu Bx F p q := by
  have hA : convexConj Bx.flip (fun y => K (p.1, y)) = F p.1 :=
    congrFun (bifunOfSaddle_eq_of_mem_bifunSaddleClass Bu Bx hF hcl hK) p.1
  have hB : concaveConj Bu (fun u => K (u, p.2)) = convexAdjointBifun Bu Bx F p.2 :=
    concaveConj_slice_eq_convexAdjointBifun Bu Bx hF hK p.2
  have h1 : q.1 ∈ superdifferential Bu (fun u => K (u, p.2)) p.1 ↔
      ((Bu p.1 q.1 : ℝ) : EReal) - convexAdjointBifun Bu Bx F p.2 q.1 = K p := by
    rw [mem_superdifferential_iff_concaveConj_eq, hB, eq_coe_sub_iff_coe_sub_eq]
  have h2 : q.2 ∈ subdifferential Bx.flip (fun y => K (p.1, y)) p.2 ↔
      ((Bx q.2 p.2 : ℝ) : EReal) - F p.1 q.2 = K p := by
    rw [mem_subdifferential_iff_convexConj_eq, hA, LinearMap.flip_apply, eq_coe_sub_iff_coe_sub_eq]
  rw [isBifunSubgradientPair_iff, mem_saddleSubdifferential, h1, h2]
  constructor
  · rintro ⟨ha, hb⟩
    rw [ha, hb]
  · intro hd
    have hle1 : ((Bx q.2 p.2 : ℝ) : EReal) - F p.1 q.2 ≤ K p :=
      le_trans (sub_le_convexConj Bx (F p.1) q.2 p.2) (hK.1 p)
    have hiinf : concaveBracket Bu (convexAdjointBifun Bu Bx F) p.1 p.2
        ≤ ((Bu p.1 q.1 : ℝ) : EReal) - convexAdjointBifun Bu Bx F p.2 q.1 := by
      rw [concaveBracket_apply]
      exact iInf_le (fun v => ((Bu p.1 v : ℝ) : EReal) - convexAdjointBifun Bu Bx F p.2 v) q.1
    have hle2 : K p ≤ ((Bu p.1 q.1 : ℝ) : EReal) - convexAdjointBifun Bu Bx F p.2 q.1 :=
      le_trans (hK.2 p) hiinf
    have hle2' : K p ≤ ((Bx q.2 p.2 : ℝ) : EReal) - F p.1 q.2 := by rw [hd]; exact hle2
    have heq1 : ((Bx q.2 p.2 : ℝ) : EReal) - F p.1 q.2 = K p := le_antisymm hle1 hle2'
    have heq2 : ((Bu p.1 q.1 : ℝ) : EReal) - convexAdjointBifun Bu Bx F p.2 q.1 = K p := by
      rw [← hd]; exact heq1
    exact ⟨heq2, heq1⟩

/-- The same relation read from the conjugate side, so the subdifferentials of conjugate classes
are inverse to each other, exactly as `∂(f*) = (∂f)⁻¹` for convex functions. `K̄*` lies in the class
`Ω (F_*^*)` at the flipped pairings, and the biadjoint identity turns the resulting condition into
the relation reflected by `sub_coe_eq_sub_coe_iff_neg`. -/
theorem mem_saddleSubdifferential_upperConjSaddle_iff (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) (p : U × Y) (q : V × X) :
    p ∈ saddleSubdifferential Bu.flip Bx (upperConjSaddle Bu Bx K) q ↔
      IsBifunSubgradientPair Bu Bx F p q := by
  have hGconv : ConvexBifun (lowerAdjointBifun Bu Bx F) := convexBifun_lowerAdjointBifun Bu Bx F
  have := isContinuousPairing_prodPairing_flip Bu Bx
  have hGcl : ClosedConvexBifun (lowerAdjointBifun Bu Bx F) := closedConvexBifun_lowerAdjointBifun
  have hKstar : upperConjSaddle Bu Bx K
      ∈ bifunSaddleClass Bu.flip Bx.flip (lowerAdjointBifun Bu Bx F) := by
    rw [saddleClass_conjSaddle Bu Bx hF hcl hK]
    exact mem_saddleClass_right (partialCl₂_upperConjSaddle Bu Bx hF hcl hK)
  have hmain := mem_saddleSubdifferential_iff_isBifunSubgradientPair Bu.flip Bx.flip hGconv hGcl
    hKstar q p
  rw [LinearMap.flip_flip] at hmain
  rw [hmain, isBifunSubgradientPair_def, isBifunSubgradientPair_def,
    convexAdjointBifun_flip_lowerAdjointBifun (Bu := Bu) (Bx := Bx) hF hcl]
  simp only [inverseBifun_apply, LinearMap.flip_apply]
  exact sub_coe_eq_sub_coe_iff_neg.symm

/-- `∂K* (0, 0)` *is* the set of saddle-points of `K`. The conjugate-side reading at `q = 0` is
the direct reading at `q = 0`, which is the saddle-point property for the untilted `K`. -/
theorem mem_saddleSubdifferential_upperConjSaddle_zero_iff (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) (p : U × Y) :
    p ∈ saddleSubdifferential Bu.flip Bx (upperConjSaddle Bu Bx K) 0 ↔ IsSaddlePoint K p := by
  rw [mem_saddleSubdifferential_upperConjSaddle_iff Bu Bx hF hcl hK p 0,
    ← mem_saddleSubdifferential_iff_isBifunSubgradientPair Bu Bx hF hcl hK p 0,
    mem_saddleSubdifferential_iff_isSaddlePoint, saddleTilt_zero]

/-- The saddle-points of `K` form a convex product set. -/
theorem convex_setOf_isSaddlePoint (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) : Convex ℝ {p : U × Y | IsSaddlePoint K p} := by
  have hset : {p : U × Y | IsSaddlePoint K p}
      = saddleSubdifferential Bu.flip Bx (upperConjSaddle Bu Bx K) 0 := by
    ext p
    exact (mem_saddleSubdifferential_upperConjSaddle_zero_iff Bu Bx hF hcl hK p).symm
  rw [hset]
  exact convex_saddleSubdifferential

/-- `K` has a saddle-point exactly when the origin lies in `dom ∂K*`. -/
theorem exists_isSaddlePoint_iff_zero_mem_domSaddleSubdifferential (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    (∃ p, IsSaddlePoint K p) ↔
      (0 : V × X) ∈ domSaddleSubdifferential Bu.flip Bx (upperConjSaddle Bu Bx K) := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, (mem_saddleSubdifferential_upperConjSaddle_zero_iff Bu Bx hF hcl hK p).2 hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, (mem_saddleSubdifferential_upperConjSaddle_zero_iff Bu Bx hF hcl hK p).1 hp⟩

end ClassSubdifferential


/-! ### Existence of a saddle-point -/

section Existence

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ Y] in
/-- If the origin lies in the relative interior of the effective domain `C* × D*` of the conjugate
class, then `K` has a saddle-point: `ri (dom K*) ⊆ dom ∂K*` makes `∂K* (0, 0)` nonempty, and that
set is the set of saddle-points. -/
theorem exists_isSaddlePoint_of_zero_mem_kernelSet_upperConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hpr : ProperConvex (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F)
    (h0 : (0 : V × X) ∈ kernelSet (upperConjSaddle Bu Bx K)) : ∃ p, IsSaddlePoint K p := by
  have hcc : ConcaveConvexFn (upperConjSaddle Bu Bx K) :=
    concaveConvexFn_upperConjSaddle Bu Bx hF hcl hK
  have hprop : ProperSaddleFn (upperConjSaddle Bu Bx K) :=
    properSaddleFn_upperConjSaddle Bu Bx hF hcl hpr hK
  have hclosed : ClosedSaddleFn (upperConjSaddle Bu Bx K) :=
    closedSaddleFn_of_mem_saddleClass (partialCl₁_lowerConjSaddle Bu Bx hF hcl hK)
      (partialCl₂_upperConjSaddle Bu Bx hF hcl hK)
      (mem_saddleClass_right (partialCl₂_upperConjSaddle Bu Bx hF hcl hK))
  have hstruct : SaddleStructure (upperConjSaddle Bu Bx K) :=
    (closedSaddleFn_iff_saddleStructure hcc hprop).1 hclosed
  have hmem := kernelSet_subset_domSaddleSubdifferential (Bu := Bu.flip) (Bx := Bx) hcc hstruct h0
  exact (exists_isSaddlePoint_iff_zero_mem_domSaddleSubdifferential Bu Bx hF hcl hK).2 hmem

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ Y] in
/-- The same with the hypothesis in the `int` form: `(0, 0) ∈ int (dom K*) = int C* × int D*`. -/
theorem exists_isSaddlePoint_of_zero_mem_interior_dom_upperConjSaddle
    (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hpr : ProperConvex (graphFn F))
    (hK : K ∈ bifunSaddleClass Bu Bx F)
    (h₁ : (0 : V) ∈ interior (dom₁ (upperConjSaddle Bu Bx K)))
    (h₂ : (0 : X) ∈ interior (dom₂ (upperConjSaddle Bu Bx K))) : ∃ p, IsSaddlePoint K p :=
  exists_isSaddlePoint_of_zero_mem_kernelSet_upperConjSaddle Bu Bx hF hcl hpr hK
    ⟨interior_subset_intrinsicInterior h₁, interior_subset_intrinsicInterior h₂⟩

end Existence

/-! ### The Lagrangian in subgradient form -/

section Lagrangian

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {F : Bifun U X} {v : V} {x : X}

/-- `(0, 0) ∈ ∂L (v, x)` exactly when `v` is a Kuhn–Tucker vector for `(P)` and `x` is an optimal
solution to `(P)`. The subgradient condition says "`(v, x)` is a saddle-point of `L`", which the
Lagrangian characterisation reads off. The pairing `Bx` is arbitrary data: the subgradient tested
there is `0`, so no property of it is used. -/
theorem zero_mem_saddleSubdifferential_saddleLagrangian_iff (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hpr : ProperConvex (graphFn F)) :
    (0 : U × Y) ∈ saddleSubdifferential Bu.flip Bx (saddleLagrangian Bu F) (v, x)
      ↔ v ∈ KuhnTucker Bu F ∧ x ∈ argmin (F 0) := by
  rw [mem_saddleSubdifferential_iff_isSaddlePoint, saddleTilt_zero]
  exact isSaddlePoint_lagrangian_iff hF hcl hpr

end Lagrangian

end ConvexAnalysis
