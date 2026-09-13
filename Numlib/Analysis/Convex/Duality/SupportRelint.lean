import Numlib.Analysis.Convex.Duality.Support
import Numlib.Analysis.Convex.RelativeInterior

/-!
# Relative interiors, interiors and affine hulls from the support function

The support function of a set records the closed half-spaces containing it, and therefore knows the
closed convex hull exactly: `x ∈ cl (conv s)` if and only if `⟨x, y⟩ ≤ δ*(y ∣ s)` for every `y`. In
finite dimensions it knows more — the relative interior, the interior and the affine hull of a
convex set can all be read off from *which* of those inequalities are strict.

The dividing line is the set of directions in which the support function is **additively
reversible**, `-δ*(-y ∣ C) = δ*(y ∣ C)`. These are exactly the directions in which `⟨·, y⟩` is
constant on `C`, i.e. along which `C` lies inside a hyperplane; no inequality can be strict there.
The relative interior asks for strictness everywhere else; the interior asks for strictness in
every direction but `0`, so there are no reversible directions to spare; and the affine hull asks
for equality in the reversible directions and nothing at all elsewhere.

## Main results

* `supportFn_neg_eq_neg_iff`, `neg_supportFn_neg_eq_iff` — the reversible directions of a support
  function are its directions of constancy.
* `mem_relint_iff_lt_supportFn`, `mem_interior_iff_lt_supportFn` — the `ri` and `int` clauses
  (Theorem 13.1 in [^1]).
* `mem_affineSpan_iff_eq_supportFn` — the `aff` clause: the affine hull of a set is the
  intersection of the hyperplanes containing it. No convexity is needed.
* `isBounded_iff_forall_bddAbove` — a set is bounded in the norm exactly when its support function
  is finite everywhere.

The closure clause is `mem_closure_convexHull_iff_le_supportFn`, in `Duality/Support.lean`; it is
the one clause of the four that holds in any locally convex space.

## Divergences from the reference

All three clauses here are genuinely finite-dimensional. Let `φ` be a discontinuous linear
functional and `C = ker φ`, a dense proper subspace: then `aff C = ri C = C` while `int C = ∅`, and
since a continuous functional constant on a dense set vanishes, the reversible directions of
`δ*(· ∣ C)` are exactly the `y` with `⟨·, y⟩ = 0` and `δ*(y ∣ C) = +∞` elsewhere. All three
conditions are then satisfied by every point of the space.

The `int` clause carries two hypotheses the book does not write. **`B.SeparatingRight`**: over `ℝⁿ`
paired with itself, `y ≠ 0` and `⟨·, y⟩ ≠ 0` are the same condition, but over a general pairing a
`y ≠ 0` pairing trivially with `E` would demand `⟨x, y⟩ = 0 < δ*(y ∣ C) = 0`. **`C.Nonempty`**: for
`C = ∅` the condition is false as soon as some `y ≠ 0` exists, and vacuously true over the zero
space, where `int ∅ = ∅`.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §13 and §1.
-/

namespace ConvexAnalysis

/-! ### Directions of constancy -/

section Constancy

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s : Set E} {y : F}

/-- **The support function in a direction of constancy is that constant.** -/
theorem supportFn_eq_coe_of_forall_eq (hs : s.Nonempty) {c : ℝ} (h : ∀ x ∈ s, B x y = c) :
    supportFn B s y = ((c : ℝ) : EReal) := by
  obtain ⟨x₀, hx₀⟩ := hs
  refine le_antisymm (supportFn_le_coe_iff.2 fun x hx => (h x hx).le) ?_
  rw [← h x₀ hx₀]
  exact le_supportFn hx₀ y

/-- **A support function is additively reversible in the direction `y` exactly when `⟨·, y⟩` is
constant on the set**: `δ*(-y | s) = -δ*(y | s)` says that the supremum and the infimum of `⟨·, y⟩`
over `s` agree. Nonemptiness is needed — for `s = ∅` both sides are `-∞` and `-(-∞) = +∞`. -/
theorem supportFn_neg_eq_neg_iff (hs : s.Nonempty) (y : F) :
    supportFn B s (-y) = -supportFn B s y ↔ ∃ c : ℝ, ∀ x ∈ s, B x y = c := by
  obtain ⟨x₀, hx₀⟩ := hs
  constructor
  · intro h
    have hbot : supportFn B s y ≠ ⊥ := supportFn_ne_bot ⟨x₀, hx₀⟩ y
    have hbot' : supportFn B s (-y) ≠ ⊥ := supportFn_ne_bot ⟨x₀, hx₀⟩ (-y)
    have htop : supportFn B s y ≠ ⊤ := by
      intro ht
      rw [ht, _root_.EReal.neg_top] at h
      exact hbot' h
    obtain ⟨c, hc⟩ :=
      EReal.exists_coe_of_ne_bot_of_lt_top hbot (lt_top_iff_ne_top.2 htop)
    refine ⟨c, fun x hx => ?_⟩
    have h1 : B x y ≤ c := supportFn_le_coe_iff.1 hc.le x hx
    have h2 : B x (-y) ≤ -c := by
      refine supportFn_le_coe_iff.1 ?_ x hx
      rw [h, hc, ← _root_.EReal.coe_neg]
    rw [map_neg] at h2
    linarith
  · rintro ⟨c, hc⟩
    have hy : supportFn B s y = ((c : ℝ) : EReal) :=
      supportFn_eq_coe_of_forall_eq ⟨x₀, hx₀⟩ hc
    have hy' : supportFn B s (-y) = ((-c : ℝ) : EReal) :=
      supportFn_eq_coe_of_forall_eq ⟨x₀, hx₀⟩ fun x hx => by rw [map_neg, hc x hx]
    rw [hy, hy', _root_.EReal.coe_neg]

/-- `supportFn_neg_eq_neg_iff` in the orientation the clauses below use:
`-δ*(-y | s) = δ*(y | s)`. -/
theorem neg_supportFn_neg_eq_iff (hs : s.Nonempty) (y : F) :
    -supportFn B s (-y) = supportFn B s y ↔ ∃ c : ℝ, ∀ x ∈ s, B x y = c := by
  rw [neg_eq_iff_eq_neg]
  exact supportFn_neg_eq_neg_iff hs y

end Constancy

/-! ### The relative interior, the interior and the affine hull -/

section FiniteDim

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {C : Set E}

/-- **A point outside the affine hull is cut away from it by a direction of constancy.** The affine
hull is closed because the dimension is finite, so a point outside it is strongly separated from
it, and a functional bounded below on an affine set is constant on it. -/
theorem exists_forall_eq_of_notMem_affineSpan (hne : C.Nonempty) {x : E}
    (hx : x ∉ affineSpan ℝ C) :
    ∃ (y : F) (c : ℝ), (∀ z ∈ C, B z y = c) ∧ B x y ≠ c := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨g, u, v, hgx, huv, hgA⟩ := geometric_hahn_banach_compact_closed
    (convex_singleton x) isCompact_singleton (affineSpan ℝ C).convex
    (affineSpan ℝ C).closed_of_finiteDimensional (Set.disjoint_singleton_left.2 hx)
  obtain ⟨y, hy⟩ := exists_pairing_eq B g
  refine ⟨y, g p, fun z hz => ?_, ?_⟩
  · rw [← hy z]
    exact eq_of_le_on_affineSubspace (fun w hw => (hgA w hw).le)
      (subset_affineSpan ℝ C hz) (subset_affineSpan ℝ C hp)
  · rw [← hy x]
    have h₁ : g x < u := hgx x rfl
    have h₂ : v < g p := hgA p (subset_affineSpan ℝ C hp)
    exact ne_of_lt (by linarith)

/-- **The `ri` clause**: a point lies in the relative interior of a convex set exactly when it
satisfies every inequality the support function records, *strictly* in every direction in which the
support function is not additively reversible.

Read through the pairing: `⟨x, y⟩ ≤ δ*(y | C)` is an equality precisely when `⟨·, y⟩` attains its
maximum over `C` at `x`, and that is compatible with `x ∈ ri C` only for a `⟨·, y⟩` constant
on `C`. -/
theorem mem_relint_iff_lt_supportFn (hC : Convex ℝ C) (x : E) :
    x ∈ ri C ↔ (∀ y : F, ((B x y : ℝ) : EReal) ≤ supportFn B C y) ∧
      ∀ y : F, -supportFn B C (-y) ≠ supportFn B C y →
        ((B x y : ℝ) : EReal) < supportFn B C y := by
  constructor
  · intro hx
    have hxC : x ∈ C := intrinsicInterior_subset hx
    refine ⟨fun y => le_supportFn hxC y, fun y hy => ?_⟩
    rcases lt_or_eq_of_le (le_supportFn (B := B) hxC y) with hlt | heq
    · exact hlt
    · exfalso
      have hmax : ∀ z ∈ C, evalCLM B y z ≤ evalCLM B y x := fun z hz => by
        simpa using supportFn_le_coe_iff.1 (le_of_eq heq.symm) z hz
      have hnc : ¬∃ c : ℝ, ∀ z ∈ C, B z y = c :=
        fun h => hy ((neg_supportFn_neg_eq_iff (B := B) ⟨x, hxC⟩ y).2 h)
      obtain ⟨z, hz, hzne⟩ : ∃ z ∈ C, B z y ≠ B x y := by
        by_contra hcon
        push Not at hcon
        exact hnc ⟨B x y, hcon⟩
      exact (notMem_relint_iff_exists_isMaxOn hC hxC).2
        ⟨evalCLM B y, hmax, z, hz, by simpa using hzne⟩ hx
  · rintro ⟨hle, hlt⟩
    have hxcl : x ∈ closure C := by
      have h := (mem_closure_convexHull_iff_le_supportFn (B := B) C x).2 hle
      rwa [hC.convexHull_eq] at h
    have hne : C.Nonempty := closure_nonempty_iff.1 ⟨x, hxcl⟩
    rw [← Convex.relint_closure hC]
    by_contra hnot
    obtain ⟨g, hmax, z, hz, hzne⟩ := (notMem_relint_iff_exists_isMaxOn hC.closure hxcl).1 hnot
    obtain ⟨y, hy⟩ := exists_pairing_eq B g
    have hsupp : supportFn B C y = ((g x : ℝ) : EReal) := by
      rw [← supportFn_closure (B := B) C]
      refine le_antisymm (supportFn_le_coe_iff.2 fun w hw => ?_) ?_
      · rw [← hy w]; exact hmax w hw
      · rw [hy x]; exact le_supportFn hxcl y
    obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ w ∈ C, B w y = c := by
      refine (neg_supportFn_neg_eq_iff (B := B) hne y).1 ?_
      by_contra hcon
      have hstrict := hlt y hcon
      rw [hsupp, ← hy x] at hstrict
      exact absurd hstrict (lt_irrefl _)
    have hclc : closure C ⊆ {w : E | B w y = c} :=
      closure_minimal (fun w hw => hc w hw)
        (isClosed_eq (continuous_pairing B y) continuous_const)
    have hz' : B z y = c := hclc hz
    have hx' : B x y = c := hclc hxcl
    exact hzne (by rw [hy z, hy x, hz', hx'])

/-- **The `int` clause**: a point lies in the interior of a nonempty convex set exactly when it
satisfies *strictly* every inequality the support function records in a nonzero direction. The
relative interior is the interior exactly when `0` is the only reversible direction, and asking for
strictness in every nonzero direction asks for both at once. -/
theorem mem_interior_iff_lt_supportFn (hC : Convex ℝ C) (hne : C.Nonempty)
    (hB : B.SeparatingRight) (x : E) :
    x ∈ interior C ↔ ∀ y : F, y ≠ 0 → ((B x y : ℝ) : EReal) < supportFn B C y := by
  constructor
  · intro hx
    have htop : affineSpan ℝ C = ⊤ := hC.interior_nonempty_iff_affineSpan_eq_top.1 ⟨x, hx⟩
    have hri : x ∈ ri C := by rwa [intrinsicInterior_eq_interior htop]
    intro y hy
    refine ((mem_relint_iff_lt_supportFn (B := B) hC x).1 hri).2 y ?_
    intro hrev
    obtain ⟨c, hc⟩ := (neg_supportFn_neg_eq_iff (B := B) hne y).1 hrev
    have hmem : ∀ w : E, w ∈ affineSpan ℝ C := by
      intro w
      rw [htop]
      exact AffineSubspace.mem_top ℝ E w
    have hEqOn : Set.EqOn (B.flip y).toAffineMap (AffineMap.const ℝ E c) C := fun w hw => hc w hw
    have hall : ∀ w : E, B w y = c := fun w => by
      simpa using AffineMap.eqOn_affineSpan hEqOn (hmem w)
    have hc0 : c = 0 := by simpa using (hall 0).symm
    exact hy (hB y fun z => by rw [hall z, hc0])
  · intro h
    have htop : affineSpan ℝ C = ⊤ := by
      by_contra hcon
      obtain ⟨p, hp⟩ : ∃ p : E, p ∉ affineSpan ℝ C := by
        by_contra hall
        push Not at hall
        exact hcon (eq_top_iff.2 fun q _ => hall q)
      obtain ⟨y, c, hc, hpc⟩ := exists_forall_eq_of_notMem_affineSpan (B := B) hne hp
      obtain ⟨w, hw⟩ := hne
      have hy0 : y ≠ 0 := by
        rintro rfl
        have hc0 : c = 0 := by simpa using (hc w hw).symm
        exact hpc (by simp [hc0])
      have h₁ : B x y < c := by
        have hlt := h y hy0
        rw [supportFn_eq_coe_of_forall_eq (B := B) ⟨w, hw⟩ hc] at hlt
        exact_mod_cast hlt
      have h₂ : B x (-y) < -c := by
        have hlt := h (-y) (neg_ne_zero.2 hy0)
        rw [supportFn_eq_coe_of_forall_eq (B := B) ⟨w, hw⟩
          fun z hz => by rw [map_neg, hc z hz]] at hlt
        exact_mod_cast hlt
      rw [map_neg] at h₂
      linarith
    rw [← intrinsicInterior_eq_interior htop, mem_relint_iff_lt_supportFn (B := B) hC x]
    refine ⟨fun y => ?_, fun y hrev => ?_⟩
    · by_cases hy : y = 0
      · subst hy
        simp [supportFn_zero hne]
      · exact (h y hy).le
    · refine h y fun hy => ?_
      subst hy
      exact hrev (by simp [supportFn_zero hne])

/-- **The `aff` clause**: the affine hull of a nonempty set is the set of points satisfying with
equality every inequality the support function records reversibly. Convexity is not needed. -/
theorem mem_affineSpan_iff_eq_supportFn (hne : C.Nonempty) (x : E) :
    x ∈ affineSpan ℝ C ↔ ∀ y : F, -supportFn B C (-y) = supportFn B C y →
      ((B x y : ℝ) : EReal) = supportFn B C y := by
  constructor
  · intro hx y hrev
    obtain ⟨c, hc⟩ := (neg_supportFn_neg_eq_iff (B := B) hne y).1 hrev
    have hEqOn : Set.EqOn (B.flip y).toAffineMap (AffineMap.const ℝ E c) C := fun w hw => hc w hw
    have hxc : B x y = c := by simpa using AffineMap.eqOn_affineSpan hEqOn hx
    rw [hxc, supportFn_eq_coe_of_forall_eq (B := B) hne hc]
  · intro h
    by_contra hx
    obtain ⟨y, c, hc, hxc⟩ := exists_forall_eq_of_notMem_affineSpan (B := B) hne hx
    have hsupp : supportFn B C y = ((c : ℝ) : EReal) :=
      supportFn_eq_coe_of_forall_eq (B := B) hne hc
    have hrev : -supportFn B C (-y) = supportFn B C y :=
      (neg_supportFn_neg_eq_iff (B := B) hne y).2 ⟨c, hc⟩
    have heq := h y hrev
    rw [hsupp] at heq
    exact hxc (by exact_mod_cast heq)

/-! ### Boundedness in the norm -/

/-- **Boundedness in the norm**: in finite dimensions a set is bounded in the norm exactly when
every `⟨·, y⟩` is bounded above on it, i.e. exactly when its support function is finite
everywhere.

`exists_supportFn_finite_iff` states the same equivalence with "bounded" read in the *pairing*
sense, and holds in any locally convex space. What is finite-dimensional here is the upgrade to
`Bornology.IsBounded`, a coordinate estimate against a finite basis. -/
theorem isBounded_iff_forall_bddAbove :
    Bornology.IsBounded C ↔ ∀ y : F, ∃ c : ℝ, ∀ x ∈ C, B x y ≤ c := by
  constructor
  · intro hb y
    obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.1 hb
    set φ : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (B.flip y)
    refine ⟨‖φ‖ * r, fun x hx => ?_⟩
    calc (B x y : ℝ) = φ x := rfl
      _ ≤ ‖φ x‖ := Real.le_norm_self _
      _ ≤ ‖φ‖ * ‖x‖ := φ.le_opNorm x
      _ ≤ ‖φ‖ * r := by
          exact mul_le_mul_of_nonneg_left (hr x hx) (norm_nonneg φ)
  · intro h
    rw [isBounded_iff_forall_norm_le]
    set b := Module.finBasis ℝ E
    have hco : ∀ i, ∃ y : F, ∀ x : E, b.coord i x = B x y := fun i =>
      exists_pairing_eq B ⟨b.coord i, LinearMap.continuous_of_finiteDimensional _⟩
    choose y hy using hco
    have hbd : ∀ i, ∃ c : ℝ, ∀ x ∈ C, |b.coord i x| ≤ c := by
      intro i
      obtain ⟨c₁, hc₁⟩ := h (y i)
      obtain ⟨c₂, hc₂⟩ := h (-(y i))
      refine ⟨max c₁ c₂, fun x hx => ?_⟩
      have h₁ : b.coord i x ≤ c₁ := by rw [hy i x]; exact hc₁ x hx
      have h₂ : -(b.coord i x) ≤ c₂ := by
        rw [hy i x, ← map_neg (B x) (y i)]
        exact hc₂ x hx
      rw [abs_le]
      exact ⟨by linarith [le_max_right c₁ c₂], by linarith [le_max_left c₁ c₂]⟩
    choose c hc using hbd
    refine ⟨∑ i, c i * ‖b i‖, fun x hx => ?_⟩
    calc ‖x‖ = ‖∑ i, b.repr x i • b i‖ := by rw [b.sum_repr]
      _ ≤ ∑ i, ‖b.repr x i • b i‖ := norm_sum_le _ _
      _ ≤ ∑ i, c i * ‖b i‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_smul, Real.norm_eq_abs, ← b.coord_apply]
          exact mul_le_mul_of_nonneg_right (hc i x hx) (norm_nonneg _)

end FiniteDim

end ConvexAnalysis
