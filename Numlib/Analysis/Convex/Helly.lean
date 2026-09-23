import Mathlib.Analysis.Convex.Radon
import Numlib.Analysis.Convex.Caratheodory
import Numlib.Analysis.Convex.Duality.Level
import Numlib.Analysis.Convex.Duality.Ops
import Numlib.Analysis.Convex.Operations.Basic
import Numlib.Analysis.Convex.Polyhedral.Separation
import Numlib.Analysis.Convex.RelativeInterior

/-!
# Systems of convex inequalities: theorems of the alternative

The engine of the section is this: for proper convex functions `f₁, …, f_m` that are finite on
`ri C`, either the strict system `fᵢ(x) < 0` has a solution in `C`, or some non-trivial
non-negative combination `λ₁f₁ + ⋯ + λ_mf_m` is non-negative on all of `C`. It is the existence
workhorse behind the Lagrange multiplier theorems.

The hypothesis `ri C ⊆ dom fᵢ` is not decoration. On `ℝ` take `f₁ x = -√x` for `x ≥ 0` and `+∞`
otherwise, `f₂ x = x`, `C = ℝ`; neither alternative holds.

The refinements that weaken the recession hypothesis of the infinite-system alternative are in
`Numlib/Analysis/Convex/HellyRefined.lean`; they share this file's tail, since
`exists_multipliers_of_posHomGen_convFn_convexConj_eq_bot` is the half of it that does not mention
recession at all.

## Main results

* `alternative_of_convex_system` — the substantial half of the alternative for a finite strict
  system ([rockafellar1970convex] Theorem 21.1); `not_exists_forall_neg_of_forall_zero_le_weighted`
  is the easy half, that the two alternatives exclude each other.
* `alternative_of_convex_system_affine` — the refinement that keeps affine constraints apart and
  so sharpens alternative (b) to "not all of the `λᵢ` on the *convex* constraints vanish".
* `helly_finite` — **Helly's theorem** for finite collections (Mathlib's `Convex.helly_theorem'`).
* `exists_mem_of_forall_subsystem`, `exists_mem_of_forall_subsystem_lt` — a finite mixed system of
  convex inequalities is solvable as soon as every subsystem of at most `n + 1` of them is.
* `sparse_alternative_of_convex_system` — the multipliers may be taken supported on at most `n + 1`
  indices.
* `alternative_infinite_system_univ`, `alternative_infinite_system` — the alternative for *weak*
  inequalities over an arbitrary index set ([rockafellar1970convex] Theorem 21.3).
* `exists_multipliers_of_posHomGen_convFn_convexConj_eq_bot` — its multiplier half, with `k(0) = -∞`
  as a hypothesis rather than a consequence of the recession assumption.
* `exists_forall_le_zero_of_forall_subsystem` — the solvability criterion for an infinite system,
  where the subsystems need only be solvable to within an arbitrary tolerance.
* `helly_of_no_common_recession` — **Helly's theorem** for an infinite family of closed convex sets
  with no common direction of recession.
* `helly_of_exists_isBounded_biInter` — when every finite subfamily has a common point, that
  recession hypothesis may be replaced by "some finite subfamily has a bounded intersection".
* `finrank_eq_of_isCompatiblePairing` — the bookkeeping lemma that lets the multiplier count be
  stated as `dim E + 1` although Carathéodory is applied in `F`.

## Implementation notes

The weighted sum is read in `EReal` with the convention `0 · ∞ = 0`: `∑ i, (l i : EReal) * f i x`
is exactly `λ₁f₁(x) + ⋯ + λ_mf_m(x)`, and a vanishing multiplier silently drops its constraint.
Multipliers are *not* normalised to sum to `1`; alternative (b) is `∑ λᵢ fᵢ(x) ≥ ε` with the `λᵢ`
unnormalised, and that is what is proved.

The affine refinement keeps the affine constraints in a separate index type — the convex
constraints in `ι`, the affine ones in `κ`, and the separating space `(ι ⊕ κ) → ℝ`. They enter as
*equations* `aⱼ(x) = z(inr j)` rather than inequalities, which is what makes the non-containment
clause of polyhedral separation usable, and they are modelled as `E →ᵃ[ℝ] ℝ` rather than as
`EReal`-valued convex functions. The unrefined alternative is the case `κ = Empty` but is proved
independently, needing only proper separation where the refinement needs the polyhedral form.

## References

* [rockafellar1970convex] §21.
-/

open Set Filter Topology

namespace ConvexAnalysis

section Exclusive

variable {E : Type*} {ι : Type*} [Fintype ι] {C : Set E} {f : ι → E → EReal}

/-- **The two alternatives exclude each other**: a point of `C` at which every `fᵢ` is negative
makes every term of `λ₁f₁ + ⋯ + λ_mf_m` non-positive, and the terms with `λᵢ ≠ 0` strictly
negative. -/
theorem not_exists_forall_neg_of_forall_zero_le_weighted {l : ι → ℝ} (hl : ∀ i, 0 ≤ l i)
    (hl0 : l ≠ 0) (h : ∀ x ∈ C, (0 : EReal) ≤ ∑ i, (l i : EReal) * f i x) :
    ¬ ∃ x ∈ C, ∀ i, f i x < 0 := by
  classical
  rintro ⟨x, hx, hneg⟩
  obtain ⟨j, hj⟩ : ∃ j, l j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hl0 (funext hcon)
  have hjpos : 0 < l j := lt_of_le_of_ne (hl j) (Ne.symm hj)
  have hterm : ∀ i, (l i : EReal) * f i x ≤ 0 := by
    intro i
    rcases eq_or_lt_of_le (hl i) with h0 | h0
    · rw [← h0]; simp
    · calc (l i : EReal) * f i x
          ≤ (l i : EReal) * 0 := by
            refine mul_le_mul_of_nonneg_left (hneg i).le ?_
            exact_mod_cast (hl i)
        _ = 0 := by simp
  have hjneg : (l j : EReal) * f j x < 0 := by
    have hlt : ¬ ((l j : EReal) * 0 ≤ (l j : EReal) * f j x) := by
      rw [EReal.coe_mul_le_coe_mul_iff hjpos]
      exact not_le.2 (hneg j)
    simpa using not_le.1 hlt
  have hrest : ∑ i ∈ Finset.univ.erase j, (l i : EReal) * f i x ≤ 0 :=
    Finset.sum_nonpos fun i _ => hterm i
  have hsum : ∑ i, (l i : EReal) * f i x < 0 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    calc (l j : EReal) * f j x + ∑ i ∈ Finset.univ.erase j, (l i : EReal) * f i x
        ≤ (l j : EReal) * f j x + 0 := add_le_add (le_refl _) hrest
      _ = (l j : EReal) * f j x := add_zero _
      _ < 0 := hjneg
  exact absurd (h x hx) (not_le.2 hsum)

end Exclusive

section Alternative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] {C : Set E} {f : ι → E → EReal}

/-- **The alternative for a finite system of strict convex inequalities.** For proper convex
functions finite on `ri C`, exactly one of the two alternatives holds: either the strict system
`fᵢ(x) < 0` is solvable in `C`, or a non-trivial non-negative combination of the `fᵢ` is
non-negative throughout `C`. This is the half with content; exclusivity is
`not_exists_forall_neg_of_forall_zero_le_weighted`. -/
theorem alternative_of_convex_system [Nonempty ι] (hC : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hp : ∀ i, ProperConvex (f i)) (hdom : ∀ i, ri C ⊆ convexDom (f i)) :
    (∃ x ∈ C, ∀ i, f i x < 0) ∨
      ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ l ≠ 0 ∧
        ∀ x ∈ C, (0 : EReal) ≤ ∑ i, (l i : EReal) * f i x := by
  classical
  by_cases halt : ∃ x ∈ C, ∀ i, f i x < 0
  · exact Or.inl halt
  refine Or.inr ?_
  have hno : ∀ x ∈ C, ∃ i, (0 : EReal) ≤ f i x := by
    intro x hx
    by_contra hcon
    push Not at hcon
    exact halt ⟨x, hx, hcon⟩
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · refine ⟨fun _ => 1, fun _ => zero_le_one, ?_, by simp⟩
    intro hzero
    have hone := congrFun hzero (Classical.arbitrary ι)
    norm_num at hone
  obtain ⟨y₀, hy₀⟩ := Convex.relint_nonempty hC hCne
  have hfinri : ∀ i, ∀ z ∈ ri C, f i z ≠ ⊤ := fun i z hz => (mem_convexDom.1 (hdom i hz)).ne
  -- the two convex sets of Rockafellar's proof, in `ι → ℝ`
  set C₁ : Set (ι → ℝ) := {z | ∃ x ∈ C, ∀ i, f i x < ((z i : ℝ) : EReal)} with hC₁def
  set C₂ : Set (ι → ℝ) := {z | ∀ i, z i ≤ 0} with hC₂def
  have hC₁conv : Convex ℝ C₁ := by
    rw [hC₁def]
    rintro z ⟨x, hx, hzx⟩ w ⟨u, hu, hwu⟩ a b ha hb hab
    refine ⟨a • x + b • u, hC hx hu ha hb hab, fun i => ?_⟩
    obtain ⟨rx, hrx⟩ := EReal.exists_coe_of_ne_bot_of_lt_top ((hp i).ne_bot x)
      (lt_of_lt_of_le (hzx i) le_top)
    obtain ⟨ru, hru⟩ := EReal.exists_coe_of_ne_bot_of_lt_top ((hp i).ne_bot u)
      (lt_of_lt_of_le (hwu i) le_top)
    have hrxlt : rx < z i := by
      have h := hzx i; rw [hrx] at h; exact_mod_cast h
    have hrult : ru < w i := by
      have h := hwu i; rw [hru] at h; exact_mod_cast h
    have hcombo : f i (a • x + b • u) ≤ (((a * rx + b * ru : ℝ)) : EReal) :=
      (hf i).epi_combo (le_of_eq hrx) (le_of_eq hru) ha hb hab
    have harith : a * rx + b * ru < a * z i + b * w i := by
      rcases eq_or_lt_of_le ha with h0 | h0
      · have hb1 : b = 1 := by linarith
        rw [← h0, hb1]; simpa using hrult
      · nlinarith
    refine lt_of_le_of_lt hcombo ?_
    have hpi : ((a • z + b • w) i : ℝ) = a * z i + b * w i := by simp
    rw [hpi]
    exact_mod_cast harith
  have hC₁ne : C₁.Nonempty := by
    refine ⟨fun i => (f i y₀).toReal + 1, ?_⟩
    rw [hC₁def]
    refine ⟨y₀, intrinsicInterior_subset hy₀, fun i => ?_⟩
    have hcoe : (((f i y₀).toReal : ℝ) : EReal) = f i y₀ :=
      EReal.coe_toReal (hfinri i y₀ hy₀) ((hp i).ne_bot y₀)
    rw [← hcoe]
    exact_mod_cast (by linarith : (f i y₀).toReal < (f i y₀).toReal + 1)
  have hC₂conv : Convex ℝ C₂ := by
    rw [hC₂def]
    intro z hz w hw a b ha hb hab i
    have hpi : ((a • z + b • w) i : ℝ) = a * z i + b * w i := by simp
    rw [hpi]
    have h1 : a * z i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha (hz i)
    have h2 : b * w i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb (hw i)
    linarith
  have hC₂ne : C₂.Nonempty := by
    refine ⟨0, ?_⟩
    rw [hC₂def]
    intro i; simp
  have hdisj : Disjoint C₁ C₂ := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    rw [hC₁def] at hz1
    rw [hC₂def] at hz2
    obtain ⟨x, hx, hzx⟩ := hz1
    obtain ⟨i, hi⟩ := hno x hx
    have hcast : ((z i : ℝ) : EReal) ≤ 0 := by exact_mod_cast hz2 i
    exact absurd (lt_of_lt_of_le (hzx i) hcast) (not_lt.2 hi)
  obtain ⟨g, c, hsep⟩ :=
    (exists_separatesProperly_iff_disjoint_relint hC₂conv hC₁conv hC₂ne hC₁ne).2
      (Disjoint.mono intrinsicInterior_subset intrinsicInterior_subset hdisj.symm)
  -- the multipliers are the coordinates of the separating functional
  set l : ι → ℝ := fun i => g (Pi.single i 1) with hldef
  have hsingle : ∀ (i : ι) (r : ℝ), (Pi.single i r : ι → ℝ) = r • Pi.single i (1 : ℝ) := by
    intro i r
    funext j
    simp [Pi.single_apply]
  have hrepr : ∀ z : ι → ℝ, g z = ∑ i, z i * l i := by
    intro z
    have hz : ∑ i, (Pi.single i (z i) : ι → ℝ) = z := Finset.univ_sum_single z
    calc g z = g (∑ i, (Pi.single i (z i) : ι → ℝ)) := by rw [hz]
      _ = ∑ i, g (Pi.single i (z i)) := map_sum _ _ _
      _ = ∑ i, z i * l i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hsingle i (z i), map_smul, smul_eq_mul, hldef]
  have hc0 : 0 ≤ c := by
    have h0 : (0 : ι → ℝ) ∈ C₂ := by rw [hC₂def]; intro i; simp
    have hle := hsep.le_of_mem_left h0
    simpa using hle
  have hlnonneg : ∀ i, 0 ≤ l i := by
    intro i
    by_contra hneg
    push Not at hneg
    have hlpos : (0 : ℝ) < -l i := by linarith
    have hNpos : 0 < (c + 1) / (-l i) := div_pos (by linarith) hlpos
    have hmem : (Pi.single i (-((c + 1) / (-l i))) : ι → ℝ) ∈ C₂ := by
      rw [hC₂def]
      intro j
      rcases eq_or_ne j i with rfl | hji
      · simp only [Pi.single_eq_same]; linarith
      · simp [Pi.single_eq_of_ne hji]
    have hle := hsep.le_of_mem_left hmem
    rw [hrepr] at hle
    have hine : l i ≠ 0 := ne_of_lt hneg
    have hval : ∑ j, (Pi.single i (-((c + 1) / (-l i))) : ι → ℝ) j * l j
        = -((c + 1) / (-l i)) * l i := by
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul])
        (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]
    rw [hval] at hle
    have hcomp : -((c + 1) / (-l i)) * l i = c + 1 := by
      rw [div_neg, neg_neg, div_mul_cancel₀ _ hine]
    rw [hcomp] at hle
    linarith
  have hlne : l ≠ 0 := by
    intro hzero
    have hg0 : ∀ z : ι → ℝ, g z = 0 := by
      intro z; rw [hrepr, hzero]; simp
    obtain ⟨z₁, hz₁⟩ := hC₁ne
    have hc1 : c ≤ 0 := by
      have hle := hsep.le_of_mem_right hz₁
      rwa [hg0] at hle
    have hceq : c = 0 := le_antisymm hc1 hc0
    exact hsep.not_subset fun z _ => by simp [hg0 z, hceq]
  have hkey : ∀ z ∈ C₁, 0 ≤ ∑ i, z i * l i := by
    intro z hz
    have hle := hsep.le_of_mem_right hz
    rw [hrepr] at hle
    linarith
  -- the weighted sum, and its real value on `ri C`
  have hsumcoe : ∀ z ∈ ri C, ∑ i, (l i : EReal) * f i z
      = ((∑ i, (f i z).toReal * l i : ℝ) : EReal) := by
    intro z hz
    rw [EReal.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcoe : (((f i z).toReal : ℝ) : EReal) = f i z :=
      EReal.coe_toReal (hfinri i z hz) ((hp i).ne_bot z)
    rw [mul_comm, EReal.coe_mul, hcoe]
  have hri : ∀ z ∈ ri C, (0 : EReal) ≤ ∑ i, (l i : EReal) * f i z := by
    intro z hz
    have hzC : z ∈ C := intrinsicInterior_subset hz
    have hcoe : ∀ i, (((f i z).toReal : ℝ) : EReal) = f i z :=
      fun i => EReal.coe_toReal (hfinri i z hz) ((hp i).ne_bot z)
    have hstep : ∀ ε : ℝ, 0 < ε → 0 ≤ ∑ i, ((f i z).toReal + ε) * l i := by
      intro ε hε
      refine hkey _ ?_
      rw [hC₁def]
      refine ⟨z, hzC, fun i => ?_⟩
      rw [← hcoe i]
      exact_mod_cast (by linarith : (f i z).toReal < (f i z).toReal + ε)
    have hexp : ∀ ε : ℝ, ∑ i, ((f i z).toReal + ε) * l i
        = (∑ i, (f i z).toReal * l i) + ε * ∑ i, l i := by
      intro ε
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hA : 0 ≤ ∑ i, (f i z).toReal * l i := by
      by_contra hcon
      push Not at hcon
      have hLnn : (0 : ℝ) ≤ ∑ i, l i := Finset.sum_nonneg fun i _ => hlnonneg i
      have hLpos : (0 : ℝ) < (∑ i, l i) + 1 := by linarith
      have hεpos : 0 < -(∑ i, (f i z).toReal * l i) / ((∑ i, l i) + 1) :=
        div_pos (by linarith) hLpos
      have h1 := hstep _ hεpos
      rw [hexp] at h1
      have h2 : (∑ i, (f i z).toReal * l i)
          + (-(∑ i, (f i z).toReal * l i) / ((∑ i, l i) + 1)) * ∑ i, l i
          = (∑ i, (f i z).toReal * l i) / ((∑ i, l i) + 1) := by
        field_simp
        ring
      rw [h2] at h1
      have h3 := (le_div_iff₀ hLpos).1 h1
      simp only [zero_mul] at h3
      linarith
    rw [hsumcoe z hz]
    exact_mod_cast hA
  -- `ConvexFn.le_of_mem_closure` carries the bound from `ri C` to `C`
  refine ⟨l, hlnonneg, hlne, fun x hx => ?_⟩
  have hgconv : ConvexFn (fun x => ∑ i, (l i : EReal) * f i x) :=
    ConvexFn.sum (fun i _ => convexFn_coe_mul (hlnonneg i) (hf i))
      (fun i _ x => EReal.coe_mul_ne_bot (hlnonneg i) ((hp i).ne_bot x))
  have hgbot : ∀ z, (∑ i, (l i : EReal) * f i z) ≠ ⊥ := fun z =>
    EReal.sum_ne_bot fun i _ => EReal.coe_mul_ne_bot (hlnonneg i) ((hp i).ne_bot z)
  have hgfin : ∀ z ∈ ri C, (∑ i, (l i : EReal) * f i z) ≠ ⊤ := by
    intro z hz
    rw [hsumcoe z hz]
    exact EReal.coe_ne_top _
  have hxcl : x ∈ closure (ri C) := by
    rw [Convex.closure_relint hC]; exact subset_closure hx
  have hfinal := hgconv.le_of_mem_closure hgbot (Convex.relint hC) hgfin (c := 0)
    (fun z hz => by simpa using hri z hz) hxcl
  simpa using hfinal

end Alternative

/-! ### The alternative with affine constraints -/

section AffineSum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {κ : Type*} [Fintype κ] {C : Set E} {a : κ → (E →ᵃ[ℝ] ℝ)}

omit [FiniteDimensional ℝ E] in
/-- A finite real combination of affine functions is affine along segments. -/
theorem combo_affine_sum (μ : κ → ℝ) {s t : ℝ} (hst : s + t = 1) (x y : E) :
    (∑ j, μ j * a j (s • x + t • y)) = s * (∑ j, μ j * a j x) + t * (∑ j, μ j * a j y) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Convex.combo_affine_apply hst]
  simp only [smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] in
/-- Such a combination, read in `EReal`, is convex — it is in fact affine. -/
theorem convexFn_coe_affine_sum (μ : κ → ℝ) :
    ConvexFn (fun x => ((∑ j, μ j * a j x : ℝ) : EReal)) := by
  refine convexFn_of_epi_combo fun x y p q hx hy s t hs ht hst => ?_
  rw [EReal.coe_le_coe_iff] at hx hy ⊢
  rw [combo_affine_sum μ hst]
  nlinarith [mul_le_mul_of_nonneg_left hx hs, mul_le_mul_of_nonneg_left hy ht]

omit [FiniteDimensional ℝ E] in
/-- The affine step: a combination of affine functions that is non-negative on a convex set `C` and
non-positive at a relative interior point of `C` vanishes on all of `C`. This is the affine
analogue of `eq_zero_of_nonpos_of_mem_relint`, and the reason the multipliers on the convex
constraints cannot all vanish. -/
theorem eq_zero_of_nonneg_of_mem_relint_affine_sum (μ : κ → ℝ) {z : E} (hz : z ∈ ri C)
    (hnonneg : ∀ x ∈ C, 0 ≤ ∑ j, μ j * a j x) (hz0 : (∑ j, μ j * a j z) ≤ 0) :
    ∀ x ∈ C, (∑ j, μ j * a j x) = 0 := by
  have hzC : z ∈ C := intrinsicInterior_subset hz
  have hFz : (∑ j, μ j * a j z) = 0 := le_antisymm hz0 (hnonneg z hzC)
  intro x hx
  refine le_antisymm ?_ (hnonneg x hx)
  obtain ⟨ν, hν, hw⟩ := exists_one_lt_smul_mem_of_mem_relint hz (subset_affineSpan ℝ C hx)
  have hval := combo_affine_sum (a := a) μ (s := 1 - ν) (t := ν) (by ring) x z
  have hcon := hnonneg _ hw
  rw [hval, hFz] at hcon
  nlinarith

end AffineSum

section Orthant

/-- The non-positive orthant of `σ → ℝ` is polyhedral: it is cut out by the coordinate
projections. -/
theorem polyhedral_nonpos_orthant (σ : Type*) [Finite σ] :
    Polyhedral {z : σ → ℝ | ∀ s, z s ≤ 0} := by
  classical
  have : Fintype σ := Fintype.ofFinite σ
  refine ⟨Finset.univ.image (fun s : σ => (LinearMap.proj s, (0 : ℝ))), ?_⟩
  ext z
  constructor
  · rintro hz q hq
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hq
    obtain ⟨s, rfl⟩ := hq
    simpa using hz s
  · intro hz s
    simpa using hz (LinearMap.proj s, (0 : ℝ)) (by simp)

end Orthant

section AffineAlternative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {C : Set E} {f : ι → E → EReal}
variable {a : κ → (E →ᵃ[ℝ] ℝ)}

/-- **The alternative with affine constraints treated separately.** If the affine system
`a_j x ≤ 0` is solvable in `ri C`, then either the mixed system `f_i x < 0`, `a_j x ≤ 0` is
solvable in `C`, or there are non-negative multipliers — *not all of the `λ_i` zero* — making the
combined function non-negative on `C`. The unrefined alternative is the case `κ = Empty`; what the
affine constraints buy is the sharper conclusion `l ≠ 0`, at the price of needing polyhedral
separation rather than proper separation. -/
theorem alternative_of_convex_system_affine (hC : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hp : ∀ i, ProperConvex (f i)) (hdom : ∀ i, ri C ⊆ convexDom (f i))
    (hfeas : ∃ x ∈ ri C, ∀ j, a j x ≤ 0) :
    (∃ x ∈ C, (∀ i, f i x < 0) ∧ ∀ j, a j x ≤ 0) ∨
      ∃ (l : ι → ℝ) (μ : κ → ℝ), (∀ i, 0 ≤ l i) ∧ (∀ j, 0 ≤ μ j) ∧ l ≠ 0 ∧
        ∀ x ∈ C, (0 : EReal)
          ≤ (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * a j x : ℝ) : EReal) := by
  classical
  by_cases halt : ∃ x ∈ C, (∀ i, f i x < 0) ∧ ∀ j, a j x ≤ 0
  · exact Or.inl halt
  refine Or.inr ?_
  obtain ⟨y₀, hy₀, hy₀a⟩ := hfeas
  have hy₀C : y₀ ∈ C := intrinsicInterior_subset hy₀
  have hfinri : ∀ i, ∀ z ∈ ri C, f i z ≠ ⊤ := fun i z hz => (mem_convexDom.1 (hdom i hz)).ne
  -- Rockafellar's two sets, in `(ι ⊕ κ) → ℝ`
  set D₁ : Set (ι ⊕ κ → ℝ) :=
    {z | ∃ x ∈ C, (∀ i, f i x < ((z (Sum.inl i) : ℝ) : EReal)) ∧ ∀ j, a j x = z (Sum.inr j)}
    with hD₁def
  set D₂ : Set (ι ⊕ κ → ℝ) := {z | ∀ s, z s ≤ 0} with hD₂def
  have hD₂poly : Polyhedral D₂ := by rw [hD₂def]; exact polyhedral_nonpos_orthant _
  have hD₁conv : Convex ℝ D₁ := by
    rw [hD₁def]
    rintro z ⟨x, hx, hzx, hax⟩ w ⟨u, hu, hwu, hau⟩ p q hpp hqq hpq
    refine ⟨p • x + q • u, hC hx hu hpp hqq hpq, fun i => ?_, fun j => ?_⟩
    · obtain ⟨rx, hrx⟩ := EReal.exists_coe_of_ne_bot_of_lt_top ((hp i).ne_bot x)
        (lt_of_lt_of_le (hzx i) le_top)
      obtain ⟨ru, hru⟩ := EReal.exists_coe_of_ne_bot_of_lt_top ((hp i).ne_bot u)
        (lt_of_lt_of_le (hwu i) le_top)
      have hrxlt : rx < z (Sum.inl i) := by
        have h := hzx i; rw [hrx] at h; exact_mod_cast h
      have hrult : ru < w (Sum.inl i) := by
        have h := hwu i; rw [hru] at h; exact_mod_cast h
      have hcombo : f i (p • x + q • u) ≤ (((p * rx + q * ru : ℝ)) : EReal) :=
        (hf i).epi_combo (le_of_eq hrx) (le_of_eq hru) hpp hqq hpq
      have harith : p * rx + q * ru < p * z (Sum.inl i) + q * w (Sum.inl i) := by
        rcases eq_or_lt_of_le hpp with h0 | h0
        · have hq1 : q = 1 := by linarith
          rw [← h0, hq1]; simpa using hrult
        · nlinarith
      refine lt_of_le_of_lt hcombo ?_
      have hpi : ((p • z + q • w) (Sum.inl i) : ℝ)
          = p * z (Sum.inl i) + q * w (Sum.inl i) := by simp
      rw [hpi]
      exact_mod_cast harith
    · have hpi : ((p • z + q • w) (Sum.inr j) : ℝ)
          = p * z (Sum.inr j) + q * w (Sum.inr j) := by simp
      rw [hpi, ← hax j, ← hau j, Convex.combo_affine_apply hpq]
      simp
  have hD₁ne : D₁.Nonempty := by
    refine ⟨Sum.elim (fun i => (f i y₀).toReal + 1) (fun j => a j y₀), ?_⟩
    rw [hD₁def]
    refine ⟨y₀, hy₀C, fun i => ?_, fun j => by simp⟩
    have hcoe : (((f i y₀).toReal : ℝ) : EReal) = f i y₀ :=
      EReal.coe_toReal (hfinri i y₀ hy₀) ((hp i).ne_bot y₀)
    simp only [Sum.elim_inl]
    rw [← hcoe]
    exact_mod_cast (by linarith : (f i y₀).toReal < (f i y₀).toReal + 1)
  have hdisj : Disjoint D₁ D₂ := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    rw [hD₁def] at hz1
    rw [hD₂def] at hz2
    obtain ⟨x, hx, hzx, hax⟩ := hz1
    refine halt ⟨x, hx, fun i => ?_, fun j => ?_⟩
    · exact lt_of_lt_of_le (hzx i) (by exact_mod_cast hz2 (Sum.inl i))
    · rw [hax j]; exact hz2 (Sum.inr j)
  obtain ⟨g, α, hsep, hns⟩ :=
    (exists_separates_not_subset_iff_disjoint_relint hD₂poly hD₁conv hD₁ne).2
      (Disjoint.mono_right intrinsicInterior_subset hdisj.symm)
  -- the multipliers are the coordinates of the separating functional
  set w : (ι ⊕ κ) → ℝ := fun s => g (Pi.single s 1) with hwdef
  have hsingle : ∀ (s : ι ⊕ κ) (r : ℝ),
      (Pi.single s r : (ι ⊕ κ) → ℝ) = r • Pi.single s (1 : ℝ) := by
    intro s r
    funext t
    simp [Pi.single_apply]
  have hrepr : ∀ z : (ι ⊕ κ) → ℝ, g z = ∑ s, w s * z s := by
    intro z
    have hz : ∑ s, (Pi.single s (z s) : (ι ⊕ κ) → ℝ) = z := Finset.univ_sum_single z
    calc g z = g (∑ s, (Pi.single s (z s) : (ι ⊕ κ) → ℝ)) := by rw [hz]
      _ = ∑ s, g (Pi.single s (z s)) := map_sum _ _ _
      _ = ∑ s, w s * z s := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [hsingle s (z s), map_smul, smul_eq_mul, hwdef, mul_comm]
  have hα0 : 0 ≤ α := by
    have h0 : (0 : (ι ⊕ κ) → ℝ) ∈ D₂ := by rw [hD₂def]; intro s; simp
    simpa using hsep.le_of_mem_left h0
  have hwnonneg : ∀ s, 0 ≤ w s := by
    intro s
    by_contra hneg
    push Not at hneg
    have hwne : w s ≠ 0 := ne_of_lt hneg
    have hpos : (0 : ℝ) < -w s := by linarith
    have hmem : (Pi.single s (-((α + 1) / (-w s))) : (ι ⊕ κ) → ℝ) ∈ D₂ := by
      rw [hD₂def]
      intro t
      rcases eq_or_ne t s with hts | hts
      · rw [hts, Pi.single_eq_same]
        have hq : 0 < (α + 1) / (-w s) := div_pos (by linarith) hpos
        linarith
      · simp [Pi.single_eq_of_ne hts]
    have hle := hsep.le_of_mem_left hmem
    rw [hrepr] at hle
    have hvalue : ∑ t, w t * (Pi.single s (-((α + 1) / (-w s))) : (ι ⊕ κ) → ℝ) t
        = w s * -((α + 1) / (-w s)) := by
      rw [Finset.sum_eq_single s (fun t _ ht => by rw [Pi.single_eq_of_ne ht, mul_zero])
        (fun h => absurd (Finset.mem_univ s) h), Pi.single_eq_same]
    rw [hvalue] at hle
    have hcomp : w s * -((α + 1) / (-w s)) = α + 1 := by
      rw [div_neg, neg_neg, mul_comm, div_mul_cancel₀ _ hwne]
    rw [hcomp] at hle
    linarith
  have hkey : ∀ z ∈ D₁, α ≤ ∑ s, w s * z s := by
    intro z hz
    have hle := hsep.le_of_mem_right hz
    rwa [hrepr] at hle
  -- the value of the combination on `ri C`
  have hval : ∀ x ∈ ri C, α ≤ (∑ i, w (Sum.inl i) * (f i x).toReal)
      + ∑ j, w (Sum.inr j) * a j x := by
    intro x hx
    have hxC : x ∈ C := intrinsicInterior_subset hx
    have hcoe : ∀ i, (((f i x).toReal : ℝ) : EReal) = f i x :=
      fun i => EReal.coe_toReal (hfinri i x hx) ((hp i).ne_bot x)
    have hstep : ∀ ε : ℝ, 0 < ε → α ≤ (∑ i, w (Sum.inl i) * ((f i x).toReal + ε))
        + ∑ j, w (Sum.inr j) * a j x := by
      intro ε hε
      have hz : Sum.elim (fun i => (f i x).toReal + ε) (fun j => a j x) ∈ D₁ := by
        rw [hD₁def]
        refine ⟨x, hxC, fun i => ?_, fun j => by simp⟩
        simp only [Sum.elim_inl]
        rw [← hcoe i]
        exact_mod_cast (by linarith : (f i x).toReal < (f i x).toReal + ε)
      have h := hkey _ hz
      rw [Fintype.sum_sum_type] at h
      simpa using h
    by_contra hcon
    push Not at hcon
    set A := ∑ i, w (Sum.inl i) * (f i x).toReal with hAdef
    set B := ∑ j, w (Sum.inr j) * a j x with hBdef
    set L := ∑ i, w (Sum.inl i) with hLdef
    have hLnn : (0 : ℝ) ≤ L := Finset.sum_nonneg fun i _ => hwnonneg _
    have hLpos : (0 : ℝ) < L + 1 := by linarith
    have hδ : 0 < α - (A + B) := by linarith
    have hεpos : 0 < (α - (A + B)) / (L + 1) := div_pos hδ hLpos
    have hexp : ∑ i, w (Sum.inl i) * ((f i x).toReal + (α - (A + B)) / (L + 1))
        = A + ((α - (A + B)) / (L + 1)) * L := by
      rw [hAdef, hLdef, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h1 := hstep _ hεpos
    rw [hexp] at h1
    have h2 : ((α - (A + B)) / (L + 1)) * L < α - (A + B) := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hLpos]
      nlinarith
    linarith
  -- `ConvexFn.le_of_mem_closure` carries the bound from `ri C` to `C`
  have hAconv : ConvexFn (fun x => ∑ i, (w (Sum.inl i) : EReal) * f i x) :=
    ConvexFn.sum (fun i _ => convexFn_coe_mul (hwnonneg _) (hf i))
      (fun i _ x => EReal.coe_mul_ne_bot (hwnonneg _) ((hp i).ne_bot x))
  have hAbot : ∀ x, (∑ i, (w (Sum.inl i) : EReal) * f i x) ≠ ⊥ := fun x =>
    EReal.sum_ne_bot fun i _ => EReal.coe_mul_ne_bot (hwnonneg _) ((hp i).ne_bot x)
  have hFconv : ConvexFn (fun x => (∑ i, (w (Sum.inl i) : EReal) * f i x)
      + ((∑ j, w (Sum.inr j) * a j x : ℝ) : EReal)) :=
    hAconv.add (convexFn_coe_affine_sum _) hAbot (fun x => EReal.coe_ne_bot _)
  have hFbot : ∀ x, ((∑ i, (w (Sum.inl i) : EReal) * f i x)
      + ((∑ j, w (Sum.inr j) * a j x : ℝ) : EReal)) ≠ ⊥ := fun x =>
    EReal.add_ne_bot_iff.2 ⟨hAbot x, EReal.coe_ne_bot _⟩
  have hFcoe : ∀ x ∈ ri C, (∑ i, (w (Sum.inl i) : EReal) * f i x)
      + ((∑ j, w (Sum.inr j) * a j x : ℝ) : EReal)
      = (((∑ i, w (Sum.inl i) * (f i x).toReal) + ∑ j, w (Sum.inr j) * a j x : ℝ) : EReal) := by
    intro x hx
    rw [EReal.coe_add]
    congr 1
    rw [EReal.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcoe : (((f i x).toReal : ℝ) : EReal) = f i x :=
      EReal.coe_toReal (hfinri i x hx) ((hp i).ne_bot x)
    rw [EReal.coe_mul, hcoe]
  have hFC : ∀ x ∈ C, ((α : ℝ) : EReal) ≤ (∑ i, (w (Sum.inl i) : EReal) * f i x)
      + ((∑ j, w (Sum.inr j) * a j x : ℝ) : EReal) := by
    intro x hx
    have hxcl : x ∈ closure (ri C) := by
      rw [Convex.closure_relint hC]; exact subset_closure hx
    refine hFconv.le_of_mem_closure hFbot (Convex.relint hC) ?_ ?_ hxcl
    · intro z hz
      rw [hFcoe z hz]
      exact EReal.coe_ne_top _
    · intro z hz
      rw [hFcoe z hz]
      exact_mod_cast hval z hz
  -- the multipliers on the convex constraints are not all zero
  have hlne : (fun i => w (Sum.inl i)) ≠ (0 : ι → ℝ) := by
    intro hzero
    have hw0 : ∀ i, w (Sum.inl i) = 0 := fun i => congrFun hzero i
    have haff : ∀ x ∈ C, α ≤ ∑ j, w (Sum.inr j) * a j x := by
      intro x hx
      have h := hFC x hx
      have hz : (∑ i, (w (Sum.inl i) : EReal) * f i x) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hw0 i]
        simp
      rw [hz, zero_add] at h
      exact_mod_cast h
    have hy₀le : (∑ j, w (Sum.inr j) * a j y₀) ≤ 0 :=
      Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hwnonneg _) (hy₀a j)
    have hα : α = 0 := le_antisymm (le_trans (haff y₀ hy₀C) hy₀le) hα0
    have hconst : ∀ x ∈ C, (∑ j, w (Sum.inr j) * a j x) = 0 :=
      eq_zero_of_nonneg_of_mem_relint_affine_sum (a := a) _ hy₀
        (fun x hx => by rw [← hα]; exact haff x hx) hy₀le
    obtain ⟨z, hzD, hzne⟩ := Set.not_subset.1 hns
    have hzlt : α < g z := lt_of_le_of_ne (hsep.le_of_mem_right hzD) (Ne.symm hzne)
    rw [hD₁def] at hzD
    obtain ⟨x, hx, _, hax⟩ := hzD
    have hgz : g z = 0 := by
      rw [hrepr, Fintype.sum_sum_type]
      have h1 : ∑ i, w (Sum.inl i) * z (Sum.inl i) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hw0 i, zero_mul]
      have h2 : ∑ j, w (Sum.inr j) * z (Sum.inr j) = 0 := by
        rw [show (∑ j, w (Sum.inr j) * z (Sum.inr j))
          = ∑ j, w (Sum.inr j) * a j x from Finset.sum_congr rfl fun j _ => by rw [hax j]]
        exact hconst x hx
      rw [h1, h2, add_zero]
    rw [hgz, hα] at hzlt
    exact lt_irrefl 0 hzlt
  refine ⟨fun i => w (Sum.inl i), fun j => w (Sum.inr j), fun i => hwnonneg _,
    fun j => hwnonneg _, hlne, fun x hx => ?_⟩
  exact le_trans (by exact_mod_cast hα0) (hFC x hx)

end AffineAlternative

/-! ### Helly's theorem and its corollaries: finite collections -/

section Finite

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} {C : Set E} {f : ι → E → EReal} {g : κ → E → EReal}

/-- **Helly's theorem** for finite collections: a finite collection of convex sets in an
`n`-dimensional space has a common point as soon as every `n + 1` of them do. No closedness and no
recession hypothesis is needed — that is what distinguishes it from the infinite version
`helly_of_no_common_recession`. This is Mathlib's `Convex.helly_theorem'`, restated. -/
theorem helly_finite {F : ι → Set E} {s : Finset ι} (hconv : ∀ i ∈ s, Convex ℝ (F i))
    (hinter : ∀ I ⊆ s, I.card ≤ Module.finrank ℝ E + 1 → (⋂ i ∈ I, F i).Nonempty) :
    (⋂ i ∈ s, F i).Nonempty :=
  Convex.helly_theorem' hconv hinter

/-- **A finite system of convex inequalities** — some strict, some weak — is solvable in a convex
set `C` as soon as every subsystem of at most `n + 1` inequalities is solvable in `C`. Counting is
the only fiddly point: a subcollection of at most `n + 1` of the sets `C`, `{fᵢ < 0}`, `{gⱼ ≤ 0}`
uses at most `n + 1` of the inequalities whether or not it also uses `C`. -/
theorem exists_mem_of_forall_subsystem [Finite ι] [Finite κ] (hC : Convex ℝ C)
    (hf : ∀ i, ConvexFn (f i)) (hg : ∀ j, ConvexFn (g j))
    (hsub : ∀ (S : Finset ι) (T : Finset κ), S.card + T.card ≤ Module.finrank ℝ E + 1 →
      ∃ x ∈ C, (∀ i ∈ S, f i x < 0) ∧ ∀ j ∈ T, g j x ≤ 0) :
    ∃ x ∈ C, (∀ i, f i x < 0) ∧ ∀ j, g j x ≤ 0 := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have : Fintype κ := Fintype.ofFinite κ
  let F : Option (ι ⊕ κ) → Set E := fun o =>
    match o with
    | none => C
    | some (Sum.inl i) => {x | f i x < 0}
    | some (Sum.inr j) => {x | g j x ≤ 0}
  have hconv : ∀ o ∈ (Finset.univ : Finset (Option (ι ⊕ κ))), Convex ℝ (F o) := by
    rintro (_ | (i | j)) _
    · exact hC
    · exact (hf i).convex_lt 0
    · exact (hg j).convex_le 0
  have hinter : ∀ I ⊆ (Finset.univ : Finset (Option (ι ⊕ κ))),
      I.card ≤ Module.finrank ℝ E + 1 → (⋂ o ∈ I, F o).Nonempty := by
    intro I _ hcard
    set S : Finset ι := Finset.univ.filter (fun i => some (Sum.inl i) ∈ I) with hSdef
    set T : Finset κ := Finset.univ.filter (fun j => some (Sum.inr j) ∈ I) with hTdef
    have hSinj : Function.Injective (fun i : ι => (some (Sum.inl i) : Option (ι ⊕ κ))) := by
      intro i i' h
      simpa using h
    have hTinj : Function.Injective (fun j : κ => (some (Sum.inr j) : Option (ι ⊕ κ))) := by
      intro j j' h
      simpa using h
    have hdisj : Disjoint (S.image (fun i : ι => (some (Sum.inl i) : Option (ι ⊕ κ))))
        (T.image (fun j : κ => (some (Sum.inr j) : Option (ι ⊕ κ)))) := by
      simp only [Finset.disjoint_left, Finset.mem_image]
      rintro o ⟨i, _, rfl⟩ ⟨j, _, hj⟩
      simp at hj
    have hsubI : S.image (fun i : ι => (some (Sum.inl i) : Option (ι ⊕ κ)))
        ∪ T.image (fun j : κ => (some (Sum.inr j) : Option (ι ⊕ κ))) ⊆ I := by
      intro o ho
      simp only [Finset.mem_union, Finset.mem_image, hSdef, hTdef, Finset.mem_filter,
        Finset.mem_univ, true_and] at ho
      rcases ho with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
      · exact hi
      · exact hj
    have hle : S.card + T.card ≤ I.card := by
      rw [← Finset.card_image_of_injective S hSinj, ← Finset.card_image_of_injective T hTinj,
        ← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card hsubI
    obtain ⟨x, hxC, hxf, hxg⟩ := hsub S T (le_trans hle hcard)
    refine ⟨x, ?_⟩
    simp only [Set.mem_iInter]
    rintro (_ | (i | j)) ho
    · exact hxC
    · exact hxf i (by simp [hSdef, ho])
    · exact hxg j (by simp [hTdef, ho])
  obtain ⟨x, hx⟩ := helly_finite hconv hinter
  simp only [Set.mem_iInter] at hx
  exact ⟨x, hx none (Finset.mem_univ _), fun i => hx (some (Sum.inl i)) (Finset.mem_univ _),
    fun j => hx (some (Sum.inr j)) (Finset.mem_univ _)⟩

/-- The same for a system of strict inequalities only — the form the sparse alternative uses. -/
theorem exists_mem_of_forall_subsystem_lt [Finite ι] (hC : Convex ℝ C)
    (hf : ∀ i, ConvexFn (f i))
    (hsub : ∀ S : Finset ι, S.card ≤ Module.finrank ℝ E + 1 → ∃ x ∈ C, ∀ i ∈ S, f i x < 0) :
    ∃ x ∈ C, ∀ i, f i x < 0 := by
  obtain ⟨x, hx, hxf, -⟩ :=
    exists_mem_of_forall_subsystem (κ := Empty) (g := fun j => j.elim) hC hf (fun j => j.elim)
      (fun S T hcard => by
        obtain ⟨x, hx, hxf⟩ := hsub S (le_trans (Nat.le_add_right _ _) hcard)
        exact ⟨x, hx, hxf, fun j => j.elim⟩)
  exact ⟨x, hx, hxf⟩

variable [Fintype ι]

/-- **The multipliers can be chosen supported on at most `n + 1` indices**: if alternative (a)
fails, it already fails for a subsystem of at most `n + 1` inequalities, and the multipliers the
alternative produces for that subsystem extend by zero — harmless in `EReal` because
`0 · (+∞) = 0`. -/
theorem sparse_alternative_of_convex_system [Nonempty ι] (hC : Convex ℝ C)
    (hf : ∀ i, ConvexFn (f i)) (hp : ∀ i, ProperConvex (f i)) (hdom : ∀ i, ri C ⊆ convexDom (f i)) :
    (∃ x ∈ C, ∀ i, f i x < 0) ∨
      ∃ (S : Finset ι) (l : ι → ℝ), S.card ≤ Module.finrank ℝ E + 1 ∧ (∀ i ∉ S, l i = 0) ∧
        (∀ i, 0 ≤ l i) ∧ l ≠ 0 ∧ ∀ x ∈ C, (0 : EReal) ≤ ∑ i, (l i : EReal) * f i x := by
  classical
  by_cases halt : ∃ x ∈ C, ∀ i, f i x < 0
  · exact Or.inl halt
  refine Or.inr ?_
  -- alternative (a) already fails for a subsystem of at most `n + 1` inequalities
  have hsmall : ∃ S : Finset ι, S.card ≤ Module.finrank ℝ E + 1
      ∧ ¬ ∃ x ∈ C, ∀ i ∈ S, f i x < 0 := by
    by_contra hcon
    push Not at hcon
    exact halt (exists_mem_of_forall_subsystem_lt hC hf hcon)
  obtain ⟨S, hScard, hSalt⟩ := hsmall
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · -- an empty subsystem can only fail because `C` itself is empty
    have hCempty : C = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      exact fun x hx => hSalt ⟨x, hx, by simp⟩
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    refine ⟨{i₀}, fun i => if i = i₀ then 1 else 0, by simp, ?_, ?_, ?_, ?_⟩
    · intro i hi
      simp only [Finset.mem_singleton] at hi
      simp [hi]
    · intro i; positivity
    · intro hzero
      have h := congrFun hzero i₀
      simp at h
    · intro x hx
      rw [hCempty] at hx
      exact absurd hx (Set.notMem_empty x)
  -- the finite alternative, applied to the subsystem
  have hSnonempty : Nonempty (↥S) := hSne.to_subtype
  obtain hsolv | ⟨l', hl'0, hl'ne, hl'⟩ :=
    alternative_of_convex_system (ι := ↥S) (f := fun i : ↥S => f i) hC
      (fun i => hf i) (fun i => hp i) (fun i => hdom i)
  · exact absurd ⟨hsolv.choose, hsolv.choose_spec.1,
      fun i hi => hsolv.choose_spec.2 ⟨i, hi⟩⟩ hSalt
  refine ⟨S, fun i => if h : i ∈ S then l' ⟨i, h⟩ else 0, hScard, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp [hi]
  · intro i
    by_cases h : i ∈ S
    · simpa [h] using hl'0 ⟨i, h⟩
    · simp [h]
  · intro hzero
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : ↥S, l' i₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hl'ne (funext hcon)
    have h := congrFun hzero (i₀ : ι)
    simp only [i₀.2, Pi.zero_apply, Subtype.coe_eta, ↓reduceDIte] at h
    exact hi₀ h
  · intro x hx
    have hshrink : ∑ i, ((if h : i ∈ S then l' ⟨i, h⟩ else 0 : ℝ) : EReal) * f i x
        = ∑ i ∈ S, ((if h : i ∈ S then l' ⟨i, h⟩ else 0 : ℝ) : EReal) * f i x := by
      refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
      intro i _ hi
      simp [hi]
    rw [hshrink, ← Finset.sum_coe_sort S]
    have hcongr : ∀ i : ↥S, ((if h : (i : ι) ∈ S then l' ⟨(i : ι), h⟩ else 0 : ℝ) : EReal)
        * f i x = (l' i : EReal) * f i x := by
      intro i
      simp only [i.2, Subtype.coe_eta, ↓reduceDIte]
    rw [Finset.sum_congr rfl fun i _ => hcongr i]
    exact hl' x hx

end Finite

/-! ### Weak inequalities over an arbitrary index set

The proof runs on two prerequisites: `convexCl_posHomGen` identifies the conjugate of the positively
homogeneous convex function `k` generated by `h = conv {fᵢ* | i ∈ I}`, and
`exists_affineIndependent_of_convFn_lt` extracts finitely many multipliers from `h(0) < 0`. -/

section Infinite

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {ι : Type*} {f : ι → E → EReal} {C : Set E}

/-- In finite dimensions a **compatible pairing forces the two spaces to have equal dimension**:
`evalCLM B` and `evalCLM B.flip` are surjective onto the two continuous duals, which in finite
dimensions have the dimension of the space. This is what lets the multiplier count be stated as
`n + 1` with `n = dim E`, although Carathéodory is applied in `F`. -/
theorem finrank_eq_of_isCompatiblePairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [IsCompatiblePairing B] [IsCompatiblePairing B.flip] :
    Module.finrank ℝ F = Module.finrank ℝ E := by
  have hE : Module.finrank ℝ (StrongDual ℝ E) = Module.finrank ℝ E := by
    rw [← LinearEquiv.finrank_eq
      (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ))]
    exact Subspace.dual_finrank_eq
  have hF : Module.finrank ℝ (StrongDual ℝ F) = Module.finrank ℝ F := by
    rw [← LinearEquiv.finrank_eq
      (LinearMap.toContinuousLinearMap : (F →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (F →L[ℝ] ℝ))]
    exact Subspace.dual_finrank_eq
  have h₁ := LinearMap.finrank_le_finrank_of_surjective
    (IsCompatiblePairing.surjective_eval B)
  have h₂ := LinearMap.finrank_le_finrank_of_surjective
    (IsCompatiblePairing.surjective_eval B.flip)
  omega

/-- **The multiplier half of the infinite alternative**, isolated from the recession hypothesis.
Once the positively homogeneous convex function `k` generated by `conv {fᵢ*}` has `k(0) = -∞`, the
multipliers come out directly. `alternative_infinite_system` gets `k(0) = -∞` from a recession
hypothesis; the refinement in `HellyRefined.lean` gets it from a polyhedral subfamily instead
(`apply_zero_eq_bot_of_le_of_le`), and that is the *only* difference between the two. -/
theorem exists_multipliers_of_posHomGen_convFn_convexConj_eq_bot [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (hf : ∀ i, ClosedProperConvexFn (f i))
    (hk0 : posHomGen (convFn fun i => convexConj B (f i)) (0 : F) = ⊥) :
    ∃ (t : Finset ι) (l : ι → ℝ) (ε : ℝ), (∀ i, 0 ≤ l i) ∧ (∀ i ∉ t, l i = 0) ∧ 0 < ε ∧
      t.card ≤ Module.finrank ℝ E + 1 ∧
      ∀ x : E, (ε : EReal) ≤ ∑ i ∈ t, (l i : EReal) * f i x := by
  classical
  have hconvg : ∀ i, ConvexFn ((fun j => convexConj B (f j)) i) :=
      fun i => convexFn_convexConj B (f i)
  have hgbot : ∀ (i : ι) (y : F), (fun j => convexConj B (f j)) i y ≠ ⊥ :=
    fun i y => convexConj_ne_bot (hf i).proper.convexDom_nonempty y
  have hh0 : (convFn fun i => convexConj B (f i)) (0 : F) < ((0 : ℝ) : EReal) := by
    have hbot := (posHomGen_apply_zero_eq_bot_iff (convexFn_convFn _)).1 hk0
    rwa [EReal.coe_zero]
  -- finitely many multipliers, at most `n + 1` of them
  obtain ⟨t, w, q, hwpos, hwsum, hcard, -, hqtop, hq0, hqval⟩ :=
    exists_affineIndependent_of_convFn_lt hconvg hgbot hh0
  obtain ⟨c, hc⟩ : ∃ c : ι → ℝ, ∀ i ∈ t, convexConj B (f i) (q i) = (c i : EReal) := by
    refine ⟨fun i => (convexConj B (f i) (q i)).toReal, fun i hi => ?_⟩
    exact (EReal.coe_toReal (hqtop i hi) (hgbot i (q i))).symm
  have hcsum : ∑ i ∈ t, w i * c i < 0 := by
    have heq : ∑ i ∈ t, (w i : EReal) * convexConj B (f i) (q i)
        = ((∑ i ∈ t, w i * c i : ℝ) : EReal) := by
      rw [EReal.coe_sum]
      exact Finset.sum_congr rfl fun i hi => by rw [hc i hi, ← EReal.coe_mul]
    rw [heq] at hqval
    exact_mod_cast hqval
  refine ⟨t, fun i => if i ∈ t then w i else 0, -∑ i ∈ t, w i * c i, ?_, ?_, by linarith, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ t
    · have hnn : (0 : ℝ) ≤ (if i ∈ t then w i else 0) := by
        have hif : (if i ∈ t then w i else 0) = w i := by simp [hi]
        rw [hif]
        exact (hwpos i hi).le
      exact hnn
    · have hnn : (0 : ℝ) ≤ (if i ∈ t then w i else 0) := by simp [hi]
      exact hnn
  · intro i hi
    have hz : (if i ∈ t then w i else 0) = (0 : ℝ) := by simp [hi]
    exact hz
  · rw [← finrank_eq_of_isCompatiblePairing B]
    exact hcard
  · intro x
    have hlval : ∑ i ∈ t, (w i : EReal) * f i x
        = ∑ i ∈ t, ((if i ∈ t then w i else 0 : ℝ) : EReal) * f i x := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hif : (if i ∈ t then w i else 0) = w i := by simp [hi]
      rw [hif]
    -- Fenchel's inequality at each index, summed
    have hterm : ∀ i ∈ t,
        ((w i * (B x (q i) - c i) : ℝ) : EReal) ≤ (w i : EReal) * f i x := by
      intro i hi
      have hfen : ((B x (q i) : ℝ) : EReal) - f i x ≤ convexConj B (f i) (q i) :=
        sub_le_convexConj B (f i) x (q i)
      rw [hc i hi] at hfen
      have hstep : ((B x (q i) : ℝ) : EReal) - ((c i : ℝ) : EReal) ≤ f i x :=
        EReal.coe_sub_le_comm.1 hfen
      rw [← EReal.coe_sub] at hstep
      calc ((w i * (B x (q i) - c i) : ℝ) : EReal)
          = (w i : EReal) * ((B x (q i) - c i : ℝ) : EReal) := EReal.coe_mul _ _
        _ ≤ (w i : EReal) * f i x :=
            mul_le_mul_of_nonneg_left hstep (by exact_mod_cast (hwpos i hi).le)
    have hsum : ((∑ i ∈ t, w i * (B x (q i) - c i) : ℝ) : EReal)
        ≤ ∑ i ∈ t, (w i : EReal) * f i x := by
      rw [EReal.coe_sum]
      exact Finset.sum_le_sum hterm
    have hlin : ∑ i ∈ t, w i * B x (q i) = 0 := by
      have hmap : (B x) (∑ i ∈ t, w i • q i) = ∑ i ∈ t, w i * (B x) (q i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
      rw [hq0, map_zero] at hmap
      exact hmap.symm
    have hval : ∑ i ∈ t, w i * (B x (q i) - c i) = -∑ i ∈ t, w i * c i := by
      calc ∑ i ∈ t, w i * (B x (q i) - c i)
          = ∑ i ∈ t, (w i * B x (q i) - w i * c i) := Finset.sum_congr rfl fun i _ => by ring
        _ = (∑ i ∈ t, w i * B x (q i)) - ∑ i ∈ t, w i * c i := Finset.sum_sub_distrib _ _
        _ = -∑ i ∈ t, w i * c i := by rw [hlin]; ring
    rw [hval] at hsum
    exact le_of_le_of_eq hsum hlval


/-- **The infinite alternative over the whole space.** Either the weak system `fᵢ(x) ≤ 0` is
solvable, or finitely many non-negative multipliers — at most `n + 1` of them non-zero — make
`∑ λᵢ fᵢ` bounded away from `0` from above.

With `h = conv {fᵢ*}` and `k` the positively homogeneous convex function it generates, `cl k` is
the support function of `{x | ∀ i, fᵢ(x) ≤ 0}`, which is empty when (a) fails, so `(cl k)(0) = -∞`;
the recession hypothesis puts `0` in `ri (dom k)`, so `k(0) = -∞`; and that turns into the
multipliers. The final step is not the textbook's: the inequality `∑ λᵢ fᵢ(x) ≥ -∑ λᵢ fᵢ*(yᵢ)` is
**Fenchel's inequality** summed termwise, using only `∑ λᵢ yᵢ = 0`, so no infimal convolution is
needed. -/
theorem alternative_infinite_system_univ [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : ∀ i, ClosedProperConvexFn (f i))
    (hrec : ∀ y : E, (∀ i, recessionFn (f i) y ≤ 0) → y = 0) :
    (∃ x : E, ∀ i, f i x ≤ 0) ∨
      ∃ (t : Finset ι) (l : ι → ℝ) (ε : ℝ), (∀ i, 0 ≤ l i) ∧ (∀ i ∉ t, l i = 0) ∧ 0 < ε ∧
        t.card ≤ Module.finrank ℝ E + 1 ∧
        ∀ x : E, (ε : EReal) ≤ ∑ i ∈ t, (l i : EReal) * f i x := by
  classical
  by_cases halt : ∃ x : E, ∀ i, f i x ≤ 0
  · exact Or.inl halt
  refine Or.inr (exists_multipliers_of_posHomGen_convFn_convexConj_eq_bot (B := B) hf ?_)
  -- the conjugate of the convex hull is the pointwise supremum of the `fᵢ`.
  have hconj : convexConj B.flip (convFn fun i => convexConj B (f i)) = ⨆ i, f i := by
    rw [convexConj_convFn]
    exact iSup_congr fun i => convexBiconj_eq_self (hf i).convex (hf i).closed
  -- alternative (a) fails, so the level set of the conjugate is empty
  have hD :
      {x : E | convexConj B.flip (convFn fun i => convexConj B (f i)) x ≤ 0} = (∅ : Set E) := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have hx' : (⨆ i, f i) x ≤ 0 := by rw [← hconj]; exact hx
    rw [iSup_apply] at hx'
    exact halt ⟨x, fun i => le_trans (le_iSup (fun j => f j x) i) hx'⟩
  -- `cl k` is the support function of that level set, hence `-∞` everywhere
  have hclk : convexCl (posHomGen (convFn fun i => convexConj B (f i))) (0 : F) = ⊥ := by
    rw [convexCl_posHomGen (B := B), hD]
    simp
  have hdomsub : ∀ i,
      convexDom (convexConj B (f i))
          ⊆ convexDom (posHomGen (convFn fun j => convexConj B (f j))) := by
    intro i y hy
    exact lt_of_le_of_lt (le_trans (posHomGen_le _ y) (convFn_le _ i y)) hy
  have hzeromem : (0 : F) ∈ convexDom (posHomGen (convFn fun i => convexConj B (f i))) :=
    mem_convexDom.2 (lt_of_le_of_ne le_top (posHomGen_apply_zero_ne_top _))
  -- the recession hypothesis puts the origin in the relative interior of `dom k`
  have hri : (0 : F) ∈ ri (convexDom (posHomGen (convFn fun i => convexConj B (f i)))) := by
    by_contra hnot
    obtain ⟨ψ, hψle, y₁, hy₁, hy₁lt⟩ :=
      exists_lt_of_notMem_relint (convexFn_posHomGen _).convex_convexDom ⟨0, hzeromem⟩ hnot
    obtain ⟨v, hv⟩ := exists_pairing_eq B.flip ψ
    have hψ0 : ψ (0 : F) = 0 := map_zero ψ
    have hrecv : ∀ i, recessionFn (f i) v ≤ 0 := by
      intro i
      have hpi : ProperConvex (convexConj B (f i)) := properConvex_convexConj (hf i)
      have hbi : convexConj B.flip (convexConj B (f i)) = f i :=
          convexBiconj_eq_self (hf i).convex (hf i).closed
      have h13 : recessionFn (f i) = supportFn B.flip (convexDom (convexConj B (f i))) := by
        have hstep := recessionFn_convexConj (B := B.flip) (f := convexConj B (f i)) hpi
          (by rw [hbi]; exact (hf i).proper)
        rwa [hbi] at hstep
      rw [h13]
      have hle : supportFn B.flip (convexDom (convexConj B (f i))) v ≤ ((0 : ℝ) : EReal) := by
        rw [supportFn_le_coe_iff]
        intro y hy
        have h1 := hψle y (hdomsub i hy)
        rw [hv y, hψ0] at h1
        exact h1
      simpa using hle
    have hψ1 : ψ y₁ = 0 := by rw [hv y₁, hrec v hrecv]; simp
    rw [hψ1, hψ0] at hy₁lt
    exact lt_irrefl (0 : ℝ) hy₁lt
  -- `k` agrees with `cl k` there, so `k(0) = -∞` and `h(0) < 0`
  rw [← (convexFn_posHomGen _).convexCl_eq_of_mem_relint_convexDom hri]
  exact hclk

/-- **The alternative for an infinite system of weak convex inequalities.** For a collection of
closed proper convex functions indexed by an *arbitrary* set and a non-empty closed convex set `C`,
exactly one of the following holds: the weak system `fᵢ(x) ≤ 0` is solvable in `C`, or there are
non-negative multipliers — only finitely many non-zero, and at most `n + 1` of them — with
`∑ λᵢ fᵢ ≥ ε > 0` throughout `C`. The hypothesis is that the `fᵢ` have no common direction of
recession which is also a direction of recession of `C`; a family built from two hyperbolas shows
it cannot be dropped. `C` is folded into the collection as its indicator function, which is why the
index type of the auxiliary system is `Option ι`. -/
theorem alternative_infinite_system [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : ∀ i, ClosedProperConvexFn (f i)) (hC : Convex ℝ C) (hCc : IsClosed C) (hCne : C.Nonempty)
    (hrec : ∀ y : E, (∀ i, recessionFn (f i) y ≤ 0) → y ∈ recessionCone C → y = 0) :
    (∃ x ∈ C, ∀ i, f i x ≤ 0) ∨
      ∃ (t : Finset ι) (l : ι → ℝ) (ε : ℝ), (∀ i, 0 ≤ l i) ∧ (∀ i ∉ t, l i = 0) ∧ 0 < ε ∧
        t.card ≤ Module.finrank ℝ E + 1 ∧
        ∀ x ∈ C, (ε : EReal) ≤ ∑ i ∈ t, (l i : EReal) * f i x := by
  classical
  have hnone : ∀ x : E, (Option.elim none (indicatorFn C) f) x = indicatorFn C x := fun _ => rfl
  have hg : ∀ o : Option ι, ClosedProperConvexFn (Option.elim o (indicatorFn C) f) := by
    rintro (_ | i)
    · have hind : ClosedProperConvexFn (indicatorFn C) :=
        ⟨convexFn_indicatorFn.2 hC, closedConvex_indicatorFn hCc,
          ⟨by rw [convexDom_indicatorFn]; exact hCne, indicatorFn_ne_bot C⟩⟩
      exact hind
    · exact hf i
  have hgrec : ∀ y : E,
      (∀ o : Option ι, recessionFn (Option.elim o (indicatorFn C) f) y ≤ 0) → y = 0 := by
    intro y hy
    refine hrec y (fun i => hy (some i)) ?_
    have h0 : recessionFn (indicatorFn C) y ≤ 0 := hy none
    rw [recessionFn_indicatorFn hCne] at h0
    by_contra hcon
    rw [indicatorFn_of_notMem hcon] at h0
    exact absurd h0 (by simp)
  rcases alternative_infinite_system_univ (B := B) hg hgrec with
    ⟨x, hx⟩ | ⟨t', l', ε, hl0, hlz, hε, hcard, hineq⟩
  · refine Or.inl ⟨x, ?_, fun i => hx (some i)⟩
    have h0 : indicatorFn C x ≤ 0 := hx none
    by_contra hcon
    rw [indicatorFn_of_notMem hcon] at h0
    exact absurd h0 (by simp)
  · refine Or.inr ?_
    have hinj : Set.InjOn (some : ι → Option ι) ((some : ι → Option ι) ⁻¹' ↑t') :=
      Set.injOn_of_injective (Option.some_injective ι)
    have himg : (t'.preimage some hinj).image some = t'.erase none := by
      ext o
      simp only [Finset.mem_image, Finset.mem_preimage, Finset.mem_erase]
      cases o with
      | none => simp
      | some i => simp
    refine ⟨t'.preimage some hinj, fun i => l' (some i), ε, fun i => hl0 (some i), ?_, hε, ?_, ?_⟩
    · intro i hi
      exact hlz (some i) fun hc => hi (Finset.mem_preimage.2 hc)
    · exact le_trans (Finset.card_le_card_of_injOn some
        (fun i hi => Finset.mem_preimage.1 hi)
        (fun a _ b _ hab => Option.some_injective _ hab)) hcard
    · intro x hx
      have hz : (l' none : EReal) * (Option.elim none (indicatorFn C) f) x = 0 := by
        rw [hnone x, indicatorFn_of_mem hx, mul_zero]
      calc (ε : EReal)
          ≤ ∑ o ∈ t', (l' o : EReal) * (Option.elim o (indicatorFn C) f) x := hineq x
        _ = ∑ o ∈ t'.erase none, (l' o : EReal) * (Option.elim o (indicatorFn C) f) x :=
            (Finset.sum_erase t' hz).symm
        _ = ∑ i ∈ t'.preimage some hinj, (l' (some i) : EReal) * f i x := by
            rw [← himg, Finset.sum_image fun a _ b _ hab => Option.some_injective _ hab]
            exact Finset.sum_congr rfl fun i _ => rfl

omit [FiniteDimensional ℝ E] in
/-- **Multipliers are incompatible with approximate solvability of every subsystem.** Multipliers
that keep `∑ λᵢ fᵢ` at least `ε > 0` on `C` cannot coexist with subsystems solvable to within
`ε / (2 ∑ λᵢ)`. Rockafellar normalises the multipliers to sum to `1` and argues with a strict
inequality; halving the tolerance instead makes every step non-strict, which matters because
`EReal` is not a cancellative ordered monoid and strict sums do not add. -/
theorem not_forall_le_weighted_of_forall_subsystem {t : Finset ι} {l : ι → ℝ} {ε : ℝ}
    (hCne : C.Nonempty) (hl0 : ∀ i, 0 ≤ l i) (hε : 0 < ε)
    (hcard : t.card ≤ Module.finrank ℝ E + 1)
    (hsub : ∀ δ : ℝ, 0 < δ → ∀ S : Finset ι, S.card ≤ Module.finrank ℝ E + 1 →
      ∃ x ∈ C, ∀ i ∈ S, f i x < (δ : EReal)) :
    ¬ ∀ x ∈ C, (ε : EReal) ≤ ∑ i ∈ t, (l i : EReal) * f i x := by
  intro hineq
  have hlam0 : 0 ≤ ∑ i ∈ t, l i := Finset.sum_nonneg fun i _ => hl0 i
  have hlampos : 0 < ∑ i ∈ t, l i := by
    rcases eq_or_lt_of_le hlam0 with h0 | h0
    · exfalso
      have hzero : ∀ i ∈ t, l i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hl0 j).1 h0.symm
      obtain ⟨x, hxC⟩ := hCne
      have hbound := hineq x hxC
      rw [Finset.sum_congr rfl fun i hi => by
        rw [hzero i hi, EReal.coe_zero, zero_mul]] at hbound
      have h2 : ((ε : ℝ) : EReal) ≤ 0 := by simpa using hbound
      have h3 : ε ≤ 0 := by exact_mod_cast h2
      linarith
    · exact h0
  obtain ⟨x, hxC, hxlt⟩ :=
    hsub (ε / (2 * ∑ i ∈ t, l i)) (by positivity) t hcard
  have hbound : ∀ i ∈ t, (l i : EReal) * f i x
      ≤ ((l i * (ε / (2 * ∑ j ∈ t, l j)) : ℝ) : EReal) := by
    intro i hi
    calc (l i : EReal) * f i x
        ≤ (l i : EReal) * ((ε / (2 * ∑ j ∈ t, l j) : ℝ) : EReal) :=
          mul_le_mul_of_nonneg_left (hxlt i hi).le (by exact_mod_cast hl0 i)
      _ = _ := (EReal.coe_mul _ _).symm
  have hsum : ∑ i ∈ t, (l i : EReal) * f i x ≤ ((ε / 2 : ℝ) : EReal) := by
    refine le_trans (Finset.sum_le_sum hbound) (le_of_eq ?_)
    rw [← EReal.coe_sum, ← Finset.sum_mul]
    congr 1
    field_simp
  have hfin : ((ε : ℝ) : EReal) ≤ ((ε / 2 : ℝ) : EReal) := le_trans (hineq x hxC) hsum
  have hfin' : ε ≤ ε / 2 := by exact_mod_cast hfin
  linarith

/-- Under the same recession hypothesis, an infinite system of weak convex inequalities is solvable
in `C` as soon as every subsystem of at most `n + 1` of the inequalities is solvable in `C` to
within an arbitrarily small tolerance. -/
theorem exists_forall_le_zero_of_forall_subsystem [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip]
    (hf : ∀ i, ClosedProperConvexFn (f i)) (hC : Convex ℝ C) (hCc : IsClosed C) (hCne : C.Nonempty)
    (hrec : ∀ y : E, (∀ i, recessionFn (f i) y ≤ 0) → y ∈ recessionCone C → y = 0)
    (hsub : ∀ δ : ℝ, 0 < δ → ∀ S : Finset ι, S.card ≤ Module.finrank ℝ E + 1 →
      ∃ x ∈ C, ∀ i ∈ S, f i x < (δ : EReal)) :
    ∃ x ∈ C, ∀ i, f i x ≤ 0 := by
  rcases alternative_infinite_system (B := B) hf hC hCc hCne hrec with
    hgood | ⟨t, l, ε, hl0, -, hε, hcard, hineq⟩
  · exact hgood
  exact absurd hineq (not_forall_le_weighted_of_forall_subsystem hCne hl0 hε hcard hsub)

/-- **Helly's theorem for an *infinite* family.** A family of non-empty closed convex sets with
**no common direction of recession** has a common point as soon as every `n + 1` of them do. The
recession hypothesis cannot be dropped: a family built from two hyperbolas has the
`(n+1)`-intersection property and empty total intersection. Compare `helly_finite`, where the
family is finite and neither closedness nor a recession hypothesis is needed. -/
theorem helly_of_no_common_recession [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    {K : ι → Set E} (hconv : ∀ i, Convex ℝ (K i)) (hcl : ∀ i, IsClosed (K i))
    (hne : ∀ i, (K i).Nonempty)
    (hrec : ∀ y : E, (∀ i, y ∈ recessionCone (K i)) → y = 0)
    (hinter : ∀ S : Finset ι, S.card ≤ Module.finrank ℝ E + 1 → (⋂ i ∈ S, K i).Nonempty) :
    (⋂ i, K i).Nonempty := by
  have hfi : ∀ i, ClosedProperConvexFn (indicatorFn (K i)) := fun i =>
    ⟨convexFn_indicatorFn.2 (hconv i), closedConvex_indicatorFn (hcl i),
      ⟨by rw [convexDom_indicatorFn]; exact hne i, indicatorFn_ne_bot (K i)⟩⟩
  have hrec' : ∀ y : E, (∀ i, recessionFn (indicatorFn (K i)) y ≤ 0) →
      y ∈ recessionCone (Set.univ : Set E) → y = 0 := by
    intro y hy _
    refine hrec y fun i => ?_
    have h0 := hy i
    rw [recessionFn_indicatorFn (hne i)] at h0
    by_contra hcon
    rw [indicatorFn_of_notMem hcon] at h0
    exact absurd h0 (by simp)
  have hsub : ∀ δ : ℝ, 0 < δ → ∀ S : Finset ι, S.card ≤ Module.finrank ℝ E + 1 →
      ∃ x ∈ (Set.univ : Set E), ∀ i ∈ S, indicatorFn (K i) x < (δ : EReal) := by
    intro δ hδ S hS
    obtain ⟨x, hx⟩ := hinter S hS
    refine ⟨x, Set.mem_univ x, fun i hi => ?_⟩
    rw [indicatorFn_of_mem (Set.mem_iInter₂.1 hx i hi)]
    exact_mod_cast hδ
  obtain ⟨x, -, hx⟩ :=
    exists_forall_le_zero_of_forall_subsystem (B := B) hfi convex_univ isClosed_univ
      ⟨0, Set.mem_univ 0⟩ hrec' hsub
  refine ⟨x, Set.mem_iInter.2 fun i => ?_⟩
  by_contra hcon
  have h0 := hx i
  rw [indicatorFn_of_notMem hcon] at h0
  exact absurd h0 (by simp)

/-- **Helly's theorem with a bounded subfamily in place of the recession hypothesis.** A family of
closed convex sets *every finite subfamily of which has a common point* has a common point
outright, as soon as **some** finite subfamily has a bounded intersection. Under that standing
hypothesis the recession and the bounded-subfamily hypotheses are equivalent
(`iInter_recessionCone_eq_zero_iff_exists_isBounded`), and the bounded subfamily is in practice a
single bounded `K i`. -/
theorem helly_of_exists_isBounded_biInter [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    {K : ι → Set E} (hconv : ∀ i, Convex ℝ (K i)) (hcl : ∀ i, IsClosed (K i))
    (hne : ∀ S : Finset ι, (⋂ i ∈ S, K i).Nonempty)
    (hbdd : ∃ S : Finset ι, Bornology.IsBounded (⋂ i ∈ S, K i)) :
    (⋂ i, K i).Nonempty := by
  have hrec : ⋂ i, recessionCone (K i) = {0} :=
    (iInter_recessionCone_eq_zero_iff_exists_isBounded hconv hcl hne).2 hbdd
  refine helly_of_no_common_recession (B := B) hconv hcl (fun i => by simpa using hne {i})
    (fun y hy => ?_) fun S _ => hne S
  have hy' : y ∈ ⋂ i, recessionCone (K i) := mem_iInter.2 hy
  rw [hrec] at hy'
  simpa using hy'

end Infinite


end ConvexAnalysis
