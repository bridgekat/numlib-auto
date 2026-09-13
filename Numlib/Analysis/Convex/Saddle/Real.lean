import Numlib.Analysis.Convex.Saddle.Minimax

/-!
# Saddle-points relative to a product set, and real-valued saddle-functions

`IsSaddlePointOn K C D p` of `Saddle/Minimax` is the saddle-point condition relative to `C × D`;
the minimax theory there — `isSaddlePoint_iff_attained`, `maximin_le_minimax`, and the rest — is
stated over the whole space. This module transfers it to `C × D` and then reads it for a
**real-valued** `L : U × X → ℝ`, where the two iterated extrema become conditionally complete
`sSup`/`sInf` and the boundedness hypotheses that `ℝ` needs appear.

## Main results

* `isSaddlePointOn_iff_isSaddlePoint_subtype` — a saddle-point of `K` relative to `C × D` is a
  saddle-point of the restriction of `K` to the subtype product `↥C × ↥D`; `maximin_subtype` and
  `minimax_subtype` identify the iterated extrema of that restriction with
  `⨆ u ∈ C, ⨅ x ∈ D, K (u, x)` and `⨅ x ∈ D, ⨆ u ∈ C, K (u, x)`.
* `biSup_biInf_le_biInf_biSup` — `sup inf ≤ inf sup` over `C × D`;
  `isSaddlePointOn_iff_attained` — `p` is a saddle-point relative to `C × D` exactly when the outer
  extrema of `sup inf` and `inf sup` over `C × D` are attained at `p.1` and `p.2` and agree;
  `IsSaddlePointOn.biSup_biInf_eq`, `IsSaddlePointOn.biInf_biSup_eq` — both then equal `K p`.
* For `L : U × X → ℝ` read through `EReal`: `IsSaddlePointOn.isGreatest_image_coe`,
  `.isLeast_image_coe`, `.sSup_image_coe_eq`, `.sInf_image_coe_eq` — the two partial extrema at a
  saddle-point; `.isLeast_sSup_coe`, `.isGreatest_sInf_coe` — the primal problem
  `inf_{x ∈ D} sup_{u ∈ C} L (u, x)` is solved at `p.2` and the dual problem
  `sup_{u ∈ C} inf_{x ∈ D} L (u, x)` at `p.1`, both with value `L p`;
  `.sInf_sSup_eq_sSup_sInf_coe` — the minimax equality, no duality gap; and the converse
  `isSaddlePointOn_coe_of_isLeast_of_isGreatest`.

The convention is Rockafellar's: the first variable is maximised over `C`, the second minimised over
`D`. A saddle-point in the opposite convention — min in the first variable, max in the second, as
in Atkinson–Han, *Theoretical Numerical Analysis*, Definition 8.6.1 — is `IsSaddlePointOn` of the
transposed kernel `fun q => L (q.2, q.1)` on `D × C`, definitionally; the real-valued statements
above are Atkinson–Han's Proposition 8.6.2 and (8.6.12)–(8.6.14) under that transposition.

## Implementation notes

`EReal.coe_sSup_of_bddAbove` and `EReal.coe_sInf_of_bddBelow` are the only new order facts: the
coercion `ℝ → EReal` carries a conditionally complete supremum to the corresponding `⨆`. They are
what lets each real statement be read off its `EReal` original rather than reproved. The
`BddAbove`/`BddBelow` hypotheses are not decoration: `sSup` and `sInf` take junk values on unbounded
sets of reals, and the `EReal` statements hold with no hypothesis precisely because `⊤` and `⊥` are
available there.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §36.
* K. Atkinson and W. Han, *Theoretical Numerical Analysis*, 3rd ed., Springer, 2009, §8.6.
-/

open Set

/-! ### The coercion `ℝ → EReal` and conditionally complete extrema -/

namespace EReal

/-- The coercion `ℝ → EReal` carries the supremum of a nonempty bounded set to the `EReal`
supremum of its image. -/
theorem coe_sSup_of_bddAbove {s : Set ℝ} (hne : s.Nonempty) (hbdd : BddAbove s) :
    ((sSup s : ℝ) : EReal) = ⨆ a ∈ s, (a : EReal) := by
  rw [← sSup_image]
  exact Monotone.map_csSup_of_continuousAt continuous_coe_real_ereal.continuousAt
    coe_strictMono.monotone hne hbdd

/-- The coercion `ℝ → EReal` carries the infimum of a nonempty bounded set to the `EReal` infimum
of its image. -/
theorem coe_sInf_of_bddBelow {s : Set ℝ} (hne : s.Nonempty) (hbdd : BddBelow s) :
    ((sInf s : ℝ) : EReal) = ⨅ a ∈ s, (a : EReal) := by
  rw [← sInf_image]
  exact Monotone.map_csInf_of_continuousAt continuous_coe_real_ereal.continuousAt
    coe_strictMono.monotone hne hbdd

end EReal

namespace ConvexAnalysis

/-! ### Transfer to the subtype product -/

section Subtype

variable {U X : Type*} {K : U × X → EReal} {C : Set U} {D : Set X} {p : U × X}

/-- A saddle-point of `K` relative to `C × D` is a saddle-point, over the whole of `↥C × ↥D`, of
the restriction of `K`. -/
theorem isSaddlePointOn_iff_isSaddlePoint_subtype (h₁ : p.1 ∈ C) (h₂ : p.2 ∈ D) :
    IsSaddlePointOn K C D p ↔
      IsSaddlePoint (fun q : C × D => K (q.1, q.2)) (⟨p.1, h₁⟩, ⟨p.2, h₂⟩) := by
  simp only [IsSaddlePointOn, IsSaddlePoint, h₁, h₂, true_and, SetCoe.forall]

/-- `sup inf` of the restriction of `K` to `↥C × ↥D` is `sup inf` over `C × D`. -/
theorem maximin_subtype (K : U × X → EReal) (C : Set U) (D : Set X) :
    maximin (fun q : C × D => K (q.1, q.2)) = ⨆ u ∈ C, ⨅ x ∈ D, K (u, x) := by
  rw [maximin_apply, iSup_subtype]
  exact iSup_congr fun u => iSup_congr fun _ => iInf_subtype

/-- `inf sup` of the restriction of `K` to `↥C × ↥D` is `inf sup` over `C × D`. -/
theorem minimax_subtype (K : U × X → EReal) (C : Set U) (D : Set X) :
    minimax (fun q : C × D => K (q.1, q.2)) = ⨅ x ∈ D, ⨆ u ∈ C, K (u, x) := by
  rw [minimax_apply, iInf_subtype]
  exact iInf_congr fun x => iInf_congr fun _ => iSup_subtype

/-- **`sup inf ≤ inf sup` over `C × D`**, with no hypothesis. -/
theorem biSup_biInf_le_biInf_biSup (K : U × X → EReal) (C : Set U) (D : Set X) :
    (⨆ u ∈ C, ⨅ x ∈ D, K (u, x)) ≤ ⨅ x ∈ D, ⨆ u ∈ C, K (u, x) := by
  rw [← maximin_subtype, ← minimax_subtype]
  exact maximin_le_minimax _

/-- `p` is a saddle-point relative to `C × D` exactly when the outer supremum in `sup inf` over
`C × D` is attained at `p.1`, the outer infimum in `inf sup` over `C × D` is attained at `p.2`,
and the two extrema agree. -/
theorem isSaddlePointOn_iff_attained (h₁ : p.1 ∈ C) (h₂ : p.2 ∈ D) :
    IsSaddlePointOn K C D p ↔
      (⨅ x ∈ D, K (p.1, x)) = (⨆ u ∈ C, ⨅ x ∈ D, K (u, x)) ∧
        (⨆ u ∈ C, K (u, p.2)) = (⨅ x ∈ D, ⨆ u ∈ C, K (u, x)) ∧
          (⨆ u ∈ C, ⨅ x ∈ D, K (u, x)) = ⨅ x ∈ D, ⨆ u ∈ C, K (u, x) := by
  rw [isSaddlePointOn_iff_isSaddlePoint_subtype h₁ h₂, isSaddlePoint_iff_attained,
    hasSaddleValue_iff, maximin_subtype, minimax_subtype, iInf_subtype, iSup_subtype]

/-- At a saddle-point relative to `C × D` the supremum of `K (·, p.2)` over `C` is `K p`. -/
theorem IsSaddlePointOn.biSup_eq (h : IsSaddlePointOn K C D p) :
    (⨆ u ∈ C, K (u, p.2)) = K p :=
  le_antisymm (iSup₂_le h.2.2.1) (le_iSup₂ (f := fun u (_ : u ∈ C) => K (u, p.2)) p.1 h.1)

/-- At a saddle-point relative to `C × D` the infimum of `K (p.1, ·)` over `D` is `K p`. -/
theorem IsSaddlePointOn.biInf_eq (h : IsSaddlePointOn K C D p) :
    (⨅ x ∈ D, K (p.1, x)) = K p :=
  le_antisymm (iInf₂_le (f := fun x (_ : x ∈ D) => K (p.1, x)) p.2 h.2.1) (le_iInf₂ h.2.2.2)

/-- At a saddle-point relative to `C × D`, `sup inf` over `C × D` is `K p`. -/
theorem IsSaddlePointOn.biSup_biInf_eq (h : IsSaddlePointOn K C D p) :
    (⨆ u ∈ C, ⨅ x ∈ D, K (u, x)) = K p :=
  ((isSaddlePointOn_iff_attained h.1 h.2.1).1 h).1.symm.trans h.biInf_eq

/-- At a saddle-point relative to `C × D`, `inf sup` over `C × D` is `K p`. -/
theorem IsSaddlePointOn.biInf_biSup_eq (h : IsSaddlePointOn K C D p) :
    (⨅ x ∈ D, ⨆ u ∈ C, K (u, x)) = K p :=
  ((isSaddlePointOn_iff_attained h.1 h.2.1).1 h).2.1.symm.trans h.biSup_eq

end Subtype

/-! ### Real-valued saddle-functions -/

section Real

variable {U X : Type*} {L : U × X → ℝ} {C : Set U} {D : Set X} {p : U × X}

/-- At a saddle-point of a real-valued `L` relative to `C × D`, `L (·, p.2)` attains its maximum
over `C` at `p.1`. -/
theorem IsSaddlePointOn.isGreatest_image_coe (h : IsSaddlePointOn (fun q => (L q : EReal)) C D p) :
    IsGreatest ((fun u => L (u, p.2)) '' C) (L p) :=
  ⟨⟨p.1, h.1, rfl⟩, by
    rintro _ ⟨u, hu, rfl⟩
    exact EReal.coe_le_coe_iff.1 (h.2.2.1 u hu)⟩

/-- At a saddle-point of a real-valued `L` relative to `C × D`, `L (p.1, ·)` attains its minimum
over `D` at `p.2`. -/
theorem IsSaddlePointOn.isLeast_image_coe (h : IsSaddlePointOn (fun q => (L q : EReal)) C D p) :
    IsLeast ((fun x => L (p.1, x)) '' D) (L p) :=
  ⟨⟨p.2, h.2.1, rfl⟩, by
    rintro _ ⟨x, hx, rfl⟩
    exact EReal.coe_le_coe_iff.1 (h.2.2.2 x hx)⟩

/-- `sup_{u ∈ C} L (u, p.2) = L p` at a saddle-point. -/
theorem IsSaddlePointOn.sSup_image_coe_eq (h : IsSaddlePointOn (fun q => (L q : EReal)) C D p) :
    sSup ((fun u => L (u, p.2)) '' C) = L p :=
  h.isGreatest_image_coe.csSup_eq

/-- `inf_{x ∈ D} L (p.1, x) = L p` at a saddle-point. -/
theorem IsSaddlePointOn.sInf_image_coe_eq (h : IsSaddlePointOn (fun q => (L q : EReal)) C D p) :
    sInf ((fun x => L (p.1, x)) '' D) = L p :=
  h.isLeast_image_coe.csInf_eq

/-- **The primal problem is solved at a saddle-point.** For a real-valued `L` whose slices
`L (·, x)` are bounded above on `C`, the objective `x ↦ sup_{u ∈ C} L (u, x)` attains its least
value over `D` at `p.2`, and that value is `L p`. This is `IsSaddlePointOn.biInf_biSup_eq` read in
`ℝ`; the boundedness is what makes each `sSup` the real supremum. -/
theorem IsSaddlePointOn.isLeast_sSup_coe (h : IsSaddlePointOn (fun q => (L q : EReal)) C D p)
    (hbdd : ∀ x ∈ D, BddAbove ((fun u => L (u, x)) '' C)) :
    IsLeast ((fun x => sSup ((fun u => L (u, x)) '' C)) '' D) (L p) := by
  have hcoe : ∀ x ∈ D, ((sSup ((fun u => L (u, x)) '' C) : ℝ) : EReal) =
      ⨆ u ∈ C, ((L (u, x) : ℝ) : EReal) := fun x hx => by
    rw [EReal.coe_sSup_of_bddAbove ((nonempty_of_mem h.1).image _) (hbdd x hx), ← sSup_image,
      ← sSup_image,
      image_image]
  refine ⟨⟨p.2, h.2.1, h.sSup_image_coe_eq⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  refine EReal.coe_le_coe_iff.1 ?_
  rw [hcoe x hx, ← h.biInf_biSup_eq]
  exact iInf₂_le (f := fun x (_ : x ∈ D) => ⨆ u ∈ C, ((L (u, x) : ℝ) : EReal)) x hx

/-- **The dual problem is solved at a saddle-point.** For a real-valued `L` whose slices `L (u, ·)`
are bounded below on `D`, the objective `u ↦ inf_{x ∈ D} L (u, x)` attains its greatest value over
`C` at `p.1`, and that value is again `L p`. With `IsSaddlePointOn.isLeast_sSup_coe` this is the
minimax equality. -/
theorem IsSaddlePointOn.isGreatest_sInf_coe (h : IsSaddlePointOn (fun q => (L q : EReal)) C D p)
    (hbdd : ∀ u ∈ C, BddBelow ((fun x => L (u, x)) '' D)) :
    IsGreatest ((fun u => sInf ((fun x => L (u, x)) '' D)) '' C) (L p) := by
  have hcoe : ∀ u ∈ C, ((sInf ((fun x => L (u, x)) '' D) : ℝ) : EReal) =
      ⨅ x ∈ D, ((L (u, x) : ℝ) : EReal) := fun u hu => by
    rw [EReal.coe_sInf_of_bddBelow ((nonempty_of_mem h.2.1).image _) (hbdd u hu), ← sInf_image,
      ← sInf_image,
      image_image]
  refine ⟨⟨p.1, h.1, h.sInf_image_coe_eq⟩, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  refine EReal.coe_le_coe_iff.1 ?_
  rw [hcoe u hu, ← h.biSup_biInf_eq]
  exact le_iSup₂ (f := fun u (_ : u ∈ C) => ⨅ x ∈ D, ((L (u, x) : ℝ) : EReal)) u hu

/-- **No duality gap.** At a saddle-point of a real-valued `L` the primal value
`inf_{x ∈ D} sup_{u ∈ C} L (u, x)` and the dual value `sup_{u ∈ C} inf_{x ∈ D} L (u, x)` agree,
both being `L p`. -/
theorem IsSaddlePointOn.sInf_sSup_eq_sSup_sInf_coe
    (h : IsSaddlePointOn (fun q => (L q : EReal)) C D p)
    (hbddA : ∀ x ∈ D, BddAbove ((fun u => L (u, x)) '' C))
    (hbddB : ∀ u ∈ C, BddBelow ((fun x => L (u, x)) '' D)) :
    sInf ((fun x => sSup ((fun u => L (u, x)) '' C)) '' D) =
      sSup ((fun u => sInf ((fun x => L (u, x)) '' D)) '' C) :=
  (h.isLeast_sSup_coe hbddA).csInf_eq.trans (h.isGreatest_sInf_coe hbddB).csSup_eq.symm

/-- **The converse**: if the primal objective `x ↦ sup_{u ∈ C} L (u, x)` attains its minimum over
`D` at `p.2`, the dual objective `u ↦ inf_{x ∈ D} L (u, x)` attains its maximum over `C` at `p.1`,
and the two extremal values agree, then `p` is a saddle-point of `L` relative to `C × D`. The
boundedness hypotheses are needed only at `p` itself, to read the two extremal values as real
numbers. -/
theorem isSaddlePointOn_coe_of_isLeast_of_isGreatest (h₁ : p.1 ∈ C) (h₂ : p.2 ∈ D)
    (hbddA : BddAbove ((fun u => L (u, p.2)) '' C)) (hbddB : BddBelow ((fun x => L (p.1, x)) '' D))
    (hleast : IsLeast ((fun x => sSup ((fun u => L (u, x)) '' C)) '' D)
      (sSup ((fun u => L (u, p.2)) '' C)))
    (hgreatest : IsGreatest ((fun u => sInf ((fun x => L (u, x)) '' D)) '' C)
      (sInf ((fun x => L (p.1, x)) '' D)))
    (heq : sInf ((fun x => sSup ((fun u => L (u, x)) '' C)) '' D) =
      sSup ((fun u => sInf ((fun x => L (u, x)) '' D)) '' C)) :
    IsSaddlePointOn (fun q => (L q : EReal)) C D p := by
  have hval : sSup ((fun u => L (u, p.2)) '' C) = sInf ((fun x => L (p.1, x)) '' D) := by
    rw [← hleast.csInf_eq, heq, hgreatest.csSup_eq]
  refine (isSaddlePointOn_iff_biSup_eq_biInf h₁ h₂).2 ?_
  have hS := EReal.coe_sSup_of_bddAbove ((nonempty_of_mem h₁).image _) hbddA
  have hI := EReal.coe_sInf_of_bddBelow ((nonempty_of_mem h₂).image _) hbddB
  simp only [iSup_image] at hS
  simp only [iInf_image] at hI
  rw [← hS, ← hI, hval]

end Real

end ConvexAnalysis
