import Numlib.Analysis.Convex.Saddle.Correspondence
import Numlib.Analysis.Convex.Saddle.Minimax
import NumlibSurface.Rockafellar.Chapter06.Section29

/-!
# Rockafellar §30: adjoint bifunctions and dual programs

Surface file for R. Tyrrell Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §30
(pp. 307–326): the **adjoint** `F*` of a convex bifunction, the **dual program** `(P*)` it defines,
and the exact circumstances — Rockafellar calls them *normality* — under which the two programs
have the same optimal value.

All 10 numbered results of §30 are formalized: Theorems 30.1, 30.2, 30.3, 30.4 and 30.5 and
Corollaries 30.2.1, 30.2.2, 30.2.3, 30.5.1 and 30.5.2, with one declaration per clause for the
multi-clause results. With them: the **Gale–Kuhn–Tucker Duality Theorem**, which the book names in
running text and never states as a numbered result; the adjoint of the indicator bifunction of a
linear transformation, which is what justifies the word "adjoint"; the Lagrangian reading of the
two objective functions that §36 takes up; and the section's two unnumbered counterexamples,
`abnormalBifun` and `noDualSolutionBifun`, placed at the end of the file because each cites a
theorem stated further on.

`dualProgram F` is an `abbrev` for the backbone's `adjointBifun (pairing m) (pairing n) F`, so
every backbone theorem about `adjointBifun` applies to it verbatim. `Normal`, `ConcaveNormal`,
`ConcaveConsistent`, `ConcaveKuhnTucker`, `ConcavePolyhedralBifun`, `supBifun`,
`concaveAdjointBifun` and `clBifun` are the backbone's under the book's own definitions.

Four statements drop closedness that the book assumes — Corollary 30.2.1's first half, the first
formulas of Corollaries 30.2.2 and 30.2.3, and Theorem 30.3's (a) ⟺ (c). Each runs on
Fenchel–Moreau for `inf F`, and the adjoint cannot tell `F` from `cl F`.

## Main results

* `theorem_30_1_concave`, `theorem_30_1_closed`, `theorem_30_1_proper`, `theorem_30_1_biadjoint`,
  `theorem_30_1_biadjoint_closed`, `theorem_30_1_injective`, `theorem_30_1_surjective`,
  `theorem_30_1_polyhedral` — the adjoint is a one-to-one correspondence between the closed proper
  convex bifunctions and the closed proper concave ones, with `F** = cl F`.
* `theorem_30_2_first` through `theorem_30_2_fourth` — the four conjugacy formulas relating the
  objectives and perturbation functions of `(P)` and `(P*)`.
* `corollary_30_2_1_dual`, `corollary_30_2_1_primal`, `corollary_30_2_2_first`,
  `corollary_30_2_2_second`, `corollary_30_2_2_weak`, `corollary_30_2_3_first`,
  `corollary_30_2_3_second` — consistency of one program read off the other, and weak duality
  `inf F0 ≥ sup F*0`.
* `theorem_30_3`, `theorem_30_3_a_iff_b`, `theorem_30_3_a_iff_c`, `theorem_30_3_b_iff_c` — the
  three equivalent forms of normality.
* `theorem_30_4_a` through `theorem_30_4_j`, and `gale_kuhn_tucker_duality` — the ten sufficient
  conditions for normality, and the Gale–Kuhn–Tucker duality theorem they yield.
* `theorem_30_5`, `theorem_30_5_dual`, `corollary_30_5_1` with its three clauses,
  `corollary_30_5_1_eq`, `corollary_30_5_2`, `corollary_30_5_2_dual` — under normality the
  Kuhn–Tucker vectors of each program are the optimal solutions of the other, and the saddle-points
  of the Lagrangian are the optimal pairs.
* `abnormalBifun_duality_gap`, `noDualSolutionBifun_*` — the two counterexamples: a duality gap,
  and a normal program whose dual has no optimal solution.

## Where the book needs correcting

**Theorem 30.4(i) and (j) are false as the book states them.** Rockafellar disposes of them in six
words — "Of course, (i) and (j) are contained in (g) and (h)" — and the containment needs the
objective to be proper. With `F0 ≡ +∞` every point is an optimal solution, so that set is non-empty
and bounded while no sublevel set of `F0` is. `theorem_30_4_i` therefore assumes `Proper (F 0)` and
`theorem_30_4_j` assumes `Proper fun v => -(F* 0) v`; with those the containment is right.
-/

open Filter Set Topology

namespace Rockafellar

open ConvexAnalysis

/-! ### The adjoint bifunction and the dual program -/

/-- **Rockafellar's adjoint bifunction `F*`**: the bifunction from `ℝⁿ` to `ℝᵐ` given by
`(F*x*)(u*) = inf_{u,x} {(Fu)(x) - ⟨x, x*⟩ + ⟨u, u*⟩}`, which is the bifunction of the **dual
program** `(P*)`. An `abbrev` for the backbone's `adjointBifun` at the two Euclidean pairings. -/
noncomputable abbrev dualProgram {m n : ℕ} (F : Bifun (Rn m) (Rn n)) : Bifun (Rn n) (Rn m) :=
  adjointBifun (pairing m) (pairing n) F

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- The book's defining formula for the adjoint. Rockafellar writes the two brackets as
`-⟨x, x*⟩ + ⟨u, u*⟩`; the backbone groups them inside one real subtraction, which cannot meet
`∞ - ∞`. -/
theorem dualProgram_apply (F : Bifun (Rn m) (Rn n)) (y : Rn n) (v : Rn m) :
    dualProgram F y v
      = ⨅ p : Rn m × Rn n, (F p.1 p.2 + ((pairing m p.1 v - pairing n p.2 y : ℝ) : EReal)) :=
  rfl

/-- **The objective function of `(P*)`**: `(F*0)(u*) = inf_u {⟨u, u*⟩ + inf Fu}`. -/
theorem dualProgram_zero_apply (F : Bifun (Rn m) (Rn n)) (v : Rn m) :
    dualProgram F 0 v = ⨅ u : Rn m, (((pairing m u v : ℝ) : EReal) + infBifun F u) :=
  adjointBifun_zero_apply (pairing m) (pairing n) F v

/-- **Rockafellar's definition of a normal convex program**: `(P)` is *normal* when its perturbation
function `inf F` is closed at `u = 0`. This is the backbone's `Normal`, unfolded. -/
theorem normal_iff_clFn_infBifun_zero (F : Bifun (Rn m) (Rn n)) :
    Normal F ↔ clFn (infBifun F) 0 = infBifun F 0 := Iff.rfl

/-- **Normality of the dual program**: `(P*)` is normal when `cl (sup F*)` agrees with `sup F*` at
`x* = 0`. -/
theorem concaveNormal_iff_clConcave_supBifun_zero (G : Bifun (Rn n) (Rn m)) :
    ConcaveNormal G ↔ clConcave (supBifun G) 0 = supBifun G 0 := Iff.rfl

/-! ### Theorem 30.1 -/

/-- **Theorem 30.1**, the concavity clause: the adjoint of *any* bifunction from `ℝᵐ` to `ℝⁿ` is a
concave bifunction from `ℝⁿ` to `ℝᵐ`. No hypothesis on `F` is used. -/
theorem theorem_30_1_concave (F : Bifun (Rn m) (Rn n)) : ConcaveBifun (dualProgram F) :=
  concaveBifun_adjointBifun (pairing m) (pairing n) F

/-- **Theorem 30.1**, the closedness clause: `F*` is a *closed* concave bifunction, again with no
hypothesis on `F`. -/
theorem theorem_30_1_closed (F : Bifun (Rn m) (Rn n)) :
    ClosedConcaveFn (graphFn (dualProgram F)) :=
  closedConcaveFn_graphFn_adjointBifun (Bu := pairing m) (Bx := pairing n) (F := F)

/-- **Theorem 30.1**, the properness clause: `F*` is proper if and only if `F` is, for a closed
convex `F`. -/
theorem theorem_30_1_proper (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    ProperConcave (graphFn (dualProgram F)) ↔ Proper (graphFn F) :=
  properConcave_graphFn_adjointBifun_iff (Bu := pairing m) (Bx := pairing n) hF hcl

/-- **Theorem 30.1**: `F** = cl F` for a convex bifunction. -/
theorem theorem_30_1_biadjoint (hF : ConvexBifun F) :
    concaveAdjointBifun (pairing m) (pairing n) (dualProgram F) = clBifun F :=
  concaveAdjointBifun_adjointBifun_eq_clBifun hF

/-- **Theorem 30.1**: `F** = F` when `F` is closed — which is why the program dual to `(P*)` is
`(P)` again. -/
theorem theorem_30_1_biadjoint_closed (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    concaveAdjointBifun (pairing m) (pairing n) (dualProgram F) = F :=
  concaveAdjointBifun_adjointBifun_eq_self hF hcl

/-- **Theorem 30.1**, the injectivity half of "the adjoint operation establishes a one-to-one
correspondence": two closed convex bifunctions with the same adjoint are equal. The
surjectivity half is `theorem_30_1_surjective`. -/
theorem theorem_30_1_injective {F₁ F₂ : Bifun (Rn m) (Rn n)} (hF₁ : ConvexBifun F₁)
    (hcl₁ : ClosedBifun F₁) (hF₂ : ConvexBifun F₂) (hcl₂ : ClosedBifun F₂)
    (h : dualProgram F₁ = dualProgram F₂) : F₁ = F₂ := by
  rw [← theorem_30_1_biadjoint_closed hF₁ hcl₁, ← theorem_30_1_biadjoint_closed hF₂ hcl₂, h]

/-- **Theorem 30.1**, the surjectivity half: every closed proper *concave* bifunction `G` from `ℝⁿ`
to `ℝᵐ` is the adjoint of a closed proper convex bifunction — namely of `G`'s own lower adjoint. -/
theorem theorem_30_1_surjective {G : Bifun (Rn n) (Rn m)} (hG : ConcaveBifun G)
    (hclG : ClosedConcaveFn (graphFn G)) (hpG : ProperConcave (graphFn G)) :
    ∃ F : Bifun (Rn m) (Rn n),
      ConvexBifun F ∧ ClosedBifun F ∧ Proper (graphFn F) ∧ dualProgram F = G := by
  have hgraph : graphFn (inverseBifun G)
      = compLin (fun q => -(graphFn G q)) (swapLin (Rn m) (Rn n)) := rfl
  have hconv : ConvexBifun (inverseBifun G) := by
    rw [convexBifun_iff, hgraph]
    exact convexFn_compLin _ (concaveFn_iff_convexFn_neg.1 hG)
  have hclosed : ClosedBifun (inverseBifun G) := by
    have hcont : Continuous (swapLin (Rn m) (Rn n)) := by
      change Continuous fun p : Rn m × Rn n => ((p.2, p.1) : Rn n × Rn m)
      exact continuous_snd.prodMk continuous_fst
    rw [closedBifun_iff, hgraph]
    exact closedFn_compLin (closedConcaveFn_iff.1 hclG) hcont
  have hdual : dualProgram (lowerAdjointBifun (pairing m) (pairing n) (inverseBifun G)) = G := by
    have hbi := lowerAdjointBifun_lowerAdjointBifun_eq_clBifun
      (Bu := pairing m) (Bx := pairing n) (F := inverseBifun G) hconv
    simp only [flip_pairing] at hbi
    rw [hclosed.clBifun_eq] at hbi
    funext y v
    have hval := congrFun (congrFun hbi v) y
    rw [lowerAdjointBifun_apply, inverseBifun_apply] at hval
    exact neg_inj.1 hval
  have hconvF : ConvexBifun (lowerAdjointBifun (pairing m) (pairing n) (inverseBifun G)) :=
    convexBifun_lowerAdjointBifun (pairing m) (pairing n) (inverseBifun G)
  have hclF : ClosedBifun (lowerAdjointBifun (pairing m) (pairing n) (inverseBifun G)) :=
    closedBifun_lowerAdjointBifun
  refine ⟨lowerAdjointBifun (pairing m) (pairing n) (inverseBifun G), hconvF, hclF, ?_, hdual⟩
  exact (theorem_30_1_proper hconvF hclF).1 (by rw [hdual]; exact hpG)

/-- **Theorem 30.1**, last clause: "If `F` is polyhedral, so is `F*`." The book's justification is
Theorem 19.2. Neither properness nor closedness is needed. -/
theorem theorem_30_1_polyhedral (hF : PolyhedralBifun F) :
    ConcavePolyhedralBifun (dualProgram F) :=
  polyhedralFn_neg_graphFn_adjointBifun (pairing m) (pairing n) hF

/-! ### The adjoint of an indicator bifunction

Rockafellar's first example of the adjoint operation, and the one that justifies the name: "the
adjoint operation for bifunctions can rightly be viewed as a generalization of the adjoint
operation for linear transformations". `linearIndicatorBifun` itself is §29's. -/

@[simp] theorem linearIndicatorBifun_self (A : Rn m →ₗ[ℝ] Rn n) (u : Rn m) :
    linearIndicatorBifun A u (A u) = 0 := by
  rw [linearIndicatorBifun_apply]
  exact indicatorFn_of_mem (Set.mem_singleton _)

theorem linearIndicatorBifun_of_ne (A : Rn m →ₗ[ℝ] Rn n) {u : Rn m} {x : Rn n} (h : x ≠ A u) :
    linearIndicatorBifun A u x = ⊤ := by
  rw [linearIndicatorBifun_apply]
  exact indicatorFn_of_notMem (by simpa using h)

private theorem iInf_linearIndicatorBifun_slice (A : Rn m →ₗ[ℝ] Rn n) (u v : Rn m) (y : Rn n) :
    (⨅ x : Rn n, (linearIndicatorBifun A u x + ((pairing m u v - pairing n x y : ℝ) : EReal)))
      = ((pairing m u (v - LinearMap.adjoint A y) : ℝ) : EReal) := by
  have hval : (pairing m u v - pairing n (A u) y : ℝ)
      = pairing m u (v - LinearMap.adjoint A y) := by
    rw [map_sub, isAdjointPair_adjoint A u y]
  refine le_antisymm (le_trans (iInf_le _ (A u)) (le_of_eq ?_)) (le_iInf fun x => ?_)
  · rw [linearIndicatorBifun_self, zero_add, hval]
  · by_cases hx : x = A u
    · subst hx
      rw [linearIndicatorBifun_self, zero_add, hval]
    · rw [linearIndicatorBifun_of_ne A hx, EReal.top_add_coe]
      exact le_top

private theorem iInf_pairing_coe (w : Rn m) :
    (⨅ u : Rn m, ((pairing m u w : ℝ) : EReal)) = ⨆ _ : w = 0, (0 : EReal) := by
  by_cases hw : w = 0
  · rw [iSup_pos hw, hw]
    simp
  · rw [iSup_neg hw]
    refine iInf_eq_bot.2 fun b hb => ?_
    obtain ⟨c, -, hcb⟩ := EReal.lt_iff_exists_real_btwn.1 hb
    have hpos : 0 < pairing m w w := by
      rw [pairing_apply]
      exact real_inner_self_pos.2 hw
    refine ⟨((c - 1) / (pairing m w w)) • w, ?_⟩
    have hval : pairing m (((c - 1) / (pairing m w w)) • w) w = c - 1 := by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hpos.ne']
    rw [hval]
    refine lt_trans ?_ hcb
    exact_mod_cast (by linarith : c - 1 < c)

/-- **§30**: the adjoint of the convex indicator bifunction of `A` is the *concave* indicator
bifunction of the adjoint transformation, `F*x* = -δ(· | A*x*)`. Here `A*` is `LinearMap.adjoint A`;
on `ℝⁿ` the adjoint is canonical, so it is not carried as data. -/
theorem dualProgram_linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) (y : Rn n) (v : Rn m) :
    dualProgram (linearIndicatorBifun A) y v = ⨆ _ : v = LinearMap.adjoint A y, (0 : EReal) := by
  rw [dualProgram_apply, iInf_prod]
  rw [iInf_congr fun u : Rn m => iInf_linearIndicatorBifun_slice A u v y, iInf_pairing_coe]
  by_cases h : v = LinearMap.adjoint A y
  · rw [iSup_pos h, iSup_pos (sub_eq_zero.2 h)]
  · rw [iSup_neg h, iSup_neg (fun hc => h (sub_eq_zero.1 hc))]

/-! ### Theorem 30.2 -/

/-- **Theorem 30.2**, first formula: `(-inf F)* = F*0`. The objective of the dual program is the
*concave* conjugate of the concave function `-inf F` — and not a statement about `conj`, since
`g* ≠ -(-g)*`. -/
theorem theorem_30_2_first (F : Bifun (Rn m) (Rn n)) :
    concaveConj (pairing m) (fun u => -(infBifun F u)) = dualProgram F 0 :=
  (adjointBifun_zero_eq_concaveConj (pairing m) (pairing n) F).symm

/-- **Theorem 30.2**, second formula: `(F*0)* = -cl (inf F)`. -/
theorem theorem_30_2_second (hF : ConvexBifun F) :
    concaveConj (pairing m) (dualProgram F 0) = fun u => -(clFn (infBifun F) u) := by
  have hconc : ConcaveFn (fun u => -(infBifun F u)) :=
    concaveFn_iff_convexFn_neg.2 (by simpa using convexFn_infBifun hF)
  have hbi := biconcaveConj_eq_clConcave (B := pairing m) hconc
  rw [← theorem_30_2_first F]
  have hflip : concaveConj (pairing m) (concaveConj (pairing m) (fun u => -(infBifun F u)))
      = biconcaveConj (pairing m) (fun u => -(infBifun F u)) := by
    rw [biconcaveConj, flip_pairing]
  rw [hflip, hbi]
  funext u
  rw [clConcave_apply]
  simp only [neg_neg]

/-- **Theorem 30.2**, third formula: `(-sup F*)* = F0`. For a closed convex `F` the objective of
`(P)` is the conjugate of the convex function `-sup F*`. -/
theorem theorem_30_2_third (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    conj (pairing n) (fun y => -(supBifun (dualProgram F) y)) = F 0 := by
  have h := concaveAdjointBifun_adjointBifun_eq_self (Bu := pairing m) (Bx := pairing n) hF hcl
  have h2 := concaveAdjointBifun_zero_eq_conj (pairing m) (pairing n) (dualProgram F)
  rw [flip_pairing] at h2
  rw [← h2, h]

/-- **Theorem 30.2**, fourth formula: `(F0)* = -cl (sup F*)`. -/
theorem theorem_30_2_fourth (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    conj (pairing n) (F 0) = fun y => -(clConcave (supBifun (dualProgram F)) y) := by
  have hconv : ConvexFn (fun y => -(supBifun (dualProgram F) y)) :=
    convexFn_neg_supBifun (concaveBifun_adjointBifun (pairing m) (pairing n) F)
  have hbi := biconj_eq_clFn (B := (pairing n).flip) hconv
  rw [← theorem_30_2_third hF hcl]
  have hflip : conj (pairing n) (conj (pairing n) (fun y => -(supBifun (dualProgram F) y)))
      = biconj (pairing n).flip (fun y => -(supBifun (dualProgram F) y)) := by
    rw [biconj, flip_pairing, flip_pairing]
  rw [hflip, hbi]
  funext y
  rw [clConcave_apply]
  simp only [neg_neg]

/-! ### The Lagrangian form of the two objectives -/

/-- **§30**, the remark after Theorem 30.2: the objective function of `(P*)` is the infimum of the
Lagrangian of `(P)` over the primal variable, `(F*0)(u*) = inf_x L(u*, x)`. -/
theorem dualProgram_zero_eq_iInf_lagrangian (F : Bifun (Rn m) (Rn n)) (v : Rn m) :
    dualProgram F 0 v = ⨅ x : Rn n, lagrangian (pairing m) F v x :=
  (iInf_lagrangian_eq_adjointBifun_zero (Bu := pairing m) (pairing n)).symm

/-- **§30**: for a closed convex `F` the objective function of `(P)` is the supremum of the
Lagrangian over the price variable, `(F0)(x) = sup_{u*} L(u*, x)`. -/
theorem objective_eq_iSup_lagrangian (hF : ConvexBifun F) (hcl : ClosedBifun F) (x : Rn n) :
    F 0 x = ⨆ v : Rn m, lagrangian (pairing m) F v x :=
  (iSup_lagrangian_eq (Bu := pairing m) hF hcl).symm

/-- **§30**: the optimal value of `(P*)` is `sup_{u*} inf_x L(u*, x)`. -/
theorem supBifun_dualProgram_eq_maximin (F : Bifun (Rn m) (Rn n)) :
    supBifun (dualProgram F) 0 = maximin (saddleLagrangian (pairing m) F) := by
  rw [supBifun_apply, maximin_apply]
  exact iSup_congr fun v => dualProgram_zero_eq_iInf_lagrangian F v

/-- **§30**: for a closed convex `F` the optimal value of `(P)` is `inf_x sup_{u*} L(u*, x)`.
Together with `supBifun_dualProgram_eq_maximin` this is why normality is the existence of a
saddle-value, the reading §36 takes up. -/
theorem infBifun_eq_minimax (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    infBifun F 0 = minimax (saddleLagrangian (pairing m) F) := by
  rw [infBifun_apply, minimax_apply]
  exact iInf_congr fun x => objective_eq_iSup_lagrangian hF hcl x

/-! ### Corollary 30.2.1 -/

/-- **Corollary 30.2.1**, first half: `(P*)` is inconsistent exactly when some perturbation of `(P)`
has no lower bound. Stated for an arbitrary convex `F`, although the book assumes closedness for the
whole corollary: the adjoint never sees the difference between `F` and `cl F`. -/
theorem corollary_30_2_1_dual (hF : ConvexBifun F) :
    ¬ ConcaveConsistent (dualProgram F) ↔ ∃ u : Rn m, infBifun F u = ⊥ :=
  not_concaveConsistent_adjointBifun_iff (Bu := pairing m) (pairing n) hF

/-- **Corollary 30.2.1**, first half, positively. -/
theorem corollary_30_2_1_dual' (hF : ConvexBifun F) :
    ConcaveConsistent (dualProgram F) ↔ ∀ u : Rn m, infBifun F u ≠ ⊥ :=
  concaveConsistent_adjointBifun_iff (Bu := pairing m) (pairing n) hF

/-- **Corollary 30.2.1**, second half: `(P)` is inconsistent exactly when some perturbation of
`(P*)` has no upper bound. This half really does need `F` closed — it is the first half read for the
dual pair, and `F** = F` is what identifies the objective of `(P)`. -/
theorem corollary_30_2_1_primal (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    ¬ Consistent F ↔ ∃ y : Rn n, supBifun (dualProgram F) y = ⊤ :=
  not_consistent_iff_exists_supBifun_eq_top (Bu := pairing m) (Bx := pairing n) hF hcl

/-- **Corollary 30.2.1**, second half, positively. -/
theorem corollary_30_2_1_primal' (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    Consistent F ↔ ∀ y : Rn n, supBifun (dualProgram F) y ≠ ⊤ :=
  consistent_iff_forall_supBifun_ne_top (Bu := pairing m) (Bx := pairing n) hF hcl

/-! ### Corollary 30.2.2 -/

/-- **Corollary 30.2.2**, first formula: `(cl (inf F))(0) = sup F*0`. Closedness of `F` is not used:
the formula is Fenchel–Moreau for `inf F`, and `F*` does not distinguish `F` from `cl F`. -/
theorem corollary_30_2_2_first (hF : ConvexBifun F) :
    clFn (infBifun F) 0 = supBifun (dualProgram F) 0 := by
  rw [supBifun_apply]
  exact clFn_infBifun_zero_eq_iSup_adjointBifun (Bu := pairing m) (pairing n) hF

/-- **Corollary 30.2.2**, second formula: `(cl (sup F*))(0) = inf F0`. Here closedness of `F` is
what turns `F**` back into `F`. -/
theorem corollary_30_2_2_second (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    clConcave (supBifun (dualProgram F)) 0 = infBifun F 0 :=
  clConcave_supBifun_adjointBifun_zero_eq (Bu := pairing m) (Bx := pairing n) hF hcl

/-- **Corollary 30.2.2**, weak duality: `inf F0 ≥ sup F*0`, always. No hypothesis at all — it is
`⟨u, u*⟩ + inf Fu` evaluated at `u = 0`. -/
theorem corollary_30_2_2_weak (F : Bifun (Rn m) (Rn n)) :
    supBifun (dualProgram F) 0 ≤ infBifun F 0 := by
  rw [supBifun_apply]
  exact iSup_adjointBifun_zero_le (pairing m) (pairing n) F

/-! ### Corollary 30.2.3 -/

/-- **Corollary 30.2.3**, first formula: unless *both* programs are inconsistent,
`liminf_{u → 0} (inf Fu) = sup F*0`. The excluded case is Rockafellar's own: the two sides differ
only when `cl (inf F)` is `-∞`, so `(P*)` is inconsistent, and the `liminf` is `+∞`, so `(P)` is. -/
theorem corollary_30_2_3_first (hF : ConvexBifun F)
    (h : Consistent F ∨ ConcaveConsistent (dualProgram F)) :
    Filter.liminf (infBifun F) (𝓝 (0 : Rn m)) = supBifun (dualProgram F) 0 := by
  rw [supBifun_apply]
  exact liminf_infBifun_eq_iSup_adjointBifun (Bu := pairing m) (pairing n) hF h

/-- **Corollary 30.2.3**, second formula: unless both programs are inconsistent,
`limsup_{x* → 0} (sup F*x*) = inf F0`. -/
theorem corollary_30_2_3_second (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (h : Consistent F ∨ ConcaveConsistent (dualProgram F)) :
    Filter.limsup (supBifun (dualProgram F)) (𝓝 (0 : Rn n)) = infBifun F 0 :=
  limsup_supBifun_adjointBifun_eq (Bu := pairing m) (Bx := pairing n) hF hcl h

/-! ### Theorem 30.3 -/

/-- **Theorem 30.3(a) ⟺ (c)**: a convex program is normal exactly when there is no duality gap.
Closedness of `F` is *not* needed, although the theorem carries it: only Corollary 30.2.2's first
formula is used. -/
theorem theorem_30_3_a_iff_c (hF : ConvexBifun F) :
    Normal F ↔ infBifun F 0 = supBifun (dualProgram F) 0 := by
  rw [normal_iff_iSup_adjointBifun_eq (Bu := pairing m) (pairing n) hF, supBifun_apply]
  exact eq_comm

/-- **Theorem 30.3(b) ⟺ (c)**. -/
theorem theorem_30_3_b_iff_c (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    ConcaveNormal (dualProgram F) ↔ infBifun F 0 = supBifun (dualProgram F) 0 := by
  rw [concaveNormal_adjointBifun_iff (Bu := pairing m) (Bx := pairing n) hF hcl, supBifun_apply]
  exact eq_comm

/-- **Theorem 30.3(a) ⟺ (b)**: a convex program is normal exactly when its dual is. -/
theorem theorem_30_3_a_iff_b (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    Normal F ↔ ConcaveNormal (dualProgram F) :=
  normal_iff_concaveNormal_adjointBifun (Bu := pairing m) (Bx := pairing n) hF hcl

/-- **Theorem 30.3**, the three clauses as the book states them: for a closed convex bifunction `F`,
`(P)` is normal, `(P*)` is normal, and the two optimal values agree, are equivalent. -/
theorem theorem_30_3 (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    [Normal F, ConcaveNormal (dualProgram F),
      infBifun F 0 = supBifun (dualProgram F) 0].TFAE := by
  tfae_have 1 ↔ 2 := theorem_30_3_a_iff_b hF hcl
  tfae_have 1 ↔ 3 := theorem_30_3_a_iff_c hF
  tfae_finish

/-! ### Theorem 30.4

Rockafellar argues (a), (c) and (e), says "Dually, (b), (d) and (f) imply that normality holds",
gives one compressed sentence for (g), and disposes of (h), (i) and (j) as "special cases" and "of
course … contained in". Each declaration below records what the book supplies for its own clause. -/

/-- **Theorem 30.4(a)**: a *strongly* consistent convex program is normal. **The book proves this
clause**, by the argument used here: `0 ∈ ri (dom (inf F))` by Theorem 29.1, and a convex function
agrees with its closure on the relative interior of its effective domain. -/
theorem theorem_30_4_a (hs : StronglyConsistent F) (hF : ConvexBifun F) : Normal F :=
  StronglyConsistent.normal hs hF

/-- **Theorem 30.4(a)**, the parenthetical *strict* form. -/
theorem theorem_30_4_a' (hs : StrictlyConsistent F) (hF : ConvexBifun F) : Normal F :=
  StrictlyConsistent.normal hs hF

/-- **Theorem 30.4(b)**: if the *dual* program is strongly consistent then normality holds for the
pair. **The book does not argue this clause** — "Dually, (b), (d) and (f) imply that normality
holds". The route here is the dual of (a) composed with Theorem 30.3(a) ⟺ (b). -/
theorem theorem_30_4_b (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hs : ConcaveStronglyConsistent (dualProgram F)) : Normal F :=
  normal_of_concaveStronglyConsistent_adjointBifun (Bu := pairing m) (Bx := pairing n) hF hcl hs

/-- **Theorem 30.4(c)**: if `(P)` has a Kuhn–Tucker vector — its optimal value being finite, which
is part of the definition — then `(P)` is normal. **The book proves this clause**, from Theorem 29.1
and Corollary 23.5.2; the route here is cheaper, weak duality pinning the dual optimal value. -/
theorem theorem_30_4_c (hF : ConvexBifun F) (h : (KuhnTucker (pairing m) F).Nonempty) :
    Normal F :=
  normal_of_kuhnTucker_nonempty (Bu := pairing m) (pairing n) hF h

/-- **Theorem 30.4(d)**: if the *dual* program has a Kuhn–Tucker vector then normality holds for the
pair. **The book does not argue this clause.** -/
theorem theorem_30_4_d (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (h : (ConcaveKuhnTucker (pairing n) (dualProgram F)).Nonempty) : Normal F := by
  refine normal_of_concaveKuhnTucker_adjointBifun_nonempty (Bu := pairing m) (Bx := pairing n)
    hF hcl ?_
  rwa [flip_pairing]

/-- **Theorem 30.4(e)**: a polyhedral convex program that is merely *consistent* is normal. **The
book proves this clause**: Theorem 29.2 makes `inf F` polyhedral, and a polyhedral convex function
agrees with its closure throughout its effective domain. -/
theorem theorem_30_4_e (hF : PolyhedralBifun F) (hc : Consistent F) : Normal F :=
  PolyhedralBifun.normal hF hc

/-- **Theorem 30.4(f)**: if `(P*)` is polyhedral and consistent then normality holds for the pair.
**The book does not argue this clause.** By `theorem_30_1_polyhedral` the hypothesis follows from
polyhedrality of `F`, which is how the Gale–Kuhn–Tucker theorem below uses it. -/
theorem theorem_30_4_f (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hG : ConcavePolyhedralBifun (dualProgram F)) (hc : ConcaveConsistent (dualProgram F)) :
    Normal F :=
  normal_of_concavePolyhedral_adjointBifun (Bu := pairing m) (Bx := pairing n) hF hcl hG hc

/-- **Theorem 30.4(g)**: if some sublevel set of the objective `F0` is non-empty and bounded, then
normality holds.

**The book's one sentence hides the argument**: "Condition (g) is equivalent by Theorem 27.1(d) to
having `0 ∈ int (dom (F0)*)`, i.e. `(P*)` strictly consistent." The "i.e." is not an abbreviation —
strict consistency of `(P*)` is an interior condition on an intersection over *all* perturbations —
and what closes it is that all slices of a closed convex bifunction have the same recession
function, so the two sets are in fact equal. No properness is assumed: an improper closed convex
bifunction has `inf F0 = -∞` and is normal automatically. -/
theorem theorem_30_4_g (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (h : ∃ α : ℝ, {x : Rn n | F 0 x ≤ (α : EReal)}.Nonempty ∧
      Bornology.IsBounded {x : Rn n | F 0 x ≤ (α : EReal)}) : Normal F :=
  normal_of_exists_setOf_le (Bu := pairing m) (Bx := pairing n) hF hcl h

/-- **Theorem 30.4(h)**: if some superlevel set of the dual objective `F*0` is non-empty and
bounded, then normality holds. **The book does not argue this clause.** The route here is not the
book's: `-F*` is a closed convex bifunction with no hypothesis on `F`, so clause (g) applies to it
and Theorem 30.3 transports the conclusion back. -/
theorem theorem_30_4_h (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (h : ∃ α : ℝ, {v : Rn m | (α : EReal) ≤ dualProgram F 0 v}.Nonempty ∧
      Bornology.IsBounded {v : Rn m | (α : EReal) ≤ dualProgram F 0 v}) : Normal F :=
  normal_of_exists_setOf_ge_adjointBifun (Bu := pairing m) (Bx := pairing n) hF hcl h

/-- **Theorem 30.4(i)**: if the optimal solutions to `(P)` form a non-empty bounded set — in
particular if there is exactly one — then normality holds.

**As the book states it the clause is false**: the asserted containment in (g) needs `F0` proper,
since with `F0 ≡ +∞` the set of optimal solutions is non-empty and bounded while no sublevel set is.
With `Proper (F 0)`, `argmin (F0)` is a level set of `F0` at its minimum value and (g) applies. -/
theorem theorem_30_4_i (hF : ConvexBifun F) (hcl : ClosedBifun F) (hp : Proper (F 0))
    (hne : (argmin (F 0)).Nonempty) (hbd : Bornology.IsBounded (argmin (F 0))) : Normal F :=
  normal_of_argmin_nonempty_and_isBounded (Bu := pairing m) (Bx := pairing n) hF hcl hp hne hbd

/-- **Theorem 30.4(j)**: if the optimal solutions to `(P*)` form a non-empty bounded set then
normality holds. As in (i), the containment the book asserts needs properness of the dual
objective. -/
theorem theorem_30_4_j (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hp : Proper fun v => -(dualProgram F 0 v))
    (hne : (argmax (dualProgram F 0)).Nonempty)
    (hbd : Bornology.IsBounded (argmax (dualProgram F 0))) : Normal F :=
  normal_of_argmax_adjointBifun_nonempty_and_isBounded (Bu := pairing m) (Bx := pairing n)
    hF hcl hp hne hbd

/-- **The Gale–Kuhn–Tucker Duality Theorem**, which Rockafellar names in running text with no
numbered statement of its own: for a polyhedral closed convex bifunction the optimal values of `(P)`
and `(P*)` are equal unless both programs are inconsistent.

Stated at the generality the argument actually has — the book applies it to a particular dual pair
of linear programs, saying "these are polyhedral convex programs, so it follows". Clause (e) covers
consistent `(P)` and clause (f), fed by `theorem_30_1_polyhedral`, consistent `(P*)`. Closedness is
free in the intended application: a proper polyhedral convex bifunction is closed. -/
theorem gale_kuhn_tucker_duality (hF : PolyhedralBifun F) (hcl : ClosedBifun F)
    (h : Consistent F ∨ ConcaveConsistent (dualProgram F)) :
    infBifun F 0 = supBifun (dualProgram F) 0 := by
  refine (theorem_30_3_a_iff_c hF.convexBifun).1 ?_
  rcases h with hc | hc
  · exact theorem_30_4_e hF hc
  · exact theorem_30_4_f hF.convexBifun hcl (theorem_30_1_polyhedral hF) hc

/-! ### Theorem 30.5 -/

/-- **Theorem 30.5**, first assertion: under normality, `u*` is a Kuhn–Tucker vector for `(P)` if
and only if `u*` is an optimal solution to `(P*)`. -/
theorem theorem_30_5 (hF : ConvexBifun F) (hn : Normal F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) (v : Rn m) :
    v ∈ KuhnTucker (pairing m) F ↔ v ∈ argmax (dualProgram F 0) := by
  rw [mem_kuhnTucker_iff_adjointBifun_zero_eq_iSup (Bu := pairing m) (pairing n) hF hn ht hb,
    mem_argmax_iff_eq_iSup]

/-- **Theorem 30.5**, second assertion: under normality, `x` is a Kuhn–Tucker vector for `(P*)` if
and only if `x` is an optimal solution to `(P)`. The book says only "the proof of the dual assertion
of the theorem is parallel" and does not carry it out. -/
theorem theorem_30_5_dual (hF : ConvexBifun F) (hcl : ClosedBifun F) (hn : Normal F)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) (x : Rn n) :
    x ∈ ConcaveKuhnTucker (pairing n) (dualProgram F) ↔ x ∈ argmin (F 0) := by
  have h := mem_concaveKuhnTucker_adjointBifun_iff_mem_argmin (Bu := pairing m) (Bx := pairing n)
    (x := x) hF hcl hn ht hb
  rw [flip_pairing] at h
  exact h

/-! ### Corollary 30.5.1 -/

/-- **Corollary 30.5.1**, (b) ⟺ (c): `(ū*, x̄)` is a saddle-point of the Lagrangian exactly when
`(F0)(x̄) ≤ (F*0)(ū*)` — in which case weak duality forces equality. -/
theorem corollary_30_5_1_b_iff_c (hF : ConvexBifun F) (hcl : ClosedBifun F) (v : Rn m) (x : Rn n) :
    IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x) ↔ F 0 x ≤ dualProgram F 0 v :=
  isSaddlePoint_lagrangian_iff_le_adjointBifun (Bu := pairing m) (pairing n) hF hcl

/-- **Corollary 30.5.1**, (a) ⟺ (b): `(ū*, x̄)` is a saddle-point of the Lagrangian exactly when
normality holds and `x̄`, `ū*` are optimal solutions to `(P)` and `(P*)`. The book's proof is
"immediate from Theorem 29.3", the existence of a Kuhn–Tucker vector implying normality. -/
theorem corollary_30_5_1_a_iff_b (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (v : Rn m) (x : Rn n) :
    IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x)
      ↔ Normal F ∧ x ∈ argmin (F 0) ∧ v ∈ argmax (dualProgram F 0) := by
  rw [isSaddlePoint_lagrangian_iff_normal_and_optimal (Bu := pairing m) (pairing n) hF hcl hpr,
    mem_argmax_iff_eq_iSup]

/-- **Corollary 30.5.1**, (a) ⟺ (c). -/
theorem corollary_30_5_1_a_iff_c (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (v : Rn m) (x : Rn n) :
    (Normal F ∧ x ∈ argmin (F 0) ∧ v ∈ argmax (dualProgram F 0))
      ↔ F 0 x ≤ dualProgram F 0 v :=
  (corollary_30_5_1_a_iff_b hF hcl hpr v x).symm.trans (corollary_30_5_1_b_iff_c hF hcl v x)

/-- **Corollary 30.5.1**, the three clauses as the book states them. -/
theorem corollary_30_5_1 (hF : ConvexBifun F) (hcl : ClosedBifun F) (hpr : Proper (graphFn F))
    (v : Rn m) (x : Rn n) :
    [Normal F ∧ x ∈ argmin (F 0) ∧ v ∈ argmax (dualProgram F 0),
      IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x),
      F 0 x ≤ dualProgram F 0 v].TFAE := by
  tfae_have 1 ↔ 2 := (corollary_30_5_1_a_iff_b hF hcl hpr v x).symm
  tfae_have 2 ↔ 3 := corollary_30_5_1_b_iff_c hF hcl v x
  tfae_finish

/-- **Corollary 30.5.1**, the parenthesis: when clause (c) holds, equality actually holds. This is
weak duality (Corollary 30.2.2) in the other direction. -/
theorem corollary_30_5_1_eq (F : Bifun (Rn m) (Rn n)) (v : Rn m) (x : Rn n)
    (h : F 0 x ≤ dualProgram F 0 v) : F 0 x = dualProgram F 0 v :=
  le_antisymm h ((adjointBifun_zero_le (pairing m) (pairing n) F v).trans
    (iInf_le (fun z => F 0 z) x))

/-! ### Corollary 30.5.2 -/

/-- The optimal value of a consistent program is not `+∞`. -/
private theorem infBifun_zero_ne_top (hc : Consistent F) : infBifun F 0 ≠ ⊤ := by
  obtain ⟨x, hx⟩ := hc
  rw [infBifun_apply]
  intro hcon
  exact hx (iInf_eq_top.1 hcon x)

/-- If the dual is consistent and normality holds, the optimal value is not `-∞`. -/
private theorem infBifun_zero_ne_bot (hF : ConvexBifun F) (hn : Normal F)
    (hc : ConcaveConsistent (dualProgram F)) : infBifun F 0 ≠ ⊥ := by
  obtain ⟨v, hv⟩ := hc
  rw [(theorem_30_3_a_iff_c hF).1 hn, supBifun_apply]
  intro hcon
  exact hv (iSup_eq_bot.1 hcon v)

/-- **Corollary 30.5.2**, second assertion: if `(P)` is strongly consistent and `(P*)` is consistent
then `(P*)` has an optimal solution. Theorem 30.4(a) gives normality, so the common optimal value is
finite, Corollary 29.1.4 supplies a Kuhn–Tucker vector, and Theorem 30.5 makes it optimal. -/
theorem corollary_30_5_2_dual (hF : ConvexBifun F) (hs : StronglyConsistent F)
    (hc : ConcaveConsistent (dualProgram F)) : (argmax (dualProgram F 0)).Nonempty := by
  have hn : Normal F := theorem_30_4_a hs hF
  have ht : infBifun F 0 ≠ ⊤ := infBifun_zero_ne_top hs.consistent
  have hb : infBifun F 0 ≠ ⊥ := infBifun_zero_ne_bot hF hn hc
  obtain ⟨v, hv⟩ := kuhnTucker_nonempty_of_stronglyConsistent (B := pairing m) hF
    (proper_infBifun_of_stronglyConsistent hF hs hb) hs ht
  exact ⟨v, (theorem_30_5 hF hn ht hb v).1 hv⟩

/-- **Corollary 30.5.2**, first assertion: if `(P)` is consistent and `(P*)` is strongly consistent
then `(P)` has an optimal solution. This is the assertion the book proves, through the *concave*
Corollary 29.1.4; the route here runs the convex one on `-F*` instead. -/
theorem corollary_30_5_2 (hF : ConvexBifun F) (hcl : ClosedBifun F) (hc : Consistent F)
    (hs : ConcaveStronglyConsistent (dualProgram F)) : (argmin (F 0)).Nonempty := by
  have hn : Normal F := theorem_30_4_b hF hcl hs
  have hb : infBifun F 0 ≠ ⊥ := infBifun_zero_ne_bot hF hn hs.concaveConsistent
  obtain ⟨x, hx⟩ := exists_infBifun_eq_of_concaveStronglyConsistent (Bu := pairing m)
    (Bx := pairing n) hF hcl hc hb hs
  exact ⟨x, mem_argmin_iff_eq_iInf.2 (hx.trans (infBifun_apply F 0))⟩

/-! ### The section's two counterexamples: the toolkit

Both of Rockafellar's unnumbered examples are bifunctions from `R` to `R`, so both live on `Rn 1`.
These are the coordinate lemmas they share. -/

/-- The point of `Rn 1` with coordinate `t`. -/
private noncomputable def coord1 (t : ℝ) : Rn 1 := WithLp.toLp 2 ![t]

@[simp] private theorem coord1_apply (t : ℝ) : coord1 t 0 = t := rfl

@[simp] private theorem zero_coord (i : Fin 1) : (0 : Rn 1) i = 0 := rfl

private theorem ext_one {x y : Rn 1} (h : x 0 = y 0) : x = y := by
  ext i
  fin_cases i
  exact h

private theorem pairing_one (u v : Rn 1) : pairing 1 u v = u 0 * v 0 := by
  simp [PiLp.inner_apply, mul_comm]

private theorem smul_coord (a : ℝ) (x : Rn 1) : (a • x) 0 = a * x 0 := rfl

private theorem tendsto_coord1 :
    Filter.Tendsto (fun k : ℕ => ((1 / (k + 1) : ℝ)) • coord1 1) Filter.atTop (nhds 0) := by
  have hc : Continuous fun c : ℝ => c • coord1 1 := continuous_id.smul continuous_const
  have h := (hc.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  rw [zero_smul] at h
  exact h

/-! ### An unnumbered counterexample: an abnormal program with a duality gap

"There do exist convex programs which are not normal … For an example of abnormality consider the
closed proper convex bifunction `F` from `R` to `R` defined by `(Fu)(x) = exp(-√(ux))` if
`u ≥ 0, x ≥ 0`, and `+∞` otherwise." -/

/-- **§30**, the abnormal example: `(Fu)(x) = exp(-√(ux))` on the closed first quadrant, `+∞` off
it. The domain condition is carried as a `⨅` over a proposition, which keeps `Decidable` out of the
statement.

Rockafellar calls this "the closed proper convex bifunction `F`". Convexity is **not** proved here:
it is the concavity of the geometric mean on the first quadrant composed with `exp`, elementary
two-variable real analysis with no convex-analytic content. What is proved is the perturbation
function the book displays, the duality gap `abnormalBifun_duality_gap` — `inf F0 = 1` against
`sup F*0 = 0` — and the failure of normality, the last from the perturbation function alone. -/
noncomputable def abnormalBifun (u x : Rn 1) : EReal :=
  ⨅ _ : 0 ≤ u 0 ∧ 0 ≤ x 0, ((Real.exp (-Real.sqrt (u 0 * x 0)) : ℝ) : EReal)

/-- The value of the abnormal example on the first quadrant. -/
theorem abnormalBifun_of_mem {u x : Rn 1} (h : 0 ≤ u 0 ∧ 0 ≤ x 0) :
    abnormalBifun u x = ((Real.exp (-Real.sqrt (u 0 * x 0)) : ℝ) : EReal) :=
  iInf_pos h

/-- The value of the abnormal example off the first quadrant. -/
theorem abnormalBifun_of_notMem {u x : Rn 1} (h : ¬ (0 ≤ u 0 ∧ 0 ≤ x 0)) :
    abnormalBifun u x = ⊤ :=
  iInf_neg h

/-- Every value of the abnormal example is `≥ 0`: the exponential is positive. -/
theorem zero_le_abnormalBifun (u x : Rn 1) : 0 ≤ abnormalBifun u x := by
  by_cases h : 0 ≤ u 0 ∧ 0 ≤ x 0
  · rw [abnormalBifun_of_mem h]
    exact_mod_cast (Real.exp_pos _).le
  · rw [abnormalBifun_of_notMem h]
    exact le_top

/-- Hence every value of the perturbation function is `≥ 0`. -/
theorem zero_le_infBifun_abnormalBifun (u : Rn 1) : 0 ≤ infBifun abnormalBifun u :=
  le_iInf fun x => zero_le_abnormalBifun u x

/-- **§30**: the optimal value of `(P)` is `1`. At `u = 0` the objective is `exp(-√0) = 1` on the
whole non-negative axis. -/
theorem infBifun_abnormalBifun_zero : infBifun abnormalBifun 0 = 1 := by
  refine le_antisymm ?_ (le_iInf fun x => ?_)
  · refine le_trans (iInf_le _ (0 : Rn 1)) (le_of_eq ?_)
    rw [abnormalBifun_of_mem (u := (0 : Rn 1)) (x := (0 : Rn 1)) ⟨le_rfl, le_rfl⟩]
    norm_num
  · by_cases h : 0 ≤ (0 : Rn 1) 0 ∧ 0 ≤ x 0
    · rw [abnormalBifun_of_mem h, zero_coord, zero_mul, Real.sqrt_zero, neg_zero, Real.exp_zero]
      exact le_rfl
    · rw [abnormalBifun_of_notMem h]
      exact le_top

/-- `exp(-1/ε) ≤ ε` for `ε > 0`, from `1 + r ≤ exp r`. This is the whole analytic content of the
example: `exp(-√(ux))` can be driven below any positive number by moving out along `x`. -/
private theorem exp_neg_le {ε : ℝ} (hε : 0 < ε) : Real.exp (-(1 / ε)) ≤ ε := by
  have hexp : 0 < Real.exp (1 / ε) := Real.exp_pos _
  have hkey : 1 / ε + 1 ≤ Real.exp (1 / ε) := Real.add_one_le_exp _
  have h1 : ε * (1 / ε) = 1 := by field_simp
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ hexp]
  nlinarith [mul_le_mul_of_nonneg_left hkey hε.le]

/-- **§30**: `inf Fu = 0` for every `u > 0`. -/
theorem infBifun_abnormalBifun_of_pos {u : Rn 1} (hu : 0 < u 0) :
    infBifun abnormalBifun u = 0 := by
  refine le_antisymm (EReal.le_zero_of_forall_le_pos fun ε hε => ?_)
    (zero_le_infBifun_abnormalBifun u)
  refine le_trans (iInf_le _ (coord1 ((1 / ε) ^ 2 / u 0))) ?_
  have hx : 0 ≤ (1 / ε) ^ 2 / u 0 := by positivity
  rw [abnormalBifun_of_mem (u := u) (x := coord1 ((1 / ε) ^ 2 / u 0))
    ⟨hu.le, by rw [coord1_apply]; exact hx⟩, coord1_apply]
  have hval : u 0 * ((1 / ε) ^ 2 / u 0) = (1 / ε) ^ 2 := by field_simp
  rw [hval, Real.sqrt_sq (by positivity)]
  exact EReal.coe_le_coe_iff.2 (exp_neg_le hε)

/-- **§30**: `inf Fu = +∞` for `u < 0` — the program is inconsistent for negative perturbations. -/
theorem infBifun_abnormalBifun_of_neg {u : Rn 1} (hu : u 0 < 0) :
    infBifun abnormalBifun u = ⊤ :=
  le_antisymm le_top (le_iInf fun x => by
    rw [abnormalBifun_of_notMem (fun h => absurd h.1 (not_le.2 hu))])

/-- **§30**: the optimal value of `(P*)` is `0`, so `(P)` and `(P*)` have a genuine duality gap:
`inf F0 = 1` while `sup F*0 = 0`. -/
theorem supBifun_dualProgram_abnormalBifun_zero :
    supBifun (dualProgram abnormalBifun) 0 = 0 := by
  refine le_antisymm ?_ ?_
  · rw [supBifun_apply]
    refine iSup_le fun v => EReal.le_zero_of_forall_le_pos fun ε hε => ?_
    rw [dualProgram_zero_apply]
    set t : ℝ := ε / (|v 0| + 1) with ht
    have hden : 0 < |v 0| + 1 := by positivity
    have htpos : 0 < t := by rw [ht]; positivity
    refine le_trans (iInf_le _ (coord1 t)) ?_
    rw [pairing_one, coord1_apply,
      infBifun_abnormalBifun_of_pos (u := coord1 t) (by rw [coord1_apply]; exact htpos), add_zero]
    have hle : t * v 0 ≤ ε := by
      have h1 : v 0 ≤ |v 0| := le_abs_self _
      have h2 : t * (|v 0| + 1) = ε := by rw [ht]; field_simp
      nlinarith [htpos.le]
    exact_mod_cast hle
  · refine le_trans ?_ (le_iSup (fun v => dualProgram abnormalBifun 0 v) (0 : Rn 1))
    rw [dualProgram_zero_apply]
    refine le_iInf fun u => ?_
    rw [pairing_one, zero_coord, mul_zero]
    simpa using zero_le_infBifun_abnormalBifun u

/-- **§30**: the abnormal example really has a duality gap. -/
theorem abnormalBifun_duality_gap :
    supBifun (dualProgram abnormalBifun) 0 ≠ infBifun abnormalBifun 0 := by
  rw [supBifun_dualProgram_abnormalBifun_zero, infBifun_abnormalBifun_zero]
  exact fun h => absurd h.symm one_ne_zero

/-- **§30**: the example is *not normal* — `(cl (inf F))(0) = 0` while `(inf F)(0) = 1`. Proved
directly from the perturbation function with no appeal to convexity of `F`: the closure is below the
lower semicontinuous hull, and `inf F` vanishes along `u_k = 1/(k+1) → 0`. -/
theorem not_normal_abnormalBifun : ¬ Normal abnormalBifun := by
  intro hn
  rw [normal_iff_clFn_infBifun_zero, infBifun_abnormalBifun_zero] at hn
  have hle : clFn (infBifun abnormalBifun) 0 ≤ 0 := by
    refine le_trans (clFn_le_lscHull _ 0) ?_
    rw [lscHull_eq_liminf, Filter.liminf_eq]
    refine sSup_le fun a ha => ?_
    obtain ⟨k, hk⟩ := (tendsto_coord1.eventually ha).exists
    rwa [infBifun_abnormalBifun_of_pos (u := ((1 / (k + 1) : ℝ)) • coord1 1)
      (by rw [smul_coord, coord1_apply, mul_one]; positivity)] at hk
  rw [hn] at hle
  exact absurd hle (by norm_num)

/-! ### An unnumbered counterexample: a normal program whose dual has no optimal solution

"An example of a normal convex program `(P)`, such that `(P)` has an optimal solution but `(P*)` has
no optimal solution, is obtained when `F` is the closed convex bifunction from `R` to `R` given by
`(Fu)(x) = x` if `x² ≤ u`, `+∞` if `x² > u`." -/

/-- **§30.** The example: `(Fu)(x) = x` on `{x² ≤ u}`, `+∞` off it. -/
noncomputable def noDualSolutionBifun (u x : Rn 1) : EReal :=
  ⨅ _ : (x 0) ^ 2 ≤ u 0, ((x 0 : ℝ) : EReal)

/-- The value of the example on its effective domain. -/
theorem noDualSolutionBifun_of_le {u x : Rn 1} (h : (x 0) ^ 2 ≤ u 0) :
    noDualSolutionBifun u x = ((x 0 : ℝ) : EReal) :=
  iInf_pos h

/-- The value of the example off its effective domain. -/
theorem noDualSolutionBifun_of_lt {u x : Rn 1} (h : u 0 < (x 0) ^ 2) :
    noDualSolutionBifun u x = ⊤ :=
  iInf_neg (not_le.2 h)

private theorem noDualSolutionBifun_ne_bot (u x : Rn 1) : noDualSolutionBifun u x ≠ ⊥ := by
  by_cases h : (x 0) ^ 2 ≤ u 0
  · rw [noDualSolutionBifun_of_le h]
    exact EReal.coe_ne_bot _
  · rw [noDualSolutionBifun_of_lt (not_le.1 h)]
    exact top_ne_bot

/-- The objective of `(P)` vanishes at the origin. -/
theorem noDualSolutionBifun_zero_zero : noDualSolutionBifun 0 (0 : Rn 1) = 0 := by
  rw [noDualSolutionBifun_of_le (u := (0 : Rn 1)) (x := (0 : Rn 1)) (by simp)]
  simp

/-- The objective of `(P)` is `+∞` away from the origin: `x² ≤ 0` forces `x = 0`. -/
theorem noDualSolutionBifun_zero_of_ne {x : Rn 1} (hx : x ≠ 0) :
    noDualSolutionBifun 0 x = ⊤ := by
  refine noDualSolutionBifun_of_lt ?_
  rw [zero_coord]
  by_contra hcon
  rw [not_lt] at hcon
  have hx0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0)]
  exact hx (ext_one (by rw [hx0, zero_coord]))

/-- **§30**: `x = 0` is the unique optimal solution to `(P)`. -/
theorem argmin_noDualSolutionBifun : argmin (noDualSolutionBifun 0) = {(0 : Rn 1)} := by
  ext x
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hx
    by_contra hne
    have h := hx 0
    rw [noDualSolutionBifun_zero_of_ne hne, noDualSolutionBifun_zero_zero] at h
    exact absurd h (by simp)
  · rintro rfl
    intro z
    rw [noDualSolutionBifun_zero_zero]
    by_cases hz : z = 0
    · rw [hz, noDualSolutionBifun_zero_zero]
    · rw [noDualSolutionBifun_zero_of_ne hz]
      exact le_top

/-- The optimal value of `(P)` is `0`. -/
theorem infBifun_noDualSolutionBifun_zero : infBifun noDualSolutionBifun 0 = 0 := by
  rw [infBifun_apply]
  refine le_antisymm (le_trans (iInf_le _ (0 : Rn 1))
    (le_of_eq noDualSolutionBifun_zero_zero)) (le_iInf fun z => ?_)
  by_cases hz : z = 0
  · rw [hz, noDualSolutionBifun_zero_zero]
  · rw [noDualSolutionBifun_zero_of_ne hz]
    exact le_top

private theorem convex_noDualSolutionSet :
    Convex ℝ {p : Rn 1 × Rn 1 | (p.2 0) ^ 2 ≤ p.1 0} := by
  intro p hp q hq a b ha hb hab
  have hp' : (p.2 0) ^ 2 ≤ p.1 0 := hp
  have hq' : (q.2 0) ^ 2 ≤ q.1 0 := hq
  change ((a • p + b • q).2 0) ^ 2 ≤ (a • p + b • q).1 0
  have h1 : (a • p + b • q).1 0 = a * p.1 0 + b * q.1 0 := rfl
  have h2 : (a • p + b • q).2 0 = a * p.2 0 + b * q.2 0 := rfl
  rw [h1, h2]
  have key : a * p.2 0 ^ 2 + b * q.2 0 ^ 2 - (a * p.2 0 + b * q.2 0) ^ 2
      = a * b * (p.2 0 - q.2 0) ^ 2 := by
    linear_combination (-(a * p.2 0 ^ 2 + b * q.2 0 ^ 2)) * hab
  have hnn : 0 ≤ a * b * (p.2 0 - q.2 0) ^ 2 := mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
  have h3 : a * p.2 0 ^ 2 ≤ a * p.1 0 := mul_le_mul_of_nonneg_left hp' ha
  have h4 : b * q.2 0 ^ 2 ≤ b * q.1 0 := mul_le_mul_of_nonneg_left hq' hb
  linarith

private theorem graphFn_noDualSolutionBifun :
    graphFn noDualSolutionBifun
      = fun p : Rn 1 × Rn 1 =>
          indicatorFn {q : Rn 1 × Rn 1 | (q.2 0) ^ 2 ≤ q.1 0} p + ((p.2 0 : ℝ) : EReal) := by
  funext p
  by_cases h : (p.2 0) ^ 2 ≤ p.1 0
  · rw [indicatorFn_of_mem (s := {q : Rn 1 × Rn 1 | (q.2 0) ^ 2 ≤ q.1 0}) h, zero_add]
    exact noDualSolutionBifun_of_le h
  · rw [indicatorFn_of_notMem (s := {q : Rn 1 × Rn 1 | (q.2 0) ^ 2 ≤ q.1 0}) h,
      EReal.top_add_coe]
    exact noDualSolutionBifun_of_lt (not_le.1 h)

/-- The example is a convex bifunction: its graph function is a linear coordinate added to the
indicator of the convex set `{(u, x) | x² ≤ u}`. -/
theorem convexBifun_noDualSolutionBifun : ConvexBifun noDualSolutionBifun := by
  rw [convexBifun_iff, graphFn_noDualSolutionBifun]
  exact convexFn_add_coe (l := fun p : Rn 1 × Rn 1 => p.2 0)
    (convexFn_indicatorFn.2 convex_noDualSolutionSet) fun _ _ _ _ _ => rfl

/-- The example is a closed bifunction: its epigraph is cut out by two continuous inequalities. -/
theorem closedBifun_noDualSolutionBifun : ClosedBifun noDualSolutionBifun := by
  have hne : ∀ p : Rn 1 × Rn 1, graphFn noDualSolutionBifun p ≠ ⊥ := fun p =>
    noDualSolutionBifun_ne_bot p.1 p.2
  rw [closedBifun_iff, closedFn_iff_lowerSemicontinuous hne,
    lowerSemicontinuous_iff_isClosed_epi]
  have hc1 : Continuous fun q : (Rn 1 × Rn 1) × ℝ => q.1.2 0 :=
    (continuous_coord 0).comp (continuous_snd.comp continuous_fst)
  have hc2 : Continuous fun q : (Rn 1 × Rn 1) × ℝ => q.1.1 0 :=
    (continuous_coord 0).comp (continuous_fst.comp continuous_fst)
  have hset : epi (graphFn noDualSolutionBifun)
      = {q : (Rn 1 × Rn 1) × ℝ | (q.1.2 0) ^ 2 ≤ q.1.1 0} ∩ {q | q.1.2 0 ≤ q.2} := by
    ext q
    constructor
    · intro hq
      have hq' : graphFn noDualSolutionBifun q.1 ≤ ((q.2 : ℝ) : EReal) := hq
      by_cases hm : (q.1.2 0) ^ 2 ≤ q.1.1 0
      · refine ⟨hm, ?_⟩
        have hval : graphFn noDualSolutionBifun q.1 = ((q.1.2 0 : ℝ) : EReal) :=
          noDualSolutionBifun_of_le hm
        rw [hval] at hq'
        exact_mod_cast hq'
      · exfalso
        have hval : graphFn noDualSolutionBifun q.1 = ⊤ :=
          noDualSolutionBifun_of_lt (not_le.1 hm)
        rw [hval] at hq'
        exact absurd (top_le_iff.1 hq') (by simp)
    · rintro ⟨hm, hle⟩
      have hval : graphFn noDualSolutionBifun q.1 = ((q.1.2 0 : ℝ) : EReal) :=
        noDualSolutionBifun_of_le hm
      change graphFn noDualSolutionBifun q.1 ≤ ((q.2 : ℝ) : EReal)
      rw [hval]
      exact_mod_cast hle
  rw [hset]
  exact (isClosed_le (hc1.pow 2) hc2).inter (isClosed_le hc1 continuous_snd)

/-- The objective of `(P)` is a proper convex function. -/
theorem proper_noDualSolutionBifun_zero : Proper (noDualSolutionBifun 0) :=
  ⟨⟨0, by rw [mem_dom, noDualSolutionBifun_zero_zero]; simp⟩,
    fun x => noDualSolutionBifun_ne_bot 0 x⟩

/-- **§30**: the example *is* normal. Rockafellar reads this off the lower semicontinuity of
`inf Fu = -√u` at `u = 0`; here it is Theorem 30.4(i), since the set of optimal solutions is the
single point `0`. -/
theorem normal_noDualSolutionBifun : Normal noDualSolutionBifun :=
  theorem_30_4_i convexBifun_noDualSolutionBifun closedBifun_noDualSolutionBifun
    proper_noDualSolutionBifun_zero
    (by rw [argmin_noDualSolutionBifun]; exact Set.singleton_nonempty _)
    (by rw [argmin_noDualSolutionBifun]; exact Bornology.isBounded_singleton)

/-- **§30**: `inf Fu ≤ -√u` for `u ≥ 0`. The infimum is attained at `x = -√u`, the left endpoint of
`{x | x² ≤ u}`; only this half of the book's display is needed. -/
theorem infBifun_noDualSolutionBifun_le {t : ℝ} (ht : 0 ≤ t) :
    infBifun noDualSolutionBifun (coord1 t) ≤ ((-Real.sqrt t : ℝ) : EReal) := by
  have hcond : (coord1 (-Real.sqrt t) 0) ^ 2 ≤ coord1 t 0 := by
    rw [coord1_apply, coord1_apply, neg_pow, Real.sq_sqrt ht]
    simp
  refine le_trans (iInf_le _ (coord1 (-Real.sqrt t))) (le_of_eq ?_)
  rw [noDualSolutionBifun_of_le hcond, coord1_apply]

/-- **§30**: `(P)` has *no* Kuhn–Tucker vector. The perturbation function `-√u` is lower
semicontinuous at `0` but has derivative `-∞` there, so no linear minorant exists; concretely,
`⟨u, u*⟩ + inf Fu` dips below `inf F0 = 0` at `u = s²` with `s = 1/(1 + |u*|)`. -/
theorem kuhnTucker_noDualSolutionBifun :
    KuhnTucker (pairing 1) noDualSolutionBifun = ∅ := by
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hv
  rw [mem_kuhnTucker_iff_forall_le] at hv
  obtain ⟨-, -, hle⟩ := hv
  have habs : (0 : ℝ) < 1 + |v 0| := by positivity
  set s : ℝ := 1 / (1 + |v 0|) with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have h := hle (coord1 (s ^ 2))
  rw [infBifun_noDualSolutionBifun_zero, pairing_one, coord1_apply] at h
  have hb := infBifun_noDualSolutionBifun_le (t := s ^ 2) (by positivity)
  rw [Real.sqrt_sq hs0.le] at hb
  have hchain : ((s ^ 2 * v 0 : ℝ) : EReal)
      + infBifun noDualSolutionBifun (coord1 (s ^ 2)) ≤ ((s ^ 2 * v 0 + -s : ℝ) : EReal) := by
    rw [EReal.coe_add]
    exact add_le_add le_rfl hb
  have hfin : (0 : EReal) ≤ ((s ^ 2 * v 0 + -s : ℝ) : EReal) := le_trans h hchain
  have hreal : (0 : ℝ) ≤ s ^ 2 * v 0 + -s := by exact_mod_cast hfin
  have hsv : s * v 0 < 1 := by
    rw [hs, div_mul_eq_mul_div, one_mul, div_lt_one habs]
    linarith [le_abs_self (v 0)]
  nlinarith [mul_lt_mul_of_pos_left hsv hs0]

/-- **§30**: the dual program `(P*)` has *no* optimal solution, although `(P)` is normal and has
one. By Theorem 30.5 the optimal solutions to `(P*)` are the Kuhn–Tucker vectors for `(P)`, and
there are none. -/
theorem argmax_dualProgram_noDualSolutionBifun :
    argmax (dualProgram noDualSolutionBifun 0) = ∅ := by
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hv
  have ht : infBifun noDualSolutionBifun 0 ≠ ⊤ := by
    rw [infBifun_noDualSolutionBifun_zero]; simp
  have hb : infBifun noDualSolutionBifun 0 ≠ ⊥ := by
    rw [infBifun_noDualSolutionBifun_zero]; simp
  have h := (theorem_30_5 convexBifun_noDualSolutionBifun normal_noDualSolutionBifun ht hb v).2 hv
  rw [kuhnTucker_noDualSolutionBifun] at h
  exact h

end Rockafellar
