import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Sequences
import NumlibSurface.ConnGouldToint.Chapter06.Section01
import Numlib.Optimization.ModelBased.RatioTest

/-! # Filter SQP methods

The filter retains an entry unless the new entry Pareto-dominates it.
This keeps every previously forbidden region forbidden. Deletion by the
printed margin test alone can admit infinitely many insertions bounded
away from feasibility, as the counterexample below shows.
-/

open Filter Topology
open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter15

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private noncomputable def filterViolationEntry (eq : ι → Bool) (c : ι → ℝ) : Option ι → ℝ
  | none => 0
  | some j => if eq j then |c j| else -c j

/-- The maximum constraint violation (15.5.3), including zero. -/
noncomputable def sqpFilterViolation [Fintype ι] (eq : ι → Bool) (c : ι → ℝ) : ℝ :=
  Finset.univ.sup' ⟨none, Finset.mem_univ _⟩ (filterViolationEntry eq c)

/-- Feasibility of a step for the linearized constraints (15.5.1a,c). -/
def sqpFilterLinearFeasible (eq : ι → Bool) (c : ι → ℝ) (a : ι → E) (s : E) : Prop :=
  ∀ j, if eq j then c j + ⟪a j, s⟫ = 0 else 0 ≤ c j + ⟪a j, s⟫

/-- The normal step is compatible when it is feasible for the linearized
constraints and leaves the margin prescribed by (15.5.5). -/
def sqpFilterCompatible (eq : ι → Bool) (c : ι → ℝ) (a : ι → E)
    (n : E) (κΔ κμ Δ μ : ℝ) : Prop :=
  sqpFilterLinearFeasible eq c a n ∧ ‖n‖ ≤ κΔ * Δ * min 1 (κμ * Δ ^ μ)

/-- The objective switching test (15.5.8). -/
def sqpFilterSwitching (κ θ predicted : ℝ) : Prop := κ * θ ^ 2 ≤ predicted

/-- The first-order tangential criticality measure at the normal-step
base. Directions are displacements from that base, so the affine
constraints are evaluated at the total step. -/
noncomputable def sqpFilterCriticality (eq : ι → Bool) (c : ι → ℝ) (a : ι → E)
    (g n : E) : ℝ :=
  -sInf ((fun d : E => ⟪g, d⟫) '' {d : E | ‖d‖ ≤ 1 ∧ sqpFilterLinearFeasible eq c a (n + d)})

/-- A feasible normal-step base has zero tangential criticality
exactly when no feasible unit displacement has negative slope. -/
theorem sqpFilterCriticality_zero_iff (eq : ι → Bool) (c : ι → ℝ) (a : ι → E)
    (g n : E) (hn : sqpFilterLinearFeasible eq c a n) :
    sqpFilterCriticality eq c a g n = 0 ↔
      ∀ d : E, ‖d‖ ≤ 1 → sqpFilterLinearFeasible eq c a (n + d) → 0 ≤ ⟪g, d⟫ := by
  let D := {d : E | ‖d‖ ≤ 1 ∧ sqpFilterLinearFeasible eq c a (n + d)}
  let V := (fun d : E => ⟪g, d⟫) '' D
  have hzero : (0 : ℝ) ∈ V := by
    refine ⟨0, ?_, by simp⟩
    simpa [D] using hn
  have hbdd : BddBelow V := by
    refine ⟨-‖g‖, ?_⟩
    rintro y ⟨d, hd, rfl⟩
    have hh := (abs_real_inner_le_norm g d).trans
      (mul_le_of_le_one_right (norm_nonneg g) hd.1)
    exact (abs_le.mp hh).1
  change -sInf V = 0 ↔ _
  rw [neg_eq_zero]
  constructor
  · intro h d hd hf
    rw [← h]
    exact csInf_le hbdd ⟨d, ⟨hd, hf⟩, rfl⟩
  · intro h
    refine le_antisymm (csInf_le hbdd hzero) (le_csInf ⟨0, hzero⟩ ?_)
    rintro _ ⟨d, hd, rfl⟩
    exact h d hd.1 hd.2

private theorem sqpFilterViolation_le [Fintype ι] {eq : ι → Bool} {c : ι → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hc : ∀ j, (if eq j then |c j| else -c j) ≤ B) :
    sqpFilterViolation eq c ≤ B := by
  apply Finset.sup'_le
  intro j _
  cases j
  · exact hB
  · exact hc _

/-- Lemma 15.5.1. A feasible linearization step cannot be shorter than
the maximum violation divided by a uniform positive gradient bound. -/
theorem lemma_15_5_1 [Fintype ι] (eq : ι → Bool) (c : ℕ → ι → ℝ) (a : ℕ → ι → E)
    (n : ℕ → E) {G : ℝ} (hG : 0 ≤ G) (ha : ∀ k j, ‖a k j‖ ≤ G)
    (hlin : ∀ᶠ k in atTop, sqpFilterLinearFeasible eq (c k) (a k) (n k)) :
    ∃ κ > 0, ∀ᶠ k in atTop, κ * sqpFilterViolation eq (c k) ≤ ‖n k‖ := by
  refine ⟨1 / (G + 1), by positivity, ?_⟩
  filter_upwards [hlin] with k hk
  have hb : sqpFilterViolation eq (c k) ≤ (G + 1) * ‖n k‖ := by
    apply sqpFilterViolation_le (by positivity)
    intro j
    have h := hk j
    have hinner : |⟪a k j, n k⟫| ≤ (G + 1) * ‖n k‖ :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right ((ha k j).trans (by linarith)) (norm_nonneg _))
    cases he : eq j <;> simp only [he, Bool.false_eq_true, ↓reduceIte] at h ⊢
    · exact (by linarith only [h] : -c k j ≤ ⟪a k j, n k⟫).trans
        ((le_abs_self _).trans hinner)
    · have hh : c k j = -⟪a k j, n k⟫ := eq_neg_of_add_eq_zero_left h
      simpa only [hh, abs_neg] using hinner
  rw [one_div_mul_eq_div]
  exact (div_le_iff₀ (by positivity : 0 < G + 1)).mpr (by simpa only [mul_comm] using hb)

/-- The strict acceptance margin (15.5.7) against one entry. -/
def sqpFilterAcceptsPair (γ : ℝ) (trial old : ℝ × ℝ) : Prop :=
  trial.1 < (1 - γ) * old.1 ∨ trial.2 < old.2 - γ * trial.1

/-- A trial pair must pass the margin test against all stored entries. -/
def sqpFilterAccepts (γ : ℝ) (F : Set (ℝ × ℝ)) (trial : ℝ × ℝ) : Prop :=
  ∀ p ∈ F, sqpFilterAcceptsPair γ trial p

/-- Insert a new pair and discard the old pairs that it Pareto-dominates. -/
def sqpFilterInsert (F : Set (ℝ × ℝ)) (p : ℝ × ℝ) : Set (ℝ × ℝ) :=
  insert p {q | q ∈ F ∧ ¬ (p.1 ≤ q.1 ∧ p.2 ≤ q.2)}

/-- The source's margin-based deletion, retained to state the counterexample. -/
def sqpFilterPrintedInsert (γ : ℝ) (F : Set (ℝ × ℝ)) (p : ℝ × ℝ) : Set (ℝ × ℝ) :=
  insert p {q | q ∈ F ∧ sqpFilterAcceptsPair γ q p}

private theorem filter_accepts_prior {γ : ℝ} (hγ : γ ≤ 1) {F : Set (ℝ × ℝ)}
    {p q : ℝ × ℝ} (h : sqpFilterAccepts γ (sqpFilterInsert F p) q) :
    sqpFilterAccepts γ F q := by
  intro z hz
  by_cases hd : p.1 ≤ z.1 ∧ p.2 ≤ z.2
  · rcases h p (Set.mem_insert _ _) with h₁ | h₂
    · exact Or.inl (h₁.trans_le (mul_le_mul_of_nonneg_left hd.1 (sub_nonneg.mpr hγ)))
    · exact Or.inr (h₂.trans_le (sub_le_sub_right hd.2 _))
  · exact h z (Set.mem_insert_of_mem _ ⟨hz, hd⟩)

/-- Lemma 15.5.2. The violation of the insertion stream tends to zero.
Pareto deletion preserves the margins against earlier insertions, so
compactness excludes an infinite stream bounded away from feasibility. -/
theorem lemma_15_5_2 (p : ℕ → ℝ × ℝ) (F : ℕ → Set (ℝ × ℝ))
    {γ V lo hi : ℝ} (hγ : 0 < γ) (hγ' : γ < 1)
    (hθ : ∀ k, (p k).1 ∈ Set.Icc 0 V) (hf : ∀ k, (p k).2 ∈ Set.Icc lo hi)
    (haccept : ∀ k, sqpFilterAccepts γ (F k) (p k))
    (hupdate : ∀ k, F (k + 1) = sqpFilterInsert (F k) (p k)) :
    Tendsto (fun k => (p k).1) atTop (𝓝 0) := by
  have hsep (i j : ℕ) (hij : i < j) : sqpFilterAcceptsPair γ (p j) (p i) := by
    have hback (k j : ℕ) (hk : k ≤ j) :
        sqpFilterAccepts γ (F j) (p j) → sqpFilterAccepts γ (F k) (p j) := by
      intro hj
      -- Keep the trial fixed while inducting over the intervening insertions.
      have aux (l : ℕ) (hl : k ≤ l) :
          sqpFilterAccepts γ (F l) (p j) → sqpFilterAccepts γ (F k) (p j) := by
        induction l, hl using Nat.le_induction with
        | base => exact id
        | succ l hl ih =>
          intro hh
          rw [hupdate] at hh
          exact ih (filter_accepts_prior hγ'.le hh)
      exact aux j hk hj
    have hh := hback (i + 1) j hij (haccept j)
    rw [hupdate] at hh
    exact hh (p i) (Set.mem_insert _ _)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  by_contra! h
  have hfreq : ∃ᶠ k in atTop, ε ≤ (p k).1 := by
    apply frequently_atTop.mpr
    intro N
    obtain ⟨k, hk, hh⟩ := h N
    exact ⟨k, hk, by simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (hθ k).1] using hh⟩
  let δ := γ * ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨i, himono, hiθ⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨w, _, q, hq, hw⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := V)).prod
    (isCompact_Icc (a := lo) (b := hi))).tendsto_subseq (x := p ∘ i) (fun k => ⟨hθ _, hf _⟩)
  obtain ⟨Nθ, hNθ⟩ := Metric.tendsto_atTop.mp (continuous_fst.tendsto w |>.comp hw) δ hδ
  obtain ⟨Nf, hNf⟩ := Metric.tendsto_atTop.mp (continuous_snd.tendsto w |>.comp hw) δ hδ
  let N := max Nθ Nf
  let k := i (q N)
  let l := i (q (N + 1))
  have hθk := hNθ N (le_max_left _ _)
  have hθl := hNθ (N + 1) ((le_max_left _ _).trans (Nat.le_succ _))
  have hfk := hNf N (le_max_right _ _)
  have hfl := hNf (N + 1) ((le_max_right _ _).trans (Nat.le_succ _))
  simp only [Function.comp_apply, Real.dist_eq] at hθk hθl hfk hfl
  have hkθ : ε ≤ (p k).1 := hiθ (q N)
  have hlθ : ε ≤ (p l).1 := hiθ (q (N + 1))
  have hmargin₁ := mul_le_mul_of_nonneg_left hkθ hγ.le
  have hmargin₂ := mul_le_mul_of_nonneg_left hlθ hγ.le
  dsimp only [δ] at hθk hθl hfk hfl
  rcases hsep k l (himono (hq (Nat.lt_succ_self _))) with hs | hs
  · linarith only [(abs_lt.mp hθk).2, (abs_lt.mp hθl).1, hs, hmargin₁, mul_pos hγ hε]
  · linarith only [(abs_lt.mp hfk).2, (abs_lt.mp hfl).1, hs, hmargin₂, mul_pos hγ hε]

/-- The printed deletion rule can forget an earlier margin. This
bounded insertion stream alternates between two positive violation
levels, and every insertion removes the previous entry. -/
theorem sqpFilter_margin_deletion_counterexample :
    ∃ (p : ℕ → ℝ × ℝ) (F : ℕ → Set (ℝ × ℝ)),
      F 0 = ∅ ∧
      (∀ k, (p k).1 ∈ Set.Icc (1 : ℝ) 4 ∧ (p k).2 ∈ Set.Icc (0 : ℝ) 2) ∧
      (∀ k, sqpFilterAccepts (1 / 2) (F k) (p k)) ∧
      (∀ k, F (k + 1) = sqpFilterPrintedInsert (1 / 2) (F k) (p k)) := by
  let r (j : ℕ) := 1 / ((j : ℝ) + 1)
  have hr (j : ℕ) : 0 < r j := by dsimp [r]; positivity
  have hr₁ (j : ℕ) : r j ≤ 1 := by
    dsimp [r]
    apply (div_le_iff₀ (by positivity : 0 < (j : ℝ) + 1)).mpr
    linarith only [Nat.cast_nonneg (α := ℝ) j]
  have hdec (j : ℕ) : r (j + 1) < r j := by
    apply one_div_lt_one_div_of_lt (by positivity)
    push_cast
    linarith
  let H (j : ℕ) : ℝ × ℝ := (2 + 2 * r j, 0)
  let L (j : ℕ) : ℝ × ℝ := (1 + r (j + 1), 1 + r j)
  let p (k : ℕ) := if k % 2 = 0 then H (k / 2) else L (k / 2)
  have he (j : ℕ) : p (2 * j) = H j := by
    have hm : (2 * j) % 2 = 0 := by omega
    have hd : (2 * j) / 2 = j := by omega
    simp only [p, hm, ↓reduceIte, hd]
  have ho (j : ℕ) : p (2 * j + 1) = L j := by
    have hm : (2 * j + 1) % 2 ≠ 0 := by omega
    have hd : (2 * j + 1) / 2 = j := by omega
    simp only [p, ite_eq_right hm, hd]
  have hp (k : ℕ) : ∃ j, k = 2 * j ∨ k = 2 * j + 1 :=
    ⟨k / 2, by omega⟩
  have hpair (k : ℕ) :
      sqpFilterAcceptsPair (1 / 2) (p (k + 1)) (p k) ∧
        ¬ sqpFilterAcceptsPair (1 / 2) (p k) (p (k + 1)) := by
    obtain ⟨j, rfl | rfl⟩ := hp k
    · rw [he, ho]
      simp only [sqpFilterAcceptsPair, H, L, not_or, not_lt]
      refine ⟨Or.inl ?_, ?_, ?_⟩ <;> linarith only [hdec j, hr j, hr (j + 1)]
    · rw [show 2 * j + 1 + 1 = 2 * (j + 1) by omega, he, ho]
      simp only [sqpFilterAcceptsPair, H, L, not_or, not_lt]
      refine ⟨Or.inr ?_, ?_, ?_⟩ <;> linarith only [hdec j, hr j, hr (j + 1)]
  let F (k : ℕ) : Set (ℝ × ℝ) := if k = 0 then ∅ else {p (k - 1)}
  refine ⟨p, F, by simp [F], ?_, ?_, ?_⟩
  · intro k
    obtain ⟨j, rfl | rfl⟩ := hp k
    · rw [he]
      exact ⟨⟨by dsimp [H]; linarith only [hr j], by dsimp [H]; linarith only [hr₁ j]⟩,
        by simp [H]⟩
    · rw [ho]
      exact ⟨⟨by dsimp [L]; linarith only [hr (j + 1)],
        by dsimp [L]; linarith only [hr₁ (j + 1)]⟩,
        ⟨by dsimp [L]; linarith only [hr j], by dsimp [L]; linarith only [hr₁ j]⟩⟩
  · intro k q hq
    cases k with
    | zero => simp [F] at hq
    | succ k =>
      simp only [F, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
        Set.mem_singleton_iff] at hq
      rw [hq]
      exact (hpair k).1
  · intro k
    cases k with
    | zero => simp [F, sqpFilterPrintedInsert]
    | succ k =>
      simp only [F, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, sqpFilterPrintedInsert]
      have hnone : {q | q ∈ ({p k} : Set (ℝ × ℝ)) ∧
          sqpFilterAcceptsPair (1 / 2) q (p (k + 1))} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro q hq
        have heq := Set.mem_singleton_iff.mp hq.1
        exact (hpair k).2 (heq ▸ hq.2)
      rw [hnone]
      ext q
      simp

/-- Lemma 15.5.3. Compatibility bounds the current violation, and
linearized feasibility plus a Taylor bound on the full trial segment
bounds the trial violation. -/
theorem lemma_15_5_3 [Fintype ι] (eq : ι → Bool) (c cTrial : ι → ℝ)
    (a : ι → E) (n s : E) {κ K L Δ μ : ℝ}
    (hκ : 0 < κ) (hL : 0 ≤ L) (hΔ : 0 ≤ Δ)
    (hn : κ * sqpFilterViolation eq c ≤ ‖n‖)
    (hcompat : ‖n‖ ≤ K * Δ ^ (1 + μ))
    (hs : ‖s‖ ≤ Δ) (hlinear : sqpFilterLinearFeasible eq c a s)
    (hTaylor : ∀ j, |cTrial j - (c j + ⟪a j, s⟫)| ≤ L * ‖s‖ ^ 2) :
    sqpFilterViolation eq c ≤ max (K / κ) L * Δ ^ (1 + μ) ∧
      sqpFilterViolation eq cTrial ≤ max (K / κ) L * Δ ^ 2 := by
  constructor
  · have h := hn.trans hcompat
    have hdiv : sqpFilterViolation eq c ≤ (K / κ) * Δ ^ (1 + μ) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hκ).mpr
      simpa only [mul_comm κ] using h
    exact hdiv.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hΔ _))
  · have hB : sqpFilterViolation eq cTrial ≤ L * Δ ^ 2 := by
      apply sqpFilterViolation_le (by positivity)
      intro j
      have hj := hlinear j
      have he := (hTaylor j).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hs 2) hL)
      cases heq : eq j <;> simp only [heq, Bool.false_eq_true, ↓reduceIte] at hj ⊢
      · linarith only [(abs_le.mp he).1, hj]
      · simpa only [hj, sub_zero] using he
    exact hB.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))

/-- The model decrease radius in (15.5.19). Here `K` is the product
of the two normal-step compatibility constants. -/
noncomputable def filterModelRadius (G B K κ ε μ : ℝ) : ℝ :=
  min (ε / (B + 1))
    (min ((2 * G / ((B + 1) * K)) ^ (1 / (1 + μ)))
      ((κ * ε / (4 * G * K)) ^ (1 / μ)))

/-- A positive upper bound for the gradient gives the printed threshold
and implies the division-free normal-cost condition of Lemma 15.5.4. -/
theorem filterModelRadius_bounds {G B K κ ε μ Δ χ : ℝ}
    (hG : 0 < G) (hB : 0 ≤ B) (hK : 0 < K) (hκ : 0 < κ) (hε : 0 < ε) (hμ : 0 < μ)
    (hΔ : 0 < Δ) (hχ : ε ≤ χ) (hsmall : Δ ≤ filterModelRadius G B K κ ε μ) :
    Δ ≤ χ / (B + 1) ∧
      (G + (1 / 2) * B * (K * Δ ^ (1 + μ))) * K * Δ ^ μ ≤ κ * ε / 2 := by
  have hB₁ : 0 < B + 1 := by positivity
  unfold filterModelRadius at hsmall
  obtain ⟨h₁, h₂, h₃⟩ := (le_min_iff.mp hsmall).imp_right le_min_iff.mp
  have hp₂ : Δ ^ (1 + μ) ≤ 2 * G / ((B + 1) * K) :=
    (Real.le_rpow_inv_iff_of_pos hΔ.le (by positivity) (by positivity)).mp
      (by simpa only [one_div] using h₂)
  have hp₃ : Δ ^ μ ≤ κ * ε / (4 * G * K) :=
    (Real.le_rpow_inv_iff_of_pos hΔ.le (by positivity) hμ).mp
      (by simpa only [one_div] using h₃)
  have hq₂ := (le_div_iff₀ (mul_pos hB₁ hK)).mp hp₂
  have hq₃ := (le_div_iff₀ (by positivity : 0 < 4 * G * K)).mp hp₃
  have hnorm : 0 ≤ K * Δ ^ (1 + μ) := by positivity
  have hcost : G + (1 / 2) * B * (K * Δ ^ (1 + μ)) ≤ 2 * G := by
    nlinarith only [hq₂, hnorm]
  refine ⟨h₁.trans (div_le_div_of_nonneg_right hχ hB₁.le), ?_⟩
  calc
    _ ≤ (2 * G) * K * Δ ^ μ := by gcongr
    _ ≤ _ := by nlinarith only [hq₃]

/-- The radius ensuring a very successful ratio in (15.5.21). -/
noncomputable def filterRatioRadius (δm η κ ε C : ℝ) : ℝ :=
  min δm ((1 - η) * κ * ε / (2 * C))

/-- The ratio threshold gives the error bound required by Lemma 15.5.5. -/
theorem filterRatioRadius_bound {δm η κ ε C Δ : ℝ} (hC : 0 < C)
    (hΔ : Δ ≤ filterRatioRadius δm η κ ε C) :
    Δ ≤ δm ∧ C * Δ ≤ (1 - η) * (κ * ε / 2) := by
  obtain ⟨h₁, h₂⟩ := le_min_iff.mp hΔ
  exact ⟨h₁, by nlinarith only [(le_div_iff₀ (by positivity : 0 < 2 * C)).mp h₂]⟩

/-- The feasibility-switch radius in (15.5.22). -/
noncomputable def filterFeasibilityRadius (δm κ ε κθ K μ : ℝ) : ℝ :=
  min δm ((κ * ε / (2 * κθ * K ^ 2)) ^ (1 / (1 + 2 * μ)))

/-- The feasibility-switch threshold yields the bound in Lemma 15.5.6. -/
theorem filterFeasibilityRadius_bound {δm κ ε κθ K μ Δ : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hκθ : 0 < κθ) (hK : 0 < K) (hμ : 0 ≤ μ)
    (hΔ : 0 ≤ Δ) (hsmall : Δ ≤ filterFeasibilityRadius δm κ ε κθ K μ) :
    Δ ≤ δm ∧ κθ * K ^ 2 * Δ ^ (1 + 2 * μ) ≤ κ * ε / 2 := by
  obtain ⟨h₁, h₂⟩ := le_min_iff.mp hsmall
  have hp : Δ ^ (1 + 2 * μ) ≤ κ * ε / (2 * κθ * K ^ 2) :=
    (Real.le_rpow_inv_iff_of_pos hΔ (by positivity) (by positivity)).mp
      (by simpa only [one_div] using h₂)
  exact ⟨h₁, by nlinarith only [(le_div_iff₀ (by positivity : 0 < 2 * κθ * K ^ 2)).mp hp]⟩

/-- The objective-margin radius in (15.5.23). -/
noncomputable def filterObjectiveMarginRadius (δρ η κ ε M γ : ℝ) : ℝ :=
  min (η * κ * ε / (2 * M * γ)) δρ

/-- Strict inequality at the radius threshold gives the strict filter
margin required by the objective branch. -/
theorem filterObjectiveMarginRadius_bound {δρ η κ ε M γ Δ : ℝ}
    (hM : 0 < M) (hγ : 0 < γ) (hΔ : Δ < filterObjectiveMarginRadius δρ η κ ε M γ) :
    Δ < δρ ∧ γ * M * Δ < η * (κ * ε / 2) := by
  obtain ⟨h₁, h₂⟩ := lt_min_iff.mp hΔ
  exact ⟨h₂, by nlinarith only [(lt_div_iff₀ (by positivity : 0 < 2 * M * γ)).mp h₁]⟩

/-- The positive tangential decrease floor (15.5.31). -/
noncomputable def filterTangentialDecreaseFloor (κ ε r B : ℝ) : ℝ :=
  κ * ε * min (ε / B) r

/-- Radius and criticality lower bounds give the positive floor in (15.5.31). -/
theorem filterTangentialDecreaseFloor_le {κ ε r B χ Δ : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hr : 0 < r) (hB : 0 < B)
    (hχ : ε ≤ χ) (hΔ : r ≤ Δ) :
    0 < filterTangentialDecreaseFloor κ ε r B ∧
      filterTangentialDecreaseFloor κ ε r B ≤ κ * χ * min (χ / B) Δ := by
  unfold filterTangentialDecreaseFloor
  constructor
  · positivity
  · have hmin := min_le_min (div_le_div_of_nonneg_right hχ hB.le) hΔ
    exact mul_le_mul (mul_le_mul_of_nonneg_left hχ hκ.le) hmin
      (le_min (div_pos hε hB).le hr.le) (mul_nonneg hκ.le (hε.le.trans hχ))

/-- The predecessor radius in (15.5.37), with the minimum violation
of the filter supplied as a parameter. -/
noncomputable def filterPredecessorRadius (δρ γ θF M Δ₀ : ℝ) : ℝ :=
  min δρ (min (Real.sqrt ((1 - γ) * θF / M)) Δ₀)

/-- The lower radius-update factor transfers (15.5.37) to the preceding
iteration, as in (15.5.38). -/
theorem filterPredecessorRadius_le {δρ γ θF M Δ₀ γ₀ Δprev Δ : ℝ}
    (hγ₀ : 0 < γ₀) (hupdate : γ₀ * Δprev ≤ Δ)
    (hΔ : Δ ≤ γ₀ * filterPredecessorRadius δρ γ θF M Δ₀) :
    Δprev ≤ filterPredecessorRadius δρ γ θF M Δ₀ :=
  le_of_mul_le_mul_left (hupdate.trans hΔ) hγ₀

/-- Lemma 15.5.4. The normal model cost is bounded by the gradient
and Hessian bounds times the compatibility step length. The smallness
test is written without dividing by the gradient bound, which can be
zero. -/
theorem lemma_15_5_4 (f₀ : ℝ) (g n s : E) (H : E →L[ℝ] E)
    {G B K κ ε Δ μ χ : ℝ}
    (hG : 0 ≤ G) (hB : 0 ≤ B) (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hΔ : 0 < Δ) (hχ : ε ≤ χ) (hcurv : Δ ≤ χ / (B + 1))
    (hg : ‖g‖ ≤ G) (hH : ‖H‖ ≤ B)
    (hn : ‖n‖ ≤ K * Δ ^ (1 + μ))
    (hsmall : (G + (1 / 2) * B * (K * Δ ^ (1 + μ))) * K * Δ ^ μ ≤ κ * ε / 2)
    (hTang : κ * χ * min (χ / (B + 1)) Δ ≤
      Chapter06.quadraticModel f₀ g H.toLinearMap n - Chapter06.quadraticModel f₀ g H.toLinearMap s) :
    κ * ε / 2 * Δ ≤ f₀ - Chapter06.quadraticModel f₀ g H.toLinearMap s := by
  let a := K * Δ ^ (1 + μ)
  have ha : 0 ≤ a := mul_nonneg hK (Real.rpow_nonneg hΔ.le _)
  rw [min_eq_right hcurv] at hTang
  have hT := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hχ hκ) hΔ.le).trans hTang
  have hlin : ⟪g, n⟫ ≤ G * a :=
    (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul hg hn (norm_nonneg _) hG))
  have hcurv' : ⟪n, H n⟫ ≤ B * a ^ 2 := calc
    _ ≤ |⟪n, H n⟫| := le_abs_self _
    _ ≤ ‖n‖ * ‖H n‖ := abs_real_inner_le_norm _ _
    _ ≤ a * (B * a) :=
      mul_le_mul hn ((H.le_opNorm n).trans (mul_le_mul hH hn (norm_nonneg _) hB))
        (norm_nonneg _) ha
    _ = _ := by ring
  have hcost : G * a + (1 / 2) * (B * a ^ 2) ≤ κ * ε / 2 * Δ := by
    have hpow : a = K * Δ ^ μ * Δ := by
      dsimp [a]
      rw [Real.rpow_add hΔ, Real.rpow_one]
      ring
    calc
      _ = ((G + (1 / 2) * B * a) * K * Δ ^ μ) * Δ := by
        calc
          _ = (G + (1 / 2) * B * a) * a := by ring
          _ = (G + (1 / 2) * B * a) * (K * Δ ^ μ * Δ) :=
            congrArg (fun z => (G + (1 / 2) * B * a) * z) hpow
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hΔ.le
  simp only [Chapter06.quadraticModel, ContinuousLinearMap.coe_coe] at hT ⊢
  linarith only [hT, hlin, hcurv', hcost]

omit [InnerProductSpace ℝ E] in
/-- Lemma 15.5.5. A quadratic model error is small relative to the
linear predicted reduction at sufficiently small radius. -/
theorem lemma_15_5_5 (f : E → ℝ) (x s : E) {η a Δ C d : ℝ}
    (ha : 0 < a) (hΔ : 0 < Δ) (hpred : a * Δ ≤ d)
    (hη : η ≤ 1) (hsmall : C * Δ ≤ (1 - η) * a)
    (herr : |f (x + s) - (f x - d)| ≤ C * Δ ^ 2) :
    η ≤ Optimization.reductionRatio f x s d := by
  have hpos : 0 < d := (mul_pos ha hΔ).trans_le hpred
  have h₁ := mul_le_mul_of_nonneg_right hsmall hΔ.le
  have h₂ := mul_le_mul_of_nonneg_left hpred (sub_nonneg.mpr hη)
  have h := Optimization.le_reductionRatio_of_abs_sub_le hpos
    (herr.trans (by nlinarith only [h₁, h₂]))
  linarith only [h]

/-- Lemma 15.5.6. Compatibility makes the squared violation of higher
order than the linear model decrease. -/
theorem lemma_15_5_6 {θ Δ μ K κ a d : ℝ} (hθ : 0 ≤ θ) (hΔ : 0 < Δ) (hκ : 0 ≤ κ)
    (hcompat : θ ≤ K * Δ ^ (1 + μ))
    (hsmall : κ * K ^ 2 * Δ ^ (1 + 2 * μ) ≤ a) (hpred : a * Δ ≤ d) :
    κ * θ ^ 2 ≤ d := by
  have hpow : (Δ ^ (1 + μ)) ^ (2 : ℕ) = Δ ^ (1 + 2 * μ) * Δ := by
    calc
      _ = Δ ^ ((1 + μ) * (2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hΔ.le]
        norm_num
      _ = Δ ^ (1 + 2 * μ) * Δ ^ (1 : ℝ) := by
        rw [← Real.rpow_add hΔ]
        congr 1
        ring
      _ = _ := by rw [Real.rpow_one]
  calc
    _ ≤ κ * (K * Δ ^ (1 + μ)) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hθ hcompat 2) hκ
    _ = (κ * K ^ 2 * Δ ^ (1 + 2 * μ)) * Δ := by rw [mul_pow, hpow]; ring
    _ ≤ a * Δ := mul_le_mul_of_nonneg_right hsmall hΔ.le
    _ ≤ _ := hpred

omit [InnerProductSpace ℝ E] in
/-- Lemma 15.5.7 with a strict radius threshold. The strict inequality
is needed for the objective branch of the filter's acceptance rule. -/
theorem lemma_15_5_7 (f : E → ℝ) (x s : E) {θtrial γ η a Δ M d : ℝ}
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ha : 0 < a) (hΔ : 0 < Δ)
    (hpred : a * Δ ≤ d) (hratio : η ≤ Optimization.reductionRatio f x s d)
    (htrial : θtrial ≤ M * Δ ^ 2) (hsmall : γ * M * Δ < η * a) :
    f (x + s) < f x - γ * θtrial := by
  have hd : 0 < d := (mul_pos ha hΔ).trans_le hpred
  have hactual := (le_div_iff₀ hd).mp hratio
  change η * d ≤ f x - f (x + s) at hactual
  have h₁ := mul_le_mul_of_nonneg_left htrial hγ
  have h₂ := mul_lt_mul_of_pos_right hsmall hΔ
  have h₃ := mul_le_mul_of_nonneg_left hpred hη
  nlinarith only [h₁, h₂, h₃, hactual]

/-- A trial that strictly improves both margin tests against the
current iterate remains acceptable against the current filter. -/
theorem sqpFilterAccepts_of_improvement {γ : ℝ} (hγ : 0 ≤ γ)
    {F : Set (ℝ × ℝ)} {p q : ℝ × ℝ} (hp : 0 ≤ p.1)
    (h : sqpFilterAccepts γ F p)
    (hθ : q.1 < (1 - γ) * p.1) (hf : q.2 < p.2 - γ * q.1) :
    sqpFilterAccepts γ (insert p F) q := by
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | hz
  · exact Or.inr hf
  · rcases h z hz with h₁ | h₂
    · exact Or.inl (hθ.trans (lt_of_le_of_lt (by nlinarith only [mul_nonneg hγ hp]) h₁))
    · exact Or.inr (hf.trans (by nlinarith only [h₂, mul_nonneg hγ hp]))

/-- Lemma 15.5.8. A sufficiently small current radius is compatible
after either a successful predecessor or a rejected predecessor whose
trial passed the objective margin and model-ratio tests. The latter
case uses the current iterate's filter acceptance to quantify rejection. -/
theorem lemma_15_5_8 {γ γ₀ K U M Δprev Δ μ θ θprev θtrial fprev ftrial normal : ℝ}
    (hγ : 0 ≤ γ) (hγ' : γ < 1) (hγ₀ : 0 < γ₀) (hΔ : 0 < Δ)
    (hΔprev : 0 ≤ Δprev) (hU : 0 ≤ U) (hM : 0 ≤ M)
    (hθprev : 0 ≤ θprev) (hupdate : γ₀ * Δprev ≤ Δ)
    (htrial : θtrial ≤ M * Δprev ^ 2) (hn : normal ≤ U * θ)
    (hthreshold : U * M * Δ ^ (1 - μ) ≤ (1 - γ) * γ₀ ^ 2 * K)
    {F : Set (ℝ × ℝ)} (hcurrent : sqpFilterAccepts γ F (θprev, fprev))
    (hobj : ftrial < fprev - γ * θtrial)
    (hbranch : θ = θtrial ∨
      (θ = θprev ∧ ¬ sqpFilterAccepts γ (insert (θprev, fprev) F) (θtrial, ftrial))) :
    normal ≤ K * Δ ^ (1 + μ) := by
  have hθ : (1 - γ) * θ ≤ M * Δprev ^ 2 := by
    rcases hbranch with h | ⟨h, hfail⟩
    · have hT : 0 ≤ M * Δprev ^ 2 := mul_nonneg hM (sq_nonneg _)
      rw [h]
      exact (mul_le_mul_of_nonneg_left htrial (sub_nonneg.mpr hγ'.le)).trans
        (by nlinarith only [mul_nonneg hγ hT])
    · rw [h]
      have hh : (1 - γ) * θprev ≤ θtrial := by
        by_contra! hh
        exact hfail (sqpFilterAccepts_of_improvement hγ hθprev hcurrent hh hobj)
      exact hh.trans htrial
  have hsq : γ₀ ^ 2 * Δprev ^ 2 ≤ Δ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (mul_nonneg hγ₀.le hΔprev) hupdate 2
  have hc : 0 < (1 - γ) * γ₀ ^ 2 := mul_pos (sub_pos.mpr hγ') (sq_pos_of_pos hγ₀)
  have hpow : Δ ^ (1 - μ) * Δ ^ (1 + μ) = Δ ^ (2 : ℕ) := by
    rw [← Real.rpow_add hΔ, ← Real.rpow_natCast]
    congr 1
    norm_num
  apply le_of_mul_le_mul_left _ hc
  calc
    _ ≤ ((1 - γ) * θ) * (γ₀ ^ 2 * U) := by
      have hh := mul_le_mul_of_nonneg_left hn hc.le
      linarith only [hh, show ((1 - γ) * γ₀ ^ 2) * (U * θ) =
        ((1 - γ) * θ) * (γ₀ ^ 2 * U) by ring]
    _ ≤ (M * Δprev ^ 2) * (γ₀ ^ 2 * U) :=
      mul_le_mul_of_nonneg_right hθ (mul_nonneg (sq_nonneg _) hU)
    _ = (U * M) * (γ₀ ^ 2 * Δprev ^ 2) := by ring
    _ ≤ (U * M) * Δ ^ 2 := mul_le_mul_of_nonneg_left hsq (mul_nonneg hU hM)
    _ = (U * M * Δ ^ (1 - μ)) * Δ ^ (1 + μ) := by rw [← hpow]; ring
    _ ≤ ((1 - γ) * γ₀ ^ 2 * K) * Δ ^ (1 + μ) :=
      mul_le_mul_of_nonneg_right hthreshold (Real.rpow_nonneg hΔ.le _)
    _ = _ := by ring

/-- Lemma 15.5.9. On an infinite insertion stream, small-radius
nonrestoration and switching exclude large criticality at small
radii. At larger radii the tangential decrease stays positive, whereas
the normal model loss and the switching threshold both vanish. -/
theorem lemma_15_5_9 (p : ℕ → ℝ × ℝ) (F : ℕ → Set (ℝ × ℝ))
    (χ Δ normalCost d : ℕ → ℝ) (R : Set ℕ)
    {γ V lo hi K U μ κ β κθ : ℝ} (hγ : 0 < γ) (hγ' : γ < 1)
    (hθ : ∀ k, (p k).1 ∈ Set.Icc 0 V) (hf : ∀ k, (p k).2 ∈ Set.Icc lo hi)
    (haccept : ∀ k, sqpFilterAccepts γ (F k) (p k))
    (hupdate : ∀ k, F (k + 1) = sqpFilterInsert (F k) (p k))
    (hχ : ∀ k, 0 ≤ χ k) (hμ : 0 ≤ μ)
    (hK : 0 < K) (hκ : 0 < κ) (hβ : 0 < β)
    (hcost : Tendsto normalCost atTop (𝓝 0))
    (hrestore : ∀ k ∈ R, K * min (Δ k) (Δ k ^ (1 + μ)) < U * (p k).1)
    (hswitch : ∀ k ∉ R, d k < κθ * (p k).1 ^ 2)
    (hTang : ∀ k ∉ R, κ * χ k * min (χ k / β) (Δ k) ≤ d k + normalCost k)
    (hsmall : ∀ ε > 0, ∃ r > 0, ∀ᶠ k in atTop, ε ≤ χ k → Δ k ≤ r →
      k ∉ R ∧ κθ * (p k).1 ^ 2 ≤ d k) :
    Tendsto (fun k => (p k).1) atTop (𝓝 0) ∧ Tendsto χ atTop (𝓝 0) := by
  have hθlim := lemma_15_5_2 p F hγ hγ' hθ hf haccept hupdate
  refine ⟨hθlim, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
  obtain ⟨r, hr, hsmall'⟩ := hsmall ε hε
  let a := κ * ε * min (ε / β) r
  have ha : 0 < a := mul_pos (mul_pos hκ hε) (lt_min (div_pos hε hβ) hr)
  let b := K * min r (r ^ (1 + μ))
  have hb : 0 < b := mul_pos hK (lt_min hr (Real.rpow_pos_of_pos hr _))
  have ht₀ : Tendsto (fun k => U * (p k).1) atTop (𝓝 0) := by
    simpa only [mul_zero] using hθlim.const_mul U
  have ht₁ : Tendsto (fun k => κθ * (p k).1 ^ 2 + normalCost k) atTop (𝓝 0) := by
    simpa using ((hθlim.pow 2).const_mul κθ).add hcost
  apply eventually_atTop.mp
  filter_upwards [hsmall', ht₀.eventually_lt_const hb, ht₁.eventually_lt_const ha] with k hs hb' ha'
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hχ k)]
  by_contra! hlarge
  have hrΔ : r < Δ k := by
    by_contra! h
    obtain ⟨hk, hh⟩ := hs hlarge h
    exact (not_le_of_gt (hswitch k hk)) hh
  have hn : k ∉ R := by
    intro hk
    have h := mul_le_mul_of_nonneg_left (min_le_min hrΔ.le
      (Real.rpow_le_rpow hr.le hrΔ.le (by linarith only [hμ] : 0 ≤ 1 + μ))) hK.le
    exact (not_lt_of_ge h) ((hrestore k hk).trans hb')
  have hmin := min_le_min (div_le_div_of_nonneg_right hlarge hβ.le) hrΔ.le
  have hpred : a ≤ d k + normalCost k :=
    (mul_le_mul (mul_le_mul_of_nonneg_left hlarge hκ.le) hmin
      (le_min (div_nonneg hε.le hβ.le) hr.le)
      (mul_nonneg hκ.le (hχ k))).trans (hTang k hn)
  linarith only [hpred, hswitch k hn, ha']

/-- Lemma 15.5.10. Once the filter is frozen and the switching test
holds, the objective decrease drives the violation to zero at each
success. The iterate is unchanged up to the next success. -/
theorem lemma_15_5_10 (θ f n : ℕ → ℝ) (S : Set ℕ) {η κ U l : ℝ}
    (hη : 0 < η) (hκ : 0 < κ) (hl : 0 < l)
    (hθ : ∀ k, 0 ≤ θ k)
    (hmono : Antitone f) (hbelow : BddBelow (Set.range f))
    (hS : ∃ᶠ k in atTop, k ∈ S)
    (hdrop : ∀ᶠ k in atTop, k ∈ S → η * κ * θ k ^ 2 ≤ f k - f (k + 1))
    (hstay : ∀ᶠ k in atTop, k ∉ S → θ (k + 1) = θ k)
    (hnormal : Tendsto θ atTop (𝓝 0) → ∀ᶠ k in atTop, l * θ k ≤ n k ∧ n k ≤ U * θ k) :
    Tendsto θ atTop (𝓝 0) ∧ (∀ᶠ k in atTop, l * θ k ≤ n k ∧ n k ≤ U * θ k) ∧
      Tendsto n atTop (𝓝 0) := by
  classical
  have hlim := tendsto_atTop_ciInf hmono hbelow
  have hdiff : Tendsto (fun k => f k - f (k + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using hlim.sub (hlim.comp (tendsto_add_atTop_nat 1))
  have ht : Tendsto θ atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((hdrop.and hstay).and (hdiff.eventually_lt_const (mul_pos (mul_pos hη hκ) (sq_pos_of_pos hε))))
    refine ⟨N, fun k hk => ?_⟩
    have hfind : ∃ j, k ≤ j ∧ j ∈ S := frequently_atTop.mp hS k
    let j := Nat.find hfind
    have hj : k ≤ j ∧ j ∈ S := Nat.find_spec hfind
    have hjN := hN j (hk.trans hj.1)
    have heq (i : ℕ) (hi : k ≤ i) : i ≤ j → θ i = θ k := by
      induction i, hi using Nat.le_induction with
      | base => intro; rfl
      | succ i hi ih =>
        intro h
        have hij := Nat.lt_of_succ_le h
        have hin : i ∉ S := fun hs => Nat.find_min hfind hij ⟨hi, hs⟩
        exact ((hN i (hk.trans hi)).1.2 hin).trans (ih hij.le)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hθ k), ← heq j hj.1 le_rfl]
    by_contra! h
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le h 2) (mul_nonneg hη.le hκ.le)
    exact (not_le_of_gt hjN.2) (hh.trans (hjN.1.1 hj.2))
  refine ⟨ht, hnormal ht, ?_⟩
  have hlim' : Tendsto (fun k => U * θ k) atTop (𝓝 0) := by simpa only [mul_zero] using ht.const_mul U
  exact squeeze_zero' ((hnormal ht).mono (fun k hk => (mul_nonneg hl.le (hθ k)).trans hk.1))
    ((hnormal ht).mono (fun _ hk => hk.2)) hlim'

/-- Lemma 15.5.11. A positive violation floor for the finite filter,
the strict current-iterate objective margin, and the very-successful
ratio guarantee prevent radius shrinkage at sufficiently small radii. -/
theorem lemma_15_5_11 (p q : ℕ → ℝ × ℝ) (F : Set (ℝ × ℝ)) (Δ ρ : ℕ → ℝ)
    {γ γ₀ θF M r η₂ : ℝ} (hγ : γ < 1) (hγ₀ : 0 < γ₀) (hθF : 0 < θF)
    (hM : 0 ≤ M) (hr : 0 < r) (hΔ : ∀ k, 0 < Δ k)
    (hF : ∀ z ∈ F, θF ≤ z.1)
    (hnext : ∀ k, γ₀ * Δ k ≤ Δ (k + 1))
    (htrial : ∀ᶠ k in atTop, Δ k ≤ r →
      (q k).1 ≤ M * Δ k ^ 2 ∧ (q k).2 < (p k).2 - γ * (q k).1 ∧ η₂ ≤ ρ k)
    (hvery : ∀ᶠ k in atTop, sqpFilterAccepts γ (insert (p k) F) (q k) →
      η₂ ≤ ρ k → Δ k ≤ Δ (k + 1)) :
    ∃ b > 0, ∀ᶠ k in atTop, b ≤ Δ k := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (htrial.and hvery)
  let t := min r (min 1 ((1 - γ) * θF / (2 * (M + 1))))
  have ht : 0 < t := lt_min hr (lt_min zero_lt_one
    (div_pos (mul_pos (sub_pos.mpr hγ) hθF) (by positivity)))
  let b := min (Δ N) (γ₀ * t)
  have hb : 0 < b := lt_min (hΔ N) (mul_pos hγ₀ ht)
  refine ⟨b, hb, eventually_atTop.mpr ⟨N, fun k hk => ?_⟩⟩
  induction k, hk using Nat.le_induction with
  | base => exact min_le_left _ _
  | succ k hk ih =>
    by_cases hsmall : Δ k ≤ t
    · obtain ⟨htθ, htf, hρ⟩ := (hN k hk).1 (hsmall.trans (min_le_left _ _))
      have hΔ₁ : Δ k ≤ 1 := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hΔ₂ := (le_div_iff₀ (by positivity : 0 < 2 * (M + 1))).mp
        (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
      have hθ : (q k).1 < (1 - γ) * θF := by
        have hs : Δ k ^ 2 ≤ Δ k := by
          nlinarith only [mul_nonneg (hΔ k).le (sub_nonneg.mpr hΔ₁)]
        have h := mul_le_mul_of_nonneg_left hs hM
        nlinarith only [htθ, h, hΔ₂, hΔ k, mul_nonneg hM (hΔ k).le]
      apply ih.trans ((hN k hk).2 ?_ hρ)
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact Or.inr htf
      · exact Or.inl (hθ.trans_le (mul_le_mul_of_nonneg_left (hF z hz) (sub_nonneg.mpr hγ.le)))
    · exact (min_le_right _ _).trans
        ((mul_le_mul_of_nonneg_left (le_of_not_ge hsmall) hγ₀.le).trans (hnext k))

/-- Lemma 15.5.12. If criticality were uniformly positive on the tail,
the radius floor would force a positive tangential decrease on every
success, contradicting convergence of the objective and vanishing
normal model cost. -/
theorem lemma_15_5_12 (χ f Δ d normalCost : ℕ → ℝ) (S : Set ℕ)
    {κ β η : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hη : 0 < η)
    (hχ : ∀ k, 0 ≤ χ k)
    (hmono : Antitone f) (hbelow : BddBelow (Set.range f))
    (hS : ∃ᶠ k in atTop, k ∈ S)
    (hcost : Tendsto normalCost atTop (𝓝 0))
    (hTang : ∀ᶠ k in atTop, κ * χ k * min (χ k / β) (Δ k) ≤ d k + normalCost k)
    (hdrop : ∀ᶠ k in atTop, k ∈ S → η * d k ≤ f k - f (k + 1))
    (hfloor : ∀ ε > 0, (∀ᶠ k in atTop, ε ≤ χ k) → ∃ b > 0, ∀ᶠ k in atTop, b ≤ Δ k) :
    liminf χ atTop = 0 ∧ (∀ ε > 0, ∃ᶠ k in atTop, χ k < ε) := by
  have hlim := tendsto_atTop_ciInf hmono hbelow
  have hdiff : Tendsto (fun k => (f k - f (k + 1)) / η + normalCost k) atTop (𝓝 0) := by
    have hh : Tendsto (fun k => f k - f (k + 1)) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, sub_self] using hlim.sub (hlim.comp (tendsto_add_atTop_nat 1))
    simpa only [zero_div, zero_add] using (hh.div_const η).add hcost
  have hfreq (ε : ℝ) (hε : 0 < ε) : ∃ᶠ k in atTop, χ k < ε := by
    by_contra! h
    have he : ∀ᶠ k in atTop, ε ≤ χ k := by simpa only [not_lt] using h
    obtain ⟨b, hb, hB⟩ := hfloor ε hε he
    let a := κ * ε * min (ε / β) b
    have ha : 0 < a := mul_pos (mul_pos hκ hε) (lt_min (div_pos hε hβ) hb)
    have hbad : ∀ᶠ k in atTop, k ∉ S := by
      filter_upwards [he, hB, hTang, hdrop, hdiff.eventually_lt_const ha] with k hk hbk hTk hdk hdiffk
      intro hSk
      have hd := (le_div_iff₀ hη).mpr (by simpa only [mul_comm η] using hdk hSk)
      have hmin := min_le_min (div_le_div_of_nonneg_right hk hβ.le) hbk
      have hpred : a ≤ d k + normalCost k :=
        (mul_le_mul (mul_le_mul_of_nonneg_left hk hκ.le) hmin
          (le_min (div_nonneg hε.le hβ.le) hb.le) (mul_nonneg hκ.le (hχ k))).trans hTk
      exact (not_lt_of_ge (hpred.trans (add_le_add_left hd _))) hdiffk
    exact hS hbad
  refine ⟨?_, hfreq⟩
  have hbdd : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) χ :=
    ⟨0, show ∀ᶠ k in atTop, 0 ≤ χ k from Eventually.of_forall hχ⟩
  have hc : (atTop : Filter ℕ).IsCoboundedUnder (· ≥ ·) χ := by
    refine ⟨1, fun b h => ?_⟩
    obtain ⟨k, hk, hbk⟩ := ((hfreq 1 zero_lt_one).and_eventually h).exists
    exact hbk.trans hk.le
  refine le_antisymm ?_ (le_liminf_of_le hc (Eventually.of_forall hχ))
  by_contra! hpos
  have hliminf := liminf_le_of_frequently_le
    ((hfreq _ (half_pos hpos)).mono fun _ h => h.le) hbdd
  linarith

/-- Theorem 15.5.14, assembling the infinite-insertion and frozen-filter
tail estimates. The criticality measure here is the single-step measure
in (15.5.45). A failed restoration may instead terminate at a stationary
point for the infeasibility problem. -/
theorem theorem_15_5_14 (θ π : ℕ → ℝ) (A : Set ℕ) (restorationFailure : Prop)
    (hπ : ∀ k, 0 ≤ π k)
    (hinfinite : ¬ restorationFailure → ∀ j : ℕ → ℕ, StrictMono j → (∀ k, j k ∈ A) →
      Tendsto (θ ∘ j) atTop (𝓝 0) ∧ Tendsto (π ∘ j) atTop (𝓝 0))
    (hfinite : ¬ restorationFailure → A.Finite →
      Tendsto θ atTop (𝓝 0) ∧ (∀ ε > 0, ∃ᶠ k in atTop, π k < ε)) :
    restorationFailure ∨ ∃ j : ℕ → ℕ, StrictMono j ∧
      Tendsto (θ ∘ j) atTop (𝓝 0) ∧ Tendsto (π ∘ j) atTop (𝓝 0) := by
  classical
  by_cases hfail : restorationFailure
  · exact Or.inl hfail
  right
  by_cases hA : A.Finite
  · obtain ⟨hθ, hπsmall⟩ := hfinite hfail hA
    have hcluster : MapClusterPt 0 atTop π := by
      apply mapClusterPt_iff_frequently.mpr
      intro s hs
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
      refine (hπsmall ε hε).mono fun k hk => hball ?_
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (hπ k)] using hk
    obtain ⟨j, hj, hlim⟩ := hcluster.tendsto_subseq
    exact ⟨j, hj, hθ.comp hj.tendsto_atTop, hlim⟩
  · obtain ⟨j, hj, hmem⟩ := extraction_of_frequently_atTop
      (Nat.frequently_atTop_iff_infinite.mpr hA)
    exact ⟨j, hj, hinfinite hfail j hj hmem⟩

omit [InnerProductSpace ℝ E] in
/-- Theorem 15.5.13. Relative compactness gives a cluster point of the
jointly feasible and critical subsequence. The vanishing normal step
identifies the limit of the tangential base points with the limit
of the iterates. Continuity and the criticality characterization
then give a first-order critical point. -/
theorem theorem_15_5_13 (x n : ℕ → E) (violation critical : E → ℝ)
    (A : Set ℕ) (restorationFailure : Prop) (firstOrder : E → Prop)
    {U : Set E} (hU : IsCompact U) (hx : ∀ k, x k ∈ U)
    (hχ : ∀ k, 0 ≤ critical (x k + n k))
    (hθcont : Continuous violation) (hχcont : Continuous critical)
    (hKKT : ∀ z, violation z = 0 → critical z = 0 → firstOrder z)
    (hnormal : ∀ j : ℕ → ℕ, StrictMono j →
      Tendsto (fun k => violation (x (j k))) atTop (𝓝 0) →
      ∃ B, ∀ᶠ k in atTop, ‖n (j k)‖ ≤ B * violation (x (j k)))
    (hinfinite : ¬ restorationFailure → ∀ j : ℕ → ℕ, StrictMono j → (∀ k, j k ∈ A) →
      Tendsto (fun k => violation (x (j k))) atTop (𝓝 0) ∧
      Tendsto (fun k => critical (x (j k) + n (j k))) atTop (𝓝 0))
    (hfinite : ¬ restorationFailure → A.Finite →
      Tendsto (fun k => violation (x k)) atTop (𝓝 0) ∧
      (∀ ε > 0, ∃ᶠ k in atTop, critical (x k + n k) < ε)) :
    restorationFailure ∨ ∃ (j : ℕ → ℕ) (xstar : E), StrictMono j ∧
      Tendsto (x ∘ j) atTop (𝓝 xstar) ∧ firstOrder xstar := by
  rcases theorem_15_5_14 (fun k => violation (x k)) (fun k => critical (x k + n k))
    A restorationFailure hχ hinfinite hfinite with hfail | ⟨i, hi, hθ, hχlim⟩
  · exact Or.inl hfail
  right
  obtain ⟨xstar, _, j, hj, hlim⟩ := hU.tendsto_subseq (x := x ∘ i) (fun k => hx (i k))
  let l := i ∘ j
  have hl : StrictMono l := hi.comp hj
  have hθ₀ : Tendsto (fun k => violation (x (l k))) atTop (𝓝 0) := hθ.comp hj.tendsto_atTop
  have hχ₀ : Tendsto (fun k => critical (x (l k) + n (l k))) atTop (𝓝 0) :=
    hχlim.comp hj.tendsto_atTop
  obtain ⟨B, hB⟩ := hnormal l hl hθ₀
  have hn : Tendsto (n ∘ l) atTop (𝓝 0) := by
    refine squeeze_zero_norm' hB ?_
    simpa only [mul_zero] using hθ₀.const_mul B
  have hnormalBase : Tendsto (fun k => x (l k) + n (l k)) atTop (𝓝 xstar) := by
    simpa only [l, Function.comp_apply, add_zero] using hlim.add hn
  refine ⟨l, xstar, hl, hlim, hKKT xstar ?_ ?_⟩
  · exact tendsto_nhds_unique ((hθcont.tendsto xstar).comp hlim) hθ₀
  · exact tendsto_nhds_unique ((hχcont.tendsto xstar).comp hnormalBase) hχ₀

/-- Radius rule of Algorithm 15.5.1, completed for accepted trials
below the first ratio threshold. Such trials can occur when the
switching test fails. The rejection contraction hypothesis is
separate, since the printed parameter range allows equality to one. -/
def sqpFilterRadiusUpdate (γ₀ γ₁ γ₂ η₁ η₂ ρ Δ Δnext : ℝ) (accepted : Bool) : Prop :=
  if accepted = false ∨ ρ < η₁ then Δnext ∈ Set.Icc (γ₀ * Δ) (γ₁ * Δ)
  else if η₂ ≤ ρ then Δnext ∈ Set.Icc Δ (γ₂ * Δ)
  else Δnext ∈ Set.Icc (γ₁ * Δ) Δ

/-- A constant feasible trace can repeatedly reject the same trial if
the rejected radius need not decrease. The objective is quadratic,
the trial minimizes the affine model on the unit ball, and the
gradient at the repeated iterate is nonzero. -/
theorem sqpFilter_unchanged_rejected_radius_counterexample :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ ∃ x s Δ : ℕ → ℝ,
      (∀ k, deriv f (x k) = -1) ∧
      (∀ k, 0 < Δ k ∧ |s k| ≤ Δ k) ∧
      (∀ k, IsMinOn (fun t : ℝ => f (x k) + deriv f (x k) * t)
        (Set.Icc (-Δ k) (Δ k)) (s k)) ∧
      (∀ k, ¬ sqpFilterAcceptsPair (1 / 2) (0, f (x k + s k)) (0, f (x k))) ∧
      (∀ k, x (k + 1) = x k ∧
        sqpFilterRadiusUpdate (1 / 2) 1 2 (1 / 4) (3 / 4) 0 (Δ k) (Δ (k + 1)) false) := by
  let f (x : ℝ) := x ^ 2 - x
  have hf : deriv f 0 = -1 := by
    have h : HasDerivAt f (-1) 0 := by
      convert ((hasDerivAt_pow 2 (0 : ℝ)).sub (hasDerivAt_id 0)) using 1 <;> first | rfl | norm_num
    exact h.deriv
  refine ⟨f, (contDiff_id.pow 2).sub contDiff_id,
    fun _ => 0, fun _ => 1, fun _ => 1, fun _ => hf, ?_, ?_, ?_, ?_⟩
  · intro
    norm_num
  · intro
    apply isMinOn_iff.mpr
    intro y hy
    rw [hf]
    have h := hy.2
    linarith
  · intro
    norm_num [sqpFilterAcceptsPair, f]
  · intro
    norm_num [sqpFilterRadiusUpdate]

/-- Strictly contracting the radius on rejections prevents an infinite
rejection tail whose radii are bounded below. -/
theorem sqpFilter_success_frequently_of_radius_floor (Δ : ℕ → ℝ) (S : Set ℕ)
    {γ : ℝ} (hγ : 0 ≤ γ) (hγ' : γ < 1)
    (hfloor : ∃ b > 0, ∀ᶠ k in atTop, b ≤ Δ k)
    (hreject : ∀ᶠ k in atTop, k ∉ S → Δ (k + 1) ≤ γ * Δ k) :
    ∃ᶠ k in atTop, k ∈ S := by
  by_contra! h
  obtain ⟨b, hb, hB⟩ := hfloor
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hB.and hreject).and h)
  have hpow (j : ℕ) : Δ (N + j) ≤ γ ^ j * Δ N := by
    induction j with
    | zero => simp
    | succ j ih =>
      have h := hN (N + j) (Nat.le_add_right _ _)
      rw [Nat.add_succ, pow_succ]
      refine (h.1.2 h.2).trans ?_
      calc
        _ ≤ γ * (γ ^ j * Δ N) := mul_le_mul_of_nonneg_left ih hγ
        _ = _ := by ring
  have hlim : Tendsto (fun j : ℕ => γ ^ j * Δ N) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ hγ').mul_const (Δ N)
  obtain ⟨j, hj⟩ := (hlim.eventually_lt_const hb).exists
  exact (not_lt_of_ge (((hN (N + j) (Nat.le_add_right _ _)).1.1).trans (hpow j))) hj

end ConnGouldToint.Chapter15
