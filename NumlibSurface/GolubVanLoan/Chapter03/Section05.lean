import Numlib.Direct.ConditionEstimation
import Numlib.Direct.Refinement
import NumlibSurface.GolubVanLoan.Chapter02.Section06
import NumlibSurface.GolubVanLoan.Chapter03.Section04

/-!
# Golub–Van Loan §3.5: improving and estimating accuracy

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition, §3.5:
the rigorous readings of Heuristic I and (3.5.2), scaling ((3.5.3), equilibration), iterative
improvement ((3.5.4), mixed precision (3.5.5)) and condition estimation (the implication of Cline,
Moler, Stewart and Wilkinson).

## Design

The `∞`-norm of a vector is Mathlib's sup norm on `Fin n → ℝ`, that of a matrix Mathlib's scoped
`Matrix.Norms.Operator` norm (`= Matrix.lpOpNorm ⊤`, `Matrix.lpOpNorm_top`), and
`κ_∞(A) = Matrix.condNumberLp ⊤ A`. Heuristics I–III, (3.5.1) and the "correct digits" statements
have no rigorous reading beyond the planned nodes: each rigorous node says which inequality the
heuristic rests on. The iterative improvement programs are written with the rounding hook as the
other algorithms of the chapter; their exact semantics is `A x_new = b`. The mixed-precision
program takes two hooks, the working precision `rnd` and the residual precision `rndHi`; the
residual is stored back in working precision (one `rnd` after the `rndHi` flops).
-/

open FloatingPoint Matrix

open scoped Matrix.Norms.Operator

namespace GolubVanLoan.Chapter03

variable {n : ℕ}

/-! ### Residuals and accuracy (§3.5.1) -/

/-- The residual of a solution of a nearby system: if `(A + E) x̂ = b` then
`‖b - A x̂‖_∞ ≤ ‖E‖_∞ ‖x̂‖_∞`. -/
theorem norm_residual_le_of_add_mulVec_eq {A E : Matrix (Fin n) (Fin n) ℝ} {b x : Fin n → ℝ}
    (h : (A + E) *ᵥ x = b) : ‖b - A *ᵥ x‖ ≤ ‖E‖ * ‖x‖ := by
  have : b - A *ᵥ x = E *ᵥ x := by rw [← h, add_mulVec]; abel
  rw [this]
  exact linfty_opNorm_mulVec E x

/-- **Heuristic I**, its rigorous reading: "Gaussian elimination produces a solution `x̂` with a
relatively small residual" — under the hypotheses of (3.4.9), every computed solution of
Gaussian elimination with partial pivoting has `‖b - A x̂‖_∞ ≤ n² (1 + u) γ_{3n} ρ ‖A‖_∞ ‖x̂‖_∞`,
the rigorous form of `‖b - A x̂‖_∞ ≈ u ‖A‖_∞ ‖x̂‖_∞`. -/
theorem heuristic_I {fp : RoundingModel ℝ} (hu : fp.u < 1) (hn : ((3 * n : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ out ∈ (algorithm_3_4_1 fp.round A).run, (∀ j, out.1 j j ≠ 0) →
      (∀ i j, |packedU out.1 i j| ≤ ρ * ‖A‖) →
      ∀ x ∈ (solvePLU fp.round out.1 out.2 b).run,
        ‖b - A *ᵥ x‖ ≤ (n : ℝ) ^ 2 * (1 + fp.u) * gamma fp.u (3 * n) * ρ * ‖A‖ * ‖x‖ := by
  intro out hout hpiv hU x hx
  obtain ⟨E, hAx, hE⟩ := equation_3_4_9 hu hn A b hρ out hout hpiv hU x hx
  exact (norm_residual_le_of_add_mulVec_eq hAx).trans
    (mul_le_mul_of_nonneg_right hE (norm_nonneg _))

/-- **(3.5.2)**, rigorous reading: combining Theorem 2.6.2 with a backward error
`(A + E) x̂ = b`, `‖E‖_∞ ≤ ε ‖A‖_∞`, gives `‖x̂ - x‖_∞ / ‖x‖_∞ ≤ 2 ε κ_∞(A) / (1 - ε κ_∞(A))` —
the book's `‖x̂ - x‖_∞ / ‖x‖_∞ ≈ u κ_∞(A)` for `ε` of order `u`. -/
theorem equation_3_5_2 {A E : Matrix (Fin n) (Fin n) ℝ} {b x y : Fin n → ℝ} (hA : IsUnit A)
    (hx : A *ᵥ x = b) (hb : b ≠ 0) (hy : (A + E) *ᵥ y = b) {ε : ℝ} (hε : 0 ≤ ε)
    (hE : ‖E‖ ≤ ε * ‖A‖) (hr : ε * condNumberLp ⊤ A < 1) :
    ‖y - x‖ / ‖x‖ ≤ 2 * ε / (1 - ε * condNumberLp ⊤ A) * condNumberLp ⊤ A := by
  have h := GolubVanLoan.Chapter02.theorem_2_6_2 ⊤ (ΔA := E) (Δb := 0) (y := y) hA hx hb
    (by rw [add_zero]; exact hy)
    (by rw [lpOpNorm_top, lpOpNorm_top]; exact hE)
    (by rw [WithLp.toLp_zero, norm_zero]; exact mul_nonneg hε (norm_nonneg _)) hr
  simpa only [PiLp.norm_toLp] using h

/-! ### Scaling (§3.5.2) -/

/-- **(3.5.3)**, its exact part: for nonsingular (in the book diagonal) `D₁`, `D₂`, `Ax = b` is
the scaled system `(D₁⁻¹ A D₂) y = D₁⁻¹ b` with `x = D₂ y`, and the relative error of `ŷ` is the
relative error of `x̂ = D₂ ŷ` in the `D₂`-norm `‖z‖_{D₂} = ‖D₂⁻¹ z‖_∞`. The "`≈ u κ_∞(D₁⁻¹ A D₂)`"
is (3.5.2) for the scaled system. -/
theorem equation_3_5_3 {D₁ D₂ : Matrix (Fin n) (Fin n) ℝ} (h₁ : IsUnit D₁) (h₂ : IsUnit D₂)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    (∀ x, A *ᵥ x = b ↔ (D₁⁻¹ * A * D₂) *ᵥ (D₂⁻¹ *ᵥ x) = D₁⁻¹ *ᵥ b) ∧
      ∀ y ŷ : Fin n → ℝ, ‖D₂⁻¹ *ᵥ (D₂ *ᵥ ŷ - D₂ *ᵥ y)‖ / ‖D₂⁻¹ *ᵥ (D₂ *ᵥ y)‖ =
        ‖ŷ - y‖ / ‖y‖ := by
  have hD : D₂⁻¹ * D₂ = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 h₂)
  refine ⟨fun x => scaled_mulVec_eq_iff (isUnit_nonsing_inv_iff.2 h₁) h₂ A x b,
    fun y ŷ => ?_⟩
  rw [← mulVec_sub, mulVec_mulVec, mulVec_mulVec, hD, one_mulVec, one_mulVec]

/-- §3.5.2, row–column equilibration: "the object is to choose `D₁` and `D₂` so that the
`∞`-norm of each row and column of `D₁⁻¹ A D₂` belongs to the interval `[1/β, 1]`". -/
def IsEquilibrated (β : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i, 1 / β ≤ ‖M i‖ ∧ ‖M i‖ ≤ 1) ∧ ∀ j, 1 / β ≤ ‖Mᵀ j‖ ∧ ‖Mᵀ j‖ ≤ 1

/-! ### Iterative improvement (§3.5.3) -/

section Improvement

variable {M : Type → Type} [Monad M]

/-- A loop writing entry `k` with a value `g k` fixed in advance sets the listed entries. -/
theorem foldl_update_apply (u : (Fin n → ℝ) → Fin n → Fin n → ℝ) (g : Fin n → ℝ)
    (hu : ∀ y k, u y k = Function.update y k (g k)) (l : List (Fin n)) (y₀ : Fin n → ℝ)
    (i : Fin n) : l.foldl u y₀ i = if i ∈ l then g i else y₀ i := by
  induction l generalizing y₀ with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, hu]
    by_cases hi : i ∈ l <;> by_cases hia : i = a <;> simp [hi, hia]

variable (rnd : ℝ → M ℝ)

/-- **(3.5.4)**, one step of iterative improvement with `PA = LU`:
```
r = b - A x̂
Solve Ly = Pr.
Solve Uz = y.
x_new = x̂ + z
```
The residual row by row, `r_i = fl(b_i - fl(A(i,:) · x̂))` with the dot product of Algorithm 1.1.1;
the solves are `solvePLU`; the update entrywise rounded. -/
noncomputable def iterativeImprovementStep (A F : Matrix (Fin n) (Fin n) ℝ) (piv : Fin n → Fin n)
    (b x : Fin n → ℝ) : M (Fin n → ℝ) := do
  let r ← (List.finRange n).foldlM (fun (r : Fin n → ℝ) i => do
    let s ← dotAccum rnd (List.finRange n) (A i) x 0
    let ri ← rnd (b i - s)
    pure (Function.update r i ri)) 0
  let z ← solvePLU rnd F piv r
  (List.finRange n).foldlM (fun (y : Fin n → ℝ) i => do
    let yi ← rnd (x i + z i)
    pure (Function.update y i yi)) x

/-- **(3.5.5)**, mixed-precision iterative improvement: "once we have computed `PA = LU` and
initialize `x = 0`, we repeat
```
r = b - Ax (higher precision)
Solve Ly = Pr for y and Uz = y for z.
x = x + z
```
" `k` times. The residual is computed with the hook `rndHi` (the `2t`-digit arithmetic) and stored
in working precision (one `rnd`); everything else uses the working hook `rnd`. -/
noncomputable def mixedPrecisionImprovement (rndHi : ℝ → M ℝ) (A F : Matrix (Fin n) (Fin n) ℝ)
    (piv : Fin n → Fin n) (b : Fin n → ℝ) (k : ℕ) : M (Fin n → ℝ) :=
  (List.range k).foldlM (fun (x : Fin n → ℝ) _ => do
    let r ← (List.finRange n).foldlM (fun (r : Fin n → ℝ) i => do
      let s ← dotAccum rndHi (List.finRange n) (A i) x 0
      let t ← rndHi (b i - s)
      let ri ← rnd t
      pure (Function.update r i ri)) 0
    let z ← solvePLU rnd F piv r
    (List.finRange n).foldlM (fun (y : Fin n → ℝ) i => do
      let yi ← rnd (x i + z i)
      pure (Function.update y i yi)) x) 0

end Improvement

/-- The exact solve through packed factors of `PA = LU` solves `A z = r`. -/
theorem mulVec_solvePLU_id {A F : Matrix (Fin n) (Fin n) ℝ} {piv : Fin n → Fin n}
    (hLU : IsLU ((pivPerm piv).permMatrix ℝ * A) (packedL F) (packedU F))
    (hd : ∀ i, packedU F i i ≠ 0) (r : Fin n → ℝ) :
    A *ᵥ Id.run (solvePLU pure F piv r) = r := by
  change A *ᵥ Id.run (algorithm_3_1_2 pure (packedU F)
    (Id.run (algorithm_3_1_1 pure (packedL F) (applyPiv piv r)))) = r
  rw [algorithm_3_1_1_eq_forwardSubst, algorithm_3_1_2_eq_backSubst, (applyPiv_eq _ _).1]
  exact mulVec_luSolve_permMatrix r hLU hd

/-- The exact residual loop computes `b - A x`. -/
private theorem residual_id (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) :
    (List.finRange n).foldl (fun (r : Fin n → ℝ) i =>
      Function.update r i (b i - (0 + ((List.finRange n).map fun k => A i k * x k).sum))) 0 =
      b - A *ᵥ x := by
  funext i
  rw [foldl_update_apply _ (fun i => b i - (0 + ((List.finRange n).map fun k => A i k * x k).sum))
    (fun _ _ => rfl)]
  simp [mulVec, dotProduct, Fin.sum_univ_def]

/-- The exact correction loop computes `x + z`. -/
private theorem update_add_id (x z : Fin n → ℝ) :
    (List.finRange n).foldl (fun (y : Fin n → ℝ) i => Function.update y i (x i + z i)) x =
      x + z := by
  funext i
  rw [foldl_update_apply _ (fun i => x i + z i) (fun _ _ => rfl)]
  simp

/-- **(3.5.4)**, "in exact arithmetic `A x_new = A x̂ + A z = (b - r) + r = b`": with exact factors
`PA = LU` of a nonsingular `A` (a nonzero diagonal of `U`), one step of iterative improvement from
any `x̂` lands on the solution. -/
theorem equation_3_5_4 {A F : Matrix (Fin n) (Fin n) ℝ} {piv : Fin n → Fin n}
    (hLU : IsLU ((pivPerm piv).permMatrix ℝ * A) (packedL F) (packedU F))
    (hd : ∀ i, packedU F i i ≠ 0) (b x : Fin n → ℝ) :
    A *ᵥ Id.run (iterativeImprovementStep pure A F piv b x) = b := by
  have h : Id.run (iterativeImprovementStep pure A F piv b x) =
      x + Id.run (solvePLU pure F piv (b - A *ᵥ x)) := by
    simp only [iterativeImprovementStep, dotAccum_pure, pure_bind, List.foldlM_pure]
    rw [← residual_id A b x, ← update_add_id]
    rfl
  rw [h, mulVec_add, mulVec_solvePLU_id hLU hd]
  abel

/-- **(3.5.5)** in exact arithmetic: with both hooks exact and exact factors of a nonsingular `A`,
after `k ≥ 1` passes mixed-precision iterative improvement returns the solution of `Ax = b` (the
first pass lands on it, and a pass from the solution stays there, (3.5.4)). -/
theorem equation_3_5_5 {A F : Matrix (Fin n) (Fin n) ℝ} {piv : Fin n → Fin n}
    (hLU : IsLU ((pivPerm piv).permMatrix ℝ * A) (packedL F) (packedU F))
    (hd : ∀ i, packedU F i i ≠ 0) (b : Fin n → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    A *ᵥ Id.run (mixedPrecisionImprovement pure pure A F piv b k) = b := by
  have hstep : ∀ x : Fin n → ℝ, Id.run (do
      let r ← (List.finRange n).foldlM (fun (r : Fin n → ℝ) i => do
        let s ← dotAccum pure (List.finRange n) (A i) x 0
        let t ← pure (b i - s)
        let ri ← pure t
        pure (Function.update r i ri)) 0
      let z ← solvePLU pure F piv r
      (List.finRange n).foldlM (fun (y : Fin n → ℝ) i => do
        let yi ← pure (x i + z i)
        pure (Function.update y i yi)) x : Id _) =
      x + Id.run (solvePLU pure F piv (b - A *ᵥ x)) := fun x => by
    simp only [dotAccum_pure, pure_bind, List.foldlM_pure]
    rw [← residual_id A b x, ← update_add_id]
    rfl
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [mixedPrecisionImprovement, List.idRun_foldlM, add_comm, List.range_succ, List.foldl_append,
    List.foldl_cons, List.foldl_nil, hstep, mulVec_add, mulVec_solvePLU_id hLU hd]
  abel

/-! ### Condition estimation (§3.5.4) -/

/-- §3.5.4, the implication of Cline, Moler, Stewart and Wilkinson: "`Ay = d ⇒
‖A⁻¹‖_∞ ≥ ‖y‖_∞ / ‖d‖_∞`", written `‖y‖_∞ ≤ ‖A⁻¹‖_∞ ‖d‖_∞`, and hence the estimate
`κ̂_∞ = ‖A‖_∞ ‖y‖_∞ / ‖d‖_∞` never exceeds `κ_∞(A)`. -/
theorem condEstimate_lowerBound {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) {y d : Fin n → ℝ}
    (hy : A *ᵥ y = d) :
    ‖y‖ ≤ ‖A⁻¹‖ * ‖d‖ ∧ ‖A‖ * ‖y‖ / ‖d‖ ≤ condNumberLp ⊤ A := by
  have h₁ := norm_le_lpOpNorm_inv_mul_lpSeminorm_mulVec ⊤ hA y
  rw [lpSeminorm_apply, lpSeminorm_apply, PiLp.norm_toLp, PiLp.norm_toLp, hy,
    lpOpNorm_top] at h₁
  have h₂ := lpCondEstimate_le_condNumberLp ⊤ hA d
  have hy' : A⁻¹ *ᵥ d = y := by
    rw [← hy, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hA), one_mulVec]
  rw [lpCondEstimate, hy', lpSeminorm_apply, lpSeminorm_apply, PiLp.norm_toLp, PiLp.norm_toLp,
    lpOpNorm_top] at h₂
  exact ⟨h₁, h₂⟩

/-! ### Back substitution with a chosen right-hand side (3.5.6) -/

section ChosenRHS

/-- **A loop invariant for `List.foldl`**, indexed by the processed prefix. -/
theorem foldl_invariant {α σ : Type*} {l : List α} (f : σ → α → σ) (I : List α → σ → Prop)
    {s₀ : σ} (h0 : I [] s₀) (hstep : ∀ p x q, l = p ++ x :: q → ∀ s, I p s → I (p ++ [x]) (f s x)) :
    I l (l.foldl f s₀) := by
  suffices H : ∀ (r p : List α) (s : σ), p ++ r = l → I p s → I l (r.foldl f s) from
    H l [] s₀ rfl h0
  intro r
  induction r with
  | nil => rintro p s rfl hs; simpa using hs
  | cons x r ih =>
    rintro p s rfl hs
    exact ih (p ++ [x]) (f s x) (by simp) (hstep p x r rfl s hs)

/-- A loop over a duplicate-free list rewriting entry `k` from its current value writes every
listed entry once, from its initial value. -/
theorem foldl_update_self_apply {n : ℕ} (h : Fin n → ℝ → ℝ) {l : List (Fin n)} (hl : l.Nodup)
    (y₀ : Fin n → ℝ) (i : Fin n) :
    l.foldl (fun y k => Function.update y k (h k (y k))) y₀ i =
      if i ∈ l then h i (y₀ i) else y₀ i := by
  induction l generalizing y₀ with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih (List.nodup_cons.1 hl).2]
    have ha := (List.nodup_cons.1 hl).1
    by_cases hi : i ∈ l
    · have hia : i ≠ a := fun e => ha (e ▸ hi)
      simp [hi, hia]
    · by_cases hia : i = a
      · subst hia; simp [hi]
      · simp [hi, hia]

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {n : ℕ}

/-- **(3.5.6)**, the column version of back substitution with the right-hand side chosen on the
fly, "normally used to solve `Ty = d`, but in the condition estimation setting we are free to pick
the right-hand side":
```
p(1:n) = 0
for k = n:-1:1
    Choose d(k).
    y(k) = (d(k) - p(k))/T(k,k)
    p(1:k-1) = p(1:k-1) + y(k) T(1:k-1,k)
end
```
The choice is a function `choose k p` of the step and of the running vector `p` (exact: the
sign of `p(k)`, or the look-ahead of Algorithm 3.5.1); every difference, quotient, product and sum
is rounded. Returns `(y, d)`. -/
noncomputable def backSubstChosenRHS (choose : Fin n → (Fin n → ℝ) → ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ) : M ((Fin n → ℝ) × (Fin n → ℝ)) := do
  let st ← (List.finRange n).reverse.foldlM
    (fun (st : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) k => do
      let t ← rnd (choose k st.2.2 - st.2.2 k)
      let yk ← rnd (t / T k k)
      let p ← ((List.finRange n).filter (· < k)).foldlM (fun (p : Fin n → ℝ) i => do
        let q ← rnd (yk * T i k)
        let pi ← rnd (p i + q)
        pure (Function.update p i pi)) st.2.2
      pure (Function.update st.1 k yk, Function.update st.2.1 k (choose k st.2.2), p)) (0, 0, 0)
  pure (st.1, st.2.1)

/-- In the reversed list of indices, the indices processed before `x` are those above `x`. -/
theorem mem_prefix_reverse_finRange_iff {p q : List (Fin n)} {x : Fin n}
    (h : (List.finRange n).reverse = p ++ x :: q) (j : Fin n) : j ∈ p ↔ x < j := by
  have hs : (List.finRange n).reverse.Pairwise (fun a b => b < a) :=
    List.pairwise_reverse.2 (List.pairwise_lt_finRange n)
  constructor
  · intro hj
    rw [h] at hs
    exact (List.pairwise_append.1 hs).2.2 j hj x List.mem_cons_self
  · intro hxj
    exact mem_prefix_of_pairwise hs h (List.mem_reverse.2 (List.mem_finRange j)) (ne_of_gt hxj)
      (lt_asymm hxj)

/-- The exact run of (3.5.6): each `y(k)` solves row `k` of `T y = d` given the later entries,
every `d(k)` is a choice `choose k q` for some running vector `q`. -/
theorem backSubstChosenRHS_id {choose : Fin n → (Fin n → ℝ) → ℝ} {T : Matrix (Fin n) (Fin n) ℝ}
    (hd : ∀ i, T i i ≠ 0) :
    (∀ j, (Id.run (backSubstChosenRHS pure choose T)).1 j * T j j =
      (Id.run (backSubstChosenRHS pure choose T)).2 j -
        ∑ l ∈ Finset.univ.filter (j < ·), T j l * (Id.run (backSubstChosenRHS pure choose T)).1 l) ∧
      ∀ j, ∃ q, (Id.run (backSubstChosenRHS pure choose T)).2 j = choose j q := by
  let step : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) → Fin n →
      (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) := fun st k =>
    (Function.update st.1 k ((choose k st.2.2 - st.2.2 k) / T k k),
      Function.update st.2.1 k (choose k st.2.2),
      ((List.finRange n).filter (· < k)).foldl (fun p i => Function.update p i
        (p i + (choose k st.2.2 - st.2.2 k) / T k k * T i k)) st.2.2)
  have hrun : Id.run (backSubstChosenRHS pure choose T) =
      (((List.finRange n).reverse.foldl step (0, 0, 0)).1,
        ((List.finRange n).reverse.foldl step (0, 0, 0)).2.1) := by
    simp only [backSubstChosenRHS, pure_bind, List.foldlM_pure]
    rfl
  rw [hrun]
  let I : List (Fin n) → (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) → Prop := fun pr st =>
    (∀ j ∈ pr, st.1 j * T j j = st.2.1 j - ∑ l ∈ Finset.univ.filter (j < ·), T j l * st.1 l) ∧
    (∀ j ∈ pr, ∃ q, st.2.1 j = choose j q) ∧
    (∀ i, i ∉ pr → st.2.2 i = ∑ j ∈ Finset.univ.filter (· ∈ pr), T i j * st.1 j)
  have hI : I (List.finRange n).reverse ((List.finRange n).reverse.foldl step (0, 0, 0)) := by
    refine foldl_invariant step I ⟨by simp, by simp, fun i _ => by simp⟩ ?_
    rintro pr x q hl ⟨y, d, p⟩ ⟨h₁, h₂, h₃⟩
    dsimp only at h₁ h₂ h₃
    have hmem := mem_prefix_reverse_finRange_iff hl
    have hxpr : x ∉ pr := fun h => lt_irrefl x ((hmem x).1 h)
    have hy' : ∀ j, j ≠ x → Function.update y x ((choose x p - p x) / T x x) j = y j :=
      fun j hj => Function.update_of_ne hj _ _
    have hp' : ∀ i, ((List.finRange n).filter (· < x)).foldl (fun p' i => Function.update p' i
        (p' i + (choose x p - p x) / T x x * T i x)) p i =
        if i < x then p i + (choose x p - p x) / T x x * T i x else p i := fun i => by
      rw [foldl_update_self_apply (fun i v => v + (choose x p - p x) / T x x * T i x)
        ((List.nodup_finRange n).filter _)]
      simp
    refine ⟨fun j hj => ?_, fun j hj => ?_, fun i hi => ?_⟩
    · rcases List.mem_append.1 hj with hj | hj
      · have hxj : x < j := (hmem j).1 hj
        simp only [step]
        rw [hy' j (ne_of_gt hxj), Function.update_of_ne (ne_of_gt hxj), h₁ j hj]
        congr 1
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [hy' l (ne_of_gt (hxj.trans (Finset.mem_filter.1 hl).2))]
      · rw [List.mem_singleton.1 hj]
        simp only [step, Function.update_self]
        rw [div_mul_cancel₀ _ (hd x), h₃ x hxpr]
        congr 1
        refine Finset.sum_congr (by ext l; simp [hmem]) fun l hl => ?_
        rw [Function.update_of_ne (ne_of_gt (Finset.mem_filter.1 hl).2)]
    · rcases List.mem_append.1 hj with hj | hj
      · obtain ⟨q', hq'⟩ := h₂ j hj
        refine ⟨q', ?_⟩
        simp only [step]
        rw [Function.update_of_ne (ne_of_gt ((hmem j).1 hj)), hq']
      · rw [List.mem_singleton.1 hj]
        exact ⟨p, by simp [step]⟩
    · have hix : i ≠ x := fun h => hi (List.mem_append.2 (Or.inr (h ▸ List.mem_singleton_self x)))
      have hipr : i ∉ pr := fun h => hi (List.mem_append.2 (Or.inl h))
      have hlt : i < x := by
        rcases lt_or_gt_of_ne hix with h | h
        · exact h
        · exact absurd ((hmem i).2 h) hipr
      simp only [step]
      rw [hp' i]
      simp only [hlt, ↓reduceIte]
      rw [h₃ i hipr]
      have hsplit : Finset.univ.filter (· ∈ pr ++ [x]) =
          insert x (Finset.univ.filter (· ∈ pr)) := by
        ext j; simp [or_comm]
      rw [hsplit, Finset.sum_insert (by simp [hxpr]), Function.update_self]
      rw [add_comm]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [hy' j (fun h => hxpr (h ▸ (Finset.mem_filter.1 hj).2))]
  exact ⟨fun j => hI.1 j (List.mem_reverse.2 (List.mem_finRange j)),
    fun j => hI.2.1 j (List.mem_reverse.2 (List.mem_finRange j))⟩

/-- **(3.5.6) solves the system it builds**: for upper triangular `T` with nonzero diagonal, the
exact output `(y, d)` of back substitution with the right-hand side chosen on the fly satisfies
`T y = d`. -/
theorem equation_3_5_6 {choose : Fin n → (Fin n → ℝ) → ℝ} {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.IsUpperTriangular) (hd : ∀ i, T i i ≠ 0) :
    T *ᵥ (Id.run (backSubstChosenRHS pure choose T)).1 =
      (Id.run (backSubstChosenRHS pure choose T)).2 := by
  funext j
  rw [mulVec_apply_of_isUpperTriangular hT, mul_comm, (backSubstChosenRHS_id hd).1 j]
  ring

/-- The sign choice of §3.5.4, "`d(k) = -sign(p(k))`": `-1` if `p(k) ≥ 0`, `+1` otherwise. -/
noncomputable def signChoice (k : Fin n) (p : Fin n → ℝ) : ℝ := if 0 ≤ p k then -1 else 1

/-- §3.5.4: with `d(k) = -sign(p(k))` the right-hand side is a sign vector, "since this is a unit
vector, we obtain the estimate `κ̂_∞ = ‖T‖_∞ ‖y‖_∞`", a lower bound for `κ_∞(T)` for nonsingular
upper triangular `T`. -/
theorem backSubstChosenRHS_sign [NeZero n] {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.IsUpperTriangular) (hd : ∀ i, T i i ≠ 0) :
    (∀ j, |(Id.run (backSubstChosenRHS pure signChoice T)).2 j| = 1) ∧
      ‖T‖ * ‖(Id.run (backSubstChosenRHS pure signChoice T)).1‖ ≤ condNumberLp ⊤ T := by
  have hsign : ∀ j, |(Id.run (backSubstChosenRHS pure signChoice T)).2 j| = 1 := fun j => by
    obtain ⟨q, hq⟩ := (backSubstChosenRHS_id (choose := signChoice) hd).2 j
    rw [hq, signChoice]
    split_ifs <;> simp
  refine ⟨hsign, ?_⟩
  have hU : IsUnit T := (isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular hT).2 hd
  have := linfty_opNorm_mul_norm_le_condNumberLp_top_of_mulVec_eq hU (equation_3_5_6 hT hd)
    fun j => by rw [Real.norm_eq_abs]; exact hsign j
  rwa [lpOpNorm_top] at this

end ChosenRHS

/-! ### The condition estimator (Algorithm 3.5.1) and the `PA = LU` estimate (§3.5.4) -/

section Estimator

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {n : ℕ}

/-- The `∞`-norm of a matrix computed as the largest rounded row sum of absolute values (the
`O(n²)` formula (2.3.10)): each row sum `fl(⋯fl(|a_i1| + |a_i2|)⋯)`, then the maximum, which
compares only (the sup norm of the vector of row sums). -/
noncomputable def linftyNormRounded {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : M ℝ := do
  let r ← (List.finRange m).foldlM (fun (r : Fin m → ℝ) i => do
    let s ← (List.finRange n).foldlM (fun (c : ℝ) j => rnd (c + |A i j|)) 0
    pure (Function.update r i s)) 0
  pure ‖r‖

/-- **Algorithm 3.5.1 (Condition Estimator).** "Let `T ∈ ℝ^{n×n}` be a nonsingular upper triangular
matrix. This algorithm computes unit `∞`-norm `y` and a scalar `κ` so `‖Ty‖_∞ ≈ 1/‖T⁻¹‖_∞` and
`κ ≈ κ_∞(T)`."
```
p(1:n) = 0
for k = n:-1:1
    y(k)⁺ = (1 - p(k))/T(k,k)
    y(k)⁻ = (-1 - p(k))/T(k,k)
    p(k)⁺ = p(1:k-1) + T(1:k-1,k) y(k)⁺
    p(k)⁻ = p(1:k-1) + T(1:k-1,k) y(k)⁻
    if |y(k)⁺| + ‖p(k)⁺‖₁ ≥ |y(k)⁻| + ‖p(k)⁻‖₁
        y(k) = y(k)⁺,  p(1:k-1) = p(k)⁺
    else
        y(k) = y(k)⁻,  p(1:k-1) = p(k)⁻
    end
end
κ = ‖y‖_∞ ‖T‖_∞
y = y/‖y‖_∞
```
Every flop is rounded, those of the look-ahead scores included (convention 1); `|·|`, the
comparison and the maximum `‖y‖_∞` are exact; `‖T‖_∞` is `linftyNormRounded`. Returns `(κ, y)`. -/
noncomputable def algorithm_3_5_1 (T : Matrix (Fin n) (Fin n) ℝ) : M (ℝ × (Fin n → ℝ)) := do
  let st ← (List.finRange n).reverse.foldlM (fun (st : (Fin n → ℝ) × (Fin n → ℝ)) k => do
    let tp ← rnd (1 - st.2 k)
    let yp ← rnd (tp / T k k)
    let tm ← rnd (-1 - st.2 k)
    let ym ← rnd (tm / T k k)
    let pp ← ((List.finRange n).filter (· < k)).foldlM (fun (q : Fin n → ℝ) i => do
      let a ← rnd (T i k * yp)
      let b ← rnd (q i + a)
      pure (Function.update q i b)) st.2
    let pm ← ((List.finRange n).filter (· < k)).foldlM (fun (q : Fin n → ℝ) i => do
      let a ← rnd (T i k * ym)
      let b ← rnd (q i + a)
      pure (Function.update q i b)) st.2
    let sp ← ((List.finRange n).filter (· < k)).foldlM (fun (c : ℝ) i => rnd (c + |pp i|)) |yp|
    let sm ← ((List.finRange n).filter (· < k)).foldlM (fun (c : ℝ) i => rnd (c + |pm i|)) |ym|
    if sm ≤ sp then pure (Function.update st.1 k yp, pp)
    else pure (Function.update st.1 k ym, pm)) (0, 0)
  let tn ← linftyNormRounded rnd T
  let κ ← rnd (‖st.1‖ * tn)
  let y ← (List.finRange n).foldlM (fun (y : Fin n → ℝ) i => do
    let yi ← rnd (st.1 i / ‖st.1‖)
    pure (Function.update y i yi)) st.1
  pure (κ, y)

/-- §3.5.4, condition estimation from `PA = LU`:
"Step 1. Apply the lower triangular version of Algorithm 3.5.1 to `Uᵀ` and obtain a large-norm
solution to `Uᵀy = d`. Step 2. Solve the triangular systems `Lᵀr = y`, `Lw = Pr`, and `Uz = w`.
Step 3. Set `κ̂_∞ = ‖A‖_∞ ‖z‖_∞ / ‖r‖_∞`." The lower triangular version of Algorithm 3.5.1 on
`Uᵀ` is
Algorithm 3.5.1 on `Uᵀ` read in the reversed order (an upper triangular matrix); `Lᵀr = y` is
Algorithm 3.1.2; `Lw = Pr`, `Uz = w` is `solvePLU`. -/
noncomputable def luCondEstimate (A F : Matrix (Fin n) (Fin n) ℝ) (piv : Fin n → Fin n) : M ℝ := do
  let out ← algorithm_3_5_1 rnd ((packedU F)ᵀ.submatrix Fin.rev Fin.rev)
  let r ← algorithm_3_1_2 rnd (packedL F)ᵀ (out.2 ∘ Fin.rev)
  let z ← solvePLU rnd F piv r
  let an ← linftyNormRounded rnd A
  let t ← rnd (an * ‖z‖)
  rnd (t / ‖r‖)

/-- In exact arithmetic the rounded `∞`-norm is the `∞`-norm. -/
theorem linftyNormRounded_id {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (linftyNormRounded pure A) = ‖A‖ := by
  have hrow : ∀ i, (List.finRange n).foldl (fun (c : ℝ) j => c + |A i j|) 0 = ∑ j, |A i j| :=
    fun i => by rw [List.foldl_add_eq_add_sum_map, zero_add, Fin.sum_univ_def]
  have hr : (List.finRange m).foldl (fun (r : Fin m → ℝ) i => Function.update r i
      ((List.finRange n).foldl (fun (c : ℝ) j => c + |A i j|) 0)) 0 = fun i => ∑ j, |A i j| := by
    funext i
    rw [foldl_update_apply _ (fun i => (List.finRange n).foldl (fun (c : ℝ) j => c + |A i j|) 0)
      (fun _ _ => rfl), hrow]
    simp
  have h : Id.run (linftyNormRounded pure A) = ‖fun i => ∑ j, |A i j|‖ := by
    simp only [linftyNormRounded, pure_bind, List.foldlM_pure]
    rw [← hr]
    rfl
  rw [h]
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg A)).2 fun i => ?_) ?_
  · rw [Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)]
    exact sum_abs_apply_le_linfty_opNorm A i
  · refine linfty_opNorm_le_of_forall_sum_le (norm_nonneg _) fun i => ?_
    refine (le_abs_self _).trans ?_
    have := norm_le_pi_norm (fun i => ∑ j, |A i j|) i
    rwa [Real.norm_eq_abs] at this

/-- **§3.5.4, "note that `‖z‖_∞ ≤ ‖A⁻¹‖_∞ ‖r‖_∞`"**: in exact arithmetic, with exact factors
`PA = LU` of a nonsingular `A`, the estimate of `luCondEstimate` never exceeds `κ_∞(A)`,
whatever Step 1 produced, since `Az = r`. -/
theorem luCondEstimate_le {A F : Matrix (Fin n) (Fin n) ℝ} {piv : Fin n → Fin n} (hA : IsUnit A)
    (hLU : IsLU ((pivPerm piv).permMatrix ℝ * A) (packedL F) (packedU F))
    (hd : ∀ i, packedU F i i ≠ 0) :
    Id.run (luCondEstimate pure A F piv) ≤ condNumberLp ⊤ A := by
  set r := Id.run (algorithm_3_1_2 pure (packedL F)ᵀ
    ((Id.run (algorithm_3_5_1 pure ((packedU F)ᵀ.submatrix Fin.rev Fin.rev))).2 ∘ Fin.rev))
  set z := Id.run (solvePLU pure F piv r)
  have hz : A *ᵥ z = r := mulVec_solvePLU_id hLU hd r
  have h : Id.run (luCondEstimate pure A F piv) = ‖A‖ * ‖z‖ / ‖r‖ := by
    change Id.run (linftyNormRounded pure A) * ‖z‖ / ‖r‖ = _
    rw [linftyNormRounded_id]
  rw [h]
  exact (condEstimate_lowerBound hA hz).2

end Estimator

/-! ### What Algorithm 3.5.1 provably computes -/

section EstimatorSpec

variable {n : ℕ}

/-- The exact look-ahead choice of Algorithm 3.5.1: `d(k) = +1` if the score
`|y(k)⁺| + ‖p(k)⁺‖₁` is at least `|y(k)⁻| + ‖p(k)⁻‖₁`, else `-1`. -/
noncomputable def lookaheadChoice (T : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (p : Fin n → ℝ) :
    ℝ :=
  if |(-1 - p k) / T k k| + ∑ i ∈ Finset.univ.filter (· < k),
        |p i + T i k * ((-1 - p k) / T k k)| ≤
      |(1 - p k) / T k k| + ∑ i ∈ Finset.univ.filter (· < k),
        |p i + T i k * ((1 - p k) / T k k)| then 1 else -1

/-- A running sum over the indices before `k` is the sum over them. -/
private theorem foldl_filter_add (k : Fin n) (f : Fin n → ℝ) (c : ℝ) :
    ((List.finRange n).filter (· < k)).foldl (fun c i => c + f i) c =
      c + ∑ i ∈ Finset.univ.filter (· < k), f i := by
  rw [List.foldl_add_eq_add_sum_map, ← List.sum_toFinset _ ((List.nodup_finRange n).filter _)]
  congr 2
  ext i
  simp

/-- The exact step of Algorithm 3.5.1's loop is the step of back substitution with the look-ahead
choice, on the components `(y, p)`. -/
private theorem step_3_5_1_eq (T : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (y p : Fin n → ℝ) :
    (let yp := (1 - p k) / T k k
     let ym := (-1 - p k) / T k k
     let pp := ((List.finRange n).filter (· < k)).foldl
       (fun q i => Function.update q i (q i + T i k * yp)) p
     let pm := ((List.finRange n).filter (· < k)).foldl
       (fun q i => Function.update q i (q i + T i k * ym)) p
     if ((List.finRange n).filter (· < k)).foldl (fun c i => c + |pm i|) |ym| ≤
         ((List.finRange n).filter (· < k)).foldl (fun c i => c + |pp i|) |yp|
       then (Function.update y k yp, pp) else (Function.update y k ym, pm)) =
    (Function.update y k ((lookaheadChoice T k p - p k) / T k k),
      ((List.finRange n).filter (· < k)).foldl (fun q i => Function.update q i
        (q i + (lookaheadChoice T k p - p k) / T k k * T i k)) p) := by
  have hnd := (List.nodup_finRange n).filter (· < k)
  have hq : ∀ c : ℝ, ((List.finRange n).filter (· < k)).foldl
      (fun q i => Function.update q i (q i + T i k * c)) p =
      ((List.finRange n).filter (· < k)).foldl
      (fun q i => Function.update q i (q i + c * T i k)) p := fun c => by
    funext i
    rw [foldl_update_self_apply (fun i v => v + T i k * c) hnd,
      foldl_update_self_apply (fun i v => v + c * T i k) hnd, mul_comm]
  have hval : ∀ c : ℝ, ∀ i, i < k → ((List.finRange n).filter (· < k)).foldl
      (fun q i => Function.update q i (q i + T i k * c)) p i = p i + T i k * c :=
    fun c i hi => by
      rw [foldl_update_self_apply (fun i v => v + T i k * c) hnd]
      simp [hi]
  have hscore : ∀ c : ℝ, ((List.finRange n).filter (· < k)).foldl (fun s i => s + |((List.finRange
      n).filter (· < k)).foldl (fun q i => Function.update q i (q i + T i k * c)) p i|) |c| =
      |c| + ∑ i ∈ Finset.univ.filter (· < k), |p i + T i k * c| := fun c => by
    rw [foldl_filter_add]
    congr 1
    exact Finset.sum_congr rfl fun i hi => by rw [hval c i (Finset.mem_filter.1 hi).2]
  simp only [hscore, lookaheadChoice]
  split_ifs with h
  · rw [hq]
  · rw [hq]

/-- **What Algorithm 3.5.1 provably computes** (the rigorous half of "`‖Ty‖_∞ ≈ 1/‖T⁻¹‖_∞` and
`κ ≈ κ_∞(T)`"): for a nonsingular upper triangular `T` (`n ≥ 1`), in exact arithmetic, the
unnormalized `y₀` solves `T y₀ = d` for a sign vector `d` (`|d(k)| = 1`, the look-ahead choice),
`κ = ‖y₀‖_∞ ‖T‖_∞ ≤ κ_∞(T)`, the returned `y = y₀ / ‖y₀‖_∞` has `‖y‖_∞ = 1`, and
`‖Ty‖_∞ ≥ 1 / ‖T⁻¹‖_∞`. How close `κ` is to `κ_∞(T)` has no theorem. -/
theorem algorithm_3_5_1_spec [NeZero n] {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.IsUpperTriangular) (hd : ∀ i, T i i ≠ 0) :
    ∃ y₀ d : Fin n → ℝ, (∀ i, |d i| = 1) ∧ T *ᵥ y₀ = d ∧
      (Id.run (algorithm_3_5_1 pure T)).1 = ‖y₀‖ * ‖T‖ ∧
      (Id.run (algorithm_3_5_1 pure T)).2 = (fun i => y₀ i / ‖y₀‖) ∧
      (Id.run (algorithm_3_5_1 pure T)).1 ≤ condNumberLp ⊤ T ∧
      ‖(Id.run (algorithm_3_5_1 pure T)).2‖ = 1 ∧
      1 ≤ ‖T⁻¹‖ * ‖T *ᵥ (Id.run (algorithm_3_5_1 pure T)).2‖ := by
  set out := Id.run (backSubstChosenRHS pure (lookaheadChoice T) T)
  -- the exact loop of Algorithm 3.5.1 is back substitution with the look-ahead choice
  let stepBS : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) → Fin n →
      (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) := fun st k =>
    (Function.update st.1 k ((lookaheadChoice T k st.2.2 - st.2.2 k) / T k k),
      Function.update st.2.1 k (lookaheadChoice T k st.2.2),
      ((List.finRange n).filter (· < k)).foldl (fun p i => Function.update p i
        (p i + (lookaheadChoice T k st.2.2 - st.2.2 k) / T k k * T i k)) st.2.2)
  let step35 : (Fin n → ℝ) × (Fin n → ℝ) → Fin n → (Fin n → ℝ) × (Fin n → ℝ) := fun st k =>
    let yp := (1 - st.2 k) / T k k
    let ym := (-1 - st.2 k) / T k k
    let pp := ((List.finRange n).filter (· < k)).foldl
      (fun q i => Function.update q i (q i + T i k * yp)) st.2
    let pm := ((List.finRange n).filter (· < k)).foldl
      (fun q i => Function.update q i (q i + T i k * ym)) st.2
    if ((List.finRange n).filter (· < k)).foldl (fun c i => c + |pm i|) |ym| ≤
        ((List.finRange n).filter (· < k)).foldl (fun c i => c + |pp i|) |yp|
      then (Function.update st.1 k yp, pp) else (Function.update st.1 k ym, pm)
  have hsim : ∀ (l : List (Fin n)) (y d p : Fin n → ℝ),
      l.foldl step35 (y, p) = ((l.foldl stepBS (y, d, p)).1, (l.foldl stepBS (y, d, p)).2.2) := by
    intro l
    induction l with
    | nil => intro y d p; rfl
    | cons k l ih =>
      intro y d p
      rw [List.foldl_cons, List.foldl_cons]
      have h := step_3_5_1_eq T k y p
      change step35 (y, p) k = _ at h
      rw [h]
      exact ih _ _ _
  have hout : out = (((List.finRange n).reverse.foldl stepBS (0, 0, 0)).1,
      ((List.finRange n).reverse.foldl stepBS (0, 0, 0)).2.1) := by
    simp only [out, backSubstChosenRHS, pure_bind, List.foldlM_pure]
    rfl
  set Y := ((List.finRange n).reverse.foldl step35 (0, 0)).1 with hY
  have hYout : Y = out.1 := by
    rw [hY, hsim _ 0 0 0, hout]
  have hrun : Id.run (algorithm_3_5_1 pure T) = (‖Y‖ * Id.run (linftyNormRounded pure T),
      (List.finRange n).foldl (fun y i => Function.update y i (Y i / ‖Y‖)) Y) := by
    simp only [algorithm_3_5_1, pure_bind, ite_pure, List.foldlM_pure]
    rfl
  have hy : (List.finRange n).foldl (fun y i => Function.update y i (Y i / ‖Y‖)) Y =
      fun i => Y i / ‖Y‖ := by
    funext i
    rw [foldl_update_apply _ (fun i => Y i / ‖Y‖) (fun _ _ => rfl)]
    simp
  have hsign : ∀ i, |out.2 i| = 1 := fun i => by
    obtain ⟨q, hq⟩ := (backSubstChosenRHS_id (choose := lookaheadChoice T) hd).2 i
    rw [hq, lookaheadChoice]
    split_ifs <;> simp
  have hTy : T *ᵥ out.1 = out.2 := equation_3_5_6 hT hd
  have hU : IsUnit T := (isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular hT).2 hd
  have hy0 : out.1 ≠ 0 := by
    intro h0
    have := hsign 0
    rw [← hTy, h0, mulVec_zero] at this
    simp at this
  have hκ := linfty_opNorm_mul_norm_le_condNumberLp_top_of_mulVec_eq hU hTy
    fun j => by rw [Real.norm_eq_abs]; exact hsign j
  rw [lpOpNorm_top] at hκ
  have hsmul : (fun i => out.1 i / ‖out.1‖) = (‖out.1‖⁻¹ : ℝ) • out.1 := by
    funext i
    simp [div_eq_inv_mul]
  refine ⟨out.1, out.2, hsign, hTy, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun, linftyNormRounded_id, hYout]
  · rw [hrun, hy, hYout]
  · rw [hrun, linftyNormRounded_id, hYout, mul_comm]
    exact hκ
  · rw [hrun, hy, hYout, hsmul, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hy0)]
  · rw [hrun, hy, hYout, hsmul]
    have := one_le_lpOpNorm_top_inv_mul_norm_mulVec_inv_norm_smul hU hy0
    rwa [lpOpNorm_top] at this

end EstimatorSpec

end GolubVanLoan.Chapter03
