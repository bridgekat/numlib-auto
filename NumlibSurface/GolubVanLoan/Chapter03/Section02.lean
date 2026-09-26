import Numlib.FloatingPoint.LU
import NumlibSurface.GolubVanLoan.Chapter03.Section01

/-!
# Golub–Van Loan §3.2: the LU factorization

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition, §3.2:
Gauss transformations and their rounding errors (§3.2.1–3.2.3), Gaussian elimination as the
factorization `A = L U` ((3.2.3)–(3.2.7), Theorem 3.2.1), the outer product LU of Algorithm 3.2.1
with its rounding bridge into the backbone's `FloatingPoint.RoundsLU`, the rectangular factorization
(§3.2.10) and the Schur complement (3.2.9).

## Design

Indices are 0-based: the book's step `k = 1:n-1` is `k : Fin n` with a harmless empty last step,
its `A^{(k)}` (the matrix after `k - 1` steps in (3.2.3)) is `gaussStage A (k - 1) =
Matrix.gemStage A (k - 1)`, and "`A(1:k,1:k)` is nonsingular for `k = 1:n-1`" is
`∀ k : Fin n, (A.strictLeadingPrincipalSubmatrix k).det ≠ 0` (the order-`0` block is empty).

The Gauss transformation `M_k = I - τ e_kᵀ` is `gaussTransformation τ k`; built from the column of a
matrix by the Gauss vector `gaussVector`, it is the backbone's `Matrix.gaussTransform`
(`gaussTransformation_gaussVector_eq_gaussTransform`), through which (3.2.3)–(3.2.7) are the
backbone's statements about `Matrix.gemStage` and `Matrix.gemLower`.

Algorithm 3.2.1 is a program in the conventions of `NumlibSurface/GolubVanLoan` overwriting the
matrix entry by entry (`Matrix.updateRow A i (Function.update (A i) j a)`); its packed output is
read by `packedL F = 1 + F.strictLower` and `packedU F = F - F.strictLower`. Its bridge
`algorithm_3_2_1_rounds` puts every run in the relational model into `FloatingPoint.RoundsLU`, and
the exact specification is read off the bridge at the exact model
(`FloatingPoint.roundsLU_exact_iff`).
The loops write one matrix entry per step, reading only entries outside the loop's own positions;
`mem_run_foldlM_updateEntry` gives the run set of such a loop, entry by entry.

## Main results

* `gaussTransformation`, `gaussVector`, `IsGaussTransformation` and their algebra (§3.2.1–3.2.2,
  §3.2.5);
* `gaussUpdate`, `gaussVector_rounding`, `gaussUpdate_rounding` (§3.2.3);
* `equation_3_2_3` … `equation_3_2_7`, `theorem_3_2_1` (with `_unique`, `_det`);
* `algorithm_3_2_1`, `algorithm_3_2_1_rounds`, `algorithm_3_2_1_spec`;
* `rectangularLU_exists` (§3.2.10), `equation_3_2_9`.
-/

open FloatingPoint Matrix

namespace GolubVanLoan.Chapter03

/-! ### Loops over matrix entries -/

section Loops

/-- A loop of loops is one loop over the pairs, the outer index first. -/
theorem foldlM_foldlM_eq_foldlM_flatMap {M : Type → Type} [Monad M] [LawfulMonad M]
    {σ α β : Type} (l₁ : List α) (l₂ : α → List β) (f : σ → α → β → M σ) (s : σ) :
    l₁.foldlM (fun s a => (l₂ a).foldlM (fun s b => f s a b) s) s =
      (l₁.flatMap fun a => (l₂ a).map (a, ·)).foldlM (fun s p => f s p.1 p.2) s := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldlM_cons, List.flatMap_cons, List.foldlM_append, List.foldlM_map, ih]

/-- A loop commutes with an equivalence of states that intertwines its steps. -/
theorem map_foldlM_equiv {M : Type → Type} [Monad M] [LawfulMonad M] {σ τ α : Type} (e : σ ≃ τ)
    (f : σ → α → M σ) (f' : τ → α → M τ) (h : ∀ s a, f' (e s) a = e <$> f s a) (l : List α)
    (s : σ) : e <$> l.foldlM f s = l.foldlM f' (e s) := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih => simp only [List.foldlM_cons, map_bind, ih, h, bind_map_left]

/-- A matrix as a function on the positions. -/
def entryEquiv (m n : ℕ) : Matrix (Fin m) (Fin n) ℝ ≃ (Fin m × Fin n → ℝ) where
  toFun A p := A p.1 p.2
  invFun f i j := f (i, j)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Updating one entry of a matrix is updating the matrix, read on positions, at one position. -/
theorem entryEquiv_updateRow_update {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin m × Fin n) (x : ℝ) :
    entryEquiv m n (A.updateRow a.1 (Function.update (A a.1) a.2 x)) =
      Function.update (entryEquiv m n A) a x := by
  funext p
  obtain ⟨i, j⟩ := p
  obtain ⟨i', j'⟩ := a
  change (A.updateRow i' (Function.update (A i') j' x)) i j =
    Function.update (fun p : Fin m × Fin n => A p.1 p.2) (i', j') x (i, j)
  rw [updateRow_apply, Function.update_apply]
  by_cases hi : i = i' <;> by_cases hj : j = j' <;> simp [hi, hj]

/-- **One matrix entry per step.** Over a duplicate-free list of positions, a loop whose step at
`(i, j)` rewrites the entry `(i, j)` only — from its current value and from entries at positions
outside the list — has as run set the matrices that agree with the initial one off the list and
whose entry at each listed position is a result of its step on the initial matrix. The matrix form
of `SetM.mem_run_foldlM_update_of_nodup`. -/
theorem mem_run_foldlM_updateEntry {m n : ℕ} (l : List (Fin m × Fin n)) (hl : l.Nodup)
    (g : Fin m × Fin n → ℝ → Matrix (Fin m) (Fin n) ℝ → SetM ℝ)
    (hg : ∀ a ∈ l, ∀ x (A A' : Matrix (Fin m) (Fin n) ℝ),
      (∀ i j, (i, j) ∉ l → A i j = A' i j) → g a x A = g a x A')
    (A₀ A : Matrix (Fin m) (Fin n) ℝ) :
    A ∈ (l.foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) a => do
        let x ← g a (A a.1 a.2) A
        pure (A.updateRow a.1 (Function.update (A a.1) a.2 x))) A₀).run ↔
      (∀ i j, (i, j) ∉ l → A i j = A₀ i j) ∧ ∀ a ∈ l, A a.1 a.2 ∈ (g a (A₀ a.1 a.2) A₀).run := by
  let e := entryEquiv m n
  have he : ∀ (B : Matrix (Fin m) (Fin n) ℝ) p, e B p = B p.1 p.2 := fun _ _ => rfl
  have hmap := map_foldlM_equiv e (fun (A : Matrix (Fin m) (Fin n) ℝ) a => do
        let x ← g a (A a.1 a.2) A
        pure (A.updateRow a.1 (Function.update (A a.1) a.2 x)))
    (fun y a => do let x ← g a (y a) (e.symm y); pure (Function.update y a x))
    (fun B a => by
      simp only [map_bind, map_pure, Equiv.symm_apply_apply, he]
      congr 1
      funext x
      exact congrArg pure (entryEquiv_updateRow_update B a x).symm) l A₀
  have key := SetM.mem_run_foldlM_update_of_nodup (fun a x y => g a x (e.symm y)) l hl
    (fun a ha x y y' hy => hg a ha x _ _ fun i j hij => hy (i, j) hij) (e A₀) (e A)
  have hA : A ∈ (l.foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) a => do
        let x ← g a (A a.1 a.2) A
        pure (A.updateRow a.1 (Function.update (A a.1) a.2 x))) A₀).run ↔
      e A ∈ (e <$> l.foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) a => do
        let x ← g a (A a.1 a.2) A
        pure (A.updateRow a.1 (Function.update (A a.1) a.2 x))) A₀).run := by
    rw [SetM.mem_run_map]
    exact ⟨fun h => ⟨A, h, rfl⟩, fun ⟨B, hB, hBA⟩ => e.injective hBA ▸ hB⟩
  rw [hA, hmap, key]
  simp only [Equiv.symm_apply_apply, he]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun i j hij => h₁ (i, j) hij, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun p hp => h₁ p.1 p.2 hp, h₂⟩

end Loops

/-! ### Gauss transformations (§3.2.1–3.2.2) -/

section Gauss

variable {n : ℕ}

/-- (3.2.1): if `A = L U`, `L y = b` and `U x = y`, then `A x = b` — "the solution to the original
`A x = b` problem is then found by a two-step triangular solve process". -/
theorem equation_3_2_1 {A L U : Matrix (Fin n) (Fin n) ℝ} (hA : A = L * U) {b y x : Fin n → ℝ}
    (hy : L *ᵥ y = b) (hx : U *ᵥ x = y) : A *ᵥ x = b := by
  rw [hA, ← mulVec_mulVec, hx, hy]

/-- §3.2.1, the Gauss vector of `v` at `k`: `τ_i = v_i / v_k` for `i > k` and `τ_i = 0` for
`i ≤ k` (0-based). -/
noncomputable def gaussVector (v : Fin n → ℝ) (k : Fin n) : Fin n → ℝ :=
  fun i => if k < i then v i / v k else 0

/-- §3.2.1, (3.2.2): the matrix `M_k = I_n - τ e_kᵀ`. -/
noncomputable def gaussTransformation (τ : Fin n → ℝ) (k : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  1 - vecMulVec τ (Pi.single k 1)

/-- §3.2.1: "a matrix of the form `M_k = I_n - τ e_kᵀ ∈ ℝ^{n×n}` is a Gauss transformation if
the first `k` components of `τ ∈ ℝⁿ` are zero" (0-based: the components `≤ k`). The components below
are the *multipliers*, `τ` the *Gauss vector*. -/
def IsGaussTransformation (M : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : Prop :=
  ∃ τ : Fin n → ℝ, (∀ i, i ≤ k → τ i = 0) ∧ M = gaussTransformation τ k

/-- The entries of a Gauss transformation. -/
theorem gaussTransformation_apply (τ : Fin n → ℝ) (k i j : Fin n) :
    gaussTransformation τ k i j =
      (1 : Matrix (Fin n) (Fin n) ℝ) i j - if j = k then τ i else 0 := by
  simp [gaussTransformation, vecMulVec_apply, Pi.single_apply]

/-- §3.2.2: "`M_k C = (I_n - τ e_kᵀ) C = C - τ (e_kᵀ C) = C - τ C(k,:)` is an outer product update",
and when the first `k` components of `τ` vanish only the rows below `k` change. -/
theorem gaussTransformation_mul {r : ℕ} (τ : Fin n → ℝ) (k : Fin n)
    (C : Matrix (Fin n) (Fin r) ℝ) :
    gaussTransformation τ k * C = C - vecMulVec τ (C k) ∧
      ((∀ i, i ≤ k → τ i = 0) → ∀ i, i ≤ k → (gaussTransformation τ k * C) i = C i) := by
  have h : gaussTransformation τ k * C = C - vecMulVec τ (C k) := by
    ext i j
    simp [gaussTransformation, mul_apply, vecMulVec_apply, Pi.single_apply, sub_mul,
      Finset.sum_sub_distrib, one_apply, ite_mul]
  refine ⟨h, fun hτ i hi => ?_⟩
  rw [h]
  ext j
  simp [vecMulVec_apply, hτ i hi]

/-- A Gauss transformation applied to a vector: `(I - τ e_kᵀ) v = v - v_k τ`. -/
theorem gaussTransformation_mulVec (τ : Fin n → ℝ) (k : Fin n) (v : Fin n → ℝ) :
    gaussTransformation τ k *ᵥ v = fun i => v i - τ i * v k := by
  ext i
  simp [gaussTransformation, mulVec, dotProduct, vecMulVec_apply, Pi.single_apply, sub_mul,
    Finset.sum_sub_distrib, one_apply, ite_mul]

/-- §3.2.1, the display after (3.2.2): if `v_k ≠ 0`, the Gauss transformation of the Gauss vector
of `v` zeroes the components of `v` below `k` and keeps the others. -/
theorem gaussTransformation_gaussVector_mulVec {v : Fin n → ℝ} {k : Fin n} (hv : v k ≠ 0) :
    gaussTransformation (gaussVector v k) k *ᵥ v = fun i => if i ≤ k then v i else 0 := by
  ext i
  rw [gaussTransformation_mulVec]
  by_cases hik : i ≤ k
  · simp [gaussVector, not_lt.2 hik, hik]
  · have hki : k < i := not_le.1 hik
    simp [gaussVector, hki, hik, div_mul_cancel₀ _ hv]

/-- §3.2.1: "such a matrix is unit lower triangular". -/
theorem isUnitLowerTriangular_gaussTransformation {M : Matrix (Fin n) (Fin n) ℝ} {k : Fin n}
    (hM : IsGaussTransformation M k) : M.IsUnitLowerTriangular := by
  obtain ⟨τ, hτ, rfl⟩ := hM
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    rw [gaussTransformation_apply, one_apply_ne hij'.ne]
    split_ifs with hjk
    · rw [hτ i (hjk ▸ hij'.le), sub_zero]
    · rw [sub_zero]
  · rw [gaussTransformation_apply, one_apply_eq]
    split_ifs with hik
    · rw [hτ i hik.le, sub_zero]
    · rw [sub_zero]

/-- §3.2.5: "if `M_k = I_n - τ e_kᵀ` then its inverse is prescribed by `M_k⁻¹ = I_n + τ e_kᵀ`":
when `τ_k = 0`, `(I - τ e_kᵀ)(I + τ e_kᵀ) = I`, since `(τ e_kᵀ)² = τ (e_kᵀ τ) e_kᵀ = 0`. -/
theorem gaussTransformation_inv {τ : Fin n → ℝ} {k : Fin n} (hτ : τ k = 0) :
    gaussTransformation τ k * gaussTransformation (-τ) k = 1 ∧
      (gaussTransformation τ k)⁻¹ = gaussTransformation (-τ) k := by
  have h : gaussTransformation τ k * gaussTransformation (-τ) k = 1 := by
    rw [(gaussTransformation_mul τ k _).1]
    ext i j
    by_cases hij : i = j <;> by_cases hjk : j = k <;>
      simp [gaussTransformation, vecMulVec_apply, one_apply, hτ, hij, hjk, eq_comm (a := k)]
  exact ⟨h, inv_eq_right_inv h⟩

/-- **The book's `M_k` built from column `k` of `M` is the backbone's Gaussian transformation**
`Matrix.gaussTransform M k`, which performs one elimination step: `M_k M = Matrix.elimStep M k`
(`Matrix.gaussTransform_mul`). The bridge through which (3.2.3)–(3.2.7) are backbone statements. -/
theorem gaussTransformation_gaussVector_eq_gaussTransform (M : Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n) :
    gaussTransformation (gaussVector (fun i => M i k) k) k = gaussTransform M k := by
  ext i j
  simp only [gaussTransformation_apply, gaussTransform, elimMultipliers, Matrix.sub_apply,
    of_apply, gaussVector]
  by_cases hj : j = k
  · subst hj
    by_cases hi : j < i <;> simp [hi, div_eq_mul_inv]
  · simp [hj]

end Gauss

/-! ### Rounding a Gauss transformation (§3.2.3) -/

section GaussUpdate

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- §3.2.2–3.2.3, applying a computed Gauss transformation: from the pivot column `v` the computed
Gauss vector `τ̂_i = fl(v_i / v_k)`, `i > k`, then the update "row by row":
```
for i = k+1:n
    C(i,:) = C(i,:) - τ_i · C(k,:)
end
```
entrywise `c_ij = fl(c_ij - fl(τ̂_i c_kj))`. Returns `(τ̂, fl((I - τ̂ e_kᵀ) C))`. -/
noncomputable def gaussUpdate {n r : ℕ} (v : Fin n → ℝ) (k : Fin n)
    (C : Matrix (Fin n) (Fin r) ℝ) : M ((Fin n → ℝ) × Matrix (Fin n) (Fin r) ℝ) := do
  let τ ← ((List.finRange n).filter (k < ·)).foldlM (fun (τ : Fin n → ℝ) i => do
    let t ← rnd (v i / v k)
    pure (Function.update τ i t)) 0
  let C ← ((List.finRange n).filter (k < ·)).foldlM (fun (C : Matrix (Fin n) (Fin r) ℝ) i =>
    (List.finRange r).foldlM (fun (C : Matrix (Fin n) (Fin r) ℝ) j => do
      let p ← rnd (τ i * C k j)
      let c ← rnd (C i j - p)
      pure (C.updateRow i (Function.update (C i) j c))) C) C
  pure (τ, C)

variable {fp : RoundingModel ℝ} {n r : ℕ}

/-- The run set of `gaussUpdate`, entry by entry: the computed Gauss vector rounds `v_i / v_k`
below `k` and vanishes elsewhere; every entry below row `k` is `fl(c_ij - fl(τ̂_i c_kj))`, and the
rows up to `k` are unchanged. -/
theorem mem_run_gaussUpdate {v : Fin n → ℝ} {k : Fin n} {C : Matrix (Fin n) (Fin r) ℝ}
    {out : (Fin n → ℝ) × Matrix (Fin n) (Fin r) ℝ} (h : out ∈ (gaussUpdate fp.round v k C).run) :
    (∀ i, ¬ k < i → out.1 i = 0) ∧ (∀ i, k < i → fp.Rounds (v i / v k) (out.1 i)) ∧
      (∀ i j, ¬ k < i → out.2 i j = C i j) ∧
      ∀ i j, k < i → ∃ p, fp.Rounds (out.1 i * C k j) p ∧ fp.Rounds (C i j - p) (out.2 i j) := by
  simp only [gaussUpdate, SetM.mem_run_bind, SetM.mem_run_pure] at h
  obtain ⟨τ, hτ, C', hC', rfl⟩ := h
  dsimp only
  have hnd : ((List.finRange n).filter (k < ·)).Nodup := (List.nodup_finRange n).filter _
  have hmem : ∀ i, i ∈ (List.finRange n).filter (k < ·) ↔ k < i := fun i => by simp
  obtain ⟨hτ₁, hτ₂⟩ := (SetM.mem_run_foldlM_update_of_nodup
    (fun a _ (_ : Fin n → ℝ) => fp.round (v a / v k)) _ hnd (fun _ _ _ _ _ _ => rfl) 0 τ).1 hτ
  have hflat := foldlM_foldlM_eq_foldlM_flatMap ((List.finRange n).filter (k < ·))
    (fun _ => List.finRange r) (fun (C : Matrix (Fin n) (Fin r) ℝ) i j => (do
      let p ← fp.round (τ i * C k j)
      let c ← fp.round (C i j - p)
      pure (C.updateRow i (Function.update (C i) j c)) : SetM _)) C
  beta_reduce at hflat
  rw [hflat] at hC'
  have hl : ((((List.finRange n).filter (k < ·)).flatMap fun a =>
      (List.finRange r).map (a, ·))).Nodup :=
    List.nodup_flatMap.2 ⟨fun a _ => (List.nodup_finRange r).map fun _ _ h => (Prod.mk.inj h).2,
      hnd.imp fun {a b} hab => List.disjoint_left.2 fun {x} hxa hxb => by
        obtain ⟨_, _, rfl⟩ := List.mem_map.1 hxa
        obtain ⟨_, _, h⟩ := List.mem_map.1 hxb
        exact hab (Prod.mk.inj h).1.symm⟩
  have hlmem : ∀ i j, (i, j) ∈ (((List.finRange n).filter (k < ·)).flatMap fun a =>
      (List.finRange r).map (a, ·)) ↔ k < i := fun i j => by simp
  have key := mem_run_foldlM_updateEntry _ hl
    (fun a x (C : Matrix (Fin n) (Fin r) ℝ) => fp.round (τ a.1 * C k a.2) >>= fun p =>
      fp.round (x - p))
    (fun a _ x A A' hA => by
      rw [hA k a.2 fun h => lt_irrefl k ((hlmem k a.2).1 h)]) C C'
  simp only [bind_assoc] at key
  obtain ⟨hC₁, hC₂⟩ := key.1 hC'
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i j hi => ?_, fun i j hi => ?_⟩
  · rw [hτ₁ i fun h => hi ((hmem i).1 h)]
    rfl
  · exact hτ₂ i ((hmem i).2 hi)
  · exact hC₁ i j fun h => hi ((hlmem i j).1 h)
  · obtain ⟨p, hp, hc⟩ := SetM.mem_run_bind.1 (hC₂ (i, j) ((hlmem i j).2 hi))
    exact ⟨p, hp, hc⟩

/-- §3.2.3, "`τ̂ = τ + e`, `|e| ≤ u |τ|`": the computed Gauss vector of every run is within `u` of
the exact one, componentwise (one rounded division; exact, with no `O(u²)`). -/
theorem gaussVector_rounding (v : Fin n → ℝ) (k : Fin n) (C : Matrix (Fin n) (Fin r) ℝ) :
    ∀ out ∈ (gaussUpdate fp.round v k C).run,
      ∀ i, |out.1 i - gaussVector v k i| ≤ fp.u * |gaussVector v k i| := by
  intro out hout i
  obtain ⟨h₁, h₂, -, -⟩ := mem_run_gaussUpdate hout
  by_cases hi : k < i
  · simp only [gaussVector, hi, ↓reduceIte]
    exact fp.abs_sub_le (h₂ i hi)
  · simp [gaussVector, hi, h₁ i hi]

/-- `|(1 + δ₀)(1 + δ₁)(1 + δ₂) - 1| ≤ γ₃` for three relative errors bounded by `u`. -/
private theorem abs_three_mul_sub_one_le {u δ₀ δ₁ δ₂ : ℝ} (hu : 0 ≤ u) (h3 : 3 * u < 1)
    (h₀ : |δ₀| ≤ u) (h₁ : |δ₁| ≤ u) (h₂ : |δ₂| ≤ u) :
    |(1 + δ₀) * (1 + δ₁) * (1 + δ₂) - 1| ≤ gamma u 3 := by
  have h := abs_prod_one_add_sub_one_le_gamma (n := 3) hu (by norm_num; linarith)
    (δ := ![δ₀, δ₁, δ₂]) (fun i => by fin_cases i <;> simpa) (ρ := fun _ => 1)
    (fun _ => Or.inl rfl)
  simpa [Fin.prod_univ_three] using h

/-- **§3.2.3, rounding of a Gauss transform update**, rigorous form: every run of
`gaussUpdate fp.round v k C` returns `fl((I - τ̂ e_kᵀ) C) = (I - τ e_kᵀ) C + E` with `τ` the exact
Gauss vector and `|E| ≤ u |C| + γ₃ |τ| |C(k,:)|` entrywise, `E` vanishing in the rows up to `k`.
Entry `(i, j)` below row `k` is `(c_ij - τ_i (1 + δ₀) c_kj (1 + δ₁))(1 + δ₂)`, so
`E_ij = δ₂ c_ij - τ_i c_kj ((1 + δ₀)(1 + δ₁)(1 + δ₂) - 1)`. The book's
`|E| ≤ 3u (|C| + |τ| |C(k,:)|) + O(u²)` follows (`u ≤ 3u`, `γ₃ = 3u + O(u²)`). -/
theorem gaussUpdate_rounding (h3 : 3 * fp.u < 1) (v : Fin n → ℝ) (k : Fin n)
    (C : Matrix (Fin n) (Fin r) ℝ) :
    ∀ out ∈ (gaussUpdate fp.round v k C).run, ∃ E : Matrix (Fin n) (Fin r) ℝ,
      out.2 = gaussTransformation (gaussVector v k) k * C + E ∧
      (∀ i j, |E i j| ≤ fp.u * |C i j| + gamma fp.u 3 * (|gaussVector v k i| * |C k j|)) ∧
      ∀ i j, i ≤ k → E i j = 0 := by
  intro out hout
  obtain ⟨-, h₂, h₃, h₄⟩ := mem_run_gaussUpdate hout
  have hmul := (gaussTransformation_mul (gaussVector v k) k C).1
  have hτk : ∀ i, ¬ k < i → gaussVector v k i = 0 := fun i hi => by simp [gaussVector, hi]
  refine ⟨out.2 - gaussTransformation (gaussVector v k) k * C, by abel, fun i j => ?_,
    fun i j hi => ?_⟩
  · rw [hmul, Matrix.sub_apply, Matrix.sub_apply, vecMulVec_apply]
    by_cases hi : k < i
    · obtain ⟨p, hp, hc⟩ := h₄ i j hi
      obtain ⟨δ₀, hδ₀, ht⟩ := (h₂ i hi).exists_delta
      obtain ⟨δ₁, hδ₁, hp'⟩ := hp.exists_delta
      obtain ⟨δ₂, hδ₂, hc'⟩ := hc.exists_delta
      have hγ := abs_three_mul_sub_one_le fp.u_nonneg h3 hδ₀ hδ₁ hδ₂
      have hτi : gaussVector v k i = v i / v k := by simp [gaussVector, hi]
      have heq : out.2 i j - (C i j - gaussVector v k i * C k j) =
          C i j * δ₂ - gaussVector v k i * C k j * ((1 + δ₀) * (1 + δ₁) * (1 + δ₂) - 1) := by
        rw [hc', hp', ht, hτi]
        ring
      rw [heq]
      calc |C i j * δ₂ - gaussVector v k i * C k j * ((1 + δ₀) * (1 + δ₁) * (1 + δ₂) - 1)|
          ≤ |C i j * δ₂| + |gaussVector v k i * C k j *
              ((1 + δ₀) * (1 + δ₁) * (1 + δ₂) - 1)| := abs_sub _ _
        _ ≤ fp.u * |C i j| + gamma fp.u 3 * (|gaussVector v k i| * |C k j|) := by
            have e1 : |C i j| * |δ₂| ≤ fp.u * |C i j| := by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_right hδ₂ (abs_nonneg _)
            have e2 : |gaussVector v k i| * |C k j| * |(1 + δ₀) * (1 + δ₁) * (1 + δ₂) - 1| ≤
                gamma fp.u 3 * (|gaussVector v k i| * |C k j|) := by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_right hγ (by positivity)
            rw [abs_mul, abs_mul, abs_mul]
            exact add_le_add e1 e2
    · rw [h₃ i j hi, hτk i hi]
      have : 0 ≤ fp.u * |C i j| + gamma fp.u 3 * (|(0 : ℝ)| * |C k j|) := by
        rw [abs_zero, zero_mul, mul_zero, add_zero]
        exact mul_nonneg fp.u_nonneg (abs_nonneg _)
      simpa using this
  · rw [Matrix.sub_apply, h₃ i j (not_lt.2 hi), (gaussTransformation_mul (gaussVector v k) k C).2
      (fun i hi => hτk i (not_lt.2 hi)) i hi, sub_self]

end GaussUpdate

/-! ### Gaussian elimination as a factorization (§3.2.4–3.2.6) -/

section Elimination

variable {n : ℕ}

/-- (3.2.3), the matrices of Gaussian elimination: the book's `A^{(k+1)} = M_k A^{(k)}` (1-based,
`A^{(1)} = A`) is the stage after `k` steps, `gaussStage A k = Matrix.gemStage A k` (0-based). -/
noncomputable abbrev gaussStage (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  gemStage A k

/-- **(3.2.3)**, the step of Gaussian elimination: "for `i = k+1:n`, determine the multipliers
`τ_i^{(k)} = a_ik^{(k)} / a_kk^{(k)}`; apply `M_k = I - τ^{(k)} e_kᵀ` to obtain
`A^{(k+1)} = M_k A^{(k)}`". -/
theorem equation_3_2_3 (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    gaussStage A (k + 1) =
      gaussTransformation (gaussVector (fun i => gaussStage A k i k) k) k * gaussStage A k := by
  rw [gaussTransformation_gaussVector_eq_gaussTransform]
  exact gemStage_succ_eq_gaussTransform_mul A k.2

/-- §3.2.4, "these quantities are called pivots": the pivot `a_kk^{(k)}` of the `k`-th step
(0-based), the diagonal entry of the stage after `k` steps. -/
noncomputable def pivot (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : ℝ :=
  gaussStage A k k k

/-- The book's pivot hypothesis in the backbone's form. -/
theorem pivot_ne_zero_iff (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ k : Fin n, (k : ℕ) + 1 < n → pivot A k ≠ 0) ↔
      ∀ (m : ℕ) (hm : m < n), m + 1 < n → gemStage A m ⟨m, hm⟩ ⟨m, hm⟩ ≠ 0 :=
  ⟨fun h m hm hmn => h ⟨m, hm⟩ hmn, fun h k hk => h k k.2 hk⟩

/-- **(3.2.4)–(3.2.5)**, §3.2.5: "if no zero pivots are encountered in (3.2.3), then Gauss
transformations `M_1, …, M_{n-1}` are generated such that `M_{n-1} ⋯ M_1 A = U` is upper
triangular", and `A = L U` with `L = M_1⁻¹ ⋯ M_{n-1}⁻¹` unit lower triangular — the backbone's
multiplier matrix `Matrix.gemLower A`. The last pivot divides nothing and may vanish. -/
theorem equation_3_2_4 {A : Matrix (Fin n) (Fin n) ℝ}
    (hpiv : ∀ k : Fin n, (k : ℕ) + 1 < n → pivot A k ≠ 0) :
    IsLU A (gemLower A) (gaussStage A n) :=
  isLU_gemLower_gemStage A ((pivot_ne_zero_iff A).1 hpiv)

/-- The inverse of the book's `M_k` is the backbone's unipotent factor `Matrix.elimMul`. -/
theorem inv_gaussTransformation_gaussVector (M : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    (gaussTransformation (gaussVector (fun i => M i k) k) k)⁻¹ = elimMul M k := by
  rw [gaussTransformation_gaussVector_eq_gaussTransform]
  exact inv_eq_left_inv (elimMul_mul_gaussTransform M k)

/-- **(3.2.5)** with §3.2.6: `L = M_1⁻¹ ⋯ M_{n-1}⁻¹ = I_n + ∑_k τ^{(k)} e_kᵀ` is the matrix of
multipliers `Matrix.gemLower A` — the ordered product of the inverse Gauss transformations of the
stages, with no pivot hypothesis. -/
theorem equation_3_2_5 (A : Matrix (Fin n) (Fin n) ℝ) :
    ((List.finRange n).map fun k : Fin n =>
      (gaussTransformation (gaussVector (fun i => gaussStage A k i k) k) k)⁻¹).prod =
      gemLower A := by
  let F : ℕ → Matrix (Fin n) (Fin n) ℝ := fun k =>
    if h : k < n then elimMul (gemStage A k) ⟨k, h⟩ else 1
  have hmap : ((List.finRange n).map fun k : Fin n =>
      (gaussTransformation (gaussVector (fun i => gaussStage A k i k) k) k)⁻¹) =
      (List.range n).map F := by
    rw [← List.map_coe_finRange_eq_range, List.map_map]
    refine List.map_congr_left fun k _ => ?_
    simp only [Function.comp_apply, F, k.2, ↓reduceDIte]
    exact inv_gaussTransformation_gaussVector _ k
  have key : ∀ k ≤ n, ((List.range k).map F).prod = gemLowerStage A k := by
    intro k hk
    induction k with
    | zero => simp [gemLowerStage_zero]
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih (by omega), List.map_singleton,
        List.prod_singleton, gemLowerStage_succ A (by omega)]
      simp only [F, show k < n by omega, ↓reduceDIte]
  rw [hmap, key n le_rfl, gemLowerStage_of_le A le_rfl]

/-- **Theorem 3.2.1 (LU Factorization), existence**: "if `A ∈ ℝ^{n×n}` and
`det(A(1:k,1:k)) ≠ 0` for `k = 1:n-1`, then there exists a unit lower triangular `L ∈ ℝ^{n×n}` and
an upper triangular `U ∈ ℝ^{n×n}` such that `A = LU`". -/
theorem theorem_3_2_1 {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ k : Fin n, (A.strictLeadingPrincipalSubmatrix k).det ≠ 0) :
    ∃ L U, IsLU A L U :=
  exists_isLU_of_forall_isUnit_strictLeadingPrincipalSubmatrix fun k =>
    (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hA k))

/-- **Theorem 3.2.1, uniqueness**: "if this is the case and `A` is nonsingular, then the
factorization is unique". The leading-minor hypothesis alone suffices (`Matrix.IsLU.unique`); the
book's nonsingularity of `A` is carried for faithfulness. -/
theorem theorem_3_2_1_unique {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ k : Fin n, (A.strictLeadingPrincipalSubmatrix k).det ≠ 0) (_hdet : A.det ≠ 0)
    {L₁ U₁ L₂ U₂ : Matrix (Fin n) (Fin n) ℝ} (h₁ : IsLU A L₁ U₁) (h₂ : IsLU A L₂ U₂) :
    L₁ = L₂ ∧ U₁ = U₂ :=
  h₁.unique h₂ fun k => (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hA k))

/-- **Theorem 3.2.1, determinant**: "if `A = LU`, then `det(A) = u₁₁ ⋯ u_nn`". -/
theorem theorem_3_2_1_det {A L U : Matrix (Fin n) (Fin n) ℝ} (h : IsLU A L U) :
    A.det = ∏ i, U i i :=
  h.det_eq_prod_diag

/-- **(3.2.6)**: if the pivots of the first `k` steps are nonzero, the leading principal minor of
order `k + 1` is the product of the leading diagonal entries of the stage after `k` steps,
`det(A(1:k+1,1:k+1)) = a_11^{(k)} ⋯ a_{k+1,k+1}^{(k)}` (0-based). -/
theorem equation_3_2_6 {A : Matrix (Fin n) (Fin n) ℝ} {k : Fin n}
    (hpiv : ∀ m : Fin n, m < k → pivot A m ≠ 0) :
    (A.leadingPrincipalSubmatrix k).det = ∏ i : {i // i ≤ k}, gaussStage A k i i := by
  have h := isLU_leadingPrincipalSubmatrix_gemStage A k.2
    fun m hm hmk _ => hpiv ⟨m, hm⟩ (Fin.lt_def.2 hmk)
  simp only [Fin.eta] at h
  convert h.det_eq_prod_diag using 2
  all_goals rfl

/-- **(3.2.7)**, "the `k`-th column of `L` is defined by the multipliers that arise in the `k`-th
step of (3.2.3)": `L(k+1:n, k) = τ^{(k)}(k+1:n)`. -/
theorem equation_3_2_7 (A : Matrix (Fin n) (Fin n) ℝ) {i k : Fin n} (hki : k < i) :
    gemLower A i k = gaussVector (fun i => gaussStage A k i k) k i := by
  simp [gemLower, gaussVector, hki]

end Elimination

/-! ### The packed factors -/

section Packed

variable {n : ℕ}

/-- The unit lower factor stored below the diagonal of a packed matrix (§3.2.8: "`A(i+1:n, i)` is
overwritten by `L(i+1:n, i)`"): `packedL F = I + strictLower F`. -/
def packedL (F : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := 1 + F.strictLower

/-- The upper factor stored on and above the diagonal of a packed matrix ("`A(i, i:n)` is
overwritten by `U(i, i:n)`"): `packedU F = F - strictLower F`. -/
def packedU (F : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := F - F.strictLower

variable (F : Matrix (Fin n) (Fin n) ℝ)

theorem packedL_apply_of_lt {i j : Fin n} (h : j < i) : packedL F i j = F i j := by
  simp [packedL, h, h.ne']

theorem packedL_apply_self (i : Fin n) : packedL F i i = 1 := by
  simp [packedL]

theorem packedL_apply_of_lt' {i j : Fin n} (h : i < j) : packedL F i j = 0 := by
  simp [packedL, h.ne, not_lt.2 h.le]

theorem packedU_apply_of_le {i j : Fin n} (h : i ≤ j) : packedU F i j = F i j := by
  simp [packedU, not_lt.2 h]

theorem packedU_apply_of_lt {i j : Fin n} (h : j < i) : packedU F i j = 0 := by
  simp [packedU, h]

end Packed

/-! ### Algorithm 3.2.1 (Outer Product LU) -/

section Algorithm321

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One step `k` of the outer product LU (the body of Algorithm 3.2.1, shared with the pivoting
Algorithms 3.4.1 and 3.4.3): with `ρ = k+1:n`, `A(ρ,k) = A(ρ,k)/A(k,k)` entry by entry, then the
outer product update `A(ρ,ρ) = A(ρ,ρ) - A(ρ,k) · A(k,ρ)` row by row, every quotient, product and
difference rounded. -/
noncomputable def outerProductStep {n : ℕ} (k : Fin n) (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) := do
  let A ← ((List.finRange n).filter (k < ·)).foldlM (fun (A : Matrix (Fin n) (Fin n) ℝ) i => do
    let l ← rnd (A i k / A k k)
    pure (A.updateRow i (Function.update (A i) k l))) A
  ((List.finRange n).filter (k < ·)).foldlM (fun (A : Matrix (Fin n) (Fin n) ℝ) i =>
    ((List.finRange n).filter (k < ·)).foldlM (fun (A : Matrix (Fin n) (Fin n) ℝ) j => do
      let p ← rnd (A i k * A k j)
      let a ← rnd (A i j - p)
      pure (A.updateRow i (Function.update (A i) j a))) A) A

/-- **Algorithm 3.2.1 (Outer Product LU).** "Suppose `A ∈ ℝ^{n×n}` has the property that
`A(1:k,1:k)` is nonsingular for `k = 1:n-1`. This algorithm computes the factorization `A = LU`
where `L` is unit lower triangular and `U` is upper triangular. For `i = 1:n-1`, `A(i,i:n)` is
overwritten by `U(i,i:n)` while `A(i+1:n,i)` is overwritten by `L(i+1:n,i)`."
```
for k = 1:n-1
    ρ = k+1:n
    A(ρ,k) = A(ρ,k)/A(k,k)
    A(ρ,ρ) = A(ρ,ρ) - A(ρ,k)·A(k,ρ)
end
```
The outer product update is carried out row by row (the `kij` form of §3.2.9); every quotient,
product and difference is rounded. The last step `k = n` is empty. -/
noncomputable def algorithm_3_2_1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun A k => outerProductStep rnd k A) A

variable {fp : RoundingModel ℝ} {n : ℕ}

/-- **The run set of one step `k` of the outer product LU**: the multipliers of column `k` below
the pivot are rounded quotients, the trailing block receives one rounded update from the new
multipliers and the pivot row, and every other entry is unchanged. -/
theorem mem_run_outerProductStep (k : Fin n) {S S' : Matrix (Fin n) (Fin n) ℝ}
    (h : S' ∈ (outerProductStep fp.round k S).run) :
    (∀ i j, ¬ (k < i ∧ (j = k ∨ k < j)) → S' i j = S i j) ∧
      (∀ i, k < i → fp.Rounds (S i k / S k k) (S' i k)) ∧
      ∀ i j, k < i → k < j →
        ∃ p, fp.Rounds (S' i k * S' k j) p ∧ fp.Rounds (S i j - p) (S' i j) := by
  rw [outerProductStep, SetM.mem_run_bind] at h
  obtain ⟨S₁, h₁, h₂⟩ := h
  have hnd : ((List.finRange n).filter (k < ·)).Nodup := (List.nodup_finRange n).filter _
  have hmem : ∀ i, i ∈ (List.finRange n).filter (k < ·) ↔ k < i := fun i => by simp
  -- the division loop
  have hdiv : ((List.finRange n).filter (k < ·)).foldlM
      (fun (A : Matrix (Fin n) (Fin n) ℝ) i => do
        let l ← fp.round (A i k / A k k)
        pure (A.updateRow i (Function.update (A i) k l))) S =
      (((List.finRange n).filter (k < ·)).map (·, k)).foldlM
        (fun (A : Matrix (Fin n) (Fin n) ℝ) a => do
          let x ← (fun (_ : Fin n × Fin n) x (A : Matrix (Fin n) (Fin n) ℝ) =>
            fp.round (x / A k k)) a (A a.1 a.2) A
          pure (A.updateRow a.1 (Function.update (A a.1) a.2 x))) S := by
    rw [List.foldlM_map]
  have hl₁ : (((List.finRange n).filter (k < ·)).map (·, k)).Nodup :=
    hnd.map fun _ _ h => (Prod.mk.inj h).1
  have hl₁mem : ∀ i j, (i, j) ∈ ((List.finRange n).filter (k < ·)).map (·, k) ↔
      k < i ∧ j = k := fun i j => by
    simp only [List.mem_map, hmem, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha, rfl, rfl⟩; exact ⟨ha, rfl⟩
    · rintro ⟨hi, rfl⟩; exact ⟨i, hi, rfl, rfl⟩
  rw [hdiv] at h₁
  obtain ⟨hS₁, hS₁'⟩ := (mem_run_foldlM_updateEntry _ hl₁
    (fun _ x (A : Matrix (Fin n) (Fin n) ℝ) => fp.round (x / A k k))
    (fun a _ x A A' hA => by
      rw [hA k k fun h => lt_irrefl k ((hl₁mem k k).1 h).1]) S S₁).1 h₁
  -- the update loop
  have hflat := foldlM_foldlM_eq_foldlM_flatMap ((List.finRange n).filter (k < ·))
    (fun _ => (List.finRange n).filter (k < ·)) (fun (A : Matrix (Fin n) (Fin n) ℝ) i j => (do
      let p ← fp.round (A i k * A k j)
      let a ← fp.round (A i j - p)
      pure (A.updateRow i (Function.update (A i) j a)) : SetM _)) S₁
  beta_reduce at hflat
  rw [hflat] at h₂
  have hl₂ : ((((List.finRange n).filter (k < ·)).flatMap fun a =>
      ((List.finRange n).filter (k < ·)).map (a, ·))).Nodup :=
    List.nodup_flatMap.2 ⟨fun a _ => hnd.map fun _ _ h => (Prod.mk.inj h).2,
      hnd.imp fun {a b} hab => List.disjoint_left.2 fun {x} hxa hxb => by
        obtain ⟨_, _, rfl⟩ := List.mem_map.1 hxa
        obtain ⟨_, _, h⟩ := List.mem_map.1 hxb
        exact hab (Prod.mk.inj h).1.symm⟩
  have hl₂mem : ∀ i j, (i, j) ∈ (((List.finRange n).filter (k < ·)).flatMap fun a =>
      ((List.finRange n).filter (k < ·)).map (a, ·)) ↔ k < i ∧ k < j := fun i j => by
    simp only [List.mem_flatMap, List.mem_map, hmem, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha, b, hb, rfl, rfl⟩; exact ⟨ha, hb⟩
    · rintro ⟨hi, hj⟩; exact ⟨i, hi, j, hj, rfl, rfl⟩
  have key := mem_run_foldlM_updateEntry _ hl₂
    (fun a x (A : Matrix (Fin n) (Fin n) ℝ) => fp.round (A a.1 k * A k a.2) >>= fun p =>
      fp.round (x - p))
    (fun a _ x A A' hA => by
      rw [hA a.1 k fun h => lt_irrefl k ((hl₂mem a.1 k).1 h).2,
        hA k a.2 fun h => lt_irrefl k ((hl₂mem k a.2).1 h).1]) S₁ S'
  simp only [bind_assoc] at key
  obtain ⟨hS', hS''⟩ := key.1 h₂
  have hS'k : ∀ i, S' i k = S₁ i k := fun i => hS' i k fun h => lt_irrefl k ((hl₂mem i k).1 h).2
  have hS'r : ∀ j, S' k j = S₁ k j := fun j => hS' k j fun h => lt_irrefl k ((hl₂mem k j).1 h).1
  refine ⟨fun i j hij => ?_, fun i hi => ?_, fun i j hi hj => ?_⟩
  · rw [hS' i j fun h => hij ⟨((hl₂mem i j).1 h).1, Or.inr ((hl₂mem i j).1 h).2⟩,
      hS₁ i j fun h => hij ⟨((hl₁mem i j).1 h).1, Or.inl ((hl₁mem i j).1 h).2⟩]
  · rw [hS'k]
    exact hS₁' (i, k) ((hl₁mem i k).2 ⟨hi, rfl⟩)
  · obtain ⟨p, hp, hc⟩ := SetM.mem_run_bind.1 (hS'' (i, j) ((hl₂mem i j).2 ⟨hi, hj⟩))
    refine ⟨p, by rw [hS'k, hS'r]; exact hp, ?_⟩
    rw [← hS₁ i j fun h => hj.ne' ((hl₁mem i j).1 h).2]
    exact hc

/-- An entry on or above the diagonal, finished: a running difference over `r < i`. -/
def LUUpperEntry (fp : RoundingModel ℝ) (A S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : Prop :=
  ∃ (o : List (Fin n)) (p : Fin n → ℝ), o.Nodup ∧ (∀ r, r ∈ o ↔ r < i) ∧
    (∀ r ∈ o, fp.Rounds (S i r * S r j) (p r)) ∧
    RoundsSumFrom fp (A i j) (o.map fun r => -p r) (S i j)

/-- An entry below the diagonal, finished: a running difference over `r < j`, then divided. -/
def LULowerEntry (fp : RoundingModel ℝ) (A S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : Prop :=
  ∃ (o : List (Fin n)) (p : Fin n → ℝ) (t : ℝ), o.Nodup ∧ (∀ r, r ∈ o ↔ r < j) ∧
    (∀ r ∈ o, fp.Rounds (S i r * S r j) (p r)) ∧
    RoundsSumFrom fp (A i j) (o.map fun r => -p r) t ∧ fp.Rounds (t / S j j) (S i j)

/-- An entry of the trailing block after `k` steps: a running difference over `r < k`. -/
def LUTrailingEntry (fp : RoundingModel ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : Prop :=
  ∃ (o : List (Fin n)) (p : Fin n → ℝ), o.Nodup ∧ (∀ r : Fin n, r ∈ o ↔ (r : ℕ) < k) ∧
    (∀ r ∈ o, fp.Rounds (S i r * S r j) (p r)) ∧
    RoundsSumFrom fp (A i j) (o.map fun r => -p r) (S i j)

/-- The invariant of Algorithm 3.2.1 after `k` steps: rows and columns before `k` finished, the
trailing block holding running differences over `r < k`. -/
def LUStageInv (fp : RoundingModel ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, ((i : ℕ) < k → i ≤ j → LUUpperEntry fp A S i j) ∧
    ((j : ℕ) < k → j < i → LULowerEntry fp A S i j) ∧
    (k ≤ (i : ℕ) → k ≤ (j : ℕ) → LUTrailingEntry fp A k S i j)

/-- One step of Algorithm 3.2.1 keeps the invariant. -/
theorem luStageInv_step (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n)
    {S S' : Matrix (Fin n) (Fin n) ℝ} (hS : LUStageInv fp A k S)
    (hunch : ∀ i j, ¬ (k < i ∧ (j = k ∨ k < j)) → S' i j = S i j)
    (hdiv : ∀ i, k < i → fp.Rounds (S i k / S k k) (S' i k))
    (hupd : ∀ i j, k < i → k < j →
      ∃ p, fp.Rounds (S' i k * S' k j) p ∧ fp.Rounds (S i j - p) (S' i j)) :
    LUStageInv fp A (k + 1) S' := by
  -- entries in the rows up to `k`, and in the columns before `k`, are unchanged
  have hrow : ∀ i j : Fin n, (i : ℕ) ≤ k → S' i j = S i j := fun i j hi =>
    hunch i j fun h => absurd (Fin.lt_def.1 h.1) (not_lt.2 hi)
  have hcol : ∀ i j : Fin n, (j : ℕ) < k → S' i j = S i j := fun i j hj =>
    hunch i j fun h => h.2.elim (fun h' => absurd (h' ▸ hj) (lt_irrefl _))
      fun h' => absurd (Fin.lt_def.1 h') (not_lt.2 hj.le)
  intro i j
  refine ⟨fun hi hij => ?_, fun hj hji => ?_, fun hi hj => ?_⟩
  · -- a finished entry of `U`
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hS i j).1 hi hij
      refine ⟨o, p, hnd, ho, fun r hr => ?_, ?_⟩
      · have hri := Fin.lt_def.1 ((ho r).1 hr)
        rw [hrow i r (by omega), hrow r j (by omega)]
        exact hp r hr
      · rw [hrow i j (by omega)]
        exact hsum
    · have hik : i = k := Fin.ext hi
      subst hik
      obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hS i j).2.2 le_rfl (Fin.le_def.1 hij)
      refine ⟨o, p, hnd, fun r => (ho r).trans Fin.lt_def.symm, fun r hr => ?_, ?_⟩
      · have hri := (ho r).1 hr
        rw [hrow i r le_rfl, hrow r j (by omega)]
        exact hp r hr
      · rw [hrow i j le_rfl]
        exact hsum
  · -- a finished entry of `L`
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · obtain ⟨o, p, t, hnd, ho, hp, hsum, hx⟩ := (hS i j).2.1 hj hji
      refine ⟨o, p, t, hnd, ho, fun r hr => ?_, hsum, ?_⟩
      · have hrj := Fin.lt_def.1 ((ho r).1 hr)
        rw [hcol i r (by omega), hcol r j hj]
        exact hp r hr
      · rw [hcol i j hj, hcol j j hj]
        exact hx
    · have hjk : j = k := Fin.ext hj
      subst hjk
      obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hS i j).2.2 (Fin.le_def.1 hji.le) le_rfl
      refine ⟨o, p, S i j, hnd, fun r => (ho r).trans Fin.lt_def.symm, fun r hr => ?_, hsum, ?_⟩
      · have hrj := (ho r).1 hr
        rw [hcol i r hrj, hrow r j hrj.le]
        exact hp r hr
      · rw [hrow j j le_rfl]
        exact hdiv i hji
  · -- the trailing block receives one more subtraction
    have hki : k < i := Fin.lt_def.2 (by omega)
    have hkj : k < j := Fin.lt_def.2 (by omega)
    obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hS i j).2.2 (by omega) (by omega)
    obtain ⟨q, hq, hq'⟩ := hupd i j hki hkj
    have hko : k ∉ o := fun h => lt_irrefl (k : ℕ) ((ho k).1 h)
    refine ⟨o ++ [k], Function.update p k q,
      hnd.append (List.nodup_singleton _) (List.disjoint_singleton.2 hko), fun r => ?_,
      fun r hr => ?_, ?_⟩
    · rw [List.mem_append, ho r, List.mem_singleton, Fin.ext_iff]
      omega
    · rcases List.mem_append.1 hr with hr | hr
      · have hrk := (ho r).1 hr
        rw [Function.update_of_ne (fun h => by subst h; exact lt_irrefl _ hrk), hcol i r hrk,
          hrow r j hrk.le]
        exact hp r hr
      · rw [List.mem_singleton.1 hr, Function.update_self]
        exact hq
    · rw [List.map_append, List.map_singleton, Function.update_self]
      have hmap : (o.map fun r => -Function.update p k q r) = o.map fun r => -p r := by
        refine List.map_congr_left fun r hr => ?_
        rw [Function.update_of_ne (fun h : r = k => hko (h ▸ hr))]
      rw [hmap, roundsSumFrom_append_singleton]
      exact ⟨S i j, hsum, by rw [← sub_eq_add_neg]; exact hq'⟩

/-- Before the first step the invariant holds: nothing is finished, and the trailing block is the
matrix itself. -/
theorem luStageInv_zero (A : Matrix (Fin n) (Fin n) ℝ) : LUStageInv fp A 0 A := fun _ _ =>
  ⟨fun h => absurd h (Nat.not_lt_zero _), fun h => absurd h (Nat.not_lt_zero _),
    fun _ _ => ⟨[], fun _ => 0, List.nodup_nil, fun r => by simp, by simp, .nil _⟩⟩

/-- **The finished invariant is a computed LU factorization**: after all `n` steps every entry is
finished, and the packed matrix read as `packedL`, `packedU` satisfies `FloatingPoint.RoundsLU`. -/
theorem roundsLU_of_luStageInv {A F : Matrix (Fin n) (Fin n) ℝ} (hinv : LUStageInv fp A n F) :
    RoundsLU fp A (packedL F) (packedU F) := by
  refine ⟨fun i j hij => packedL_apply_of_lt' F hij, packedL_apply_self F,
    fun i j hij => packedU_apply_of_lt F hij, fun i j hij => ?_, fun i j hij => ?_⟩
  · obtain ⟨o, p, hnd, ho, hp, hsum⟩ := (hinv i j).1 i.2 hij
    refine ⟨o, p, hnd, ho, fun r hr => ?_, ?_⟩
    · have hri := (ho r).1 hr
      rw [packedL_apply_of_lt F hri, packedU_apply_of_le F (hri.le.trans hij)]
      exact hp r hr
    · rw [packedU_apply_of_le F hij]
      exact hsum
  · obtain ⟨o, p, t, hnd, ho, hp, hsum, hx⟩ := (hinv i j).2.1 j.2 hij
    refine ⟨o, p, t, hnd, ho, fun r hr => ?_, hsum, ?_⟩
    · have hrj := (ho r).1 hr
      rw [packedL_apply_of_lt F (hrj.trans hij), packedU_apply_of_le F hrj.le]
      exact hp r hr
    · rw [packedL_apply_of_lt F hij, packedU_apply_of_le F le_rfl]
      exact hx

/-- **The bridge of Algorithm 3.2.1**: every run in the relational model returns packed factors
that are an admissible computed LU factorization, `FloatingPoint.RoundsLU fp A (packedL F)
(packedU F)`, with no hypothesis on `A` (a zero pivot gives junk quotients that `RoundsLU` allows
as well). Invariant after `k` steps: the rows and columns before `k` are finished entries of the
Doolittle recurrence, and the trailing block holds the running differences over `r < k`. -/
theorem algorithm_3_2_1_rounds (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ F ∈ (algorithm_3_2_1 fp.round A).run, RoundsLU fp A (packedL F) (packedU F) := by
  intro F hF
  have hinv := SetM.forall_mem_run_foldlM_finRange (LUStageInv fp A) (luStageInv_zero A)
    (fun k S hS S' hS' => by
      obtain ⟨h₁, h₂, h₃⟩ := mem_run_outerProductStep k hS'
      exact luStageInv_step A k hS h₁ h₂ h₃) F hF
  exact roundsLU_of_luStageInv hinv

/-- The exact run of Algorithm 3.2.1 is a run of the exact model. -/
private theorem algorithm_3_2_1_mem_exact (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_3_2_1 pure A) ∈ (algorithm_3_2_1 (RoundingModel.exact ℝ).round A).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_3_2_1, outerProductStep, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

/-- In exact arithmetic Algorithm 3.2.1 computes the Doolittle factors, for every `A`. -/
theorem algorithm_3_2_1_packed_eq (A : Matrix (Fin n) (Fin n) ℝ) :
    packedL (Id.run (algorithm_3_2_1 pure A)) = A.luLower ∧
      packedU (Id.run (algorithm_3_2_1 pure A)) = A.luUpper :=
  roundsLU_exact_iff.1 (algorithm_3_2_1_rounds A _ (algorithm_3_2_1_mem_exact A))

/-- **Exact correctness of Algorithm 3.2.1**: if `A(1:k,1:k)` is nonsingular for `k = 1:n-1`, the
packed output holds the LU factorization `A = L U`. Read off the bridge at the exact model. -/
theorem algorithm_3_2_1_spec {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ k : Fin n, (A.strictLeadingPrincipalSubmatrix k).det ≠ 0) :
    IsLU A (packedL (Id.run (algorithm_3_2_1 pure A)))
      (packedU (Id.run (algorithm_3_2_1 pure A))) := by
  obtain ⟨hL, hU⟩ := algorithm_3_2_1_packed_eq A
  rw [hL, hU]
  exact isLU_luLower_luUpper A fun k => (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hA k))

end Algorithm321

/-! ### Rectangular and block LU (§3.2.10–3.2.11) -/

section Rectangular

/-- §3.2.10: "the LU factorization of `A ∈ ℝ^{n×r}` is guaranteed to exist if `A(1:k,1:k)` is
nonsingular for `k = 1:min{n, r}`" — a unit lower trapezoidal `L ∈ ℝ^{n×p}` and an upper
trapezoidal `U ∈ ℝ^{p×r}`, `p = min{n, r}`, with `A = LU`. -/
theorem rectangularLU_exists {n r : ℕ} {A : Matrix (Fin n) (Fin r) ℝ}
    (hA : ∀ k (hk : k + 1 ≤ min n r),
      (A.submatrix (Fin.castLE (hk.trans (min_le_left _ _)))
        (Fin.castLE (hk.trans (min_le_right _ _)))).det ≠ 0) :
    ∃ L U, IsRectLU (P := min n r) A L U :=
  exists_isRectLU_of_forall_isUnit hA

end Rectangular

/-! ### Block LU and the Schur complement (§3.2.11) -/

section BlockLU

variable {r s : ℕ}

/-- **(3.2.9)**, the Schur complement: if `[A₁₁; A₂₁] = [L₁₁; L₂₁] U₁₁` and `L₁₁ U₁₂ = A₁₂`, then
```
[A₁₁ A₁₂; A₂₁ A₂₂] = [L₁₁ 0; L₂₁ I] [I 0; 0 Ã] [U₁₁ U₁₂; 0 I],   Ã = A₂₂ - L₂₁ U₁₂,
```
and when `L₁₁` is unit lower triangular and `U₁₁` nonsingular, `Ã = A₂₂ - A₂₁ A₁₁⁻¹ A₁₂` "is the
Schur complement of `A₁₁` in `A`". Blocks over `Fin r ⊕ Fin s`. -/
theorem equation_3_2_9 {A₁₁ L₁₁ U₁₁ : Matrix (Fin r) (Fin r) ℝ} {A₁₂ U₁₂ : Matrix (Fin r) (Fin s) ℝ}
    {A₂₁ L₂₁ : Matrix (Fin s) (Fin r) ℝ} (A₂₂ : Matrix (Fin s) (Fin s) ℝ)
    (h₁₁ : A₁₁ = L₁₁ * U₁₁) (h₂₁ : A₂₁ = L₂₁ * U₁₁) (h₁₂ : L₁₁ * U₁₂ = A₁₂) :
    fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ =
        fromBlocks L₁₁ 0 L₂₁ 1 * fromBlocks 1 0 0 (A₂₂ - L₂₁ * U₁₂) * fromBlocks U₁₁ U₁₂ 0 1 ∧
      (L₁₁.IsUnitLowerTriangular → IsUnit U₁₁ →
        A₂₂ - L₂₁ * U₁₂ = A₂₂ - A₂₁ * A₁₁⁻¹ * A₁₂) := by
  refine ⟨?_, fun hL hU => ?_⟩
  · rw [fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero,
      zero_add, h₁₁, h₂₁, h₁₂]
    congr 1
    abel
  · have hLd : IsUnit L₁₁.det := (isUnit_iff_isUnit_det _).1 hL.isUnit
    have hUd : IsUnit U₁₁.det := (isUnit_iff_isUnit_det _).1 hU
    rw [h₁₁, h₂₁, ← h₁₂, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc L₁₁⁻¹ L₁₁, nonsing_inv_mul _ hLd, Matrix.one_mul,
      ← Matrix.mul_assoc U₁₁ U₁₁⁻¹, mul_nonsing_inv _ hUd, Matrix.one_mul]

/-- The two-block matrix read on `Fin (r + s)`. -/
theorem reindex_fromBlocks_apply {α : Type*} (A₁₁ : Matrix (Fin r) (Fin r) α)
    (A₁₂ : Matrix (Fin r) (Fin s) α) (A₂₁ : Matrix (Fin s) (Fin r) α)
    (A₂₂ : Matrix (Fin s) (Fin s) α) (i j : Fin (r + s)) :
    reindex finSumFinEquiv finSumFinEquiv (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) i j =
      fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) :=
  rfl

/-- §3.2.11, after (3.2.9): "if `Ã = L₂₂ U₂₂` is the LU factorization of `Ã`, then
`A = [L₁₁ 0; L₂₁ L₂₂] [U₁₁ U₁₂; 0 U₂₂]` is the LU factorization of `A`" — on `Fin (r + s)`
through `finSumFinEquiv`; the step of the recursion of Algorithm 3.2.3. -/
theorem blockLU_of_schur {A₁₁ L₁₁ U₁₁ : Matrix (Fin r) (Fin r) ℝ}
    {A₁₂ U₁₂ : Matrix (Fin r) (Fin s) ℝ} {A₂₁ L₂₁ : Matrix (Fin s) (Fin r) ℝ}
    {A₂₂ L₂₂ U₂₂ : Matrix (Fin s) (Fin s) ℝ} (h₁₁ : IsLU A₁₁ L₁₁ U₁₁) (h₂₁ : A₂₁ = L₂₁ * U₁₁)
    (h₁₂ : L₁₁ * U₁₂ = A₁₂) (h₂₂ : IsLU (A₂₂ - L₂₁ * U₁₂) L₂₂ U₂₂) :
    IsLU (reindex finSumFinEquiv finSumFinEquiv (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂))
      (reindex finSumFinEquiv finSumFinEquiv (fromBlocks L₁₁ 0 L₂₁ L₂₂))
      (reindex finSumFinEquiv finSumFinEquiv (fromBlocks U₁₁ U₁₂ 0 U₂₂)) := by
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => ?_, ?_⟩
  · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    rw [reindex_fromBlocks_apply]
    rcases finSumFinEquiv_symm_cases i with ⟨hi, hi'⟩ | ⟨hi, hi'⟩ <;>
      rcases finSumFinEquiv_symm_cases j with ⟨hj, hj'⟩ | ⟨hj, hj'⟩ <;> rw [hi', hj']
    · exact h₁₁.isUnitLowerTriangular.isLowerTriangular
        (OrderDual.toDual_lt_toDual.2 (Fin.lt_def.2 (Fin.lt_def.1 hij')))
    · rfl
    · exact (by have := Fin.lt_def.1 hij'; omega : False).elim
    · exact h₂₂.isUnitLowerTriangular.isLowerTriangular (OrderDual.toDual_lt_toDual.2
        (Fin.lt_def.2 (show (i : ℕ) - r < j - r by have := Fin.lt_def.1 hij'; omega)))
  · rw [reindex_fromBlocks_apply]
    rcases finSumFinEquiv_symm_cases i with ⟨hi, hi'⟩ | ⟨hi, hi'⟩ <;> rw [hi']
    · exact h₁₁.isUnitLowerTriangular.diag_eq_one _
    · exact h₂₂.isUnitLowerTriangular.diag_eq_one _
  · dsimp only [id] at hij
    rw [reindex_fromBlocks_apply]
    rcases finSumFinEquiv_symm_cases i with ⟨hi, hi'⟩ | ⟨hi, hi'⟩ <;>
      rcases finSumFinEquiv_symm_cases j with ⟨hj, hj'⟩ | ⟨hj, hj'⟩ <;> rw [hi', hj']
    · exact h₁₁.isUpperTriangular (Fin.lt_def.2 (Fin.lt_def.1 hij))
    · exact (by have := Fin.lt_def.1 hij; omega : False).elim
    · rfl
    · exact h₂₂.isUpperTriangular
        (Fin.lt_def.2 (show (j : ℕ) - r < i - r by have := Fin.lt_def.1 hij; omega))
  · rw [reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
    congr 1
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, h₁₁.mul_eq, h₂₂.mul_eq, h₁₂, ← h₂₁,
      add_sub_cancel]

end BlockLU

/-! ### The outer product point of view (§3.2.7) -/

section OuterProduct

variable {s : ℕ}

/-- **§3.2.7**: with `A = [α wᵀ; z B]` and `α ≠ 0`, the first step of Gaussian elimination is the
decomposition `A = [1 0; z/α I] [1 0; 0 B - zwᵀ/α] [α wᵀ; 0 I]`, and if `B - zwᵀ/α = L₁ U₁` then
`A = [1 0; z/α L₁] [α wᵀ; 0 U₁]` is the LU factorization of `A` (on `Fin (1 + s)` through
`finSumFinEquiv`). The case `r = 1` of (3.2.9) and of `blockLU_of_schur`. -/
theorem outerProduct_decomposition {α : ℝ} (hα : α ≠ 0) (w z : Fin s → ℝ)
    (B : Matrix (Fin s) (Fin s) ℝ) :
    fromBlocks (of fun _ _ => α : Matrix (Fin 1) (Fin 1) ℝ) (of fun _ j => w j)
        (of fun i _ => z i) B =
      fromBlocks 1 0 (of fun i _ => z i / α) 1 *
          fromBlocks 1 0 0 (B - of fun i j => z i * w j / α) *
        fromBlocks (of fun _ _ => α) (of fun _ j => w j) 0 1 ∧
      ∀ L₁ U₁ : Matrix (Fin s) (Fin s) ℝ, IsLU (B - of fun i j => z i * w j / α) L₁ U₁ →
        IsLU (reindex finSumFinEquiv finSumFinEquiv (fromBlocks (of fun _ _ => α : Matrix (Fin 1)
            (Fin 1) ℝ) (of fun _ j => w j) (of fun i _ => z i) B))
          (reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 (of fun i _ => z i / α) L₁))
          (reindex finSumFinEquiv finSumFinEquiv
            (fromBlocks (of fun _ _ => α) (of fun _ j => w j) 0 U₁)) := by
  have h₁₁ : (of fun _ _ => α : Matrix (Fin 1) (Fin 1) ℝ) = 1 * of fun _ _ => α :=
    (Matrix.one_mul _).symm
  have h₂₁ : (of fun i _ => z i : Matrix (Fin s) (Fin 1) ℝ) =
      (of fun i _ => z i / α) * (of fun _ _ => α : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    simp [mul_apply, div_mul_cancel₀ _ hα]
  have h₁₂ : (1 : Matrix (Fin 1) (Fin 1) ℝ) * (of fun _ j => w j : Matrix (Fin 1) (Fin s) ℝ) =
      of fun _ j => w j := Matrix.one_mul _
  have hmul : (of fun i (_ : Fin 1) => z i / α) * (of fun (_ : Fin 1) j => w j) =
      (of fun i j => z i * w j / α : Matrix (Fin s) (Fin s) ℝ) := by
    ext i j
    simp [mul_apply]
    ring
  refine ⟨?_, fun L₁ U₁ h => ?_⟩
  · have := (equation_3_2_9 B h₁₁ h₂₁ h₁₂).1
    rwa [hmul] at this
  · have h₁ : IsLU (of fun _ _ => α : Matrix (Fin 1) (Fin 1) ℝ) 1 (of fun _ _ => α) :=
      ⟨isUnitLowerTriangular_one, fun i j hij => (lt_irrefl i (Subsingleton.elim j i ▸ hij)).elim,
        Matrix.one_mul _⟩
    exact blockLU_of_schur h₁ h₂₁ h₁₂ (by rwa [hmul])

end OuterProduct

/-! ### Algorithm 3.2.2 (Gaxpy LU) and the rectangular outer product LU (3.2.8) -/

section Gaxpy

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 3.2.2 (Gaxpy LU).** "Suppose `A ∈ ℝ^{n×n}` has the property that `A(1:k,1:k)` is
nonsingular for `k = 1:n-1`. This algorithm computes the factorization `A = LU` where `L` is unit
lower triangular and `U` is upper triangular. Initialize `L` to the identity and `U` to the zero
matrix."
```
for j = 1:n
    if j = 1
        v = A(:,1)
    else
        ã = A(:,j)
        Solve L(1:j-1,1:j-1) · z = ã(1:j-1) for z ∈ ℝ^{j-1}.
        U(1:j-1,j) = z,  v(j:n) = ã(j:n) - L(j:n,1:j-1) · z
    end
    U(j,j) = v(j),  L(j+1:n,j) = v(j+1:n)/v(j)
end
```
The unit lower triangular solve is row-oriented forward substitution in running differences
(`z(i)` is `ã(i)` minus the rounded products `L(i,r) z(r)`, `r < i`, one rounded subtraction at a
time, with no division by the unit diagonal, §3.1.7), and the gaxpy `v(j:n)` the same running
differences over `r < j`; both are one loop over the rows, `v(1:j-1)` holding `z`. The state is
the pair `(L, U)`. -/
noncomputable def algorithm_3_2_2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) j => do
    let v ← (List.finRange n).foldlM (fun (v : Fin n → ℝ) i => do
      let vi ← ((List.finRange n).filter (fun r => r < i ∧ r < j)).foldlM (fun (c : ℝ) r => do
        let p ← rnd (st.1 i r * v r)
        rnd (c - p)) (A i j)
      pure (Function.update v i vi)) (fun i => A i j)
    let L ← ((List.finRange n).filter (j < ·)).foldlM (fun (L : Matrix (Fin n) (Fin n) ℝ) i => do
      let l ← rnd (v i / v j)
      pure (L.updateRow i (Function.update (L i) j l))) st.1
    pure (L, st.2.updateCol j fun i => if i ≤ j then v i else 0)) (1, 0)

/-- **(3.2.8)**, the outer product LU of a tall `A ∈ ℝ^{n×r}`, `r ≤ n`: "Algorithm 3.2.1
modifies to the following"
```
for k = 1:r
    ρ = k+1:n
    A(ρ,k) = A(ρ,k)/A(k,k)
    if k < r
        μ = k+1:r
        A(ρ,μ) = A(ρ,μ) - A(ρ,k) · A(k,μ)
    end
end
```
"Upon completion, `A` is overwritten by the strictly lower triangular portion of `L ∈ ℝ^{n×r}` and
the upper triangular portion of `U ∈ ℝ^{r×r}`." The guard `k < r` is the emptiness of `μ`. -/
noncomputable def tallOuterProductLU {n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin n) (Fin r) ℝ) :
    M (Matrix (Fin n) (Fin r) ℝ) :=
  (List.finRange r).foldlM (fun (A : Matrix (Fin n) (Fin r) ℝ) k => do
    let A ← ((List.finRange n).filter (Fin.castLE hrn k < ·)).foldlM
      (fun (A : Matrix (Fin n) (Fin r) ℝ) i => do
        let l ← rnd (A i k / A (Fin.castLE hrn k) k)
        pure (A.updateRow i (Function.update (A i) k l))) A
    ((List.finRange n).filter (Fin.castLE hrn k < ·)).foldlM
      (fun (A : Matrix (Fin n) (Fin r) ℝ) i =>
        ((List.finRange r).filter (k < ·)).foldlM (fun (A : Matrix (Fin n) (Fin r) ℝ) j => do
          let p ← rnd (A i k * A (Fin.castLE hrn k) j)
          let a ← rnd (A i j - p)
          pure (A.updateRow i (Function.update (A i) j a))) A) A) A

end Gaxpy

/-! ### Recursive block LU (Algorithm 3.2.3) -/

section BlockLUAlgorithm

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 3.2.3 (Recursive Block LU).** "Suppose `A ∈ ℝ^{n×n}` has an LU factorization and
`r` is a positive integer. The following algorithm computes unit lower triangular `L ∈ ℝ^{n×n}` and
upper triangular `U ∈ ℝ^{n×n}` so `A = LU`."
```
function [L, U] = BlockLU(A, n, r)
if n ≤ r
    Compute the LU factorization A = LU using (say) Algorithm 3.2.1.
else
    Use (3.2.8) to compute the LU factorization A(:,1:r) = [L₁₁; L₂₁] U₁₁.
    Solve L₁₁ U₁₂ = A(1:r, r+1:n) for U₁₂.
    Ã = A(r+1:n, r+1:n) - L₂₁ U₁₂
    [L₂₂, U₂₂] = BlockLU(Ã, n - r, r)
    L = [L₁₁ 0; L₂₁ L₂₂],  U = [U₁₁ U₁₂; 0 U₂₂]
end
```
Recursion on `n`; the split `Fin n ≃ Fin r ⊕ Fin (n - r)` is `finSumFinEquiv` up to `finCongr`.
`L₁₁ U₁₂ = A₁₂` is solved column by column by Algorithm 3.1.3, and `Ã` entrywise as
`fl(ã_ij - fl(L₂₁(i,:) · U₁₂(:,j)))` with the dot product of Algorithm 1.1.1 (the book does not
analyse the rounding of its level-3 product). -/
noncomputable def algorithm_3_2_3 (r : ℕ) (hr : 0 < r) :
    (n : ℕ) → Matrix (Fin n) (Fin n) ℝ → M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)
  | n, A =>
    if h : n ≤ r then do
      let F ← algorithm_3_2_1 rnd A
      pure (packedL F, packedU F)
    else do
      let e : Fin r ⊕ Fin (n - r) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
      let F ← tallOuterProductLU rnd (le_of_lt (not_le.1 h)) (fun i k => A i (e (Sum.inl k)))
      let L₁₁ : Matrix (Fin r) (Fin r) ℝ := of fun i k =>
        if k < i then F (e (Sum.inl i)) k else if i = k then 1 else 0
      let L₂₁ : Matrix (Fin (n - r)) (Fin r) ℝ := of fun i k => F (e (Sum.inr i)) k
      let U₁₁ : Matrix (Fin r) (Fin r) ℝ := of fun i k => if i ≤ k then F (e (Sum.inl i)) k else 0
      let U₁₂ ← (List.finRange (n - r)).foldlM (fun (U₁₂ : Matrix (Fin r) (Fin (n - r)) ℝ) c => do
        let col ← algorithm_3_1_3 rnd L₁₁ (fun i => A (e (Sum.inl i)) (e (Sum.inr c)))
        pure (U₁₂.updateCol c col)) 0
      let Ã ← (List.finRange (n - r)).foldlM (fun (Ã : Matrix (Fin (n - r)) (Fin (n - r)) ℝ) i =>
        (List.finRange (n - r)).foldlM (fun (Ã : Matrix (Fin (n - r)) (Fin (n - r)) ℝ) j => do
          let s ← dotAccum rnd (List.finRange r) (L₂₁ i) (fun k => U₁₂ k j) 0
          let a ← rnd (A (e (Sum.inr i)) (e (Sum.inr j)) - s)
          pure (Ã.updateRow i (Function.update (Ã i) j a))) Ã) 0
      let LU₂₂ ← algorithm_3_2_3 r hr (n - r) Ã
      pure (reindex e e (fromBlocks L₁₁ 0 L₂₁ LU₂₂.1), reindex e e (fromBlocks U₁₁ U₁₂ 0 LU₂₂.2))
  termination_by n => n
  decreasing_by omega

end BlockLUAlgorithm

/-! ### The bridge of Algorithm 3.2.2 -/

section GaxpyBridge

variable {fp : RoundingModel ℝ} {n : ℕ}

/-- A run of a loop of rounded subtractions of rounded values is a running difference. -/
theorem exists_of_mem_run_foldlM_sub {ι : Type*} {o : List ι} (ho : o.Nodup)
    {f : ι → ℝ} {c x : ℝ}
    (h : x ∈ (o.foldlM (fun (c : ℝ) r => do let p ← fp.round (f r); fp.round (c - p)) c).run) :
    ∃ p : ι → ℝ, (∀ r ∈ o, fp.Rounds (f r) (p r)) ∧ RoundsSumFrom fp c (o.map fun r => -p r) x := by
  classical
  induction o generalizing c with
  | nil =>
    rw [List.foldlM_nil, SetM.mem_run_pure] at h
    exact ⟨fun _ => 0, by simp, h ▸ .nil _⟩
  | cons a o ih =>
    simp only [List.foldlM_cons, bind_assoc, SetM.mem_run_bind, RoundingModel.mem_run_round] at h
    obtain ⟨pa, hpa, c', hc', h⟩ := h
    obtain ⟨p, hp, hsum⟩ := ih (List.nodup_cons.1 ho).2 h
    have ha : a ∉ o := (List.nodup_cons.1 ho).1
    refine ⟨Function.update p a pa, fun r hr => ?_, ?_⟩
    · rcases List.mem_cons.1 hr with rfl | hr
      · rwa [Function.update_self]
      · rw [Function.update_of_ne fun (e : r = a) => ha (e ▸ hr)]
        exact hp r hr
    · rw [List.map_cons, Function.update_self]
      have hmap : (o.map fun r => -Function.update p a pa r) = o.map fun r => -p r :=
        List.map_congr_left fun r hr => by
          rw [Function.update_of_ne fun (e : r = a) => ha (e ▸ hr)]
      rw [hmap]
      exact .cons (by rw [← sub_eq_add_neg]; exact hc') hsum

/-- The invariant of Algorithm 3.2.2 after the columns before `j`: those columns hold finished
entries of the Doolittle recurrence, and the later columns of `L` and `U` are still those of the
identity and of the zero matrix. -/
def GaxpyInv (fp : RoundingModel ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (j : ℕ)
    (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i c : Fin n, (c : ℕ) < j → i ≤ c → ∃ (o : List (Fin n)) (p : Fin n → ℝ), o.Nodup ∧
    (∀ r, r ∈ o ↔ r < i) ∧ (∀ r ∈ o, fp.Rounds (st.1 i r * st.2 r c) (p r)) ∧
    RoundsSumFrom fp (A i c) (o.map fun r => -p r) (st.2 i c)) ∧
  (∀ i c : Fin n, (c : ℕ) < j → c < i → ∃ (o : List (Fin n)) (p : Fin n → ℝ) (t : ℝ), o.Nodup ∧
    (∀ r, r ∈ o ↔ r < c) ∧ (∀ r ∈ o, fp.Rounds (st.1 i r * st.2 r c) (p r)) ∧
    RoundsSumFrom fp (A i c) (o.map fun r => -p r) t ∧ fp.Rounds (t / st.2 c c) (st.1 i c)) ∧
  (∀ i c : Fin n, j ≤ (c : ℕ) → st.1 i c = if i = c then 1 else 0) ∧
  (∀ i c : Fin n, j ≤ (c : ℕ) → st.2 i c = 0) ∧
  (∀ i c : Fin n, i < c → st.1 i c = 0) ∧ (∀ i, st.1 i i = 1) ∧
  (∀ i c : Fin n, c < i → st.2 i c = 0)

/-- One column of Algorithm 3.2.2 keeps its invariant. -/
theorem gaxpyInv_step (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n)
    (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) (hst : GaxpyInv fp A j st)
    (st' : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)
    (hst' : st' ∈ (do
      let v ← (List.finRange n).foldlM (fun (v : Fin n → ℝ) i => do
        let vi ← ((List.finRange n).filter (fun r => r < i ∧ r < j)).foldlM (fun (c : ℝ) r => do
          let p ← fp.round (st.1 i r * v r)
          fp.round (c - p)) (A i j)
        pure (Function.update v i vi)) (fun i => A i j)
      let L ← ((List.finRange n).filter (j < ·)).foldlM
        (fun (L : Matrix (Fin n) (Fin n) ℝ) i => do
          let l ← fp.round (v i / v j)
          pure (L.updateRow i (Function.update (L i) j l))) st.1
      pure (L, st.2.updateCol j fun i => if i ≤ j then v i else 0) : SetM _).run) :
    GaxpyInv fp A (j + 1) st' := by
  obtain ⟨L, U⟩ := st
  obtain ⟨hU, hL, hLid, hU0, hLlow, hLdiag, hUup⟩ := hst
  dsimp only at hst' hU hL hLid hU0 hLlow hLdiag hUup
  rw [SetM.mem_run_bind] at hst'
  obtain ⟨v, hv, hst'⟩ := hst'
  rw [SetM.mem_run_bind] at hst'
  obtain ⟨L', hL', hst'⟩ := hst'
  rw [SetM.mem_run_pure] at hst'
  subst hst'
  -- the entries of `v`: running differences over `r < min i j`
  have hvrow : ∀ i, ∃ (o : List (Fin n)) (p : Fin n → ℝ), o.Nodup ∧
      (∀ r, r ∈ o ↔ r < i ∧ r < j) ∧ (∀ r ∈ o, fp.Rounds (L i r * v r) (p r)) ∧
      RoundsSumFrom fp (A i j) (o.map fun r => -p r) (v i) := by
    have key := forall_mem_run_foldlM_update_rows (List.nodup_finRange n)
      (fun i (s : Fin n → ℝ) => ((List.finRange n).filter (fun r => r < i ∧ r < j)).foldlM
        (fun (c : ℝ) r => do let p ← fp.round (L i r * s r); fp.round (c - p)) (A i j))
      (fun i s x => ∃ (o : List (Fin n)) (p : Fin n → ℝ), o.Nodup ∧
        (∀ r, r ∈ o ↔ r < i ∧ r < j) ∧ (∀ r ∈ o, fp.Rounds (L i r * s r) (p r)) ∧
        RoundsSumFrom fp (A i j) (o.map fun r => -p r) x)
      (fun i => A i j) ?_ ?_ v hv
    · exact fun i => key i (List.mem_finRange i)
    · rintro p i q hl s - x hx
      have hnd := (List.nodup_finRange n).filter (fun r => decide (r < i ∧ r < j))
      obtain ⟨pp, hpp, hsum⟩ := exists_of_mem_run_foldlM_sub hnd hx
      exact ⟨_, pp, hnd, fun r => by simp, hpp, hsum⟩
    · rintro p i q hl s s' x hss ⟨o, pp, hnd, ho, hpp, hsum⟩
      refine ⟨o, pp, hnd, ho, fun r hr => ?_, hsum⟩
      have hri := ((ho r).1 hr).1
      have hrp : r ∈ p := mem_prefix_of_pairwise (List.pairwise_lt_finRange n) hl
        (List.mem_finRange r) (ne_of_lt hri) (lt_asymm hri)
      rw [← hss r hrp]
      exact hpp r hr
  -- the entries of `L'`
  have hL'eq : ((List.finRange n).filter (j < ·)).foldlM
      (fun (L : Matrix (Fin n) (Fin n) ℝ) i => do
        let l ← fp.round (v i / v j)
        pure (L.updateRow i (Function.update (L i) j l))) L =
      (((List.finRange n).filter (j < ·)).map (·, j)).foldlM
        (fun (L : Matrix (Fin n) (Fin n) ℝ) a => do
          let x ← (fun (a : Fin n × Fin n) (_ : ℝ) (_ : Matrix (Fin n) (Fin n) ℝ) =>
            fp.round (v a.1 / v j)) a (L a.1 a.2) L
          pure (L.updateRow a.1 (Function.update (L a.1) a.2 x))) L := by
    rw [List.foldlM_map]
  have hnd₁ : ((List.finRange n).filter (j < ·)).Nodup := (List.nodup_finRange n).filter _
  have hl₁ : (((List.finRange n).filter (j < ·)).map (·, j)).Nodup :=
    hnd₁.map fun _ _ h => (Prod.mk.inj h).1
  have hl₁mem : ∀ i c, (i, c) ∈ ((List.finRange n).filter (j < ·)).map (·, j) ↔
      j < i ∧ c = j := fun i c => by
    simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha, rfl, rfl⟩; exact ⟨ha, rfl⟩
    · rintro ⟨hi, rfl⟩; exact ⟨i, hi, rfl, rfl⟩
  rw [hL'eq] at hL'
  obtain ⟨hL'₁, hL'₂⟩ := (mem_run_foldlM_updateEntry _ hl₁
    (fun a _ (_ : Matrix (Fin n) (Fin n) ℝ) => fp.round (v a.1 / v j))
    (fun _ _ _ _ _ _ => rfl) L L').1 hL'
  have hL'o : ∀ i c, ¬ (j < i ∧ c = j) → L' i c = L i c := fun i c h =>
    hL'₁ i c fun hm => h ((hl₁mem i c).1 hm)
  have hL'j : ∀ i, j < i → fp.Rounds (v i / v j) (L' i j) := fun i hi =>
    hL'₂ (i, j) ((hl₁mem i j).2 ⟨hi, rfl⟩)
  have hLc : ∀ i c, c ≠ j → L' i c = L i c := fun i c hc => hL'o i c fun h => hc h.2
  set U' := U.updateCol j fun i => if i ≤ j then v i else 0 with hU'
  have hU'o : ∀ i c, c ≠ j → U' i c = U i c := fun i c hc => by
    simp [hU', hc]
  have hU'j : ∀ i, U' i j = if i ≤ j then v i else 0 := fun i => by simp [hU']
  -- the columns before `j` are unchanged, and so are their products
  have hcol : ∀ i c r : Fin n, c < j → r ≤ c → L' i r = L i r ∧ U' r c = U r c :=
    fun i c r hc hr => ⟨hLc i r (ne_of_lt (lt_of_le_of_lt hr hc)), hU'o r c (ne_of_lt hc)⟩
  dsimp only [GaxpyInv]
  refine ⟨fun i c hc hic => ?_, fun i c hc hci => ?_, fun i c hc => ?_, fun i c hc => ?_,
    fun i c hic => ?_, fun i => ?_, fun i c hci => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | hc
    · have hc' : c < j := Fin.lt_def.2 hc
      obtain ⟨o, p, hnd, ho, hp, hsum⟩ := hU i c hc hic
      refine ⟨o, p, hnd, ho, fun r hr => ?_, ?_⟩
      · have hri := (ho r).1 hr
        rw [(hcol i c r hc' (hri.le.trans hic)).1, (hcol i c r hc' (hri.le.trans hic)).2]
        exact hp r hr
      · rw [hU'o i c (ne_of_lt hc')]
        exact hsum
    · have hcj : c = j := Fin.ext hc
      subst hcj
      obtain ⟨o, p, hnd, ho, hp, hsum⟩ := hvrow i
      refine ⟨o, p, hnd, fun r => (ho r).trans ⟨fun h => h.1, fun h => ⟨h, lt_of_lt_of_le h hic⟩⟩,
        fun r hr => ?_, ?_⟩
      · have hr' := (ho r).1 hr
        rw [hLc i r (ne_of_lt hr'.2), hU'j r]
        simp only [hr'.2.le, ↓reduceIte]
        exact hp r hr
      · rw [hU'j i]
        simp only [hic, ↓reduceIte]
        exact hsum
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | hc
    · have hc' : c < j := Fin.lt_def.2 hc
      obtain ⟨o, p, t, hnd, ho, hp, hsum, hx⟩ := hL i c hc hci
      refine ⟨o, p, t, hnd, ho, fun r hr => ?_, hsum, ?_⟩
      · have hrc := (ho r).1 hr
        rw [(hcol i c r hc' hrc.le).1, (hcol i c r hc' hrc.le).2]
        exact hp r hr
      · rw [hU'o c c (ne_of_lt hc'), hLc i c (ne_of_lt hc')]
        exact hx
    · have hcj : c = j := Fin.ext hc
      subst hcj
      obtain ⟨o, p, hnd, ho, hp, hsum⟩ := hvrow i
      refine ⟨o, p, v i, hnd, fun r => (ho r).trans ⟨fun h => h.2, fun h => ⟨h.trans hci, h⟩⟩,
        fun r hr => ?_, hsum, ?_⟩
      · have hr' := (ho r).1 hr
        rw [hLc i r (ne_of_lt hr'.2), hU'j r]
        simp only [hr'.2.le, ↓reduceIte]
        exact hp r hr
      · rw [hU'j c]
        simp only [le_refl, ↓reduceIte]
        exact hL'j i hci
  · have hcj : c ≠ j := fun h => by rw [h] at hc; exact absurd hc (by simp)
    rw [hLc i c hcj]
    exact hLid i c (by omega)
  · have hcj : c ≠ j := fun h => by rw [h] at hc; exact absurd hc (by simp)
    rw [hU'o i c hcj]
    exact hU0 i c (by omega)
  · by_cases hcj : c = j
    · subst hcj
      rw [hL'o i c fun h => lt_asymm h.1 hic]
      exact hLlow i c hic
    · rw [hLc i c hcj]
      exact hLlow i c hic
  · rw [hL'o i i fun ⟨h1, h2⟩ => by subst h2; exact lt_irrefl _ h1]
    exact hLdiag i
  · by_cases hcj : c = j
    · subst hcj
      rw [hU'j i]
      simp only [not_le.2 hci, ↓reduceIte]
    · rw [hU'o i c hcj]
      exact hUup i c hci

/-- **The bridge of Algorithm 3.2.2**: every run `(L̂, Û)` in the relational model is an
admissible computed LU factorization, `FloatingPoint.RoundsLU fp A L̂ Û`, with no hypothesis on
`A`: each `û_ij`, `i ≤ j`, is the running difference of `a_ij` over `r < i` (the unit triangular
solve for `i < j`, the gaxpy for `i = j`), and each `l̂_ij`, `i > j`, the gaxpy's running
difference over `r < j` divided by `û_jj`. -/
theorem algorithm_3_2_2_rounds (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ out ∈ (algorithm_3_2_2 fp.round A).run, RoundsLU fp A out.1 out.2 := by
  intro out hout
  have h0 : GaxpyInv fp A 0 (1, 0) := ⟨fun _ _ h => absurd h (Nat.not_lt_zero _),
    fun _ _ h => absurd h (Nat.not_lt_zero _), fun i c _ => by simp [one_apply],
    fun _ _ _ => rfl, fun i c h => by simp [one_apply, h.ne], fun i => by simp,
    fun _ _ _ => rfl⟩
  obtain ⟨hU, hL, -, -, hLlow, hLdiag, hUup⟩ := SetM.forall_mem_run_foldlM_finRange
    (GaxpyInv fp A) h0 (fun j st hst st' hst' => gaxpyInv_step A j st hst st' hst') out hout
  exact ⟨hLlow, hLdiag, hUup, fun i j hij => hU i j j.2 hij, fun i j hji => hL i j j.2 hji⟩

/-- The exact run of Algorithm 3.2.2 is a run of the exact model. -/
private theorem algorithm_3_2_2_mem_exact (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_3_2_2 pure A) ∈ (algorithm_3_2_2 (RoundingModel.exact ℝ).round A).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_3_2_2, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

/-- **Exact correctness of Algorithm 3.2.2**: its exact output is the Doolittle pair
`(luLower A, luUpper A)` for every `A`, the LU factorization when `A(1:k,1:k)` is nonsingular for
`k = 1:n-1`. Read off the bridge at the exact model. -/
theorem algorithm_3_2_2_spec (A : Matrix (Fin n) (Fin n) ℝ) :
    (Id.run (algorithm_3_2_2 pure A)).1 = A.luLower ∧
      (Id.run (algorithm_3_2_2 pure A)).2 = A.luUpper ∧
      ((∀ k : Fin n, (A.strictLeadingPrincipalSubmatrix k).det ≠ 0) →
        IsLU A (Id.run (algorithm_3_2_2 pure A)).1 (Id.run (algorithm_3_2_2 pure A)).2) := by
  obtain ⟨hL, hU⟩ := roundsLU_exact_iff.1 (algorithm_3_2_2_rounds A _ (algorithm_3_2_2_mem_exact A))
  refine ⟨hL, hU, fun hA => ?_⟩
  rw [hL, hU]
  exact isLU_luLower_luUpper A fun k => (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hA k))

end GaxpyBridge

end GolubVanLoan.Chapter03
