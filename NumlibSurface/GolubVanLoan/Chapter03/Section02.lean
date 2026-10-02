import Numlib.Data.Fin.Sum
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
* `rectangularLU_exists` (§3.2.10), `equation_3_2_9`;
* `equation_3_2_8` (the rectangular outer product LU computes `A = L U`, by a simulation of
  Algorithm 3.2.1 on the bordered square `[A | [0; I]]`) and `algorithm_3_2_3_spec` (strong
  induction on `n` through `blockLU_of_schur`);
* `algorithm_3_2_4` (nonrecursive block LU, blocks by `Fin.divNat`) and `algorithm_3_2_4_spec`
  (invariant: finished factors where `min(i,j) < k r`, Schur complement values elsewhere).
-/

open FloatingPoint Matrix

namespace GolubVanLoan.Chapter03

/-! ### Loops over matrix entries -/

section Loops

/-- **One matrix entry per step.** Over a duplicate-free list of positions, a loop whose step at
`(i, j)` rewrites the entry `(i, j)` only — from its current value and from entries at positions
outside the list — has as run set the matrices that agree with the initial one off the list and
whose entry at each listed position is a result of its step on the initial matrix: the backbone's
`SetM.mem_run_foldlM_updateRow_update_of_nodup`. -/
theorem mem_run_foldlM_updateEntry {m n : ℕ} (l : List (Fin m × Fin n)) (hl : l.Nodup)
    (g : Fin m × Fin n → ℝ → Matrix (Fin m) (Fin n) ℝ → SetM ℝ)
    (hg : ∀ a ∈ l, ∀ x (A A' : Matrix (Fin m) (Fin n) ℝ),
      (∀ i j, (i, j) ∉ l → A i j = A' i j) → g a x A = g a x A')
    (A₀ A : Matrix (Fin m) (Fin n) ℝ) :
    A ∈ (l.foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) a => do
        let x ← g a (A a.1 a.2) A
        pure (A.updateRow a.1 (Function.update (A a.1) a.2 x))) A₀).run ↔
      (∀ i j, (i, j) ∉ l → A i j = A₀ i j) ∧ ∀ a ∈ l, A a.1 a.2 ∈ (g a (A₀ a.1 a.2) A₀).run :=
  SetM.mem_run_foldlM_updateRow_update_of_nodup l hl g hg A₀ A

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
  have hflat := List.foldlM_foldlM_eq_foldlM_flatMap ((List.finRange n).filter (k < ·))
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
  have hflat := List.foldlM_foldlM_eq_foldlM_flatMap ((List.finRange n).filter (k < ·))
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
    refine ⟨o, hnd, ho, p, fun r hr => ?_, ?_⟩
    · beta_reduce
      have hri := (ho r).1 hr
      rw [packedL_apply_of_lt F hri, packedU_apply_of_le F (hri.le.trans hij)]
      exact hp r hr
    · rw [packedU_apply_of_le F hij]
      exact hsum
  · obtain ⟨o, p, t, hnd, ho, hp, hsum, hx⟩ := (hinv i j).2.1 j.2 hij
    refine ⟨o, t, hnd, ho, ⟨p, fun r hr => ?_, hsum⟩, ?_⟩
    · beta_reduce
      have hrj := (ho r).1 hr
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
      have hrp : r ∈ p := List.mem_prefix_of_pairwise (List.pairwise_lt_finRange n) hl
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
  refine ⟨hLlow, hLdiag, hUup, fun i j hij => ?_, fun i j hji => ?_⟩
  · obtain ⟨o, p, hnd, ho, hp, hs⟩ := hU i j j.2 hij
    exact ⟨o, hnd, ho, p, hp, hs⟩
  · obtain ⟨o, p, t, hnd, ho, hp, hs, hx⟩ := hL i j j.2 hji
    exact ⟨o, t, hnd, ho, ⟨p, hp, hs⟩, hx⟩

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

/-! ### The rectangular outer product LU (3.2.8): exact semantics -/

section TallLU

/-- One step `k` of (3.2.8): the multipliers of column `k` below the pivot row, then the update of
the columns `k+1:r` of the rows below the pivot. -/
private noncomputable def tallOuterProductStep {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)
    {n r : ℕ} (hrn : r ≤ n) (k : Fin r) (A : Matrix (Fin n) (Fin r) ℝ) :
    M (Matrix (Fin n) (Fin r) ℝ) := do
  let A ← ((List.finRange n).filter (Fin.castLE hrn k < ·)).foldlM
    (fun (A : Matrix (Fin n) (Fin r) ℝ) i => do
      let l ← rnd (A i k / A (Fin.castLE hrn k) k)
      pure (A.updateRow i (Function.update (A i) k l))) A
  ((List.finRange n).filter (Fin.castLE hrn k < ·)).foldlM
    (fun (A : Matrix (Fin n) (Fin r) ℝ) i =>
      ((List.finRange r).filter (k < ·)).foldlM (fun (A : Matrix (Fin n) (Fin r) ℝ) j => do
        let p ← rnd (A i k * A (Fin.castLE hrn k) j)
        let a ← rnd (A i j - p)
        pure (A.updateRow i (Function.update (A i) j a))) A) A

variable {n r : ℕ}

private theorem tallOuterProductLU_eq_foldlM {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)
    (hrn : r ≤ n) (A : Matrix (Fin n) (Fin r) ℝ) :
    tallOuterProductLU rnd hrn A =
      (List.finRange r).foldlM (fun A k => tallOuterProductStep rnd hrn k A) A :=
  rfl

/-- The run set of one step of (3.2.8), as `mem_run_outerProductStep` for Algorithm 3.2.1: the
multipliers below the pivot row are rounded quotients, the entries right of column `k` below the
pivot row receive one rounded update, every other entry is unchanged. -/
private theorem mem_run_tallOuterProductStep {fp : RoundingModel ℝ} (hrn : r ≤ n) (k : Fin r)
    {S S' : Matrix (Fin n) (Fin r) ℝ} (h : S' ∈ (tallOuterProductStep fp.round hrn k S).run) :
    (∀ i j, ¬ (Fin.castLE hrn k < i ∧ (j = k ∨ k < j)) → S' i j = S i j) ∧
      (∀ i, Fin.castLE hrn k < i → fp.Rounds (S i k / S (Fin.castLE hrn k) k) (S' i k)) ∧
      ∀ i j, Fin.castLE hrn k < i → k < j →
        ∃ p, fp.Rounds (S' i k * S' (Fin.castLE hrn k) j) p ∧ fp.Rounds (S i j - p) (S' i j) := by
  set K := Fin.castLE hrn k with hK
  rw [tallOuterProductStep, SetM.mem_run_bind] at h
  obtain ⟨S₁, h₁, h₂⟩ := h
  have hnd : ((List.finRange n).filter (K < ·)).Nodup := (List.nodup_finRange n).filter _
  have hndc : ((List.finRange r).filter (k < ·)).Nodup := (List.nodup_finRange r).filter _
  have hmem : ∀ i, i ∈ (List.finRange n).filter (K < ·) ↔ K < i := fun i => by simp
  have hmemc : ∀ j, j ∈ (List.finRange r).filter (k < ·) ↔ k < j := fun j => by simp
  -- the division loop
  have hdiv : ((List.finRange n).filter (K < ·)).foldlM
      (fun (A : Matrix (Fin n) (Fin r) ℝ) i => do
        let l ← fp.round (A i k / A K k)
        pure (A.updateRow i (Function.update (A i) k l))) S =
      (((List.finRange n).filter (K < ·)).map (·, k)).foldlM
        (fun (A : Matrix (Fin n) (Fin r) ℝ) a => do
          let x ← (fun (_ : Fin n × Fin r) x (A : Matrix (Fin n) (Fin r) ℝ) =>
            fp.round (x / A K k)) a (A a.1 a.2) A
          pure (A.updateRow a.1 (Function.update (A a.1) a.2 x))) S := by
    rw [List.foldlM_map]
  have hl₁ : (((List.finRange n).filter (K < ·)).map (·, k)).Nodup :=
    hnd.map fun _ _ h => (Prod.mk.inj h).1
  have hl₁mem : ∀ i j, (i, j) ∈ ((List.finRange n).filter (K < ·)).map (·, k) ↔
      K < i ∧ j = k := fun i j => by
    simp only [List.mem_map, hmem, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha, rfl, rfl⟩; exact ⟨ha, rfl⟩
    · rintro ⟨hi, rfl⟩; exact ⟨i, hi, rfl, rfl⟩
  rw [hdiv] at h₁
  obtain ⟨hS₁, hS₁'⟩ := (mem_run_foldlM_updateEntry _ hl₁
    (fun _ x (A : Matrix (Fin n) (Fin r) ℝ) => fp.round (x / A K k))
    (fun a _ x A A' hA => by
      rw [hA K k fun h => lt_irrefl K ((hl₁mem K k).1 h).1]) S S₁).1 h₁
  -- the update loop
  have hflat := List.foldlM_foldlM_eq_foldlM_flatMap ((List.finRange n).filter (K < ·))
    (fun _ => (List.finRange r).filter (k < ·)) (fun (A : Matrix (Fin n) (Fin r) ℝ) i j => (do
      let p ← fp.round (A i k * A K j)
      let a ← fp.round (A i j - p)
      pure (A.updateRow i (Function.update (A i) j a)) : SetM _)) S₁
  beta_reduce at hflat
  rw [hflat] at h₂
  have hl₂ : ((((List.finRange n).filter (K < ·)).flatMap fun a =>
      ((List.finRange r).filter (k < ·)).map (a, ·))).Nodup :=
    List.nodup_flatMap.2 ⟨fun a _ => hndc.map fun _ _ h => (Prod.mk.inj h).2,
      hnd.imp fun {a b} hab => List.disjoint_left.2 fun {x} hxa hxb => by
        obtain ⟨_, _, rfl⟩ := List.mem_map.1 hxa
        obtain ⟨_, _, h⟩ := List.mem_map.1 hxb
        exact hab (Prod.mk.inj h).1.symm⟩
  have hl₂mem : ∀ i j, (i, j) ∈ (((List.finRange n).filter (K < ·)).flatMap fun a =>
      ((List.finRange r).filter (k < ·)).map (a, ·)) ↔ K < i ∧ k < j := fun i j => by
    simp only [List.mem_flatMap, List.mem_map, hmem, hmemc, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha, b, hb, rfl, rfl⟩; exact ⟨ha, hb⟩
    · rintro ⟨hi, hj⟩; exact ⟨i, hi, j, hj, rfl, rfl⟩
  have key := mem_run_foldlM_updateEntry _ hl₂
    (fun a x (A : Matrix (Fin n) (Fin r) ℝ) => fp.round (A a.1 k * A K a.2) >>= fun p =>
      fp.round (x - p))
    (fun a _ x A A' hA => by
      rw [hA a.1 k fun h => lt_irrefl k ((hl₂mem a.1 k).1 h).2,
        hA K a.2 fun h => lt_irrefl K ((hl₂mem K a.2).1 h).1]) S₁ S'
  simp only [bind_assoc] at key
  obtain ⟨hS', hS''⟩ := key.1 h₂
  have hS'k : ∀ i, S' i k = S₁ i k := fun i => hS' i k fun h => lt_irrefl k ((hl₂mem i k).1 h).2
  have hS'r : ∀ j, S' K j = S₁ K j := fun j => hS' K j fun h => lt_irrefl K ((hl₂mem K j).1 h).1
  refine ⟨fun i j hij => ?_, fun i hi => ?_, fun i j hi hj => ?_⟩
  · rw [hS' i j fun h => hij ⟨((hl₂mem i j).1 h).1, Or.inr ((hl₂mem i j).1 h).2⟩,
      hS₁ i j fun h => hij ⟨((hl₁mem i j).1 h).1, Or.inl ((hl₁mem i j).1 h).2⟩]
  · rw [hS'k]
    exact hS₁' (i, k) ((hl₁mem i k).2 ⟨hi, rfl⟩)
  · obtain ⟨p, hp, hc⟩ := SetM.mem_run_bind.1 (hS'' (i, j) ((hl₂mem i j).2 ⟨hi, hj⟩))
    refine ⟨p, by rw [hS'k, hS'r]; exact hp, ?_⟩
    rw [← hS₁ i j fun h => hj.ne' ((hl₁mem i j).1 h).2]
    exact hc

/-- One exact step of (3.2.8), entrywise. -/
private theorem tallOuterProductStep_exact (hrn : r ≤ n) (k : Fin r)
    (S : Matrix (Fin n) (Fin r) ℝ) :
    (∀ i j, ¬ (Fin.castLE hrn k < i ∧ (j = k ∨ k < j)) →
        Id.run (tallOuterProductStep pure hrn k S) i j = S i j) ∧
      (∀ i, Fin.castLE hrn k < i →
        Id.run (tallOuterProductStep pure hrn k S) i k = S i k / S (Fin.castLE hrn k) k) ∧
      ∀ i j, Fin.castLE hrn k < i → k < j →
        Id.run (tallOuterProductStep pure hrn k S) i j = S i j -
          Id.run (tallOuterProductStep pure hrn k S) i k *
            Id.run (tallOuterProductStep pure hrn k S) (Fin.castLE hrn k) j := by
  have hmem : Id.run (tallOuterProductStep pure hrn k S) ∈
      (tallOuterProductStep (RoundingModel.exact ℝ).round hrn k S).run := by
    rw [RoundingModel.round_exact]
    simp only [tallOuterProductStep, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
    rfl
  obtain ⟨h₁, h₂, h₃⟩ := mem_run_tallOuterProductStep hrn k hmem
  refine ⟨h₁, fun i hi => h₂ i hi, fun i j hi hj => ?_⟩
  obtain ⟨p, hp, hq⟩ := h₃ i j hi hj
  rw [RoundingModel.exact_rounds_iff] at hp hq
  rw [hq, hp]

/-- One exact step of Algorithm 3.2.1, entrywise. -/
private theorem outerProductStep_exact (k : Fin n) (S : Matrix (Fin n) (Fin n) ℝ) :
    (∀ i j, ¬ (k < i ∧ (j = k ∨ k < j)) → Id.run (outerProductStep pure k S) i j = S i j) ∧
      (∀ i, k < i → Id.run (outerProductStep pure k S) i k = S i k / S k k) ∧
      ∀ i j, k < i → k < j →
        Id.run (outerProductStep pure k S) i j = S i j -
          Id.run (outerProductStep pure k S) i k * Id.run (outerProductStep pure k S) k j := by
  have hmem : Id.run (outerProductStep pure k S) ∈
      (outerProductStep (RoundingModel.exact ℝ).round k S).run := by
    rw [RoundingModel.round_exact]
    simp only [outerProductStep, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
    rfl
  obtain ⟨h₁, h₂, h₃⟩ := mem_run_outerProductStep k hmem
  refine ⟨h₁, fun i hi => h₂ i hi, fun i j hi hj => ?_⟩
  obtain ⟨p, hp, hq⟩ := h₃ i j hi hj
  rw [RoundingModel.exact_rounds_iff] at hp hq
  rw [hq, hp]


/-- The indices of `Fin n` below `r`, read in `Fin r`: the filter of `List.finRange n` by
`· < r` is `List.finRange r`. -/
private theorem filterMap_finRange_lt (hrn : r ≤ n) :
    (List.finRange n).filterMap
        (fun k : Fin n => if h : (k : ℕ) < r then some (⟨k, h⟩ : Fin r) else none) =
      List.finRange r := by
  induction n, hrn using Nat.le_induction with
  | base =>
    conv_rhs => rw [← List.filterMap_some (l := List.finRange r)]
    exact List.filterMap_congr fun k _ => by simp
  | succ m hrm ih =>
    rw [List.finRange_succ_last, List.filterMap_append, List.filterMap_map]
    have hlast : (List.filterMap (fun k : Fin (m + 1) =>
        if h : (k : ℕ) < r then some (⟨k, h⟩ : Fin r) else none) [Fin.last m]) = [] := by
      simp only [List.filterMap_cons, List.filterMap_nil, Fin.val_last]
      rw [dite_eq_right (by omega)]
    rw [hlast, List.append_nil, ← ih]
    rfl

/-- The square matrix `[A | [0; I]]` bordering a tall `A ∈ ℝ^{n×r}`: its first `r` columns are
those of `A`, its last `n - r` columns those of the identity. -/
private def tallBorder (A : Matrix (Fin n) (Fin r) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if h : (j : ℕ) < r then A i ⟨j, h⟩ else if i = j then 1 else 0

/-- **Simulation**: in exact arithmetic, the steps `k < r` of Algorithm 3.2.1 on a square matrix
act on its first `r` columns as the steps of (3.2.8) on a tall matrix holding them, and the steps
`k ≥ r` leave those columns alone. -/
private theorem foldl_outerProductStep_castLE (hrn : r ≤ n) (l : List (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (T : Matrix (Fin n) (Fin r) ℝ)
    (hST : ∀ i j, S i (Fin.castLE hrn j) = T i j) (i : Fin n) (j : Fin r) :
    l.foldl (fun S k => Id.run (outerProductStep pure k S)) S i (Fin.castLE hrn j) =
      (l.filterMap fun k : Fin n => if h : (k : ℕ) < r then some (⟨k, h⟩ : Fin r) else none).foldl
        (fun T k => Id.run (tallOuterProductStep pure hrn k T)) T i j := by
  induction l generalizing S T with
  | nil => exact hST i j
  | cons k l ih =>
    rw [List.foldl_cons, List.filterMap_cons]
    obtain ⟨h₁, h₂, h₃⟩ := outerProductStep_exact k S
    by_cases hk : (k : ℕ) < r
    · rw [dite_eq_left hk]
      simp only [List.foldl_cons]
      refine ih _ _ fun i j => ?_
      set k' : Fin r := ⟨k, hk⟩
      have hkk : Fin.castLE hrn k' = k := Fin.ext rfl
      obtain ⟨g₁, g₂, g₃⟩ := tallOuterProductStep_exact hrn k' T
      rw [hkk] at g₁ g₂ g₃
      have hjk : Fin.castLE hrn j = k ↔ j = k' := by
        rw [← hkk]; exact (Fin.castLE_injective hrn).eq_iff
      have hlt : k < Fin.castLE hrn j ↔ k' < j := by
        rw [← hkk]; exact Fin.castLE_lt_castLE_iff hrn
      have hST' : ∀ i, S i k = T i k' := fun i => hkk ▸ hST i k'
      by_cases hij : k < i ∧ (Fin.castLE hrn j = k ∨ k < Fin.castLE hrn j)
      · rcases hij with ⟨hi, hj | hj⟩
        · obtain rfl : j = k' := hjk.1 hj
          rw [hkk, h₂ i hi, g₂ i hi, hST' i, hST' k]
        · rw [h₃ i _ hi hj, g₃ i j hi (hlt.1 hj), h₂ i hi, g₂ i hi,
            h₁ k _ fun h => lt_irrefl _ h.1, g₁ k j fun h => lt_irrefl _ h.1, hST, hST, hST' i,
            hST' k]
      · rw [h₁ i _ hij, g₁ i j fun h => hij ⟨h.1, h.2.imp (fun h' => hjk.2 h') hlt.2⟩, hST]
    · rw [dite_eq_right hk]
      refine ih _ _ fun i j => ?_
      have hjr : ((Fin.castLE hrn j : Fin n) : ℕ) < r := by simp
      rw [h₁ i _ fun h => ?_, hST]
      rcases h.2 with h | h
      · exact hk (by rw [← h]; exact hjr)
      · exact hk (lt_trans (Fin.lt_def.1 h) hjr)


/-- The strict leading principal submatrices of the bordered matrix `[A | [0; I]]` are nonsingular
when the leading blocks of `A` of order `≤ r` are: below order `r` they are those blocks, beyond it
block lower triangular with diagonal blocks `A(1:r,1:r)` and `I`. -/
private theorem tallBorder_det_ne_zero (hrn : r ≤ n) {A : Matrix (Fin n) (Fin r) ℝ}
    (hA : ∀ k (hk : k ≤ r), (A.submatrix (Fin.castLE (hk.trans hrn)) (Fin.castLE hk)).det ≠ 0)
    (k : Fin n) : ((tallBorder A).strictLeadingPrincipalSubmatrix k).det ≠ 0 := by
  let e : Fin k ≃ {i : Fin n // i < k} :=
    { toFun := fun a => ⟨⟨a, by omega⟩, Fin.lt_def.2 a.2⟩
      invFun := fun i => ⟨i.1, Fin.lt_def.1 i.2⟩
      left_inv := fun a => rfl
      right_inv := fun i => rfl }
  rw [← det_submatrix_equiv_self e]
  by_cases hkr : (k : ℕ) ≤ r
  · convert hA k hkr using 2
    ext a b
    simp only [submatrix_apply, strictLeadingPrincipalSubmatrix, toBlock_apply, tallBorder, e,
      Equiv.coe_fn_mk, of_apply]
    rw [dite_eq_left (by omega)]
    rfl
  · let e₂ : Fin r ⊕ Fin (k - r) ≃ Fin k := finSumFinEquiv.trans (finCongr (by omega))
    rw [← det_submatrix_equiv_self e₂, ← fromBlocks_toBlocks (submatrix _ e₂ e₂)]
    have h₁₂ : ((((tallBorder A).strictLeadingPrincipalSubmatrix k).submatrix e e).submatrix
        e₂ e₂).toBlocks₁₂ = 0 := by
      ext a b
      simp only [toBlocks₁₂, submatrix_apply, strictLeadingPrincipalSubmatrix, toBlock_apply,
        tallBorder, e, e₂, Equiv.coe_fn_mk, of_apply, Equiv.trans_apply, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, finCongr_apply,
        Matrix.zero_apply]
      rw [dite_eq_right (by simp),
        ite_eq_right (by intro h; have := congrArg Fin.val h; simp at this; omega)]
    have h₂₂ : ((((tallBorder A).strictLeadingPrincipalSubmatrix k).submatrix e e).submatrix
        e₂ e₂).toBlocks₂₂ = 1 := by
      ext a b
      simp only [toBlocks₂₂, submatrix_apply, strictLeadingPrincipalSubmatrix, toBlock_apply,
        tallBorder, e, e₂, Equiv.coe_fn_mk, of_apply, Equiv.trans_apply,
        finSumFinEquiv_apply_right, finCongr_apply, one_apply]
      rw [dite_eq_right (by simp)]
      by_cases hab : a = b
      · subst hab; simp
      · rw [ite_eq_right hab, ite_eq_right]
        intro h
        exact hab (Fin.ext (by have := congrArg Fin.val h; simp at this; omega))
    have h₁₁ : ((((tallBorder A).strictLeadingPrincipalSubmatrix k).submatrix e e).submatrix
        e₂ e₂).toBlocks₁₁ = A.submatrix (Fin.castLE (le_rfl.trans hrn)) (Fin.castLE le_rfl) := by
      ext a b
      simp only [toBlocks₁₁, submatrix_apply, strictLeadingPrincipalSubmatrix, toBlock_apply,
        tallBorder, e, e₂, Equiv.coe_fn_mk, of_apply, Equiv.trans_apply,
        finSumFinEquiv_apply_left, finCongr_apply]
      rw [dite_eq_left (by simp)]
      rfl
    rw [h₁₂, h₂₂, h₁₁, det_fromBlocks_zero₁₂, det_one, mul_one]
    exact hA r le_rfl

/-- The unit lower trapezoidal factor `L ∈ ℝ^{n×r}` held by the output `F` of (3.2.8): the strictly
lower part of `F`, ones on the diagonal, zeros above it. -/
def tallPackedL (F : Matrix (Fin n) (Fin r) ℝ) : Matrix (Fin n) (Fin r) ℝ :=
  of fun i k => if (k : ℕ) < i then F i k else if (i : ℕ) = k then 1 else 0

/-- The upper triangular factor `U ∈ ℝ^{r×r}` held by the output `F` of (3.2.8): the upper
triangular part of its first `r` rows. -/
def tallPackedU (hrn : r ≤ n) (F : Matrix (Fin n) (Fin r) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  of fun i k => if i ≤ k then F (Fin.castLE hrn i) k else 0

/-- **(3.2.8) computes a rectangular LU factorization**: if `A(1:k,1:k)` is nonsingular for
`k = 1:r` (the order-`0` block is empty), the exact output of (3.2.8) holds a rectangular LU
factorization `A = L U`, `L ∈ ℝ^{n×r}` unit lower trapezoidal (`tallPackedL`), `U ∈ ℝ^{r×r}`
upper triangular (`tallPackedU`). Proof: on the bordered square matrix `[A | [0; I]]`, whose strict
leading principal submatrices are nonsingular, the first `r` columns of Algorithm 3.2.1 perform
the operations of (3.2.8) (a simulation in exact arithmetic), and its LU factorization
(`algorithm_3_2_1_spec`) restricted to the first `r` columns is `A = L U`. -/
theorem equation_3_2_8 (hrn : r ≤ n) {A : Matrix (Fin n) (Fin r) ℝ}
    (hA : ∀ k (hk : k ≤ r), (A.submatrix (Fin.castLE (hk.trans hrn)) (Fin.castLE hk)).det ≠ 0) :
    IsRectLU A (tallPackedL (Id.run (tallOuterProductLU pure hrn A)))
      (tallPackedU hrn (Id.run (tallOuterProductLU pure hrn A))) := by
  set F := Id.run (tallOuterProductLU pure hrn A) with hF
  set G := Id.run (algorithm_3_2_1 pure (tallBorder A)) with hG
  have hBA : ∀ i j, tallBorder A i (Fin.castLE hrn j) = A i j := fun i j => by
    simp [tallBorder]
  have hGF : ∀ i j, G i (Fin.castLE hrn j) = F i j := fun i j => by
    have h := foldl_outerProductStep_castLE hrn (List.finRange n) (tallBorder A) A hBA i j
    rw [filterMap_finRange_lt hrn] at h
    rw [hG, hF, tallOuterProductLU_eq_foldlM, algorithm_3_2_1, List.idRun_foldlM,
      List.idRun_foldlM]
    exact h
  have hLU := algorithm_3_2_1_spec (tallBorder_det_ne_zero hrn hA)
  rw [← hG] at hLU
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun i j hij => ?_, ?_⟩
  · simp only [tallPackedL, of_apply]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · simp only [tallPackedL, of_apply]
    rw [ite_eq_right (by omega), ite_eq_left hij]
  · simp only [tallPackedU, of_apply]
    rw [ite_eq_right (by rw [Fin.le_def]; omega)]
  · ext i j
    have h := congrFun (congrFun hLU.mul_eq i) (Fin.castLE hrn j)
    rw [hBA, mul_apply] at h
    rw [mul_apply, ← h]
    refine Fintype.sum_of_injective (Fin.castLE hrn) (Fin.castLE_injective hrn) _ _
      (fun t ht => ?_) (fun t => ?_)
    · have htr : r ≤ (t : ℕ) := by
        by_contra hcon
        exact ht ⟨⟨t, by omega⟩, Fin.ext rfl⟩
      rw [packedU_apply_of_lt G (Fin.lt_def.2 (by simp; omega)), mul_zero]
    · congr 1
      · simp only [tallPackedL, of_apply]
        by_cases hti : (t : ℕ) < i
        · rw [ite_eq_left hti, packedL_apply_of_lt G (Fin.lt_def.2 (by simpa using hti)), hGF]
        · rw [ite_eq_right hti]
          by_cases hit : (i : ℕ) = t
          · rw [ite_eq_left hit, show Fin.castLE hrn t = i from Fin.ext (by simp [hit]),
              packedL_apply_self]
          · rw [ite_eq_right hit, packedL_apply_of_lt' G (Fin.lt_def.2 (by simp; omega))]
      · simp only [tallPackedU, of_apply]
        by_cases htj : t ≤ j
        · rw [ite_eq_left htj, packedU_apply_of_le G ((Fin.castLE_le_castLE_iff hrn).2 htj), hGF]
        · rw [ite_eq_right htj,
            packedU_apply_of_lt G ((Fin.castLE_lt_castLE_iff hrn).2 (not_le.1 htj))]

end TallLU

/-! ### Algorithm 3.2.3: exact semantics -/

section BlockLUSpec

/-- A loop writing column `c` with a vector `g c` fixed in advance sets the listed columns. -/
private theorem foldl_updateCol_const {m q : ℕ} (g : Fin q → Fin m → ℝ) (l : List (Fin q))
    (X₀ : Matrix (Fin m) (Fin q) ℝ) (i : Fin m) (c : Fin q) :
    l.foldl (fun (X : Matrix (Fin m) (Fin q) ℝ) c => X.updateCol c (g c)) X₀ i c =
      if c ∈ l then g c i else X₀ i c := by
  induction l generalizing X₀ with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    by_cases hc : c ∈ l <;> by_cases hca : c = a <;> simp [hc, hca]

/-- A double loop writing entry `(i, j)` with a value `g i j` fixed in advance sets the listed
entries. -/
private theorem foldl_foldl_updateEntry_const {m q : ℕ} (g : Fin m → Fin q → ℝ)
    (R : List (Fin m)) (C : List (Fin q)) (X₀ : Matrix (Fin m) (Fin q) ℝ) (i : Fin m)
    (j : Fin q) :
    R.foldl (fun (X : Matrix (Fin m) (Fin q) ℝ) i =>
        C.foldl (fun (X : Matrix (Fin m) (Fin q) ℝ) j =>
          X.updateRow i (Function.update (X i) j (g i j))) X) X₀ i j =
      if i ∈ R ∧ j ∈ C then g i j else X₀ i j := by
  have hrow : ∀ (a : Fin m) (X : Matrix (Fin m) (Fin q) ℝ) (i : Fin m) (j : Fin q),
      C.foldl (fun (X : Matrix (Fin m) (Fin q) ℝ) j =>
        X.updateRow a (Function.update (X a) j (g a j))) X i j =
      if i = a ∧ j ∈ C then g a j else X i j := by
    intro a
    induction C with
    | nil => intro X i j; simp
    | cons b C ih =>
      intro X i j
      rw [List.foldl_cons, ih]
      by_cases hia : i = a
      · subst hia
        by_cases hj : j ∈ C
        · simp [hj]
        · by_cases hjb : j = b
          · subst hjb; simp [hj]
          · simp [hj, hjb]
      · simp [hia]
  induction R generalizing X₀ with
  | nil => simp
  | cons a R ih =>
    rw [List.foldl_cons, ih, hrow]
    by_cases hi : i ∈ R
    · by_cases hj : j ∈ C <;> simp [hi, hj]
    · by_cases hia : i = a
      · subst hia; simp [hi]
      · simp [hi, hia]

/-- An LU factorization of a block matrix read on `Fin n` through `finSumFinEquiv` followed by a
cast of `Fin (r + s)` to `Fin n` (an order isomorphism). -/
private theorem isLU_reindex_finSumFinEquiv_trans {r s n : ℕ} (h : r + s = n)
    {A L U : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ}
    (hLU : IsLU (reindex finSumFinEquiv finSumFinEquiv A) (reindex finSumFinEquiv finSumFinEquiv L)
      (reindex finSumFinEquiv finSumFinEquiv U)) :
    IsLU (reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h)) A)
      (reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h)) L)
      (reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h)) U) := by
  rw [← isBlockLU_id_iff, isBlockLU_reindex_iff] at hLU ⊢
  exact (isBlockLU_comp_iff (f := finCongr h) (b := id ∘ finSumFinEquiv)
    (fun a b hab => hab)).2 hLU

/-- **Exact correctness of Algorithm 3.2.3**: if `A(1:k,1:k)` is nonsingular for `k = 1:n-1` (the
book's "A has an LU factorization" does not prevent a zero pivot, e.g. `!![0, 1; 0, 1]`), the exact
output `(L, U)` of the recursive block LU is the LU factorization `A = L U`. Strong induction on
`n`: the block column is factored by (3.2.8) (`equation_3_2_8`), `U₁₂` solves `L₁₁ U₁₂ = A₁₂`
(`algorithm_3_1_3_spec`), `Ã = A₂₂ - L₂₁ U₁₂` has nonsingular strict leading blocks (their
determinants times `det U₁₁` are those of `A`, by (3.2.9)), and the factors assemble by
`blockLU_of_schur`. -/
theorem algorithm_3_2_3_spec (r : ℕ) (hr : 0 < r) {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ k : Fin n, (A.strictLeadingPrincipalSubmatrix k).det ≠ 0) :
    IsLU A (Id.run (algorithm_3_2_3 pure r hr n A)).1
      (Id.run (algorithm_3_2_3 pure r hr n A)).2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [algorithm_3_2_3]
  by_cases h : n ≤ r
  · rw [dite_eq_left h]
    exact algorithm_3_2_1_spec hA
  rw [dite_eq_right h]
  have hrn : r ≤ n := by omega
  have hrs : r + (n - r) = n := by omega
  set e : Fin r ⊕ Fin (n - r) ≃ Fin n := finSumFinEquiv.trans (finCongr hrs) with he
  set A₁ : Matrix (Fin n) (Fin r) ℝ := fun i k => A i (e (Sum.inl k)) with hA₁
  set F := Id.run (tallOuterProductLU pure hrn A₁) with hF
  set L₁₁ : Matrix (Fin r) (Fin r) ℝ :=
    of fun i k => if k < i then F (e (Sum.inl i)) k else if i = k then 1 else 0 with hL₁₁
  set L₂₁ : Matrix (Fin (n - r)) (Fin r) ℝ := of fun i k => F (e (Sum.inr i)) k with hL₂₁
  set U₁₁ : Matrix (Fin r) (Fin r) ℝ :=
    of fun i k => if i ≤ k then F (e (Sum.inl i)) k else 0 with hU₁₁
  set U₁₂ : Matrix (Fin r) (Fin (n - r)) ℝ := Id.run ((List.finRange (n - r)).foldlM
    (fun (U₁₂ : Matrix (Fin r) (Fin (n - r)) ℝ) c => do
      let col ← algorithm_3_1_3 pure L₁₁ (fun i => A (e (Sum.inl i)) (e (Sum.inr c)))
      pure (U₁₂.updateCol c col)) 0) with hU₁₂
  set Ã : Matrix (Fin (n - r)) (Fin (n - r)) ℝ := Id.run ((List.finRange (n - r)).foldlM
    (fun (Ã : Matrix (Fin (n - r)) (Fin (n - r)) ℝ) i =>
      (List.finRange (n - r)).foldlM (fun (Ã : Matrix (Fin (n - r)) (Fin (n - r)) ℝ) j => do
        let s ← dotAccum pure (List.finRange r) (L₂₁ i) (fun k => U₁₂ k j) 0
        let a ← pure (A (e (Sum.inr i)) (e (Sum.inr j)) - s)
        pure (Ã.updateRow i (Function.update (Ã i) j a))) Ã) 0) with hÃ
  set LU₂₂ := Id.run (algorithm_3_2_3 pure r hr (n - r) Ã) with hLU₂₂
  change IsLU A (reindex e e (fromBlocks L₁₁ 0 L₂₁ LU₂₂.1))
    (reindex e e (fromBlocks U₁₁ U₁₂ 0 LU₂₂.2))
  -- the blocks of `A`
  set A₁₁ : Matrix (Fin r) (Fin r) ℝ := A.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl) with hA₁₁
  set A₁₂ : Matrix (Fin r) (Fin (n - r)) ℝ := A.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr) with hA₁₂
  set A₂₁ : Matrix (Fin (n - r)) (Fin r) ℝ := A.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl) with hA₂₁
  set A₂₂ : Matrix (Fin (n - r)) (Fin (n - r)) ℝ := A.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)
    with hA₂₂
  have hval_l : ∀ i : Fin r, ((e (Sum.inl i) : Fin n) : ℕ) = i := fun i => by simp [he]
  have hval_r : ∀ i : Fin (n - r), ((e (Sum.inr i) : Fin n) : ℕ) = r + i := fun i => by simp [he]
  -- (3.2.8) on the block column
  have hA₁det : ∀ k (hk : k ≤ r),
      (A₁.submatrix (Fin.castLE (hk.trans hrn)) (Fin.castLE hk)).det ≠ 0 := by
    intro k hk
    have hkn : k < n := by omega
    have h1 : A₁.submatrix (Fin.castLE (hk.trans hrn)) (Fin.castLE hk) =
        A.submatrix (Fin.castLE (⟨k, hkn⟩ : Fin n).isLt.le)
          (Fin.castLE (⟨k, hkn⟩ : Fin n).isLt.le) := by
      ext a b
      rfl
    rw [h1, ← det_strictLeadingPrincipalSubmatrix_castLE]
    exact hA ⟨k, hkn⟩
  have hRect := equation_3_2_8 hrn hA₁det
  rw [← hF] at hRect
  have hmul : ∀ i j, A i (e (Sum.inl j)) =
      ∑ t, tallPackedL F i t * tallPackedU hrn F t j := fun i j => by
    rw [← mul_apply, hRect.mul_eq]
  have hL₁₁' : ∀ i t, L₁₁ i t = tallPackedL F (e (Sum.inl i)) t := fun i t => by
    simp only [hL₁₁, tallPackedL, of_apply, hval_l, Fin.lt_def, Fin.ext_iff]
  have hL₂₁' : ∀ i t, L₂₁ i t = tallPackedL F (e (Sum.inr i)) t := fun i t => by
    simp only [hL₂₁, tallPackedL, of_apply, hval_r]
    rw [ite_eq_left (by omega)]
  have hU₁₁' : U₁₁ = tallPackedU hrn F := by
    ext i k
    simp only [hU₁₁, tallPackedU, of_apply]
    congr 2
  have h₁₁mul : A₁₁ = L₁₁ * U₁₁ := by
    ext i j
    rw [hA₁₁, submatrix_apply, Function.comp_apply, Function.comp_apply, hmul, mul_apply, hU₁₁']
    simp only [hL₁₁']
  have h₂₁ : A₂₁ = L₂₁ * U₁₁ := by
    ext i j
    rw [hA₂₁, submatrix_apply, Function.comp_apply, Function.comp_apply, hmul, mul_apply, hU₁₁']
    simp only [hL₂₁']
  have hL₁₁unit : L₁₁.IsUnitLowerTriangular := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      simp only [hL₁₁, of_apply]
      rw [ite_eq_right (not_lt.2 hij'.le), ite_eq_right hij'.ne]
    · simp [hL₁₁]
  have hU₁₁upper : U₁₁.IsUpperTriangular := fun i j hij => by
    simp only [hU₁₁, of_apply]
    rw [ite_eq_right (not_le.2 (show j < i from hij))]
  have h₁₁ : IsLU A₁₁ L₁₁ U₁₁ := ⟨hL₁₁unit, hU₁₁upper, h₁₁mul.symm⟩
  -- the multiple right-hand side solve
  have hU₁₂' : ∀ i c, U₁₂ i c =
      Id.run (algorithm_3_1_3 pure L₁₁ (fun i => A (e (Sum.inl i)) (e (Sum.inr c)))) i := by
    intro i c
    rw [hU₁₂, List.idRun_foldlM]
    exact (foldl_updateCol_const (fun c => Id.run (algorithm_3_1_3 pure L₁₁
      (fun i => A (e (Sum.inl i)) (e (Sum.inr c))))) (List.finRange (n - r)) 0 i c).trans
      (ite_eq_left (List.mem_finRange c))
  have h₁₂ : L₁₁ * U₁₂ = A₁₂ := by
    ext i c
    have hsol := algorithm_3_1_3_spec hL₁₁unit.isLowerTriangular
      (fun i => by rw [hL₁₁unit.diag_eq_one]; exact one_ne_zero)
      (fun i => A (e (Sum.inl i)) (e (Sum.inr c)))
    have := congrFun hsol i
    rw [mulVec, dotProduct] at this
    rw [mul_apply, hA₁₂, submatrix_apply, Function.comp_apply, Function.comp_apply, ← this]
    simp only [hU₁₂']
  -- the Schur complement
  have hÃ' : Ã = A₂₂ - L₂₁ * U₁₂ := by
    ext i j
    rw [hÃ, List.idRun_foldlM]
    simp only [List.idRun_foldlM, Id.run_bind, Id.run_pure, dotAccum_id_finRange, zero_add]
    rw [foldl_foldl_updateEntry_const (fun i j => A (e (Sum.inr i)) (e (Sum.inr j)) -
      L₂₁ i ⬝ᵥ fun k => U₁₂ k j), ite_eq_left ⟨List.mem_finRange i, List.mem_finRange j⟩]
    simp [hA₂₂, mul_apply, dotProduct]
  -- the strict leading blocks of `Ã`
  have hdetU : U₁₁.det ≠ 0 := by
    have h1 := hA ⟨r, by omega⟩
    rw [det_strictLeadingPrincipalSubmatrix_castLE] at h1
    have h2 : A.submatrix (Fin.castLE (⟨r, by omega⟩ : Fin n).isLt.le)
        (Fin.castLE (⟨r, by omega⟩ : Fin n).isLt.le) = A₁₁ := by
      ext a b
      simp only [submatrix_apply, hA₁₁, Function.comp_apply]
      congr 1
    rw [h2, h₁₁mul, det_mul, h₁₁.isUnitLowerTriangular.det_eq_one, one_mul] at h1
    exact h1
  have hÃdet : ∀ k : Fin (n - r), (Ã.strictLeadingPrincipalSubmatrix k).det ≠ 0 := by
    intro k
    have hk : (k : ℕ) ≤ n - r := k.isLt.le
    have hp : r + k < n := by omega
    set c : Fin k → Fin (n - r) := Fin.castLE hk with hc
    have h9 := (equation_3_2_9 (A₂₂.submatrix c c) (A₁₂ := A₁₂.submatrix id c)
      (A₂₁ := A₂₁.submatrix c id) (L₂₁ := L₂₁.submatrix c id) (U₁₂ := U₁₂.submatrix id c)
      h₁₁mul (by rw [h₂₁]; rfl) (by rw [← h₁₂]; rfl)).1
    have hblk : (A.submatrix (Fin.castLE (⟨r + k, hp⟩ : Fin n).isLt.le)
        (Fin.castLE (⟨r + k, hp⟩ : Fin n).isLt.le)).submatrix finSumFinEquiv finSumFinEquiv =
        fromBlocks A₁₁ (A₁₂.submatrix id c) (A₂₁.submatrix c id) (A₂₂.submatrix c c) := by
      ext (a | a) (b | b) <;>
        simp only [submatrix_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
          fromBlocks_apply₂₂, hA₁₁, hA₁₂, hA₂₁, hA₂₂, Function.comp_apply, id] <;>
        congr 1
    have h1 := hA ⟨r + k, hp⟩
    rw [det_strictLeadingPrincipalSubmatrix_castLE, ← det_submatrix_equiv_self finSumFinEquiv,
      hblk, h9, det_mul, det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₁₂,
      det_fromBlocks_zero₂₁, h₁₁.isUnitLowerTriangular.det_eq_one, det_one, det_one, one_mul,
      one_mul, one_mul, mul_one] at h1
    have h3 : A₂₂.submatrix c c - L₂₁.submatrix c id * U₁₂.submatrix id c =
        Ã.submatrix (Fin.castLE k.isLt.le) (Fin.castLE k.isLt.le) := by
      rw [hÃ']
      ext a b
      simp [mul_apply, hc]
    rw [h3] at h1
    rw [det_strictLeadingPrincipalSubmatrix_castLE]
    exact left_ne_zero_of_mul h1
  -- assembly
  have h₂₂ : IsLU (A₂₂ - L₂₁ * U₁₂) LU₂₂.1 LU₂₂.2 := by
    rw [← hÃ']
    exact ih (n - r) (by omega) hÃdet
  have hAe : A = reindex e e (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) := by
    ext i j
    rw [reindex_apply, submatrix_apply]
    rcases hi : e.symm i with i' | i' <;> rcases hj : e.symm j with j' | j' <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, hA₁₁, hA₁₂, hA₂₁, hA₂₂, submatrix_apply, Function.comp_apply] <;>
      rw [← hi, ← hj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [hAe, he]
  exact isLU_reindex_finSumFinEquiv_trans hrs (blockLU_of_schur h₁₁ h₂₁ h₁₂ h₂₂)

end BlockLUSpec

/-! ### Algorithm 3.2.4 (Nonrecursive Block LU) -/

section NonrecursiveBlockLU

section Program

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 3.2.4 (Nonrecursive Block LU).** "Suppose `A ∈ ℝ^{n×n}` has an LU factorization
and `r` is a positive integer. The following algorithm computes unit lower triangular
`L ∈ ℝ^{n×n}` and upper triangular `U ∈ ℝ^{n×n}` so `A = LU`."
```
for k = 1:N
    Rectangular Gaussian elimination:  [A_kk; …; A_Nk] = [L_kk; …; L_Nk] U_kk
    Multiple right hand side solve:    L_kk [U_{k,k+1} | … | U_kN] = [A_{k,k+1} | … | A_kN]
    Level-3 updates:                   A_ij = A_ij - L_ik U_kj,  i = k+1:N, j = k+1:N
end
```
For `n = N r` ("for clarity"), the blocks are `r` consecutive indices: the block of
`i : Fin (N * r)` is `i.divNat`. `A` is overwritten in place and its blocks are index lists of the
full matrix (convention 10): the rectangular elimination (3.2.8) of the block column is, for each
pivot `p` of block `k`, the outer product step of Algorithm 3.2.1 with its update restricted to the
columns of block `k`; the multiple right-hand side solve is Algorithm 3.1.3 on the rows of block
`k` (`forwardSubstColOn`), column by column, against the unit lower triangular `L_kk` held below
the diagonal of `A_kk`; the level-3 update is entrywise, `fl(a_ij - fl(L_ik(i,:) · U_kj(:,j)))`
with the dot product of Algorithm 1.1.1 over the indices of block `k`. The packed output is read
by `packedL` and `packedU`. -/
noncomputable def algorithm_3_2_4 {N r : ℕ} (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) :
    M (Matrix (Fin (N * r)) (Fin (N * r)) ℝ) :=
  (List.finRange N).foldlM (fun (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) k => do
    -- rectangular Gaussian elimination on the block column `A(k:N, k)`
    let A ← ((List.finRange (N * r)).filter fun i => i.divNat = k).foldlM
      (fun (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) p => do
        let A ← ((List.finRange (N * r)).filter (p < ·)).foldlM
          (fun (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) i => do
            let l ← rnd (A i p / A p p)
            pure (A.updateRow i (Function.update (A i) p l))) A
        ((List.finRange (N * r)).filter (p < ·)).foldlM
          (fun (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) i =>
            ((List.finRange (N * r)).filter fun j => j.divNat = k ∧ p < j).foldlM
              (fun (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) j => do
                let q ← rnd (A i p * A p j)
                let a ← rnd (A i j - q)
                pure (A.updateRow i (Function.update (A i) j a))) A) A) A
    -- multiple right-hand side solve with the unit lower triangular `L_kk`
    let A ← ((List.finRange (N * r)).filter fun c => k < c.divNat).foldlM
      (fun (B : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) c => do
        let x ← forwardSubstColOn rnd ((List.finRange (N * r)).filter fun i => i.divNat = k)
          (of fun i j => if j < i then A i j else if i = j then 1 else 0) fun i => B i c
        pure (B.updateCol c x)) A
    -- level-3 updates
    ((List.finRange (N * r)).filter fun i => k < i.divNat).foldlM
      (fun (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) i =>
        ((List.finRange (N * r)).filter fun j => k < j.divNat).foldlM
          (fun (A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) j => do
            let s ← dotAccum rnd ((List.finRange (N * r)).filter fun t => t.divNat = k) (A i)
              (fun t => A t j) 0
            let a ← rnd (A i j - s)
            pure (A.updateRow i (Function.update (A i) j a))) A) A) A

end Program


section Exact

variable {n : ℕ}

/-- The trailing values after the pivots below `P`: `a_ij - ∑_{t < P} ℓ_it u_tj`. -/
private def schurRest (A L U : Matrix (Fin n) (Fin n) ℝ) (P : ℕ) (i j : Fin n) : ℝ :=
  A i j - ∑ t : Fin n, if (t : ℕ) < P then L i t * U t j else 0

/-- The factors `L`, `U` packed in one matrix: `U` on and above the diagonal, `L` below. -/
private def packLU (L U : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if j < i then L i j else U i j

section Schur

variable {A L U : Matrix (Fin n) (Fin n) ℝ} (hLU : IsLU A L U)
include hLU

private theorem schurRest_eq (P : ℕ) (i j : Fin n) :
    schurRest A L U P i j = ∑ t : Fin n, if P ≤ (t : ℕ) then L i t * U t j else 0 := by
  rw [schurRest, ← hLU.mul_eq, mul_apply, sub_eq_iff_eq_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : (t : ℕ) < P
  · rw [ite_eq_right (by omega), ite_eq_left h, zero_add]
  · rw [ite_eq_left (by omega), ite_eq_right h, add_zero]

private theorem schurRest_row (p j : Fin n) : schurRest A L U p p j = U p j := by
  rw [schurRest_eq hLU, Finset.sum_eq_single p]
  · rw [ite_eq_left le_rfl, hLU.isUnitLowerTriangular.diag_eq_one, one_mul]
  · intro t _ htp
    by_cases h : (p : ℕ) ≤ t
    · rw [ite_eq_left h, hLU.isUnitLowerTriangular.isLowerTriangular
        (OrderDual.toDual_lt_toDual.2 (lt_of_le_of_ne (Fin.le_def.2 h) (Ne.symm htp))),
        zero_mul]
    · rw [ite_eq_right h]
  · simp

private theorem schurRest_col (p i : Fin n) : schurRest A L U p i p = L i p * U p p := by
  rw [schurRest_eq hLU, Finset.sum_eq_single p]
  · rw [ite_eq_left le_rfl]
  · intro t _ htp
    by_cases h : (p : ℕ) ≤ t
    · rw [ite_eq_left h, hLU.isUpperTriangular
        (show p < t from lt_of_le_of_ne (Fin.le_def.2 h) (Ne.symm htp)), mul_zero]
    · rw [ite_eq_right h]
  · simp

omit hLU in
private theorem schurRest_succ (p : Fin n) (i j : Fin n) :
    schurRest A L U (p + 1) i j = schurRest A L U p i j - L i p * U p j := by
  rw [schurRest, schurRest, sub_sub, ← Finset.sum_erase_add _ _ (Finset.mem_univ p),
    ← Finset.sum_erase_add (s := Finset.univ) (a := p) _ (Finset.mem_univ p),
    ite_eq_left (Nat.lt_succ_self _), ite_eq_right (lt_irrefl _), add_zero]
  congr 2
  refine Finset.sum_congr rfl fun t ht => ?_
  have htp : (t : ℕ) ≠ p := fun h => (Finset.mem_erase.1 ht).1 (Fin.ext h)
  by_cases h : (t : ℕ) < p
  · rw [ite_eq_left h, ite_eq_left (by omega)]
  · rw [ite_eq_right h, ite_eq_right (by omega)]

end Schur

/-! #### Loops of Algorithm 3.2.4 in exact arithmetic -/

/-- The division loop of the block column elimination: the listed rows of column `p` are divided
by the pivot. -/
private theorem foldl_divCol_apply (p : Fin n) {R : List (Fin n)} (hR : R.Nodup) (hpR : p ∉ R)
    (S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    R.foldl (fun (S : Matrix (Fin n) (Fin n) ℝ) i =>
        S.updateRow i (Function.update (S i) p (S i p / S p p))) S i j =
      if j = p ∧ i ∈ R then S i p / S p p else S i j := by
  induction R generalizing S with
  | nil => simp
  | cons a R ih =>
    rcases List.nodup_cons.1 hR with ⟨ha, hR'⟩
    have hpa : p ≠ a := fun h => hpR (h ▸ List.mem_cons_self)
    rw [List.foldl_cons, ih hR' fun h => hpR (List.mem_cons_of_mem _ h)]
    have hpp : (S.updateRow a (Function.update (S a) p (S a p / S p p))) p p = S p p := by
      rw [updateRow_ne hpa]
    rw [hpp]
    by_cases hia : i = a
    · subst hia
      simp only [ha, and_false, ↓reduceIte, List.mem_cons, true_or, and_true, updateRow_self,
        Function.update_apply]
    · have hi : (i ∈ a :: R) ↔ i ∈ R := by simp [hia]
      simp only [hi, updateRow_ne hia]

/-- A double loop subtracting from each listed entry `(i, j)` a quantity `g S i j` read off entries
outside the listed block writes every listed entry once, from its initial value. -/
private theorem foldl_foldl_sub_apply {R C : List (Fin n)} (hR : R.Nodup) (hC : C.Nodup)
    (g : Matrix (Fin n) (Fin n) ℝ → Fin n → Fin n → ℝ)
    (hg : ∀ S S' : Matrix (Fin n) (Fin n) ℝ, (∀ a b, ¬ (a ∈ R ∧ b ∈ C) → S a b = S' a b) →
      ∀ i j, g S i j = g S' i j)
    (S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    R.foldl (fun (S : Matrix (Fin n) (Fin n) ℝ) i =>
        C.foldl (fun (S : Matrix (Fin n) (Fin n) ℝ) j =>
        S.updateRow i (Function.update (S i) j (S i j - g S i j))) S) S i j =
      if i ∈ R ∧ j ∈ C then S i j - g S i j else S i j := by
  -- one row
  have hrow : ∀ i₀ ∈ R, ∀ (C' : List (Fin n)), C'.Nodup → (∀ b ∈ C', b ∈ C) →
      ∀ (S : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n),
      C'.foldl (fun (S : Matrix (Fin n) (Fin n) ℝ) j =>
        S.updateRow i₀ (Function.update (S i₀) j (S i₀ j - g S i₀ j))) S a b =
      if a = i₀ ∧ b ∈ C' then S i₀ b - g S i₀ b else S a b := by
    intro i₀ hi₀ C' hC' hsub
    induction C' with
    | nil => intro S a b; simp
    | cons c C' ih =>
      intro S a b
      rcases List.nodup_cons.1 hC' with ⟨hc, hC''⟩
      rw [List.foldl_cons, ih hC'' fun b hb => hsub b (List.mem_cons_of_mem _ hb)]
      set S₁ := S.updateRow i₀ (Function.update (S i₀) c (S i₀ c - g S i₀ c)) with hS₁
      have hS₁g : ∀ i j, g S₁ i j = g S i j := fun i j =>
        (hg S S₁ (fun a' b' hab => by
          rw [hS₁, updateRow_apply]
          split_ifs with h
          · rw [h, Function.update_of_ne fun h' => hab ⟨by rw [h]; exact hi₀,
              by rw [h']; exact hsub c List.mem_cons_self⟩]
          · rfl) i j).symm
      by_cases hab : a = i₀ ∧ b ∈ C'
      · have hbc : b ≠ c := fun h => hc (h ▸ hab.2)
        rw [ite_eq_left hab, ite_eq_left ⟨hab.1, List.mem_cons_of_mem _ hab.2⟩, hS₁g, hS₁,
          updateRow_self, Function.update_of_ne hbc]
      · rw [ite_eq_right hab, hS₁, updateRow_apply]
        by_cases ha : a = i₀
        · subst ha
          by_cases hbc : b = c
          · subst hbc
            simp
          · have hb : b ∉ c :: C' := by
              intro h
              rcases List.mem_cons.1 h with h | h
              · exact hbc h
              · exact hab ⟨rfl, h⟩
            simp [hb, Function.update_of_ne hbc]
        · simp [ha]
  -- all rows
  have hall : ∀ (R' : List (Fin n)), R'.Nodup → (∀ a ∈ R', a ∈ R) →
      ∀ (S : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n),
      R'.foldl (fun (S : Matrix (Fin n) (Fin n) ℝ) i =>
        C.foldl (fun (S : Matrix (Fin n) (Fin n) ℝ) j =>
          S.updateRow i (Function.update (S i) j (S i j - g S i j))) S) S a b =
      if a ∈ R' ∧ b ∈ C then S a b - g S a b else S a b := by
    intro R' hR' hsub
    induction R' with
    | nil => intro S a b; simp
    | cons c R' ih =>
      intro S a b
      rcases List.nodup_cons.1 hR' with ⟨hc, hR''⟩
      rw [List.foldl_cons, ih hR'' fun a ha => hsub a (List.mem_cons_of_mem _ ha)]
      have hrowc := hrow c (hsub c List.mem_cons_self) C hC fun b hb => hb
      set S₁ := C.foldl (fun (S : Matrix (Fin n) (Fin n) ℝ) j =>
        S.updateRow c (Function.update (S c) j (S c j - g S c j))) S with hS₁
      have hS₁g : ∀ i j, g S₁ i j = g S i j := fun i j =>
        (hg S S₁ (fun a' b' hab => by
          rw [hS₁, hrowc, ite_eq_right (show ¬ (a' = c ∧ b' ∈ C) from fun h =>
            hab ⟨by rw [h.1]; exact hsub c List.mem_cons_self, h.2⟩)])
          i j).symm
      by_cases hab : a ∈ R' ∧ b ∈ C
      · have hac : a ≠ c := fun h => hc (h ▸ hab.1)
        rw [ite_eq_left hab, ite_eq_left ⟨List.mem_cons_of_mem _ hab.1, hab.2⟩, hS₁g, hS₁,
          hrowc, ite_eq_right fun h => hac h.1]
      · rw [ite_eq_right hab, hS₁, hrowc]
        by_cases hac : a = c
        · subst hac
          simp
        · have : ¬ (a ∈ c :: R' ∧ b ∈ C) := fun h =>
            hab ⟨(List.mem_cons.1 h.1).resolve_left hac, h.2⟩
          rw [ite_eq_right fun h => hac h.1, ite_eq_right this]
  exact hall R hR (fun a ha => ha) S i j

/-- Uniqueness of the solution of a unit lower triangular system on a sorted index list: two
vectors satisfying the same equations `∑_{j ∈ o} L(i,j) x(j) = b(i)`, `i ∈ o`, agree on `o`. -/
private theorem eq_on_of_sum_eq {o : List (Fin n)} (ho : o.Pairwise (· < ·))
    {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular) (hd : ∀ i ∈ o, L i i ≠ 0)
    {y z : Fin n → ℝ}
    (h : ∀ i ∈ o, (o.map fun j => L i j * y j).sum = (o.map fun j => L i j * z j).sum) :
    ∀ i ∈ o, y i = z i := by
  have hnd : o.Nodup := ho.imp ne_of_lt
  suffices H : ∀ m : ℕ, ∀ i ∈ o, (i : ℕ) = m → y i = z i from fun i hi => H i i hi rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro i hi him
  have key : ∑ j ∈ o.toFinset, L i j * (y j - z j) = 0 := by
    rw [Finset.sum_congr rfl fun j _ => mul_sub (L i j) (y j) (z j), Finset.sum_sub_distrib,
      List.sum_toFinset _ hnd, List.sum_toFinset _ hnd, h i hi, sub_self]
  rw [Finset.sum_eq_single i] at key
  · exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left (hd i hi))
  · intro j hj hji
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · rw [ih j (him ▸ Fin.lt_def.1 hlt) j (List.mem_toFinset.1 hj) rfl, sub_self, mul_zero]
    · rw [hL (OrderDual.toDual_lt_toDual.2 hgt), zero_mul]
  · intro h
    exact absurd (List.mem_toFinset.2 hi) h

/-- One pivot `p` of the block column elimination of Algorithm 3.2.4, in exact arithmetic: if the
columns of the block (`B j`) hold the finished factors where `min(i,j) < p` and the trailing values
`a_ij - ∑_{t<p} ℓ_it u_tj` elsewhere, then after the division and the update restricted to the
block they do so with `p + 1`; the other columns are untouched. -/
private theorem elimStep {A L U : Matrix (Fin n) (Fin n) ℝ} (hLU : IsLU A L U)
    (hpiv : ∀ p i : Fin n, p < i → U p p ≠ 0) (B : Fin n → Prop) [DecidablePred B] (p : Fin n)
    (hp : B p) (S₀ E : Matrix (Fin n) (Fin n) ℝ)
    (hE : ∀ i j, E i j = if B j then (if ((min i j : Fin n) : ℕ) < p then packLU L U i j
      else schurRest A L U p i j) else S₀ i j) (i j : Fin n) :
    ((List.finRange n).filter (p < ·)).foldl (fun (S : Matrix (Fin n) (Fin n) ℝ) i =>
        ((List.finRange n).filter fun j => B j ∧ p < j).foldl
          (fun (S : Matrix (Fin n) (Fin n) ℝ) j =>
            S.updateRow i (Function.update (S i) j (S i j - S i p * S p j))) S)
      (((List.finRange n).filter (p < ·)).foldl (fun (S : Matrix (Fin n) (Fin n) ℝ) i =>
        S.updateRow i (Function.update (S i) p (S i p / S p p))) E) i j =
    if B j then (if ((min i j : Fin n) : ℕ) < p + 1 then packLU L U i j
      else schurRest A L U (p + 1) i j) else S₀ i j := by
  set R := (List.finRange n).filter (p < ·) with hR
  set C := (List.finRange n).filter fun j => B j ∧ p < j with hC
  have hmemR : ∀ i, i ∈ R ↔ p < i := fun i => by simp [hR]
  have hmemC : ∀ j, j ∈ C ↔ B j ∧ p < j := fun j => by simp [hC]
  have hpR : p ∉ R := fun h => lt_irrefl p ((hmemR p).1 h)
  have hpC : p ∉ C := fun h => lt_irrefl p ((hmemC p).1 h).2
  set E₁ := R.foldl (fun (S : Matrix (Fin n) (Fin n) ℝ) i =>
    S.updateRow i (Function.update (S i) p (S i p / S p p))) E with hE₁def
  have hE₁ : ∀ i j, E₁ i j = if j = p ∧ i ∈ R then E i p / E p p else E i j := fun i j =>
    foldl_divCol_apply p ((List.nodup_finRange n).filter _) hpR E i j
  rw [foldl_foldl_sub_apply ((List.nodup_finRange n).filter _) ((List.nodup_finRange n).filter _)
    (fun S i j => S i p * S p j) (fun S S' hSS' i j => by
      rw [hSS' i p fun h => hpC h.2, hSS' p j fun h => hpR h.1]) E₁ i j]
  -- the entries of `E` the step reads
  have hEpp : E p p = U p p := by
    rw [hE, ite_eq_left hp, ite_eq_right (by simp), schurRest_row hLU]
  have hEip : ∀ i, p < i → E i p = L i p * U p p := fun i hi => by
    rw [hE, ite_eq_left hp, ite_eq_right (by simp [Fin.val_min, le_of_lt (Fin.lt_def.1 hi)]),
      schurRest_col hLU]
  have hEpj : ∀ j, B j → p ≤ j → E p j = U p j := fun j hj hpj => by
    rw [hE, ite_eq_left hj, ite_eq_right (by simp [Fin.val_min, Fin.le_def.1 hpj]),
      schurRest_row hLU]
  have hE₁ip : ∀ i, p < i → E₁ i p = L i p := fun i hi => by
    rw [hE₁, ite_eq_left ⟨rfl, (hmemR i).2 hi⟩, hEip i hi, hEpp,
      mul_div_cancel_right₀ _ (hpiv p i hi)]
  by_cases hij : i ∈ R ∧ j ∈ C
  · rw [ite_eq_left hij]
    have hi := (hmemR i).1 hij.1
    obtain ⟨hBj, hj⟩ := (hmemC j).1 hij.2
    have hi' := Fin.lt_def.1 hi
    have hj' := Fin.lt_def.1 hj
    have hmin : ¬ ((min i j : Fin n) : ℕ) < p + 1 := by
      simp only [Fin.val_min]; omega
    have hEij : E i j = schurRest A L U p i j := by
      rw [hE, ite_eq_left hBj, ite_eq_right (by simp only [Fin.val_min]; omega)]
    have hE₁ij : E₁ i j = schurRest A L U p i j := by
      rw [hE₁, ite_eq_right (fun h => ne_of_gt hj h.1), hEij]
    have hE₁pj : E₁ p j = U p j := by
      rw [hE₁, ite_eq_right (fun h => hpR h.2), hEpj j hBj hj.le]
    rw [hE₁ij, hE₁ip i hi, hE₁pj, ite_eq_left hBj, ite_eq_right hmin, schurRest_succ]
  · rw [ite_eq_right hij, hE₁]
    by_cases hjp : j = p ∧ i ∈ R
    · rw [ite_eq_left hjp]
      obtain ⟨rfl, hi⟩ := hjp
      have hi' := (hmemR i).1 hi
      have hi'' := Fin.lt_def.1 hi'
      rw [hEip i hi', hEpp, mul_div_cancel_right₀ _ (hpiv j i hi'), ite_eq_left hp,
        ite_eq_left (by simp only [Fin.val_min]; omega)]
      simp only [packLU, of_apply]
      rw [ite_eq_left hi']
    · rw [ite_eq_right hjp, hE]
      by_cases hBj : B j
      · simp only [hBj, ↓reduceIte]
        by_cases hlt : ((min i j : Fin n) : ℕ) < p
        · rw [ite_eq_left hlt, ite_eq_left (by omega)]
        · rw [ite_eq_right hlt]
          have hmin : ((min i j : Fin n) : ℕ) = p := by
            by_contra hne
            have hgt : (p : ℕ) < i ∧ (p : ℕ) < j := by
              simp only [Fin.val_min] at hlt hne; omega
            exact hij ⟨(hmemR i).2 (Fin.lt_def.2 hgt.1),
              (hmemC j).2 ⟨hBj, Fin.lt_def.2 hgt.2⟩⟩
          rw [ite_eq_left (by omega)]
          by_cases hip : (i : ℕ) = p
          · obtain rfl : i = p := Fin.ext hip
            have hij' : (i : ℕ) ≤ j := by simp only [Fin.val_min] at hmin; omega
            rw [schurRest_row hLU]
            simp only [packLU, of_apply]
            rw [ite_eq_right (not_lt.2 (Fin.le_def.2 hij'))]
          · exfalso
            simp only [Fin.val_min] at hmin
            exact hjp ⟨Fin.ext (by omega), (hmemR i).2 (Fin.lt_def.2 (by omega))⟩
      · simp only [hBj, ↓reduceIte]


/-- Removing the pivots of one block from the trailing values. -/
private theorem schurRest_add_block {A L U : Matrix (Fin n) (Fin n) ℝ} (K r : ℕ)
    (B : Fin n → Prop) [DecidablePred B] (hB : ∀ t : Fin n, B t ↔ K ≤ (t : ℕ) ∧ (t : ℕ) < K + r)
    (i j : Fin n) :
    schurRest A L U (K + r) i j =
      schurRest A L U K i j - ∑ t : Fin n, if B t then L i t * U t j else 0 := by
  rw [schurRest, schurRest, sub_sub, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h1 : (t : ℕ) < K
  · rw [ite_eq_left (by omega), ite_eq_left h1, ite_eq_right (by rw [hB]; omega), add_zero]
  · by_cases h2 : (t : ℕ) < K + r
    · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left (by rw [hB]; omega), zero_add]
    · rw [ite_eq_right h2, ite_eq_right h1, ite_eq_right (by rw [hB]; omega), add_zero]

/-- **Exact correctness of Algorithm 3.2.4**: if `A(1:k,1:k)` is nonsingular for `k = 1:n-1`, the
exact packed output of the nonrecursive block LU holds the LU factorization `A = L U`. Invariant
over the block steps: after the blocks before `k`, the entries with `min(i,j) < k r` hold the
finished factors and the others `a_ij - ∑_{t < k r} ℓ_it u_tj`, the Schur complement of the leading
`k r × k r` block (`equation_3_2_9`); within a step the block column is finished pivot by pivot,
the block row by the unit lower triangular solve (whose solution is unique), and the trailing
block receives the contributions of the block. -/
theorem algorithm_3_2_4_spec {N r : ℕ} {A : Matrix (Fin (N * r)) (Fin (N * r)) ℝ}
    (hA : ∀ k : Fin (N * r), (A.strictLeadingPrincipalSubmatrix k).det ≠ 0) :
    IsLU A (packedL (Id.run (algorithm_3_2_4 pure A)))
      (packedU (Id.run (algorithm_3_2_4 pure A))) := by
  obtain ⟨L, U, hLU⟩ := exists_isLU_of_forall_isUnit_strictLeadingPrincipalSubmatrix (A := A)
    fun k => (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hA k))
  have hpiv : ∀ p i : Fin (N * r), p < i → U p p ≠ 0 := fun p i hpi =>
    hLU.diag_upper_ne_zero_of_lt ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hA i))) hpi
  have hLlow : ∀ i j : Fin (N * r), i < j → L i j = 0 := fun i j h =>
    hLU.isUnitLowerTriangular.isLowerTriangular (OrderDual.toDual_lt_toDual.2 h)
  have hpL : packedL (packLU L U) = L := by
    ext i j
    rcases lt_trichotomy j i with h | rfl | h
    · rw [packedL_apply_of_lt _ h]
      simp only [packLU, of_apply]
      rw [ite_eq_left h]
    · rw [packedL_apply_self, hLU.isUnitLowerTriangular.diag_eq_one]
    · rw [packedL_apply_of_lt' _ h, hLlow i j h]
  have hpU : packedU (packLU L U) = U := by
    ext i j
    by_cases h : i ≤ j
    · rw [packedU_apply_of_le _ h]
      simp only [packLU, of_apply]
      rw [ite_eq_right (not_lt.2 h)]
    · rw [packedU_apply_of_lt _ (not_le.1 h), hLU.isUpperTriangular (not_le.1 h)]
  suffices hout : Id.run (algorithm_3_2_4 pure A) = packLU L U by
    rw [hout, hpL, hpU]
    exact hLU
  rcases Nat.eq_zero_or_pos r with hr0 | hr
  · subst hr0
    ext i j
    exact absurd i.isLt (by simp)
  set T := packLU L U with hT
  -- the program in exact arithmetic
  set Elim : Fin N → Matrix (Fin (N * r)) (Fin (N * r)) ℝ → Matrix (Fin (N * r)) (Fin (N * r)) ℝ :=
    fun k S => ((List.finRange (N * r)).filter fun i => i.divNat = k).foldl
      (fun (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) p =>
        ((List.finRange (N * r)).filter (p < ·)).foldl
          (fun (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) i =>
            ((List.finRange (N * r)).filter fun j => j.divNat = k ∧ p < j).foldl
              (fun (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) j =>
                S.updateRow i (Function.update (S i) j (S i j - S i p * S p j))) S)
          (((List.finRange (N * r)).filter (p < ·)).foldl
            (fun (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) i =>
              S.updateRow i (Function.update (S i) p (S i p / S p p))) S)) S with hElim
  set Y : Fin N → Matrix (Fin (N * r)) (Fin (N * r)) ℝ → (Fin (N * r) → ℝ) → Fin (N * r) → ℝ :=
    fun k E v => Id.run (forwardSubstColOn pure
      ((List.finRange (N * r)).filter fun i => i.divNat = k)
      (of fun i j => if j < i then E i j else if i = j then 1 else 0) v) with hY
  set Solve : Fin N → Matrix (Fin (N * r)) (Fin (N * r)) ℝ →
      Matrix (Fin (N * r)) (Fin (N * r)) ℝ :=
    fun k E => ((List.finRange (N * r)).filter fun c => k < c.divNat).foldl
      (fun (B : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) c => B.updateCol c (Y k E fun i => B i c))
      E with hSolve
  set Upd : Fin N → Matrix (Fin (N * r)) (Fin (N * r)) ℝ → Matrix (Fin (N * r)) (Fin (N * r)) ℝ :=
    fun k X => ((List.finRange (N * r)).filter fun i => k < i.divNat).foldl
      (fun (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) i =>
        ((List.finRange (N * r)).filter fun j => k < j.divNat).foldl
          (fun (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) j =>
            S.updateRow i (Function.update (S i) j (S i j - (0 +
              (((List.finRange (N * r)).filter fun t => t.divNat = k).map
                fun t => S i t * S t j).sum)))) S) X with hUpd
  have hprog : Id.run (algorithm_3_2_4 pure A) =
      (List.finRange N).foldl (fun S k => Upd k (Solve k (Elim k S))) A := by
    simp only [algorithm_3_2_4, List.idRun_foldlM, Id.run_bind, Id.run_pure, pure_bind,
      dotAccum_id, hElim, hSolve, hUpd, hY]
  rw [hprog]
  have key := List.foldl_prefix_induction (l := List.finRange N) (b := A)
    (fun S k => Upd k (Solve k (Elim k S)))
    (fun (pre : List (Fin N)) (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) => ∀ i j,
      S i j = if (min i j).divNat ∈ pre then T i j else
        A i j - ∑ t : Fin (N * r), if t.divNat ∈ pre then L i t * U t j else 0)
    (fun i j => by simp) ?_
  · ext i j
    simpa using key i j
  rintro pre x post hpq S hS
  set K : ℕ := (x : ℕ) * r with hK
  have hsorted : (pre ++ x :: post).Pairwise (· < ·) := hpq ▸ (List.sortedLT_finRange N).pairwise
  have hblk : ∀ t : Fin (N * r), t.divNat = x ↔ K ≤ (t : ℕ) ∧ (t : ℕ) < K + r := fun t => by
    rw [Fin.ext_iff, Fin.coe_divNat, Nat.div_eq_iff hr]
    omega
  have hlat : ∀ t : Fin (N * r), x < t.divNat ↔ K + r ≤ (t : ℕ) := fun t => by
    rw [Fin.lt_def, Fin.coe_divNat, ← Nat.succ_le_iff, Nat.le_div_iff_mul_le hr, Nat.succ_mul]
  have hmem : ∀ t : Fin (N * r), t.divNat ∈ pre ↔ (t : ℕ) < K := fun t => by
    constructor
    · intro h
      have hlt : t.divNat < x := (List.pairwise_append.1 hsorted).2.2 _ h x List.mem_cons_self
      rw [Fin.lt_def, Fin.coe_divNat, Nat.div_lt_iff_lt_mul hr] at hlt
      exact hlt
    · intro h
      have hlt : t.divNat < x := by
        rw [Fin.lt_def, Fin.coe_divNat, Nat.div_lt_iff_lt_mul hr]
        exact h
      exact List.mem_prefix_of_pairwise (List.sortedLT_finRange N).pairwise hpq
        (List.mem_finRange _) (ne_of_lt hlt) (not_lt.2 hlt.le)
  have hmem' : ∀ t : Fin (N * r), t.divNat ∈ pre ++ [x] ↔ (t : ℕ) < K + r := fun t => by
    rw [List.mem_append, List.mem_singleton, hmem, hblk]
    omega
  have hS' : ∀ i j, S i j = if ((min i j : Fin (N * r)) : ℕ) < K then T i j else
      schurRest A L U K i j := fun i j => by
    rw [hS i j]
    simp only [hmem, schurRest]
  -- phase 1: the block column elimination
  have hbks : ((List.finRange (N * r)).filter fun i => i.divNat = x).Pairwise (· < ·) :=
    (List.sortedLT_finRange _).pairwise.filter _
  have hE : ∀ i j, Elim x S i j = if j.divNat = x then T i j else S i j := by
    have key1 := List.foldl_prefix_induction
      (l := (List.finRange (N * r)).filter fun i => i.divNat = x) (b := S)
      (fun (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) p =>
        ((List.finRange (N * r)).filter (p < ·)).foldl
          (fun (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) i =>
            ((List.finRange (N * r)).filter fun j => j.divNat = x ∧ p < j).foldl
              (fun (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) j =>
                S.updateRow i (Function.update (S i) j (S i j - S i p * S p j))) S)
          (((List.finRange (N * r)).filter (p < ·)).foldl
            (fun (S : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) i =>
              S.updateRow i (Function.update (S i) p (S i p / S p p))) S))
      (fun (pre' : List (Fin (N * r))) (E : Matrix (Fin (N * r)) (Fin (N * r)) ℝ) => ∀ i j,
        E i j = if j.divNat = x then
          (if ((min i j : Fin (N * r)) : ℕ) < K ∨ min i j ∈ pre' then T i j else
            A i j - ∑ t : Fin (N * r), if (t : ℕ) < K ∨ t ∈ pre' then L i t * U t j else 0)
          else S i j)
      (fun i j => by
        rw [hS' i j]
        by_cases hj : j.divNat = x <;> simp [hj, schurRest]) ?_
    · intro i j
      rw [hElim]
      simp only
      rw [key1 i j]
      by_cases hj : j.divNat = x
      · rw [ite_eq_left hj, ite_eq_left hj, ite_eq_left]
        by_cases hmK : ((min i j : Fin (N * r)) : ℕ) < K
        · exact Or.inl hmK
        · refine Or.inr (List.mem_filter.2 ⟨List.mem_finRange _, decide_eq_true ?_⟩)
          have hjb := (hblk j).1 hj
          rw [hblk]
          simp only [Fin.val_min] at hmK ⊢
          omega
      · rw [ite_eq_right hj, ite_eq_right hj]
    rintro pre' p post' hpq' E hE'
    have hpb : p ∈ (List.finRange (N * r)).filter fun i => i.divNat = x := by
      rw [hpq']; exact List.mem_append.2 (Or.inr List.mem_cons_self)
    have hp : p.divNat = x := by simpa using hpb
    have hpK := (hblk p).1 hp
    have hmemp : ∀ t : Fin (N * r), ((t : ℕ) < K ∨ t ∈ pre') ↔ (t : ℕ) < p := fun t => by
      constructor
      · rintro (h | h)
        · omega
        · exact Fin.lt_def.1 ((List.pairwise_append.1 (hpq' ▸ hbks)).2.2 _ h p
            List.mem_cons_self)
      · intro h
        by_cases htK : (t : ℕ) < K
        · exact Or.inl htK
        · refine Or.inr (List.mem_prefix_of_pairwise hbks hpq' ?_ (fun e => by subst e; omega)
            (fun h' => by have := Fin.lt_def.1 h'; omega))
          exact List.mem_filter.2 ⟨List.mem_finRange _, decide_eq_true ((hblk t).2 (by omega))⟩
    have hmemp' : ∀ t : Fin (N * r), ((t : ℕ) < K ∨ t ∈ pre' ++ [p]) ↔ (t : ℕ) < p + 1 :=
      fun t => by
        rw [List.mem_append, List.mem_singleton, ← or_assoc, hmemp, Fin.ext_iff]
        omega
    have hEn : ∀ i j, E i j = if j.divNat = x then
        (if ((min i j : Fin (N * r)) : ℕ) < p then T i j else schurRest A L U p i j)
        else S i j := fun i j => by
      rw [hE' i j]
      simp only [hmemp, schurRest]
    intro i j
    rw [elimStep hLU hpiv (fun j => j.divNat = x) p hp S E hEn i j]
    simp only [hmemp', schurRest, ← hT]
  -- phase 2: the multiple right-hand side solve
  set E := Elim x S with hEdef
  have hbk : ∀ t, t ∈ (List.finRange (N * r)).filter (fun i => i.divNat = x) ↔ t.divNat = x :=
    fun t => by simp
  have hlatm : ∀ t, t ∈ (List.finRange (N * r)).filter (fun i => x < i.divNat) ↔ x < t.divNat :=
    fun t => by simp
  have hLk : ∀ i j, i.divNat = x → j.divNat = x →
      (of fun i j => if j < i then E i j else if i = j then 1 else 0 :
        Matrix (Fin (N * r)) (Fin (N * r)) ℝ) i j = L i j := fun i j hi hj => by
    simp only [of_apply]
    rcases lt_trichotomy j i with h | rfl | h
    · rw [ite_eq_left h, hE, ite_eq_left hj]
      simp only [hT, packLU, of_apply]
      rw [ite_eq_left h]
    · rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl, hLU.isUnitLowerTriangular.diag_eq_one]
    · rw [ite_eq_right (not_lt.2 h.le), ite_eq_right (ne_of_lt h), hLlow i j h]
  have hYc : ∀ c, x < c.divNat → ∀ i, Y x E (fun i => E i c) i =
      if i.divNat = x then U i c else E i c := by
    intro c hc i
    have hLkl : (of fun i j => if j < i then E i j else if i = j then 1 else 0 :
        Matrix (Fin (N * r)) (Fin (N * r)) ℝ).IsLowerTriangular := fun a b hab => by
      have hab' : a < b := OrderDual.toDual_lt_toDual.1 hab
      simp only [of_apply]
      rw [ite_eq_right (not_lt.2 hab'.le), ite_eq_right (ne_of_lt hab')]
    obtain ⟨h₁, h₂⟩ := forwardSubstColOn_exact hbks hLkl (fun a _ => by simp)
      (fun i => E i c)
    by_cases hi : i.divNat = x
    · rw [ite_eq_left hi]
      refine eq_on_of_sum_eq (y := Y x E fun i => E i c) (z := fun j => U j c) hbks hLkl
        (fun a _ => by simp) (fun a ha => ?_) i ((hbk i).2 hi)
      refine (h₂ a ha).trans ?_
      have ha' := (hbk a).1 ha
      have hac : a < c := Fin.lt_def.2 (by have := (hblk a).1 ha'; have := (hlat c).1 hc; omega)
      rw [List.map_congr_left fun j hj => by rw [hLk a j ha' ((hbk j).1 hj)],
        List.sum_map_filter_finRange (fun j => j.divNat = x), Finset.sum_filter, hE,
        ite_eq_right (by intro h; rw [h] at hc; exact lt_irrefl x hc), hS', ite_eq_right (by
            simp only [Fin.val_min]; have := (hblk a).1 ha'; have := Fin.lt_def.1 hac; omega),
        schurRest_eq hLU]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases ht : t.divNat = x
      · rw [ite_eq_left ht, ite_eq_left ((hblk t).1 ht).1]
      · rw [ite_eq_right ht]
        by_cases hKt : K ≤ (t : ℕ)
        · rw [ite_eq_left hKt, hLlow a t (Fin.lt_def.2 (by
            have := (hblk a).1 ha'; rw [hblk] at ht; omega)), zero_mul]
        · rw [ite_eq_right hKt]
    · rw [ite_eq_right hi]
      exact h₁ i fun h => hi ((hbk i).1 h)
  have hX : ∀ i c, Solve x E i c =
      if x < c.divNat ∧ i.divNat = x then U i c else E i c := fun i c => by
    rw [hSolve]
    simp only
    rw [foldl_updateCol_apply_of_col (Y x E) ((List.nodup_finRange _).filter _)]
    by_cases hc : x < c.divNat
    · rw [ite_eq_left ((hlatm c).2 hc), hYc c hc i]
      by_cases hi : i.divNat = x
      · rw [ite_eq_left hi, ite_eq_left ⟨hc, hi⟩]
      · rw [ite_eq_right hi, ite_eq_right (by intro h; exact hi h.2)]
    · rw [ite_eq_right (by intro h; exact hc ((hlatm c).1 h)),
        ite_eq_right (by intro h; exact hc h.1)]
  -- phase 3: the level-3 update
  set X := Solve x E with hXdef
  intro i j
  rw [hUpd]
  beta_reduce
  rw [foldl_foldl_sub_apply ((List.nodup_finRange _).filter _) ((List.nodup_finRange _).filter _)
    (fun S i j => 0 + (((List.finRange (N * r)).filter fun t => t.divNat = x).map
      fun t => S i t * S t j).sum) (fun S S' hSS' i j => by
        congr 2
        refine List.map_congr_left fun t ht => ?_
        have ht' := (hbk t).1 ht
        have htl : ¬ x < t.divNat := by rw [ht']; exact lt_irrefl x
        rw [hSS' i t fun h => htl ((hlatm t).1 h.2), hSS' t j fun h => htl ((hlatm t).1 h.1)])]
  simp only [hmem', hlatm]
  change _ = if _ then T i j else schurRest A L U (K + r) i j
  have hXbk : ∀ i t, t.divNat = x → X i t = E i t := fun i t ht => by
    rw [hX, ite_eq_right (by intro h; rw [ht] at h; exact lt_irrefl x h.1)]
  by_cases hij : x < i.divNat ∧ x < j.divNat
  · rw [ite_eq_left hij]
    have hi := (hlat i).1 hij.1
    have hj := (hlat j).1 hij.2
    have hix : i.divNat ≠ x := fun h => by rw [h] at hij; exact lt_irrefl x hij.1
    have hjx : j.divNat ≠ x := fun h => by rw [h] at hij; exact lt_irrefl x hij.2
    rw [hX i j, ite_eq_right (by intro h; exact hix h.2), hE i j, ite_eq_right hjx, hS' i j,
      ite_eq_right (by simp only [Fin.val_min]; omega),
      ite_eq_right (by simp only [Fin.val_min]; omega),
      schurRest_add_block K r (fun t => t.divNat = x) hblk, zero_add]
    congr 1
    rw [List.map_congr_left (g := fun t => L i t * U t j) fun t ht => by
        have ht' := (hbk t).1 ht
        rw [hXbk i t ht', hE i t, ite_eq_left ht', hX t j, ite_eq_left ⟨hij.2, ht'⟩]
        have hti : t < i := Fin.lt_def.2 (by have := (hblk t).1 ht'; omega)
        simp only [hT, packLU, of_apply]
        rw [ite_eq_left hti],
      List.sum_map_filter_finRange (fun t => t.divNat = x), Finset.sum_filter]
  · rw [ite_eq_right hij, hX]
    by_cases hc : x < j.divNat ∧ i.divNat = x
    · rw [ite_eq_left hc]
      have hi := (hblk i).1 hc.2
      have hj := (hlat j).1 hc.1
      rw [ite_eq_left (by simp only [Fin.val_min]; omega)]
      simp only [hT, packLU, of_apply]
      rw [ite_eq_right (not_lt.2 (Fin.le_def.2 (by omega)))]
    · rw [ite_eq_right hc, hE]
      by_cases hj : j.divNat = x
      · rw [ite_eq_left hj, ite_eq_left (by
          have := (hblk j).1 hj; simp only [Fin.val_min]; omega)]
      · rw [ite_eq_right hj, hS']
        have hmK : ((min i j : Fin (N * r)) : ℕ) < K := by
          by_cases hjl : x < j.divNat
          · have hi1 : ¬ x < i.divNat := fun h => hij ⟨h, hjl⟩
            have hi2 : ¬ i.divNat = x := fun h => hc ⟨hjl, h⟩
            rw [hlat] at hi1
            rw [hblk] at hi2
            simp only [Fin.val_min]
            omega
          · rw [hlat] at hjl
            rw [hblk] at hj
            simp only [Fin.val_min]
            omega
        rw [ite_eq_left hmK, ite_eq_left (by omega)]

end Exact

end NonrecursiveBlockLU

end GolubVanLoan.Chapter03
