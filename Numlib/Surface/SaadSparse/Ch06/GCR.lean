import Numlib.Surface.SaadSparse.Ch06.CR

/-!
# Saad, §6.9: GCR, ORTHOMIN and ORTHODIR

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003, §6.9.

**Lemma 6.21** with (6.104)–(6.105) says that *any* sequence of directions `p_0, …, p_{m-1}`
that is `AᴴA`-orthogonal and spans `𝒦_m(A, r_0)` produces the minimal-residual approximation by
the one-line update (6.105); it is `isMinResIterate_of_orthogonalDirections` below, a direct
specialization of the backbone `Krylov.isMinResIterate_of_orthogonal_directions`
(`Numlib/Krylov/CR.lean`), and `eq_6_104` is the resulting closed form.

The section's three algorithms are the three ways the book builds such a sequence:
**Algorithm 6.21** (GCR) is `gcr`, whose new direction is the residual orthogonalized against
the previous ones; **ORTHODIR** is `orthodir`, whose new direction is `A p_j` orthogonalized in
the same way (6.107); **ORTHOMIN(k)** is `orthomin`, GCR with lines 6–7 truncated to the last
`k` directions. Each carries the triple `(x_j, r_j, p_j)`, and the step is packaged as
`gcrBody`, `orthodirBody`, `orthominBody` so that the three recursions differ only in that one
function.

The full versions satisfy the minimal-residual specification, so `gcr` and `orthodir` compute
the GMRES approximation (`gcrX_isMinResIterate`, `orthodirX_isMinResIterate`,
`gcrX_eq_gmresFixed`, `orthodirX_eq_gmresFixed`). The truncated and restarted variants
ORTHOMIN(k) and GCR(m) (`gcrRestarted`, **Algorithm 6.21** with restarts) satisfy no global
specification and the book proves nothing about them; the one statement it does make,
"ORTHOMIN(k) with `k ≥ m` is GCR", is `orthomin_eq_gcr`.

Indices are `0`-based, as in the book: `gcrP A b x₀ j` is the book's `p_j`. Division by a
vanishing quantity is `0` in Lean, which reproduces the book's breakdown behaviour.

Definitions are polymorphic in `𝕜`; the numbered results are stated over `ℝ`, the book's
generality in §6.9.
-/

open scoped ComplexOrder Matrix

namespace SaadSparse.Ch06

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-! ### Krylov glue -/

private theorem krylov_mono {v : 𝔼} {k l : ℕ} (h : k ≤ l) : krylov A v k ≤ krylov A v l := by
  rw [krylov_eq, krylov_eq]
  exact Krylov.subspace_mono (op A) v h

private theorem apply_mem_krylov_succ {v x : 𝔼} {m : ℕ} (h : x ∈ krylov A v m) :
    op A x ∈ krylov A v (m + 1) := by
  rw [krylov_eq] at h
  rw [krylov_eq]
  exact Krylov.map_subspace_le (op A) v m ⟨x, h, rfl⟩

/-! ### Lemma 6.21 and (6.104)–(6.105) -/

/-- **Lemma 6.21** with **(6.105)**: if the directions `p_0, …, p_{m-1}` are `AᴴA`-orthogonal
with `A p_i ≠ 0` and span `𝒦_m(A, r_0)`, then the sequence produced by the update (6.105)
`x_{j+1} = x_j + ((r_j, A p_j)/(A p_j, A p_j)) p_j` reaches the minimal-residual approximation
of `x_0 + 𝒦_m(A, r_0)` at step `m`. -/
theorem isMinResIterate_of_orthogonalDirections {m : ℕ} (p : ℕ → 𝔼)
    (horth : ∀ i < m, ∀ l < m, i ≠ l → inner 𝕜 (op A (p i)) (op A (p l)) = 0)
    (hne : ∀ i < m, op A (p i) ≠ 0)
    (hspan : Submodule.span 𝕜 (Set.range fun i : Fin m => p (i : ℕ)) = krylov A (r₀ A b x₀) m)
    (x : ℕ → 𝔼) (hx0 : x 0 = x₀)
    (hstep : ∀ j, x (j + 1) = x j +
      (inner 𝕜 (op A (p j)) (b - op A (x j)) / inner 𝕜 (op A (p j)) (op A (p j))) • p j) :
    Krylov.IsMinResIterate (op A) b x₀ m (x m) := by
  rw [krylov_eq] at hspan
  exact Krylov.isMinResIterate_of_orthogonal_directions p horth hne hspan x hx0 hstep

/-- The residual of a sequence updated along the directions `p_j` with coefficients `c_j`. -/
private theorem residual_eq_sub_sum (p x : ℕ → 𝔼) (c : ℕ → 𝕜)
    (hstep : ∀ j, x (j + 1) = x j + c j • p j) (j : ℕ) :
    b - op A (x j) = (b - op A (x 0)) - ∑ l ∈ Finset.range j, c l • op A (p l) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h : b - op A (x (j + 1)) = (b - op A (x j)) - c j • op A (p j) := by
      rw [hstep j, map_add, map_smul]
      abel
    rw [h, ih, Finset.sum_range_succ]
    abel

/-- **(6.104)**: the approximation produced by the update (6.105) has the closed form
`x_m = x_0 + ∑_{i<m} ((r_0, A p_i)/(A p_i, A p_i)) p_i`, because `(r_j, A p_j) = (r_0, A p_j)`
once the directions are `AᴴA`-orthogonal. -/
theorem eq_6_104 {m : ℕ} (p : ℕ → 𝔼)
    (horth : ∀ i < m, ∀ l < m, i ≠ l → inner 𝕜 (op A (p i)) (op A (p l)) = 0)
    (x : ℕ → 𝔼) (hx0 : x 0 = x₀)
    (hstep : ∀ j, x (j + 1) = x j +
      (inner 𝕜 (op A (p j)) (b - op A (x j)) / inner 𝕜 (op A (p j)) (op A (p j))) • p j) :
    x m = x₀ + ∑ i ∈ Finset.range m,
      (inner 𝕜 (op A (p i)) (r₀ A b x₀) / inner 𝕜 (op A (p i)) (op A (p i))) • p i := by
  have hres := residual_eq_sub_sum A b p x
    (fun l => inner 𝕜 (op A (p l)) (b - op A (x l)) / inner 𝕜 (op A (p l)) (op A (p l))) hstep
  have hnum : ∀ j < m, inner 𝕜 (op A (p j)) (b - op A (x j))
      = inner 𝕜 (op A (p j)) (r₀ A b x₀) := by
    intro j hj
    have hz : ∀ l ∈ Finset.range j,
        inner 𝕜 (op A (p j))
          ((inner 𝕜 (op A (p l)) (b - op A (x l)) / inner 𝕜 (op A (p l)) (op A (p l))) •
            op A (p l)) = 0 := by
      intro l hl
      have hlj := Finset.mem_range.1 hl
      rw [inner_smul_right, horth j hj l (by omega) (by omega), mul_zero]
    rw [hres j, hx0, inner_sub_right, inner_sum, Finset.sum_eq_zero hz, sub_zero]
  have hx : ∀ j ≤ m, x j = x₀ + ∑ i ∈ Finset.range j,
      (inner 𝕜 (op A (p i)) (r₀ A b x₀) / inner 𝕜 (op A (p i)) (op A (p i))) • p i := by
    intro j
    induction j with
    | zero => intro _; simpa using hx0
    | succ j ih =>
      intro hj
      rw [hstep j, hnum j (by omega), ih (by omega), Finset.sum_range_succ]
      abel
  exact hx m le_rfl

/-! ### The generic step and the orthogonality it produces -/

/-- Lines 3–5 of **Algorithm 6.21**, shared by GCR, ORTHOMIN(k) and ORTHODIR: the step length
`α_j = (r_j, A p_j)/(A p_j, A p_j)` on a state `(x_j, r_j, p_j)`. -/
noncomputable def gcrStepAlpha (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (op A s.2.2) s.2.1 / inner 𝕜 (op A s.2.2) (op A s.2.2)

/-- The coefficient `β_ij = -(A z, A p_i)/(A p_i, A p_i)` used in line 6 of Algorithm 6.21 and
in (6.107), with `z = r_{j+1}` for GCR and ORTHOMIN(k) and `z = A p_j` for ORTHODIR. -/
noncomputable def gcrStepBeta (A : Matrix (Fin n) (Fin n) 𝕜) (pi z : 𝔼) : 𝕜 :=
  -(inner 𝕜 (op A pi) (op A z) / inner 𝕜 (op A pi) (op A pi))

/-- Lines 3–7 of **Algorithm 6.21** (GCR) applied to the history `s` of states
`(x_i, r_i, p_i)`, `i ≤ j`. -/
noncomputable def gcrBody (A : Matrix (Fin n) (Fin n) 𝕜) {j : ℕ}
    (s : Fin (j + 1) → 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 :=
  ((s (Fin.last j)).1 + gcrStepAlpha A (s (Fin.last j)) • (s (Fin.last j)).2.2,
    (s (Fin.last j)).2.1 - gcrStepAlpha A (s (Fin.last j)) • op A (s (Fin.last j)).2.2,
    ((s (Fin.last j)).2.1 - gcrStepAlpha A (s (Fin.last j)) • op A (s (Fin.last j)).2.2) +
      ∑ i : Fin (j + 1), gcrStepBeta A (s i).2.2
        ((s (Fin.last j)).2.1 - gcrStepAlpha A (s (Fin.last j)) • op A (s (Fin.last j)).2.2) •
          (s i).2.2)

/-- Lines 3–5 of Algorithm 6.21 with the direction update (6.107) of **ORTHODIR**: the new
direction is `A p_j` orthogonalized against the previous directions. -/
noncomputable def orthodirBody (A : Matrix (Fin n) (Fin n) 𝕜) {j : ℕ}
    (s : Fin (j + 1) → 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 :=
  ((s (Fin.last j)).1 + gcrStepAlpha A (s (Fin.last j)) • (s (Fin.last j)).2.2,
    (s (Fin.last j)).2.1 - gcrStepAlpha A (s (Fin.last j)) • op A (s (Fin.last j)).2.2,
    op A (s (Fin.last j)).2.2 +
      ∑ i : Fin (j + 1),
        gcrStepBeta A (s i).2.2 (op A (s (Fin.last j)).2.2) • (s i).2.2)

/-- Lines 3–5 of Algorithm 6.21 with the truncated lines 6a–7a of **ORTHOMIN(k)**: only the
directions `p_i` with `j - k + 1 ≤ i ≤ j` are used. -/
noncomputable def orthominBody (A : Matrix (Fin n) (Fin n) 𝕜) (k : ℕ) {j : ℕ}
    (s : Fin (j + 1) → 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 :=
  ((s (Fin.last j)).1 + gcrStepAlpha A (s (Fin.last j)) • (s (Fin.last j)).2.2,
    (s (Fin.last j)).2.1 - gcrStepAlpha A (s (Fin.last j)) • op A (s (Fin.last j)).2.2,
    ((s (Fin.last j)).2.1 - gcrStepAlpha A (s (Fin.last j)) • op A (s (Fin.last j)).2.2) +
      ∑ i : Fin (j + 1), if j + 1 ≤ (i : ℕ) + k then
        gcrStepBeta A (s i).2.2
          ((s (Fin.last j)).2.1 - gcrStepAlpha A (s (Fin.last j)) • op A (s (Fin.last j)).2.2) •
            (s i).2.2
      else 0)

/-- With `k` at least the number of steps performed, ORTHOMIN(k) does not truncate anything. -/
private theorem orthominBody_eq_gcrBody {k j : ℕ} (hk : j + 1 ≤ k)
    (s : Fin (j + 1) → 𝔼 × 𝔼 × 𝔼) : orthominBody A k s = gcrBody A s := by
  rw [orthominBody, gcrBody]
  refine congrArg _ (congrArg _ (congrArg _ (Finset.sum_congr rfl fun i _ => ?_)))
  exact ite_eq_left_of_eq_true _ _ (eq_true (by omega))

/-- **The `AᴴA`-orthogonality of Lemma 6.21, produced by construction**: if each new direction
is a vector `z_j` from which its `A`-projections on the previous directions have been
subtracted, then the vectors `A p_i` are pairwise orthogonal. GCR takes `z_j = r_{j+1}` and
ORTHODIR takes `z_j = A p_j`. -/
private theorem inner_apply_eq_zero_of_recur (p z : ℕ → 𝔼) {m : ℕ}
    (hrec : ∀ j, p (j + 1) = z j + ∑ i ∈ Finset.range (j + 1), gcrStepBeta A (p i) (z j) • p i)
    (hne : ∀ i < m, op A (p i) ≠ 0) :
    ∀ i < m, ∀ l < m, i ≠ l → inner 𝕜 (op A (p i)) (op A (p l)) = 0 := by
  have key : ∀ N, N ≤ m → ∀ i < N, ∀ l < N, i ≠ l →
      inner 𝕜 (op A (p i)) (op A (p l)) = 0 := by
    intro N
    induction N with
    | zero => intro _ i hi; omega
    | succ N ih =>
      intro hN
      have ihN := ih (by omega)
      have hlast : ∀ i < N, inner 𝕜 (op A (p i)) (op A (p N)) = 0 := by
        intro i hi
        obtain ⟨j, rfl⟩ : ∃ j, N = j + 1 := ⟨N - 1, by omega⟩
        have hnz : inner 𝕜 (op A (p i)) (op A (p i)) ≠ 0 := fun h =>
          hne i (by omega) (inner_self_eq_zero.1 h)
        have happ : op A (p (j + 1)) = op A (z j) +
            ∑ l ∈ Finset.range (j + 1), gcrStepBeta A (p l) (z j) • op A (p l) := by
          rw [hrec j, map_add, map_sum]
          exact congrArg _ (Finset.sum_congr rfl fun l _ => map_smul _ _ _)
        have hsum : ∑ l ∈ Finset.range (j + 1),
            gcrStepBeta A (p l) (z j) * inner 𝕜 (op A (p i)) (op A (p l))
            = gcrStepBeta A (p i) (z j) * inner 𝕜 (op A (p i)) (op A (p i)) := by
          refine Finset.sum_eq_single i (fun l hl hli => ?_) fun h =>
            absurd (Finset.mem_range.2 hi) h
          rw [ihN i hi l (Finset.mem_range.1 hl) (Ne.symm hli), mul_zero]
        rw [happ, inner_add_right, inner_sum]
        simp only [inner_smul_right]
        rw [hsum, gcrStepBeta, neg_mul, div_mul_cancel₀ _ hnz, add_neg_cancel]
      intro i hi l hl hil
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl' | rfl
        · exact ihN i hi' l hl' hil
        · exact hlast i hi'
      · rw [← inner_conj_symm, hlast l (by omega), map_zero]
  exact key m le_rfl

/-- The directions of a GCR-type recursion stay inside the Krylov subspaces. -/
private theorem mem_krylov_of_recur (p z : ℕ → 𝔼) (v : 𝔼) (c : ℕ → ℕ → 𝕜) (hp0 : p 0 = v)
    (hrec : ∀ j, p (j + 1) = z j + ∑ i ∈ Finset.range (j + 1), c i j • p i)
    (hz : ∀ j, (∀ i ≤ j, p i ∈ krylov A v (i + 1)) → z j ∈ krylov A v (j + 2)) (j : ℕ) :
    p j ∈ krylov A v (j + 1) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero => rw [hp0]; exact self_mem_krylov A v one_pos
    | succ j =>
      have hp : ∀ i ≤ j, p i ∈ krylov A v (i + 1) := fun i hi => ih i (by omega)
      rw [hrec j]
      refine Submodule.add_mem _ (hz j hp) (Submodule.sum_mem _ fun i hi => ?_)
      exact Submodule.smul_mem _ _
        (krylov_mono A (by have := Finset.mem_range.1 hi; omega) (hp i (by
          have := Finset.mem_range.1 hi; omega)))

/-- `AᴴA`-orthogonal, nonzero directions inside `𝒦_m` span it, provided `m` does not exceed the
grade of `r_0`. -/
private theorem span_eq_krylov (p : ℕ → 𝔼) {m : ℕ}
    (horth : ∀ i < m, ∀ l < m, i ≠ l → inner 𝕜 (op A (p i)) (op A (p l)) = 0)
    (hne : ∀ i < m, op A (p i) ≠ 0)
    (hmem : ∀ j, p j ∈ krylov A (r₀ A b x₀) (j + 1))
    (hm : m ≤ grade A (r₀ A b x₀)) :
    Submodule.span 𝕜 (Set.range fun i : Fin m => p (i : ℕ)) = krylov A (r₀ A b x₀) m := by
  have hindep : LinearIndependent 𝕜 fun i : Fin m => p (i : ℕ) := by
    have h1 : LinearIndependent 𝕜 ((op A) ∘ fun i : Fin m => p (i : ℕ)) :=
      linearIndependent_of_ne_zero_of_inner_eq_zero (fun i => hne i i.2)
        fun i l hil => horth i i.2 l l.2 fun h => hil (Fin.ext h)
    exact LinearIndependent.of_comp (op A) h1
  have hle : Submodule.span 𝕜 (Set.range fun i : Fin m => p (i : ℕ))
      ≤ krylov A (r₀ A b x₀) m := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact krylov_mono A i.2 (hmem (i : ℕ))
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [finrank_span_eq_card hindep, finrank_krylov, min_eq_left hm, Fintype.card_fin]

/-- The recurrence residual of a GCR-type algorithm is the true residual. -/
private theorem residual_eq_of_recur (x r p : ℕ → 𝔼) (c : ℕ → 𝕜) (hr0 : r 0 = b - op A (x 0))
    (hx : ∀ j, x (j + 1) = x j + c j • p j) (hr : ∀ j, r (j + 1) = r j - c j • op A (p j))
    (j : ℕ) : r j = b - op A (x j) := by
  induction j with
  | zero => exact hr0
  | succ j ih =>
    rw [hr j, ih, hx j, map_add, map_smul]
    abel

/-! ### Algorithm 6.21: GCR -/

/-- **Algorithm 6.21** (GCR) run for `j` steps: the triple `(x_j, r_j, p_j)`, started from
`r_0 = b - A x_0` and `p_0 = r_0`. -/
noncomputable def gcrAux (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) : ℕ → 𝔼 × 𝔼 × 𝔼
  | 0 => (x₀, b - op A x₀, b - op A x₀)
  | j + 1 => gcrBody A fun i : Fin (j + 1) => gcrAux A b x₀ (i : ℕ)
  termination_by j => j
  decreasing_by exact i.isLt

/-- The `j`-th GCR iterate `x_j` of Algorithm 6.21. -/
noncomputable def gcrX (j : ℕ) : 𝔼 := (gcrAux A b x₀ j).1

/-- The `j`-th GCR residual `r_j` of Algorithm 6.21. -/
noncomputable def gcrR (j : ℕ) : 𝔼 := (gcrAux A b x₀ j).2.1

/-- The `j`-th GCR direction `p_j` of Algorithm 6.21. -/
noncomputable def gcrP (j : ℕ) : 𝔼 := (gcrAux A b x₀ j).2.2

/-- The step length `α_j = (r_j, A p_j)/(A p_j, A p_j)` of Algorithm 6.21, line 3. -/
noncomputable def gcrAlpha (j : ℕ) : 𝕜 := gcrStepAlpha A (gcrAux A b x₀ j)

/-- The direction coefficient `β_ij = -(A r_{j+1}, A p_i)/(A p_i, A p_i)` of Algorithm 6.21,
line 6. -/
noncomputable def gcrBeta (i j : ℕ) : 𝕜 :=
  gcrStepBeta A (gcrP A b x₀ i) (gcrR A b x₀ (j + 1))

@[simp] theorem gcrX_zero : gcrX A b x₀ 0 = x₀ := by rw [gcrX, gcrAux]

@[simp] theorem gcrR_zero : gcrR A b x₀ 0 = b - op A x₀ := by rw [gcrR, gcrAux]

/-- Algorithm 6.21, line 1: `p_0 = r_0`. -/
@[simp] theorem gcrP_zero : gcrP A b x₀ 0 = gcrR A b x₀ 0 := by rw [gcrP, gcrR, gcrAux]

theorem gcrAlpha_eq (j : ℕ) : gcrAlpha A b x₀ j =
    inner 𝕜 (op A (gcrP A b x₀ j)) (gcrR A b x₀ j) /
      inner 𝕜 (op A (gcrP A b x₀ j)) (op A (gcrP A b x₀ j)) := rfl

/-- Algorithm 6.21, line 4: `x_{j+1} = x_j + α_j p_j`. -/
theorem gcrX_succ (j : ℕ) :
    gcrX A b x₀ (j + 1) = gcrX A b x₀ j + gcrAlpha A b x₀ j • gcrP A b x₀ j := by
  rw [gcrX, gcrAux]
  rfl

/-- Algorithm 6.21, line 5: `r_{j+1} = r_j - α_j A p_j`. -/
theorem gcrR_succ (j : ℕ) :
    gcrR A b x₀ (j + 1) = gcrR A b x₀ j - gcrAlpha A b x₀ j • op A (gcrP A b x₀ j) := by
  rw [gcrR, gcrAux]
  rfl

/-- Algorithm 6.21, line 7: `p_{j+1} = r_{j+1} + ∑_{i ≤ j} β_ij p_i`. -/
theorem gcrP_succ (j : ℕ) : gcrP A b x₀ (j + 1) =
    gcrR A b x₀ (j + 1) + ∑ i ∈ Finset.range (j + 1), gcrBeta A b x₀ i j • gcrP A b x₀ i := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => gcrBeta A b x₀ i j • gcrP A b x₀ i) (j + 1)]
  simp only [gcrBeta, gcrR_succ]
  rw [gcrP, gcrAux]
  rfl

theorem gcrR_eq_residual (j : ℕ) : gcrR A b x₀ j = b - op A (gcrX A b x₀ j) :=
  residual_eq_of_recur A b (gcrX A b x₀) (gcrR A b x₀) (gcrP A b x₀) (gcrAlpha A b x₀)
    (by rw [gcrR_zero, gcrX_zero]) (gcrX_succ A b x₀) (gcrR_succ A b x₀) j

theorem gcrP_mem_krylov (j : ℕ) : gcrP A b x₀ j ∈ krylov A (r₀ A b x₀) (j + 1) := by
  refine mem_krylov_of_recur A (gcrP A b x₀) (fun j => gcrR A b x₀ (j + 1)) (r₀ A b x₀)
    (gcrBeta A b x₀) (by rw [gcrP_zero, gcrR_zero]) (gcrP_succ A b x₀) (fun j hp => ?_) j
  have hr : ∀ l, l ≤ j + 1 → gcrR A b x₀ l ∈ krylov A (r₀ A b x₀) (l + 1) := by
    intro l
    induction l with
    | zero => intro _; rw [gcrR_zero]; exact self_mem_krylov A _ one_pos
    | succ l ih =>
      intro hl
      rw [gcrR_succ]
      exact Submodule.sub_mem _ (krylov_mono A (by omega) (ih (by omega)))
        (Submodule.smul_mem _ _ (apply_mem_krylov_succ A (hp l (by omega))))
  exact hr (j + 1) le_rfl

/-- §6.9: the vectors `A p_i` built by Algorithm 6.21 are orthogonal, which is the hypothesis of
Lemma 6.21. -/
theorem inner_apply_gcrP_eq_zero {m : ℕ} (hne : ∀ i < m, op A (gcrP A b x₀ i) ≠ 0) :
    ∀ i < m, ∀ l < m, i ≠ l → inner 𝕜 (op A (gcrP A b x₀ i)) (op A (gcrP A b x₀ l)) = 0 :=
  inner_apply_eq_zero_of_recur A (gcrP A b x₀) (fun j => gcrR A b x₀ (j + 1))
    (gcrP_succ A b x₀) hne

theorem span_gcrP_eq {m : ℕ} (hne : ∀ i < m, op A (gcrP A b x₀ i) ≠ 0)
    (hm : m ≤ grade A (r₀ A b x₀)) :
    Submodule.span 𝕜 (Set.range fun i : Fin m => gcrP A b x₀ (i : ℕ))
      = krylov A (r₀ A b x₀) m :=
  span_eq_krylov A b x₀ (gcrP A b x₀) (inner_apply_gcrP_eq_zero A b x₀ hne) hne
    (gcrP_mem_krylov A b x₀) hm

/-- **GCR is mathematically equivalent to full GMRES**: Algorithm 6.21 realises the
minimal-residual specification on `𝒦_m(A, r_0)`, by Lemma 6.21. -/
theorem gcrX_isMinResIterate {m : ℕ} (hne : ∀ i < m, op A (gcrP A b x₀ i) ≠ 0)
    (hm : m ≤ grade A (r₀ A b x₀)) :
    Krylov.IsMinResIterate (op A) b x₀ m (gcrX A b x₀ m) := by
  refine isMinResIterate_of_orthogonalDirections A b x₀ (gcrP A b x₀)
    (inner_apply_gcrP_eq_zero A b x₀ hne) hne (span_gcrP_eq A b x₀ hne hm) (gcrX A b x₀)
    (gcrX_zero A b x₀) fun j => ?_
  rw [gcrX_succ, gcrAlpha_eq, gcrR_eq_residual]

/-! ### ORTHODIR -/

/-- **ORTHODIR** run for `j` steps: the triple `(x_j, r_j, p_j)`, with the direction update
(6.107) `p_{j+1} = A p_j + ∑_{i ≤ j} β_ij p_i` and the iterate update (6.105). -/
noncomputable def orthodirAux (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) : ℕ → 𝔼 × 𝔼 × 𝔼
  | 0 => (x₀, b - op A x₀, b - op A x₀)
  | j + 1 => orthodirBody A fun i : Fin (j + 1) => orthodirAux A b x₀ (i : ℕ)
  termination_by j => j
  decreasing_by exact i.isLt

/-- The `j`-th ORTHODIR iterate `x_j`. -/
noncomputable def orthodirX (j : ℕ) : 𝔼 := (orthodirAux A b x₀ j).1

/-- The `j`-th ORTHODIR residual `r_j`. -/
noncomputable def orthodirR (j : ℕ) : 𝔼 := (orthodirAux A b x₀ j).2.1

/-- The `j`-th ORTHODIR direction `p_j`. -/
noncomputable def orthodirP (j : ℕ) : 𝔼 := (orthodirAux A b x₀ j).2.2

/-- The step length `α_j = (r_j, A p_j)/(A p_j, A p_j)` of (6.105). -/
noncomputable def orthodirAlpha (j : ℕ) : 𝕜 := gcrStepAlpha A (orthodirAux A b x₀ j)

/-- The direction coefficient `β_ij = -(A² p_j, A p_i)/(A p_i, A p_i)` of (6.107). -/
noncomputable def orthodirBeta (i j : ℕ) : 𝕜 :=
  gcrStepBeta A (orthodirP A b x₀ i) (op A (orthodirP A b x₀ j))

@[simp] theorem orthodirX_zero : orthodirX A b x₀ 0 = x₀ := by rw [orthodirX, orthodirAux]

@[simp] theorem orthodirR_zero : orthodirR A b x₀ 0 = b - op A x₀ := by
  rw [orthodirR, orthodirAux]

@[simp] theorem orthodirP_zero : orthodirP A b x₀ 0 = orthodirR A b x₀ 0 := by
  rw [orthodirP, orthodirR, orthodirAux]

theorem orthodirAlpha_eq (j : ℕ) : orthodirAlpha A b x₀ j =
    inner 𝕜 (op A (orthodirP A b x₀ j)) (orthodirR A b x₀ j) /
      inner 𝕜 (op A (orthodirP A b x₀ j)) (op A (orthodirP A b x₀ j)) := rfl

/-- (6.105) for ORTHODIR: `x_{j+1} = x_j + α_j p_j`. -/
theorem orthodirX_succ (j : ℕ) :
    orthodirX A b x₀ (j + 1) = orthodirX A b x₀ j + orthodirAlpha A b x₀ j • orthodirP A b x₀ j
    := by
  rw [orthodirX, orthodirAux]
  rfl

theorem orthodirR_succ (j : ℕ) : orthodirR A b x₀ (j + 1) =
    orthodirR A b x₀ j - orthodirAlpha A b x₀ j • op A (orthodirP A b x₀ j) := by
  rw [orthodirR, orthodirAux]
  rfl

/-- (6.107): `p_{j+1} = A p_j + ∑_{i ≤ j} β_ij p_i`. -/
theorem orthodirP_succ (j : ℕ) : orthodirP A b x₀ (j + 1) = op A (orthodirP A b x₀ j) +
    ∑ i ∈ Finset.range (j + 1), orthodirBeta A b x₀ i j • orthodirP A b x₀ i := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => orthodirBeta A b x₀ i j • orthodirP A b x₀ i)
    (j + 1), orthodirP, orthodirAux]
  rfl

theorem orthodirR_eq_residual (j : ℕ) : orthodirR A b x₀ j = b - op A (orthodirX A b x₀ j) :=
  residual_eq_of_recur A b (orthodirX A b x₀) (orthodirR A b x₀) (orthodirP A b x₀)
    (orthodirAlpha A b x₀) (by rw [orthodirR_zero, orthodirX_zero]) (orthodirX_succ A b x₀)
    (orthodirR_succ A b x₀) j

theorem orthodirP_mem_krylov (j : ℕ) :
    orthodirP A b x₀ j ∈ krylov A (r₀ A b x₀) (j + 1) :=
  mem_krylov_of_recur A (orthodirP A b x₀) (fun j => op A (orthodirP A b x₀ j)) (r₀ A b x₀)
    (orthodirBeta A b x₀) (by rw [orthodirP_zero, orthodirR_zero]) (orthodirP_succ A b x₀)
    (fun j hp => apply_mem_krylov_succ A (hp j le_rfl)) j

/-- §6.9: ORTHODIR builds an `AᴴA`-orthogonal sequence of directions. -/
theorem inner_apply_orthodirP_eq_zero {m : ℕ} (hne : ∀ i < m, op A (orthodirP A b x₀ i) ≠ 0) :
    ∀ i < m, ∀ l < m, i ≠ l →
      inner 𝕜 (op A (orthodirP A b x₀ i)) (op A (orthodirP A b x₀ l)) = 0 :=
  inner_apply_eq_zero_of_recur A (orthodirP A b x₀) (fun j => op A (orthodirP A b x₀ j))
    (orthodirP_succ A b x₀) hne

theorem span_orthodirP_eq {m : ℕ} (hne : ∀ i < m, op A (orthodirP A b x₀ i) ≠ 0)
    (hm : m ≤ grade A (r₀ A b x₀)) :
    Submodule.span 𝕜 (Set.range fun i : Fin m => orthodirP A b x₀ (i : ℕ))
      = krylov A (r₀ A b x₀) m :=
  span_eq_krylov A b x₀ (orthodirP A b x₀) (inner_apply_orthodirP_eq_zero A b x₀ hne) hne
    (orthodirP_mem_krylov A b x₀) hm

/-- **ORTHODIR is mathematically equivalent to full GMRES**, by Lemma 6.21. -/
theorem orthodirX_isMinResIterate {m : ℕ} (hne : ∀ i < m, op A (orthodirP A b x₀ i) ≠ 0)
    (hm : m ≤ grade A (r₀ A b x₀)) :
    Krylov.IsMinResIterate (op A) b x₀ m (orthodirX A b x₀ m) := by
  refine isMinResIterate_of_orthogonalDirections A b x₀ (orthodirP A b x₀)
    (inner_apply_orthodirP_eq_zero A b x₀ hne) hne (span_orthodirP_eq A b x₀ hne hm)
    (orthodirX A b x₀) (orthodirX_zero A b x₀) fun j => ?_
  rw [orthodirX_succ, orthodirAlpha_eq, orthodirR_eq_residual]

/-! ### ORTHOMIN(k) and GCR(m): the truncated and restarted variants -/

/-- **ORTHOMIN(k)** run for `j` steps: Algorithm 6.21 with lines 6–7 truncated to the last `k`
directions. Being truncated it satisfies no global minimization property, and the book proves
none; the only statement about it is `orthomin_eq_gcr`. -/
noncomputable def orthominAux (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (k : ℕ) :
    ℕ → 𝔼 × 𝔼 × 𝔼
  | 0 => (x₀, b - op A x₀, b - op A x₀)
  | j + 1 => orthominBody A k fun i : Fin (j + 1) => orthominAux A b x₀ k (i : ℕ)
  termination_by j => j
  decreasing_by exact i.isLt

/-- The `j`-th ORTHOMIN(k) iterate `x_j`. -/
noncomputable def orthominX (k j : ℕ) : 𝔼 := (orthominAux A b x₀ k j).1

/-- The `j`-th ORTHOMIN(k) residual `r_j`. -/
noncomputable def orthominR (k j : ℕ) : 𝔼 := (orthominAux A b x₀ k j).2.1

/-- The `j`-th ORTHOMIN(k) direction `p_j`. -/
noncomputable def orthominP (k j : ℕ) : 𝔼 := (orthominAux A b x₀ k j).2.2

@[simp] theorem orthominX_zero (k : ℕ) : orthominX A b x₀ k 0 = x₀ := by
  rw [orthominX, orthominAux]

@[simp] theorem orthominR_zero (k : ℕ) : orthominR A b x₀ k 0 = b - op A x₀ := by
  rw [orthominR, orthominAux]

@[simp] theorem orthominP_zero (k : ℕ) : orthominP A b x₀ k 0 = orthominR A b x₀ k 0 := by
  rw [orthominP, orthominR, orthominAux]

/-- §6.9: **ORTHOMIN(k) is GCR for `k ≥ m`** — with a window at least as wide as the number of
steps taken, no direction is dropped. -/
theorem orthomin_eq_gcr {k : ℕ} : ∀ j ≤ k, orthominAux A b x₀ k j = gcrAux A b x₀ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    cases j with
    | zero => rw [orthominAux, gcrAux]
    | succ j =>
      have hs : (fun i : Fin (j + 1) => orthominAux A b x₀ k (i : ℕ))
          = fun i : Fin (j + 1) => gcrAux A b x₀ (i : ℕ) :=
        funext fun i => ih (i : ℕ) (by omega) (by omega)
      rw [orthominAux, gcrAux, hs, orthominBody_eq_gcrBody A hj]

theorem orthominX_eq_gcrX {k m : ℕ} (hk : m ≤ k) : orthominX A b x₀ k m = gcrX A b x₀ m := by
  rw [orthominX, gcrX, orthomin_eq_gcr A b x₀ m hk]

/-- One cycle of **GCR(m)**: `m` steps of Algorithm 6.21 from `x_0`. -/
noncomputable def gcrCycle (A : Matrix (Fin n) (Fin n) 𝕜) (b : 𝔼) (m : ℕ) (x₀ : 𝔼) : 𝔼 :=
  gcrX A b x₀ m

/-- **GCR(m)**: the restarted iterate after `k` cycles of `m` steps. Being restarted it
satisfies no global minimization property, and the book proves none. -/
noncomputable def gcrRestarted (A : Matrix (Fin n) (Fin n) 𝕜) (b : 𝔼) (m : ℕ) (x₀ : 𝔼)
    (k : ℕ) : 𝔼 :=
  (gcrCycle A b m)^[k] x₀

@[simp] theorem gcrRestarted_zero (m : ℕ) : gcrRestarted A b m x₀ 0 = x₀ := rfl

theorem gcrRestarted_succ (m k : ℕ) :
    gcrRestarted A b m x₀ (k + 1) = gcrCycle A b m (gcrRestarted A b m x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-! ### The GMRES approximation -/

/-- The book's grade `μ` of `v_1` is the grade of `r_0`: the two starting vectors are
proportional. -/
theorem grade_r₀_eq_grade_v₁ : grade A (r₀ A b x₀) = grade A (v₁ A b x₀) := by
  rw [grade_eq, grade_v₁]

/-- **GCR computes the GMRES approximation** (§6.9: GCR is "mathematically equivalent to the
full GMRES algorithm"). -/
theorem gcrX_eq_gmresFixed (hA : IsUnit A) {m : ℕ} (hne : ∀ i < m, op A (gcrP A b x₀ i) ≠ 0)
    (hm : m ≤ grade A (r₀ A b x₀)) : gcrX A b x₀ m = gmresFixed A b x₀ m := by
  have hm' : m ≤ grade A (v₁ A b x₀) := by rwa [← grade_r₀_eq_grade_v₁]
  obtain ⟨z, -, hz⟩ :=
    Krylov.existsUnique_isMinResIterate_of_injective (injective_op_of_isUnit hA) b x₀ m
  rw [hz _ (gcrX_isMinResIterate A b x₀ hne hm),
    hz _ (gmresFixed_isMinResIterate A b x₀ hm' (isUnit_R_of_isUnit A b x₀ hA hm'))]

/-- **ORTHODIR computes the GMRES approximation** (§6.9). -/
theorem orthodirX_eq_gmresFixed (hA : IsUnit A) {m : ℕ}
    (hne : ∀ i < m, op A (orthodirP A b x₀ i) ≠ 0) (hm : m ≤ grade A (r₀ A b x₀)) :
    orthodirX A b x₀ m = gmresFixed A b x₀ m := by
  have hm' : m ≤ grade A (v₁ A b x₀) := by rwa [← grade_r₀_eq_grade_v₁]
  obtain ⟨z, -, hz⟩ :=
    Krylov.existsUnique_isMinResIterate_of_injective (injective_op_of_isUnit hA) b x₀ m
  rw [hz _ (orthodirX_isMinResIterate A b x₀ hne hm),
    hz _ (gmresFixed_isMinResIterate A b x₀ hm' (isUnit_R_of_isUnit A b x₀ hA hm'))]

end General

/-! ### The results of §6.9, in the book's real setting -/

section BookResults

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))

/-- **Lemma 6.21** with **(6.104)** and **(6.105)**. Let `p_0, p_1, …, p_{m-1}` be a sequence of
vectors such that `{p_0, …, p_{j-1}}` is a basis of `𝒦_j(A, r_0)` for each `j ≤ m` — here: they
span `𝒦_m` and are `AᴴA`-orthogonal with `A p_i ≠ 0` — and let `x_j` be the sequence produced by
`x_{j+1} = x_j + ((r_j, A p_j)/(A p_j, A p_j)) p_j` (6.105) from `x_0`. Then `x_m` minimizes the
residual norm over `x_0 + 𝒦_m(A, r_0)`, and it is given in closed form by
`x_m = x_0 + ∑_{i<m} ((r_0, A p_i)/(A p_i, A p_i)) p_i` (6.104). -/
theorem lemma_6_21 {m : ℕ} (p : ℕ → EuclideanSpace ℝ (Fin n))
    (horth : ∀ i < m, ∀ l < m, i ≠ l → inner ℝ (op A (p i)) (op A (p l)) = 0)
    (hne : ∀ i < m, op A (p i) ≠ 0)
    (hspan : Submodule.span ℝ (Set.range fun i : Fin m => p (i : ℕ)) = krylov A (r₀ A b x₀) m)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx0 : x 0 = x₀)
    (hstep : ∀ j, x (j + 1) = x j +
      (inner ℝ (op A (p j)) (b - op A (x j)) / inner ℝ (op A (p j)) (op A (p j))) • p j) :
    Krylov.IsMinResIterate (op A) b x₀ m (x m) ∧
      x m = x₀ + ∑ i ∈ Finset.range m,
        (inner ℝ (op A (p i)) (r₀ A b x₀) / inner ℝ (op A (p i)) (op A (p i))) • p i :=
  ⟨isMinResIterate_of_orthogonalDirections A b x₀ p horth hne hspan x hx0 hstep,
    eq_6_104 A b x₀ p horth x hx0 hstep⟩

/-- **§6.9**: **Algorithm 6.21** (GCR) is mathematically equivalent to the full GMRES algorithm
— its directions are `AᴴA`-orthogonal, its iterate minimizes the residual over
`x_0 + 𝒦_m(A, r_0)`, and for a nonsingular `A` it equals the GMRES approximation. -/
theorem alg_6_21_eq_gmres (hA : IsUnit A) {m : ℕ} (hne : ∀ i < m, op A (gcrP A b x₀ i) ≠ 0)
    (hm : m ≤ grade A (r₀ A b x₀)) :
    (∀ i < m, ∀ l < m, i ≠ l → inner ℝ (op A (gcrP A b x₀ i)) (op A (gcrP A b x₀ l)) = 0) ∧
      Krylov.IsMinResIterate (op A) b x₀ m (gcrX A b x₀ m) ∧
      gcrX A b x₀ m = gmresFixed A b x₀ m :=
  ⟨inner_apply_gcrP_eq_zero A b x₀ hne, gcrX_isMinResIterate A b x₀ hne hm,
    gcrX_eq_gmresFixed A b x₀ hA hne hm⟩

/-- **§6.9**: **ORTHODIR** is mathematically equivalent to the full GMRES algorithm. -/
theorem orthodir_eq_gmres (hA : IsUnit A) {m : ℕ}
    (hne : ∀ i < m, op A (orthodirP A b x₀ i) ≠ 0) (hm : m ≤ grade A (r₀ A b x₀)) :
    (∀ i < m, ∀ l < m, i ≠ l →
        inner ℝ (op A (orthodirP A b x₀ i)) (op A (orthodirP A b x₀ l)) = 0) ∧
      Krylov.IsMinResIterate (op A) b x₀ m (orthodirX A b x₀ m) ∧
      orthodirX A b x₀ m = gmresFixed A b x₀ m :=
  ⟨inner_apply_orthodirP_eq_zero A b x₀ hne, orthodirX_isMinResIterate A b x₀ hne hm,
    orthodirX_eq_gmresFixed A b x₀ hA hne hm⟩

/-- **§6.9**: **ORTHOMIN(k)** coincides with GCR as long as the window `k` is at least the
number of steps taken. -/
theorem orthomin_eq_gcr_book {k m : ℕ} (hk : m ≤ k) :
    orthominX A b x₀ k m = gcrX A b x₀ m :=
  orthominX_eq_gcrX A b x₀ hk

end BookResults

end SaadSparse.Ch06
