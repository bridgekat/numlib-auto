import Mathlib.Data.Matrix.ColumnRowPartitioned
import Numlib.FloatingPoint.Program
import Numlib.FloatingPoint.Substitution

/-!
# Golub–Van Loan §3.1: triangular systems

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition, §3.1:
the row-oriented (dot product) substitutions, Algorithms 3.1.1–3.1.2, with their backward errors
(3.1.1)–(3.1.2); the column-oriented (saxpy) substitutions, Algorithms 3.1.3–3.1.4; the block
forward elimination (3.1.4) for `L X = B`; nonsquare triangular systems (§3.1.6); and the algebra
of triangular matrices (§3.1.7).

## Design

Every algorithm is a program generic in a monad `M` and a rounding hook `rnd : ℝ → M ℝ`
(`Numlib/FloatingPoint/Program`, conventions 1–14 of `NumlibSurface/GolubVanLoan`), overwriting
`b : Fin n → ℝ` by `Function.update`. Indices are 0-based: the book's `b(1)` is `b 0`, its
`L(i,1:i-1) · b(1:i-1)` is the accumulation `FloatingPoint.dotAccum` over the index list
`(List.finRange n).filter (· < i)` (Algorithm 1.1.1 on the prefix).

The backbone specifications are `Matrix.forwardSubst` and `Matrix.backSubst`
(`Numlib/Direct/Substitution`), and the relational predicates of
`Numlib/FloatingPoint/Substitution`: the inner-product order `FloatingPoint.RoundsForwardSubstDot`
/ `RoundsBackSubstDot` for the row versions, the running differences
`FloatingPoint.RoundsForwardSubst` / `RoundsBackSubst` for the column versions. Each algorithm
carries (convention 12):

* `…_rounds`, the bridge: every run in the relational model (`M := SetM`, `rnd := fp.round`)
  satisfies the relational predicate, with no hypothesis on the matrix;
* `…_spec`, the exact semantics, read off the bridge at `FloatingPoint.RoundingModel.exact ℝ`
  (convention 11): the `Id` run is a run of the exact model, where the predicate pins the output to
  `forwardSubst`/`backSubst`;
* `equation_3_1_1`, `equation_3_1_2`, `…_rounding`: the book's backward errors in their rigorous
  form `|F| ≤ γ_n |L|` (`FloatingPoint.gamma fp.u n`), whose first-order form is the book's
  `n u |L| + O(u²)`.

Two loop lemmas carry the bridges. A loop that writes entry `i` at step `i`, reading only the
entries written before it and its own initial value, satisfies any row property that is stable
under changes of the later entries (`SetM.forall_mem_run_foldlM_update_of_nodup`): the row
versions, one loop over any sorted index list of any linear order. The column versions are likewise
one loop over any linear order (`FloatingPoint.roundsForwardSubst_of_mem_run_colSubst`). In both
pairs back substitution is the forward loop on the dual order `(Fin n)ᵒᵈ`, as in the backbone
(`FloatingPoint.roundsBackSubst_iff_roundsForwardSubst_toDual`,
`FloatingPoint.roundsBackSubstDot_iff_roundsForwardSubstDot_toDual`).

## Main results

* `algorithm_3_1_1` … `algorithm_3_1_4` with `_rounds` and `_spec`;
* `equation_3_1_1`, `equation_3_1_2`, `algorithm_3_1_3_rounding`, `algorithm_3_1_4_rounding`;
* `blockForwardElim`, the block forward elimination (3.1.4), and `equation_3_1_4`, its exact
  semantics (`L X = B`), through `forwardSubstColOn_exact`;
* `unitForwardSubstColOn`, the unit lower triangular solve that does not divide by the unit
  diagonal (convention 2), used by the block LU Algorithms 3.2.3–3.2.4;
* `nonsquareLower_tall`, `nonsquareLower_wide` (§3.1.6);
* `triangular_inv`, `triangular_mul`, `unitTriangular_inv`, `unitTriangular_mul` (§3.1.7).

## Not formalized here

The flop counts and the level-3 fraction (§3.1.5); the least-squares remark of §3.1.6; the
numerical example of §3.1.3; the Problems.
-/

open FloatingPoint Matrix

namespace GolubVanLoan.Chapter03

/-! ### Loop lemmas -/

/-- On `Fin n`, the minimal index is `0`. -/
private theorem fin_isMin_iff {n : ℕ} (i : Fin n) : IsMin i ↔ (i : ℕ) = 0 := by
  constructor
  · intro h
    by_contra h0
    exact h.not_lt (b := ⟨0, by omega⟩) (by rw [Fin.lt_def]; dsimp only; omega)
  · intro h j _
    rw [Fin.le_def, h]
    exact Nat.zero_le _

/-- On `Fin n`, the maximal index is `n - 1`. -/
private theorem fin_isMax_iff {n : ℕ} (i : Fin n) : IsMax i ↔ (i : ℕ) = n - 1 := by
  constructor
  · intro h
    by_contra h0
    exact h.not_lt (b := ⟨n - 1, by omega⟩) (by rw [Fin.lt_def]; dsimp only; omega)
  · intro h j _
    rw [Fin.le_def, h]
    omega

/-! ### The four substitution algorithms -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 3.1.1 (Row-Oriented Forward Substitution).** "If `L ∈ ℝ^{n×n}` is lower
triangular and `b ∈ ℝⁿ`, then this algorithm overwrites `b` with the solution to `Lx = b`. `L` is
assumed to be nonsingular."
```
b(1) = b(1)/L(1,1)
for i = 2:n
    b(i) = (b(i) - L(i,1:i-1) · b(1:i-1))/L(i,i)
end
```
The first row divides only; the dot product `L(i,1:i-1) · b(1:i-1)` is Algorithm 1.1.1 on the
prefix, accumulated from `0` (`FloatingPoint.dotAccum`), then subtracted from `b(i)`; every
product, sum, difference and quotient is rounded. -/
noncomputable def algorithm_3_1_1 {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun (b : Fin n → ℝ) (i : Fin n) => do
    let t ← if (i : ℕ) = 0 then pure (b i) else do
      let s ← dotAccum rnd ((List.finRange n).filter (· < i)) (L i) b 0
      rnd (b i - s)
    let x ← rnd (t / L i i)
    pure (Function.update b i x)) b

/-- **Algorithm 3.1.2 (Row-Oriented Back Substitution).** "If `U ∈ ℝ^{n×n}` is upper triangular
and `b ∈ ℝⁿ`, then the following algorithm overwrites `b` with the solution to `Ux = b`. `U` is
assumed to be nonsingular."
```
b(n) = b(n)/U(n,n)
for i = n-1:-1:1
    b(i) = (b(i) - U(i,i+1:n) · b(i+1:n))/U(i,i)
end
```
The last row divides only; the dot product runs over `j > i` in increasing order. -/
noncomputable def algorithm_3_1_2 {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    M (Fin n → ℝ) :=
  (List.finRange n).reverse.foldlM (fun (b : Fin n → ℝ) (i : Fin n) => do
    let t ← if (i : ℕ) = n - 1 then pure (b i) else do
      let s ← dotAccum rnd ((List.finRange n).filter (i < ·)) (U i) b 0
      rnd (b i - s)
    let x ← rnd (t / U i i)
    pure (Function.update b i x)) b

/-- **Algorithm 3.1.3 (Column-Oriented Forward Substitution).** "If the matrix `L ∈ ℝ^{n×n}` is
lower triangular and `b ∈ ℝⁿ`, then this algorithm overwrites `b` with the solution to `Lx = b`.
`L` is assumed to be nonsingular."
```
for j = 1:n-1
    b(j) = b(j)/L(j,j)
    b(j+1:n) = b(j+1:n) - b(j) · L(j+1:n,j)
end
b(n) = b(n)/L(n,n)
```
The book's final `b(n) = b(n)/L(n,n)` is the last iteration, whose saxpy is empty. -/
noncomputable def algorithm_3_1_3 {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun (b : Fin n → ℝ) j => do
      let bj ← rnd (b j / L j j)
      ((List.finRange n).filter (j < ·)).foldlM
        (fun (b : Fin n → ℝ) i => do
          let p ← rnd (b j * L i j)
          let bi ← rnd (b i - p)
          pure (Function.update b i bi))
        (Function.update b j bj))
    b

/-- **Algorithm 3.1.4 (Column-Oriented Back Substitution).** "If `U ∈ ℝ^{n×n}` is upper
triangular and `b ∈ ℝⁿ`, then this algorithm overwrites `b` with the solution to `Ux = b`. `U` is
assumed to be nonsingular."
```
for j = n:-1:2
    b(j) = b(j)/U(j,j)
    b(1:j-1) = b(1:j-1) - b(j) · U(1:j-1,j)
end
b(1) = b(1)/U(1,1)
```
The book's final `b(1) = b(1)/U(1,1)` is the last iteration, whose saxpy is empty. -/
noncomputable def algorithm_3_1_4 {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    M (Fin n → ℝ) :=
  (List.finRange n).reverse.foldlM (fun (b : Fin n → ℝ) j => do
      let bj ← rnd (b j / U j j)
      ((List.finRange n).filter (· < j)).foldlM
        (fun (b : Fin n → ℝ) i => do
          let p ← rnd (b j * U i j)
          let bi ← rnd (b i - p)
          pure (Function.update b i bi))
        (Function.update b j bj))
    b

end Programs

/-! ### The rounding bridges -/

section Bridges

variable (fp : RoundingModel ℝ) {n : ℕ}

/-- **Row-oriented forward substitution, over any linear order**: the loop "for `i` in increasing
order, `b(i) = (b(i) - L(i,c i) · b(c i))/L(i,i)`", the first row dividing only (`first i`, the
minimal index) and the dot product over the list `c i` of the indices below `i` accumulated from
`0` (`FloatingPoint.dotAccum`), computes in every run an admissible forward substitution in the
inner-product order, `FloatingPoint.RoundsForwardSubstDot`. Algorithm 3.1.1 is its instance on
`Fin n`, Algorithm 3.1.2 its instance on the dual order `(Fin n)ᵒᵈ`. -/
private theorem roundsForwardSubstDot_of_mem_run_rowSubst {ι : Type} [LinearOrder ι]
    (L : Matrix ι ι ℝ) {l : List ι} (hl : l.Pairwise (· < ·)) (hall : ∀ i, i ∈ l)
    (first : ι → Prop) [DecidablePred first] (hfirst : ∀ i, first i ↔ IsMin i)
    (c : ι → List ι) (hc : ∀ i, (c i).Nodup) (hcm : ∀ i j, j ∈ c i ↔ j < i) (b x : ι → ℝ)
    (hx : x ∈ (l.foldlM (fun (b : ι → ℝ) (i : ι) => do
      let t ← if first i then pure (b i) else do
        let s ← dotAccum fp.round (c i) (L i) b 0
        fp.round (b i - s)
      let x ← fp.round (t / L i i)
      pure (Function.update b i x)) b).run) :
    RoundsForwardSubstDot fp L b x := by
  have hnd : l.Nodup := hl.imp ne_of_lt
  let g : ι → (ι → ℝ) → SetM ℝ := fun i s =>
    if first i then fp.round (s i / L i i) else do
      let t ← dotAccum fp.round (c i) (L i) s 0
      let u ← fp.round (s i - t)
      fp.round (u / L i i)
  have hprog : l.foldlM (fun (b : ι → ℝ) (i : ι) => do
      let t ← if first i then pure (b i) else do
        let s ← dotAccum fp.round (c i) (L i) b 0
        fp.round (b i - s)
      let x ← fp.round (t / L i i)
      pure (Function.update b i x)) b =
      l.foldlM (fun s i => do let x ← g i s; pure (Function.update s i x)) b := by
    congr 1
    funext s i
    simp only [g]
    split_ifs <;> simp only [pure_bind, bind_assoc]
  rw [hprog] at hx
  have key := SetM.forall_mem_run_foldlM_update_of_nodup hnd g
    (fun i s x => (IsMin i → fp.Rounds (b i / L i i) x) ∧
      (¬ IsMin i → ∃ (o : List ι) (p : ι → ℝ) (s' t : ℝ), o.Nodup ∧
        (∀ j, j ∈ o ↔ j < i) ∧ (∀ j ∈ o, fp.Rounds (L i j * s j) (p j)) ∧
        RoundsSumFrom fp 0 (o.map p) s' ∧ fp.Rounds (b i - s') t ∧ fp.Rounds (t / L i i) x))
    b ?_ ?_ x hx
  · exact fun i => key i (hall i)
  · rintro p i q hl' s hs x hx
    have hsi : s i = b i := hs i fun h =>
      List.disjoint_of_nodup_append (hl' ▸ hnd) h List.mem_cons_self
    by_cases hi : first i
    · simp only [g, hi, ↓reduceIte] at hx
      refine ⟨fun _ => ?_, fun h => absurd ((hfirst i).1 hi) h⟩
      rw [← hsi]
      exact hx
    · simp only [g, hi, ↓reduceIte, SetM.mem_run_bind] at hx
      obtain ⟨s', hs', t, ht, hx⟩ := hx
      obtain ⟨pp, hpp, hsum⟩ := exists_of_mem_run_dotAccum (hc i) hs'
      refine ⟨fun h => absurd ((hfirst i).2 h) hi, fun _ =>
        ⟨_, pp, s', t, hc i, hcm i, hpp, hsum, ?_, hx⟩⟩
      rw [← hsi]
      exact ht
  · rintro p i q hl' s s' x hss ⟨h₁, h₂⟩
    refine ⟨h₁, fun hi => ?_⟩
    obtain ⟨o, pp, s₁, t, hnd', ho, hpp, hsum, ht, hx⟩ := h₂ hi
    refine ⟨o, pp, s₁, t, hnd', ho, fun j hj => ?_, hsum, ht, hx⟩
    have hjp : j ∈ p := List.mem_prefix_of_pairwise hl hl' (hall j) (ne_of_lt ((ho j).1 hj))
      (lt_asymm ((ho j).1 hj))
    rw [← hss j hjp]
    exact hpp j hj

/-- **The bridge of Algorithm 3.1.1**: every run in the relational model is an admissible forward
substitution in the inner-product order, `FloatingPoint.RoundsForwardSubstDot`. No hypothesis on
`L`. -/
theorem algorithm_3_1_1_rounds (L : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    ∀ x ∈ (algorithm_3_1_1 fp.round L b).run, RoundsForwardSubstDot fp L b x :=
  fun x hx => roundsForwardSubstDot_of_mem_run_rowSubst fp L (List.pairwise_lt_finRange n)
    List.mem_finRange (fun i => (i : ℕ) = 0) (fun i => (fin_isMin_iff i).symm)
    (fun i => (List.finRange n).filter (· < i)) (fun _ => (List.nodup_finRange n).filter _)
    (fun i j => by simp) b x hx

/-- **The bridge of Algorithm 3.1.2**: every run is an admissible back substitution in the
inner-product order, `FloatingPoint.RoundsBackSubstDot` — Algorithm 3.1.1's loop on the dual order
`(Fin n)ᵒᵈ`. No hypothesis on `U`. -/
theorem algorithm_3_1_2_rounds (U : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    ∀ x ∈ (algorithm_3_1_2 fp.round U b).run, RoundsBackSubstDot fp U b x := by
  intro x hx
  rw [roundsBackSubstDot_iff_roundsForwardSubstDot_toDual]
  refine roundsForwardSubstDot_of_mem_run_rowSubst (ι := (Fin n)ᵒᵈ) fp U
    (l := ((List.finRange n).reverse : List (Fin n)ᵒᵈ))
    (List.pairwise_reverse.2 (List.pairwise_lt_finRange n))
    (fun i => List.mem_reverse.2 (List.mem_finRange (OrderDual.ofDual i)))
    (fun i => ((OrderDual.ofDual i : Fin n) : ℕ) = n - 1)
    (fun i => (fin_isMax_iff (OrderDual.ofDual i)).symm.trans isMin_toDual_iff.symm)
    (fun i : (Fin n)ᵒᵈ =>
      ((List.finRange n).filter (fun j : Fin n => OrderDual.ofDual i < j) : List (Fin n)ᵒᵈ))
    (fun _ => (List.nodup_finRange n).filter _) (fun i j => ?_) b x hx
  change OrderDual.ofDual j ∈ (List.finRange n).filter
      (fun j : Fin n => decide (OrderDual.ofDual i < j)) ↔ OrderDual.ofDual i < OrderDual.ofDual j
  simp

/-- **The bridge of Algorithm 3.1.3** (the prototype's): every run is an admissible forward
substitution in the running-difference order, `FloatingPoint.RoundsForwardSubst`. No hypothesis on
`L`, and no idempotence: the relation starts from the unrounded `b i`. -/
theorem algorithm_3_1_3_rounds (L : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    ∀ x ∈ (algorithm_3_1_3 fp.round L b).run, RoundsForwardSubst fp L b x :=
  fun x hx => FloatingPoint.roundsForwardSubst_of_mem_run_colSubst fp L
    (List.pairwise_lt_finRange n) List.mem_finRange (fun j => (List.finRange n).filter (j < ·))
    (fun _ => (List.nodup_finRange n).filter _) (fun j i => by simp) b x hx

/-- **The bridge of Algorithm 3.1.4**: every run is an admissible back substitution,
`FloatingPoint.RoundsBackSubst` — Algorithm 3.1.3's loop on the dual order `(Fin n)ᵒᵈ`. -/
theorem algorithm_3_1_4_rounds (U : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    ∀ x ∈ (algorithm_3_1_4 fp.round U b).run, RoundsBackSubst fp U b x := by
  intro x hx
  rw [roundsBackSubst_iff_roundsForwardSubst_toDual]
  refine FloatingPoint.roundsForwardSubst_of_mem_run_colSubst (ι := (Fin n)ᵒᵈ) fp U
    (l := ((List.finRange n).reverse : List (Fin n)ᵒᵈ))
    (List.pairwise_reverse.2 (List.pairwise_lt_finRange n))
    (fun i => List.mem_reverse.2 (List.mem_finRange (OrderDual.ofDual i)))
    (fun j : (Fin n)ᵒᵈ =>
      ((List.finRange n).filter (fun i : Fin n => i < OrderDual.ofDual j) : List (Fin n)ᵒᵈ))
    (fun _ => (List.nodup_finRange n).filter _) (fun j i => ?_) b x hx
  change OrderDual.ofDual i ∈ (List.finRange n).filter
      (fun i : Fin n => decide (i < OrderDual.ofDual j)) ↔ OrderDual.ofDual i < OrderDual.ofDual j
  simp

end Bridges

/-! ### The exact semantics -/

section Exact

variable {n : ℕ}

/-- The exact run of Algorithm 3.1.1 is a run of the exact model. -/
private theorem algorithm_3_1_1_mem_exact (L : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    Id.run (algorithm_3_1_1 pure L b) ∈
      (algorithm_3_1_1 (RoundingModel.exact ℝ).round L b).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_3_1_1, dotAccum_pure, pure_bind, ite_pure, List.foldlM_pure,
    SetM.mem_run_pure]
  rfl

private theorem algorithm_3_1_2_mem_exact (U : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    Id.run (algorithm_3_1_2 pure U b) ∈
      (algorithm_3_1_2 (RoundingModel.exact ℝ).round U b).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_3_1_2, dotAccum_pure, pure_bind, ite_pure, List.foldlM_pure,
    SetM.mem_run_pure]
  rfl

private theorem algorithm_3_1_3_mem_exact (L : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    Id.run (algorithm_3_1_3 pure L b) ∈
      (algorithm_3_1_3 (RoundingModel.exact ℝ).round L b).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_3_1_3, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

private theorem algorithm_3_1_4_mem_exact (U : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    Id.run (algorithm_3_1_4 pure U b) ∈
      (algorithm_3_1_4 (RoundingModel.exact ℝ).round U b).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_3_1_4, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

/-- In exact arithmetic Algorithm 3.1.1 computes `Matrix.forwardSubst L b`, for every `L` (a zero
diagonal entry gives the same junk quotient on both sides). -/
theorem algorithm_3_1_1_eq_forwardSubst (L : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    Id.run (algorithm_3_1_1 pure L b) = L.forwardSubst b :=
  roundsForwardSubstDot_exact_iff.1
    (algorithm_3_1_1_rounds _ L b _ (algorithm_3_1_1_mem_exact L b))

/-- In exact arithmetic Algorithm 3.1.2 computes `Matrix.backSubst U b`, for every `U`. -/
theorem algorithm_3_1_2_eq_backSubst (U : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    Id.run (algorithm_3_1_2 pure U b) = U.backSubst b :=
  roundsBackSubstDot_exact_iff.1
    (algorithm_3_1_2_rounds _ U b _ (algorithm_3_1_2_mem_exact U b))

/-- In exact arithmetic Algorithm 3.1.3 computes `Matrix.forwardSubst L b`, for every `L`. -/
theorem algorithm_3_1_3_eq_forwardSubst (L : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    Id.run (algorithm_3_1_3 pure L b) = L.forwardSubst b :=
  roundsForwardSubst_exact_iff.1
    (algorithm_3_1_3_rounds _ L b _ (algorithm_3_1_3_mem_exact L b))

/-- In exact arithmetic Algorithm 3.1.4 computes `Matrix.backSubst U b`, for every `U`. -/
theorem algorithm_3_1_4_eq_backSubst (U : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    Id.run (algorithm_3_1_4 pure U b) = U.backSubst b :=
  roundsBackSubst_exact_iff.1
    (algorithm_3_1_4_rounds _ U b _ (algorithm_3_1_4_mem_exact U b))

/-- **Exact correctness of Algorithm 3.1.1**: for lower triangular nonsingular `L` (nonzero
diagonal, `Matrix.IsLowerTriangular.isUnit_iff`), the algorithm
overwrites `b` with the solution of `L x = b`. Read off the bridge at the exact model. -/
theorem algorithm_3_1_1_spec {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular)
    (hd : ∀ i, L i i ≠ 0) (b : Fin n → ℝ) : L *ᵥ Id.run (algorithm_3_1_1 pure L b) = b := by
  rw [algorithm_3_1_1_eq_forwardSubst]
  exact mulVec_forwardSubst b hL hd

/-- **Exact correctness of Algorithm 3.1.2**: for upper triangular `U` with nonzero diagonal, the
algorithm overwrites `b` with the solution of `U x = b`. -/
theorem algorithm_3_1_2_spec {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) (b : Fin n → ℝ) : U *ᵥ Id.run (algorithm_3_1_2 pure U b) = b := by
  rw [algorithm_3_1_2_eq_backSubst]
  exact mulVec_backSubst b hU hd

/-- **Exact correctness of Algorithm 3.1.3**: for lower triangular `L` with nonzero diagonal, the
algorithm overwrites `b` with the solution of `L x = b`. -/
theorem algorithm_3_1_3_spec {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular)
    (hd : ∀ i, L i i ≠ 0) (b : Fin n → ℝ) : L *ᵥ Id.run (algorithm_3_1_3 pure L b) = b := by
  rw [algorithm_3_1_3_eq_forwardSubst]
  exact mulVec_forwardSubst b hL hd

/-- **Exact correctness of Algorithm 3.1.4**: for upper triangular `U` with nonzero diagonal, the
algorithm overwrites `b` with the solution of `U x = b`. -/
theorem algorithm_3_1_4_spec {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) (b : Fin n → ℝ) : U *ᵥ Id.run (algorithm_3_1_4 pure U b) = b := by
  rw [algorithm_3_1_4_eq_backSubst]
  exact mulVec_backSubst b hU hd

end Exact

/-! ### The backward errors -/

section Rounding

variable {fp : RoundingModel ℝ} {n : ℕ}

/-- **(3.1.1)**, rigorous form: the solution `x̂` computed by Algorithm 3.1.1 satisfies
`(L + F) x̂ = b` with `|F| ≤ γ_n |L|` entrywise — the book's `|F| ≤ n u |L| + O(u²)`, since
`γ_n = n u / (1 - n u) = n u + O(u²)`. -/
theorem equation_3_1_1 (hu : fp.u < 1) (hn : (n : ℝ) * fp.u < 1)
    {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular) (hd : ∀ i, L i i ≠ 0)
    {b x : Fin n → ℝ} (hx : x ∈ (algorithm_3_1_1 fp.round L b).run) :
    ∃ F : Matrix (Fin n) (Fin n) ℝ, (∀ i j, |F i j| ≤ gamma fp.u n * |L i j|) ∧
      (L + F) *ᵥ x = b := by
  simpa using exists_roundsForwardSubstDot_eq hu (by simpa using hn) hL hd
    (algorithm_3_1_1_rounds fp L b x hx)

/-- **(3.1.2)**, rigorous form: the solution `x̂` computed by Algorithm 3.1.2 satisfies
`(U + F) x̂ = b` with `|F| ≤ γ_n |U|` entrywise (the book's `n u |U| + O(u²)`). -/
theorem equation_3_1_2 (hu : fp.u < 1) (hn : (n : ℝ) * fp.u < 1)
    {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0)
    {b x : Fin n → ℝ} (hx : x ∈ (algorithm_3_1_2 fp.round U b).run) :
    ∃ F : Matrix (Fin n) (Fin n) ℝ, (∀ i j, |F i j| ≤ gamma fp.u n * |U i j|) ∧
      (U + F) *ᵥ x = b := by
  simpa using exists_roundsBackSubstDot_eq hu (by simpa using hn) hU hd
    (algorithm_3_1_2_rounds fp U b x hx)

/-- §3.1.3, "the roundoff behavior of these implementations is essentially the same as for the
dot product versions", for Algorithm 3.1.3: `(L + F) x̂ = b` with `|F| ≤ γ_n |L|`, the constant of
(3.1.1) ([higham2002accuracy] Theorem 8.5 in the running-difference order). -/
theorem algorithm_3_1_3_rounding (hu : fp.u < 1) (hn : (n : ℝ) * fp.u < 1)
    {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular) (hd : ∀ i, L i i ≠ 0)
    {b x : Fin n → ℝ} (hx : x ∈ (algorithm_3_1_3 fp.round L b).run) :
    ∃ F : Matrix (Fin n) (Fin n) ℝ, (∀ i j, |F i j| ≤ gamma fp.u n * |L i j|) ∧
      (L + F) *ᵥ x = b := by
  simpa using exists_roundsForwardSubst_eq hu (by simpa using hn) hL hd
    (algorithm_3_1_3_rounds fp L b x hx)

/-- §3.1.3 for Algorithm 3.1.4: `(U + F) x̂ = b` with `|F| ≤ γ_n |U|`, the constant of (3.1.2). -/
theorem algorithm_3_1_4_rounding (hu : fp.u < 1) (hn : (n : ℝ) * fp.u < 1)
    {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.IsUpperTriangular) (hd : ∀ i, U i i ≠ 0)
    {b x : Fin n → ℝ} (hx : x ∈ (algorithm_3_1_4 fp.round U b).run) :
    ∃ F : Matrix (Fin n) (Fin n) ℝ, (∀ i j, |F i j| ≤ gamma fp.u n * |U i j|) ∧
      (U + F) *ᵥ x = b := by
  simpa using exists_roundsBackSubst_eq hu (by simpa using hn) hU hd
    (algorithm_3_1_4_rounds fp U b x hx)

end Rounding

/-! ### Multiple right-hand sides: block forward elimination (3.1.4) -/

section Block

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- Column-oriented forward substitution (Algorithm 3.1.3) on the rows and columns of an index
list `o`, the book's "solve `L_JJ X_J = B_J`" for a diagonal block given by its index list
(convention 10); on `List.finRange n` it is `algorithm_3_1_3` (`forwardSubstColOn_finRange`). -/
noncomputable def forwardSubstColOn {n : ℕ} (o : List (Fin n)) (L : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) : M (Fin n → ℝ) :=
  o.foldlM (fun (b : Fin n → ℝ) j => do
      let bj ← rnd (b j / L j j)
      (o.filter (j < ·)).foldlM
        (fun (b : Fin n → ℝ) i => do
          let p ← rnd (b j * L i j)
          let bi ← rnd (b i - p)
          pure (Function.update b i bi))
        (Function.update b j bj))
    b

/-- On the full index list the block substitution is Algorithm 3.1.3. -/
theorem forwardSubstColOn_finRange {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    forwardSubstColOn rnd (List.finRange n) L b = algorithm_3_1_3 rnd L b :=
  rfl

/-- **The unit lower triangular solve** on the rows and columns of an index list `o`: the loop of
`forwardSubstColOn` for a unit lower triangular `L`, whose division by the unit diagonal is not
performed (convention 2; "unit triangular solves inside factorizations do not divide", §3.1.7):
for `j` in `o`, `b(i) = b(i) - b(j) L(i,j)` for the later `i` of `o`, every product and difference
rounded. The diagonal of `L` is not read. It is the solve with `L₁₁`, `L_kk` of the block LU
Algorithms 3.2.3 and 3.2.4. -/
noncomputable def unitForwardSubstColOn {n : ℕ} (o : List (Fin n))
    (L : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : M (Fin n → ℝ) :=
  o.foldlM (fun (b : Fin n → ℝ) j =>
      (o.filter (j < ·)).foldlM
        (fun (b : Fin n → ℝ) i => do
          let p ← rnd (b j * L i j)
          let bi ← rnd (b i - p)
          pure (Function.update b i bi)) b)
    b

/-- **(3.1.4), block forward elimination** for `L X = B` with `B ∈ ℝ^{n×q}`:
```
for j = 1:N
    Solve L_jj X_j = B_j
    for i = j+1:N
        B_i = B_i - L_ij X_j
    end
end
```
The blocks are the fibres of a labelling `blk : Fin n → Fin N` (contiguous when `blk` is monotone;
no divisibility of `n` by `N` is assumed, P3.1.3). The solve is Algorithm 3.1.3 on the rows of block
`J`, column by column; the block saxpy `B_I = B_I - L_IJ X_J` is carried out row by row for the
rows of the later blocks, each entry `B(i,c)` receiving the rounded products `L(i,j) X(j,c)`,
`j` in block `J`, as rounded running differences. -/
noncomputable def blockForwardElim {n N q : ℕ} (blk : Fin n → Fin N)
    (L : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin q) ℝ) :
    M (Matrix (Fin n) (Fin q) ℝ) :=
  (List.finRange N).foldlM (fun (B : Matrix (Fin n) (Fin q) ℝ) J => do
    let B ← (List.finRange q).foldlM (fun (B : Matrix (Fin n) (Fin q) ℝ) c => do
      let x ← forwardSubstColOn rnd ((List.finRange n).filter (blk · = J)) L (fun i => B i c)
      pure (B.updateCol c x)) B
    ((List.finRange n).filter (J < blk ·)).foldlM (fun (B : Matrix (Fin n) (Fin q) ℝ) i =>
      (List.finRange q).foldlM (fun (B : Matrix (Fin n) (Fin q) ℝ) c =>
        ((List.finRange n).filter (blk · = J)).foldlM (fun (B : Matrix (Fin n) (Fin q) ℝ) j => do
          let p ← rnd (L i j * B j c)
          let v ← rnd (B i c - p)
          pure (B.updateRow i (Function.update (B i) c v))) B) B) B) B

end Block

/-! ### The exact semantics of (3.1.4) -/

section BlockExact

/-- In exact arithmetic, a loop subtracting `b j · L(i,j)` from entry `i` for every listed `i`
(which does not include `j`) subtracts once from each listed entry. -/
private theorem foldl_saxpy_apply {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (j : Fin n)
    {c : List (Fin n)} (hc : c.Nodup) (hjc : j ∉ c) (b : Fin n → ℝ) (i : Fin n) :
    c.foldl (fun (b : Fin n → ℝ) i => Function.update b i (b i - b j * L i j)) b i =
      if i ∈ c then b i - b j * L i j else b i := by
  induction c generalizing b with
  | nil => simp
  | cons a c ih =>
    rcases List.nodup_cons.1 hc with ⟨ha, hc'⟩
    have hja : j ≠ a := fun h => hjc (h ▸ List.mem_cons_self)
    rw [List.foldl_cons, ih hc' (fun h => hjc (List.mem_cons_of_mem _ h)),
      Function.update_of_ne hja]
    by_cases hia : i = a
    · subst hia
      simp [ha]
    · simp [hia]

/-- **Column-oriented forward substitution on a sorted index list, in exact arithmetic**: the rows
off the list keep their values, and every listed row `i` satisfies `∑_{j ∈ o} L(i,j) y(j) = b(i)`
(for lower triangular `L` with nonzero diagonal on the list). -/
theorem forwardSubstColOn_exact {n : ℕ} {o : List (Fin n)} (ho : o.Pairwise (· < ·))
    {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular) (hd : ∀ i ∈ o, L i i ≠ 0)
    (b : Fin n → ℝ) :
    (∀ i, i ∉ o → Id.run (forwardSubstColOn pure o L b) i = b i) ∧
      ∀ i ∈ o, (o.map fun j => L i j * Id.run (forwardSubstColOn pure o L b) j).sum = b i := by
  have hprog : Id.run (forwardSubstColOn pure o L b) = o.foldl (fun (b : Fin n → ℝ) j =>
      (o.filter (j < ·)).foldl (fun (b : Fin n → ℝ) i => Function.update b i (b i - b j * L i j))
        (Function.update b j (b j / L j j))) b := by
    simp only [forwardSubstColOn, List.idRun_foldlM, pure_bind, Id.run_pure]
  rw [hprog]
  have hnd : o.Nodup := ho.imp ne_of_lt
  refine List.foldl_prefix_induction (l := o) _
    (fun (p : List (Fin n)) (s : Fin n → ℝ) => (∀ i, i ∉ o → s i = b i) ∧
      (∀ i ∈ p, (p.map fun j => L i j * s j).sum = b i) ∧
      ∀ i ∈ o, i ∉ p → s i = b i - (p.map fun j => L i j * s j).sum)
    ⟨fun _ _ => rfl, by simp, by simp⟩ ?_ |> fun h => ⟨h.1, h.2.1⟩
  rintro p x q hpq s ⟨h₁, h₂, h₃⟩
  rw [hpq] at ho hnd
  have hpx : ∀ j ∈ p, j < x := fun j hj =>
    (List.pairwise_append.1 ho).2.2 j hj x List.mem_cons_self
  have hxq : ∀ j ∈ q, x < j := fun j hj =>
    List.rel_of_pairwise_cons (List.pairwise_append.1 ho).2.1 hj
  have hxo : x ∈ p ++ x :: q := List.mem_append.2 (Or.inr List.mem_cons_self)
  have hxp : x ∉ p := fun h => lt_irrefl x (hpx x h)
  set s₁ := Function.update s x (s x / L x x) with hs₁
  have hs₂ : ∀ i, ((p ++ x :: q).filter (x < ·)).foldl
      (fun (b : Fin n → ℝ) i => Function.update b i (b i - b x * L i x)) s₁ i =
      if i ∈ p ++ x :: q ∧ x < i then s₁ i - s₁ x * L i x else s₁ i := fun i => by
    rw [foldl_saxpy_apply L x (hnd.filter _) (by simp)]
    simp only [List.mem_filter, decide_eq_true_eq]
  simp only [hpq] at h₁ h₃ ⊢
  have hx₂ : s₁ x = s x / L x x := by rw [hs₁, Function.update_self]
  have hp₂ : ∀ j ∈ p, (if j ∈ p ++ x :: q ∧ x < j then s₁ j - s₁ x * L j x else s₁ j) = s j :=
    fun j hj => by
      rw [ite_eq_right fun h => lt_asymm h.2 (hpx j hj), hs₁,
        Function.update_of_ne (ne_of_lt (hpx j hj))]
  have hsum : ∀ i, (p.map fun j => L i j *
      (if j ∈ p ++ x :: q ∧ x < j then s₁ j - s₁ x * L j x else s₁ j)).sum =
      (p.map fun j => L i j * s j).sum := fun i => by
    congr 1
    exact List.map_congr_left fun j hj => by rw [hp₂ j hj]
  have hxx : (if x ∈ p ++ x :: q ∧ x < x then s₁ x - s₁ x * L x x else s₁ x) = s x / L x x := by
    rw [ite_eq_right fun h => lt_irrefl x h.2, hx₂]
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi hip => ?_⟩
  · rw [hs₂, ite_eq_right fun h => hi h.1, hs₁,
      Function.update_of_ne (fun (h : i = x) => hi (h ▸ hxo))]
    exact h₁ i hi
  · simp only [hs₂, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, add_zero]
    rw [hsum, hxx]
    rcases List.mem_append.1 hi with hi | hi
    · rw [hL (OrderDual.toDual_lt_toDual.2 (hpx i hi)), zero_mul, add_zero]
      exact h₂ i hi
    · rw [List.mem_singleton.1 hi, mul_div_cancel₀ _ (hd x (hpq ▸ hxo)),
        h₃ x hxo hxp]
      ring
  · have hip' : i ∉ p := fun h => hip (List.mem_append_left _ h)
    have hix : i ≠ x := fun h => hip (List.mem_append.2 (Or.inr (h ▸ List.mem_singleton_self x)))
    have hiq : x < i := by
      rcases List.mem_append.1 hi with h | h
      · exact absurd h hip'
      · rcases List.mem_cons.1 h with h | h
        · exact absurd h hix
        · exact hxq i h
    simp only [hs₂, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, add_zero]
    rw [hsum, hxx, ite_eq_left ⟨hi, hiq⟩, hx₂, hs₁, Function.update_of_ne hix, h₃ i hi hip']
    ring

/-- **The unit solve in exact arithmetic** is the column-oriented solve when the diagonal of `L` on
the list is `1`: the skipped division is `b(j)/1 = b(j)`. -/
theorem unitForwardSubstColOn_id_eq {n : ℕ} {o : List (Fin n)} {L : Matrix (Fin n) (Fin n) ℝ}
    (hL : ∀ j ∈ o, L j j = 1) (b : Fin n → ℝ) :
    Id.run (unitForwardSubstColOn pure o L b) = Id.run (forwardSubstColOn pure o L b) := by
  simp only [unitForwardSubstColOn, forwardSubstColOn, List.idRun_foldlM, pure_bind, Id.run_pure]
  exact List.foldl_ext _ _ _ fun b j hj => by rw [hL j hj, div_one, Function.update_eq_self]

/-- In exact arithmetic, the innermost loop of the block saxpy of (3.1.4): entry `(i,c)` receives
`L(i,j) B(j,c)` subtracted for every listed `j` (rows off `i`), every other entry is kept. -/
private theorem foldl_blockSaxpy_entry {n q : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    {o : List (Fin n)} {i : Fin n} (hi : i ∉ o) (c : Fin q) (B : Matrix (Fin n) (Fin q) ℝ)
    (r : Fin n) (s : Fin q) :
    o.foldl (fun (B : Matrix (Fin n) (Fin q) ℝ) j =>
        B.updateRow i (Function.update (B i) c (B i c - L i j * B j c))) B r s =
      if r = i ∧ s = c then B i c - (o.map fun j => L i j * B j c).sum else B r s := by
  induction o generalizing B with
  | nil =>
    simp only [List.foldl_nil, List.map_nil, List.sum_nil, sub_zero]
    split_ifs with h
    · rw [h.1, h.2]
    · rfl
  | cons a o ih =>
    rw [List.foldl_cons, ih (fun h => hi (List.mem_cons_of_mem _ h))]
    have hB : ∀ j, j ≠ i →
        (B.updateRow i (Function.update (B i) c (B i c - L i a * B a c))) j c = B j c :=
      fun j hj => by rw [updateRow_ne hj]
    have hmap : (o.map fun j => L i j *
        (B.updateRow i (Function.update (B i) c (B i c - L i a * B a c))) j c) =
        o.map fun j => L i j * B j c :=
      List.map_congr_left fun j hj => by
        rw [hB j fun h => hi (h ▸ List.mem_cons_of_mem _ hj)]
    rw [hmap]
    by_cases hr : r = i ∧ s = c
    · simp only [hr, and_self, ↓reduceIte, updateRow_self, Function.update_self, List.map_cons,
        List.sum_cons]
      ring
    · simp only [hr, ↓reduceIte, updateRow_apply]
      split_ifs with h
      · rw [h, Function.update_of_ne fun h' => hr ⟨h, h'⟩]
      · rfl

/-- The block saxpy of (3.1.4) for one row `i` over a duplicate-free list of columns. -/
private theorem foldl_blockSaxpy_row {n q : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    {o : List (Fin n)} {i : Fin n} (hi : i ∉ o) {cs : List (Fin q)} (hcs : cs.Nodup)
    (B : Matrix (Fin n) (Fin q) ℝ) (r : Fin n) (s : Fin q) :
    cs.foldl (fun (B : Matrix (Fin n) (Fin q) ℝ) c =>
        o.foldl (fun (B : Matrix (Fin n) (Fin q) ℝ) j =>
          B.updateRow i (Function.update (B i) c (B i c - L i j * B j c))) B) B r s =
      if r = i ∧ s ∈ cs then B i s - (o.map fun j => L i j * B j s).sum else B r s := by
  induction cs generalizing B with
  | nil => simp
  | cons a cs ih =>
    rcases List.nodup_cons.1 hcs with ⟨ha, hcs'⟩
    rw [List.foldl_cons, ih hcs']
    have hB := foldl_blockSaxpy_entry L hi a B
    by_cases hsa : s = a
    · subst hsa
      simp [ha, hB]
    · have hB' : ∀ r', o.foldl (fun (B : Matrix (Fin n) (Fin q) ℝ) j =>
          B.updateRow i (Function.update (B i) a (B i a - L i j * B j a))) B r' s = B r' s :=
        fun r' => by simp [hB, hsa]
      simp only [hB', List.mem_cons, hsa, false_or]

/-- The block saxpy `B_I = B_I - L_IJ X_J` of (3.1.4), in exact arithmetic: over a duplicate-free
list of rows disjoint from the block `o`, every listed row `r` receives `∑_{j ∈ o} L(r,j) B(j,c)`
subtracted in every column. -/
private theorem foldl_blockSaxpy {n q : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    {o R : List (Fin n)} (hR : R.Nodup) (hRo : ∀ r ∈ R, r ∉ o) (B : Matrix (Fin n) (Fin q) ℝ)
    (r : Fin n) (s : Fin q) :
    R.foldl (fun (B : Matrix (Fin n) (Fin q) ℝ) i => (List.finRange q).foldl
        (fun (B : Matrix (Fin n) (Fin q) ℝ) c => o.foldl (fun (B : Matrix (Fin n) (Fin q) ℝ) j =>
          B.updateRow i (Function.update (B i) c (B i c - L i j * B j c))) B) B) B r s =
      if r ∈ R then B r s - (o.map fun j => L r j * B j s).sum else B r s := by
  induction R generalizing B with
  | nil => simp
  | cons a R ih =>
    rcases List.nodup_cons.1 hR with ⟨ha, hR'⟩
    rw [List.foldl_cons, ih hR' fun r hr => hRo r (List.mem_cons_of_mem _ hr)]
    have hao : a ∉ o := hRo a List.mem_cons_self
    have hB := foldl_blockSaxpy_row L hao (List.nodup_finRange q) B
    by_cases hra : r = a
    · subst hra
      simp [ha, hB]
    · have hB' : ∀ r', r' ≠ a → (List.finRange q).foldl
          (fun (B : Matrix (Fin n) (Fin q) ℝ) c => o.foldl (fun (B : Matrix (Fin n) (Fin q) ℝ) j =>
            B.updateRow a (Function.update (B a) c (B a c - L a j * B j c))) B) B r' s = B r' s :=
        fun r' hr' => by simp [hB, hr']
      have hmap : (o.map fun j => L r j * ((List.finRange q).foldl
          (fun (B : Matrix (Fin n) (Fin q) ℝ) c => o.foldl (fun (B : Matrix (Fin n) (Fin q) ℝ) j =>
            B.updateRow a (Function.update (B a) c (B a c - L a j * B j c))) B) B) j s) =
          o.map fun j => L r j * B j s :=
        List.map_congr_left fun j hj => by rw [hB' j fun h => hao (h ▸ hj)]
      rw [hmap, hB' r hra]
      simp only [List.mem_cons, hra, false_or]

/-- A sum over a filtered `List.finRange` is a sum over the filtered `Finset.univ`, written with an
indicator. -/
private theorem sum_map_filter_finRange {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (f : Fin n → ℝ) :
    (((List.finRange n).filter fun k => decide (P k)).map f).sum =
      ∑ k, if P k then f k else 0 := by
  rw [Fin.sum_univ_def]
  induction (List.finRange n) with
  | nil => simp
  | cons a l ih => by_cases h : P a <;> simp [h, ih]

/-- **(3.1.4) computes the block solution**: for a monotone block labelling `blk` (contiguous
blocks) and lower triangular `L` with nonzero diagonal, the exact run of the block forward
elimination solves `L X = B`. Invariant after the blocks of a prefix `p`: the rows of those blocks
are finished (`∑_{blk j ∈ p} L(i,j) X(j,c) = B(i,c)`), every later row holds `B(i,c)` minus the
contributions of the finished rows. -/
theorem equation_3_1_4 {n N q : ℕ} {blk : Fin n → Fin N} (hblk : Monotone blk)
    {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular) (hd : ∀ i, L i i ≠ 0)
    (B : Matrix (Fin n) (Fin q) ℝ) : L * Id.run (blockForwardElim pure blk L B) = B := by
  set o : Fin N → List (Fin n) := fun J => (List.finRange n).filter (blk · = J) with ho
  set R : Fin N → List (Fin n) := fun J => (List.finRange n).filter (J < blk ·) with hR
  set Y : Fin N → (Fin n → ℝ) → Fin n → ℝ :=
    fun J v => Id.run (forwardSubstColOn pure (o J) L v) with hY
  set F : Matrix (Fin n) (Fin q) ℝ → Fin N → Matrix (Fin n) (Fin q) ℝ :=
    fun (S : Matrix (Fin n) (Fin q) ℝ) J => (R J).foldl
        (fun (S : Matrix (Fin n) (Fin q) ℝ) i => (List.finRange q).foldl
          (fun (S : Matrix (Fin n) (Fin q) ℝ) c => (o J).foldl
            (fun (S : Matrix (Fin n) (Fin q) ℝ) j =>
              S.updateRow i (Function.update (S i) c (S i c - L i j * S j c))) S) S)
        ((List.finRange q).foldl (fun (S : Matrix (Fin n) (Fin q) ℝ) c =>
          S.updateCol c (Y J fun i => S i c)) S) with hF
  have hprog : Id.run (blockForwardElim pure blk L B) = (List.finRange N).foldl F B := by
    simp only [blockForwardElim, List.idRun_foldlM, Id.run_bind, Id.run_pure, pure_bind, ho, hR,
      hY, hF]
  have hsorted : ∀ J, (o J).Pairwise (· < ·) := fun J =>
    ((List.sortedLT_finRange n).pairwise).filter _
  have hmemo : ∀ J j, j ∈ o J ↔ blk j = J := fun J j => by simp [ho]
  have hmemR : ∀ J j, j ∈ R J ↔ J < blk j := fun J j => by simp [hR]
  have hsplit : ∀ (p : List (Fin N)) (x : Fin N), x ∉ p → ∀ g : Fin n → ℝ,
      (∑ j, if blk j ∈ p ++ [x] then g j else 0) =
        (∑ j, if blk j ∈ p then g j else 0) + ∑ j, if blk j = x then g j else 0 := by
    intro p x hx g
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hp : blk j ∈ p
    · have hjx : blk j ≠ x := fun h => hx (h ▸ hp)
      simp [hp, hjx]
    · by_cases hjx : blk j = x <;> simp [hp, hjx, hx]
  rw [hprog]
  have key := List.foldl_prefix_induction (l := List.finRange N) (b := B) F
    (fun (p : List (Fin N)) (S : Matrix (Fin n) (Fin q) ℝ) => ∀ i c,
      (blk i ∈ p → (∑ j, if blk j ∈ p then L i j * S j c else 0) = B i c) ∧
      (blk i ∉ p → S i c = B i c - ∑ j, if blk j ∈ p then L i j * S j c else 0))
    (fun i c => ⟨fun h => absurd h List.not_mem_nil, fun _ => by simp⟩) ?_
  · ext i c
    have := (key i c).1 (List.mem_finRange _)
    simpa [List.mem_finRange, mul_apply] using this
  rintro p x qs hpq S hI
  simp only [hF]
  have hpx : ∀ J ∈ p, J < x := fun J hJ =>
    (List.pairwise_append.1 (hpq ▸ (List.sortedLT_finRange N).pairwise)).2.2 J hJ x
      List.mem_cons_self
  have hxq : ∀ J ∈ qs, x < J := fun J hJ =>
    List.rel_of_pairwise_cons
      (List.pairwise_append.1 (hpq ▸ (List.sortedLT_finRange N).pairwise)).2.1 hJ
  have hxp : x ∉ p := fun h => lt_irrefl x (hpx x h)
  have hlater : ∀ J, J ∉ p → J ≠ x → x < J := fun J hJp hJx => by
    have hJ : J ∈ p ++ x :: qs := hpq ▸ List.mem_finRange J
    rcases List.mem_append.1 hJ with h | h
    · exact absurd h hJp
    · rcases List.mem_cons.1 h with h | h
      · exact absurd h hJx
      · exact hxq J h
  set S₁ := (List.finRange q).foldl (fun (S : Matrix (Fin n) (Fin q) ℝ) c =>
    S.updateCol c (Y x fun i => S i c)) S with hS₁def
  have hS₁ : ∀ i c, S₁ i c = Y x (fun i => S i c) i := fun i c => by
    rw [hS₁def, Matrix.foldl_updateCol_apply (fun _ => Y x) (List.nodup_finRange q),
      ite_eq_left (List.mem_finRange c)]
  have hS₂ : ∀ i c, (R x).foldl
        (fun (S : Matrix (Fin n) (Fin q) ℝ) i => (List.finRange q).foldl
          (fun (S : Matrix (Fin n) (Fin q) ℝ) c => (o x).foldl
            (fun (S : Matrix (Fin n) (Fin q) ℝ) j =>
              S.updateRow i (Function.update (S i) c (S i c - L i j * S j c))) S) S) S₁ i c =
      if x < blk i then S₁ i c - ((o x).map fun j => L i j * S₁ j c).sum else S₁ i c :=
    fun i c => by
      rw [foldl_blockSaxpy L ((List.nodup_finRange n).filter _) (fun r hr hro =>
        lt_irrefl x (((hmemo x r).1 hro) ▸ (hmemR x r).1 hr)), if_congr (hmemR x i) rfl rfl]
  have hA : ∀ c, (∀ i, i ∉ o x → Y x (fun i => S i c) i = S i c) ∧
      ∀ i ∈ o x, ((o x).map fun j => L i j * Y x (fun i => S i c) j).sum = S i c :=
    fun c => forwardSubstColOn_exact (hsorted x) hL (fun i _ => hd i) _
  have hmapY : ∀ i c, ((o x).map fun j => L i j * S₁ j c).sum =
      ∑ j, if blk j = x then L i j * Y x (fun i => S i c) j else 0 := fun i c => by
    rw [ho, List.map_congr_left fun j _ => by rw [hS₁ j c]]
    exact sum_map_filter_finRange (fun j => blk j = x) _
  -- values of the new state on the finished rows and on the new block
  have hold : ∀ j c, blk j ∈ p → (if x < blk j then S₁ j c -
      ((o x).map fun k => L j k * S₁ k c).sum else S₁ j c) = S j c := fun j c hj => by
    rw [ite_eq_right (lt_asymm (hpx _ hj)), hS₁, (hA c).1 j fun h => hxp ((hmemo x j).1 h ▸ hj)]
  have hnew : ∀ j c, blk j = x → (if x < blk j then S₁ j c -
      ((o x).map fun k => L j k * S₁ k c).sum else S₁ j c) = Y x (fun i => S i c) j :=
    fun j c hj => by rw [ite_eq_right (hj ▸ lt_irrefl x), hS₁]
  have hsum_old : ∀ i c, (∑ j, if blk j ∈ p then L i j * (if x < blk j then S₁ j c -
      ((o x).map fun k => L j k * S₁ k c).sum else S₁ j c) else 0) =
      ∑ j, if blk j ∈ p then L i j * S j c else 0 := fun i c =>
    Finset.sum_congr rfl fun j _ => by
      by_cases hj : blk j ∈ p
      · rw [ite_eq_left hj, ite_eq_left hj, hold j c hj]
      · rw [ite_eq_right hj, ite_eq_right hj]
  have hsum_new : ∀ i c, (∑ j, if blk j = x then L i j * (if x < blk j then S₁ j c -
      ((o x).map fun k => L j k * S₁ k c).sum else S₁ j c) else 0) =
      ∑ j, if blk j = x then L i j * Y x (fun i => S i c) j else 0 := fun i c =>
    Finset.sum_congr rfl fun j _ => by
      by_cases hj : blk j = x
      · rw [ite_eq_left hj, ite_eq_left hj, hnew j c hj]
      · rw [ite_eq_right hj, ite_eq_right hj]
  intro i c
  simp only [hS₂]
  rw [hsplit p x hxp, hsum_old, hsum_new]
  refine ⟨fun hi => ?_, fun hi => ?_⟩
  · rcases List.mem_append.1 hi with hi | hi
    · have hzero : (∑ j, if blk j = x then L i j * Y x (fun i => S i c) j else 0) = 0 :=
        Finset.sum_eq_zero fun j _ => by
          split_ifs with hj
          · have hij : i < j := lt_of_not_ge fun h => by
              have h' := hblk h
              rw [hj] at h'
              exact absurd h' (not_le.2 (hpx _ hi))
            rw [hL (OrderDual.toDual_lt_toDual.2 hij), zero_mul]
          · rfl
      rw [hzero, add_zero]
      exact (hI i c).1 hi
    · have hix : blk i = x := List.mem_singleton.1 hi
      have hsumY : (∑ j, if blk j = x then L i j * Y x (fun i => S i c) j else 0) =
          ((o x).map fun j => L i j * Y x (fun i => S i c) j).sum :=
        (sum_map_filter_finRange (fun j => blk j = x) _).symm
      rw [hsumY, (hA c).2 i ((hmemo x i).2 hix), (hI i c).2 (hix ▸ hxp)]
      ring
  · have hip : blk i ∉ p := fun h => hi (List.mem_append_left _ h)
    have hix : blk i ≠ x := fun h => hi (List.mem_append_right _ (h ▸ List.mem_singleton_self _))
    rw [ite_eq_left (hlater _ hip hix), hmapY, hS₁, (hA c).1 i fun h => hix ((hmemo x i).1 h),
      (hI i c).2 hip]
    ring

end BlockExact

/-! ### Nonsquare triangular systems (§3.1.6) -/

section Nonsquare

/-- §3.1.6, `m ≥ n`: for `L₁₁` lower triangular and nonsingular, the system
`[L₁₁; L₂₁] x = [b₁; b₂]` has a solution iff `L₂₁ (L₁₁⁻¹ b₁) = b₂` ("otherwise, there is no
solution to the overall system"), and then `x = L₁₁⁻¹ b₁` is the only one. -/
theorem nonsquareLower_tall {n p : ℕ} {L₁₁ : Matrix (Fin n) (Fin n) ℝ}
    (hL : L₁₁.IsLowerTriangular) (hd : ∀ i, L₁₁ i i ≠ 0) (L₂₁ : Matrix (Fin p) (Fin n) ℝ)
    (b₁ : Fin n → ℝ) (b₂ : Fin p → ℝ) :
    ((∃ x, fromRows L₁₁ L₂₁ *ᵥ x = Sum.elim b₁ b₂) ↔ L₂₁ *ᵥ (L₁₁⁻¹ *ᵥ b₁) = b₂) ∧
      ∀ x, fromRows L₁₁ L₂₁ *ᵥ x = Sum.elim b₁ b₂ → x = L₁₁⁻¹ *ᵥ b₁ := by
  have hU : IsUnit L₁₁ := hL.isUnit_iff.2 hd
  have : Invertible L₁₁ := hU.invertible
  have key : ∀ x, fromRows L₁₁ L₂₁ *ᵥ x = Sum.elim b₁ b₂ ↔
      L₁₁ *ᵥ x = b₁ ∧ L₂₁ *ᵥ x = b₂ := by
    intro x
    rw [fromRows_mulVec]
    constructor
    · intro h
      exact ⟨funext fun i => congrFun h (Sum.inl i), funext fun i => congrFun h (Sum.inr i)⟩
    · rintro ⟨h₁, h₂⟩
      rw [h₁, h₂]
  have hsol : ∀ x, L₁₁ *ᵥ x = b₁ ↔ x = L₁₁⁻¹ *ᵥ b₁ := fun x =>
    ⟨fun h => (inv_mulVec_eq_vec h.symm).symm, fun h => by
      rw [h, mulVec_mulVec, mul_inv_of_invertible, one_mulVec]⟩
  refine ⟨⟨fun ⟨x, hx⟩ => ?_, fun h => ⟨L₁₁⁻¹ *ᵥ b₁, (key _).2 ⟨(hsol _).2 rfl, h⟩⟩⟩,
    fun x hx => (hsol x).1 ((key x).1 hx).1⟩
  obtain ⟨h₁, h₂⟩ := (key x).1 hx
  rwa [← (hsol x).1 h₁]

/-- §3.1.6, `n > m`: for a lower trapezoidal `L ∈ ℝ^{m×(m+p)}` (`l_ij = 0` for `i < j`) whose
leading block `L(1:m,1:m)` has nonzero diagonal, `L x = b` holds exactly when
`x(1:m) = L(1:m,1:m)⁻¹ b`: forward substitution on the square system, with "an arbitrary value
for `x(m+1:n)`". -/
theorem nonsquareLower_wide {m p : ℕ} {L : Matrix (Fin m) (Fin (m + p)) ℝ}
    (hL : ∀ (i : Fin m) (j : Fin (m + p)), (i : ℕ) < j → L i j = 0)
    (hd : ∀ i : Fin m, L i (Fin.castAdd p i) ≠ 0) (b : Fin m → ℝ) (x : Fin (m + p) → ℝ) :
    L *ᵥ x = b ↔ (fun i => x (Fin.castAdd p i)) = (L.submatrix id (Fin.castAdd p))⁻¹ *ᵥ b := by
  set L₁ := L.submatrix id (Fin.castAdd p)
  have hL₁ : L₁.IsLowerTriangular := fun i j hij => hL i _ (by simpa using hij)
  have hU : IsUnit L₁ := hL₁.isUnit_iff.2 hd
  have : Invertible L₁ := hU.invertible
  have hsplit : L *ᵥ x = L₁ *ᵥ fun i => x (Fin.castAdd p i) := by
    funext i
    have h₂ : ∑ j : Fin p, L i (Fin.natAdd m j) * x (Fin.natAdd m j) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [hL i _ (by simp only [Fin.val_natAdd]; omega), zero_mul]
    simp only [mulVec, dotProduct, Fin.sum_univ_add, L₁, submatrix_apply, id]
    rw [h₂, add_zero]
  rw [hsplit]
  exact ⟨fun h => (inv_mulVec_eq_vec h.symm).symm, fun h => by
    rw [h, mulVec_mulVec, mul_inv_of_invertible, one_mulVec]⟩

end Nonsquare

/-! ### The algebra of triangular matrices (§3.1.7) -/

section Algebra

variable {n : ℕ}

/-- §3.1.7: "the inverse of an upper (lower) triangular matrix is upper (lower) triangular". -/
theorem triangular_inv :
    (∀ U : Matrix (Fin n) (Fin n) ℝ, U.IsUpperTriangular → U⁻¹.IsUpperTriangular) ∧
      ∀ L : Matrix (Fin n) (Fin n) ℝ, L.IsLowerTriangular → L⁻¹.IsLowerTriangular :=
  ⟨fun _ hU => hU.inv, fun _ hL => hL.inv⟩

/-- §3.1.7: "the product of two upper (lower) triangular matrices is upper (lower) triangular". -/
theorem triangular_mul :
    (∀ U₁ U₂ : Matrix (Fin n) (Fin n) ℝ, U₁.IsUpperTriangular → U₂.IsUpperTriangular →
      (U₁ * U₂).IsUpperTriangular) ∧
    ∀ L₁ L₂ : Matrix (Fin n) (Fin n) ℝ, L₁.IsLowerTriangular → L₂.IsLowerTriangular →
      (L₁ * L₂).IsLowerTriangular :=
  ⟨fun _ _ h₁ h₂ => h₁.mul h₂, fun _ _ h₁ h₂ => h₁.mul h₂⟩

/-- §3.1.7: "the inverse of a unit upper (lower) triangular matrix is unit upper (lower)
triangular". -/
theorem unitTriangular_inv :
    (∀ U : Matrix (Fin n) (Fin n) ℝ, U.IsUnitUpperTriangular → U⁻¹.IsUnitUpperTriangular) ∧
      ∀ L : Matrix (Fin n) (Fin n) ℝ, L.IsUnitLowerTriangular → L⁻¹.IsUnitLowerTriangular :=
  ⟨fun _ hU => hU.inv, fun _ hL => hL.inv⟩

/-- §3.1.7: "the product of two unit upper (lower) triangular matrices is unit upper (lower)
triangular". -/
theorem unitTriangular_mul :
    (∀ U₁ U₂ : Matrix (Fin n) (Fin n) ℝ, U₁.IsUnitUpperTriangular → U₂.IsUnitUpperTriangular →
      (U₁ * U₂).IsUnitUpperTriangular) ∧
    ∀ L₁ L₂ : Matrix (Fin n) (Fin n) ℝ, L₁.IsUnitLowerTriangular → L₂.IsUnitLowerTriangular →
      (L₁ * L₂).IsUnitLowerTriangular :=
  ⟨fun _ _ h₁ h₂ => h₁.mul h₂, fun _ _ h₁ h₂ => h₁.mul h₂⟩

end Algebra

end GolubVanLoan.Chapter03
