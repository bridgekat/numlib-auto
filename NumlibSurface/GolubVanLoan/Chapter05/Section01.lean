import Mathlib.Basic.Real.Sign
import Numlib.FloatingPoint.Givens
import Numlib.FloatingPoint.Program
import Numlib.LinearAlgebra.Matrix.WY
import NumlibSurface.GolubVanLoan.Chapter01.Section01

/-!
# Golub–Van Loan §5.1: Householder and Givens transformations

Surface file for [golub2013matrix] §5.1.

## Conventions

Vectors are `Fin m → ℝ`, 0-based: `x 0` is the book's `x(1)`, `e₁` is `Pi.single 0 1`. The matrix
`P = I - β v vᵀ` is `1 - β • vecMulVec v v`; the book's Householder matrix `I - 2vvᵀ/vᵀv` is
`householderMatrix v`, the backbone's `Matrix.reflector v`. The Givens rotation `G(i, k, θ)` of
(5.1.7) is `givensRotation i k c s = Matrix.planeRotation i k c (-s)`: the backbone's plane
rotation has the Jacobi sign convention, and the rounding relations of
`Numlib/FloatingPoint/Givens` are stated in the book's.

**The shared helper family** (conventions 10, 13 and 14 of `NumlibSurface/GolubVanLoan`, which
every later chapter calls): `houseOn` (Algorithm 5.1.1 on the entries listed by an index list;
`algorithm_5_1_1` is its instance at the full list), `householderApplyLeft` /
`householderApplyRight` (§5.1.4, in place on the full matrix over row and column index lists),
`givensRotation`, `givensApplyLeft` / `givensApplyRight` (§5.1.9), and for reflector data
`List ((Fin m → ℝ) × ℝ)` — pairs `(v, β)` in order of application, `v` full length and zero off
its active rows, `β` the value `house` returned — `householderProduct`, `forwardAccumulation`,
`backwardAccumulation`. A block `A(j:m, k:n)` is never copied into a `Fin (m - j)`-typed array.

Every program is written once, generic in a monad `M` and a rounding hook `rnd : ℝ → M ℝ`
(`Numlib/FloatingPoint/Program`). Each carries `_rounds` (every run in the relational model
`M := SetM`, `rnd := fp.round` satisfies the backbone relation), `_spec` (the exact semantics at
`M := Id`, `rnd := pure`, read off the bridge at the exact model `RoundingModel.exact ℝ`) and,
where the book analyses it, `_rounding` (the book's error bound, with explicit `γ` constants in
place of the book's `O(u)`).

## Errata carried

Algorithm 5.1.1's `σ = 0 & x(1) < 0` branch sets `β = 2` (the book prints `β = -2`, which makes
`P` not orthogonal). The retrieval `β_j = 2/(1 + ‖A(j+1:m, j)‖²)` of (5.1.4)–(5.1.5) is wrong when
`house` returned `β = 0`; those displays are specified against the recomputed `β`
(`recomputedBeta`), every other consumer uses the returned `β`.

## Main results

* `householderMatrix` (5.1.1), `equation_5_1_2`, `parlett_formula`; `houseOn`, `algorithm_5_1_1`
  (`house`) with `houseOn_rounds` (the bridge to `FloatingPoint.RoundsHouseholderVectorParlett`),
  `houseOn_spec`, `algorithm_5_1_1_spec`, `houseOn_rounding`, `algorithm_5_1_1_rounding` (§5.1.5)
  and `householderMatrix_computed_sub_le` (`‖P̂ - P‖₂ ≤ 8 γ_K`).
* `householderApplyLeft`, `householderApplyRight` (§5.1.4), their bridges to
  `FloatingPoint.RoundsHouseholderApplyScaled`, exact specifications and rounding bounds (§5.1.5).
* The factored form (5.1.3): `householderProduct`, `storedHouseholderVec`, `storedReflectors`,
  `factoredQ`, `recomputedBeta`; (5.1.4) and (5.1.5) as programs (`factoredQTransposeMul`,
  `factoredQFirstColumns`) with `equation_5_1_4`, `equation_5_1_5`; `forwardAccumulation`,
  `backwardAccumulation` and their specifications.
* The WY representation: `equation_5_1_6`, `lemma_5_1_1`, `algorithm_5_1_2` with its
  specification, `blockReflector_mem_orthogonalGroup`.
* Givens rotations: `givensRotation` (5.1.7), `equation_5_1_8`, `algorithm_5_1_3` (`givens`) with
  its bridge to `FloatingPoint.RoundsGivensPair`, specification and rounding (§5.1.10);
  `givensApplyLeft`, `givensApplyRight` (§5.1.9) with bridges to
  `FloatingPoint.RoundsGivensRowUpdate`/`ColUpdate`, specifications and rounding bounds.
* Stewart's encoding (5.1.9)–(5.1.10), `rotationDecode_rotationCode`.
* §5.1.12: `orthogonalToWorkingPrecision` and its corollary, the Givens and Householder cases;
  `equation_5_1_11` (the two-sided accumulation of computed updates).
* §5.1.13: `complexHouseholder`, `complexGivens_mem_unitaryGroup`, `equation_5_1_12`.

The run-set lemmas `mem_run_foldlM_updateCol_of_nodup` and `mem_run_foldlM_updateRow_of_nodup`
(one column, or one row, rewritten per step) are the loop rules of the helpers.

## Not formalized

The 2-by-2 preview of §5.1.1 (prose), flop counts, the level-2/level-3 discussion of §5.1.7, the
Problems. The rounding bound of Algorithm 5.1.2 is not claimed by the book.
-/

open FloatingPoint Matrix WithLp

namespace GolubVanLoan.Chapter05

/-! ### Generic facts about index lists and the exact model -/

section Generic

/-- In the exact model a relative perturbation is an equality. -/
theorem eq_of_isRelPert_zero {n : ℕ} {x y : ℝ} (h : IsRelPert 0 n x y) : y = x := by
  obtain ⟨θ, hθ, rfl⟩ := h
  have hθ0 : θ = 0 := abs_nonpos_iff.1 (by simpa [gamma] using hθ)
  simp [hθ0]

/-- The inner-product accumulation along a mapped list is the accumulation of the composed
vectors. -/
theorem dotAccum_map {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {ι κ : Type} (f : κ → ι)
    (o : List κ) (x y : ι → ℝ) (c : ℝ) :
    dotAccum rnd (o.map f) x y c = dotAccum rnd o (x ∘ f) (y ∘ f) c := by
  simp only [dotAccum, List.foldlM_map, Function.comp_apply]

/-- **An accumulation from `0` along a duplicate-free index list is an inner product over the
listed indices**: over an idempotent model, a run of `dotAccum` along `l` is a `RoundsDot` of the
restrictions of `x` and `y` to the subtype `{i // i ∈ l}`. -/
theorem roundsDot_subtype_of_mem_run_dotAccum {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent)
    {ι : Type} {l : List ι} (hl : l.Nodup) {x y : ι → ℝ} {s : ℝ}
    (h : s ∈ (dotAccum fp.round l x y 0).run) :
    RoundsDot fp (fun i : {i // i ∈ l} => x i) (fun i => y i) s := by
  have e : dotAccum fp.round l x y 0 =
      dotAccum fp.round l.attach (x ∘ Subtype.val) (y ∘ Subtype.val) 0 := by
    conv_lhs => rw [← List.attach_map_subtype_val l]
    exact dotAccum_map _ _ _ _ _ _
  rw [e] at h
  exact roundsDot_of_mem_run_dotAccum hfp (List.nodup_attach.2 hl) (List.mem_attach l) h

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A dot product with a vector vanishing off `l` is the dot product of the restrictions to
`{i // i ∈ l}`. -/
theorem dotProduct_eq_dotProduct_subtype (l : List ι) {v : ι → ℝ} (hv : ∀ i, i ∉ l → v i = 0)
    (x : ι → ℝ) : v ⬝ᵥ x = (fun i : {i // i ∈ l} => v i) ⬝ᵥ (fun i => x i) := by
  have h0 : ∑ i : {i // i ∉ l}, v i * x i = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hv i i.2, zero_mul]
  simp only [dotProduct]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ l) (fun i => v i * x i), h0, add_zero]
  convert rfl

/-- **A rank-one modification supported on `l` acts on the coordinates of `l` only**: for `v`
vanishing off `l`, `(1 - β v vᵀ) x` is `x` off `l` and, on `l`, the action of the restricted
`1 - β v vᵀ` on the restricted `x`. -/
theorem one_sub_smul_vecMulVec_mulVec_apply_subtype (l : List ι) {v : ι → ℝ}
    (hv : ∀ i, i ∉ l → v i = 0) (β : ℝ) (x : ι → ℝ) (i : ι) :
    ((1 - β • vecMulVec v v) *ᵥ x) i =
      if h : i ∈ l then
        ((1 - β • vecMulVec (fun j : {j // j ∈ l} => v j) (fun j : {j // j ∈ l} => v j) :
          Matrix {j // j ∈ l} {j // j ∈ l} ℝ) *ᵥ (fun j : {j // j ∈ l} => x j)) ⟨i, h⟩
      else x i := by
  rw [one_sub_smul_vecMulVec_mulVec_apply]
  split_ifs with h
  · rw [one_sub_smul_vecMulVec_mulVec_apply, dotProduct_eq_dotProduct_subtype l hv]
  · rw [hv i h, mul_zero, zero_mul, sub_zero]

/-- **Orthogonality forces the `β` dichotomy**: if `1 - β v vᵀ` is orthogonal and some entry of `v`
is nonzero, then `β (β vᵀv - 2) = 0`, i.e. `β = 0` or `β vᵀv = 2`. -/
theorem beta_mul_eq_zero_of_mem_orthogonalGroup {v : ι → ℝ} {β : ℝ} {p : ι} (hp : v p ≠ 0)
    (h : (1 - β • vecMulVec v v) ∈ orthogonalGroup ι ℝ) : β * (β * (v ⬝ᵥ v) - 2) = 0 := by
  have h1 := (mem_orthogonalGroup_iff' ι ℝ).1 h
  rw [transpose_one_sub_smul_vecMulVec, one_sub_smul_vecMulVec_mul_self] at h1
  have h2 := congrFun (congrFun h1 p) p
  rw [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, one_apply_eq, smul_eq_mul,
    add_eq_left] at h2
  rcases mul_eq_zero.1 h2 with h | h
  · exact h
  · exact absurd (mul_self_eq_zero.1 h) hp

end Generic

/-! ### Loops writing one column, or one row, per step -/

section Loops

variable {m n : ℕ}

/-- **A loop rewriting one column per step**, over a duplicate-free column list: step `q`
replaces column `q` by a result of `g q` applied to its current value. Its runs are the matrices
that agree with `A` off the listed columns and whose column `q` is, for each listed `q`, a result
of `g q` on column `q` of `A`. The column form of `SetM.mem_run_foldlM_update_of_nodup`. -/
theorem mem_run_foldlM_updateCol_of_nodup (g : Fin n → (Fin m → ℝ) → SetM (Fin m → ℝ))
    {cols : List (Fin n)} (hcols : cols.Nodup) (A B : Matrix (Fin m) (Fin n) ℝ) :
    B ∈ (cols.foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) q => do
        let c ← g q (fun i => A i q); pure (A.updateCol q c)) A).run ↔
      (∀ q, q ∉ cols → ∀ i, B i q = A i q) ∧
        ∀ q ∈ cols, (fun i => B i q) ∈ (g q (fun i => A i q)).run := by
  -- the loop is the transpose of the loop on the columns of `Aᵀ`, updated by `Function.update`
  have key : ∀ (l : List (Fin n)) (D₀ : Matrix (Fin m) (Fin n) ℝ),
      l.foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) q => do
          let c ← g q (fun i => A i q); pure (A.updateCol q c)) D₀
        = (fun D : Fin n → Fin m → ℝ => (Matrix.of D)ᵀ) <$>
          l.foldlM (fun (D : Fin n → Fin m → ℝ) q => do
            let c ← g q (D q); pure (Function.update D q c)) (fun q i => D₀ i q) := by
    intro l
    induction l with
    | nil => intro D₀; simp only [List.foldlM_nil, map_pure]; rfl
    | cons a l ih =>
      intro D₀
      simp only [List.foldlM_cons, bind_assoc, pure_bind, map_bind]
      refine congrArg _ (funext fun c => ?_)
      rw [ih]
      congr 2
      funext q i
      simp only [updateCol_apply, Function.update_apply]
      split_ifs <;> rfl
  rw [key, SetM.mem_run_map]
  have h := SetM.mem_run_foldlM_update_of_nodup (fun q b (_ : Fin n → Fin m → ℝ) => g q b) cols
    hcols (fun _ _ _ _ _ _ => rfl) (fun q i => A i q)
  constructor
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨hout, hin⟩ := (h D).1 hD
    exact ⟨fun q hq i => congrFun (hout q hq) i, fun q hq => hin q hq⟩
  · rintro ⟨hout, hin⟩
    refine ⟨fun q i => B i q, (h _).2 ⟨fun q hq => funext fun i => hout q hq i, hin⟩, ?_⟩
    rfl

/-- **A loop rewriting one row per step**, over a duplicate-free row list: the row form of
`mem_run_foldlM_updateCol_of_nodup`, directly `SetM.mem_run_foldlM_update_of_nodup` on the rows. -/
theorem mem_run_foldlM_updateRow_of_nodup (g : Fin m → (Fin n → ℝ) → SetM (Fin n → ℝ))
    {rows : List (Fin m)} (hrows : rows.Nodup) (A B : Matrix (Fin m) (Fin n) ℝ) :
    B ∈ (rows.foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) r => do
        let x ← g r (A r); pure (A.updateRow r x)) A).run ↔
      (∀ r, r ∉ rows → B r = A r) ∧ ∀ r ∈ rows, B r ∈ (g r (A r)).run :=
  SetM.mem_run_foldlM_update_of_nodup (fun r b (_ : Fin m → Fin n → ℝ) => g r b) rows hrows
    (fun _ _ _ _ _ _ => rfl) A B

end Loops

/-! ### §5.1.2 Householder reflections -/

section Reflections

variable {m : ℕ}

/-- **§5.1.2, (5.1.1): the Householder reflection** `P = I - β v vᵀ`, `β = 2 / vᵀv`, with
Householder vector `v`: "if a vector `x` is multiplied by `P`, then it is reflected in the
hyperplane `span{v}⊥`". (For `v = 0` it is the identity, the value of `2 / 0 = 0`.) -/
noncomputable def householderMatrix (v : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  1 - (2 / (v ⬝ᵥ v)) • vecMulVec v v

/-- The Householder matrix is the backbone's reflector `Matrix.reflector v`. -/
theorem householderMatrix_eq_reflector (v : Fin m → ℝ) : householderMatrix v = reflector v :=
  (reflector_eq_one_sub_smul_vecMulVec v).symm

/-- **§5.1.2**: "Householder matrices are symmetric …". -/
theorem householderMatrix_isSymm (v : Fin m → ℝ) : (householderMatrix v).IsSymm :=
  transpose_one_sub_smul_vecMulVec _ _

/-- **§5.1.2**: "… and orthogonal". -/
theorem householderMatrix_mem_orthogonalGroup (v : Fin m → ℝ) :
    householderMatrix v ∈ orthogonalGroup (Fin m) ℝ := by
  rw [householderMatrix_eq_reflector]
  exact reflector_mem_orthogonalGroup v

/-- **(5.1.2)**: for `α = ±‖x‖₂` and `v = x + α e₁ ≠ 0`,
`P x = (I - 2 v vᵀ / vᵀv) x = -α e₁`, i.e. "`v = x ± ‖x‖₂ e₁ ⇒ P x = ∓ ‖x‖₂ e₁`". -/
theorem equation_5_1_2 {k : ℕ} (x : Fin (k + 1) → ℝ) {α : ℝ}
    (hα : α = ‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖ ∨
      α = -‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖)
    (hv : x + α • Pi.single 0 1 ≠ 0) :
    householderMatrix (x + α • Pi.single 0 1) *ᵥ x = -α • Pi.single 0 1 := by
  rw [householderMatrix_eq_reflector]
  refine reflector_mulVec_eq_of_sq ?_ (by simp) hv
  simp only [star_trivial, RCLike.ofReal_real_eq_id, id]
  rcases hα with rfl | rfl <;> ring

/-- **§5.1.3, Parlett's formula**: if `x₁ + ‖x‖₂ ≠ 0`, then
`x₁ - ‖x‖₂ = -(x₂² + ⋯ + x_m²) / (x₁ + ‖x‖₂)`, the cancellation-free form of `v₁ = x₁ - ‖x‖₂`
when `x₁ > 0`. -/
theorem parlett_formula {k : ℕ} (x : Fin (k + 1) → ℝ)
    (h : x 0 + ‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖ ≠ 0) :
    x 0 - ‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖ =
      -(∑ i : Fin k, x i.succ ^ 2) / (x 0 + ‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖) := by
  have hN : ‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖ ^ 2 =
      x 0 ^ 2 + ∑ i : Fin k, x i.succ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
    simp
  rw [eq_div_iff h]
  linear_combination -hN

end Reflections

/-! ### §5.1.3 Computing the Householder vector: `house` -/

section House

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {m : ℕ}

/-- The pivot entry `v(1)` of `house`: `x(1) - μ` if `x(1) ≤ 0`, else Parlett's cancellation-free
`-σ / (x(1) + μ)` (§5.1.3), each operation rounded. -/
noncomputable def parlettPivot (x₁ μ σ : ℝ) : M ℝ :=
  if x₁ ≤ 0 then rnd (x₁ - μ) else do rnd (-σ / (← rnd (x₁ + μ)))

/-- **Algorithm 5.1.1 (`house`) on the entries of `x` listed by `o`** — convention 10's form of the
book's `house(A(j:m, j))`. The pivot `p = o.head` is the book's `x(1)`, the tail `t = o.tail` its
`x(2:m)`:
```
σ = x(2:m)ᵀ x(2:m),  v = [1; x(2:m)]
if σ = 0 and x(1) >= 0:      β = 0
elseif σ = 0 & x(1) < 0:     β = 2          (the book prints -2)
else
    μ = √(x(1)² + σ)
    if x(1) <= 0:  v(1) = x(1) - μ
    else           v(1) = -σ/(x(1) + μ)
    β = 2 v(1)² / (σ + v(1)²)
    v = v / v(1)
```
`σ` is Algorithm 1.1.1 over the tail (`FloatingPoint.dotAccum`); `v(1)²` is computed once; `v` is
`1` at the pivot, `x i / v(1)` on the tail and `0` off `o`. For `o = []` the result is `(0, 0)`.
-/
noncomputable def houseOn (o : List (Fin m)) (x : Fin m → ℝ) : M ((Fin m → ℝ) × ℝ) :=
  match o with
  | [] => pure (0, 0)
  | p :: t => do
    let σ ← dotAccum rnd t x x 0
    let v : Fin m → ℝ := fun i => if i = p then 1 else if i ∈ t then x i else 0
    if σ = 0 ∧ 0 ≤ x p then pure (v, 0)
    else if σ = 0 ∧ x p < 0 then pure (v, 2)
    else do
      let μ ← rnd √(← rnd ((← rnd (x p * x p)) + σ))
      let v₁ ← parlettPivot rnd (x p) μ σ
      let q ← rnd (v₁ * v₁)
      let β ← rnd ((← rnd (2 * q)) / (← rnd (σ + q)))
      let w ← t.foldlM (fun (w : Fin m → ℝ) i => do
        let b ← rnd (x i / v₁)
        pure (Function.update w i b)) v
      pure (w, β)

/-- **Algorithm 5.1.1 (`house`)**: "Given `x ∈ ℝ^m`, this function computes `v ∈ ℝ^m` with
`v(1) = 1` and `β ∈ ℝ` such that `P = I_m - β v vᵀ` is orthogonal and `P x = ‖x‖₂ e₁`" — `houseOn`
at the full index list (convention 10). -/
noncomputable def algorithm_5_1_1 {k : ℕ} (x : Fin (k + 1) → ℝ) :
    M ((Fin (k + 1) → ℝ) × ℝ) :=
  houseOn rnd (List.finRange (k + 1)) x

end House

/-! ### `house`: the bridge, the exact semantics and the rounding bound -/

section HouseRuns

variable {m : ℕ}

/-- The number of listed indices of a duplicate-free list. -/
theorem card_subtype_mem_of_nodup {ι : Type} [DecidableEq ι] {l : List ι} (hl : l.Nodup) :
    Fintype.card {i // i ∈ l} = l.length := by
  rw [Fintype.card_of_subtype l.toFinset (fun x => List.mem_toFinset),
    List.toFinset_card_of_nodup hl]

/-- The tail of `p :: t` inside the subtype of `p :: t`, as the subtype of `t` (for `p ∉ t`). -/
private def consTailEquiv {p : Fin m} {t : List (Fin m)} (hp : p ∉ t) :
    {j : {i // i ∈ p :: t} // j ≠ ⟨p, List.mem_cons_self⟩} ≃ {i // i ∈ t} where
  toFun j := ⟨j.1.1, (List.mem_cons.1 j.1.2).resolve_left fun h => j.2 (Subtype.ext h)⟩
  invFun i := ⟨⟨i.1, List.mem_cons_of_mem _ i.2⟩, fun h => hp (by
    have h' : i.1 = p := congrArg Subtype.val h
    exact h' ▸ i.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The bridge of `house`** (convention 12): over an idempotent model, for a duplicate-free
nonempty index list `o`, every run `(v̂, β̂)` of `houseOn fp.round o x` vanishes off `o`, and on
the subtype `{i // i ∈ o}` it is a computed Householder vector of Parlett's formula
(`FloatingPoint.RoundsHouseholderVectorParlett`) with pivot `o.head`. The tail sum is a `RoundsDot`
because the accumulation starts from `0` (convention 6). -/
theorem houseOn_rounds {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent) {o : List (Fin m)}
    (ho : o.Nodup) (hne : o ≠ []) (x : Fin m → ℝ) {vβ : (Fin m → ℝ) × ℝ}
    (h : vβ ∈ (houseOn fp.round o x).run) :
    (∀ i, i ∉ o → vβ.1 i = 0) ∧
      RoundsHouseholderVectorParlett fp (fun i : {i // i ∈ o} => x i)
        ⟨o.head hne, List.head_mem hne⟩ (fun i => vβ.1 i) vβ.2 := by
  obtain ⟨p, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hp : p ∉ t := (List.nodup_cons.1 ho).1
  have ht : t.Nodup := (List.nodup_cons.1 ho).2
  simp only [houseOn, SetM.mem_run_bind] at h
  obtain ⟨σ, hσ, h⟩ := h
  have hdot : RoundsDot fp
      (fun j : {j : {i // i ∈ p :: t} // j ≠ ⟨p, List.mem_cons_self⟩} => x j.1.1)
      (fun j => x j.1.1) σ :=
    (roundsDot_comp_equiv_iff (consTailEquiv hp)).2
      (roundsDot_subtype_of_mem_run_dotAccum hfp ht hσ)
  set v : Fin m → ℝ := fun i => if i = p then 1 else if i ∈ t then x i else 0 with hv
  have hvp : v p = 1 := by simp [hv]
  have hvt : ∀ i ∈ t, v i = x i := fun i hi => by
    have hip : i ≠ p := fun e => hp (e ▸ hi)
    simp [hv, hi, hip]
  have hvout : ∀ i, i ∉ p :: t → v i = 0 := fun i hi => by
    simp only [List.mem_cons, not_or] at hi
    simp [hv, hi.1, hi.2]
  -- the entries of the subtype other than the pivot are the tail
  have htail : ∀ j : {i // i ∈ p :: t}, j ≠ ⟨p, List.mem_cons_self⟩ → j.1 ∈ t := fun j hj =>
    (List.mem_cons.1 j.2).resolve_left fun e => hj (Subtype.ext e)
  split_ifs at h with h1 h2
  · rw [SetM.mem_run_pure] at h
    subst h
    exact ⟨hvout, σ, hdot, hvp, Or.inl ⟨h1.1, h1.2, rfl, fun j hj => hvt j (htail j hj)⟩⟩
  · rw [SetM.mem_run_pure] at h
    subst h
    exact ⟨hvout, σ, hdot, hvp, Or.inr (Or.inl ⟨h2.1, h2.2, rfl,
      fun j hj => hvt j (htail j hj)⟩)⟩
  · have hσ0 : σ ≠ 0 := fun e => by
      rcases le_or_gt 0 (x p) with hx | hx
      · exact h1 ⟨e, hx⟩
      · exact h2 ⟨e, hx⟩
    simp only [SetM.mem_run_bind, RoundingModel.mem_run_round, SetM.mem_run_pure] at h
    obtain ⟨a, ha, b, hb, μ, hμ, v₁, hv₁, q, hq, c, hc, d, hd, β, hβ, w, hw, rfl⟩ := h
    have hw' := (SetM.mem_run_foldlM_update_of_nodup
      (fun i _ (_ : Fin m → ℝ) => fp.round (x i / v₁)) t ht (fun _ _ _ _ _ _ => rfl) v w).1 hw
    obtain ⟨hwout, hwin⟩ := hw'
    have hwp : w p = 1 := by rw [hwout p hp, hvp]
    refine ⟨fun i hi => ?_, σ, hdot, hwp, Or.inr (Or.inr ⟨hσ0, a, b, μ, v₁, q, c, d, ha, hb, hμ,
      ?_, hq, hc, hd, hβ, fun j hj => hwin j (htail j hj)⟩)⟩
    · have hit : i ∉ t := fun h => hi (List.mem_cons_of_mem _ h)
      change w i = 0
      rw [hwout i hit, hvout i hi]
    · unfold parlettPivot at hv₁
      by_cases hxp : x p ≤ 0
      · simp only [hxp, ↓reduceIte] at hv₁
        exact Or.inl ⟨hxp, hv₁⟩
      · simp only [hxp, ↓reduceIte, SetM.mem_run_bind] at hv₁
        exact Or.inr ⟨lt_of_not_ge hxp, hv₁⟩

/-- The exact run of `house` is the run of the exact model. -/
private theorem houseOn_mem_exact (o : List (Fin m)) (x : Fin m → ℝ) :
    Id.run (houseOn pure o x) ∈ (houseOn (RoundingModel.exact ℝ).round o x).run := by
  rw [RoundingModel.round_exact]
  cases o with
  | nil => rfl
  | cons p t =>
    simp only [houseOn, parlettPivot, dotAccum_pure, pure_bind, List.foldlM_pure]
    split_ifs <;> simp only [pure_bind, SetM.mem_run_pure] <;> rfl

/-- **Transport of reflector data along an equivalence of index types.** -/
theorem IsReflectorPert.of_comp_equiv {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : κ ≃ ι) {u : ℝ} {K : ℕ} {x : ι → ℝ} {i : ι} {c : ℝ} {vhat : ι → ℝ}
    {βhat : ℝ} (h : IsReflectorPert u K (x ∘ e) (e.symm i) c (vhat ∘ e) βhat) :
    IsReflectorPert u K x i c vhat βhat := by
  obtain ⟨v, β, hO, hmul, hβv, hβ, hv⟩ := h
  have hdot : ∀ y : ι → ℝ, (v ∘ e.symm) ⬝ᵥ y = v ⬝ᵥ (y ∘ e) := fun y => by
    rw [dotProduct_comm, dotProduct_comp_equiv_symm, dotProduct_comm]
  have hvv : (v ∘ e.symm) ⬝ᵥ (v ∘ e.symm) = v ⬝ᵥ v := by
    rw [hdot]; congr 1; ext j; simp
  refine ⟨v ∘ e.symm, β, ?_, ?_, by rwa [hvv], hβ, fun j => by simpa using hv (e.symm j)⟩
  · -- orthogonality is `β (β vᵀv - 2) = 0` unless `v = 0`
    by_cases hv0 : v = 0
    · subst hv0
      have : (0 : κ → ℝ) ∘ e.symm = 0 := rfl
      rw [this, vecMulVec_zero, smul_zero, sub_zero]
      exact one_mem _
    · obtain ⟨p, hp⟩ := Function.ne_iff.1 hv0
      refine one_sub_smul_vecMulVec_mem_orthogonalGroup ?_
      rw [hvv]
      exact beta_mul_eq_zero_of_mem_orthogonalGroup hp hO
  · funext j
    have hj := congrFun hmul (e.symm j)
    rw [one_sub_smul_vecMulVec_mulVec_apply] at hj ⊢
    rw [hdot]
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
    rw [hj]
    congr 1
    by_cases hji : j = i
    · subst hji; simp
    · rw [Pi.single_eq_of_ne hji, Pi.single_eq_of_ne (fun h => hji (e.symm.injective h))]

/-- **Exact semantics of `house` on an index list** (read off the bridge at the exact model,
convention 11): for a duplicate-free nonempty `o` with head `p`, the exact output `(v, β)` has
`v p = 1`, vanishes off `o`, `β = 0 ∨ β vᵀv = 2` (so `1 - β v vᵀ` is `1` or
`householderMatrix v`), `1 - β v vᵀ` is orthogonal, and it maps `x` to the vector that is
`‖x|_o‖₂` at the pivot, `0` on the tail and `x` off `o`: the reflector acts on the coordinates of
`o` only. -/
theorem houseOn_spec {o : List (Fin m)} (ho : o.Nodup) (hne : o ≠ []) (x : Fin m → ℝ) :
    (Id.run (houseOn pure o x)).1 (o.head hne) = 1 ∧
      (∀ i, i ∉ o → (Id.run (houseOn pure o x)).1 i = 0) ∧
      ((Id.run (houseOn pure o x)).2 = 0 ∨
        (Id.run (houseOn pure o x)).2 *
          ((Id.run (houseOn pure o x)).1 ⬝ᵥ (Id.run (houseOn pure o x)).1) = 2) ∧
      (1 - (Id.run (houseOn pure o x)).2 •
        vecMulVec (Id.run (houseOn pure o x)).1 (Id.run (houseOn pure o x)).1) ∈
          orthogonalGroup (Fin m) ℝ ∧
      (1 - (Id.run (houseOn pure o x)).2 •
        vecMulVec (Id.run (houseOn pure o x)).1 (Id.run (houseOn pure o x)).1) *ᵥ x =
          fun i => if i = o.head hne then
              ‖(toLp 2 (fun j : {j // j ∈ o} => x j) : EuclideanSpace ℝ {j // j ∈ o})‖
            else if i ∈ o then 0 else x i := by
  obtain ⟨hout, hrel⟩ := houseOn_rounds RoundingModel.isIdempotent_exact ho hne x
    (houseOn_mem_exact o x)
  generalize Id.run (houseOn pure o x) = vβ at hout hrel ⊢
  obtain ⟨hvp, v, β, hO, hmul, -, hβ, hv⟩ := hrel.isReflectorPert (by simp)
  simp only [RoundingModel.exact_u] at hβ hv
  have hβ' : vβ.2 = β := eq_of_isRelPert_zero hβ
  have hv' : (fun i : {i // i ∈ o} => vβ.1 i) = v := funext fun j => eq_of_isRelPert_zero (hv j)
  subst hβ' hv'
  have hdot : vβ.1 ⬝ᵥ vβ.1 =
      (fun i : {i // i ∈ o} => vβ.1 i) ⬝ᵥ (fun i : {i // i ∈ o} => vβ.1 i) :=
    dotProduct_eq_dotProduct_subtype o hout _
  have hc := beta_mul_eq_zero_of_mem_orthogonalGroup (v := fun i : {i // i ∈ o} => vβ.1 i)
    (p := ⟨o.head hne, List.head_mem hne⟩) (by rw [hvp]; exact one_ne_zero) hO
  rw [← hdot] at hc
  refine ⟨hvp, hout, ?_, one_sub_smul_vecMulVec_mem_orthogonalGroup hc, ?_⟩
  · rcases mul_eq_zero.1 hc with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · funext i
    rw [one_sub_smul_vecMulVec_mulVec_apply_subtype o hout]
    by_cases hio : i ∈ o
    · simp only [hio, ↓reduceDIte]
      rw [hmul]
      by_cases hih : i = o.head hne
      · subst hih
        simp
      · simp [hih]
    · have hih : i ≠ o.head hne := fun e => hio (e ▸ List.head_mem hne)
      simp [hio, hih]

/-- **§5.1.5, first claim, rigorous** ("house produces a Householder vector `v̂` that is very
close to the exact `v`"), on an index list: with `n = |o|`, `K = 18 n + 31`, `K u < 1` and an
idempotent model, every run `(v̂, β̂)` of `houseOn fp.round o x` vanishes off `o` and on
`{i // i ∈ o}` is reflector data of order `K` (`FloatingPoint.IsReflectorPert`): exact `(v, β)`
with `1 - β v vᵀ` orthogonal, sending `x|_o` to `‖x|_o‖₂ e_head`, `|β| vᵀv ≤ 2`, and
`β̂ = β (1 + θ)`, `v̂_i = v_i (1 + θ_i)` with `|θ|, |θ_i| ≤ γ_K`. The book's `O(u)` is `γ_K`. -/
theorem houseOn_rounding {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent) {o : List (Fin m)}
    (ho : o.Nodup) (hne : o ≠ []) (hu : ((18 * o.length + 31 : ℕ) : ℝ) * fp.u < 1)
    (x : Fin m → ℝ) {vβ : (Fin m → ℝ) × ℝ} (h : vβ ∈ (houseOn fp.round o x).run) :
    (∀ i, i ∉ o → vβ.1 i = 0) ∧
      IsReflectorPert fp.u (18 * o.length + 31) (fun i : {i // i ∈ o} => x i)
        ⟨o.head hne, List.head_mem hne⟩
        ‖(toLp 2 (fun j : {j // j ∈ o} => x j) : EuclideanSpace ℝ {j // j ∈ o})‖
        (fun i => vβ.1 i) vβ.2 := by
  obtain ⟨hout, hrel⟩ := houseOn_rounds hfp ho hne x h
  have hcard := card_subtype_mem_of_nodup ho
  refine ⟨hout, ?_⟩
  have := (hrel.isReflectorPert (by rwa [hcard])).2
  rwa [hcard] at this

end HouseRuns

/-! ### Algorithm 5.1.1 on a whole vector -/

section HouseVector

variable {k : ℕ}

/-- The subtype of the full index list is the whole index type. -/
private def finRangeEquiv (k : ℕ) : {i // i ∈ List.finRange (k + 1)} ≃ Fin (k + 1) :=
  Equiv.subtypeUnivEquiv List.mem_finRange

/-- The Euclidean norm of the restriction to the full index list is the norm. -/
private theorem norm_toLp_finRange (x : Fin (k + 1) → ℝ) :
    ‖(toLp 2 (fun j : {j // j ∈ List.finRange (k + 1)} => x j) :
        EuclideanSpace ℝ {j // j ∈ List.finRange (k + 1)})‖ =
      ‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖ := by
  simp only [EuclideanSpace.norm_eq]
  congr 1
  exact Fintype.sum_equiv (finRangeEquiv k) _ _ fun _ => rfl

/-- The head of the full index list is `0`. -/
private theorem head_finRange (h : List.finRange (k + 1) ≠ []) :
    (List.finRange (k + 1)).head h = 0 := by
  simp [List.finRange_succ]

/-- **Algorithm 5.1.1, exact semantics**: with `(v, β) = house(x)` in exact arithmetic, `v(1) = 1`,
`P = I - β v vᵀ` is orthogonal, `P x = ‖x‖₂ e₁`, and `β = 0 ∨ β vᵀv = 2` (so `P` is `I` or the
Householder matrix of `v`). The cases of the book: `σ = 0` (`x = x₁ e₁`; `β = 0` for `x₁ ≥ 0`,
`P = I - 2 e₁ e₁ᵀ` for `x₁ < 0`), otherwise `v = (x - ‖x‖₂ e₁) / (x₁ - ‖x‖₂)` with Parlett's
formula for `x₁ > 0`. -/
theorem algorithm_5_1_1_spec (x : Fin (k + 1) → ℝ) :
    (Id.run (algorithm_5_1_1 pure x)).1 0 = 1 ∧
      (1 - (Id.run (algorithm_5_1_1 pure x)).2 •
        vecMulVec (Id.run (algorithm_5_1_1 pure x)).1 (Id.run (algorithm_5_1_1 pure x)).1) ∈
          orthogonalGroup (Fin (k + 1)) ℝ ∧
      (1 - (Id.run (algorithm_5_1_1 pure x)).2 •
        vecMulVec (Id.run (algorithm_5_1_1 pure x)).1 (Id.run (algorithm_5_1_1 pure x)).1) *ᵥ x =
          ‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖ • Pi.single 0 1 ∧
      ((Id.run (algorithm_5_1_1 pure x)).2 = 0 ∨
        (Id.run (algorithm_5_1_1 pure x)).2 *
          ((Id.run (algorithm_5_1_1 pure x)).1 ⬝ᵥ (Id.run (algorithm_5_1_1 pure x)).1) = 2) := by
  have hne : List.finRange (k + 1) ≠ [] := by simp
  obtain ⟨h1, -, h3, h4, h5⟩ := houseOn_spec (List.nodup_finRange (k + 1)) hne x
  rw [head_finRange] at h1 h5
  refine ⟨h1, h4, ?_, h3⟩
  rw [algorithm_5_1_1, h5, norm_toLp_finRange]
  funext i
  by_cases hi : i = 0
  · subst hi; simp
  · simp [hi]

/-- **§5.1.5, first claim, for the book's `house` on a whole vector**: with `K = 18 (k + 1) + 31`,
`K u < 1` and an idempotent model, every run `(v̂, β̂)` of Algorithm 5.1.1 is reflector data of
order `K` for `x` with target `‖x‖₂ e₁`: there are exact `(v, β)` (the exact output of the same
branch) with `P = 1 - β v vᵀ` orthogonal, `P x = ‖x‖₂ e₁`, `|β| vᵀv ≤ 2`, and
`β̂ = β (1 + θ)`, `v̂_i = v_i (1 + θ_i)`, `|θ|, |θ_i| ≤ γ_K`. -/
theorem algorithm_5_1_1_rounding {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent)
    (hu : ((18 * (k + 1) + 31 : ℕ) : ℝ) * fp.u < 1) (x : Fin (k + 1) → ℝ)
    {vβ : (Fin (k + 1) → ℝ) × ℝ} (h : vβ ∈ (algorithm_5_1_1 fp.round x).run) :
    IsReflectorPert fp.u (18 * (k + 1) + 31) x 0 ‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖
      vβ.1 vβ.2 := by
  have hne : List.finRange (k + 1) ≠ [] := by simp
  have hlen : (List.finRange (k + 1)).length = k + 1 := List.length_finRange
  obtain ⟨-, hr⟩ := houseOn_rounding hfp (List.nodup_finRange (k + 1)) hne (by rwa [hlen]) x h
  rw [hlen, norm_toLp_finRange] at hr
  refine IsReflectorPert.of_comp_equiv (finRangeEquiv k) ?_
  convert hr using 2
  all_goals first
    | rfl
    | exact (head_finRange hne).symm

end HouseVector

/-! ### §5.1.4 Applying Householder matrices -/

section Apply

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {m n : ℕ}

/-- The scaled Householder vector `w = fl(β v)` on the listed entries (the book's `βv`, formed
once). -/
def householderScaled (v : Fin m → ℝ) (β : ℝ) (l : List (Fin m)) : M (Fin m → ℝ) :=
  l.foldlM (fun (w : Fin m → ℝ) i => do
    let b ← rnd (β * v i)
    pure (Function.update w i b)) 0

/-- One column of the premultiplication `A - (βv)(vᵀA)`: `s = vᵀ a` over `rows` by
Algorithm 1.1.1, then `a(i) ← fl(a(i) - fl(w(i) s))` for `i ∈ rows`, with `w = fl(βv)`. -/
def householderLeftColumn (w v : Fin m → ℝ) (rows : List (Fin m)) (a : Fin m → ℝ) :
    M (Fin m → ℝ) := do
  let s ← dotAccum rnd rows v a 0
  rows.foldlM (fun (a : Fin m → ℝ) i => do
    let b ← (do let t ← rnd (w i * s); rnd (a i - t))
    pure (Function.update a i b)) a

/-- **§5.1.4, premultiplication** `PA = A - (βv)(vᵀA)`, "a matrix-vector product and a rank-1
update", in place on the block `A(rows, cols)` of the full matrix (convention 10): the book's
`A(rows, cols) = (I - β v vᵀ) A(rows, cols)`. `w = fl(βv)` is formed once; then for each column
`q ∈ cols`, `s = vᵀ A(rows, q)` by Algorithm 1.1.1 and `A(i, q) ← fl(A(i, q) - fl(w(i) s))`.
Entries outside `rows × cols` are untouched. -/
def householderApplyLeft (v : Fin m → ℝ) (β : ℝ) (rows : List (Fin m)) (cols : List (Fin n))
    (A : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) := do
  let w ← householderScaled rnd v β rows
  cols.foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) q => do
    let c ← householderLeftColumn rnd w v rows (fun i => A i q)
    pure (A.updateCol q c)) A

/-- One row of the postmultiplication `A - (Av)(βv)ᵀ`: `s = aᵀ v` over `cols` by Algorithm 1.1.1,
then `a(j) ← fl(a(j) - fl(s w(j)))` for `j ∈ cols`, with `w = fl(βv)`. -/
def householderRightRow (w v : Fin n → ℝ) (cols : List (Fin n)) (a : Fin n → ℝ) :
    M (Fin n → ℝ) := do
  let s ← dotAccum rnd cols a v 0
  cols.foldlM (fun (a : Fin n → ℝ) j => do
    let b ← (do let t ← rnd (s * w j); rnd (a j - t))
    pure (Function.update a j b)) a

/-- **§5.1.4, postmultiplication** `AP = A - (Av)(βv)ᵀ`, in place on the block `A(rows, cols)`:
the book's `A(rows, cols) = A(rows, cols)(I - β v vᵀ)`. `w = fl(βv)` is formed once; then for each
row `r ∈ rows`, `s = A(r, cols) v` by Algorithm 1.1.1 and `A(r, j) ← fl(A(r, j) - fl(s w(j)))`.
The symmetric twin of `householderApplyLeft` (convention 14). -/
def householderApplyRight (v : Fin n → ℝ) (β : ℝ) (rows : List (Fin m)) (cols : List (Fin n))
    (A : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) := do
  let w ← householderScaled rnd v β cols
  rows.foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) r => do
    let x ← householderRightRow rnd w v cols (A r)
    pure (A.updateRow r x)) A

end Apply

/-! ### The Householder updates: bridges, exact semantics, rounding bounds -/

section ApplyRuns

variable {m n : ℕ} {fp : RoundingModel ℝ}

/-- `RoundsDot` in the exact model is the exact inner product. -/
theorem eq_dotProduct_of_roundsDot_exact {ι : Type} [Fintype ι] {x y : ι → ℝ} {s : ℝ}
    (h : RoundsDot (RoundingModel.exact ℝ) x y s) : s = x ⬝ᵥ y := by
  have := abs_sub_le_of_roundsDot (by simp) (by simp) h
  simp only [RoundingModel.exact_u, gamma, mul_zero, zero_div, sub_zero, zero_mul] at this
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-- Every run of `householderScaled` rounds `β v i` on the listed entries. -/
theorem householderScaled_rounds {l : List (Fin m)} (hl : l.Nodup) {v w : Fin m → ℝ} {β : ℝ}
    (h : w ∈ (householderScaled fp.round v β l).run) : ∀ i ∈ l, fp.Rounds (β * v i) (w i) :=
  ((SetM.mem_run_foldlM_update_of_nodup (fun i _ (_ : Fin m → ℝ) => fp.round (β * v i)) l hl
    (fun _ _ _ _ _ _ => rfl) 0 w).1 h).2

/-- The bridge of one column of the premultiplication. -/
theorem householderLeftColumn_rounds (hfp : fp.IsIdempotent) {rows : List (Fin m)}
    (hrows : rows.Nodup) {β : ℝ} {w v a b : Fin m → ℝ}
    (hw : ∀ i ∈ rows, fp.Rounds (β * v i) (w i))
    (h : b ∈ (householderLeftColumn fp.round w v rows a).run) :
    (∀ i, i ∉ rows → b i = a i) ∧
      RoundsHouseholderApplyScaled fp β (fun i : {i // i ∈ rows} => v i) (fun i => a i)
        (fun i => b i) := by
  rw [householderLeftColumn, SetM.mem_run_bind] at h
  obtain ⟨s, hs, hb⟩ := h
  obtain ⟨hout, hin⟩ := (SetM.mem_run_foldlM_update_of_nodup
    (fun i b' (_ : Fin m → ℝ) => do let t ← fp.round (w i * s); fp.round (b' - t)) rows hrows
    (fun _ _ _ _ _ _ => rfl) a b).1 hb
  refine ⟨hout, s, fun i => w i, roundsDot_subtype_of_mem_run_dotAccum hfp hrows hs,
    fun i => hw i i.2, fun i => ?_⟩
  have := hin i i.2
  simpa only [SetM.mem_run_bind, RoundingModel.mem_run_round] using this

/-- The bridge of one row of the postmultiplication (the products `fl(s w_j)` are the relation's
`fl(w_j s)`, and the inner product `aᵀv` its `vᵀa`). -/
theorem householderRightRow_rounds (hfp : fp.IsIdempotent) {cols : List (Fin n)}
    (hcols : cols.Nodup) {β : ℝ} {w v a b : Fin n → ℝ}
    (hw : ∀ j ∈ cols, fp.Rounds (β * v j) (w j))
    (h : b ∈ (householderRightRow fp.round w v cols a).run) :
    (∀ j, j ∉ cols → b j = a j) ∧
      RoundsHouseholderApplyScaled fp β (fun j : {j // j ∈ cols} => v j) (fun j => a j)
        (fun j => b j) := by
  rw [householderRightRow, SetM.mem_run_bind] at h
  obtain ⟨s, hs, hb⟩ := h
  obtain ⟨hout, hin⟩ := (SetM.mem_run_foldlM_update_of_nodup
    (fun j b' (_ : Fin n → ℝ) => do let t ← fp.round (s * w j); fp.round (b' - t)) cols hcols
    (fun _ _ _ _ _ _ => rfl) a b).1 hb
  have hdot := roundsDot_subtype_of_mem_run_dotAccum hfp hcols hs
  refine ⟨hout, s, fun j => w j, ?_, fun j => hw j j.2, fun j => ?_⟩
  · obtain ⟨o, p, ho, hfull, hp, hsum⟩ := hdot
    exact ⟨o, p, ho, hfull, fun j => by rw [mul_comm]; exact hp j, hsum⟩
  · have := hin j j.2
    simp only [SetM.mem_run_bind, RoundingModel.mem_run_round] at this
    obtain ⟨t, ht, hb⟩ := this
    exact ⟨t, by rwa [mul_comm], hb⟩

/-- **The bridge of the premultiplication** (convention 12): over an idempotent model and for
duplicate-free `rows`, `cols`, every run `B` of `householderApplyLeft fp.round v β rows cols A`
agrees with `A` outside `rows × cols`, and for every `q ∈ cols` the column `B(rows, q)` is a
computed update `FloatingPoint.RoundsHouseholderApplyScaled` of `A(rows, q)` with `(β, v(rows))`.
-/
theorem householderApplyLeft_rounds (hfp : fp.IsIdempotent) {rows : List (Fin m)}
    {cols : List (Fin n)} (hrows : rows.Nodup) (hcols : cols.Nodup) (v : Fin m → ℝ) (β : ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) {B : Matrix (Fin m) (Fin n) ℝ}
    (h : B ∈ (householderApplyLeft fp.round v β rows cols A).run) :
    (∀ i q, (i ∉ rows ∨ q ∉ cols) → B i q = A i q) ∧
      ∀ q ∈ cols, RoundsHouseholderApplyScaled fp β (fun i : {i // i ∈ rows} => v i)
        (fun i => A i q) (fun i => B i q) := by
  rw [householderApplyLeft, SetM.mem_run_bind] at h
  obtain ⟨w, hw, hB⟩ := h
  have hw' := householderScaled_rounds hrows hw
  obtain ⟨hout, hin⟩ := (mem_run_foldlM_updateCol_of_nodup
    (fun q a => householderLeftColumn fp.round w v rows a) hcols A B).1 hB
  refine ⟨fun i q hiq => ?_, fun q hq =>
    (householderLeftColumn_rounds hfp hrows hw' (hin q hq)).2⟩
  by_cases hq : q ∈ cols
  · have hi : i ∉ rows := hiq.resolve_right (not_not.2 hq)
    exact (householderLeftColumn_rounds hfp hrows hw' (hin q hq)).1 i hi
  · exact hout q hq i

/-- **The bridge of the postmultiplication**, rowwise: every run `B` of
`householderApplyRight fp.round v β rows cols A` agrees with `A` outside `rows × cols`, and for
every `r ∈ rows` the row `B(r, cols)` is a computed update `RoundsHouseholderApplyScaled` of
`A(r, cols)` with `(β, v(cols))`. -/
theorem householderApplyRight_rounds (hfp : fp.IsIdempotent) {rows : List (Fin m)}
    {cols : List (Fin n)} (hrows : rows.Nodup) (hcols : cols.Nodup) (v : Fin n → ℝ) (β : ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) {B : Matrix (Fin m) (Fin n) ℝ}
    (h : B ∈ (householderApplyRight fp.round v β rows cols A).run) :
    (∀ r j, (r ∉ rows ∨ j ∉ cols) → B r j = A r j) ∧
      ∀ r ∈ rows, RoundsHouseholderApplyScaled fp β (fun j : {j // j ∈ cols} => v j)
        (fun j => A r j) (fun j => B r j) := by
  rw [householderApplyRight, SetM.mem_run_bind] at h
  obtain ⟨w, hw, hB⟩ := h
  have hw' := householderScaled_rounds hcols hw
  obtain ⟨hout, hin⟩ := (mem_run_foldlM_updateRow_of_nodup
    (fun r a => householderRightRow fp.round w v cols a) hrows A B).1 hB
  refine ⟨fun r j hrj => ?_, fun r hr =>
    (householderRightRow_rounds hfp hcols hw' (hin r hr)).2⟩
  by_cases hr : r ∈ rows
  · have hj : j ∉ cols := hrj.resolve_left (not_not.2 hr)
    exact (householderRightRow_rounds hfp hcols hw' (hin r hr)).1 j hj
  · exact congrFun (hout r hr) j

/-- In the exact model the computed update is the exact one. -/
theorem eq_of_roundsHouseholderApplyScaled_exact {ι : Type} [Fintype ι] {β : ℝ}
    {v b y : ι → ℝ} (h : RoundsHouseholderApplyScaled (RoundingModel.exact ℝ) β v b y) (i : ι) :
    y i = b i - β * v i * (v ⬝ᵥ b) := by
  obtain ⟨s, w, hs, hw, ht⟩ := h
  obtain ⟨t, ht, hy⟩ := ht i
  rw [RoundingModel.exact_rounds_iff] at ht hy
  rw [hy, ht, (RoundingModel.exact_rounds_iff).1 (hw i), eq_dotProduct_of_roundsDot_exact hs]

private theorem householderApplyLeft_mem_exact (v : Fin m → ℝ) (β : ℝ) (rows : List (Fin m))
    (cols : List (Fin n)) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (householderApplyLeft pure v β rows cols A) ∈
      (householderApplyLeft (RoundingModel.exact ℝ).round v β rows cols A).run := by
  rw [RoundingModel.round_exact]
  simp only [householderApplyLeft, householderScaled, householderLeftColumn, dotAccum_pure,
    pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

private theorem householderApplyRight_mem_exact (v : Fin n → ℝ) (β : ℝ) (rows : List (Fin m))
    (cols : List (Fin n)) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (householderApplyRight pure v β rows cols A) ∈
      (householderApplyRight (RoundingModel.exact ℝ).round v β rows cols A).run := by
  rw [RoundingModel.round_exact]
  simp only [householderApplyRight, householderScaled, householderRightRow, dotAccum_pure,
    pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

/-- **Exact semantics of the premultiplication** (read off the bridge at the exact model,
convention 11): for duplicate-free lists and `v` vanishing off `rows`, the result is
`(I - β v vᵀ) A` in the columns of `cols` and `A` elsewhere. -/
theorem householderApplyLeft_spec {rows : List (Fin m)} {cols : List (Fin n)}
    (hrows : rows.Nodup) (hcols : cols.Nodup) {v : Fin m → ℝ} (hv : ∀ i, i ∉ rows → v i = 0)
    (β : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (householderApplyLeft pure v β rows cols A) =
      of fun i q => if q ∈ cols then
        ((1 - β • vecMulVec v v : Matrix (Fin m) (Fin m) ℝ) * A) i q else A i q := by
  obtain ⟨hout, hin⟩ := householderApplyLeft_rounds RoundingModel.isIdempotent_exact hrows hcols
    v β A
    (householderApplyLeft_mem_exact v β rows cols A)
  ext i q
  rw [of_apply]
  split_ifs with hq
  · have hPA : ((1 - β • vecMulVec v v : Matrix (Fin m) (Fin m) ℝ) * A) i q =
        ((1 - β • vecMulVec v v) *ᵥ fun r => A r q) i :=
      rfl
    rw [hPA, one_sub_smul_vecMulVec_mulVec_apply_subtype rows hv]
    split_ifs with hi
    · rw [one_sub_smul_vecMulVec_mulVec_apply]
      exact eq_of_roundsHouseholderApplyScaled_exact (hin q hq) ⟨i, hi⟩
    · exact hout i q (Or.inl hi)
  · exact hout i q (Or.inr hq)

/-- The premultiplication on all columns is `(I - β v vᵀ) A`. -/
theorem householderApplyLeft_spec_of_forall_mem {rows : List (Fin m)} {cols : List (Fin n)}
    (hrows : rows.Nodup) (hcols : cols.Nodup) (hall : ∀ q, q ∈ cols) {v : Fin m → ℝ}
    (hv : ∀ i, i ∉ rows → v i = 0) (β : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (householderApplyLeft pure v β rows cols A) = (1 - β • vecMulVec v v) * A := by
  rw [householderApplyLeft_spec hrows hcols hv]
  ext i q
  simp [hall q]

/-- **Exact semantics of the postmultiplication**: for duplicate-free lists and `v` vanishing off
`cols`, the result is `A (I - β v vᵀ)` in the rows of `rows` and `A` elsewhere. -/
theorem householderApplyRight_spec {rows : List (Fin m)} {cols : List (Fin n)}
    (hrows : rows.Nodup) (hcols : cols.Nodup) {v : Fin n → ℝ} (hv : ∀ j, j ∉ cols → v j = 0)
    (β : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (householderApplyRight pure v β rows cols A) =
      of fun r j => if r ∈ rows then
        (A * (1 - β • vecMulVec v v : Matrix (Fin n) (Fin n) ℝ)) r j else A r j := by
  obtain ⟨hout, hin⟩ := householderApplyRight_rounds RoundingModel.isIdempotent_exact hrows hcols
    v β A
    (householderApplyRight_mem_exact v β rows cols A)
  ext r j
  rw [of_apply]
  split_ifs with hr
  · have hAP : (A * (1 - β • vecMulVec v v : Matrix (Fin n) (Fin n) ℝ)) r j =
        ((1 - β • vecMulVec v v) *ᵥ A r) j := by
      conv_rhs => rw [← transpose_one_sub_smul_vecMulVec β v, mulVec_transpose]
      rfl
    rw [hAP, one_sub_smul_vecMulVec_mulVec_apply_subtype cols hv]
    split_ifs with hj
    · rw [one_sub_smul_vecMulVec_mulVec_apply]
      exact eq_of_roundsHouseholderApplyScaled_exact (hin r hr) ⟨j, hj⟩
    · exact hout r j (Or.inr hj)
  · exact hout r j (Or.inl hr)

/-- The postmultiplication on all rows is `A (I - β v vᵀ)`. -/
theorem householderApplyRight_spec_of_forall_mem {rows : List (Fin m)} {cols : List (Fin n)}
    (hrows : rows.Nodup) (hcols : cols.Nodup) (hall : ∀ r, r ∈ rows) {v : Fin n → ℝ}
    (hv : ∀ j, j ∉ cols → v j = 0) (β : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (householderApplyRight pure v β rows cols A) = A * (1 - β • vecMulVec v v) := by
  rw [householderApplyRight_spec hrows hcols hv]
  ext r j
  simp [hall r]

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **§5.1.5, second claim, rigorous**: `fl(P̂ A) = P A + F` with `‖F‖ ≤ ε ‖A‖`, on the block. If
the computed `(v̂, β̂)` are relative perturbations of order `K` of exact `(v, β)` with
`|β| vᵀv ≤ 2`, `v` vanishing off `rows`, the model idempotent and `(3K + |rows| + 3) u < 1`, then
every run `B` of `householderApplyLeft fp.round v̂ β̂ rows cols A` agrees with `A` outside
`rows × cols`, and on the block, with `P = I - β v vᵀ` restricted to `rows`, every column satisfies
`‖B(rows, q) - P A(rows, q)‖₂ ≤ ε ‖A(rows, q)‖₂` and `‖B(rows, cols) - P A(rows, cols)‖_F ≤
ε ‖A(rows, cols)‖_F`, `ε = 3 γ_{3K + |rows| + 3}`. With `P` orthogonal this is the book's
`fl(P̂ A) = P (A + E)`, `E = Pᵀ fl(P̂ A) - A`, `‖E‖ = ‖fl(P̂ A) - P A‖`. -/
theorem householderApplyLeft_rounding (hfp : fp.IsIdempotent) {rows : List (Fin m)}
    {cols : List (Fin n)} (hrows : rows.Nodup) (hcols : cols.Nodup) {K : ℕ}
    (hu : ((3 * K + rows.length + 3 : ℕ) : ℝ) * fp.u < 1) {v vhat : Fin m → ℝ}
    {β βhat : ℝ} (hβ : IsRelPert fp.u K β βhat) (hvv : ∀ i, IsRelPert fp.u K (v i) (vhat i))
    (hv : ∀ i, i ∉ rows → v i = 0) (hP : |β| * (v ⬝ᵥ v) ≤ 2) (A : Matrix (Fin m) (Fin n) ℝ)
    {B : Matrix (Fin m) (Fin n) ℝ}
    (h : B ∈ (householderApplyLeft fp.round vhat βhat rows cols A).run) :
    (∀ i q, (i ∉ rows ∨ q ∉ cols) → B i q = A i q) ∧
      (∀ q : {q // q ∈ cols},
        ‖(toLp 2 ((B.submatrix (Subtype.val : {i // i ∈ rows} → Fin m) Subtype.val -
          (1 - β • vecMulVec (fun i : {i // i ∈ rows} => v i) (fun i : {i // i ∈ rows} => v i)) *
            A.submatrix (Subtype.val : {i // i ∈ rows} → Fin m) Subtype.val).col q) :
              EuclideanSpace ℝ {i // i ∈ rows})‖ ≤
          3 * gamma fp.u (3 * K + rows.length + 3) *
            ‖(toLp 2 ((A.submatrix (Subtype.val : {i // i ∈ rows} → Fin m)
              (Subtype.val : {q // q ∈ cols} → Fin n)).col q) :
                EuclideanSpace ℝ {i // i ∈ rows})‖) ∧
      ‖B.submatrix (Subtype.val : {i // i ∈ rows} → Fin m)
          (Subtype.val : {q // q ∈ cols} → Fin n) -
        (1 - β • vecMulVec (fun i : {i // i ∈ rows} => v i) (fun i : {i // i ∈ rows} => v i)) *
          A.submatrix (Subtype.val : {i // i ∈ rows} → Fin m)
            (Subtype.val : {q // q ∈ cols} → Fin n)‖ ≤
        3 * gamma fp.u (3 * K + rows.length + 3) *
          ‖A.submatrix (Subtype.val : {i // i ∈ rows} → Fin m)
            (Subtype.val : {q // q ∈ cols} → Fin n)‖ := by
  obtain ⟨hout, hin⟩ := householderApplyLeft_rounds hfp hrows hcols vhat βhat A h
  have hcard := card_subtype_mem_of_nodup hrows
  have hP' : |β| * ((fun i : {i // i ∈ rows} => v i) ⬝ᵥ (fun i => v i)) ≤ 2 := by
    rwa [← dotProduct_eq_dotProduct_subtype rows hv]
  have := frobenius_norm_sub_le_of_forall_roundsHouseholderApplyScaled_col
    (ι := {i // i ∈ rows}) (κ := {q // q ∈ cols}) (by rwa [hcard]) hβ (fun i => hvv i) hP'
    (A := A.submatrix Subtype.val Subtype.val) (B := B.submatrix Subtype.val Subtype.val)
    (fun q => hin q q.2)
  rw [hcard] at this
  exact ⟨hout, this⟩

/-- **§5.1.5, the postmultiplication form** `fl(A P̂) = A P + F`, rowwise and in the Frobenius
norm on the block: under the hypotheses of `householderApplyLeft_rounding` with `v` vanishing off
`cols`, every row satisfies `‖B(r, cols) - A(r, cols) P‖₂ ≤ ε ‖A(r, cols)‖₂` and
`‖B(rows, cols) - A(rows, cols) P‖_F ≤ ε ‖A(rows, cols)‖_F`, `ε = 3 γ_{3K + |cols| + 3}`. -/
theorem householderApplyRight_rounding (hfp : fp.IsIdempotent) {rows : List (Fin m)}
    {cols : List (Fin n)} (hrows : rows.Nodup) (hcols : cols.Nodup) {K : ℕ}
    (hu : ((3 * K + cols.length + 3 : ℕ) : ℝ) * fp.u < 1) {v vhat : Fin n → ℝ}
    {β βhat : ℝ} (hβ : IsRelPert fp.u K β βhat) (hvv : ∀ j, IsRelPert fp.u K (v j) (vhat j))
    (hv : ∀ j, j ∉ cols → v j = 0) (hP : |β| * (v ⬝ᵥ v) ≤ 2) (A : Matrix (Fin m) (Fin n) ℝ)
    {B : Matrix (Fin m) (Fin n) ℝ}
    (h : B ∈ (householderApplyRight fp.round vhat βhat rows cols A).run) :
    (∀ r j, (r ∉ rows ∨ j ∉ cols) → B r j = A r j) ∧
      (∀ r : {r // r ∈ rows},
        ‖(toLp 2 ((B.submatrix (Subtype.val : {r // r ∈ rows} → Fin m)
            (Subtype.val : {j // j ∈ cols} → Fin n) -
          A.submatrix (Subtype.val : {r // r ∈ rows} → Fin m)
              (Subtype.val : {j // j ∈ cols} → Fin n) *
            (1 - β • vecMulVec (fun j : {j // j ∈ cols} => v j)
              (fun j : {j // j ∈ cols} => v j))).row r) :
              EuclideanSpace ℝ {j // j ∈ cols})‖ ≤
          3 * gamma fp.u (3 * K + cols.length + 3) *
            ‖(toLp 2 ((A.submatrix (Subtype.val : {r // r ∈ rows} → Fin m)
              (Subtype.val : {j // j ∈ cols} → Fin n)).row r) :
                EuclideanSpace ℝ {j // j ∈ cols})‖) ∧
      ‖B.submatrix (Subtype.val : {r // r ∈ rows} → Fin m)
          (Subtype.val : {j // j ∈ cols} → Fin n) -
        A.submatrix (Subtype.val : {r // r ∈ rows} → Fin m)
            (Subtype.val : {j // j ∈ cols} → Fin n) *
          (1 - β • vecMulVec (fun j : {j // j ∈ cols} => v j) (fun j : {j // j ∈ cols} => v j))‖ ≤
        3 * gamma fp.u (3 * K + cols.length + 3) *
          ‖A.submatrix (Subtype.val : {r // r ∈ rows} → Fin m)
            (Subtype.val : {j // j ∈ cols} → Fin n)‖ := by
  obtain ⟨hout, hin⟩ := householderApplyRight_rounds hfp hrows hcols vhat βhat A h
  have hcard := card_subtype_mem_of_nodup hcols
  have hP' : |β| * ((fun j : {j // j ∈ cols} => v j) ⬝ᵥ (fun j => v j)) ≤ 2 := by
    rwa [← dotProduct_eq_dotProduct_subtype cols hv]
  have := frobenius_norm_sub_le_of_forall_roundsHouseholderApplyScaled_row
    (ι := {j // j ∈ cols}) (κ := {r // r ∈ rows}) (by rwa [hcard]) hβ (fun j => hvv j) hP'
    (A := A.submatrix Subtype.val Subtype.val) (B := B.submatrix Subtype.val Subtype.val)
    (fun r => hin r r.2)
  rw [hcard] at this
  exact ⟨hout, this⟩

end Frobenius

section L2

open scoped Matrix.Norms.L2Operator

/-- **§5.1.5, "`P̂ = I - 2v̂v̂ᵀ/v̂ᵀv̂` satisfies `‖P̂ - P‖₂ = O(u)`"**, rigorous: for every run
`(v̂, β̂)` of Algorithm 5.1.1 (idempotent model, `K u < 1`, `K = 18 (k + 1) + 31`) there are
exact `(v, β)` — `I - β v vᵀ` orthogonal and mapping `x` to `‖x‖₂ e₁` — with `v̂_i = v_i (1 + θ_i)`,
`|θ_i| ≤ γ_K`, and the Householder matrices of the computed and the exact vector differ by at most
`8 γ_K` in the 2-norm. -/
theorem householderMatrix_computed_sub_le {k : ℕ} (hfp : fp.IsIdempotent)
    (hu : ((18 * (k + 1) + 31 : ℕ) : ℝ) * fp.u < 1) (x : Fin (k + 1) → ℝ)
    {vβ : (Fin (k + 1) → ℝ) × ℝ} (h : vβ ∈ (algorithm_5_1_1 fp.round x).run) :
    ∃ (v : Fin (k + 1) → ℝ) (β : ℝ), (1 - β • vecMulVec v v) ∈ orthogonalGroup (Fin (k + 1)) ℝ ∧
      (1 - β • vecMulVec v v) *ᵥ x = ‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖ •
        Pi.single 0 1 ∧
      (∀ i, IsRelPert fp.u (18 * (k + 1) + 31) (v i) (vβ.1 i)) ∧
      ‖householderMatrix vβ.1 - householderMatrix v‖ ≤ 8 * gamma fp.u (18 * (k + 1) + 31) := by
  obtain ⟨v, β, hO, hmul, -, -, hv⟩ := algorithm_5_1_1_rounding hfp hu x h
  refine ⟨v, β, hO, hmul, hv, ?_⟩
  -- the computed vector has `v̂ 0 = 1`, so the exact one is nonzero
  have hne : List.finRange (k + 1) ≠ [] := by simp
  obtain ⟨σ, -, h1, -⟩ := (houseOn_rounds hfp (List.nodup_finRange (k + 1)) hne x h).2
  have h0 : vβ.1 0 = 1 := by
    have := h1; simp only [head_finRange] at this; exact this
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨θ, -, hθ⟩ := hv 0
    rw [h0, Pi.zero_apply, zero_mul] at hθ
    exact one_ne_zero hθ
  rw [householderMatrix_eq_reflector, householderMatrix_eq_reflector]
  exact l2_opNorm_reflector_sub_le hv0 hv

end L2

end ApplyRuns

/-! ### §5.1.6 The factored-form representation -/

section FactoredForm

variable {m n : ℕ}

/-- The index list `[j, j+1, …, m-1]` of `Fin m`: the rows `j:m` (or columns `j:n`) of a block
`A(j:m, j:n)` in 0-based form (convention 10). -/
def indexFrom (m j : ℕ) : List (Fin m) := (List.finRange m).filter fun i => j ≤ (i : ℕ)

/-- Membership in `indexFrom m j`. -/
@[simp]
theorem mem_indexFrom {j : ℕ} {i : Fin m} : i ∈ indexFrom m j ↔ j ≤ (i : ℕ) := by
  simp [indexFrom]

/-- `indexFrom m j` has no duplicates. -/
theorem nodup_indexFrom (m j : ℕ) : (indexFrom m j).Nodup :=
  (List.nodup_finRange m).filter _

/-- A sum of a function vanishing off a duplicate-free list is the sum along the list. -/
theorem sum_eq_sum_map_of_nodup {ι : Type} [Fintype ι] {l : List ι}
    (hl : l.Nodup) {f : ι → ℝ} (hf : ∀ i, i ∉ l → f i = 0) : ∑ i, f i = (l.map f).sum := by
  classical
  rw [← List.sum_toFinset f hl]
  exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi =>
    hf i (by simpa using hi)).symm

/-- **The orthogonal matrix of reflector data** (convention 13, §5.1.6): for reflector data
`data = [(v₁, β₁), …, (v_r, β_r)]` in order of application, `Q = Q₁ Q₂ ⋯ Q_r` with
`Q_j = I - β_j v_j v_jᵀ`. -/
noncomputable def householderProduct (data : List ((Fin m → ℝ) × ℝ)) :
    Matrix (Fin m) (Fin m) ℝ :=
  (data.map fun p => 1 - p.2 • vecMulVec p.1 p.1).prod

/-- The product of no reflectors is the identity. -/
@[simp]
theorem householderProduct_nil : householderProduct ([] : List ((Fin m → ℝ) × ℝ)) = 1 := rfl

/-- The product of `p :: data` is `(I - β v vᵀ)` times the product of `data`. -/
@[simp]
theorem householderProduct_cons (p : (Fin m → ℝ) × ℝ) (data : List ((Fin m → ℝ) × ℝ)) :
    householderProduct (p :: data) = (1 - p.2 • vecMulVec p.1 p.1) * householderProduct data :=
  rfl

/-- The product of `data ++ [p]` is the product of `data` times `(I - β v vᵀ)`. -/
theorem householderProduct_concat (data : List ((Fin m → ℝ) × ℝ)) (p : (Fin m → ℝ) × ℝ) :
    householderProduct (data ++ [p]) = householderProduct data * (1 - p.2 • vecMulVec p.1 p.1) := by
  simp [householderProduct, List.prod_append]

/-- **The product of reflector data is orthogonal** when every `(v, β)` has `β = 0` or
`β vᵀv = 2` (each factor is then `I` or a Householder matrix). -/
theorem householderProduct_mem_orthogonalGroup {data : List ((Fin m → ℝ) × ℝ)}
    (h : ∀ p ∈ data, p.2 = 0 ∨ p.2 * (p.1 ⬝ᵥ p.1) = 2) :
    householderProduct data ∈ orthogonalGroup (Fin m) ℝ := by
  refine list_prod_mem fun Q hQ => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hQ
  refine one_sub_smul_vecMulVec_mem_orthogonalGroup ?_
  rcases h p hp with h0 | h2
  · rw [h0, zero_mul]
  · rw [h2, sub_self, mul_zero]

/-- **The Householder vector `v^{(j)}` read from a factored-form array** ((5.1.3), §5.1.6): zeros
above position `j`, `1` at `j`, and the essential part `A(j+1:m, j)` below. -/
def storedHouseholderVec (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) : Fin m → ℝ :=
  fun i => if (i : ℕ) < j then 0 else if (i : ℕ) = j then 1 else A i j

/-- The stored vector vanishes above its position `j`. -/
theorem storedHouseholderVec_eq_zero (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) {i : Fin m}
    (hi : i ∉ indexFrom m j) : storedHouseholderVec A j i = 0 := by
  rw [mem_indexFrom, not_le] at hi
  simp [storedHouseholderVec, hi]

/-- **The reflector data of a factored-form array** ((5.1.3), §5.1.6: "the Householder vectors and
the corresponding `β_j`"): the vectors read from the array, with the `β` that the program
returned (convention 13). -/
def storedReflectors (A : Matrix (Fin m) (Fin n) ℝ) (β : Fin n → ℝ) :
    List ((Fin m → ℝ) × ℝ) :=
  List.ofFn fun j => (storedHouseholderVec A j, β j)

/-- **(5.1.3), the factored form** `Q = Q₁ Q₂ ⋯ Q_n`, `Q_j = I_m - β_j v^{(j)} v^{(j)ᵀ}`, with the
vectors stored in the array `A` and the given `β`. -/
noncomputable def factoredQ (β : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  householderProduct (storedReflectors A β)

/-- The factored form as a product over `Fin n` in order. -/
theorem factoredQ_eq_prod (β : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    factoredQ β A = ((List.finRange n).map fun j =>
      1 - β j • vecMulVec (storedHouseholderVec A j) (storedHouseholderVec A j)).prod := by
  simp only [factoredQ, householderProduct, storedReflectors, List.ofFn_eq_map, List.map_map]
  rfl

/-- **The `β` that (5.1.4), (5.1.5) and Algorithm 5.3.2 recompute from a stored vector**,
`β_j = 2 / v^{(j)ᵀ} v^{(j)}` (the book's `2/(1 + ‖A(j+1:m, j)‖₂²)`). It is the `β` that `house`
returned exactly when that was nonzero; when `house` returned `β = 0` it is `2`. -/
noncomputable def recomputedBeta (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) : ℝ :=
  2 / (storedHouseholderVec A j ⬝ᵥ storedHouseholderVec A j)

/-- `v^{(j)ᵀ} v^{(j)} = 1 + ‖A(j+1:m, j)‖₂²`, the sum along the index list of the essential part.
-/
theorem storedHouseholderVec_dotProduct_self (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n)
    (hj : (j : ℕ) < m) :
    storedHouseholderVec A j ⬝ᵥ storedHouseholderVec A j =
      1 + ((indexFrom m (j + 1)).map fun i =>
        storedHouseholderVec A j i * storedHouseholderVec A j i).sum := by
  set v := storedHouseholderVec A j with hv
  have hsplit : ∀ i, v i * v i =
      (if i = ⟨j, hj⟩ then 1 else 0) + (if (j : ℕ) + 1 ≤ i then v i * v i else 0) := by
    intro i
    by_cases hij : (i : ℕ) = j
    · have hi : i = ⟨j, hj⟩ := Fin.ext hij
      subst hi
      simp [hv, storedHouseholderVec]
    · have hne : i ≠ ⟨j, hj⟩ := fun e => hij (by rw [e])
      by_cases hlt : (i : ℕ) < j
      · have h1 : ¬ ((j : ℕ) + 1 ≤ i) := by omega
        simp [hv, storedHouseholderVec, hlt, hne, h1]
      · have h1 : (j : ℕ) + 1 ≤ i := by omega
        simp [hne, h1]
  have htail : ∑ i : Fin m, (if (j : ℕ) + 1 ≤ (i : ℕ) then v i * v i else 0) =
      ((indexFrom m (j + 1)).map fun i => v i * v i).sum := by
    rw [sum_eq_sum_map_of_nodup (nodup_indexFrom m (j + 1)) (fun i hi => by
      rw [mem_indexFrom] at hi; simp [hi])]
    congr 1
    exact List.map_congr_left fun i hi => by rw [mem_indexFrom] at hi; simp [hi]
  change ∑ i, v i * v i = _
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, Finset.sum_ite_eq', htail]
  simp only [Finset.mem_univ, ↓reduceIte]

/-- A loop premultiplying by symmetric matrices computes the transpose of their product:
`Q_{l_k} ⋯ Q_{l_1} C = (Q_{l_1} ⋯ Q_{l_k})ᵀ C`. -/
theorem foldl_mul_eq_transpose_prod_mul {α : Type} {p : ℕ} (Q : α → Matrix (Fin m) (Fin m) ℝ)
    (hQ : ∀ a, (Q a)ᵀ = Q a) (l : List α) (C : Matrix (Fin m) (Fin p) ℝ) :
    l.foldl (fun C a => Q a * C) C = ((l.map Q).prod)ᵀ * C := by
  induction l generalizing C with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, transpose_mul, hQ,
      Matrix.mul_assoc]

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **(5.1.4) as a program**: overwriting `C ∈ ℝ^{m×p}` with `Qᵀ C` from the factored form stored
in `A`:
```
for j = 1:n
    v(j:m) = [1; A(j+1:m, j)]
    β_j = 2/(1 + ‖A(j+1:m, j)‖₂²)
    C(j:m, :) = C(j:m, :) - (β_j v(j:m))(v(j:m)ᵀ C(j:m, :))
end
```
with the book's recomputation of `β_j` (a rounded dot product, `1 +`, a division) and the update
`householderApplyLeft` on the rows `j:m` and all columns. -/
noncomputable def factoredQTransposeMul {p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (C : Matrix (Fin m) (Fin p) ℝ) : M (Matrix (Fin m) (Fin p) ℝ) :=
  (List.finRange n).foldlM (fun (C : Matrix (Fin m) (Fin p) ℝ) j => do
    let v := storedHouseholderVec A j
    let s ← dotAccum rnd (indexFrom m (j + 1)) v v 0
    let β ← rnd (2 / (← rnd (1 + s)))
    householderApplyLeft rnd v β (indexFrom m j) (List.finRange p) C) C

/-- **(5.1.5) as a program**, backward accumulation of `Q(:, 1:k)` from the factored form stored
in `A`:
```
Q = I_m(:, 1:k)
for j = n:-1:1
    v(j:m) = [1; A(j+1:m, j)]
    β_j = 2/(1 + ‖A(j+1:m, j)‖₂²)
    Q(j:m, j:k) = Q(j:m, j:k) - (β_j v(j:m))(v(j:m)ᵀ Q(j:m, j:k))
end
```
(the columns `< j` of the partial product are still those of the identity, which the reflector
`Q_j` fixes). -/
noncomputable def factoredQFirstColumns (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    M (Matrix (Fin m) (Fin k) ℝ) :=
  (List.finRange n).reverse.foldlM (fun (Q : Matrix (Fin m) (Fin k) ℝ) j => do
    let v := storedHouseholderVec A j
    let s ← dotAccum rnd (indexFrom m (j + 1)) v v 0
    let β ← rnd (2 / (← rnd (1 + s)))
    householderApplyLeft rnd v β (indexFrom m j) (indexFrom k j) Q)
    (of fun i c => if (i : ℕ) = c then 1 else 0)

/-- **§5.1.6, forward accumulation** `Q = I; for j = 1:r, Q = Q Q_j` over reflector data. -/
def forwardAccumulation (data : List ((Fin m → ℝ) × ℝ)) : M (Matrix (Fin m) (Fin m) ℝ) :=
  data.foldlM (fun (Q : Matrix (Fin m) (Fin m) ℝ) p =>
    householderApplyRight rnd p.1 p.2 (List.finRange m) (List.finRange m) Q) 1

/-- **§5.1.6, backward accumulation** `Q = I; for j = r:-1:1, Q = Q_j Q` (the one the book
recommends), over reflector data. The symmetric twin of `forwardAccumulation` (convention 14). -/
def backwardAccumulation (data : List ((Fin m → ℝ) × ℝ)) : M (Matrix (Fin m) (Fin m) ℝ) :=
  data.reverse.foldlM (fun (Q : Matrix (Fin m) (Fin m) ℝ) p =>
    householderApplyLeft rnd p.1 p.2 (List.finRange m) (List.finRange m) Q) 1

end Programs

/-- The exact step of (5.1.4) and (5.1.5): the recomputed `β` is `recomputedBeta`. -/
private theorem recomputed_beta_eq (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n)
    (hj : (j : ℕ) < m) :
    2 / (1 + (0 + ((indexFrom m (j + 1)).map fun i =>
      storedHouseholderVec A j i * storedHouseholderVec A j i).sum)) = recomputedBeta A j := by
  rw [zero_add, recomputedBeta, storedHouseholderVec_dotProduct_self A j hj]

/-- **(5.1.4) computes `Qᵀ C`**, for the reflectors with the recomputed `β` (unconditionally; they
are the reflectors of the factorization exactly when no `β` returned by `house` was `0`). -/
theorem equation_5_1_4 {p : ℕ} (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ)
    (C : Matrix (Fin m) (Fin p) ℝ) :
    Id.run (factoredQTransposeMul pure A C) = (factoredQ (recomputedBeta A) A)ᵀ * C := by
  rw [factoredQ_eq_prod, ← foldl_mul_eq_transpose_prod_mul _
    (fun j => transpose_one_sub_smul_vecMulVec _ _), factoredQTransposeMul, List.idRun_foldlM]
  congr 1
  funext C j
  simp only [dotAccum_pure, pure_bind]
  rw [householderApplyLeft_spec_of_forall_mem (nodup_indexFrom m j) (List.nodup_finRange p)
    List.mem_finRange (fun i hi => storedHouseholderVec_eq_zero A j hi),
    recomputed_beta_eq A j (by omega)]

/-- A reflector with a vector vanishing at `c` fixes the `c`-th column of the identity block. -/
private theorem one_sub_smul_vecMulVec_mul_idCols_col {k : ℕ} {v : Fin m → ℝ} {β : ℝ}
    {X : Matrix (Fin m) (Fin k) ℝ} (c : Fin k)
    (hX : ∀ i, X i c = if (i : ℕ) = c then 1 else 0)
    (hv : ∀ i : Fin m, (i : ℕ) = c → v i = 0) (i : Fin m) :
    ((1 - β • vecMulVec v v : Matrix (Fin m) (Fin m) ℝ) * X) i c = X i c := by
  have hdot : v ⬝ᵥ (fun r => X r c) = 0 :=
    Finset.sum_eq_zero fun r _ => by
      change v r * X r c = 0
      rw [hX r]
      split_ifs with h
      · rw [hv r h, zero_mul]
      · rw [mul_zero]
  change ((1 - β • vecMulVec v v) *ᵥ fun r => X r c) i = X i c
  rw [one_sub_smul_vecMulVec_mulVec_apply, hdot, mul_zero, sub_zero]

/-- **(5.1.5) computes `Q(:, 1:k)`** for the reflectors with the recomputed `β`
(`k ≤ m`, `n ≤ m`): the restriction of each update to the columns `j:k` is exact because the
columns `< j` of the partial product `Q_{j+1} ⋯ Q_n I_m(:, 1:k)` are columns of the identity, which
`Q_j` fixes. -/
theorem equation_5_1_5 {k : ℕ} (hk : k ≤ m) (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (factoredQFirstColumns pure A k) =
      (factoredQ (recomputedBeta A) A).submatrix id (Fin.castLE hk) := by
  set Q : Fin n → Matrix (Fin m) (Fin m) ℝ := fun j =>
    1 - recomputedBeta A j • vecMulVec (storedHouseholderVec A j) (storedHouseholderVec A j)
    with hQ
  set I : Matrix (Fin m) (Fin k) ℝ := of fun i c => if (i : ℕ) = c then 1 else 0 with hI
  -- the exact step
  have hstep : ∀ (j : Fin n) (X : Matrix (Fin m) (Fin k) ℝ),
      Id.run (do
        let s ← dotAccum pure (indexFrom m (j + 1)) (storedHouseholderVec A j)
          (storedHouseholderVec A j) 0
        let β ← pure (2 / (← pure (1 + s)))
        householderApplyLeft pure (storedHouseholderVec A j) β (indexFrom m j) (indexFrom k j) X) =
        of fun i c => if c ∈ indexFrom k j then (Q j * X) i c else X i c := by
    intro j X
    simp only [dotAccum_pure, pure_bind]
    rw [householderApplyLeft_spec (nodup_indexFrom m j) (nodup_indexFrom k j)
      (fun i hi => storedHouseholderVec_eq_zero A j hi), recomputed_beta_eq A j (by omega)]
  -- the loop, as a right fold over the increasing list of indices
  have key : ∀ l : List (Fin n), l.Pairwise (· < ·) →
      l.foldr (fun (j : Fin n) (X : Matrix (Fin m) (Fin k) ℝ) =>
        of fun i c => if c ∈ indexFrom k j then (Q j * X) i c else X i c) I =
        (l.map Q).prod * I := by
    intro l hl
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.pairwise_cons] at hl
      rw [List.foldr_cons, ih hl.2, List.map_cons, List.prod_cons, Matrix.mul_assoc]
      ext i c
      rw [of_apply]
      split_ifs with hc
      · rfl
      · -- column `c < a`: every reflector of the product fixes it
        rw [mem_indexFrom, not_le] at hc
        have hfix : ∀ l' : List (Fin n), (∀ b ∈ l', a < b) →
            ∀ i, ((l'.map Q).prod * I) i c = I i c := by
          intro l' hl'
          induction l' with
          | nil => intro i; simp
          | cons b l' ih' =>
            intro i
            rw [List.map_cons, List.prod_cons, Matrix.mul_assoc,
              one_sub_smul_vecMulVec_mul_idCols_col c
                (fun r => ih' (fun b' hb' => hl' b' (List.mem_cons_of_mem _ hb')) r)
                (fun r hr => storedHouseholderVec_eq_zero A b (by
                  rw [mem_indexFrom, not_le, hr]
                  exact lt_trans hc (hl' b List.mem_cons_self)))]
            exact ih' (fun b' hb' => hl' b' (List.mem_cons_of_mem _ hb')) i
        rw [one_sub_smul_vecMulVec_mul_idCols_col c (hfix l hl.1)
          (fun r hr => storedHouseholderVec_eq_zero A a (by
            rw [mem_indexFrom, not_le, hr]; exact hc))]
  rw [factoredQFirstColumns, List.foldlM_reverse, List.idRun_foldrM]
  simp only [hstep]
  rw [key (List.finRange n) (List.sortedLT_finRange n).pairwise, factoredQ_eq_prod]
  ext i c
  simp only [Matrix.mul_apply, hI, of_apply, submatrix_apply, id]
  rw [Finset.sum_eq_single (Fin.castLE hk c)]
  · simp only [Fin.val_castLE, ↓reduceIte, mul_one]
    rfl
  · intro r _ hr
    have : ¬ ((r : ℕ) = c) := fun h => hr (Fin.ext h)
    simp [this]
  · simp

/-- **Forward accumulation computes `Q = Q₁ ⋯ Q_r`** of the reflector data. -/
theorem forwardAccumulation_spec (data : List ((Fin m → ℝ) × ℝ)) :
    Id.run (forwardAccumulation pure data) = householderProduct data := by
  have key : ∀ Q₀ : Matrix (Fin m) (Fin m) ℝ,
      Id.run (data.foldlM (fun (Q : Matrix (Fin m) (Fin m) ℝ) p =>
        householderApplyRight pure p.1 p.2 (List.finRange m) (List.finRange m) Q) Q₀) =
        Q₀ * householderProduct data := by
    induction data with
    | nil => intro Q₀; simp
    | cons p data ih =>
      intro Q₀
      rw [List.foldlM_cons]
      change Id.run (data.foldlM _ (Id.run (householderApplyRight pure p.1 p.2
        (List.finRange m) (List.finRange m) Q₀))) = _
      rw [ih, householderApplyRight_spec_of_forall_mem (List.nodup_finRange m)
        (List.nodup_finRange m) List.mem_finRange (fun j hj => absurd (List.mem_finRange j) hj),
        householderProduct_cons, Matrix.mul_assoc]
  rw [forwardAccumulation, key, Matrix.one_mul]

/-- **Backward accumulation computes `Q = Q₁ ⋯ Q_r`** of the reflector data. -/
theorem backwardAccumulation_spec (data : List ((Fin m → ℝ) × ℝ)) :
    Id.run (backwardAccumulation pure data) = householderProduct data := by
  have key : ∀ Q₀ : Matrix (Fin m) (Fin m) ℝ,
      Id.run (data.reverse.foldlM (fun (Q : Matrix (Fin m) (Fin m) ℝ) p =>
        householderApplyLeft pure p.1 p.2 (List.finRange m) (List.finRange m) Q) Q₀) =
        householderProduct data * Q₀ := by
    intro Q₀
    rw [List.idRun_foldlM, List.foldl_reverse]
    induction data with
    | nil => simp
    | cons p data ih =>
      rw [List.foldr_cons, ih, householderApplyLeft_spec_of_forall_mem (List.nodup_finRange m)
        (List.nodup_finRange m) List.mem_finRange (fun j hj => absurd (List.mem_finRange j) hj),
        householderProduct_cons, Matrix.mul_assoc]
  rw [backwardAccumulation, key, Matrix.mul_one]

end FactoredForm


/-! ### §5.1.7 The WY representation -/

section WY

variable {m : ℕ}

/-- The product of reflector data indexed by `Fin r` is the backbone's product
`List.ofFn fun j => 1 - β j • vecMulVec (v j) (star (v j))` over `ℝ`. -/
theorem householderProduct_ofFn {r : ℕ} (β : Fin r → ℝ) (v : Fin r → Fin m → ℝ) :
    householderProduct (List.ofFn fun j => (v j, β j)) =
      (List.ofFn fun j => 1 - β j • vecMulVec (v j) (star (v j))).prod := by
  simp [householderProduct, List.map_ofFn, Function.comp_def]

/-- **(5.1.6)**: a product `Q = Q₁ ⋯ Q_r` of rank-one modifications `Q_j = I - β_j v_j v_jᵀ` of the
identity (in particular of `r` Householder matrices) is a rank-`r` modification of the identity,
`Q = I_m - W Yᵀ` with `W, Y ∈ ℝ^{m×r}`. -/
theorem equation_5_1_6 {r : ℕ} (β : Fin r → ℝ) (v : Fin r → Fin m → ℝ) :
    ∃ W Y : Matrix (Fin m) (Fin r) ℝ,
      householderProduct (List.ofFn fun j => (v j, β j)) = 1 - W * Yᵀ := by
  refine ⟨wyW β v, of fun i j => v j i, ?_⟩
  rw [householderProduct_ofFn, ← conjTranspose_eq_transpose_of_trivial]
  exact isWY_prod β v

/-- **Lemma 5.1.1**: if `Q = I_m - W Yᵀ` with `W, Y ∈ ℝ^{m×j}`, `P = I_m - β v vᵀ` and `z = β Q v`,
then `Q₊ = Q P = I_m - W₊ Y₊ᵀ` with `W₊ = [W | z]`, `Y₊ = [Y | v]`. (The book assumes `Q`
orthogonal; the identity does not need it.) -/
theorem lemma_5_1_1 {j : ℕ} {Q : Matrix (Fin m) (Fin m) ℝ} {W Y : Matrix (Fin m) (Fin j) ℝ}
    (hQ : Q = 1 - W * Yᵀ) (β : ℝ) (v : Fin m → ℝ) :
    Q * (1 - β • vecMulVec v v) =
      1 - (of fun i => Fin.snoc (W i) ((β • (Q *ᵥ v)) i) : Matrix (Fin m) (Fin (j + 1)) ℝ) *
        (of fun i => Fin.snoc (Y i) (v i) : Matrix (Fin m) (Fin (j + 1)) ℝ)ᵀ := by
  have h : IsWY Q W Y := by rw [IsWY, conjTranspose_eq_transpose_of_trivial]; exact hQ
  have := h.mul_one_sub_smul_vecMulVec β v
  rw [IsWY, conjTranspose_eq_transpose_of_trivial, star_trivial] at this
  exact this

/-- One step of Algorithm 5.1.2: with `v = v⁽ʲ⁾`, `β = β_j` and the previous columns `k < j`,
`t = Y(:, 1:j-1)ᵀ v` (Algorithm 1.1.1 per column), `z = β (v - W(:, 1:j-1) t)` (an accumulation,
a subtraction and a scaling per entry, each rounded), then `W(:, j) = z`, `Y(:, j) = v`. -/
noncomputable def wyStep {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)
    (data : List ((Fin m → ℝ) × ℝ))
    (st : Matrix (Fin m) (Fin data.length) ℝ × Matrix (Fin m) (Fin data.length) ℝ)
    (j : Fin data.length) :
    M (Matrix (Fin m) (Fin data.length) ℝ × Matrix (Fin m) (Fin data.length) ℝ) := do
  let v := (data.get j).1
  let β := (data.get j).2
  let prev := (List.finRange data.length).filter (· < j)
  let t ← prev.foldlM (fun (t : Fin data.length → ℝ) k => do
    let d ← Chapter01.algorithm_1_1_1 rnd (fun i => st.2 i k) v
    pure (Function.update t k d)) 0
  let z ← (List.finRange m).foldlM (fun (z : Fin m → ℝ) i => do
    let wt ← dotAccum rnd prev (st.1 i) t 0
    let d ← rnd (v i - wt)
    let b ← rnd (β * d)
    pure (Function.update z i b)) 0
  pure (st.1.updateCol j z, st.2.updateCol j v)

/-- **Algorithm 5.1.2** (the WY representation from the factored form): for reflector data
`data = [(v⁽¹⁾, β₁), …, (v⁽ʳ⁾, β_r)]` (convention 13),
```
Y = v⁽¹⁾; W = β₁ v⁽¹⁾
for j = 2:r
    z = β_j (I_m - W Yᵀ) v⁽ʲ⁾
    W = [W | z];  Y = [Y | v⁽ʲ⁾]
end
```
`W`, `Y` are kept as `m × r` arrays whose not-yet-filled columns are zero, and column `j` is
written at step `j` (`wyStep`; the first step is the loop body with no previous columns). The
product `(I - W Yᵀ) v` is formed as `v - W (Yᵀ v)` over the previous columns. -/
noncomputable def algorithm_5_1_2 {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)
    (data : List ((Fin m → ℝ) × ℝ)) :
    M (Matrix (Fin m) (Fin data.length) ℝ × Matrix (Fin m) (Fin data.length) ℝ) :=
  (List.finRange data.length).foldlM (wyStep rnd data) (0, 0)

/-- A loop writing each listed entry from a value independent of the state writes the listed
entries and keeps the others. -/
theorem foldl_update_eq {ι β : Type*} [DecidableEq ι] (g : ι → β) (l : List ι) (y₀ : ι → β) :
    l.foldl (fun y k => Function.update y k (g k)) y₀ = fun k => if k ∈ l then g k else y₀ k := by
  induction l generalizing y₀ with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    funext k
    by_cases hk : k ∈ l
    · simp [hk]
    · by_cases hka : k = a
      · subst hka; simp [hk]
      · simp [hk, hka]

/-- The exact step of Algorithm 5.1.2, when the columns `≥ j` of `W` are zero:
`W(:, j) = β (I - W Yᵀ) v`, `Y(:, j) = v`. -/
private theorem wyStep_pure (data : List ((Fin m → ℝ) × ℝ))
    (W Y : Matrix (Fin m) (Fin data.length) ℝ) (j : Fin data.length)
    (hW : ∀ i (k : Fin data.length), j ≤ k → W i k = 0) :
    Id.run (wyStep pure data (W, Y) j) =
      (W.updateCol j ((data.get j).2 • ((1 - W * Yᵀ) *ᵥ (data.get j).1)),
        Y.updateCol j (data.get j).1) := by
  set v := (data.get j).1
  set β := (data.get j).2
  set prev := (List.finRange data.length).filter (· < j) with hprev
  simp only [wyStep, Id.run_bind, Id.run_pure, List.idRun_foldlM,
    Chapter01.algorithm_1_1_1_spec, dotAccum_id]
  rw [foldl_update_eq, foldl_update_eq]
  congr 2
  funext i
  simp only [List.mem_finRange, ↓reduceIte, zero_add, Pi.smul_apply, smul_eq_mul, sub_mulVec,
    one_mulVec, Pi.sub_apply, ← mulVec_mulVec]
  congr 2
  refine (sum_eq_sum_map_of_nodup ((List.nodup_finRange _).filter _)
    (f := fun k => W i k * (if k ∈ prev then (fun r => Y r k) ⬝ᵥ v
      else (0 : Fin data.length → ℝ) k)) fun k hk => ?_).symm.trans ?_
  · have hk' : k ∉ prev := hk
    simp only [hk', ↓reduceIte, Pi.zero_apply, mul_zero]
  · change _ = ∑ k, W i k * (Yᵀ *ᵥ v) k
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k ∈ prev
    · simp only [hk, ↓reduceIte]; rfl
    · simp only [hk, ↓reduceIte, Pi.zero_apply, mul_zero]
      rw [hW i k (by simpa [hprev] using hk), zero_mul]

/-- **Algorithm 5.1.2 computes the WY representation**: in exact arithmetic the output `(W, Y)`
satisfies `Q₁ ⋯ Q_r = I_m - W Yᵀ`, and the columns of `Y` are the Householder vectors ("`Y` is
merely the matrix of Householder vectors", so for vectors of the shape (5.1.3) it is unit lower
triangular). -/
theorem algorithm_5_1_2_spec (data : List ((Fin m → ℝ) × ℝ)) :
    householderProduct data =
        1 - (Id.run (algorithm_5_1_2 pure data)).1 * (Id.run (algorithm_5_1_2 pure data)).2ᵀ ∧
      ∀ i k, (Id.run (algorithm_5_1_2 pure data)).2 i k = (data.get k).1 i := by
  set R := data.length with hR
  set f := fun st j => Id.run (wyStep pure data st j) with hf
  -- the invariant after the first `j` steps
  set I : ℕ → Matrix (Fin m) (Fin R) ℝ × Matrix (Fin m) (Fin R) ℝ → Prop := fun j st =>
    (∀ i (k : Fin R), j ≤ k → st.1 i k = 0 ∧ st.2 i k = 0) ∧
      (∀ i (k : Fin R), (k : ℕ) < j → st.2 i k = (data.get k).1 i) ∧
      1 - st.1 * st.2ᵀ = householderProduct (data.take j) with hI
  have hstep : ∀ st (j : Fin R), I j st → I (j + 1) (f st j) := by
    rintro ⟨W, Y⟩ j ⟨hz, hY, hQ⟩
    simp only [hf]
    rw [wyStep_pure data W Y j fun i k hk => (hz i k hk).1]
    refine ⟨fun i k hk => ?_, fun i k hk => ?_, ?_⟩
    · have hkj : k ≠ j := fun e => by rw [e] at hk; omega
      simp only [updateCol_ne hkj]
      exact hz i k (by omega)
    · by_cases hkj : k = j
      · subst hkj; simp
      · simp only [updateCol_ne hkj]
        exact hY i k (by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
          · exact h
          · exact absurd (Fin.ext h) hkj)
    · have htake : data.take (j + 1) = data.take j ++ [data.get j] := by
        rw [List.take_succ_eq_append_getElem j.isLt]
        rfl
      rw [htake, householderProduct_concat, ← hQ]
      set v := (data.get j).1
      set β := (data.get j).2
      -- `W' Y'ᵀ = W Yᵀ + z vᵀ`, since column `j` of `W` and of `Y` is zero
      have hWY : (W.updateCol j (β • ((1 - W * Yᵀ) *ᵥ v))) * (Y.updateCol j v)ᵀ =
          W * Yᵀ + vecMulVec (β • ((1 - W * Yᵀ) *ᵥ v)) v := by
        ext a b
        simp only [Matrix.mul_apply, Matrix.add_apply, transpose_apply, updateCol_apply,
          vecMulVec_apply]
        have hpt : ∀ k, (if k = j then (β • ((1 - W * Yᵀ) *ᵥ v)) a else W a k) *
            (if k = j then v b else Y b k) =
              W a k * Y b k + if k = j then (β • ((1 - W * Yᵀ) *ᵥ v)) a * v b else 0 := by
          intro k
          by_cases hk : k = j
          · subst hk
            have h0 : W a k = 0 := (hz a k le_rfl).1
            simp [h0]
          · simp [hk]
        simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
          ↓reduceIte]
      rw [hWY, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, mul_vecMulVec, ← sub_sub,
        smul_vecMulVec]
  have hinit : I 0 (0, 0) := ⟨fun i k _ => ⟨rfl, rfl⟩, fun i k hk => absurd hk (Nat.not_lt_zero _),
    by simp⟩
  have hall : ∀ j ≤ R, I j (((List.finRange R).take j).foldl f (0, 0)) := by
    intro j
    induction j with
    | zero => intro _; simpa using hinit
    | succ j ih =>
      intro hj
      rw [List.take_succ_eq_append_getElem (by simpa using hj), List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have h := hstep _ ⟨j, by omega⟩ (ih (by omega))
      simpa using h
  obtain ⟨-, hY, hQ⟩ := hall R le_rfl
  rw [List.take_of_length_le (by simp)] at hY hQ
  have hprog : Id.run (algorithm_5_1_2 pure data) = (List.finRange R).foldl f (0, 0) := by
    rw [algorithm_5_1_2, List.idRun_foldlM]
  rw [hprog]
  rw [List.take_of_length_le (le_of_eq hR.symm)] at hQ
  exact ⟨hQ.symm, fun i k => hY i k k.2⟩

/-- **§5.1.7, block reflectors**: "True block reflectors have the form `Q = I - 2VVᵀ` where
`V ∈ ℝ^{n×r}` satisfies `VᵀV = I_r`" — such a `Q` is orthogonal. -/
theorem blockReflector_mem_orthogonalGroup {r : ℕ} {V : Matrix (Fin m) (Fin r) ℝ}
    (hV : Vᵀ * V = 1) : 1 - (2 : ℝ) • (V * Vᵀ) ∈ orthogonalGroup (Fin m) ℝ := by
  have := one_sub_two_mul_conjTranspose_mem_unitaryGroup (R := ℝ)
    (V := V) (by rwa [conjTranspose_eq_transpose_of_trivial])
  rwa [conjTranspose_eq_transpose_of_trivial] at this

end WY

/-! ### §5.1.8–5.1.10 Givens rotations -/

section Givens

variable {m n : ℕ}

/-- **(5.1.7), the Givens rotation** `G(i, k, θ)`: the identity except for `c` at `(i, i)` and
`(k, k)`, `s` at `(i, k)` and `-s` at `(k, i)`, with `c = cos θ`, `s = sin θ`. The backbone's
`Matrix.planeRotation i k c s` has rows `(c, -s)`, `(s, c)`, hence the sign. -/
def givensRotation (i k : Fin m) (c s : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  planeRotation i k c (-s)

/-- **§5.1.8, "Givens rotations are clearly orthogonal"** (`c² + s² = 1`, `i ≠ k`). -/
theorem givensRotation_mem_orthogonalGroup {i k : Fin m} (hik : i ≠ k) {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) : givensRotation i k c s ∈ orthogonalGroup (Fin m) ℝ :=
  planeRotation_mem_orthogonalGroup hik (by rwa [neg_sq])

/-- **§5.1.8, the action of `G(i, k, θ)ᵀ`**: `y = G(i, k, θ)ᵀ x` has `y_i = c x_i - s x_k`,
`y_k = s x_i + c x_k` and `y_j = x_j` otherwise. -/
theorem givensRotation_transpose_mulVec_apply {i k : Fin m} (hik : i ≠ k) (c s : ℝ)
    (x : Fin m → ℝ) (p : Fin m) :
    ((givensRotation i k c s)ᵀ *ᵥ x) p =
      if p = i then c * x i - s * x k else if p = k then s * x i + c * x k else x p := by
  rw [givensRotation, transpose_planeRotation_mulVec_apply hik]
  split_ifs <;> ring

/-- **(5.1.8)**: with `c = x_i / √(x_i² + x_k²)` and `s = -x_k / √(x_i² + x_k²)` (not both entries
zero), `y = G(i, k, θ)ᵀ x` has `y_k = 0` (and `y_i = √(x_i² + x_k²)`). -/
theorem equation_5_1_8 {i k : Fin m} (hik : i ≠ k) (x : Fin m → ℝ) (hx : x i ≠ 0 ∨ x k ≠ 0) :
    ((givensRotation i k (x i / √(x i ^ 2 + x k ^ 2)) (-x k / √(x i ^ 2 + x k ^ 2)))ᵀ *ᵥ x) k
        = 0 ∧
      ((givensRotation i k (x i / √(x i ^ 2 + x k ^ 2)) (-x k / √(x i ^ 2 + x k ^ 2)))ᵀ *ᵥ x) i
        = √(x i ^ 2 + x k ^ 2) := by
  have hpos : 0 < x i ^ 2 + x k ^ 2 := by
    rcases hx with h | h
    · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; positivity
    · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; positivity
  have hr : √(x i ^ 2 + x k ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have hsq := Real.sq_sqrt hpos.le
  rw [givensRotation_transpose_mulVec_apply hik, givensRotation_transpose_mulVec_apply hik,
    ite_eq_right hik.symm, ite_eq_left rfl, ite_eq_left rfl]
  constructor
  · field_simp
    ring
  · field_simp
    nlinarith [hsq, Real.sqrt_nonneg (x i ^ 2 + x k ^ 2)]

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 5.1.3 (`givens`)**: "Given scalars `a` and `b`, this function computes
`c = cos(θ)` and `s = sin(θ)` so `[c s; -s c]ᵀ [a; b] = [r; 0]`":
```
if b = 0:           c = 1; s = 0
elseif |b| > |a|:   τ = -a/b; s = 1/√(1 + τ²); c = s τ
else                τ = -b/a; c = 1/√(1 + τ²); s = c τ
```
The comparisons act on the inputs (convention 1); every arithmetic result is rounded. -/
noncomputable def algorithm_5_1_3 (a b : ℝ) : M (ℝ × ℝ) :=
  if b = 0 then pure (1, 0)
  else if |b| > |a| then do
    let τ ← rnd (-a / b)
    let s ← rnd (1 / (← rnd √(← rnd (1 + (← rnd (τ * τ))))))
    let c ← rnd (s * τ)
    pure (c, s)
  else do
    let τ ← rnd (-b / a)
    let c ← rnd (1 / (← rnd √(← rnd (1 + (← rnd (τ * τ))))))
    let s ← rnd (c * τ)
    pure (c, s)

/-- One computed rotation of the entries `i, k` of a vector (§5.1.9's loop body):
`x_i ← fl(fl(c x_i) - fl(s x_k))`, `x_k ← fl(fl(s x_i) + fl(c x_k))` from the old values. -/
def givensRotateVec {p : ℕ} (i k : Fin p) (c s : ℝ) (x : Fin p → ℝ) : M (Fin p → ℝ) := do
  let y₁ ← rnd ((← rnd (c * x i)) - (← rnd (s * x k)))
  let y₂ ← rnd ((← rnd (s * x i)) + (← rnd (c * x k)))
  pure (Function.update (Function.update x i y₁) k y₂)

/-- **§5.1.9, the row update** `A([i, k], cols) = G(i, k, θ)ᵀ A([i, k], cols)`, in place on the
full matrix (conventions 10, 13): for each `j ∈ cols`, `τ₁ = A(i, j)`, `τ₂ = A(k, j)`,
`A(i, j) = c τ₁ - s τ₂`, `A(k, j) = s τ₁ + c τ₂`, each product and sum rounded. -/
def givensApplyLeft (i k : Fin m) (c s : ℝ) (cols : List (Fin n))
    (A : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) :=
  cols.foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) q => do
    let y ← givensRotateVec rnd i k c s (fun r => A r q)
    pure (A.updateCol q y)) A

/-- **§5.1.9, the column update** `A(rows, [i, k]) = A(rows, [i, k]) G(i, k, θ)`: for each
`r ∈ rows`, `τ₁ = A(r, i)`, `τ₂ = A(r, k)`, `A(r, i) = c τ₁ - s τ₂`, `A(r, k) = s τ₁ + c τ₂`.
The symmetric twin of `givensApplyLeft` (convention 14). -/
def givensApplyRight (i k : Fin n) (c s : ℝ) (rows : List (Fin m))
    (A : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) :=
  rows.foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) r => do
    let y ← givensRotateVec rnd i k c s (A r)
    pure (A.updateRow r y)) A

end Programs

variable {fp : RoundingModel ℝ}

/-- **The bridge of `givens`** (convention 12): every run `(ĉ, ŝ)` of Algorithm 5.1.3 is a computed
pair `FloatingPoint.RoundsGivensPair` of the `τ`-formula. -/
theorem algorithm_5_1_3_rounds (a b : ℝ) {cs : ℝ × ℝ}
    (h : cs ∈ (algorithm_5_1_3 fp.round a b).run) : RoundsGivensPair fp a b cs.1 cs.2 := by
  unfold algorithm_5_1_3 at h
  split_ifs at h with hb hab
  · rw [SetM.mem_run_pure] at h
    subst h
    exact Or.inl ⟨hb, rfl, rfl⟩
  · simp only [SetM.mem_run_bind, RoundingModel.mem_run_round, SetM.mem_run_pure] at h
    obtain ⟨τ, hτ, t₁, h₁, t₂, h₂, r, hr, s, hs, c, hc, rfl⟩ := h
    exact Or.inr (Or.inl ⟨hab, τ, t₁, t₂, r, hτ, h₁, h₂, hr, hs, hc⟩)
  · simp only [SetM.mem_run_bind, RoundingModel.mem_run_round, SetM.mem_run_pure] at h
    obtain ⟨τ, hτ, t₁, h₁, t₂, h₂, r, hr, c, hc, s, hs, rfl⟩ := h
    exact Or.inr (Or.inr ⟨hb, not_lt.1 hab, τ, t₁, t₂, r, hτ, h₁, h₂, hr, hc, hs⟩)

private theorem algorithm_5_1_3_mem_exact (a b : ℝ) :
    Id.run (algorithm_5_1_3 pure a b) ∈
      (algorithm_5_1_3 (RoundingModel.exact ℝ).round a b).run := by
  rw [RoundingModel.round_exact]
  unfold algorithm_5_1_3
  split_ifs <;> simp only [pure_bind, SetM.mem_run_pure] <;> rfl

/-- **Algorithm 5.1.3, exact semantics**: the output `(c, s)` satisfies `c² + s² = 1` and
`[c s; -s c]ᵀ [a; b] = [r; 0]`, i.e. `s a + c b = 0`, with `r = c a - s b` of absolute value
`√(a² + b²)` (the sign of `r` is not controlled, P5.1.11). -/
theorem algorithm_5_1_3_spec (a b : ℝ) :
    (Id.run (algorithm_5_1_3 pure a b)).1 ^ 2 + (Id.run (algorithm_5_1_3 pure a b)).2 ^ 2 = 1 ∧
      (Id.run (algorithm_5_1_3 pure a b)).2 * a + (Id.run (algorithm_5_1_3 pure a b)).1 * b = 0 ∧
      |(Id.run (algorithm_5_1_3 pure a b)).1 * a - (Id.run (algorithm_5_1_3 pure a b)).2 * b| =
        √(a ^ 2 + b ^ 2) := by
  have h := algorithm_5_1_3_rounds a b (algorithm_5_1_3_mem_exact a b)
  obtain ⟨c, s, hcs, hz, hc, hs⟩ := h.exists_isRelPert (by simp)
  rw [RoundingModel.exact_u] at hc hs
  rw [eq_of_isRelPert_zero hc, eq_of_isRelPert_zero hs]
  refine ⟨hcs, hz, ?_⟩
  rw [← Real.sqrt_sq_eq_abs]
  congr 1
  linear_combination (a ^ 2 + b ^ 2) * hcs - (s * a + c * b) * hz

/-- **§5.1.10, "the computed `ĉ`, `ŝ` satisfy `ĉ = c(1 + ε_c)`, `ŝ = s(1 + ε_s)`, `ε = O(u)`"**,
rigorous: for `13 u < 1`, every run `(ĉ, ŝ)` of Algorithm 5.1.3 has an exact rotation `(c, s)`,
`c² + s² = 1`, `s a + c b = 0`, of which it is a relative perturbation of order `13`. -/
theorem algorithm_5_1_3_rounding (hu : ((13 : ℕ) : ℝ) * fp.u < 1) (a b : ℝ) {cs : ℝ × ℝ}
    (h : cs ∈ (algorithm_5_1_3 fp.round a b).run) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ s * a + c * b = 0 ∧ IsRelPert fp.u 13 c cs.1 ∧
      IsRelPert fp.u 13 s cs.2 :=
  (algorithm_5_1_3_rounds a b h).exists_isRelPert hu

/-- The bridge of one computed rotation of two entries. -/
theorem givensRotateVec_rounds {p : ℕ} {i k : Fin p} (hik : i ≠ k) {c s : ℝ} {x y : Fin p → ℝ}
    (h : y ∈ (givensRotateVec fp.round i k c s x).run) : RoundsGivensApply fp c s i k x y := by
  simp only [givensRotateVec, SetM.mem_run_bind, RoundingModel.mem_run_round,
    SetM.mem_run_pure] at h
  obtain ⟨p₁, hp₁, q₁, hq₁, y₁, hy₁, p₂, hp₂, q₂, hq₂, y₂, hy₂, rfl⟩ := h
  refine ⟨⟨p₁, q₁, hp₁, hq₁, ?_⟩, ⟨p₂, q₂, hp₂, hq₂, ?_⟩, fun l hli hlk => ?_⟩
  · rwa [Function.update_of_ne hik, Function.update_self]
  · rwa [Function.update_self]
  · rw [Function.update_of_ne hlk, Function.update_of_ne hli]

/-- In the exact model a computed rotation is the exact one. -/
theorem eq_of_roundsGivensApply_exact {p : ℕ} {i k : Fin p} {c s : ℝ} {x y : Fin p → ℝ}
    (h : RoundsGivensApply (RoundingModel.exact ℝ) c s i k x y) :
    y i = c * x i - s * x k ∧ y k = s * x i + c * x k ∧ ∀ l, l ≠ i → l ≠ k → y l = x l := by
  obtain ⟨⟨p₁, q₁, hp₁, hq₁, h₁⟩, ⟨p₂, q₂, hp₂, hq₂, h₂⟩, h₃⟩ := h
  simp only [RoundingModel.exact_rounds_iff] at hp₁ hq₁ h₁ hp₂ hq₂ h₂
  exact ⟨by rw [h₁, hp₁, hq₁], by rw [h₂, hp₂, hq₂], h₃⟩

/-- **The bridge of the row update** (convention 12): for `i ≠ k` and a duplicate-free column
list, every run `B` of `givensApplyLeft fp.round i k c s cols A` agrees with `A` off the listed
columns and off the rows `i, k`, and on the listed columns it is a computed row update
`FloatingPoint.RoundsGivensRowUpdate` of `A`. -/
theorem givensApplyLeft_rounds {i k : Fin m} (hik : i ≠ k) (c s : ℝ) {cols : List (Fin n)}
    (hcols : cols.Nodup) (A : Matrix (Fin m) (Fin n) ℝ) {B : Matrix (Fin m) (Fin n) ℝ}
    (h : B ∈ (givensApplyLeft fp.round i k c s cols A).run) :
    (∀ r q, q ∉ cols → B r q = A r q) ∧ (∀ r q, r ≠ i → r ≠ k → B r q = A r q) ∧
      RoundsGivensRowUpdate fp c s i k (A.submatrix id (Subtype.val : {q // q ∈ cols} → Fin n))
        (B.submatrix id (Subtype.val : {q // q ∈ cols} → Fin n)) := by
  obtain ⟨hout, hin⟩ := (mem_run_foldlM_updateCol_of_nodup
    (fun _ a => givensRotateVec fp.round i k c s a) hcols A B).1 h
  refine ⟨fun r q hq => hout q hq r, fun r q hri hrk => ?_, fun q =>
    givensRotateVec_rounds hik (hin q q.2)⟩
  by_cases hq : q ∈ cols
  · exact (givensRotateVec_rounds hik (hin q hq)).2.2 r hri hrk
  · exact hout q hq r

/-- **The bridge of the column update**, rowwise: every run `B` of
`givensApplyRight fp.round i k c s rows A` agrees with `A` off the listed rows and off the columns
`i, k`, and on the listed rows it is a computed column update
`FloatingPoint.RoundsGivensColUpdate` of `A`. -/
theorem givensApplyRight_rounds {i k : Fin n} (hik : i ≠ k) (c s : ℝ) {rows : List (Fin m)}
    (hrows : rows.Nodup) (A : Matrix (Fin m) (Fin n) ℝ) {B : Matrix (Fin m) (Fin n) ℝ}
    (h : B ∈ (givensApplyRight fp.round i k c s rows A).run) :
    (∀ r q, r ∉ rows → B r q = A r q) ∧ (∀ r q, q ≠ i → q ≠ k → B r q = A r q) ∧
      RoundsGivensColUpdate fp c s i k (A.submatrix (Subtype.val : {r // r ∈ rows} → Fin m) id)
        (B.submatrix (Subtype.val : {r // r ∈ rows} → Fin m) id) := by
  obtain ⟨hout, hin⟩ := (mem_run_foldlM_updateRow_of_nodup
    (fun _ a => givensRotateVec fp.round i k c s a) hrows A B).1 h
  refine ⟨fun r q hr => congrFun (hout r hr) q, fun r q hqi hqk => ?_, fun r =>
    givensRotateVec_rounds hik (hin r r.2)⟩
  by_cases hr : r ∈ rows
  · exact (givensRotateVec_rounds hik (hin r hr)).2.2 q hqi hqk
  · exact congrFun (hout r hr) q

private theorem givensApplyLeft_mem_exact (i k : Fin m) (c s : ℝ) (cols : List (Fin n))
    (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (givensApplyLeft pure i k c s cols A) ∈
      (givensApplyLeft (RoundingModel.exact ℝ).round i k c s cols A).run := by
  rw [RoundingModel.round_exact]
  simp only [givensApplyLeft, givensRotateVec, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

private theorem givensApplyRight_mem_exact (i k : Fin n) (c s : ℝ) (rows : List (Fin m))
    (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (givensApplyRight pure i k c s rows A) ∈
      (givensApplyRight (RoundingModel.exact ℝ).round i k c s rows A).run := by
  rw [RoundingModel.round_exact]
  simp only [givensApplyRight, givensRotateVec, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

/-- **Exact semantics of the row update** (read off the bridge at the exact model, convention 11):
for `i ≠ k` and a duplicate-free column list, the result is `G(i, k, θ)ᵀ A` in the listed columns
and `A` elsewhere. -/
theorem givensApplyLeft_spec {i k : Fin m} (hik : i ≠ k) (c s : ℝ) {cols : List (Fin n)}
    (hcols : cols.Nodup) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (givensApplyLeft pure i k c s cols A) =
      of fun r q => if q ∈ cols then ((givensRotation i k c s)ᵀ * A) r q else A r q := by
  obtain ⟨hout, -, hin⟩ := givensApplyLeft_rounds hik c s hcols A
    (givensApplyLeft_mem_exact i k c s cols A)
  ext r q
  rw [of_apply]
  split_ifs with hq
  · obtain ⟨h1, h2, h3⟩ := eq_of_roundsGivensApply_exact (hin ⟨q, hq⟩)
    have hG : ((givensRotation i k c s)ᵀ * A) r q =
        ((givensRotation i k c s)ᵀ *ᵥ fun p => A p q) r := rfl
    rw [hG, givensRotation_transpose_mulVec_apply hik]
    simp only [submatrix_apply, id] at h1 h2 h3
    split_ifs with hri hrk
    · subst hri; exact h1
    · subst hrk; exact h2
    · exact h3 r hri hrk
  · exact hout r q hq

/-- The row update on all columns is `G(i, k, θ)ᵀ A`. -/
theorem givensApplyLeft_spec_of_forall_mem {i k : Fin m} (hik : i ≠ k) (c s : ℝ)
    {cols : List (Fin n)} (hcols : cols.Nodup) (hall : ∀ q, q ∈ cols)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (givensApplyLeft pure i k c s cols A) = (givensRotation i k c s)ᵀ * A := by
  rw [givensApplyLeft_spec hik c s hcols]
  ext r q
  simp [hall q]

/-- **Exact semantics of the column update**: for `i ≠ k` and a duplicate-free row list, the
result is `A G(i, k, θ)` in the listed rows and `A` elsewhere. -/
theorem givensApplyRight_spec {i k : Fin n} (hik : i ≠ k) (c s : ℝ) {rows : List (Fin m)}
    (hrows : rows.Nodup) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (givensApplyRight pure i k c s rows A) =
      of fun r q => if r ∈ rows then (A * givensRotation i k c s) r q else A r q := by
  obtain ⟨hout, -, hin⟩ := givensApplyRight_rounds hik c s hrows A
    (givensApplyRight_mem_exact i k c s rows A)
  ext r q
  rw [of_apply]
  split_ifs with hr
  · obtain ⟨h1, h2, h3⟩ := eq_of_roundsGivensApply_exact (hin ⟨r, hr⟩)
    have hG : (A * givensRotation i k c s) r q = ((givensRotation i k c s)ᵀ *ᵥ A r) q := by
      rw [mulVec_transpose]; rfl
    rw [hG, givensRotation_transpose_mulVec_apply hik]
    simp only [submatrix_apply, id] at h1 h2 h3
    split_ifs with hqi hqk
    · subst hqi; exact h1
    · subst hqk; exact h2
    · exact h3 q hqi hqk
  · exact hout r q hr

/-- The column update on all rows is `A G(i, k, θ)`. -/
theorem givensApplyRight_spec_of_forall_mem {i k : Fin n} (hik : i ≠ k) (c s : ℝ)
    {rows : List (Fin m)} (hrows : rows.Nodup) (hall : ∀ r, r ∈ rows)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (givensApplyRight pure i k c s rows A) = A * givensRotation i k c s := by
  rw [givensApplyRight_spec hik c s hrows]
  ext r q
  simp [hall r]

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **§5.1.10, "`fl[Ĝ(i,k,θ)ᵀ A] = G(i,k,θ)ᵀ (A + E)`, `‖E‖₂ ≈ u ‖A‖₂`"**, rigorous: if the computed
`(ĉ, ŝ)` are relative perturbations of order `K` of an exact `(c, s)` with `c² + s² = 1` and
`(K + 2) u < 1`, every run `B` of `givensApplyLeft fp.round i k ĉ ŝ cols A` agrees with `A` off the
listed columns, and on them `‖B(:, q) - G(i,k,θ)ᵀ A(:, q)‖₂ ≤ √2 γ_{K+2} ‖A(:, q)‖₂` for every
column and `‖B - Gᵀ A‖_F ≤ √2 γ_{K+2} ‖A‖_F` (so `E = G B - A` has the same bounds). With the data
of `algorithm_5_1_3_rounding` (`K = 13`) the constant is `√2 γ₁₅`. -/
theorem givensApplyLeft_rounding {K : ℕ} (hu : ((K + 2 : ℕ) : ℝ) * fp.u < 1) {i k : Fin m}
    (hik : i ≠ k) {c s chat shat : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hc : IsRelPert fp.u K c chat)
    (hs : IsRelPert fp.u K s shat) {cols : List (Fin n)} (hcols : cols.Nodup)
    (A : Matrix (Fin m) (Fin n) ℝ) {B : Matrix (Fin m) (Fin n) ℝ}
    (h : B ∈ (givensApplyLeft fp.round i k chat shat cols A).run) :
    (∀ r q, q ∉ cols → B r q = A r q) ∧
      (∀ q, ‖(toLp 2 ((B.submatrix id (Subtype.val : {q // q ∈ cols} → Fin n) -
          (givensRotation i k c s)ᵀ * A.submatrix id Subtype.val).col q) :
            EuclideanSpace ℝ (Fin m))‖ ≤
        √2 * gamma fp.u (K + 2) *
          ‖(toLp 2 ((A.submatrix id (Subtype.val : {q // q ∈ cols} → Fin n)).col q) :
            EuclideanSpace ℝ (Fin m))‖) ∧
      ‖B.submatrix id (Subtype.val : {q // q ∈ cols} → Fin n) -
          (givensRotation i k c s)ᵀ * A.submatrix id Subtype.val‖ ≤
        √2 * gamma fp.u (K + 2) * ‖A.submatrix id (Subtype.val : {q // q ∈ cols} → Fin n)‖ := by
  obtain ⟨hout, -, hrel⟩ := givensApplyLeft_rounds hik chat shat hcols A h
  exact ⟨hout, hrel.col_norm_sub_le hu hik hcs hc hs, hrel.frobenius_norm_sub_le hu hik hcs hc hs⟩

/-- **§5.1.10, the column form** `fl[A Ĝ(i,k,θ)] = (A + E) G(i,k,θ)`, rigorous: under the
hypotheses of `givensApplyLeft_rounding`, every run `B` of
`givensApplyRight fp.round i k ĉ ŝ rows A` agrees with `A` off the listed rows, and on them
`‖B(r, :) - A(r, :) G‖₂ ≤ √2 γ_{K+2} ‖A(r, :)‖₂` for every row and
`‖B - A G‖_F ≤ √2 γ_{K+2} ‖A‖_F`. -/
theorem givensApplyRight_rounding {K : ℕ} (hu : ((K + 2 : ℕ) : ℝ) * fp.u < 1) {i k : Fin n}
    (hik : i ≠ k) {c s chat shat : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hc : IsRelPert fp.u K c chat)
    (hs : IsRelPert fp.u K s shat) {rows : List (Fin m)} (hrows : rows.Nodup)
    (A : Matrix (Fin m) (Fin n) ℝ) {B : Matrix (Fin m) (Fin n) ℝ}
    (h : B ∈ (givensApplyRight fp.round i k chat shat rows A).run) :
    (∀ r q, r ∉ rows → B r q = A r q) ∧
      (∀ r, ‖(toLp 2 ((B.submatrix (Subtype.val : {r // r ∈ rows} → Fin m) id -
          A.submatrix Subtype.val id * givensRotation i k c s).row r) :
            EuclideanSpace ℝ (Fin n))‖ ≤
        √2 * gamma fp.u (K + 2) *
          ‖(toLp 2 ((A.submatrix (Subtype.val : {r // r ∈ rows} → Fin m) id).row r) :
            EuclideanSpace ℝ (Fin n))‖) ∧
      ‖B.submatrix (Subtype.val : {r // r ∈ rows} → Fin m) id -
          A.submatrix Subtype.val id * givensRotation i k c s‖ ≤
        √2 * gamma fp.u (K + 2) * ‖A.submatrix (Subtype.val : {r // r ∈ rows} → Fin m) id‖ := by
  obtain ⟨hout, -, hrel⟩ := givensApplyRight_rounds hik chat shat hrows A h
  exact ⟨hout, hrel.row_norm_sub_le hu hik hcs hc hs, hrel.frobenius_norm_sub_le hu hik hcs hc hs⟩

end Frobenius

end Givens

/-! ### §5.1.11 Representing products of Givens rotations -/

section Encoding

/-- **(5.1.9), Stewart's encoding** of `Z = [c s; -s c]` by one number:
`ρ = 1` if `c = 0`; `ρ = sign(c) s / 2` if `|s| < |c|`; `ρ = 2 sign(s) / c` otherwise. -/
noncomputable def rotationCode (c s : ℝ) : ℝ :=
  if c = 0 then 1 else if |s| < |c| then Real.sign c * s / 2 else 2 * Real.sign s / c

/-- **(5.1.10), the reconstruction**: `(c, s) = (0, 1)` if `ρ = 1`; `s = 2ρ`, `c = √(1 - s²)` if
`|ρ| < 1`; `c = 2/ρ`, `s = √(1 - c²)` otherwise. -/
noncomputable def rotationDecode (ρ : ℝ) : ℝ × ℝ :=
  if ρ = 1 then (0, 1)
  else if |ρ| < 1 then (√(1 - (2 * ρ) ^ 2), 2 * ρ) else (2 / ρ, √(1 - (2 / ρ) ^ 2))

/-- **§5.1.11, "it is possible to reconstruct `Z` (or `-Z`)"**: for `c² + s² = 1`, decoding the
code of `(c, s)` gives `(c, s)` or `(-c, -s)`. -/
theorem rotationDecode_rotationCode {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    rotationDecode (rotationCode c s) = (c, s) ∨ rotationDecode (rotationCode c s) = (-c, -s) := by
  have hs1 : |s| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg c]
  unfold rotationCode
  by_cases hc : c = 0
  · subst hc
    have : s = 1 ∨ s = -1 := by
      have h : (s - 1) * (s + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 h with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rw [ite_eq_left rfl, rotationDecode, ite_eq_left rfl]
    rcases this with rfl | rfl
    · left; rfl
    · right; simp
  rw [ite_eq_right hc]
  by_cases hsc : |s| < |c|
  · rw [ite_eq_left hsc]
    have hρ : |Real.sign c * s / 2| < 1 := by
      rw [abs_div, abs_mul, abs_two]
      rcases Real.sign_apply_eq_of_ne_zero c hc with h | h <;> rw [h] <;> simp <;> linarith
    have hρ1 : Real.sign c * s / 2 ≠ 1 := fun e => by rw [e] at hρ; simp at hρ
    rw [rotationDecode, ite_eq_right hρ1, ite_eq_left hρ]
    have hsq : 1 - (2 * (Real.sign c * s / 2)) ^ 2 = c ^ 2 := by
      rcases Real.sign_apply_eq_of_ne_zero c hc with h | h <;> rw [h] <;> linarith
    rw [hsq, Real.sqrt_sq_eq_abs]
    rcases lt_or_gt_of_ne hc with h | h
    · right; rw [Real.sign_of_neg h, abs_of_neg h]; ext <;> simp; ring
    · left; rw [Real.sign_of_pos h, abs_of_pos h]; ext <;> simp; ring
  · rw [ite_eq_right hsc]
    have hs0 : s ≠ 0 := fun e => by
      rw [e, abs_zero] at hsc; exact hsc (abs_pos.2 hc)
    have hcle : c ^ 2 ≤ 1 / 2 := by
      have := not_lt.1 hsc
      have h2 : c ^ 2 ≤ s ^ 2 := by rw [← sq_abs c, ← sq_abs s]; gcongr
      linarith
    have hc1 : |c| < 1 := by
      rw [← sq_lt_one_iff_abs_lt_one]; linarith
    have hρabs : |2 * Real.sign s / c| = 2 / |c| := by
      rw [abs_div, abs_mul, abs_two]
      rcases Real.sign_apply_eq_of_ne_zero s hs0 with h | h <;> rw [h] <;> simp
    have hcpos : 0 < |c| := abs_pos.2 hc
    have hρ : ¬ |2 * Real.sign s / c| < 1 := by
      rw [hρabs, div_lt_one hcpos]; linarith
    have hρ1 : 2 * Real.sign s / c ≠ 1 := fun e => by
      have h := hρabs
      rw [e, abs_one, eq_div_iff hcpos.ne'] at h
      linarith
    rw [rotationDecode, ite_eq_right hρ1, ite_eq_right hρ]
    have hinv : 2 / (2 * Real.sign s / c) = Real.sign s * c := by
      rcases Real.sign_apply_eq_of_ne_zero s hs0 with h | h <;> rw [h] <;> field_simp
    rw [hinv]
    have hsq : 1 - (Real.sign s * c) ^ 2 = s ^ 2 := by
      rcases Real.sign_apply_eq_of_ne_zero s hs0 with h | h <;> rw [h] <;> linarith
    rw [hsq, Real.sqrt_sq_eq_abs]
    rcases lt_or_gt_of_ne hs0 with h | h
    · right; rw [Real.sign_of_neg h, abs_of_neg h]; ext <;> simp
    · left; rw [Real.sign_of_pos h, abs_of_pos h]; ext <;> simp

end Encoding

/-! ### §5.1.12 Error propagation -/

section ErrorPropagation

open scoped Matrix.Norms.L2Operator

variable {m n : ℕ}

/-- **§5.1.12, orthogonal to working precision**: `Q̂` is orthogonal to working precision `ε` if
there is an orthogonal `Q` with `‖Q̂ - Q‖₂ ≤ ε` (the book's `‖Q̂ - Q‖ = O(u)`, with the `O(u)` an
explicit parameter). -/
def orthogonalToWorkingPrecision (ε : ℝ) (Qhat : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∃ Q ∈ orthogonalGroup (Fin m) ℝ, ‖Qhat - Q‖ ≤ ε

/-- **§5.1.12, "A corollary of this is that `‖Q̂ᵀQ̂ - I_m‖ = O(u)`"**: `‖Q̂ᵀQ̂ - I‖₂ ≤ 2ε + ε²`. -/
theorem orthogonalToWorkingPrecision_transpose_mul_self {ε : ℝ}
    {Qhat : Matrix (Fin m) (Fin m) ℝ} (h : orthogonalToWorkingPrecision ε Qhat) :
    ‖Qhatᵀ * Qhat - 1‖ ≤ 2 * ε + ε ^ 2 := by
  obtain ⟨Q, hQ, hε⟩ := h
  exact l2_opNorm_transpose_mul_self_sub_one_le hQ hε

/-- **§5.1.12, "The matrices defined by the floating point output of … givens are orthogonal to
working precision"**: for `13 u < 1`, `i ≠ k` and a run `(ĉ, ŝ)` of Algorithm 5.1.3, the rotation
`G(i, k)` built from `(ĉ, ŝ)` is orthogonal to working precision `γ₁₃`. -/
theorem givensRotation_orthogonalToWorkingPrecision {fp : RoundingModel ℝ}
    (hu : ((13 : ℕ) : ℝ) * fp.u < 1) {i k : Fin m} (hik : i ≠ k) (a b : ℝ) {cs : ℝ × ℝ}
    (h : cs ∈ (algorithm_5_1_3 fp.round a b).run) :
    orthogonalToWorkingPrecision (gamma fp.u 13) (givensRotation i k cs.1 cs.2) := by
  obtain ⟨c, s, hcs, -, hc, hs⟩ := algorithm_5_1_3_rounding hu a b h
  exact ⟨givensRotation i k c s, givensRotation_mem_orthogonalGroup hik hcs,
    l2_opNorm_planeRotation_sub_le (gamma_nonneg fp.u_nonneg hu) hik hcs hc hs⟩

/-- **§5.1.12, the `house` half**: the Householder matrix of a run of Algorithm 5.1.1 is orthogonal
to working precision `8 γ_K`, `K = 18 (k + 1) + 31`. -/
theorem householderMatrix_orthogonalToWorkingPrecision {fp : RoundingModel ℝ} {k : ℕ}
    (hfp : fp.IsIdempotent) (hu : ((18 * (k + 1) + 31 : ℕ) : ℝ) * fp.u < 1)
    (x : Fin (k + 1) → ℝ) {vβ : (Fin (k + 1) → ℝ) × ℝ}
    (h : vβ ∈ (algorithm_5_1_1 fp.round x).run) :
    orthogonalToWorkingPrecision (8 * gamma fp.u (18 * (k + 1) + 31))
      (householderMatrix vβ.1) := by
  obtain ⟨v, -, -, -, -, hle⟩ := householderMatrix_computed_sub_le hfp hu x h
  exact ⟨householderMatrix v, householderMatrix_mem_orthogonalGroup v, hle⟩

end ErrorPropagation

section Accumulation

open scoped Matrix.Norms.Frobenius

variable {m n : ℕ}

/-- **(5.1.11), rigorous.** Let `A₀ = A ∈ ℝ^{m×n}` and `A₁, …, A_p = B` be generated by computed
two-sided orthogonal updates: at each step there are orthogonal `Q_k`, `Z_k` (the exact
transformations determined by the *computed* data — the only reading under which the claim holds)
with `‖A_{k+1} - Q_k A_k Z_k‖_F ≤ ε ‖A_k‖_F` (the per-step bounds of
`householderApplyLeft/Right_rounding` and `givensApplyLeft/Right_rounding`, with `Z_k = I` or
`Q_k = I`). If `p ε < 1`, then `B = (Q_p ⋯ Q_1)(A + E)(Z_1 ⋯ Z_p)` with `‖E‖_F ≤ γ_p(ε) ‖A‖_F` and
`‖E‖₂ ≤ √(min(m, n)) γ_p(ε) ‖A‖₂`: the book's `‖E‖₂ ≤ c u ‖A‖₂`, `c` depending mildly on `m`,
`n`, `p`. -/
theorem equation_5_1_11 {Q : ℕ → Matrix (Fin m) (Fin m) ℝ} {Z : ℕ → Matrix (Fin n) (Fin n) ℝ}
    (hQ : ∀ k, Q k ∈ orthogonalGroup (Fin m) ℝ) (hZ : ∀ k, Z k ∈ orthogonalGroup (Fin n) ℝ)
    {A : ℕ → Matrix (Fin m) (Fin n) ℝ} {ε : ℝ} (hε : 0 ≤ ε) {p : ℕ} (hp : (p : ℝ) * ε < 1)
    (hA : ∀ k, k < p → ‖A (k + 1) - Q k * A k * Z k‖ ≤ ε * ‖A k‖) :
    ∃ E : Matrix (Fin m) (Fin n) ℝ, A p = prodRev Q p * (A 0 + E) * prodFwd Z p ∧
      ‖E‖ ≤ gamma ε p * ‖A 0‖ ∧
      lpOpNorm 2 E ≤ √(min m n : ℕ) * gamma ε p * lpOpNorm 2 (A 0) := by
  obtain ⟨E, h1, h2⟩ := exists_eq_prodRev_mul_add_mul_prodFwd_rect hQ hZ hε p hA
  have hg := one_add_pow_sub_one_le_gamma hε hp
  have hg0 := gamma_nonneg hε hp
  have hF : ‖E‖ ≤ gamma ε p * ‖A 0‖ := h2.trans (mul_le_mul_of_nonneg_right hg (norm_nonneg _))
  refine ⟨E, h1, hF, ?_⟩
  have hrank : √((A 0).rank : ℝ) ≤ √(min m n : ℕ) :=
    Real.sqrt_le_sqrt (Nat.cast_le.2 (le_min (rank_le_height _) (rank_le_width _)))
  calc lpOpNorm 2 E ≤ ‖E‖ := l2_opNorm_le_frobenius_norm E
    _ ≤ gamma ε p * ‖A 0‖ := hF
    _ ≤ gamma ε p * (√((A 0).rank : ℝ) * lpOpNorm 2 (A 0)) :=
        mul_le_mul_of_nonneg_left (frobenius_norm_le_sqrt_rank_mul_l2_opNorm _) hg0
    _ ≤ gamma ε p * (√(min m n : ℕ) * lpOpNorm 2 (A 0)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrank (lpOpNorm_nonneg 2 _)) hg0
    _ = √(min m n : ℕ) * gamma ε p * lpOpNorm 2 (A 0) := by ring

end Accumulation

/-! ### §5.1.13 The complex case -/

section Complex

open Complex

variable {m : ℕ}

/-- **§5.1.13, the complex Householder transformation**: for `x ∈ ℂ^m` with `x₁ = r e^{iθ}`
(`e^{iθ}` is `Matrix.phase x₁`, `1` at `x₁ = 0`) and `v = x ± e^{iθ} ‖x‖₂ e₁ ≠ 0`, the matrix
`P = I - (2 / vᴴv) v vᴴ` (`Matrix.reflector v`) is unitary and `P x = ∓ e^{iθ} ‖x‖₂ e₁`. -/
theorem complexHouseholder (x : Fin (m + 1) → ℂ) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hv : x + ((σ : ℂ) * phase (x 0) * (‖(toLp 2 x : EuclideanSpace ℂ (Fin (m + 1)))‖ : ℂ)) •
      Pi.single 0 1 ≠ 0) :
    reflector (x + ((σ : ℂ) * phase (x 0) *
        (‖(toLp 2 x : EuclideanSpace ℂ (Fin (m + 1)))‖ : ℂ)) • Pi.single 0 1) ∈
        unitaryGroup (Fin (m + 1)) ℂ ∧
      reflector (x + ((σ : ℂ) * phase (x 0) *
          (‖(toLp 2 x : EuclideanSpace ℂ (Fin (m + 1)))‖ : ℂ)) • Pi.single 0 1) *ᵥ x =
        -((σ : ℂ) * phase (x 0) * (‖(toLp 2 x : EuclideanSpace ℂ (Fin (m + 1)))‖ : ℂ)) •
          Pi.single 0 1 := by
  refine ⟨reflector_mem_unitaryGroup _, reflector_mulVec_eq_of_sq ?_ ?_ hv⟩
  · set N : ℝ := ‖(toLp 2 x : EuclideanSpace ℂ (Fin (m + 1)))‖
    have hph : starRingEnd ℂ (phase (x 0)) * phase (x 0) = 1 := by
      rw [RCLike.conj_mul, norm_phase]; simp
    have hσ2 : (σ : ℂ) ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
    calc star ((σ : ℂ) * phase (x 0) * (N : ℂ)) * ((σ : ℂ) * phase (x 0) * (N : ℂ))
        = (σ : ℂ) ^ 2 * (starRingEnd ℂ (phase (x 0)) * phase (x 0)) * (N : ℂ) ^ 2 := by
          simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
          ring
      _ = (N : ℂ) ^ 2 := by rw [hph, hσ2]; ring
  · have h : star ((σ : ℂ) * phase (x 0) *
        (‖(toLp 2 x : EuclideanSpace ℂ (Fin (m + 1)))‖ : ℂ)) * x 0 =
        ((σ * ‖(toLp 2 x : EuclideanSpace ℂ (Fin (m + 1)))‖ * ‖x 0‖ : ℝ) : ℂ) := by
      have := conj_phase_mul_self (x 0)
      simp only [star_mul', Complex.star_def, Complex.conj_ofReal] at this ⊢
      push_cast
      linear_combination ((σ : ℂ) * (‖(toLp 2 x : EuclideanSpace ℂ (Fin (m + 1)))‖ : ℂ)) * this
    rw [h, Complex.star_def, Complex.conj_ofReal]

/-- **§5.1.13, complex Givens rotations**: "it is easy to verify that a 2-by-2 matrix of the form
`Q = [cos θ, sin θ e^{iφ}; -sin θ e^{-iφ}, cos θ]` is unitary" — for real `c` and complex `s`
with `c² + |s|² = 1`, `[c s; -s̄ c]` is unitary, and so is its embedding in the plane `(i, k)` of
`ℂ^{m×m}`. -/
theorem complexGivens_mem_unitaryGroup {c : ℝ} {s : ℂ} (h : c ^ 2 + ‖s‖ ^ 2 = 1) :
    !![(c : ℂ), s; -starRingEnd ℂ s, (c : ℂ)] ∈ unitaryGroup (Fin 2) ℂ ∧
      ∀ {i k : Fin m}, i ≠ k →
        planeEmbed i k !![(c : ℂ), s; -starRingEnd ℂ s, (c : ℂ)] ∈ unitaryGroup (Fin m) ℂ := by
  have hs : s * starRingEnd ℂ s = ((‖s‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.mul_conj]; push_cast; rfl
  have hG : !![(c : ℂ), s; -starRingEnd ℂ s, (c : ℂ)] ∈ unitaryGroup (Fin 2) ℂ := by
    rw [mem_unitaryGroup_iff]
    have hc : (c : ℂ) ^ 2 + ((‖s‖ ^ 2 : ℝ) : ℂ) = 1 := by exact_mod_cast h
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, star_apply, of_apply, cons_val',
        cons_val_zero, cons_val_one, cons_val_fin_one, Fin.isValue, Fin.zero_eta, Fin.mk_one,
        one_apply_eq, one_apply_ne, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true,
        RCLike.star_def, Complex.conj_ofReal, map_neg, Complex.conj_conj] <;>
      first | ring1 | linear_combination hc + hs
  exact ⟨hG, fun hik => (planeEmbed_mem_unitaryGroup_iff _ hik).2 hG⟩

/-- **(5.1.12), a complex Givens rotation from three real ones**: for `u = u₁ + i u₂`,
`v = v₁ + i v₂`, let `givens` (Algorithm 5.1.3, exact) give `(c_α, s_α)` for `(u₁, u₂)` with
`r_u = c_α u₁ - s_α u₂`, `(c_β, s_β)` for `(v₁, v₂)` with `r_v`, and `(c_θ, s_θ)` for
`(r_u, r_v)`; set `e^{iφ} = (c_α c_β + s_α s_β) + i (c_α s_β - c_β s_α)`, `c = c_θ`,
`s = s_θ e^{iφ}`. Then `[c s; -s̄ c]ᴴ [u; v] = [r; 0]`, i.e. `s̄ u + c v = 0`. -/
theorem equation_5_1_12 (u v : ℂ) {cα sα cβ sβ cθ sθ : ℝ}
    (hgα : Id.run (algorithm_5_1_3 pure u.re u.im) = (cα, sα))
    (hgβ : Id.run (algorithm_5_1_3 pure v.re v.im) = (cβ, sβ))
    (hgθ : Id.run (algorithm_5_1_3 pure (cα * u.re - sα * u.im) (cβ * v.re - sβ * v.im)) =
      (cθ, sθ)) :
    starRingEnd ℂ ((sθ : ℂ) * ⟨cα * cβ + sα * sβ, cα * sβ - cβ * sα⟩) * u + (cθ : ℂ) * v = 0 := by
  have hα' := algorithm_5_1_3_spec u.re u.im
  have hβ' := algorithm_5_1_3_spec v.re v.im
  rw [hgα] at hα'
  rw [hgβ] at hβ'
  obtain ⟨hα, hαz, -⟩ := hα'
  obtain ⟨hβ, hβz, -⟩ := hβ'
  simp only at hα hαz hβ hβz
  set ru := cα * u.re - sα * u.im
  set rv := cβ * v.re - sβ * v.im
  have hθ' := algorithm_5_1_3_spec ru rv
  rw [hgθ] at hθ'
  obtain ⟨-, hθ, -⟩ := hθ'
  simp only at hθ
  -- `u = r_u e^{-iα}`, `v = r_v e^{-iβ}`
  have hu : u = (ru : ℂ) * ⟨cα, -sα⟩ := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, ru]
      linear_combination (-u.re) * hα + sα * hαz
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, ru]
      linear_combination (-u.im) * hα + cα * hαz
  have hv : v = (rv : ℂ) * ⟨cβ, -sβ⟩ := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, rv]
      linear_combination (-v.re) * hβ + sβ * hβz
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, rv]
      linear_combination (-v.im) * hβ + cβ * hβz
  -- `e^{-iφ} e^{-iα} = e^{-iβ}`
  have hconj : starRingEnd ℂ (⟨cα * cβ + sα * sβ, cα * sβ - cβ * sα⟩ : ℂ) * ⟨cα, -sα⟩ =
      ⟨cβ, -sβ⟩ := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      linear_combination cβ * hα
    · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      linear_combination (-sβ) * hα
  have hθc : (sθ : ℂ) * (ru : ℂ) + (cθ : ℂ) * (rv : ℂ) = 0 := by exact_mod_cast hθ
  rw [hu, hv, map_mul, Complex.conj_ofReal]
  linear_combination ((sθ : ℂ) * (ru : ℂ)) * hconj + (⟨cβ, -sβ⟩ : ℂ) * hθc

end Complex

end GolubVanLoan.Chapter05
