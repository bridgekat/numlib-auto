import Numlib.Surface.FongSaunders.Sec3

/-!
# §4: the exact relations behind the numerical comparison

Surface file for D. C.-L. Fong and M. A. Saunders, *CG versus MINRES: an empirical
comparison*, SQU Journal for Science **17** (2012) 44–62 (Report SOL 2011-2R).

§4 is mostly an experimental study; the material with mathematical content is formalized here:
the FOM/GMRES-type relation (4.1) between the CG and MINRES residual norms, the telescoping
product of residual ratios of §4.1.1, and the description of the MINRES iterate as the solution
of a least-squares subproblem in Lanczos coordinates (§4.2).

Left out (see `tracker/fongsaunders.md`): the test set, the diagonal preconditioning, the
figures and the percentages of monotone steps, the "cumulative minimum" heuristic, and the
MINRES-QLP relationship.

The two indefinite-case results of §4.2 (Steihaug's theorem for CG and its CR analogue) are
*deferred*: they rest on strict, symmetric-indefinite monotonicity statements that the backbone
does not yet provide (`tracker/backbone.md` §3.11, "Steihaug's generalization", phase 2), and the
surface layer may not invent them.
-/

namespace FongSaunders

open Krylov Matrix

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : Vec n}

private theorem cr_res (k : ℕ) : b - Matrix.toEuclideanLin A (cr A b k).x = (cr A b k).r :=
  (cr_residual_eq k).symm

private theorem cg_res (k : ℕ) : b - Matrix.toEuclideanLin A (cg A b k).x = (cg A b k).r :=
  (cg_residual_eq k).symm

/-! ### R4.1: equation (4.1) -/

/-- (4.1): `‖r_k^C‖ = ‖r_k^M‖ / √(1 − ‖r_k^M‖²/‖r_{k−1}^M‖²)` (Greenbaum Lemma 5.4.1 /
Titley-Péloquin), for `k ≥ 1` and `r_k^M ≠ 0`.  It is the harmonic identity
`1/‖r_{k}^M‖² = 1/‖r_{k-1}^M‖² + 1/‖r_k^C‖²` of `Numlib/Krylov/Relations.lean` rearranged. -/
theorem equation_4_1 (hA : A.PosDef) (k : ℕ) (hk : (cr A b (k + 1)).r ≠ 0) :
    ‖(cg A b (k + 1)).r‖
      = ‖(cr A b (k + 1)).r‖ /
        Real.sqrt (1 - ‖(cr A b (k + 1)).r‖ ^ 2 / ‖(cr A b k).r‖ ^ 2) := by
  have hG := isMinresIterate_iff.1 (cr_isMinresIterate (b := b) hA k)
  have hG' := isMinresIterate_iff.1 (cr_isMinresIterate (b := b) hA (k + 1))
  have hF := cg_isGalerkinIterate (b := b) hA (k + 1)
  have h0 : b - Matrix.toEuclideanLin A (cr A b (k + 1)).x ≠ 0 := by rw [cr_res]; exact hk
  have key := Krylov.inv_sq_norm_residual_minRes hG hG' hF h0
  rw [cr_res, cr_res, cg_res] at key
  have hMle : ‖(cr A b (k + 1)).r‖ ≤ ‖(cr A b k).r‖ := by
    have h := Krylov.IsMinResIterate.norm_residual_antitone
      (x := fun j => (cr A b j).x)
      (fun j => isMinresIterate_iff.1 (cr_isMinresIterate hA j)) (Nat.le_succ k)
    simp only at h
    rwa [cr_res, cr_res] at h
  have hMC : ‖(cr A b (k + 1)).r‖ ≤ ‖(cg A b (k + 1)).r‖ := by
    have h := Krylov.norm_residual_minRes_le_galerkin hG' hF
    rwa [cr_res, cg_res] at h
  have hM : 0 < ‖(cr A b (k + 1)).r‖ := norm_pos_iff.2 hk
  have hM0 : 0 < ‖(cr A b k).r‖ := lt_of_lt_of_le hM hMle
  have hC : 0 < ‖(cg A b (k + 1)).r‖ := lt_of_lt_of_le hM hMC
  have hMne : ‖(cr A b (k + 1)).r‖ ≠ 0 := hM.ne'
  have hM0ne : ‖(cr A b k).r‖ ≠ 0 := hM0.ne'
  have hCne : ‖(cg A b (k + 1)).r‖ ≠ 0 := hC.ne'
  have hval : 1 - ‖(cr A b (k + 1)).r‖ ^ 2 / ‖(cr A b k).r‖ ^ 2
      = (‖(cr A b (k + 1)).r‖ / ‖(cg A b (k + 1)).r‖) ^ 2 := by
    rw [div_pow]
    field_simp at key ⊢
    linarith
  rw [hval, Real.sqrt_sq (by positivity)]
  field_simp

/-- (4.1) for an arbitrary sequence of MINRES iterates, whose residual is `r_k^M = b − A x_k`. -/
theorem equation_4_1_minres (hA : A.PosDef) {x : ℕ → Vec n} (hx : ∀ k, IsMinresIterate A b k (x k))
    (k : ℕ) (hk : b - A ⬝ x (k + 1) ≠ 0) :
    ‖(cg A b (k + 1)).r‖
      = ‖b - A ⬝ x (k + 1)‖ /
        Real.sqrt (1 - ‖b - A ⬝ x (k + 1)‖ ^ 2 / ‖b - A ⬝ x k‖ ^ 2) := by
  have hres : ∀ j, b - A ⬝ x j = (cr A b j).r := fun j => by
    rw [(isMinresIterate_iff_eq_cr hA j (x j)).1 (hx j), ← cr_residual_eq]
  rw [hres] at hk
  rw [hres, hres]
  exact equation_4_1 hA k hk

/-! ### R4.2: the telescoping product of residual ratios (§4.1.1) -/

/-- §4.1.1: if the residuals `r_0 = b, r_1, …, r_{l−1}` are nonzero then
`∏_{k=1}^{l} ‖r_k‖/‖r_{k−1}‖ = ‖r_l‖/‖b‖`.  (The hypothesis `b ≠ 0` is automatic for `l ≥ 1`;
it is stated so that the degenerate case `l = 0` is also covered.) -/
theorem prod_ratio_residual (r : ℕ → Vec n) (hb : b ≠ 0) (hr0 : r 0 = b) (l : ℕ)
    (hne : ∀ k < l, r k ≠ 0) :
    ∏ k ∈ Finset.range l, ‖r (k + 1)‖ / ‖r k‖ = ‖r l‖ / ‖b‖ := by
  induction l with
  | zero => simp [hr0, div_self (norm_ne_zero_iff.2 hb)]
  | succ l ih =>
    have hl : ‖r l‖ ≠ 0 := norm_ne_zero_iff.2 (hne l (Nat.lt_succ_self l))
    rw [Finset.prod_range_succ, ih fun k hk => hne k (by omega)]
    field_simp

/-! ### R4.5: the MINRES subproblem in Lanczos coordinates (§4.2) -/

/-- For symmetric `A` the Arnoldi Hessenberg matrix is the Lanczos matrix `T̲_k`. -/
theorem hessenberg_eq_lanczosT (hA : A.IsSymm) (k : ℕ) :
    Arnoldi.hessenberg (Matrix.toEuclideanLin A) b k = lanczosT A b k := by
  rw [Lanczos.hessenberg_eq_map_tridiagExt b (isSymmetric_toEuclideanLin hA) k]
  ext i j
  simp

/-- §4.2: `x_k^M = V_k y_k^M` where `y_k^M` minimizes `‖T̲_k y − β_1 e_1‖` (`β_1 = ‖b‖`). -/
theorem minres_subproblem (hA : A.PosDef) (k : ℕ) (hk : k ≤ lanczosTerm A b) (y : Fin k → ℝ) :
    IsMinresIterate A b k (∑ j, y j • lanczosVec A b j) ↔
      IsMinOn (fun z : Fin k → ℝ =>
        ‖(WithLp.toLp 2 (Krylov.firstVec ‖b‖ (k + 1) - (lanczosT A b k).mulVec z) :
          Vec (k + 1))‖) Set.univ y := by
  have hK := Krylov.isMinResIterate_iff_isMinOn (A := Matrix.toEuclideanLin A) (b := b) (x₀ := 0)
    (m := k) (by rwa [sub_mulVecE_zero]) y
  rw [sub_mulVecE_zero, hessenberg_eq_lanczosT (isSymm_of_posDef hA),
    RCLike.ofReal_real_eq_id, id_eq] at hK
  rw [isMinresIterate_iff, ← hK, zero_add]

/-- §4.2: for `k ≤ ℓ` the coordinate vector `y_k^M` of the MINRES iterate is unique. -/
theorem minres_coeff_unique (hA : A.PosDef) (k : ℕ) (hk : k ≤ lanczosTerm A b) :
    ∃! y : Fin k → ℝ, IsMinresIterate A b k (∑ j, y j • lanczosVec A b j) := by
  have hinj : Function.Injective fun j : Fin k => (⟨(j : ℕ), lt_of_lt_of_le j.2 hk⟩ :
      Fin (lanczosTerm A b)) := by
    intro i j hij
    simpa [Fin.ext_iff] using hij
  have horth : Orthonormal ℝ fun j : Fin k => lanczosVec A b (j : ℕ) :=
    (lanczosVec_orthonormal A b).comp
      (fun j : Fin k => (⟨(j : ℕ), lt_of_lt_of_le j.2 hk⟩ : Fin (lanczosTerm A b))) hinj
  have hli := horth.linearIndependent
  obtain ⟨x, hx⟩ := Krylov.exists_isMinResIterate (Matrix.toEuclideanLin A) b 0 k
  obtain ⟨y, hy⟩ := (mem_krylov_iff_exists_lanczos A b k x).1
    (sub_zero_mem_subspace_iff.1 hx.mem)
  have hxy : IsMinresIterate A b k (∑ j, y j • lanczosVec A b (j : ℕ)) := by
    rw [← hy]; exact isMinresIterate_iff.2 hx
  refine ⟨y, hxy, fun z hz => ?_⟩
  have heq : ∑ j, z j • lanczosVec A b (j : ℕ) = ∑ j, y j • lanczosVec A b (j : ℕ) :=
    isMinresIterate_unique hA hz hxy
  have hzero : ∑ j, (z - y) j • lanczosVec A b (j : ℕ) = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, heq, sub_self]
  funext j
  have := Fintype.linearIndependent_iff.1 hli (z - y) hzero j
  simpa [sub_eq_zero] using this

end FongSaunders
