import Numlib.Krylov.Arnoldi
import Numlib.Krylov.Hessenberg
import Numlib.Krylov.Iterate
import Numlib.Krylov.Lanczos
import Numlib.Krylov.Relations
import Numlib.Krylov.Subspace
import Numlib.LinearSolve.Projection.Basic
import NumlibSurface.FongSaunders.Section03

/-!
# Fong–Saunders §4: the exact relations behind the numerical comparison

Surface file for D. C.-L. Fong and M. A. Saunders, *CG versus MINRES: an empirical comparison*, SQU
Journal for Science **17** (2012) 44–62 (Report SOL 2011-2R), §4.

§4 is mostly an experimental study; the material with mathematical content is formalized here:
the FOM/GMRES-type relation (4.1) between the CG and MINRES residual norms, the telescoping
product of residual ratios of §4.1.1, and the description of the MINRES iterate as the solution
of a least-squares subproblem in Lanczos coordinates (§4.2).

Left out, as empirical or as the results of other papers: the test set, the diagonal
preconditioning, the figures and the percentages of monotone steps, the "cumulative minimum"
heuristic, and the MINRES-QLP relationship, whose missing ingredient is the QLP factorization
`R_k P_k = L_k` and belongs in `Numlib/Krylov/Singular` rather than in this surface.

The two indefinite-case results of §4.2 (Steihaug's theorem for CG and its CR analogue) are
`steihaug_cg` and `steihaug_cr`, specializations of the backbone's strict, symmetric-indefinite
monotonicity theorems `CG.norm_iterate_lt_of_re_inner_apply_direction_pos` and
`CR.norm_iterate_lt_of_pos`.  The latter carries its positivity hypothesis up to the termination
index rather than up to `k`, for the reason explained at `steihaug_cr` below.
-/

namespace FongSaunders

open Krylov Matrix

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : Vec n}

/-- `b − A x_k = r_k` for CR, in the unfolded shape the backbone's residual lemmas produce. -/
private theorem cr_res (k : ℕ) : b - Matrix.toEuclideanLin A (cr A b k).x = (cr A b k).r :=
  (cr_residual_eq k).symm

/-- `b − A x_k = r_k` for CG, in the unfolded shape the backbone's residual lemmas produce. -/
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
  have hG := isMINRESIterate_iff.1 (cr_isMINRESIterate (b := b) hA k)
  have hG' := isMINRESIterate_iff.1 (cr_isMINRESIterate (b := b) hA (k + 1))
  have hF := cg_isGalerkinIterate (b := b) hA (k + 1)
  have h0 : b - Matrix.toEuclideanLin A (cr A b (k + 1)).x ≠ 0 := by rw [cr_res]; exact hk
  have key := Krylov.inv_sq_norm_residual_minRes hG hG' hF h0
  rw [cr_res, cr_res, cg_res] at key
  have hMle : ‖(cr A b (k + 1)).r‖ ≤ ‖(cr A b k).r‖ := by
    have h := Krylov.IsMinResidualIterate.norm_residual_antitone
      (x := fun j => (cr A b j).x)
      (fun j => isMINRESIterate_iff.1 (cr_isMINRESIterate hA j)) (Nat.le_succ k)
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
theorem equation_4_1_minres (hA : A.PosDef) {x : ℕ → Vec n} (hx : ∀ k, IsMINRESIterate A b k (x k))
    (k : ℕ) (hk : b - A ⬝ x (k + 1) ≠ 0) :
    ‖(cg A b (k + 1)).r‖
      = ‖b - A ⬝ x (k + 1)‖ /
        Real.sqrt (1 - ‖b - A ⬝ x (k + 1)‖ ^ 2 / ‖b - A ⬝ x k‖ ^ 2) := by
  have hres : ∀ j, b - A ⬝ x j = (cr A b j).r := fun j => by
    rw [(isMINRESIterate_iff_eq_cr hA j (x j)).1 (hx j), ← cr_residual_eq]
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
    IsMINRESIterate A b k (∑ j, y j • lanczosVec A b j) ↔
      IsMinOn (fun z : Fin k → ℝ =>
        ‖(WithLp.toLp 2 (Krylov.firstVec ‖b‖ (k + 1) - (lanczosT A b k).mulVec z) :
          Vec (k + 1))‖) Set.univ y := by
  have hK := Krylov.isMinResidualIterate_iff_isMinOn (A := Matrix.toEuclideanLin A) (b := b) (x₀ := 0)
    (m := k) (by rwa [sub_mulVecE_zero]) y
  rw [sub_mulVecE_zero, hessenberg_eq_lanczosT (isSymm_of_posDef hA),
    RCLike.ofReal_real_eq_id, id_eq] at hK
  rw [isMINRESIterate_iff, ← hK, zero_add]

/-- §4.2: for `k ≤ ℓ` the coordinate vector `y_k^M` of the MINRES iterate is unique. -/
theorem minres_coeff_unique (hA : A.PosDef) (k : ℕ) (hk : k ≤ lanczosTerm A b) :
    ∃! y : Fin k → ℝ, IsMINRESIterate A b k (∑ j, y j • lanczosVec A b j) := by
  have hinj : Function.Injective fun j : Fin k => (⟨(j : ℕ), lt_of_lt_of_le j.2 hk⟩ :
      Fin (lanczosTerm A b)) := by
    intro i j hij
    simpa [Fin.ext_iff] using hij
  have horth : Orthonormal ℝ fun j : Fin k => lanczosVec A b (j : ℕ) :=
    (lanczosVec_orthonormal A b).comp
      (fun j : Fin k => (⟨(j : ℕ), lt_of_lt_of_le j.2 hk⟩ : Fin (lanczosTerm A b))) hinj
  have hli := horth.linearIndependent
  obtain ⟨x, hx⟩ := Krylov.exists_isMinResidualIterate (Matrix.toEuclideanLin A) b 0 k
  obtain ⟨y, hy⟩ := (mem_krylov_iff_exists_lanczos A b k x).1
    (sub_zero_mem_subspace_iff.1 hx.mem)
  have hxy : IsMINRESIterate A b k (∑ j, y j • lanczosVec A b (j : ℕ)) := by
    rw [← hy]; exact isMINRESIterate_iff.2 hx
  refine ⟨y, hxy, fun z hz => ?_⟩
  have heq : ∑ j, z j • lanczosVec A b (j : ℕ) = ∑ j, y j • lanczosVec A b (j : ℕ) :=
    isMINRESIterate_unique hA hz hxy
  have hzero : ∑ j, (z - y) j • lanczosVec A b (j : ℕ) = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, heq, sub_self]
  funext j
  have := Fintype.linearIndependent_iff.1 hli (z - y) hzero j
  simpa [sub_eq_zero] using this

/-! ### R4.3, R4.4: Steihaug's theorem on indefinite systems (§4.2) -/

/-- §4.2, Steihaug's theorem: for CG on a symmetric, possibly indefinite `A x = b` from `x₀ = 0`,
the solution norms `‖x₁‖, …, ‖x_k‖` are strictly increasing as long as `p_jᵀ A p_j > 0` for the
directions `p₀, …, p_{k-1}` used in iterations `1..k`. -/
theorem steihaug_cg (hA : A.IsSymm) {k : ℕ}
    (hpos : ∀ j < k, 0 < ⟪(cg A b j).p, A ⬝ (cg A b j).p⟫_ℝ) {i : ℕ} (hi : i < k) :
    ‖(cg A b i).x‖ < ‖(cg A b (i + 1)).x‖ := by
  simp only [cg_x]
  refine CG.norm_iterate_lt_of_re_inner_apply_direction_pos b (isSymmetric_toEuclideanLin hA)
    (fun j hj => ?_) hi
  rw [RCLike.re_to_real, real_inner_comm]
  simpa only [cg_p] using hpos j hj

/-- §4.2, the CR/MINRES analogue of Steihaug's theorem: the CR solution norms are strictly
increasing as long as `ρ_j = r_jᵀ A r_j > 0` at every iteration before termination.

The paper states the property "as long as both `p_jᵀ A p_j > 0` and `r_jᵀ A r_j > 0` for all
iterations `1 ≤ j ≤ k`", a *local* hypothesis.  Its proof of Theorem 2.2 (d) expands `r_i` over
*all* the remaining steps, so a single negative `ρ_m` beyond `k` breaks the argument; the
hypothesis is therefore imposed up to the termination index `ℓ = crTerm A b`, which is how the
paper's condition reads when it is read globally.  The second condition `p_jᵀ A p_j > 0` is then
redundant, since `r_jᵀ A p_j = ρ_j ≠ 0` already forces `A p_j ≠ 0` (see
`CR.norm_iterate_lt_of_pos`).  Under these hypotheses `CR.isMinResidualIterate_of_no_breakdown`
identifies `x_k` with the MINRES iterate, so the property transfers to MINRES. -/
theorem steihaug_cr (hA : A.IsSymm) (hpos : ∀ j < crTerm A b, 0 < (cr A b j).ρ) {i : ℕ}
    (hi : i < crTerm A b) : ‖(cr A b i).x‖ < ‖(cr A b (i + 1)).x‖ := by
  have hne : {k | (cr A b k).r = 0}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [crTerm, h, Nat.sInf_empty] at hi
    exact Nat.not_lt_zero i hi
  have hstop : (CR.iterate (toEuclideanLin A) b 0 (crTerm A b)).r = 0 := by
    rw [← cr_r]; exact Nat.sInf_mem hne
  simp only [cr_x]
  refine CR.norm_iterate_lt_of_pos b (isSymmetric_toEuclideanLin hA) hstop (fun j hj => ?_) hi
  rw [RCLike.re_to_real]
  simpa only [cr_rho, cr_r] using hpos j hj

end FongSaunders
