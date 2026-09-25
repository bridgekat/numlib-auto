import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Numlib.Analysis.InnerProductSpace.Projection.Gap
import Numlib.Analysis.Normed.Operator.QuadraticEquation
import Numlib.Eigen.PowerMethod
import Numlib.LinearAlgebra.Matrix.Sylvester

/-!
# Invariant subspaces: uniqueness, perturbation, and subspace iteration

Invariant subspaces of a matrix or operator: their uniqueness for a set of eigenvalues, their
perturbation (Stewart's theorem), the transport of graph subspaces by powers, and the convergence of
subspace (orthogonal) iteration to the dominant one with explicit constants.

## Main results

* **Uniqueness.** An `A`-invariant subspace on which `A` has only eigenvalues from a set `Λ`, of the
  dimension of `⨆_{μ ∈ Λ} maxGenEigenspace A μ` (the total algebraic multiplicity of `Λ`), *is* that
  subspace (`Module.End.invtSubmodule_eq_iSup_maxGenEigenspace`). That is the precise sense of
  [golub2013matrix]'s "the unique invariant subspace associated with the eigenvalues λ₁, …, λ_r"
  (§7.3.2, the dominant invariant subspace `D_r(A)`, and §7.6.2, the first `p` Schur vectors when
  `λ(T₁₁) ∩ λ(T₂₂) = ∅`); the matrix form is `Matrix.span_cols_eq_iSup_maxGenEigenspace_of_conj`.
* **Powers from a Schur form** ([golub2013matrix] Lemma 7.3.2): with `Qᴴ A Q = D + N`,
  `‖A^k‖₂ ≤ (1+μ)^{n-1} (max |t_ii| + ‖N‖_F/(1+μ))^k` (`Matrix.l2_opNorm_pow_le_of_schur`) and the
  inverse-power bound (`Matrix.l2_opNorm_inv_pow_le_of_schur`); the diagonal scaling
  `Δ = diag(1, 1+μ, …, (1+μ)^{n-1})` shrinks the strictly upper part by `1+μ`
  (`Matrix.frobenius_norm_diagonal_mul_mul_inv_le`).
* **Stewart's perturbation theorem** ([golub2013matrix] Theorem 7.2.4, after G. W. Stewart, SIAM
  Rev. 15 (1973), Theorem 4.11), `Matrix.exists_invariant_graph_of_sep`. In Schur coordinates
  `T = fromBlocks T₁₁ T₁₂ 0 T₂₂` and a perturbation `E` with blocks `Eᵢⱼ`, the column space of
  `fromRows 1 P` is `(T + E)`-invariant exactly when `P` solves the Riccati equation
  `P A₁₁ - A₂₂ P + P A₁₂ P = E₂₁` (`Aᵢⱼ` the blocks of `T + E`). Its linear part is
  `-sylvesterMap A₂₂ A₁₁`, bounded below by `sep(A₂₂, A₁₁) = sep(A₁₁, A₂₂)` (`Matrix.sep_comm`),
  and `sep(A₁₁, A₂₂) ≥ sep(T₁₁, T₂₂) - ‖E₁₁‖_F - ‖E₂₂‖_F` (`Matrix.sep_sub_le_sep_add`); Stewart's
  quadratic-equation lemma (`ContinuousLinearEquiv.exists_apply_add_eq_of_quadratic`) solves it with
  `‖P‖_F ≤ 2γ/δ` when `4γη < δ²`. With the book's hypothesis
  `‖E‖_F (1 + 5‖T₁₂‖_F/sep) ≤ sep/5`: `δ ≥ 3 sep/5` and `γη ≤ sep²/25`, so `4γη < δ²` and
  `‖P‖_F ≤ (10/3) ‖E₂₁‖_F/sep ≤ 4 ‖E₂₁‖_F/sep` — the book's constants, with room.
* **Graph subspaces** ([golub2013matrix] Corollary 7.2.5 and (7.2.6)): the gap between
  `ran [I; 0]` and `ran [I; P]` is at most `‖P‖₂` (`Matrix.gap_range_fromRows_le`); coordinate-free,
  a subspace at gap `< 1` from `K` of the same dimension is the graph of some `X : K → Kᗮ`
  (`Submodule.exists_eq_graph_of_gap_lt_one`) with `‖X‖ = d/√(1 - d²)`
  (`Submodule.norm_eq_gap_graph_div`, inverting `Submodule.gap_graph` of
  `Numlib/Analysis/InnerProductSpace/Projection/Gap`). The gap is unitarily invariant
  (`Submodule.gap_map_linearIsometryEquiv`).
* **Transport of graphs by powers** (`Krylov.subspaceIterate_graph`): for complementary invariant
  `K`, `W` with `A` bijective on `K`, `A^k` carries the graph of `X : K → W` to the graph of
  `A₂^k X A₁^{-k}`. Pure algebra; it is the coordinate-free core of the appendix proof of
  [golub2013matrix] Theorem 7.3.1 and of Theorem 8.2.2.
* **Subspace iteration for a symmetric operator** ([golub2013matrix] Theorem 8.2.2):
  `gap D (A^k S) ≤ (r/ρ)^k d₀/√(1 - d₀²)` (`LinearMap.IsSymmetric.gap_subspaceIterate_le`, through
  `LinearMap.IsSymmetric.gap_subspaceIterate_le_of_invariant`), the `tan Θ` form of the book's
  argument with no CS decomposition.

## The corrected Theorem 7.3.1

[golub2013matrix] Theorem 7.3.1 bounds the distance of the orthogonal iterates to `D_r(A)` under the
hypothesis `d₀ = dist(D_r(A), ran Q₀) < 1`. That hypothesis is the wrong one — the proof uses
`dist(D_r(Aᴴ), ran Q₀) < 1`, and the text after the theorem says so in words — and the printed
theorem is false: for `A = [[2, 1], [0, 1]]`, `r = 1` and `Q₀ = (1, -1)/√2` (an eigenvector for
`λ₂ = 1`), `d₀ = 1/√2 < 1` but `d_k = 1/√2` for all `k`. The corrected statement
(`Matrix.gap_subspaceIterate_le_of_schur`, with the factor `d₀/√(1 - d̃₀²)`,
`d̃₀ = dist(D_r(Aᴴ), ran Q₀)`) is planned on the graph transport above.

Mathlib has invariant submodules (`Module.End.invtSubmodule`) and generalized eigenspaces, nothing
on their perturbation; `Numlib/Eigen/PowerMethod` has the qualitative convergence of subspace
iteration (`Krylov.exists_gap_subspaceIterate_le`), which assumes diagonalizability and gives no
constant.
-/

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- An invariant subspace on which every eigenvalue lies in `Λ` is contained in the sum of the
generalized eigenspaces of `Λ`: over an algebraically closed field, `S` is the sum of the
generalized eigenspaces of `A|_S` (`Module.End.iSup_maxGenEigenspace_eq_top`), each inside the
corresponding one of `A`, and those of eigenvalues outside `Λ` vanish. -/
theorem invtSubmodule_le_iSup_maxGenEigenspace [IsAlgClosed K] [FiniteDimensional K V]
    {A : Module.End K V} {Λ : Set K} {S : Submodule K V} (hS : S ∈ A.invtSubmodule)
    (hΛ : ∀ μ ∉ Λ, ∀ x ∈ S, A x = μ • x → x = 0) :
    S ≤ ⨆ μ ∈ Λ, A.maxGenEigenspace μ := by
  have hS' : ∀ x ∈ S, A x ∈ S := (A.mem_invtSubmodule_iff_forall_mem_of_mem).1 hS
  have hall : ⨆ μ, A.genEigenspace μ ⊤ = ⊤ := iSup_maxGenEigenspace_eq_top A
  calc S = S ⊓ ⨆ μ, A.genEigenspace μ ⊤ := by rw [hall, inf_top_eq]
    _ = ⨆ μ, S ⊓ A.genEigenspace μ ⊤ := Submodule.inf_iSup_genEigenspace hS' ⊤
    _ ≤ ⨆ μ ∈ Λ, A.maxGenEigenspace μ := iSup_le fun μ => ?_
  by_cases hμ : μ ∈ Λ
  · exact inf_le_right.trans (le_iSup₂_of_le μ hμ le_rfl)
  rw [Submodule.inf_genEigenspace A S hS']
  have h0 : Module.End.genEigenspace (A.restrict hS') μ ⊤ = ⊥ := by
    by_contra h
    have h1 : Module.End.HasUnifEigenvalue (A.restrict hS') μ ⊤ := h
    rw [hasUnifEigenvalue_iff_hasUnifEigenvalue_one (by simp)] at h1
    obtain ⟨x, hx⟩ := HasEigenvalue.exists_hasEigenvector h1
    have hAx : A x = μ • (x : V) := by
      simpa using congrArg Subtype.val hx.apply_eq_smul
    exact hx.2 (Subtype.ext (hΛ μ hμ x x.2 hAx))
  rw [h0, Submodule.map_bot]
  exact bot_le

/-- **Uniqueness of the invariant subspace of a spectral set** ([golub2013matrix] §7.3.2, §7.6.2):
over an algebraically closed field, an `A`-invariant subspace `S` on which every eigenvalue of `A`
lies in `Λ` (`A x = μ x`, `x ∈ S`, `μ ∉ Λ` force `x = 0`) and whose dimension is that of
`⨆ μ ∈ Λ, maxGenEigenspace A μ` (the sum of the algebraic multiplicities) *is* that subspace. -/
theorem invtSubmodule_eq_iSup_maxGenEigenspace [IsAlgClosed K] [FiniteDimensional K V]
    {A : Module.End K V} {Λ : Set K} {S : Submodule K V} (hS : S ∈ A.invtSubmodule)
    (hΛ : ∀ μ ∉ Λ, ∀ x ∈ S, A x = μ • x → x = 0)
    (hdim : Module.finrank K S = Module.finrank K ↥(⨆ μ ∈ Λ, A.maxGenEigenspace μ)) :
    S = ⨆ μ ∈ Λ, A.maxGenEigenspace μ :=
  Submodule.eq_of_le_of_finrank_eq (invtSubmodule_le_iSup_maxGenEigenspace hS hΛ) hdim

end Module.End

namespace Matrix

section Block

variable {K : Type*} [Field K] {n p q : Type*} [Fintype n] [DecidableEq n] [Fintype p]
  [DecidableEq p] [Fintype q] [DecidableEq q]

omit [DecidableEq n] [DecidableEq p] [DecidableEq q] in
/-- A matrix whose reindexing is block upper triangular acts blockwise on coordinates. -/
theorem mulVec_comp_symm_of_reindex_eq_fromBlocks {T : Matrix n n K} (e : n ≃ p ⊕ q)
    {T₁₁ : Matrix p p K} {T₁₂ : Matrix p q K} {T₂₂ : Matrix q q K}
    (hT : T.reindex e e = fromBlocks T₁₁ T₁₂ 0 T₂₂) (v : n → K) :
    (T *ᵥ v) ∘ e.symm = Sum.elim (T₁₁ *ᵥ (v ∘ e.symm ∘ Sum.inl) + T₁₂ *ᵥ (v ∘ e.symm ∘ Sum.inr))
      (T₂₂ *ᵥ (v ∘ e.symm ∘ Sum.inr)) := by
  have h : T.reindex e e *ᵥ (v ∘ e.symm) = (T *ᵥ v) ∘ e.symm := by
    rw [reindex_apply, submatrix_mulVec_equiv]
    congr 2
    ext i
    simp
  rw [← h, hT, fromBlocks_mulVec, zero_mulVec, zero_add]
  rfl

/-- **The first `p` Schur vectors span the invariant subspace of `λ(T₁₁)`** ([golub2013matrix]
§7.6.2, "the first `p` columns of `Q` span the unique invariant subspace associated with
`λ(T₁₁)`"; and the dominant invariant subspace `D_r(A)` of §7.3.2): if `Q` is invertible and
`(Q⁻¹ A Q).reindex e e = fromBlocks T₁₁ T₁₂ 0 T₂₂` with `λ(T₁₁) ∩ λ(T₂₂) = ∅`, then the span of the
columns `Q.col (e.symm (inl i))` is `⨆ μ ∈ λ(T₁₁), maxGenEigenspace A μ`. The span is invariant
with eigenvalues in `λ(T₁₁)` (`Module.End.invtSubmodule_le_iSup_maxGenEigenspace`); conversely the
trailing coordinates `π x = (Q⁻¹ x)(e.symm (inr ·))` intertwine `A` with `T₂₂`, so on a generalized
eigenvector for `μ ∉ λ(T₂₂)` they vanish, and `ker π` is the span. -/
theorem span_cols_eq_iSup_maxGenEigenspace_of_conj [IsAlgClosed K] {A Q : Matrix n n K}
    (hQ : IsUnit Q) (e : n ≃ p ⊕ q) {T₁₁ : Matrix p p K} {T₁₂ : Matrix p q K}
    {T₂₂ : Matrix q q K} (hT : (Q⁻¹ * A * Q).reindex e e = fromBlocks T₁₁ T₁₂ 0 T₂₂)
    (hdisj : Disjoint (spectrum K T₁₁) (spectrum K T₂₂)) :
    Submodule.span K (Set.range fun i : p => Q.col (e.symm (Sum.inl i))) =
      ⨆ μ ∈ spectrum K T₁₁, Module.End.maxGenEigenspace (toLin' A) μ := by
  set T := Q⁻¹ * A * Q with hTdef
  have hQd : IsUnit Q.det := (isUnit_iff_isUnit_det Q).1 hQ
  have hQQ : Q * Q⁻¹ = 1 := mul_nonsing_inv Q hQd
  have hQQ' : Q⁻¹ * Q = 1 := nonsing_inv_mul Q hQd
  have hAQ : A * Q = Q * T := by
    rw [hTdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  have hQA : Q⁻¹ * A = T * Q⁻¹ := by
    rw [hTdef, Matrix.mul_assoc, Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have hblk := mulVec_comp_symm_of_reindex_eq_fromBlocks e hT
  -- the embedding of the leading block and the trailing coordinates
  set w : (p → K) → n → K := fun c => Sum.elim c 0 ∘ e with hw
  have hwsymm : ∀ c, w c ∘ e.symm = Sum.elim c 0 := fun c => by
    ext s; simp [hw]
  have hTw : ∀ c, T *ᵥ w c = w (T₁₁ *ᵥ c) := fun c => by
    ext j
    have h := congrFun (hblk (w c)) (e j)
    have h1 : w c ∘ e.symm ∘ Sum.inl = c := by ext i; simp [hw]
    have h2 : w c ∘ e.symm ∘ Sum.inr = 0 := by ext i; simp [hw]
    rw [h1, h2] at h
    simp only [Function.comp_apply, Equiv.symm_apply_apply, mulVec_zero, add_zero] at h
    rw [h]
    simp [hw]
  -- the span is the range of `c ↦ Q w c`
  have hcol : ∀ i, Q.col (e.symm (Sum.inl i)) = Q *ᵥ w (Pi.single i 1) := fun i => by
    ext j
    simp only [col_apply, mulVec, dotProduct, hw, Function.comp_apply]
    rw [Finset.sum_eq_single (e.symm (Sum.inl i))]
    · simp
    · intro b _ hb
      rcases hbe : e b with k | k
      · have hki : k ≠ i := fun hk => hb (by rw [← hk, ← hbe, Equiv.symm_apply_apply])
        simp [hki]
      · simp
    · simp
  set L : (p → K) →ₗ[K] n → K :=
    { toFun := fun c => Q *ᵥ w c
      map_add' := fun c d => by
        rw [← mulVec_add]; congr 1; ext j
        rcases h : e j with i | i <;> simp [hw, h]
      map_smul' := fun a c => by
        rw [RingHom.id_apply, ← mulVec_smul]; congr 1; ext j
        rcases h : e j with i | i <;> simp [hw, h] } with hL
  have hspan : Submodule.span K (Set.range fun i : p => Q.col (e.symm (Sum.inl i)))
      = LinearMap.range L := by
    rw [LinearMap.range_eq_map, ← (Pi.basisFun K p).span_eq, Submodule.map_span,
      ← Set.range_comp]
    congr 1
    ext i
    simp [hL, hcol]
  rw [hspan]
  apply le_antisymm
  · -- the span is invariant, with eigenvalues in `λ(T₁₁)`
    have hinv : LinearMap.range L ∈ Module.End.invtSubmodule (toLin' A) := by
      rintro _ ⟨c, rfl⟩
      refine ⟨T₁₁ *ᵥ c, ?_⟩
      simp only [hL, LinearMap.coe_mk, AddHom.coe_mk, toLin'_apply]
      rw [mulVec_mulVec, hAQ, ← mulVec_mulVec, hTw]
    refine Module.End.invtSubmodule_le_iSup_maxGenEigenspace hinv fun μ hμ x hx hAx => ?_
    obtain ⟨c, rfl⟩ := hx
    simp only [hL, LinearMap.coe_mk, AddHom.coe_mk, toLin'_apply] at hAx ⊢
    rw [mulVec_mulVec, hAQ, ← mulVec_mulVec, hTw, ← mulVec_smul] at hAx
    have hinj : ∀ u v : n → K, Q *ᵥ u = Q *ᵥ v → u = v := fun u v h => by
      have := congrArg (Q⁻¹ *ᵥ ·) h
      simpa only [mulVec_mulVec, hQQ', one_mulVec] using this
    have h1 := congrArg (· ∘ e.symm) (hinj _ _ hAx)
    simp only [hwsymm] at h1
    have hsm : (μ • w c) ∘ e.symm = Sum.elim (μ • c) 0 := by
      ext s; rcases s with i | i <;> simp [hw]
    rw [hsm] at h1
    have hc : T₁₁ *ᵥ c = μ • c := by
      funext i; exact congrFun h1 (Sum.inl i)
    by_cases hc0 : c = 0
    · subst hc0
      have : w 0 = 0 := by ext j; rcases h : e j with i | i <;> simp [hw, h]
      rw [this, mulVec_zero]
    exact absurd ((mem_spectrum_iff_exists_mulVec_eq_smul T₁₁ μ).2 ⟨c, hc0, hc⟩) hμ
  · -- a generalized eigenvector of `λ(T₁₁)` has vanishing trailing coordinates
    refine iSup₂_le fun μ hμ x hx => ?_
    have hμ2 : μ ∉ spectrum K T₂₂ := Set.disjoint_left.1 hdisj hμ
    set π : (n → K) → q → K := fun y => (Q⁻¹ *ᵥ y) ∘ e.symm ∘ Sum.inr with hπ
    have hπA : ∀ y, π ((A - μ • 1) *ᵥ y) = (T₂₂ - μ • 1) *ᵥ π y := fun y => by
      have h := congrFun (hblk (Q⁻¹ *ᵥ y))
      ext i
      have h2 := h (Sum.inr i)
      simp only [Function.comp_apply, Sum.elim_inr] at h2
      simp only [hπ, sub_mulVec, mulVec_sub, smul_mulVec, one_mulVec, mulVec_smul,
        mulVec_mulVec, hQA, Function.comp_apply, Pi.sub_apply, Pi.smul_apply]
      rw [← mulVec_mulVec, h2]
    have hπpow : ∀ k y, π (((A - μ • 1) ^ k) *ᵥ y) = ((T₂₂ - μ • 1) ^ k) *ᵥ π y := by
      intro k
      induction k with
      | zero => intro y; simp
      | succ k ih =>
        intro y
        rw [pow_succ', ← mulVec_mulVec, hπA, ih, mulVec_mulVec, ← pow_succ']
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hx
    have hk' : ((A - μ • 1) ^ k) *ᵥ x = 0 := by
      rw [← toLin'_apply, toLin'_pow, map_sub, map_smul, toLin'_one, ← hk]
      rfl
    have hunit : IsUnit ((T₂₂ - μ • 1) ^ k) := by
      refine IsUnit.pow k ?_
      have := (spectrum.mem_iff (R := K)).not.1 hμ2
      rw [not_not, Algebra.algebraMap_eq_smul_one] at this
      rw [← neg_sub, IsUnit.neg_iff]
      exact this
    have hπx : π x = 0 := by
      have h := hπpow k x
      rw [hk'] at h
      have h0 : π 0 = 0 := by ext; simp [hπ]
      rw [h0] at h
      obtain ⟨u, hu⟩ := hunit
      have h' := congrArg ((↑u⁻¹ : Matrix q q K) *ᵥ ·) h
      simp only [mulVec_mulVec, ← hu, Units.inv_mul, one_mulVec, mulVec_zero] at h'
      exact h'.symm
    refine ⟨(Q⁻¹ *ᵥ x) ∘ e.symm ∘ Sum.inl, ?_⟩
    simp only [hL, LinearMap.coe_mk, AddHom.coe_mk]
    have hwx : w ((Q⁻¹ *ᵥ x) ∘ e.symm ∘ Sum.inl) = Q⁻¹ *ᵥ x := by
      ext j
      simp only [hw, Function.comp_apply]
      rcases hj : e j with i | i
      · have h3 : e.symm (Sum.inl i) = j := by rw [← hj, Equiv.symm_apply_apply]
        simp [h3]
      · have := congrFun hπx i
        simp only [hπ, Function.comp_apply, Pi.zero_apply] at this
        rw [Sum.elim_inr, Pi.zero_apply, ← this, ← hj, Equiv.symm_apply_apply]
    rw [hwx, mulVec_mulVec, hQQ, one_mulVec]

end Block

end Matrix

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

section Aux

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Conjugation commutes with powers: `(P X P')^k = P X^k P'` when `P' P = 1`. -/
private theorem conj_pow_of_mul_eq_one {P P' X : Matrix m m 𝕜} (h : P' * P = 1) (k : ℕ) :
    (P * X * P') ^ (k + 1) = P * X ^ (k + 1) * P' := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ X (k + 1)]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P' P, h, Matrix.one_mul]

/-- The induced norm is subadditive. -/
private theorem lpOpNorm_add_le' (A B : Matrix m m 𝕜) :
    lpOpNorm 2 (A + B) ≤ lpOpNorm 2 A + lpOpNorm 2 B := by
  rw [lpOpNorm, lpCLM_add]; exact norm_add_le _ _

/-- The induced norm of a power. -/
private theorem lpOpNorm_pow_le' (A : Matrix m m 𝕜) (k : ℕ) :
    lpOpNorm 2 (A ^ k) ≤ lpOpNorm 2 A ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, lpOpNorm, lpCLM_one]
    exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (lpOpNorm_mul_le 2 _ _).trans
      (mul_le_mul_of_nonneg_right ih (lpOpNorm_nonneg _ _))

/-- The `2`-norm of a diagonal matrix is at most any bound on its entries. -/
private theorem lpOpNorm_diagonal_le {d : m → 𝕜} {c : ℝ} (hc : 0 ≤ c) (hd : ∀ i, ‖d i‖ ≤ c) :
    lpOpNorm 2 (diagonal d) ≤ c := by
  rw [lpOpNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [lpCLM_apply, PiLp.toLp_apply, mulVec_diagonal, norm_mul, mul_pow]
  gcongr
  exact hd i

/-- A diagonal matrix with entries of modulus at least `c` stretches every vector by `c`. -/
private theorem le_norm_diagonal_apply {d : m → 𝕜} {c : ℝ} (hc : 0 ≤ c) (hd : ∀ i, c ≤ ‖d i‖)
    (x : PiLp 2 fun _ : m => 𝕜) : c * ‖x‖ ≤ ‖lpCLM 2 (diagonal d) x‖ := by
  refine (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 ?_
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [lpCLM_apply, PiLp.toLp_apply, mulVec_diagonal, norm_mul, mul_pow]
  gcongr
  exact hd i

/-- An operator bounded below by `c > 0` is invertible, with inverse of norm at most `1 / c`. -/
private theorem lpOpNorm_inv_le_of_le_norm {Y : Matrix m m 𝕜} {c : ℝ} (hc : 0 < c)
    (hY : ∀ x, c * ‖x‖ ≤ ‖lpCLM 2 Y x‖) : IsUnit Y ∧ lpOpNorm 2 Y⁻¹ ≤ 1 / c := by
  have hinj : Function.Injective Y.mulVec := by
    intro u v huv
    have h := hY (WithLp.toLp 2 (u - v))
    rw [lpCLM_apply, WithLp.ofLp_toLp, mulVec_sub, huv, sub_self] at h
    have h0 : ‖WithLp.toLp 2 (u - v)‖ = 0 := by
      have := norm_nonneg (WithLp.toLp 2 (u - v))
      simp only [WithLp.toLp_zero, norm_zero] at h
      nlinarith
    rw [norm_eq_zero] at h0
    exact sub_eq_zero.1 (by simpa using congrArg (WithLp.ofLp) h0)
  have hU : IsUnit Y := (mulVec_injective_iff_isUnit).1 hinj
  refine ⟨hU, ?_⟩
  have hYY : Y * Y⁻¹ = 1 := mul_nonsing_inv Y ((isUnit_iff_isUnit_det Y).1 hU)
  rw [lpOpNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have hx : lpCLM 2 Y (lpCLM 2 Y⁻¹ x) = x := by
    rw [← mul_apply_eq_comp, ← lpCLM_mul, hYY, lpCLM_one]; rfl
  have h := hY (lpCLM 2 Y⁻¹ x)
  rw [hx] at h
  rw [one_div_mul_eq_div, le_div_iff₀ hc, mul_comm]
  exact h

open scoped Matrix.Norms.L2Operator in
/-- Unitary conjugation preserves the `2`-norm. -/
private theorem lpOpNorm_two_unitary_conj {Q : Matrix m m 𝕜} (hQ : Q ∈ unitaryGroup m 𝕜)
    (X : Matrix m m 𝕜) : lpOpNorm 2 (Q * X * star Q) = lpOpNorm 2 X := by
  rw [lpOpNorm_two, lpOpNorm_two]
  exact l2_opNorm_unitary_mul_mul_unitary hQ X (Unitary.star_mem hQ)

end Aux

open scoped Matrix.Norms.Frobenius

/-- The scaling step of [golub2013matrix] Lemma 7.3.2: for a strictly upper triangular
`N : Matrix (Fin n) (Fin n) 𝕜`, `μ ≥ 0` and `Δ = diag((1+μ)^i)`,
`‖Δ N Δ⁻¹‖_F ≤ ‖N‖_F / (1 + μ)`: entry `(i, j)`, `i < j`, is scaled by `(1+μ)^{i-j} ≤ (1+μ)⁻¹`.
(`Δ⁻¹` is written out as the diagonal of the reciprocals.) -/
theorem frobenius_norm_diagonal_mul_mul_inv_le {N : Matrix (Fin n) (Fin n) 𝕜}
    (hN : ∀ i j, j ≤ i → N i j = 0) {μ : ℝ} (hμ : 0 ≤ μ) :
    ‖diagonal (fun i : Fin n => (((1 + μ) ^ (i : ℕ) : ℝ) : 𝕜)) * N *
        diagonal (fun i : Fin n => (((1 + μ) ^ (i : ℕ) : ℝ) : 𝕜)⁻¹)‖ ≤ ‖N‖ / (1 + μ) := by
  have h1 : (0 : ℝ) < 1 + μ := by linarith
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [div_pow, le_div_iff₀ (by positivity), frobenius_norm_sq_eq_sum_sq,
    frobenius_norm_sq_eq_sum_sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [mul_diagonal, diagonal_mul]
  by_cases hij : j ≤ i
  · rw [hN i j hij]; simp
  push Not at hij
  have hpow : (1 + μ) ^ (i : ℕ) * (1 + μ) ≤ (1 + μ) ^ (j : ℕ) := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ (by linarith) (Nat.succ_le_of_lt hij)
  have hpos : ∀ k : ℕ, (0 : ℝ) < (1 + μ) ^ k := fun k => pow_pos h1 k
  simp only [norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_pos (hpos _), mul_pow]
  have hr : ((1 + μ) ^ (i : ℕ)) ^ 2 * ((1 + μ) ^ (j : ℕ))⁻¹ ^ 2 * (1 + μ) ^ 2 ≤ 1 := by
    have hq : (1 + μ) ^ (i : ℕ) * (1 + μ) / (1 + μ) ^ (j : ℕ) ≤ 1 := by
      rw [div_le_one (hpos _)]; exact hpow
    calc ((1 + μ) ^ (i : ℕ)) ^ 2 * ((1 + μ) ^ (j : ℕ))⁻¹ ^ 2 * (1 + μ) ^ 2
        = ((1 + μ) ^ (i : ℕ) * (1 + μ) / (1 + μ) ^ (j : ℕ)) ^ 2 := by ring
      _ ≤ 1 := pow_le_one₀ (by positivity) hq
  nlinarith [sq_nonneg ‖N i j‖, hr]

/-- The common setting of [golub2013matrix] Lemma 7.3.2: the scaling `Δ = diag((1+μ)^i)` turns
the Schur form `T = D + N` into `Y = Δ T Δ⁻¹ = D + Δ N Δ⁻¹`. -/
private theorem schur_scaling {T : Matrix (Fin n) (Fin n) 𝕜} (hTu : T.IsUpperTriangular)
    {μ : ℝ} (hμ : 0 ≤ μ) :
    let d : Fin n → 𝕜 := fun i => (((1 + μ) ^ (i : ℕ) : ℝ) : 𝕜)
    diagonal d * diagonal (fun i => (d i)⁻¹) = 1 ∧
      diagonal (fun i => (d i)⁻¹) * diagonal d = 1 ∧
      lpOpNorm 2 (diagonal d) ≤ (1 + μ) ^ (n - 1) ∧
      lpOpNorm 2 (diagonal (fun i => (d i)⁻¹)) ≤ 1 ∧
      diagonal d * T * diagonal (fun i => (d i)⁻¹) =
        diagPart T + diagonal d * strictUpper T * diagonal (fun i => (d i)⁻¹) ∧
      lpOpNorm 2 (diagonal d * strictUpper T * diagonal (fun i => (d i)⁻¹)) ≤
        ‖strictUpper T‖ / (1 + μ) := by
  intro d
  have h1 : (1 : ℝ) ≤ 1 + μ := by linarith
  have hd0 : ∀ i, d i ≠ 0 := fun i => RCLike.ofReal_ne_zero.2 (pow_pos (by linarith) _).ne'
  have hnd : ∀ i, ‖d i‖ = (1 + μ) ^ (i : ℕ) := fun i => by
    simp only [d, RCLike.norm_ofReal,
      abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + μ) _)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hd0 i)
  · rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hd0 i)
  · refine lpOpNorm_diagonal_le (by positivity) fun i => ?_
    rw [hnd]
    exact pow_le_pow_right₀ h1 (by omega)
  · refine lpOpNorm_diagonal_le zero_le_one fun i => ?_
    rw [norm_inv, hnd]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ h1)
  · have hT : T = diagPart T + strictUpper T := by
      have h := diagPart_add_strictLower_add_strictUpper T
      have hl : strictLower T = 0 := by
        ext i j
        rw [strictLower_apply]
        split_ifs with h
        · exact hTu h
        · rfl
      rw [hl, add_zero] at h
      exact h.symm
    conv_lhs => rw [hT]
    rw [Matrix.mul_add, Matrix.add_mul, diagPart, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 2
    funext i
    field_simp [hd0 i]
  · refine (l2_opNorm_le_frobenius_norm _).trans ?_
    refine frobenius_norm_diagonal_mul_mul_inv_le (fun i j hji => ?_) hμ
    simp [strictUpper_apply, not_lt.2 hji]

/-- **Powers from a Schur form** ([golub2013matrix] Lemma 7.3.2, (7.3.15)): if `Q` is unitary,
`Qᴴ A Q = T` is upper triangular with strictly upper part `N` and `μ ≥ 0`, then
`‖A^k‖₂ ≤ (1 + μ)^{n-1} (max_i |t_ii| + ‖N‖_F / (1 + μ))^k` for every `k`.
`A^k = Q Δ⁻¹ (D + Δ N Δ⁻¹)^k Δ Qᴴ` with `Δ = diag((1+μ)^i)`, `‖Δ‖₂ ≤ (1+μ)^{n-1}`,
`‖Δ⁻¹‖₂ ≤ 1`, `‖D‖₂ = max |t_ii|` and `‖Δ N Δ⁻¹‖₂ ≤ ‖Δ N Δ⁻¹‖_F ≤ ‖N‖_F/(1+μ)`
(`Matrix.frobenius_norm_diagonal_mul_mul_inv_le`). -/
theorem l2_opNorm_pow_le_of_schur {A Q T : Matrix (Fin n) (Fin n) 𝕜}
    (hQ : Q ∈ unitaryGroup (Fin n) 𝕜) (hT : star Q * A * Q = T) (hTu : T.IsUpperTriangular)
    {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) :
    lpOpNorm 2 (A ^ k) ≤
      (1 + μ) ^ (n - 1) * ((⨆ i, ‖T i i‖) + ‖strictUpper T‖ / (1 + μ)) ^ k := by
  have h1 : (1 : ℝ) ≤ 1 + μ := by linarith
  have hsup0 : 0 ≤ ⨆ i, ‖T i i‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  rcases k with _ | k
  · rw [pow_zero, pow_zero, mul_one]
    refine le_trans ?_ (one_le_pow₀ h1)
    rw [lpOpNorm, lpCLM_one]; exact ContinuousLinearMap.norm_id_le
  obtain ⟨hΔ, hΔ', hΔn, hΔin, hY, hM⟩ := schur_scaling hTu hμ
  set d : Fin n → 𝕜 := fun i => (((1 + μ) ^ (i : ℕ) : ℝ) : 𝕜)
  set Δ := diagonal d
  set Δi := diagonal fun i => (d i)⁻¹
  set Y := Δ * T * Δi with hYdef
  have hQQ : Q * star Q = 1 := mem_unitaryGroup_iff.1 hQ
  have hQQ' : star Q * Q = 1 := mem_unitaryGroup_iff'.1 hQ
  have hA : A = Q * T * star Q := by
    rw [← hT]; simp only [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
    rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have hTY : T = Δi * Y * Δ := by
    simp only [hYdef, ← Matrix.mul_assoc, hΔ', Matrix.one_mul]
    rw [Matrix.mul_assoc, hΔ', Matrix.mul_one]
  have hAk : A ^ (k + 1) = Q * (Δi * Y ^ (k + 1) * Δ) * star Q := by
    rw [hA, conj_pow_of_mul_eq_one hQQ', hTY, conj_pow_of_mul_eq_one hΔ]
  rw [hAk, lpOpNorm_two_unitary_conj hQ]
  have hYn : lpOpNorm 2 Y ≤ (⨆ i, ‖T i i‖) + ‖strictUpper T‖ / (1 + μ) := by
    rw [hY]
    refine (lpOpNorm_add_le' _ _).trans (add_le_add ?_ hM)
    refine lpOpNorm_diagonal_le hsup0 fun i => ?_
    exact le_ciSup (Finite.bddAbove_range fun i => ‖T i i‖) i
  calc lpOpNorm 2 (Δi * Y ^ (k + 1) * Δ)
      ≤ lpOpNorm 2 Δi * lpOpNorm 2 (Y ^ (k + 1)) * lpOpNorm 2 Δ :=
        (lpOpNorm_mul_le 2 _ _).trans (mul_le_mul_of_nonneg_right (lpOpNorm_mul_le 2 _ _)
          (lpOpNorm_nonneg _ _))
    _ ≤ 1 * ((⨆ i, ‖T i i‖) + ‖strictUpper T‖ / (1 + μ)) ^ (k + 1) * (1 + μ) ^ (n - 1) := by
        have hYk := (lpOpNorm_pow_le' Y (k + 1)).trans
          (pow_le_pow_left₀ (lpOpNorm_nonneg _ _) hYn (k + 1))
        have hX0 : 0 ≤ (⨆ i, ‖T i i‖) + ‖strictUpper T‖ / (1 + μ) := by positivity
        exact mul_le_mul (mul_le_mul hΔin hYk (lpOpNorm_nonneg _ _) zero_le_one) hΔn
          (lpOpNorm_nonneg _ _) (mul_nonneg zero_le_one (pow_nonneg hX0 _))
    _ = _ := by ring

/-- **Powers of the inverse from a Schur form** ([golub2013matrix] Lemma 7.3.2, (7.3.16)): in the
setting of `Matrix.l2_opNorm_pow_le_of_schur`, if `(1 + μ) m > ‖N‖_F` for `m = min_i |t_ii|`,
then `‖A⁻¹^k‖₂ ≤ (1 + μ)^{n-1} (1 / (m - ‖N‖_F/(1+μ)))^k`. The hypothesis already makes `A`
nonsingular: `Y = D + Δ N Δ⁻¹` satisfies `‖Y x‖ ≥ (m - ‖Δ N Δ⁻¹‖₂) ‖x‖` (the Neumann-series bound
`‖(1 + X)⁻¹‖ ≤ 1/(1 - ‖X‖)` of the book, in lower-bound form). The book's last display writes
`|μ|` for `|λ_min|`. -/
theorem l2_opNorm_inv_pow_le_of_schur {A Q T : Matrix (Fin n) (Fin n) 𝕜}
    (hQ : Q ∈ unitaryGroup (Fin n) 𝕜) (hT : star Q * A * Q = T) (hTu : T.IsUpperTriangular)
    {μ : ℝ} (hμ : 0 ≤ μ) (hm : ‖strictUpper T‖ < (1 + μ) * ⨅ i, ‖T i i‖) (k : ℕ) :
    lpOpNorm 2 (A⁻¹ ^ k) ≤
      (1 + μ) ^ (n - 1) * (1 / ((⨅ i, ‖T i i‖) - ‖strictUpper T‖ / (1 + μ))) ^ k := by
  have h1 : (1 : ℝ) ≤ 1 + μ := by linarith
  set m := ⨅ i, ‖T i i‖ with hmdef
  have hm0 : 0 ≤ m := Real.iInf_nonneg fun _ => norm_nonneg _
  have hc : 0 < m - ‖strictUpper T‖ / (1 + μ) := by
    rw [sub_pos, div_lt_iff₀ (by linarith)]; linarith
  rcases k with _ | k
  · rw [pow_zero, pow_zero, mul_one]
    refine le_trans ?_ (one_le_pow₀ h1)
    rw [lpOpNorm, lpCLM_one]; exact ContinuousLinearMap.norm_id_le
  obtain ⟨hΔ, hΔ', hΔn, hΔin, hY, hM⟩ := schur_scaling hTu hμ
  set d : Fin n → 𝕜 := fun i => (((1 + μ) ^ (i : ℕ) : ℝ) : 𝕜)
  set Δ := diagonal d
  set Δi := diagonal fun i => (d i)⁻¹
  set Y := Δ * T * Δi with hYdef
  set M := Δ * strictUpper T * Δi
  have hQQ : Q * star Q = 1 := mem_unitaryGroup_iff.1 hQ
  have hQQ' : star Q * Q = 1 := mem_unitaryGroup_iff'.1 hQ
  have hA : A = Q * T * star Q := by
    rw [← hT]; simp only [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
    rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have hTY : T = Δi * Y * Δ := by
    simp only [hYdef, ← Matrix.mul_assoc, hΔ', Matrix.one_mul]
    rw [Matrix.mul_assoc, hΔ', Matrix.mul_one]
  -- `Y` is bounded below
  have hlow : ∀ x, (m - lpOpNorm 2 M) * ‖x‖ ≤ ‖lpCLM 2 Y x‖ := by
    intro x
    have hD := le_norm_diagonal_apply (d := T.diag) hm0
      (fun i => ciInf_le (Finite.bddBelow_range fun i => ‖T i i‖) i) x
    have hMx : ‖lpCLM 2 M x‖ ≤ lpOpNorm 2 M * ‖x‖ := (lpCLM 2 M).le_opNorm x
    have hsplit : lpCLM 2 Y x = lpCLM 2 (diagonal T.diag) x + lpCLM 2 M x := by
      rw [hY, lpCLM_add]; rfl
    rw [hsplit]
    have h2 : ‖lpCLM 2 (diagonal T.diag) x‖ ≤
        ‖lpCLM 2 (diagonal T.diag) x + lpCLM 2 M x‖ + ‖lpCLM 2 M x‖ := by
      simpa using norm_sub_le (lpCLM 2 (diagonal T.diag) x + lpCLM 2 M x) (lpCLM 2 M x)
    rw [sub_mul]
    linarith
  have hcM : m - ‖strictUpper T‖ / (1 + μ) ≤ m - lpOpNorm 2 M := by linarith
  obtain ⟨hYu, hYinv⟩ := lpOpNorm_inv_le_of_le_norm (hc.trans_le hcM) hlow
  have hYinv' : lpOpNorm 2 Y⁻¹ ≤ 1 / (m - ‖strictUpper T‖ / (1 + μ)) :=
    hYinv.trans (one_div_le_one_div_of_le hc hcM)
  -- `A⁻¹ = Q Δ⁻¹ Y⁻¹ Δ Qᴴ`
  have hΔinv : Δ⁻¹ = Δi := inv_eq_right_inv hΔ
  have hΔiinv : Δi⁻¹ = Δ := inv_eq_right_inv hΔ'
  have hQinv : Q⁻¹ = star Q := inv_eq_right_inv hQQ
  have hsQinv : (star Q)⁻¹ = Q := inv_eq_right_inv hQQ'
  have hAinv : A⁻¹ = Q * (Δi * Y⁻¹ * Δ) * star Q := by
    rw [hA, hTY, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.mul_inv_rev, hsQinv, hQinv, hΔinv, hΔiinv]
    simp only [Matrix.mul_assoc]
  rw [hAinv, conj_pow_of_mul_eq_one hQQ', lpOpNorm_two_unitary_conj hQ,
    conj_pow_of_mul_eq_one hΔ]
  calc lpOpNorm 2 (Δi * Y⁻¹ ^ (k + 1) * Δ)
      ≤ lpOpNorm 2 Δi * lpOpNorm 2 (Y⁻¹ ^ (k + 1)) * lpOpNorm 2 Δ :=
        (lpOpNorm_mul_le 2 _ _).trans (mul_le_mul_of_nonneg_right (lpOpNorm_mul_le 2 _ _)
          (lpOpNorm_nonneg _ _))
    _ ≤ 1 * (1 / (m - ‖strictUpper T‖ / (1 + μ))) ^ (k + 1) * (1 + μ) ^ (n - 1) := by
        have hYk := (lpOpNorm_pow_le' Y⁻¹ (k + 1)).trans
          (pow_le_pow_left₀ (lpOpNorm_nonneg _ _) hYinv' (k + 1))
        exact mul_le_mul (mul_le_mul hΔin hYk (lpOpNorm_nonneg _ _) zero_le_one) hΔn
          (lpOpNorm_nonneg _ _) (mul_nonneg zero_le_one (pow_nonneg (one_div_pos.2 hc).le _))
    _ = _ := by ring

end Matrix

namespace Matrix

/-- Stewart's quadratic-equation lemma for a linear operator on a finite-dimensional normed space
that is bounded below: if `δ ‖x‖ ≤ ‖L x‖` then `L` is invertible with `‖L⁻¹‖ ≤ 1/δ`, and
`ContinuousLinearEquiv.exists_apply_add_eq_of_quadratic` applies. (Stated for a general `F` so that
the operator norm is formed on `F`, not on a type with a scoped norm such as the Frobenius norm on
matrices.) -/
private theorem exists_apply_add_eq_of_quadratic_of_le_norm {𝕜 F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F] (L : F →ₗ[𝕜] F) {δ γ η : ℝ} (hδ : 0 < δ)
    (hL : ∀ x, δ * ‖x‖ ≤ ‖L x‖) {g : F} (hg : ‖g‖ ≤ γ) {φ : F → F} (hφ0 : φ 0 = 0)
    (hφ : ∀ x y, ‖φ x - φ y‖ ≤ η * (‖x‖ + ‖y‖) * ‖x - y‖) (h : 4 * γ * η < δ ^ 2) :
    ∃ x, L x + φ x = g ∧ ‖x‖ ≤ 2 * γ / δ := by
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := hL x
    rw [hx, norm_zero] at h1
    exact norm_eq_zero.1 (le_antisymm (nonpos_of_mul_nonpos_right h1 hδ) (norm_nonneg _))
  have : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  set L₁ := LinearEquiv.ofBijective L ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  set L' := L₁.toContinuousLinearEquiv
  have hLs : ‖(L'.symm : F →L[𝕜] F)‖ ≤ 1 / δ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
    have hy : L (L'.symm y) = y := L₁.apply_symm_apply y
    have h1 := hL (L'.symm y)
    rw [hy] at h1
    change ‖L'.symm y‖ ≤ 1 / δ * ‖y‖
    rw [one_div_mul_eq_div, le_div_iff₀ hδ, mul_comm]
    exact h1
  exact ContinuousLinearEquiv.exists_apply_add_eq_of_quadratic L' hδ hLs hg hφ0 hφ h

open scoped Matrix.Norms.Frobenius

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- A sum over the image of an injection is at most the full sum of a nonnegative function. -/
private theorem sum_comp_le_of_injective {α β : Type*} [Fintype α] [Fintype β] (F : β → ℝ)
    {h : α → β} (hh : Function.Injective h) (hF : ∀ b, 0 ≤ F b) : ∑ a, F (h a) ≤ ∑ b, F b := by
  classical
  rw [← Finset.sum_image (f := F) (fun x _ y _ hxy => hh hxy)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => hF _

omit [DecidableEq m] [DecidableEq n] in
/-- A submatrix along injective row and column maps has at most the Frobenius norm of the
matrix. -/
theorem frobenius_norm_submatrix_le {m' n' : Type*} [Fintype m'] [Fintype n']
    (E : Matrix m n 𝕜) {f : m' → m} {g : n' → n} (hf : Function.Injective f)
    (hg : Function.Injective g) : ‖E.submatrix f g‖ ≤ ‖E‖ := by
  refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  rw [frobenius_norm_sq_eq_sum_sq, frobenius_norm_sq_eq_sum_sq]
  calc ∑ i, ∑ j, ‖E.submatrix f g i j‖ ^ 2 ≤ ∑ i, ∑ t, ‖E (f i) t‖ ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          sum_comp_le_of_injective (fun t => ‖E (f i) t‖ ^ 2) hg fun _ => sq_nonneg _
    _ ≤ ∑ s, ∑ t, ‖E s t‖ ^ 2 :=
        sum_comp_le_of_injective (fun s => ∑ t, ‖E s t‖ ^ 2) hf
          fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Stewart's perturbation theorem for invariant subspaces** ([golub2013matrix] Theorem 7.2.4,
after G. W. Stewart, SIAM Rev. 15 (1973), Theorem 4.11), in Schur coordinates: for
`T = fromBlocks T₁₁ T₁₂ 0 T₂₂`, a perturbation `E` with `s = sep T₁₁ T₂₂ > 0` and
`‖E‖_F (1 + 5 ‖T₁₂‖_F / s) ≤ s / 5`, there is `P` with `‖P‖_F ≤ 4 ‖E₂₁‖_F / s` such that the
column space of `[I; P]` is `(T + E)`-invariant:
`(T + E) [I; P] = [I; P] (T₁₁ + E₁₁ + (T₁₂ + E₁₂) P)`.
The second block row is the Riccati equation `P A₁₁ - A₂₂ P + P A₁₂ P = E₂₁` (`Aᵢⱼ` the blocks of
`T + E`), solved by Stewart's quadratic-equation lemma
(`ContinuousLinearEquiv.exists_apply_add_eq_of_quadratic`) with `L = -sylvesterMap A₂₂ A₁₁`,
`‖L⁻¹‖ ≤ 1 / sep A₁₁ A₂₂` (`Matrix.sep_comm`), `sep A₁₁ A₂₂ ≥ s - 2‖E‖_F`
(`Matrix.sep_sub_le_sep_add`), `γ = ‖E₂₁‖_F` and `η = ‖A₁₂‖_F`: then `δ ≥ 3s/5` and
`4γη ≤ 4s²/25 < δ²`, and the solution has `‖P‖_F ≤ 2γ/δ ≤ (10/3) γ/s`. -/
theorem exists_invariant_graph_of_sep {T₁₁ : Matrix m m 𝕜} {T₁₂ : Matrix m n 𝕜}
    {T₂₂ : Matrix n n 𝕜} {E : Matrix (m ⊕ n) (m ⊕ n) 𝕜} (hs : 0 < sep T₁₁ T₂₂)
    (hE : ‖E‖ * (1 + 5 * ‖T₁₂‖ / sep T₁₁ T₂₂) ≤ sep T₁₁ T₂₂ / 5) :
    ∃ P : Matrix n m 𝕜, ‖P‖ ≤ 4 * ‖E.toBlocks₂₁‖ / sep T₁₁ T₂₂ ∧
      (fromBlocks T₁₁ T₁₂ 0 T₂₂ + E) * fromRows 1 P =
        fromRows 1 P * (T₁₁ + E.toBlocks₁₁ + (T₁₂ + E.toBlocks₁₂) * P) := by
  set s := sep T₁₁ T₂₂ with hsdef
  set ε := ‖E‖ with hεdef
  set t := ‖T₁₂‖ with htdef
  set A₁₁ := T₁₁ + E.toBlocks₁₁ with hA11
  set A₁₂ := T₁₂ + E.toBlocks₁₂ with hA12
  set A₂₂ := T₂₂ + E.toBlocks₂₂ with hA22
  set g := E.toBlocks₂₁
  have hε0 : 0 ≤ ε := norm_nonneg _
  have ht0 : 0 ≤ t := norm_nonneg _
  have hb11 : ‖E.toBlocks₁₁‖ ≤ ε :=
    frobenius_norm_submatrix_le E Sum.inl_injective Sum.inl_injective
  have hb12 : ‖E.toBlocks₁₂‖ ≤ ε :=
    frobenius_norm_submatrix_le E Sum.inl_injective Sum.inr_injective
  have hb21 : ‖g‖ ≤ ε :=
    frobenius_norm_submatrix_le E Sum.inr_injective Sum.inl_injective
  have hb22 : ‖E.toBlocks₂₂‖ ≤ ε :=
    frobenius_norm_submatrix_le E Sum.inr_injective Sum.inr_injective
  -- the arithmetic of the hypothesis
  have hE' : 5 * ε * s + 25 * ε * t ≤ s ^ 2 := by
    have h := hE
    rw [mul_add, mul_one, mul_div_assoc', le_div_iff₀ (by norm_num : (0 : ℝ) < 5)] at h
    have h2 : ε * (5 * t) / s * 5 = 25 * ε * t / s := by ring
    rw [add_mul, h2] at h
    have h3 : 25 * ε * t / s * s = 25 * ε * t := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h hs.le]
  have hεs : ε ≤ s / 5 := by nlinarith [mul_nonneg hε0 ht0]
  -- the separation of the perturbed blocks
  set δ := sep A₁₁ A₂₂ with hδdef
  have hδ : 3 * s / 5 ≤ δ := by
    have := sep_sub_le_sep_add T₁₁ E.toBlocks₁₁ T₂₂ E.toBlocks₂₂
    linarith
  have hδ0 : 0 < δ := by linarith
  have hsep' : sep A₂₂ A₁₁ = δ := sep_comm _ _
  have hlow : ∀ X : Matrix n m 𝕜, δ * ‖X‖ ≤ ‖X * A₁₁ - A₂₂ * X‖ := fun X => by
    have h := sep_mul_norm_le (A := A₂₂) (B := A₁₁) X
    rwa [hsep', norm_sub_rev] at h
  -- the linear part `L X = X A₁₁ - A₂₂ X`
  set L₀ : Matrix n m 𝕜 →ₗ[𝕜] Matrix n m 𝕜 := -sylvesterMap A₂₂ A₁₁ with hL₀
  have hL₀apply : ∀ X, L₀ X = X * A₁₁ - A₂₂ * X := fun X => by
    rw [hL₀, LinearMap.neg_apply, sylvesterMap_apply, neg_sub]
  have hinj : Function.Injective L₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    have h := hlow X
    rw [← hL₀apply, hX, norm_zero] at h
    exact norm_eq_zero.1 (le_antisymm (nonpos_of_mul_nonpos_right h hδ0) (norm_nonneg _))
  -- the quadratic part `φ X = X A₁₂ X`
  set η := ‖A₁₂‖ with hηdef
  have hη : η ≤ t + ε := (norm_add_le _ _).trans (by linarith)
  have hφ : ∀ X Y : Matrix n m 𝕜, ‖X * A₁₂ * X - Y * A₁₂ * Y‖ ≤ η * (‖X‖ + ‖Y‖) * ‖X - Y‖ := by
    intro X Y
    have heq : X * A₁₂ * X - Y * A₁₂ * Y = (X - Y) * A₁₂ * X + Y * A₁₂ * (X - Y) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(X - Y) * A₁₂ * X‖ ≤ ‖X - Y‖ * η * ‖X‖ :=
      (frobenius_norm_mul _ _).trans (by gcongr; exact frobenius_norm_mul _ _)
    have h2 : ‖Y * A₁₂ * (X - Y)‖ ≤ ‖Y‖ * η * ‖X - Y‖ :=
      (frobenius_norm_mul _ _).trans (by gcongr; exact frobenius_norm_mul _ _)
    nlinarith
  have hkey : 4 * ‖g‖ * η < δ ^ 2 := by
    have h1 : ‖g‖ * η ≤ ε * (t + ε) :=
      mul_le_mul hb21 hη (norm_nonneg _) hε0
    have h2 : ε * (t + ε) ≤ s ^ 2 / 25 := by nlinarith
    have h3 : (3 * s / 5) ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (by positivity) hδ 2
    nlinarith
  obtain ⟨P, hP, hPn⟩ := exists_apply_add_eq_of_quadratic_of_le_norm L₀ hδ0
    (fun X => (hL₀apply X).symm ▸ hlow X) le_rfl (φ := fun X => X * A₁₂ * X) (by simp) hφ hkey
  refine ⟨P, ?_, ?_⟩
  · calc ‖P‖ ≤ 2 * ‖g‖ / δ := hPn
      _ ≤ 2 * ‖g‖ / (3 * s / 5) := by gcongr
      _ ≤ 4 * ‖g‖ / s := by
          rw [div_le_div_iff₀ (by positivity) hs]; nlinarith [norm_nonneg g]
  · have hP' : P * A₁₁ - A₂₂ * P + P * A₁₂ * P = g := by
      rw [← hL₀apply]; exact hP
    conv_lhs => rw [← fromBlocks_toBlocks E, fromBlocks_add, fromBlocks_mul_fromRows]
    rw [fromRows_mul]
    congr 1
    · simp only [hA11, hA12, Matrix.mul_one, Matrix.one_mul, Matrix.mul_add, Matrix.add_mul]
    · simp only [zero_add, Matrix.mul_one]
      have hg : E.toBlocks₂₁ = P * A₁₁ - A₂₂ * P + P * A₁₂ * P := hP'.symm
      rw [hg, ← hA22, Matrix.mul_assoc P A₁₂ P]
      simp only [hA11, Matrix.mul_add]
      abel

end Matrix

namespace Submodule

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **The gap is invariant under isometries**: `gap (e K) (e L) = gap K L` for a linear isometry
equivalence `e`, since `P_{eK} = e P_K e⁻¹` (`Submodule.starProjection_map_apply`). With unitary
matrices this is the unitary invariance of [golub2013matrix]'s `dist` (§2.5.3). -/
theorem gap_map_linearIsometryEquiv (e : E ≃ₗᵢ[𝕜] F) (K L : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    (K.map (e.toLinearEquiv : E →ₗ[𝕜] F)).gap (L.map (e.toLinearEquiv : E →ₗ[𝕜] F)) =
      K.gap L := by
  have h : (K.map (e.toLinearEquiv : E →ₗ[𝕜] F)).starProjection -
      (L.map (e.toLinearEquiv : E →ₗ[𝕜] F)).starProjection =
      (e.toLinearIsometry.toContinuousLinearMap).comp
        ((K.starProjection - L.starProjection).comp
          (e.symm.toLinearIsometry.toContinuousLinearMap)) := by
    ext x
    simp [starProjection_map_apply]
  rw [gap, gap, h, LinearIsometry.norm_toContinuousLinearMap_comp]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ e.symm

/-- **A subspace close to `K` is a graph over `K`**: if `gap K S < 1` and `S` has the dimension of
`K` (finite), then `S = K.graph X` for some `X : K →L[𝕜] Kᗮ`. The restricted projection
`P_K|_S` is injective (`Submodule.eq_zero_of_starProjection_eq_zero_of_gap_lt_one`), hence
bijective, and `X = P_{Kᗮ}|_S ∘ (P_K|_S)⁻¹`. -/
theorem exists_eq_graph_of_gap_lt_one [FiniteDimensional 𝕜 E] (K S : Submodule 𝕜 E)
    (hdim : Module.finrank 𝕜 S = Module.finrank 𝕜 K) (h : K.gap S < 1) :
    ∃ X : K →L[𝕜] Kᗮ, S = K.graph X := by
  set φ := K.orthogonalProjectionRestrict S with hφ
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : K.starProjection (x : E) = 0 := by
      rw [← coe_orthogonalProjectionRestrict_apply, ← hφ, hx, ZeroMemClass.coe_zero]
    exact Subtype.ext (K.eq_zero_of_starProjection_eq_zero_of_gap_lt_one S h x.2 h0)
  have hbij : Function.Bijective φ :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩
  set ψ := LinearEquiv.ofBijective φ hbij with hψ
  set X : K →ₗ[𝕜] Kᗮ := Kᗮ.orthogonalProjectionRestrict S ∘ₗ (ψ.symm : K →ₗ[𝕜] S) with hX
  refine ⟨LinearMap.toContinuousLinearMap X, ?_⟩
  have hdec : ∀ s : S, (φ s : E) + ((Kᗮ.orthogonalProjectionRestrict S s : Kᗮ) : E) = s :=
    fun s => by
      rw [coe_orthogonalProjectionRestrict_apply, coe_orthogonalProjectionRestrict_apply,
        starProjection_orthogonal]
      simp
  ext y
  constructor
  · intro hy
    refine ⟨φ ⟨y, hy⟩, ?_⟩
    have hs : ψ.symm (φ ⟨y, hy⟩) = ⟨y, hy⟩ := ψ.symm_apply_apply ⟨y, hy⟩
    simp only [LinearMap.add_apply, Submodule.subtype_apply, LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, LinearMap.coe_toContinuousLinearMap', hX, LinearEquiv.coe_coe]
    rw [hs, hdec]
  · rintro ⟨u, rfl⟩
    have hu : φ (ψ.symm u) = u := ψ.apply_symm_apply u
    simp only [LinearMap.add_apply, Submodule.subtype_apply, LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, LinearMap.coe_toContinuousLinearMap', hX, LinearEquiv.coe_coe]
    have := hdec (ψ.symm u)
    rw [hu] at this
    rw [this]
    exact (ψ.symm u).2

/-- The norm of `X` is read off the gap of its graph: `‖X‖ = d / √(1 - d²)` for
`d = gap K (graph X) < 1` (inverting `Submodule.gap_graph`). -/
theorem norm_eq_gap_graph_div (K : Submodule 𝕜 E) [FiniteDimensional 𝕜 K] (X : K →L[𝕜] Kᗮ) :
    ‖X‖ = K.gap (K.graph X) / Real.sqrt (1 - K.gap (K.graph X) ^ 2) := by
  rw [gap_graph]
  set t := ‖X‖
  have hs : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hs2 : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  have h1 : 1 - (t / Real.sqrt (1 + t ^ 2)) ^ 2 = (1 / Real.sqrt (1 + t ^ 2)) ^ 2 := by
    rw [div_pow, div_pow, hs2]; field_simp; ring
  rw [h1, Real.sqrt_sq (by positivity)]
  field_simp

end Submodule

namespace Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Transport of a graph subspace by powers** (the coordinate-free core of [golub2013matrix]
Theorem 7.3.1's appendix proof and of Theorem 8.2.2): let `K`, `W` be `A`-invariant, `A` bijective
on `K` (`A₁ = A|_K`), `A₂ = A|_W`, and `X : K →ₗ[𝕜] W`. The graph `{u + X u | u ∈ K}` is carried by
`A^k` onto the graph of `A₂^k X A₁^{-k}`: `A^k (u + X u) = A₁^k u + A₂^k X u`, and `u ↦ A₁^k u` is a
bijection of `K`. Pure algebra: no complement, inner product or dimension is used. -/
theorem subspaceIterate_graph {A : Module.End 𝕜 E} {K W : Submodule 𝕜 E}
    (hK : ∀ x ∈ K, A x ∈ K) (hW : ∀ x ∈ W, A x ∈ W) (hA₁ : Function.Bijective (A.restrict hK))
    (X : K →ₗ[𝕜] W) (k : ℕ) :
    subspaceIterate A (LinearMap.range (K.subtype + W.subtype ∘ₗ X)) k =
      LinearMap.range (K.subtype + W.subtype ∘ₗ (((A.restrict hW) ^ k) ∘ₗ X ∘ₗ
        (((LinearEquiv.ofBijective _ hA₁).symm : K →ₗ[𝕜] K) ^ k))) := by
  set A₁ := LinearEquiv.ofBijective _ hA₁ with hA₁def
  set B : Module.End 𝕜 K := (A₁ : K →ₗ[𝕜] K) with hB
  set C : Module.End 𝕜 K := (A₁.symm : K →ₗ[𝕜] K) with hC
  have hBC : B * C = 1 := by
    ext u; simp [hB, hC]
  have hCB : C * B = 1 := by
    ext u; simp [hB, hC]
  have hcomm : Commute B C := hBC.trans hCB.symm
  have hBCk : B ^ k * C ^ k = 1 := by rw [← hcomm.mul_pow, hBC, one_pow]
  have hCBk : C ^ k * B ^ k = 1 := by rw [← hcomm.symm.mul_pow, hCB, one_pow]
  have hpowK : ∀ u : K, (A ^ k) (u : E) = ((B ^ k) u : E) := fun u => by
    have hB' : B = A.restrict hK := by ext; simp [hB, hA₁def]
    rw [hB', Module.End.pow_restrict k hK]
    rfl
  have hpowW : ∀ w : W, (A ^ k) (w : E) = (((A.restrict hW) ^ k) w : E) := fun w => by
    rw [Module.End.pow_restrict k hW]
    rfl
  ext y
  rw [mem_subspaceIterate]
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    refine ⟨(B ^ k) u, ?_⟩
    have hu : (C ^ k) ((B ^ k) u) = u := by rw [← Module.End.mul_apply, hCBk]; rfl
    simp only [LinearMap.add_apply, Submodule.subtype_apply, LinearMap.comp_apply, map_add,
      hpowK, hpowW, hu]
  · rintro ⟨u, rfl⟩
    refine ⟨_, ⟨(C ^ k) u, rfl⟩, ?_⟩
    have hu : (B ^ k) ((C ^ k) u) = u := by rw [← Module.End.mul_apply, hBCk]; rfl
    simp only [LinearMap.add_apply, Submodule.subtype_apply, LinearMap.comp_apply, map_add,
      hpowK, hpowW, hu]

end Krylov

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E}

/-- **Subspace iteration toward an invariant subspace of a symmetric operator, explicit
constant**: let `D` be `A`-invariant with `‖A u‖ ≥ ρ ‖u‖` on `D` (`ρ > 0`) and `‖A w‖ ≤ r ‖w‖` on
`Dᗮ` (`r ≥ 0`), and `S` of the dimension of `D` with `d₀ = gap D S < 1`. Then
`gap D (A^k S) ≤ (r / ρ)^k d₀ / √(1 - d₀²)`. `Dᗮ` is invariant (symmetry), `S` is the graph of
some `X : D → Dᗮ` with `‖X‖ = d₀ / √(1 - d₀²)` (`Submodule.exists_eq_graph_of_gap_lt_one`,
`Submodule.norm_eq_gap_graph_div`), `A^k S` is the graph of `A₂^k X A₁^{-k}`
(`Krylov.subspaceIterate_graph`), and `gap ≤ ‖X_k‖` (`Submodule.gap_graph`). -/
theorem gap_subspaceIterate_le_of_invariant (hA : A.IsSymmetric) {D S : Submodule 𝕜 E}
    (hD : ∀ x ∈ D, A x ∈ D) {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r)
    (hlow : ∀ u ∈ D, ρ * ‖u‖ ≤ ‖A u‖) (hup : ∀ w ∈ Dᗮ, ‖A w‖ ≤ r * ‖w‖)
    (hdim : Module.finrank 𝕜 S = Module.finrank 𝕜 D) (h0 : D.gap S < 1) (k : ℕ) :
    D.gap (Krylov.subspaceIterate A S k) ≤
      (r / ρ) ^ k * (D.gap S / Real.sqrt (1 - D.gap S ^ 2)) := by
  have hDo : ∀ x ∈ Dᗮ, A x ∈ Dᗮ := fun x hx => by
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro u hu
    rw [← hA u x]
    exact hx _ (hD u hu)
  obtain ⟨X, hX⟩ := D.exists_eq_graph_of_gap_lt_one S hdim h0
  have hnX : ‖X‖ = D.gap S / Real.sqrt (1 - D.gap S ^ 2) := by
    rw [D.gap_congr S hX]; exact D.norm_eq_gap_graph_div X
  rw [← hnX]
  -- `A` is bijective on `D`
  have hinj : Function.Injective (A.restrict hD) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h := hlow u u.2
    have hAu : A u = 0 := by
      simpa using congrArg Subtype.val hu
    rw [hAu, norm_zero] at h
    exact Subtype.ext (norm_eq_zero.1 (le_antisymm
      (nonpos_of_mul_nonpos_right h hρ |>.trans_eq rfl) (norm_nonneg _)))
  have hbij : Function.Bijective (A.restrict hD) :=
    ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  set A₁ := LinearEquiv.ofBijective _ hbij with hA₁
  -- the power bounds
  have hlowk : ∀ j (u : E), u ∈ D → ρ ^ j * ‖u‖ ≤ ‖(A ^ j) u‖ := by
    intro j
    induction j with
    | zero => intro u _; simp
    | succ j ih =>
      intro u hu
      rw [show A ^ (j + 1) = A * A ^ j from pow_succ' A j, Module.End.mul_apply]
      have hmem : (A ^ j) u ∈ D := Module.End.pow_apply_mem_of_forall_mem j hD u hu
      calc ρ ^ (j + 1) * ‖u‖ = ρ * (ρ ^ j * ‖u‖) := by ring
        _ ≤ ρ * ‖(A ^ j) u‖ := by gcongr; exact ih u hu
        _ ≤ ‖A ((A ^ j) u)‖ := hlow _ hmem
  have hupk : ∀ j (w : E), w ∈ Dᗮ → ‖(A ^ j) w‖ ≤ r ^ j * ‖w‖ := by
    intro j
    induction j with
    | zero => intro w _; simp
    | succ j ih =>
      intro w hw
      rw [show A ^ (j + 1) = A * A ^ j from pow_succ' A j, Module.End.mul_apply]
      have hmem : (A ^ j) w ∈ Dᗮ := Module.End.pow_apply_mem_of_forall_mem j hDo w hw
      calc ‖A ((A ^ j) w)‖ ≤ r * ‖(A ^ j) w‖ := hup _ hmem
        _ ≤ r * (r ^ j * ‖w‖) := by gcongr; exact ih w hw
        _ = r ^ (j + 1) * ‖w‖ := by ring
  -- the iterated graph
  set Xk : D →ₗ[𝕜] Dᗮ := ((A.restrict hDo) ^ k) ∘ₗ (X : D →ₗ[𝕜] Dᗮ) ∘ₗ
    ((A₁.symm : D →ₗ[𝕜] D) ^ k) with hXk
  have hiter : Krylov.subspaceIterate A S k = D.graph (LinearMap.toContinuousLinearMap Xk) := by
    rw [hX]
    exact Krylov.subspaceIterate_graph hD hDo hbij (X : D →ₗ[𝕜] Dᗮ) k
  rw [D.gap_congr _ hiter, Submodule.gap_graph]
  set Y := LinearMap.toContinuousLinearMap Xk
  have hY : ‖Y‖ ≤ (r / ρ) ^ k * ‖X‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
    -- `v = A₁^{-k} u`
    set v := ((A₁.symm : D →ₗ[𝕜] D) ^ k) u with hv
    have hAv : ((A ^ k) (v : E)) = u := by
      have h1 : ((A.restrict hD) ^ k) v = u := by
        have hBC : (A.restrict hD : Module.End 𝕜 D) * (A₁.symm : D →ₗ[𝕜] D) = 1 := by
          ext x; simp [hA₁]
        have hCB : (A₁.symm : D →ₗ[𝕜] D) * (A.restrict hD : Module.End 𝕜 D) = 1 := by
          ext x; simp [hA₁]
        have hcomm : Commute (A.restrict hD : Module.End 𝕜 D) (A₁.symm : D →ₗ[𝕜] D) :=
          hBC.trans hCB.symm
        rw [hv, ← Module.End.mul_apply, ← hcomm.mul_pow, hBC, one_pow]
        rfl
      rw [← h1, Module.End.pow_restrict k hD]
      rfl
    have hvn : ρ ^ k * ‖(v : E)‖ ≤ ‖(u : E)‖ := by
      rw [← hAv]; exact hlowk k v v.2
    have hYu : (Y u : E) = (A ^ k) ((X v : Dᗮ) : E) := by
      simp only [Y, hXk, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
        ContinuousLinearMap.coe_coe]
      rw [Module.End.pow_restrict k hDo]
      rfl
    rw [← Submodule.norm_coe, hYu, ← Submodule.norm_coe u]
    have hρk : 0 < ρ ^ k := pow_pos hρ k
    calc ‖(A ^ k) ((X v : Dᗮ) : E)‖ ≤ r ^ k * ‖((X v : Dᗮ) : E)‖ := hupk k _ (X v).2
      _ ≤ r ^ k * (‖X‖ * ‖(v : E)‖) := by
          gcongr; rw [Submodule.norm_coe, Submodule.norm_coe]; exact X.le_opNorm v
      _ ≤ r ^ k * (‖X‖ * (‖(u : E)‖ / ρ ^ k)) := by
          gcongr; rw [le_div_iff₀ hρk, mul_comm]; exact hvn
      _ = (r / ρ) ^ k * ‖X‖ * ‖(u : E)‖ := by rw [div_pow]; field_simp
  have hs : 1 ≤ Real.sqrt (1 + ‖Y‖ ^ 2) := by
    rw [Real.one_le_sqrt]; nlinarith [sq_nonneg ‖Y‖]
  calc ‖Y‖ / Real.sqrt (1 + ‖Y‖ ^ 2) ≤ ‖Y‖ := div_le_self (norm_nonneg _) hs
    _ ≤ (r / ρ) ^ k * ‖X‖ := hY

/-- **Subspace iteration with the explicit constant** ([golub2013matrix] Theorem 8.2.2, (8.2.12)):
let `A` be symmetric with an orthonormal eigenbasis `v` (`A (v i) = l i • v i`, `l` real), `J` a
set of indices with `|l j| ≥ ρ > 0` for `j ∈ J` and `|l i| ≤ r` for `i ∉ J`,
`D = span (v '' J)` the dominant invariant subspace, and `S` with `dim S = dim D` and
`d₀ = gap D S < 1`. Then `gap D (A^k S) ≤ (r / ρ)^k d₀ / √(1 - d₀²)`: the `tan Θ` form of the
book's argument, with no CS decomposition, through
`LinearMap.IsSymmetric.gap_subspaceIterate_le_of_invariant` (the eigenbasis gives
`‖A u‖ ≥ ρ ‖u‖` on `D` and `‖A w‖ ≤ r ‖w‖` on `Dᗮ = span (v '' Jᶜ)`). Compare
`Krylov.exists_gap_subspaceIterate_span_image_le` (any diagonalizable `A`, unspecified
constant). -/
theorem gap_subspaceIterate_le (hA : A.IsSymmetric) {ι : Type*} [Fintype ι]
    (v : OrthonormalBasis ι 𝕜 E) {l : ι → ℝ} (hv : ∀ i, A (v i) = (l i : 𝕜) • v i)
    (J : Set ι) {ρ r : ℝ} (hρ : 0 < ρ) (hJ : ∀ j ∈ J, ρ ≤ |l j|) (hJc : ∀ i ∉ J, |l i| ≤ r)
    {S : Submodule 𝕜 E} (hdim : Module.finrank 𝕜 S = Module.finrank 𝕜 (Submodule.span 𝕜 (v '' J)))
    (h0 : (Submodule.span 𝕜 (v '' J)).gap S < 1) (k : ℕ) :
    (Submodule.span 𝕜 (v '' J)).gap (Krylov.subspaceIterate A S k) ≤
      (r / ρ) ^ k * ((Submodule.span 𝕜 (v '' J)).gap S /
        Real.sqrt (1 - (Submodule.span 𝕜 (v '' J)).gap S ^ 2)) := by
  classical
  set D := Submodule.span 𝕜 (v '' J) with hDdef
  have h1 := Krylov.inner_pow_apply_of_eigenbasis v hv 1
  simp only [pow_one] at h1
  -- coordinates vanish off `J` on `D`, on `J` on `Dᗮ`
  have hDc : ∀ u ∈ D, ∀ i ∉ J, (inner 𝕜 (v i) u : 𝕜) = 0 := by
    intro u hu i hi
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨j, hj, rfl⟩
      have hij : i ≠ j := fun h => hi (by rw [h]; exact hj)
      rw [orthonormal_iff_ite.mp v.orthonormal i j]
      simp [hij]
    · simp
    · intro x y _ _ hx hy; rw [inner_add_right, hx, hy, add_zero]
    · intro c x _ hx; rw [inner_smul_right, hx, mul_zero]
  have hDo : ∀ w ∈ Dᗮ, ∀ j ∈ J, (inner 𝕜 (v j) w : 𝕜) = 0 := fun w hw j hj =>
    (Submodule.mem_orthogonal D w).1 hw _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  have hnormA : ∀ u, ‖A u‖ ^ 2 = ∑ i, |l i| ^ 2 * ‖(inner 𝕜 (v i) u : 𝕜)‖ ^ 2 := fun u => by
    rw [← v.sum_sq_norm_inner_right (A u)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1, norm_mul, RCLike.norm_ofReal, mul_pow]
  have hnorm : ∀ u, ‖u‖ ^ 2 = ∑ i, ‖(inner 𝕜 (v i) u : 𝕜)‖ ^ 2 := fun u =>
    (v.sum_sq_norm_inner_right u).symm
  have hD : ∀ x ∈ D, A x ∈ D := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, hj, rfl⟩
      rw [hv]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · simp
    · intro x y _ _ hx hy; rw [map_add]; exact D.add_mem hx hy
    · intro c x _ hx; rw [map_smul]; exact D.smul_mem c hx
  have hlow : ∀ u ∈ D, ρ * ‖u‖ ≤ ‖A u‖ := by
    intro u hu
    refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
    rw [mul_pow, hnorm, hnormA, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : i ∈ J
    · gcongr
      exact (hJ i hi)
    · rw [hDc u hu i hi, norm_zero]; simp
  have hup : ∀ w ∈ Dᗮ, ‖A w‖ ≤ max r 0 * ‖w‖ := by
    intro w hw
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [mul_pow, hnormA, hnorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : i ∈ J
    · rw [hDo w hw i hi, norm_zero]; simp
    · gcongr
      exact (hJc i hi).trans (le_max_left _ _)
  have hcore := gap_subspaceIterate_le_of_invariant hA hD hρ (le_max_right r 0) hlow hup hdim h0 k
  rcases le_or_gt 0 r with hr | hr
  · rwa [max_eq_left hr] at hcore
  -- `r < 0`: every index is in `J`, `D = ⊤ = S`, and both sides vanish
  have hall : ∀ i, i ∈ J := fun i => by
    by_contra hi; exact absurd ((abs_nonneg _).trans (hJc i hi)) (not_le.2 hr)
  have hDtop : D = ⊤ := by
    rw [hDdef, show v '' J = Set.range v by ext x; simp [hall],
      ← OrthonormalBasis.coe_toBasis, v.toBasis.span_eq]
  have hS : S = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hdim, hDtop, finrank_top])
  have hd : D.gap S = 0 := by rw [D.gap_congr S hS, hDtop, Submodule.gap_self]
  rw [hd] at hcore ⊢
  simpa using hcore

end LinearMap.IsSymmetric

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

omit [DecidableEq n] in
/-- **The distance to a graph subspace** ([golub2013matrix] Corollary 7.2.5 and (7.2.6)): in
`EuclideanSpace 𝕜 (m ⊕ n)`, `dist(ran [I; 0], ran [I; P]) ≤ ‖P‖₂` (and `‖P‖₂ ≤ ‖P‖_F`,
`Matrix.l2_opNorm_le_frobenius_norm`). The two subspaces have equal dimension, so the gap is the
one-sided `‖P_{K⊥} P_G‖`; a vector of `G` is `(x, P x)`, whose component orthogonal to
`K = ran [I; 0]` is `(0, P x)`, of norm at most `‖P‖₂ ‖x‖ ≤ ‖P‖₂ ‖(x, P x)‖`. The exact value is
`‖P‖₂ / √(1 + ‖P‖₂²)` (`Submodule.gap_graph`). -/
theorem gap_range_fromRows_le (P : Matrix n m 𝕜) :
    (LinearMap.range (toEuclideanLin (fromRows (1 : Matrix m m 𝕜) (0 : Matrix n m 𝕜)))).gap
        (LinearMap.range (toEuclideanLin (fromRows (1 : Matrix m m 𝕜) P))) ≤ lpOpNorm 2 P := by
  set K := LinearMap.range (toEuclideanLin (fromRows (1 : Matrix m m 𝕜) (0 : Matrix n m 𝕜)))
  set G := LinearMap.range (toEuclideanLin (fromRows (1 : Matrix m m 𝕜) P))
  have happ : ∀ (Q : Matrix n m 𝕜) (x : EuclideanSpace 𝕜 m),
      toEuclideanLin (fromRows 1 Q) x =
        WithLp.toLp 2 (Sum.elim (WithLp.ofLp x) (Q *ᵥ WithLp.ofLp x)) :=
    fun Q x => by rw [toEuclideanLin_apply, fromRows_mulVec, one_mulVec]
  have hinj : ∀ Q : Matrix n m 𝕜, Function.Injective (toEuclideanLin (fromRows 1 Q)) :=
    fun Q x y hxy => by
      rw [happ, happ] at hxy
      have := congrArg (fun v => (WithLp.ofLp v) ∘ Sum.inl) hxy
      exact WithLp.ofLp_injective 2 (by simpa using this)
  have hdim : Module.finrank 𝕜 G = Module.finrank 𝕜 K := by
    rw [LinearMap.finrank_range_of_inj (hinj P), LinearMap.finrank_range_of_inj (hinj 0)]
  rw [Submodule.gap_comm, Submodule.gap_eq_norm_orthogonal_mul_of_finrank_eq G K hdim]
  refine ContinuousLinearMap.opNorm_le_bound _ (lpOpNorm_nonneg _ _) fun z => ?_
  obtain ⟨x, hx⟩ := G.starProjection_apply_mem z
  rw [mul_apply_eq_comp]
  -- the decomposition `(x, P x) = (x, 0) + (0, P x)`
  set y : EuclideanSpace 𝕜 (m ⊕ n) := WithLp.toLp 2 (Sum.elim 0 (P *ᵥ WithLp.ofLp x))
  have hsplit : (G.starProjection z : EuclideanSpace 𝕜 (m ⊕ n)) =
      toEuclideanLin (fromRows 1 (0 : Matrix n m 𝕜)) x + y := by
    rw [← hx, happ, happ]
    ext (i | i) <;> simp [y]
  have hyK : y ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨u, rfl⟩
    rw [happ, EuclideanSpace.inner_eq_star_dotProduct]
    simp [y, dotProduct, Fintype.sum_sum_type]
  have hK : toEuclideanLin (fromRows 1 (0 : Matrix n m 𝕜)) x ∈ K := ⟨x, rfl⟩
  have hproj : Kᗮ.starProjection (G.starProjection z) = y := by
    rw [hsplit, map_add, (Submodule.starProjection_apply_eq_zero_iff Kᗮ).2
      (K.le_orthogonal_orthogonal hK), zero_add, Submodule.starProjection_eq_self_iff.2 hyK]
  rw [hproj]
  -- norms
  have hy : ‖y‖ = ‖WithLp.toLp 2 (P *ᵥ WithLp.ofLp x)‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp [y, Fintype.sum_sum_type]
  have hxg : ‖x‖ ≤ ‖G.starProjection z‖ := by
    rw [← hx, happ, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hPx : ‖WithLp.toLp 2 (P *ᵥ WithLp.ofLp x)‖ ≤ lpOpNorm 2 P * ‖x‖ :=
    (lpCLM 2 P).le_opNorm x
  calc ‖y‖ ≤ lpOpNorm 2 P * ‖x‖ := hy ▸ hPx
    _ ≤ lpOpNorm 2 P * ‖G.starProjection z‖ := mul_le_mul_of_nonneg_left hxg (lpOpNorm_nonneg _ _)
    _ ≤ lpOpNorm 2 P * ‖z‖ :=
        mul_le_mul_of_nonneg_left (G.norm_starProjection_apply_le z) (lpOpNorm_nonneg _ _)

end Matrix
