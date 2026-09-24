/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Schur` (once the real Schur form is there) for the
generalized real Schur form, `Mathlib.Topology.Instances.Matrix` for the compactness of the
orthogonal group.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Instances.Matrix
import Numlib.Eigen.Pencil
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.RealSchur

/-!
# The generalized real Schur form of a matrix pair

For real square matrices `A`, `B` of the same size there are orthogonal `U`, `Z` with `Uᵀ A Z`
quasi upper triangular (block upper triangular with diagonal blocks of size `1` or `2`) and
`Uᵀ B Z` upper triangular (`Matrix.exists_generalizedRealSchur`). This is the real form of the
generalized Schur decomposition of a pencil ([golub1989matrix] Theorem 7.7.2;
[quarteroni2000numerical] §5.9.1, the statement after Property 5.10), and it holds for *every*
pair — no regularity of the pencil `A - λ B` is needed.

## The proof

For a nonsingular `B` the statement reduces to the real Schur form of `B⁻¹ A`
(`Matrix.exists_orthogonal_conj_quasiUpperTriangular`) and a QR factorization of `B Z`
(`Matrix.exists_unitary_mul_isUpperTriangular`): `Uᵀ B Z = R` is the triangular factor and
`Uᵀ A Z = R (Zᵀ B⁻¹ A Z)` is triangular times quasi-triangular
(`Matrix.exists_generalizedRealSchur_of_isUnit`).

The general case is a limiting argument rather than the deflating-subspace induction of
Golub–Van Loan. `B + ε I` is nonsingular for all small `ε > 0`
(`Matrix.exists_forall_isUnit_det_add_smul_one`: `det (B + t I)` is the characteristic
polynomial of `-B` at `t`), so the pairs `(A, B + ε_k I)`, `ε_k → 0`, have generalized Schur
forms `(U_k, Z_k, p_k)`. Infinitely many `k` share the strict order relation `p_k j < p_k i`
(finitely many relations on `Fin n`), so along those `k` the block-triangularity is for one fixed
pattern; and the orthogonal group is compact (`Matrix.isCompact_orthogonalGroup`: closed, with
entries in `[-1, 1]`), so a further subsequence has `(U_k, Z_k) → (U, Z)`. Each vanishing entry
of `Uᵀ A Z` is a closed condition; and the strictly lower entries of `U_kᵀ B Z_k` equal
`-ε_k (U_kᵀ Z_k)_{ij}`, which tend to `0`.

The same argument gives the complex generalized Schur form (both factors triangular) of an
arbitrary, possibly singular, complex pair from the regular case
`Matrix.exists_unitary_pencil_isUpperTriangular` of `Numlib/Eigen/Pencil`: this is
`Matrix.exists_generalizedSchur` ([golub2013matrix] Theorem 7.7.1), with the compactness of the
unitary group over any `RCLike` field, `Matrix.isCompact_unitaryGroup`.

## References

[golub1989matrix] §7.7; [quarteroni2000numerical] §5.9.1.
-/

open Filter Topology Matrix

namespace Matrix

variable {n : ℕ}

/-! ### The nonsingular case -/

/-- **The generalized real Schur form of a pencil with nonsingular `B`**: take `Z` from the real
Schur form of `B⁻¹ A` (`Matrix.exists_orthogonal_conj_quasiUpperTriangular`), so that
`Zᵀ B⁻¹ A Z = T` is quasi upper triangular, and `U` from a QR factorization `B Z = U R`
(`Matrix.exists_unitary_mul_isUpperTriangular`); then `Uᵀ B Z = R` is upper triangular and
`Uᵀ A Z = R T` is quasi upper triangular, a triangular matrix times a quasi triangular one. -/
theorem exists_generalizedRealSchur_of_isUnit (A : Matrix (Fin n) (Fin n) ℝ)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : IsUnit B.det) :
    ∃ U ∈ orthogonalGroup (Fin n) ℝ, ∃ Z ∈ orthogonalGroup (Fin n) ℝ, ∃ p : Fin n → ℕ,
      Monotone p ∧ (∀ k, (Finset.univ.filter fun i => p i = k).card ≤ 2) ∧
        (Uᵀ * A * Z).BlockTriangular p ∧ (Uᵀ * B * Z).IsUpperTriangular := by
  obtain ⟨Z, hZ, p, hmono, hcard, htri⟩ := exists_orthogonal_conj_quasiUpperTriangular (B⁻¹ * A)
  obtain ⟨V, hV, hR⟩ := exists_unitary_mul_isUpperTriangular (B * Z)
  have hZZ : Z * Zᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hZ
  have hVU : Vᵀ ∈ orthogonalGroup (Fin n) ℝ := by
    rw [mem_orthogonalGroup_iff', transpose_transpose]
    exact (mem_orthogonalGroup_iff _ ℝ).1 hV
  refine ⟨Vᵀ, hVU, Z, hZ, p, hmono, hcard, ?_, ?_⟩
  swap
  · rw [transpose_transpose, Matrix.mul_assoc]; exact hR
  have hAZ : (V * (B * Z)) * (Zᵀ * (B⁻¹ * A) * Z) = Vᵀᵀ * A * Z := by
    rw [transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Z Zᵀ, hZZ, Matrix.one_mul, ← Matrix.mul_assoc B B⁻¹,
      Matrix.mul_nonsing_inv B hB, Matrix.one_mul]
  rw [← hAZ]
  refine BlockTriangular.mul (fun i j hij => hR ?_) htri
  by_contra hji
  exact absurd (hmono (not_lt.1 hji)) (not_le.2 hij)

/-! ### Compactness of the orthogonal group -/

/-- The unitary group is a closed subset of the matrices: it is the preimage of `1` under the
continuous map `U ↦ star U * U`. -/
theorem isClosed_unitaryGroup {m 𝕜 : Type*} [Fintype m] [DecidableEq m] [RCLike 𝕜] :
    IsClosed ((unitaryGroup m 𝕜 : Submonoid _) : Set (Matrix m m 𝕜)) := by
  have : ((unitaryGroup m 𝕜 : Submonoid _) : Set (Matrix m m 𝕜)) =
      (fun U : Matrix m m 𝕜 => star U * U) ⁻¹' {1} := by
    ext U
    simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_singleton_iff]
    exact mem_unitaryGroup_iff'
  rw [this]
  exact isClosed_singleton.preimage (continuous_star.matrix_mul continuous_id)

/-- The entries of a unitary matrix have norm at most `1`: the columns are unit vectors. -/
theorem norm_apply_le_one_of_mem_unitaryGroup {m 𝕜 : Type*} [Fintype m] [DecidableEq m]
    [RCLike 𝕜] {U : Matrix m m 𝕜} (hU : U ∈ unitaryGroup m 𝕜) (i j : m) : ‖U i j‖ ≤ 1 := by
  have h := congrFun (congrFun (mem_unitaryGroup_iff'.1 hU) j) j
  rw [mul_apply, one_apply_eq] at h
  simp only [star_apply, RCLike.star_def] at h
  have hsum : ∑ k, ‖U k j‖ ^ 2 = 1 := by
    have : ((∑ k, ‖U k j‖ ^ 2 : ℝ) : 𝕜) = 1 := by
      push_cast
      rw [← h]
      exact Finset.sum_congr rfl fun k _ => (RCLike.conj_mul _).symm
    exact_mod_cast this
  have hsq : ‖U i j‖ ^ 2 ≤ 1 := hsum ▸
    Finset.single_le_sum (f := fun k => ‖U k j‖ ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith [norm_nonneg (U i j)]

/-- **The unitary group is compact**, over `ℝ` or `ℂ`: closed, and contained in the product of
closed unit balls, one for each entry. `Matrix.isCompact_orthogonalGroup` is its real case. -/
theorem isCompact_unitaryGroup {m 𝕜 : Type*} [Fintype m] [DecidableEq m] [RCLike 𝕜] :
    IsCompact ((unitaryGroup m 𝕜 : Submonoid _) : Set (Matrix m m 𝕜)) := by
  have hcube : IsCompact (Set.pi Set.univ fun _ : m => Set.pi Set.univ fun _ : m =>
      Metric.closedBall (0 : 𝕜) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hcube.of_isClosed_subset isClosed_unitaryGroup fun U hU => ?_
  simp only [Set.mem_pi, Set.mem_univ, forall_const, Metric.mem_closedBall, dist_zero_right]
  exact fun i j => norm_apply_le_one_of_mem_unitaryGroup hU i j

/-- The orthogonal group is a closed subset of the matrices. -/
theorem isClosed_orthogonalGroup :
    IsClosed ((orthogonalGroup (Fin n) ℝ : Submonoid _) : Set (Matrix (Fin n) (Fin n) ℝ)) := by
  have : ((orthogonalGroup (Fin n) ℝ : Submonoid _) : Set (Matrix (Fin n) (Fin n) ℝ)) =
      (fun U : Matrix (Fin n) (Fin n) ℝ => Uᵀ * U) ⁻¹' {1} := by
    ext U
    simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_singleton_iff]
    exact mem_orthogonalGroup_iff' (Fin n) ℝ
  rw [this]
  exact isClosed_singleton.preimage (continuous_id.matrix_transpose.matrix_mul continuous_id)

/-- The entries of an orthogonal matrix are bounded by `1`: the columns are unit vectors. -/
theorem abs_apply_le_one_of_mem_orthogonalGroup {U : Matrix (Fin n) (Fin n) ℝ}
    (hU : U ∈ orthogonalGroup (Fin n) ℝ) (i j : Fin n) : |U i j| ≤ 1 := by
  have h := congrFun (congrFun ((mem_orthogonalGroup_iff' (Fin n) ℝ).1 hU) j) j
  rw [mul_apply, one_apply_eq] at h
  have hsq : U i j ^ 2 ≤ 1 := by
    rw [← h]
    have : U i j ^ 2 = Uᵀ j i * U i j := by rw [transpose_apply, sq]
    rw [this]
    exact Finset.single_le_sum (f := fun k => Uᵀ j k * U k j)
      (fun k _ => by rw [transpose_apply]; exact mul_self_nonneg _) (Finset.mem_univ i)
  exact abs_le_one_iff_mul_self_le_one.2 (by rw [← sq]; exact hsq)

/-- **The orthogonal group is compact**, the real case of `Matrix.isCompact_unitaryGroup`. -/
theorem isCompact_orthogonalGroup :
    IsCompact ((orthogonalGroup (Fin n) ℝ : Submonoid _) : Set (Matrix (Fin n) (Fin n) ℝ)) :=
  isCompact_unitaryGroup

/-! ### The general case, by perturbation -/

/-- `B + t I` is nonsingular for all small real `t > 0`, over `ℝ` or `ℂ`: `det (B + t I)` is the
characteristic polynomial of `-B` at `t`, which has finitely many roots. -/
theorem exists_forall_isUnit_det_add_smul_one {𝕜 : Type*} [RCLike 𝕜]
    (B : Matrix (Fin n) (Fin n) 𝕜) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → IsUnit (B + t • (1 : Matrix (Fin n) (Fin n) 𝕜)).det := by
  classical
  have hdet : ∀ t : ℝ, (B + t • (1 : Matrix (Fin n) (Fin n) 𝕜)).det =
      (-B).charpoly.eval (t : 𝕜) := by
    intro t
    rw [eval_charpoly, sub_neg_eq_add, add_comm]
    congr 2
    ext i j
    simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply,
      RCLike.real_smul_eq_coe_mul]
  have hne : (-B).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  set S := ((-B).charpoly.roots.toFinset.image RCLike.re).filter fun t => 0 < t with hS
  refine ⟨if h : S.Nonempty then S.min' h else 1, ?_, fun t ht0 htδ => ?_⟩
  · split_ifs with h
    · exact (Finset.mem_filter.1 (S.min'_mem h)).2
    · exact one_pos
  · rw [isUnit_iff_ne_zero, hdet]
    intro hroot
    have htS : t ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_image]
      refine ⟨⟨(t : 𝕜), ?_, RCLike.ofReal_re t⟩, ht0⟩
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
      exact hroot
    have hne' : S.Nonempty := ⟨t, htS⟩
    rw [dite_eq_left hne'] at htδ
    exact absurd (S.min'_le t htS) (not_le.2 htδ)

/-- **The generalized real Schur form of an arbitrary real pair** ([quarteroni2000numerical]
§5.9.1, the statement after Property 5.10; Golub–Van Loan Theorem 7.7.2): for real `A`, `B`,
without any regularity hypothesis on the pencil, there are orthogonal `U`, `Z` with `Uᵀ A Z`
quasi upper triangular — block triangular for a monotone block index `p : Fin n → ℕ` with
blocks of size at most `2` — and `Uᵀ B Z` upper triangular.

The nonsingular case is `Matrix.exists_generalizedRealSchur_of_isUnit`. In general `B + ε I` is
nonsingular for all small `ε > 0`, giving orthogonal `U_ε`, `Z_ε` and a pattern `p_ε`; along a
sequence `ε_k → 0`, infinitely many `k` share the relation `p_ε j < p_ε i`, and the orthogonal
group being compact (`Matrix.isCompact_orthogonalGroup`) a further subsequence has `U_k → U`,
`Z_k → Z`. The limits are orthogonal (a closed condition), `Uᵀ A Z` is block triangular for the
common pattern (each vanishing entry is a closed condition), and
`Uᵀ B Z = lim (U_kᵀ (B + ε_k I) Z_k - ε_k U_kᵀ Z_k)` is upper triangular because the first
term is and the second tends to zero. -/
theorem exists_generalizedRealSchur (A B : Matrix (Fin n) (Fin n) ℝ) :
    ∃ U ∈ orthogonalGroup (Fin n) ℝ, ∃ Z ∈ orthogonalGroup (Fin n) ℝ, ∃ p : Fin n → ℕ,
      Monotone p ∧ (∀ k, (Finset.univ.filter fun i => p i = k).card ≤ 2) ∧
        (Uᵀ * A * Z).BlockTriangular p ∧ (Uᵀ * B * Z).IsUpperTriangular := by
  classical
  obtain ⟨δ, hδ, hδunit⟩ := exists_forall_isUnit_det_add_smul_one B
  -- the perturbations `ε_k = δ / (k + 2)`
  set ε : ℕ → ℝ := fun k => δ / ((k : ℝ) + 2) with hε
  have hεpos : ∀ k, 0 < ε k := fun k => by positivity
  have hεlt : ∀ k, ε k < δ := fun k => by
    rw [hε]; dsimp only
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hεtend : Tendsto ε atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => ((k : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa [hε, div_eq_mul_inv] using h1.inv_tendsto_atTop.const_mul δ
  -- the generalized Schur forms of the perturbed pencils
  have hstep : ∀ k, ∃ U ∈ orthogonalGroup (Fin n) ℝ, ∃ Z ∈ orthogonalGroup (Fin n) ℝ,
      ∃ p : Fin n → ℕ, Monotone p ∧ (∀ m, (Finset.univ.filter fun i => p i = m).card ≤ 2) ∧
        (Uᵀ * A * Z).BlockTriangular p ∧ (Uᵀ * (B + ε k • 1) * Z).IsUpperTriangular :=
    fun k => exists_generalizedRealSchur_of_isUnit A (hδunit (ε k) (hεpos k) (hεlt k))
  choose U hU Z hZ p hmono hcard htri hupp using hstep
  -- infinitely many `k` share the relation `p_k j < p_k i`
  obtain ⟨R, hR⟩ := Finite.exists_infinite_fiber
    (fun k => fun i j : Fin n => decide (p k j < p k i))
  have hS : (Set.ofPred fun k => (fun i j : Fin n => decide (p k j < p k i)) = R).Infinite := by
    rw [← Set.infinite_coe_iff]
    exact hR
  set φ := Nat.nth fun k => (fun i j : Fin n => decide (p k j < p k i)) = R with hφ
  have hφmono : StrictMono φ := Nat.nth_strictMono hS
  have hφmem : ∀ k, (fun i j : Fin n => decide (p (φ k) j < p (φ k) i)) = R :=
    Nat.nth_mem_of_infinite hS
  have hrel : ∀ k i j, p (φ k) j < p (φ k) i ↔ p (φ 0) j < p (φ 0) i := by
    intro k i j
    have h1 := congrFun (congrFun (hφmem k) i) j
    have h2 := congrFun (congrFun (hφmem 0) i) j
    rw [← decide_eq_true_iff (p := p (φ k) j < p (φ k) i), ← decide_eq_true_iff
      (p := p (φ 0) j < p (φ 0) i), h1, h2]
  -- a convergent subsequence of `(U_k, Z_k)`
  have hK : IsCompact (((orthogonalGroup (Fin n) ℝ : Submonoid _) : Set (Matrix (Fin n) (Fin n) ℝ))
      ×ˢ ((orthogonalGroup (Fin n) ℝ : Submonoid _) : Set (Matrix (Fin n) (Fin n) ℝ))) :=
    (isCompact_orthogonalGroup (n := n)).prod (isCompact_orthogonalGroup (n := n))
  have : FirstCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℝ))
  obtain ⟨⟨Ul, Zl⟩, hUZ, ψ, hψ, hlim⟩ :=
    hK.tendsto_subseq (x := fun k => (U (φ k), Z (φ k))) fun k => ⟨hU _, hZ _⟩
  have hχtend : Tendsto (fun k => φ (ψ k)) atTop atTop := (hφmono.comp hψ).tendsto_atTop
  have hεlim : Tendsto (fun k => ε (φ (ψ k))) atTop (𝓝 0) := hεtend.comp hχtend
  -- the entries of `Uᵀ M Z` are continuous in `(U, Z)`
  have hcont : ∀ (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n), Continuous
      fun q : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ => (q.1ᵀ * M * q.2) i j :=
    fun M i j => ((continuous_fst.matrix_transpose.matrix_mul continuous_const).matrix_mul
      continuous_snd).matrix_elem i j
  have hent : ∀ (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n),
      Tendsto (fun k => ((U (φ (ψ k)))ᵀ * M * Z (φ (ψ k))) i j) atTop
        (𝓝 ((Ulᵀ * M * Zl) i j)) := by
    intro M i j
    have h := ((hcont M i j).tendsto (Ul, Zl)).comp hlim
    simpa only [Function.comp_def] using h
  refine ⟨Ul, hUZ.1, Zl, hUZ.2, p (φ 0), hmono _, hcard _, fun i j hij => ?_, fun i j hij => ?_⟩
  · -- the block triangular entries vanish along the subsequence
    have h := hent A i j
    have hzero : ∀ k, ((U (φ (ψ k)))ᵀ * A * Z (φ (ψ k))) i j = 0 := fun k =>
      htri (φ (ψ k)) ((hrel (ψ k) i j).2 hij)
    simp only [hzero] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  · -- the strictly lower entries of `Uᵀ B Z` are limits of `-ε_k (U_kᵀ Z_k) i j`
    have h := hent B i j
    set I : Matrix (Fin n) (Fin n) ℝ := 1 with hI
    have hval : ∀ k, ((U (φ (ψ k)))ᵀ * B * Z (φ (ψ k))) i j =
        -(ε (φ (ψ k)) * ((U (φ (ψ k)))ᵀ * I * Z (φ (ψ k))) i j) := by
      intro k
      have h := hupp (φ (ψ k)) hij
      have hsplit : (U (φ (ψ k)))ᵀ * (B + ε (φ (ψ k)) • I) * Z (φ (ψ k)) =
          (U (φ (ψ k)))ᵀ * B * Z (φ (ψ k)) + ε (φ (ψ k)) • ((U (φ (ψ k)))ᵀ * I * Z (φ (ψ k))) := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
      rw [hsplit, add_apply, smul_apply, smul_eq_mul] at h
      linarith
    have hlim2 : Tendsto (fun k => -(ε (φ (ψ k)) * ((U (φ (ψ k)))ᵀ * I * Z (φ (ψ k))) i j)) atTop
        (𝓝 (-(0 * (Ulᵀ * I * Zl) i j))) :=
      (hεlim.mul (hent I i j)).neg
    simp only [hval, zero_mul, neg_zero] at h hlim2
    exact tendsto_nhds_unique h hlim2


/-- **The complex generalized Schur form of an arbitrary pair** ([golub2013matrix] Theorem 7.7.1,
existence): for square `A`, `B` over an algebraically closed `RCLike` field (that is, over `ℂ`),
with no regularity hypothesis on the pencil, there are unitary `U`, `Z` with `Uᴴ A Z` and `Uᴴ B Z`
both upper triangular. The regular case is `Matrix.exists_unitary_pencil_isUpperTriangular`; in
general `B + ε I` is nonsingular for all small `ε > 0`, so the pencils `(A, B + ε_k I)` are regular,
the unitary group is compact (`Matrix.isCompact_unitaryGroup`), and a convergent subsequence of the
`(U_k, Z_k)` gives the form in the limit: vanishing entries are closed conditions, and the strictly
lower entries of `U_kᴴ B Z_k` are `-ε_k (U_kᴴ Z_k)_{ij} → 0`. The argument of
`Matrix.exists_generalizedRealSchur`, without the block pattern. -/
theorem exists_generalizedSchur {𝕜 : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜]
    (A B : Matrix (Fin n) (Fin n) 𝕜) :
    ∃ U ∈ unitaryGroup (Fin n) 𝕜, ∃ Z ∈ unitaryGroup (Fin n) 𝕜,
      (star U * A * Z).IsUpperTriangular ∧ (star U * B * Z).IsUpperTriangular := by
  classical
  obtain ⟨δ, hδ, hδunit⟩ := exists_forall_isUnit_det_add_smul_one B
  set ε : ℕ → ℝ := fun k => δ / ((k : ℝ) + 2) with hε
  have hεpos : ∀ k, 0 < ε k := fun k => by positivity
  have hεlt : ∀ k, ε k < δ := fun k => by
    rw [hε]; dsimp only
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hεtend : Tendsto ε atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => ((k : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa [hε, div_eq_mul_inv] using h1.inv_tendsto_atTop.const_mul δ
  -- the generalized Schur forms of the perturbed, regular, pencils
  have hstep : ∀ k, ∃ U ∈ unitaryGroup (Fin n) 𝕜, ∃ Z ∈ unitaryGroup (Fin n) 𝕜,
      (star U * A * Z).IsUpperTriangular ∧
        (star U * (B + ε k • (1 : Matrix (Fin n) (Fin n) 𝕜)) * Z).IsUpperTriangular :=
    fun k => exists_unitary_pencil_isUpperTriangular
      (isRegularPencil_of_isUnit A (hδunit (ε k) (hεpos k) (hεlt k)))
  choose U hU Z hZ hAtri hBtri using hstep
  -- a convergent subsequence of `(U_k, Z_k)`
  have hK : IsCompact (((unitaryGroup (Fin n) 𝕜 : Submonoid _) : Set (Matrix (Fin n) (Fin n) 𝕜))
      ×ˢ ((unitaryGroup (Fin n) 𝕜 : Submonoid _) : Set (Matrix (Fin n) (Fin n) 𝕜))) :=
    isCompact_unitaryGroup.prod isCompact_unitaryGroup
  have : FirstCountableTopology (Matrix (Fin n) (Fin n) 𝕜) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → 𝕜))
  obtain ⟨⟨Ul, Zl⟩, hUZ, ψ, hψ, hlim⟩ :=
    hK.tendsto_subseq (x := fun k => (U k, Z k)) fun k => ⟨hU k, hZ k⟩
  have hεlim : Tendsto (fun k => ((ε (ψ k) : ℝ) : 𝕜)) atTop (𝓝 0) := by
    have h := ((RCLike.continuous_ofReal (K := 𝕜)).tendsto 0).comp
      (hεtend.comp hψ.tendsto_atTop)
    simpa [Function.comp_def] using h
  -- the entries of `Uᴴ M Z` are continuous in `(U, Z)`
  have hcont : ∀ (M : Matrix (Fin n) (Fin n) 𝕜) (i j : Fin n), Continuous
      fun q : Matrix (Fin n) (Fin n) 𝕜 × Matrix (Fin n) (Fin n) 𝕜 => (star q.1 * M * q.2) i j :=
    fun M i j => ((continuous_fst.star.matrix_mul continuous_const).matrix_mul
      continuous_snd).matrix_elem i j
  have hent : ∀ (M : Matrix (Fin n) (Fin n) 𝕜) (i j : Fin n),
      Tendsto (fun k => (star (U (ψ k)) * M * Z (ψ k)) i j) atTop
        (𝓝 ((star Ul * M * Zl) i j)) := by
    intro M i j
    have h := ((hcont M i j).tendsto (Ul, Zl)).comp hlim
    simpa only [Function.comp_def] using h
  refine ⟨Ul, hUZ.1, Zl, hUZ.2, fun i j hij => ?_, fun i j hij => ?_⟩
  · have h := hent A i j
    have hzero : ∀ k, (star (U (ψ k)) * A * Z (ψ k)) i j = 0 := fun k => hAtri (ψ k) hij
    simp only [hzero] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  · have h := hent B i j
    set I : Matrix (Fin n) (Fin n) 𝕜 := 1 with hI
    have hval : ∀ k, (star (U (ψ k)) * B * Z (ψ k)) i j =
        -(((ε (ψ k) : ℝ) : 𝕜) * (star (U (ψ k)) * I * Z (ψ k)) i j) := by
      intro k
      have h := hBtri (ψ k) hij
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, add_apply,
        smul_apply, RCLike.real_smul_eq_coe_mul] at h
      linear_combination h
    have hlim2 : Tendsto (fun k => -(((ε (ψ k) : ℝ) : 𝕜) * (star (U (ψ k)) * I * Z (ψ k)) i j))
        atTop (𝓝 (-(0 * (star Ul * I * Zl) i j))) :=
      (hεlim.mul (hent I i j)).neg
    simp only [hval, zero_mul, neg_zero] at h hlim2
    exact tendsto_nhds_unique h hlim2

end Matrix
