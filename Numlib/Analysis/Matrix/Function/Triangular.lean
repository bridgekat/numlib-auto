/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.Interval.Finset.Basic
import Numlib.Analysis.Matrix.Function.Basic
import Numlib.LinearAlgebra.Matrix.Triangular

/-!
# Functions of triangular matrices

Let $T$ be a block upper triangular matrix, and let $f(T)$ be given by the primary functional
calculus. Then $f(T)$ is block upper triangular, and when the minimal polynomial of $T$ splits, the
diagonal blocks of $f(T)$ are $f(T_{kk})$. The commutation $f(T) T = T f(T)$ gives the Parlett
recurrence (9.1.11) of [golub2013matrix] for the entries of $f(T)$ when $T$ is upper triangular, and
its block form (9.1.12), a Sylvester equation for the off-diagonal blocks. The module also proves
the divided-difference formula of Theorem 9.1.4 of [golub2013matrix]: for upper triangular $T$ and
$i < j$,
$$f(T)_{ij} = \sum_{s \in S_{ij}} t_{s_0 s_1} t_{s_1 s_2} \cdots t_{s_{k-1} s_k}\,
  f[\lambda_{s_0}, \dots, \lambda_{s_k}],$$
where $S_{ij}$ is the set of strictly increasing index sequences $i = s_0 < s_1 < \dots < s_k = j$,
$\lambda_r = t_{rr}$, and the divided differences are confluent at repeated eigenvalues. The
presentation follows [golub2013matrix], §9.1.4–9.1.5, which cites Descloux, Davis and Van Loan for
the divided-difference formula.

## Main definitions

* `Matrix.path`: the index sequence $i, s, j$ for a set $s$ of interior indices.
* `Matrix.pathProd`: the product of the entries of $T$ along consecutive pairs of a list of indices.

## Main results

* `Matrix.BlockTriangular.pfc`: $f(T)$ is block triangular with $T$.
* `Matrix.BlockTriangular.toBlock_pfc`: if the minimal polynomial of $T$ splits, then the diagonal
  blocks of $f(T)$ are $f(T_{kk})$.
* `Matrix.pfc_apply_eq_parlett`: the Parlett recurrence (9.1.11).
* `Matrix.BlockTriangular.pfc_sylvester`: the block Parlett equations (9.1.12).
* `Matrix.pow_succ_apply_eq_sum_pathProd`: the entries of the powers of a strictly upper triangular
  matrix are sums of products along paths.
* `Matrix.pow_apply_eq_sum_pathProd`, `Matrix.aeval_apply_eq_sum_pathProd`: the divided-difference
  formula for $T^m$ and for $p(T)$ with a polynomial $p$.
* `Matrix.pfc_apply_self_of_isUpperTriangular`: $f(T)_{ii} = f(t_{ii})$ for upper triangular $T$.
* `Matrix.pfc_apply_eq_sum_divDiff`: the divided-difference formula of Theorem 9.1.4 of
  [golub2013matrix].

## Proof outline

The divided-difference formula is proved by expanding the powers of $T$ along paths
(`Matrix.pow_apply_eq_sum_pathProd`). The walks are grouped by their first step, and the loops at
the diagonal sum to the divided difference of $z \mapsto z^m$ (`Hermite.divDiff_X_pow`). By
linearity the formula extends to polynomials, and so to the Hermite interpolant that computes
$f(T)$.

## Implementation notes

* Triangularity is Mathlib's `Matrix.BlockTriangular T b`: $T_{ij} = 0$ when $b(j) < b(i)$, so $T$
  is block upper triangular. Upper triangularity is `Matrix.IsUpperTriangular`, the case
  $b = \mathrm{id}$.
* A strictly increasing sequence $i = s_0 < \dots < s_k = j$ is encoded by the finset
  `s ⊆ Finset.Ioo i j` of its interior indices. `Matrix.path i s j` is the ordered list, and
  `Matrix.pathProd T l` is the product of the entries of $T$ along consecutive pairs of `l`. The
  diagonal entries along a path, `(path i s j).map fun k => T k k`, are the nodes of the divided
  difference.
* The divided difference is `Hermite.divDiff`, defined through the jets of $f$. So the formula needs
  no smoothness hypothesis on $f$.
-/

open Polynomial Hermite Finset

namespace Matrix

section BlockTriangular

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
  {α : Type*} [LinearOrder α] {b : n → α}

/-- Let $T$ be block triangular for the block map $b$. Then every polynomial $p(T)$ in $T$ is block
triangular for $b$. -/
theorem BlockTriangular.aeval {T : Matrix n n 𝕜} (hT : T.BlockTriangular b) (p : 𝕜[X]) :
    (aeval T p).BlockTriangular b := by
  have h := aeval_subalgebra_coe p (blockTriangularSubalgebra 𝕜 𝕜 b) ⟨T, hT⟩
  rw [← h]
  exact (Polynomial.aeval (⟨T, hT⟩ : blockTriangularSubalgebra 𝕜 𝕜 b) p).2

/-- **$f(T)$ is block triangular with $T$.** Let $\mathbb{K}$ be a nontrivially normed field, let
$T \in \mathbb{K}^{n \times n}$ be block triangular for a block map $b$ into a linearly ordered
set, and let $f \colon \mathbb{K} \to \mathbb{K}$. Then $f(T)$ is block triangular for $b$. This
is in [golub2013matrix], §9.1.5.

The proof uses that $f(T)$ is a polynomial in $T$. -/
theorem BlockTriangular.pfc {T : Matrix n n 𝕜} (hT : T.BlockTriangular b) (f : 𝕜 → 𝕜) :
    (_root_.pfc f T).BlockTriangular b := by
  classical
  rw [pfc_def]
  exact hT.aeval _

/-- Let $T$ be block triangular for the block map $b$, and let $p$ be a polynomial. Then for every
block index $k$, the diagonal block of $p(T)$ with index $k$ is $p(T_{kk})$. -/
theorem BlockTriangular.toBlock_aeval {T : Matrix n n 𝕜} (hT : T.BlockTriangular b) (k : α)
    (p : 𝕜[X]) :
    (Polynomial.aeval T p).toBlock (b · = k) (b · = k) =
      Polynomial.aeval (T.toBlock (b · = k) (b · = k)) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, ← hp, ← hq]
    ext i j
    simp
  | monomial m c =>
    rw [aeval_monomial, aeval_monomial, (blockTriangular_algebraMap c).toBlock_mul (hT.pow m),
      hT.toBlock_pow]
    congr 1
    ext i j
    by_cases h : (i : n) = j
    · obtain rfl : i = j := Subtype.ext h
      simp [algebraMap_eq_diagonal]
    · have h' : i ≠ j := fun e => h (congrArg Subtype.val e)
      simp [algebraMap_eq_diagonal, diagonal_apply_ne _ h, diagonal_apply_ne _ h']

/-- **The diagonal blocks of $f(T)$ are $f$ of the diagonal blocks.** Let $\mathbb{K}$ be a
nontrivially normed field, let $T \in \mathbb{K}^{n \times n}$ be block triangular for a block
map $b$ into a linearly ordered set, and suppose that the minimal polynomial of $T$ splits over
$\mathbb{K}$. Then for every block index $k$ and every $f \colon \mathbb{K} \to \mathbb{K}$,
$$f(T)_{kk} = f(T_{kk}).$$
This is $F_{kk} = f(T_{kk})$ in [golub2013matrix], §9.1.5.

The block $T_{kk}$ is `T.toBlock (b · = k) (b · = k)`. -/
theorem BlockTriangular.toBlock_pfc {T : Matrix n n 𝕜} (hT : T.BlockTriangular b)
    (hs : (minpoly 𝕜 T).Splits) (k : α) (f : 𝕜 → 𝕜) :
    (_root_.pfc f T).toBlock (b · = k) (b · = k) =
      _root_.pfc f (T.toBlock (b · = k) (b · = k)) := by
  classical
  have hT' : IsIntegral 𝕜 T := Algebra.IsIntegral.isIntegral _
  have hdvd : minpoly 𝕜 (T.toBlock (b · = k) (b · = k)) ∣
      nodalMultiset (minpoly 𝕜 T).roots := by
    refine (minpoly.dvd 𝕜 _ ?_).trans (minpoly_dvd_nodalMultiset_roots hT' hs)
    rw [← hT.toBlock_aeval, minpoly.aeval]
    rfl
  rw [pfc_def, hT.toBlock_aeval,
    pfc_eq_aeval_of_isJetInterpolant hdvd (isJetInterpolant_interpolateJet _ _)]

end BlockTriangular

/-! ### Products of upper triangular matrices -/

section Upper

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- Let $M$ be an upper triangular matrix over a field, and let $p$ be a polynomial. Then the
diagonal entries of $p(M)$ are $p(M)_{ii} = p(M_{ii})$. -/
theorem IsUpperTriangular.aeval_apply_self {𝕜 : Type*} [Field 𝕜]
    {M : Matrix n n 𝕜} (hM : M.IsUpperTriangular) (p : 𝕜[X]) (i : n) :
    (aeval M p) i i = p.eval (M i i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial m c =>
    rw [aeval_monomial, eval_monomial, algebraMap_eq_diagonal, diagonal_mul,
      hM.pow_apply_self]
    rfl

end Upper

/-! ### The Parlett recurrence -/

section Parlett

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : Type*} [Fintype n]
  [LinearOrder n] [LocallyFiniteOrder n]

/-- **The Parlett recurrence.** Let $\mathbb{K}$ be a nontrivially normed field, let
$T \in \mathbb{K}^{n \times n}$ be upper triangular, let $f \colon \mathbb{K} \to \mathbb{K}$,
and let $F = f(T)$. If $i < j$ and $t_{ii} \neq t_{jj}$, then
$$f_{ij} = t_{ij} \frac{f_{jj} - f_{ii}}{t_{jj} - t_{ii}}
  + \sum_{i < k < j} \frac{t_{ik} f_{kj} - f_{ik} t_{kj}}{t_{jj} - t_{ii}}.$$
This is (9.1.11) of [golub2013matrix].

The proof compares the $(i, j)$ entries of $FT = TF$. -/
theorem pfc_apply_eq_parlett {T : Matrix n n 𝕜} (hT : T.IsUpperTriangular) (f : 𝕜 → 𝕜) {i j : n}
    (hij : i < j) (hne : T i i ≠ T j j) :
    pfc f T i j = T i j * (pfc f T j j - pfc f T i i) / (T j j - T i i) +
      ∑ k ∈ Ioo i j, (T i k * pfc f T k j - pfc f T i k * T k j) / (T j j - T i i) := by
  have hd : T j j - T i i ≠ 0 := sub_ne_zero.mpr hne.symm
  have h := IsUpperTriangular.apply_mul_sub_eq_of_commute (hT.pfc f) hT (commute_pfc T f) hij
  rw [← Finset.sum_div, ← add_div, eq_div_iff hd, h]

end Parlett

/-! ### The block Parlett equations -/

section BlockParlett

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
  {α : Type*} [Fintype α] [LinearOrder α] {b : n → α}

omit [Fintype α] in
/-- **The block Parlett equations.** Let $\mathbb{K}$ be a nontrivially normed field, let
$T \in \mathbb{K}^{n \times n}$ be block triangular for a block map $b$ into a finite linearly
ordered set, with blocks $T_{kl}$, let $f \colon \mathbb{K} \to \mathbb{K}$, and let $F = f(T)$
have the blocks $F_{kl}$. Then for block indices $k < l$,
$$F_{kl} T_{ll} - T_{kk} F_{kl} = T_{kl} F_{ll} - F_{kk} T_{kl}
  + \sum_{k < r < l} (T_{kr} F_{rl} - F_{kr} T_{rl}).$$
This is (9.1.12) of [golub2013matrix]. It is a Sylvester equation for $F_{kl}$ when the blocks
nearer the diagonal are known.

The block $T_{kl}$ is `T.toBlock (b · = k) (b · = l)`. -/
theorem BlockTriangular.pfc_sylvester [Finite α] [LocallyFiniteOrder α] {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] {T : Matrix n n 𝕜} (hT : T.BlockTriangular b) (f : 𝕜 → 𝕜)
    {k l : α} (hkl : k < l) :
    (_root_.pfc f T).toBlock (b · = k) (b · = l) * T.toBlock (b · = l) (b · = l) -
        T.toBlock (b · = k) (b · = k) * (_root_.pfc f T).toBlock (b · = k) (b · = l) =
      T.toBlock (b · = k) (b · = l) * (_root_.pfc f T).toBlock (b · = l) (b · = l) -
          (_root_.pfc f T).toBlock (b · = k) (b · = k) * T.toBlock (b · = k) (b · = l) +
        ∑ r ∈ Ioo k l, (T.toBlock (b · = k) (b · = r) * (_root_.pfc f T).toBlock (b · = r) (b · = l)
          - (_root_.pfc f T).toBlock (b · = k) (b · = r) * T.toBlock (b · = r) (b · = l)) := by
  have hF : (_root_.pfc f T).BlockTriangular b := hT.pfc f
  have h := congrArg (fun M => M.toBlock (b · = k) (b · = l)) (commute_pfc T f).eq
  rw [hT.toBlock_mul_eq_sum_Icc hF, hF.toBlock_mul_eq_sum_Icc hT, Icc_eq_cons_Ioc hkl.le,
    sum_cons, sum_cons, Ioc_eq_cons_Ioo hkl, sum_cons, sum_cons] at h
  rw [sum_sub_distrib, ← sub_eq_zero, ← neg_eq_zero, ← sub_eq_zero.mpr h]
  abel

end BlockParlett

/-! ### Paths and the powers of a triangular matrix -/

section Path

variable {n : Type*} [LinearOrder n]

/-- The index sequence from $i$ to $j$ with the set $s$ of interior indices: the list of $i$, then
the elements of $s$ in increasing order, then $j$. For $s \subseteq (i, j)$ it is a strictly
increasing sequence $i = s_0 < s_1 < \dots < s_k = j$, and the set $S_{ij}$ of Theorem 9.1.4 of
[golub2013matrix] is the set of the lists `Matrix.path i s j` for $s \subseteq (i, j)$. -/
def path (i : n) (s : Finset n) (j : n) : List n :=
  i :: (s.sort ++ [j])

/-- The product $t_{s_0 s_1} t_{s_1 s_2} \cdots t_{s_{k-1} s_k}$ of the entries of $T$ along the
consecutive pairs of a list $s_0, \dots, s_k$ of indices. It is $1$ for a list with at most one
element. -/
def pathProd {R : Type*} [CommMonoid R] (T : Matrix n n R) (l : List n) : R :=
  (List.zipWith (fun p q => T p q) l l.tail).prod

variable {R : Type*} [CommMonoid R]

omit [LinearOrder n] in
/-- The path product of the empty list is $1$. -/
@[simp]
theorem pathProd_nil (T : Matrix n n R) : pathProd T [] = 1 := rfl

omit [LinearOrder n] in
/-- The path product of a list with one element is $1$. -/
@[simp]
theorem pathProd_singleton (T : Matrix n n R) (i : n) : pathProd T [i] = 1 := rfl

omit [LinearOrder n] in
/-- The path product of the list $i, j, l_1, \dots$ is $t_{ij}$ times the path product of the list
$j, l_1, \dots$. -/
@[simp]
theorem pathProd_cons_cons (T : Matrix n n R) (i j : n) (l : List n) :
    pathProd T (i :: j :: l) = T i j * pathProd T (j :: l) := rfl

/-- With no interior indices, the path from $i$ to $j$ is the list $i, j$. -/
theorem path_empty (i j : n) : path i ∅ j = [i, j] := by
  simp [path]

/-- If $s \subseteq (k, j)$, then the path from $i$ to $j$ with the interior indices $\{k\} \cup s$
is $i$ followed by the path from $k$ to $j$ with the interior indices $s$. -/
theorem path_insert [LocallyFiniteOrder n] {i j k : n} {s : Finset n} (hs : s ⊆ Ioo k j) :
    path i (insert k s) j = i :: path k s j := by
  have hk : k ∉ s := fun h => by simpa using (Finset.mem_Ioo.mp (hs h)).1
  rw [path, Finset.sort_insert _ (fun x hx => (Finset.mem_Ioo.mp (hs hx)).1.le) hk]
  rfl

/-- The path product along the path from $i$ to $j$ with no interior indices is $t_{ij}$. -/
theorem pathProd_path_empty (T : Matrix n n R) (i j : n) : pathProd T (path i ∅ j) = T i j := by
  simp [path_empty]

/-- If $s \subseteq (k, j)$, then the path product along the path from $i$ to $j$ with the interior
indices $\{k\} \cup s$ is $t_{ik}$ times the path product along the path from $k$ to $j$ with
the interior indices $s$. -/
theorem pathProd_path_insert [LocallyFiniteOrder n] (T : Matrix n n R) {i j k : n}
    {s : Finset n} (hs : s ⊆ Ioo k j) :
    pathProd T (path i (insert k s) j) = T i k * pathProd T (path k s j) := by
  rw [path_insert hs, path, pathProd_cons_cons]

/-- If $i < j$ and $s \subseteq (i, j)$, then the path from $i$ to $j$ through $s$ has no repeated
index. -/
theorem nodup_path [LocallyFiniteOrder n] {i j : n} (hij : i < j) {s : Finset n}
    (hs : s ⊆ Ioo i j) : (path i s j).Nodup := by
  rw [path, List.nodup_cons, List.nodup_append]
  refine ⟨?_, Finset.sort_nodup _ _, List.nodup_singleton j, ?_⟩
  · simp only [List.mem_append, Finset.mem_sort, List.mem_singleton, not_or]
    exact ⟨fun h => by simpa using (Finset.mem_Ioo.mp (hs h)).1, hij.ne⟩
  · intro a ha c hc
    rw [List.mem_singleton] at hc
    rw [Finset.mem_sort] at ha
    subst hc
    exact (Finset.mem_Ioo.mp (hs ha)).2.ne

/-- **Grouping the index sets by their least element.** For a function $g$ on the finite sets of
indices, with values in an additive commutative monoid,
$$\sum_{s \subseteq (i, j)} g(s)
  = g(\emptyset) + \sum_{k \in (i, j)} \sum_{s \subseteq (k, j)} g(\{k\} \cup s),$$
where $(i, j)$ is the open interval of indices. -/
theorem sum_powerset_Ioo [LocallyFiniteOrder n] {M : Type*} [AddCommMonoid M]
    (g : Finset n → M) (i j : n) :
    ∑ s ∈ (Ioo i j).powerset, g s =
      g ∅ + ∑ k ∈ Ioo i j, ∑ s ∈ (Ioo k j).powerset, g (insert k s) := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset _), Finset.sum_sigma']
  congr 1
  have hne : ∀ s ∈ (Ioo i j).powerset.erase ∅, s.Nonempty := fun s hs =>
    Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hs).1
  refine Finset.sum_bij' (fun s hs => ⟨s.min' (hne s hs), s.erase (s.min' (hne s hs))⟩)
    (fun x _ => insert x.1 x.2)
    (fun s hs => ?_) (fun x hx => ?_) (fun s hs => ?_) (fun x hx => ?_) (fun s hs => ?_)
  · obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp hs
    rw [Finset.mem_powerset] at hsub
    have hmem := Finset.min'_mem s (Finset.nonempty_iff_ne_empty.mpr hne)
    refine Finset.mem_sigma.mpr ⟨hsub hmem, Finset.mem_powerset.mpr fun x hx => ?_⟩
    obtain ⟨hxne, hxs⟩ := Finset.mem_erase.mp hx
    exact Finset.mem_Ioo.mpr ⟨lt_of_le_of_ne (Finset.min'_le s x hxs) (Ne.symm hxne),
      (Finset.mem_Ioo.mp (hsub hxs)).2⟩
  · obtain ⟨hk, hs⟩ := Finset.mem_sigma.mp hx
    rw [Finset.mem_powerset] at hs
    refine Finset.mem_erase.mpr ⟨Finset.insert_ne_empty _ _, Finset.mem_powerset.mpr ?_⟩
    refine Finset.insert_subset hk fun y hy => ?_
    have := Finset.mem_Ioo.mp (hs hy)
    exact Finset.mem_Ioo.mpr ⟨(Finset.mem_Ioo.mp hk).1.trans this.1, this.2⟩
  · exact Finset.insert_erase (Finset.min'_mem s (hne s hs))
  · obtain ⟨hk, hs⟩ := Finset.mem_sigma.mp hx
    rw [Finset.mem_powerset] at hs
    have hkx : x.1 ∉ x.2 := fun h => by simpa using (Finset.mem_Ioo.mp (hs h)).1
    have hmin : (insert x.1 x.2).min' (Finset.insert_nonempty _ _) = x.1 :=
      le_antisymm (Finset.min'_le _ _ (Finset.mem_insert_self _ _))
        (Finset.le_min' _ _ _ fun y hy => by
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact le_rfl
          · exact (Finset.mem_Ioo.mp (hs hy)).1.le)
    ext
    · exact hmin
    · simp only [hmin, Finset.erase_insert hkx, heq_eq_eq]
  · rw [Finset.insert_erase (Finset.min'_mem s (hne s hs))]

variable {R : Type*} [CommRing R] [Fintype n] [LocallyFiniteOrder n]

/-- **Path expansion of the powers of a strictly upper triangular matrix.** Let $R$ be a commutative
ring, and let $N \in R^{n \times n}$ be strictly upper triangular: $n_{ij} = 0$ for $j \le i$.
Then for $r \in \mathbb{N}$ and $i < j$,
$$(N^{r+1})_{ij}
  = \sum_{s \subseteq (i, j),\ |s| = r} n_{s_0 s_1} n_{s_1 s_2} \cdots n_{s_r s_{r+1}},$$
where $i = s_0 < s_1 < \dots < s_{r+1} = j$ is the path through $s$. This is (9.2.2) of
[golub2013matrix]. -/
theorem pow_succ_apply_eq_sum_pathProd {N : Matrix n n R} (hN : ∀ i j, j ≤ i → N i j = 0)
    (r : ℕ) {i j : n} (hij : i < j) :
    (N ^ (r + 1)) i j = ∑ s ∈ (Ioo i j).powersetCard r, pathProd N (path i s j) := by
  have hU : N.IsUpperTriangular := fun i j h => hN i j h.le
  induction r generalizing i with
  | zero => simp [pathProd_path_empty]
  | succ r ih =>
    rw [pow_succ', IsUpperTriangular.mul_apply hU (hU.pow _) i j, Icc_eq_cons_Ioc hij.le,
      sum_cons,
      Ioc_eq_cons_Ioo hij,
      sum_cons, hN i i le_rfl, IsUpperTriangular.pow_apply_self hU (r + 1) j, hN j j le_rfl,
      zero_mul,
      zero_pow (Nat.succ_ne_zero _), mul_zero, zero_add, zero_add]
    rw [Finset.powersetCard_eq_filter, Finset.sum_filter, sum_powerset_Ioo]
    simp only [Finset.card_empty, (Nat.succ_ne_zero r).symm, ite_false, zero_add]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [ih (Finset.mem_Ioo.mp hk).2, Finset.mul_sum, Finset.powersetCard_eq_filter,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' := Finset.mem_powerset.mp hs
    have hks : k ∉ s := fun h => by simpa using (Finset.mem_Ioo.mp (hs' h)).1
    rw [Finset.card_insert_of_notMem hks, pathProd_path_insert _ hs']
    simp only [add_left_inj]

end Path

/-! ### Theorem 9.1.4: the divided-difference formula -/

section DivDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : Type*} [Fintype n]
  [LinearOrder n] [LocallyFiniteOrder n]

omit [Fintype n] [NontriviallyNormedField 𝕜] [LocallyFiniteOrder n] in
/-- The diagonal entries of $T$ along the path $i, s, j$, as a multiset, are $t_{ii}$ together with
the diagonal entries along the tail of the path. -/
theorem coe_map_path (T : Matrix n n 𝕜) (i j : n) (s : Finset n) :
    (((path i s j).map fun k => T k k : List 𝕜) : Multiset 𝕜) =
      T i i ::ₘ (((path i s j).tail.map fun k => T k k : List 𝕜) : Multiset 𝕜) := by
  simp [path]

omit [Fintype n] in
/-- If $s \subseteq (k, j)$, then the tail of the path from $i$ to $j$ with the interior indices
$\{k\} \cup s$ is the path from $k$ to $j$ with the interior indices $s$. -/
theorem tail_path_insert {i j k : n} {s : Finset n} (hs : s ⊆ Ioo k j) :
    (path i (insert k s) j).tail = path k s j := by
  rw [path_insert hs, List.tail_cons]

/-- **Path expansion of the powers of an upper triangular matrix.** Let $\mathbb{K}$ be a
nontrivially normed field of characteristic zero, let $T \in \mathbb{K}^{n \times n}$ be upper
triangular, and let $m \in \mathbb{N}$. Then for $i < j$,
$$(T^m)_{ij} = \sum_{s \subseteq (i, j)} t_{s_0 s_1} \cdots t_{s_{k-1} s_k}\;
  z^m[t_{s_0 s_0}, \dots, t_{s_k s_k}],$$
where $i = s_0 < \dots < s_k = j$ is the path through $s$, and $z^m[\dots]$ is the divided
difference of $z \mapsto z^m$ at the diagonal entries along the path.

The divided difference sums the loops at the diagonal entries along each path. -/
theorem pow_apply_eq_sum_pathProd [CharZero 𝕜] [DecidableEq 𝕜] {T : Matrix n n 𝕜}
    (hT : T.IsUpperTriangular)
    (m : ℕ) {i j : n} (hij : i < j) :
    (T ^ m) i j = ∑ s ∈ (Ioo i j).powerset,
      pathProd T (path i s j) * divDiff (fun z => z ^ m) ((path i s j).map fun k => T k k) := by
  induction m generalizing i with
  | zero =>
    rw [pow_zero, one_apply_ne hij.ne]
    refine (Finset.sum_eq_zero fun s _ => ?_).symm
    have h1 : (fun z : 𝕜 => z ^ 0) = fun z => (1 : 𝕜[X]).eval z := by simp
    have hcard : 1 < Multiset.card (((path i s j).map fun k => T k k : List 𝕜) : Multiset 𝕜) := by
      simp [path]
    rw [h1, divDiff_polynomial_of_degree_lt (by
      rw [degree_one]; exact_mod_cast (zero_lt_one.trans hcard)), coeff_one,
      ite_eq_right (by omega), mul_zero]
  | succ m ih =>
    rw [pow_succ', IsUpperTriangular.mul_apply hT (hT.pow _) i j, Icc_eq_cons_Ioc hij.le,
      sum_cons,
      Ioc_eq_cons_Ioo hij,
      sum_cons, ih hij, IsUpperTriangular.pow_apply_self hT m j]
    simp only [coe_map_path T i j, divDiff_X_pow, mul_add, Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun s _ => ?_
      ring
    rw [sum_powerset_Ioo, pathProd_path_empty]
    congr 1
    · simp [path, divDiff_singleton]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [ih (Finset.mem_Ioo.mp hk).2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' := Finset.mem_powerset.mp hs
    rw [pathProd_path_insert _ hs', tail_path_insert hs', mul_assoc]

omit [Fintype n] [LinearOrder n] [LocallyFiniteOrder n] in
/-- The divided difference is additive on polynomial functions: $(p + q)[s] = p[s] + q[s]$. -/
private theorem divDiff_eval_add [CharZero 𝕜] [DecidableEq 𝕜] (p q : 𝕜[X]) (s : Multiset 𝕜) :
    divDiff (fun z => (p + q).eval z) s =
      divDiff (fun z => p.eval z) s + divDiff (fun z => q.eval z) s := by
  rw [divDiff_polynomial, divDiff_polynomial, divDiff_polynomial,
    add_modByMonic, coeff_add]

/-- **Path expansion of a polynomial in an upper triangular matrix.** Let $\mathbb{K}$ be a
nontrivially normed field of characteristic zero, let $T \in \mathbb{K}^{n \times n}$ be upper
triangular, and let $p$ be a polynomial over $\mathbb{K}$. Then for $i < j$,
$$p(T)_{ij} = \sum_{s \subseteq (i, j)} t_{s_0 s_1} \cdots t_{s_{k-1} s_k}\;
  p[t_{s_0 s_0}, \dots, t_{s_k s_k}],$$
where $i = s_0 < \dots < s_k = j$ is the path through $s$, and $p[\dots]$ is the divided
difference of $p$ at the diagonal entries along the path. -/
theorem aeval_apply_eq_sum_pathProd [CharZero 𝕜] [DecidableEq 𝕜] {T : Matrix n n 𝕜}
    (hT : T.IsUpperTriangular)
    (p : 𝕜[X]) {i j : n} (hij : i < j) :
    (aeval T p) i j = ∑ s ∈ (Ioo i j).powerset,
      pathProd T (path i s j) * divDiff (fun z => p.eval z) ((path i s j).map fun k => T k k) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Matrix.add_apply, hp, hq, divDiff_eval_add, mul_add, Finset.sum_add_distrib]
  | monomial m c =>
    have h : (fun z => (monomial m c).eval z) = c • fun z : 𝕜 => z ^ m := by
      funext z
      simp [eval_monomial]
    rw [aeval_monomial, ← Algebra.smul_def, Matrix.smul_apply, pow_apply_eq_sum_pathProd hT m hij,
      smul_eq_mul, Finset.mul_sum, h]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [divDiff_const_smul]
    ring

omit [LocallyFiniteOrder n] in
/-- The minimal polynomial of an upper triangular matrix divides $\prod_k (z - t_{kk})$, whose roots
are the diagonal entries with their multiplicities. -/
private theorem minpoly_dvd_nodalMultiset_diag {T : Matrix n n 𝕜} (hT : T.IsUpperTriangular) :
    minpoly 𝕜 T ∣ nodalMultiset (Finset.univ.val.map fun k => T k k) := by
  have h : nodalMultiset (Finset.univ.val.map fun k => T k k) = T.charpoly := by
    rw [charpoly_of_isUpperTriangular _ hT, nodalMultiset, Multiset.map_map,
      Finset.prod_eq_multiset_prod]
    rfl
  rw [h]
  exact minpoly_dvd_charpoly T

omit [LocallyFiniteOrder n] in
/-- **The diagonal of $f(T)$.** Let $\mathbb{K}$ be a nontrivially normed field, let
$T \in \mathbb{K}^{n \times n}$ be upper triangular, and let
$f \colon \mathbb{K} \to \mathbb{K}$ be any function. Then $f(T)_{ii} = f(t_{ii})$ for every
$i$. This is the diagonal part of Theorem 9.1.4 of [golub2013matrix]. -/
theorem pfc_apply_self_of_isUpperTriangular {T : Matrix n n 𝕜} (hT : T.IsUpperTriangular)
    (f : 𝕜 → 𝕜) (i : n) : pfc f T i i = f (T i i) := by
  classical
  have hmem : T i i ∈ Finset.univ.val.map fun k => T k k :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
  rw [pfc_eq_aeval_of_isJetInterpolant (minpoly_dvd_nodalMultiset_diag hT)
    (isJetInterpolant_interpolateJet _ _), hT.aeval_apply_self,
    eval_interpolateJet_taylorJet hmem]

/-- The **divided-difference formula** for a function of a triangular matrix. Let $\mathbb{K}$ be a
nontrivially normed field of characteristic zero, let $T \in \mathbb{K}^{n \times n}$ be upper
triangular, and let $f \colon \mathbb{K} \to \mathbb{K}$. Then for $i < j$,
$$f(T)_{ij} = \sum_{s \in S_{ij}} t_{s_0 s_1} t_{s_1 s_2} \cdots t_{s_{k-1} s_k}\,
  f[\lambda_{s_0}, \dots, \lambda_{s_k}],$$
where $S_{ij}$ is the set of strictly increasing index sequences $i = s_0 < \dots < s_k = j$,
and $\lambda_r = t_{rr}$. This is Theorem 9.1.4 of [golub2013matrix].

The divided differences are confluent where the diagonal entries repeat, so the eigenvalues need
not be distinct. There is no smoothness hypothesis on $f$: both sides are defined through the
jets of $f$. A sequence in $S_{ij}$ is `Matrix.path i s j` for $s \subseteq (i, j)$, and
$f[\dots]$ is `Hermite.divDiff`. Together with `Matrix.pfc_apply_self_of_isUpperTriangular`
($f_{ii} = f(t_{ii})$) and `Matrix.BlockTriangular.pfc` ($f_{ij} = 0$ for $i > j$), this formula
determines $f(T)$. -/
theorem pfc_apply_eq_sum_divDiff [CharZero 𝕜] [DecidableEq 𝕜] {T : Matrix n n 𝕜}
    (hT : T.IsUpperTriangular)
    (f : 𝕜 → 𝕜) {i j : n} (hij : i < j) :
    pfc f T i j = ∑ s ∈ (Ioo i j).powerset,
      pathProd T (path i s j) * divDiff f ((path i s j).map fun k => T k k) := by
  classical
  set s₀ := Finset.univ.val.map fun k => T k k
  have hP := isJetInterpolant_interpolateJet s₀ (taylorJet f)
  rw [pfc_eq_aeval_of_isJetInterpolant (minpoly_dvd_nodalMultiset_diag hT) hP,
    aeval_apply_eq_sum_pathProd hT _ hij]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hle : (((path i s j).map fun k => T k k : List 𝕜) : Multiset 𝕜) ≤ s₀ := by
    rw [← Multiset.map_coe]
    refine Multiset.map_le_map ((Multiset.le_iff_subset
      (Multiset.coe_nodup.mpr (nodup_path hij (Finset.mem_powerset.mp hs)))).mpr
      fun x _ => Finset.mem_univ_val x)
  rw [hP.divDiff_eq hle]

end DivDiff

end Matrix
