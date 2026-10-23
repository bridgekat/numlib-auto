import Numlib.Optimization.Regularization.Universal.Parameter
/-!
# Real-power penalty and accuracy - scale estimates

Actual length checks and parameter caps give the exact penalty lower bound.
A common accuracy scale handles either failed derivative test.
-/

namespace UniversalRegularization
/-- Combining a length check with an upper parameter bound gives the exact
real-power lower bound for the regularization penalty. -/
theorem penalty_lower {α ε σ t S r j : ℝ}
    (hα : 0 < α) (hε : 0 < ε) (hσ : 0 < σ) (ht : 0 < t) (hS : 0 < S)
    (hj : 0 ≤ j) (hrj : j < r) (hcap : σ ≤ S)
    (hlen : α * ε ≤ σ * t ^ (r - j)) :
    (α ^ r / S ^ j) ^ (1 / (r - j)) * ε ^ (r / (r - j)) ≤ σ * t ^ r := by
  have hd : 0 < r - j := sub_pos.mpr hrj
  have hr : 0 < r := lt_of_le_of_lt hj hrj
  have hpow := Real.rpow_le_rpow (mul_pos hα hε).le hlen
    (div_pos hr hd).le
  rw [Real.mul_rpow hα.le hε.le, Real.mul_rpow hσ.le (Real.rpow_nonneg ht.le _),
    ←Real.rpow_mul ht.le,show (r - j) * (r / (r - j)) = r by field_simp] at hpow
  have hneg : -j / (r - j) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  have hbound := Real.rpow_le_rpow_of_nonpos hσ hcap hneg
  have hm := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hσ.le (-j / (r - j)))
  have hexp : r / (r - j)+ -j / (r - j) = 1 := by field_simp;ring
  have hprod : σ ^ (r / (r - j)) * t ^ r * σ ^ (-j / (r - j)) = σ * t^r := by
    rw [mul_right_comm,←Real.rpow_add hσ,hexp,Real.rpow_one]
  rw [hprod] at hm
  have hl := mul_le_mul_of_nonneg_left hbound
    (mul_nonneg (Real.rpow_nonneg hα.le (r / (r - j))) (Real.rpow_nonneg hε.le (r / (r - j))))
  have hid : (α ^ r / S ^ j) ^ (1 / (r - j)) * ε ^ (r / (r - j)) =
      α ^ (r / (r - j)) * ε ^ (r / (r - j)) * S ^ (-j / (r - j)) := by
    rw [Real.div_rpow (Real.rpow_nonneg hα.le _) (Real.rpow_nonneg hS.le _),
      ←Real.rpow_mul hα.le,←Real.rpow_mul hS.le,show r * (1 / (r - j)) = r / (r - j) by ring,
      show j * (1 / (r - j)) = j / (r - j) by ring,neg_div,Real.rpow_neg hS.le]
    ring
  rw [hid]
  exact hl.trans hm

/-- The source parameter accuracy power cancels to its exact successful - decrease power. -/
theorem penalty_lower_accuracy {α ε σ t U a r j : ℝ}
    (hα : 0 < α) (hε : 0 < ε) (hσ : 0 < σ) (ht : 0 < t) (hU : 0 < U)
    (hj : 0 ≤ j) (hja : j < a) (har : a ≤ r)
    (hcap : σ ≤ U * ε ^ ((a - r) / (a - j)))
    (hlen : α * ε ≤ σ * t ^ (r - j)) :
    (α ^ r / U ^ j) ^ (1 / (r - j)) * ε ^ (a / (a - j)) ≤ σ * t ^ r := by
  have hrj := hja.trans_le har
  have hh := penalty_lower hα hε hσ ht
    (mul_pos hU (Real.rpow_pos_of_pos hε _)) hj hrj hcap hlen
  convert hh using 1
  rw [Real.mul_rpow hU.le (Real.rpow_nonneg hε.le _),←Real.rpow_mul hε.le,
    div_mul_eq_div_div, Real.div_rpow
      (div_nonneg (Real.rpow_nonneg hα.le _) (Real.rpow_nonneg hU.le _))
      (Real.rpow_nonneg hε.le _),←Real.rpow_mul hε.le]
  have hid : ε ^ (a / (a - j)) =
      ε ^ (r / (r - j)) / ε ^ (((a - r) / (a - j) * j) * (1 / (r - j))) := by
    rw [←Real.rpow_sub hε]
    congr 1
    field_simp [ne_of_gt (sub_pos.mpr hja),ne_of_gt (sub_pos.mpr hrj)]
    ring
  rw [hid]
  ring
end UniversalRegularization

namespace UniversalRegularization
/-- A common accuracy scale works for either enabled derivative order. -/
theorem penalty_lower_scale {α δ σ t U a r j : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (hσ : 0 < σ) (ht : 0 < t) (hU : 0 < U)
    (hj : 0 ≤ j) (hja : j < a) (har : a ≤ r)
    (hcap : σ ≤ U * δ ^ ((a - r) / a))
    (hlen : α * δ ^ ((a - j) / a) ≤ σ * t ^ (r - j)) :
    (α ^ r / U ^ j) ^ (1 / (r - j)) * δ ≤ σ * t ^ r := by
  have ha : 0 < a := hj.trans_lt hja
  have hid1 : (δ ^ ((a - j) / a)) ^ ((a - r) / (a - j)) = δ ^ ((a - r) / a) := by
    rw [←Real.rpow_mul hδ.le]
    congr 1
    field_simp [ne_of_gt (sub_pos.mpr hja),ne_of_gt ha]
  have hid2 : (δ ^ ((a - j) / a)) ^ (a / (a - j)) = δ := by
    rw [←Real.rpow_mul hδ.le]
    have he : (a - j) / a * (a / (a - j)) = 1 := by
      field_simp [ne_of_gt (sub_pos.mpr hja),ne_of_gt ha]
    rw [he,Real.rpow_one]
  have hh := penalty_lower_accuracy hα (Real.rpow_pos_of_pos hδ _) hσ ht hU
    hj hja har (by rwa [hid1]) hlen
  rwa [hid2] at hh

/-- The power of a requested accuracy is represented by its source stopping scale. -/
theorem accuracy_power_identity {ε a j b : ℝ} (hε : 0 < ε) (ha : a ≠ 0)
    (haj : a - j ≠ 0) : (ε ^ (a / (a - j))) ^ (b / a) = ε ^ (b / (a - j)) := by
  rw [←Real.rpow_mul hε.le]
  congr 1
  field_simp

/-- An accuracy below an order's stopping scale gives its measure lower bound. -/
theorem accuracy_scale_le {ε δ a j : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hj : 0 ≤ j) (hja : j < a) (hδle : δ ≤ ε ^ (a / (a - j))) :
    δ ^ ((a - j) / a) ≤ ε := by
  have ha : 0 < a := hj.trans_lt hja
  have hh := Real.rpow_le_rpow hδ.le hδle (div_pos (sub_pos.mpr hja) ha).le
  rw [←Real.rpow_mul hε.le] at hh
  have he : a / (a - j) * ((a - j) / a) = 1 := by
    field_simp [ne_of_gt (sub_pos.mpr hja),ne_of_gt ha]
  rwa [he,Real.rpow_one] at hh

/-- The nonpositive parameter power reverses an accuracy - scale comparison. -/
theorem parameter_accuracy_le {ε δ a r j : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hj : 0 ≤ j) (hja : j < a) (har : a ≤ r)
    (hδle : δ ≤ ε ^ (a / (a - j))) :
    ε ^ ((a - r) / (a - j)) ≤ δ ^ ((a - r) / a) := by
  have ha : 0 < a := hj.trans_lt hja
  have hh := Real.rpow_le_rpow_of_nonpos hδ hδle
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr har) ha.le)
  rwa [accuracy_power_identity hε (ne_of_gt ha) (ne_of_gt (sub_pos.mpr hja))] at hh
end UniversalRegularization
