/-
Vendored from Dean Cureton and contributors, https://github.com/deancureton/MovingSofa,
revision 4d5569131940815f47a9ccf3e90a4c5043c56127, path MovingSofa/Curve/Jordan/Basic.lean.
The original work is distributed under Apache-2.0.
Local changes are documented in Attribution.md.
-/
import Numlib.ThirdParty.Jordan.MovingSofa.Geometry.Plane
import Mathlib.Analysis.Complex.Circle

namespace MovingSofa

def IsJordanArc (Γ : Set Point) : Prop :=
  ∃ (a b : ℝ) (_ : a ≤ b) (x : Set.Icc a b → Point),
    Continuous x ∧ Function.Injective x ∧ Set.range x = Γ

def IsJordanCurve (Γ : Set Point) : Prop :=
  ∃ x : Circle → Point, Continuous x ∧ Function.Injective x ∧ Set.range x = Γ

def jordanSets : (Set Point → Prop) × (Set Point → Prop) :=
  (IsJordanArc, IsJordanCurve)

def IsOrientedJordanArc (Γ : Set Point) (p q : Point) : Prop :=
  ∃ (a b : ℝ) (hab : a ≤ b) (x : Set.Icc a b → Point),
    Continuous x ∧ Function.Injective x ∧ Set.range x = Γ ∧
    x ⟨a, le_rfl, hab⟩ = p ∧ x ⟨b, hab, le_rfl⟩ = q

structure OrientedJordanArc where
  carrier : Set Point
  startPoint : Point
  endPoint : Point
  parametrizable : IsOrientedJordanArc carrier startPoint endPoint

end MovingSofa
