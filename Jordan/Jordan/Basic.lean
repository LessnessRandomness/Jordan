import Mathlib
import ImportGraph.Imports


structure Jordan_curve where
  parametrization: UnitAddCircle → ℝ × ℝ
  parametrization_continuous: Continuous parametrization
  parametrization_injective: Function.Injective parametrization


theorem Jordan_curve_theorem (jc: Jordan_curve):
  ∃ A B, (Set.range jc.parametrization)ᶜ = A ∪ B ∧
  A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
  IsConnected A ∧ IsConnected B ∧ IsOpen A ∧ IsOpen B := sorry

#min_imports
