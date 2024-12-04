import Mathlib
import ImportGraph.Imports


structure chain where
  points: List (ℝ × ℝ)
  min_size: 2 ≤ points.length
  get_segment (n: Fin (points.length - 1)): Set (ℝ × ℝ) :=
    segment (𝕜 := ℝ × ℝ) (points[n.1]'(by omega)) (points[n.1 + 1]'(by omega))
  property_of_consecutive_segments:
    ∀ (n m: Fin (points.length - 1)), n.1 + 1 = m.1 →
    (get_segment n) ∩ (get_segment m) = { points[m.1]'(by omega) }
  nonconsecutive_segments_disjoint:
    ∀ (n m: Fin (points.length - 1)), n.1 + 1 < m.1 → Disjoint (get_segment n) (get_segment m)

def chain.first (c: chain): ℝ × ℝ := c.points[0]'(by cases c; simp at *; omega)
def chain.last (c: chain): ℝ × ℝ := c.points[c.points.length - 1]'(by cases c; simp at *; omega)
def chain.connects (c: chain) (x y: ℝ × ℝ) := c.first = x ∧ c.last = y
def chain.as_Set (c: chain): Set (ℝ × ℝ) := λ (p: ℝ × ℝ) => ∃ (n: Fin (c.points.length - 1)), p ∈ c.get_segment n
def chain.polygon (c: chain): Set (ℝ × ℝ) := c.as_Set ∪ segment (𝕜 := ℝ × ℝ) c.last c.first

theorem baby_Jordan (c: chain):
  ∃ A B, c.polygonᶜ = A ∪ B ∧
  A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
  (∀ x ∈ A, ∀ y ∈ A, ∃ (c: chain), c.connects x y ∧ Disjoint c.as_Set c.polygon) ∧
  (∀ x ∈ B, ∀ y ∈ B, ∃ (c: chain), c.connects x y ∧ Disjoint c.as_Set c.polygon) ∧
  (∀ x ∈ A, ∀ y ∈ B, ∀ (c: chain), c.connects x y → Disjoint c.as_Set c.polygon → False) := sorry


structure Jordan_curve where
  param: UnitAddCircle → ℝ × ℝ
  param_continuous: Continuous param
  param_injective: Function.Injective param

theorem Jordan_curve_theorem (jc: Jordan_curve):
  ∃ A B, (Set.range jc.param)ᶜ = A ∪ B ∧
  A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
  IsConnected A ∧ IsConnected B ∧ IsOpen A ∧ IsOpen B := sorry




#min_imports
