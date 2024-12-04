import Mathlib
import ImportGraph.Imports


structure chain where
  points: List (ℝ × ℝ)
  min_size: 2 ≤ points.length
  get_segment (n: Fin (points.length - 1)): Set (ℝ × ℝ) :=
    segment (𝕜 := ℝ × ℝ) (points[n.1]'(by cases n; simp at *; omega)) (points[n.1 + 1]'(by cases n; simp at *; omega))
  no_selfcrossing: ∀ (n m: Fin (points.length - 1)), n.1 + 1 < m.1 → Disjoint (get_segment n) (get_segment m)

def chain.first (c: chain): ℝ × ℝ := c.points[0]'(by cases c; simp at *; omega)
def chain.last (c: chain): ℝ × ℝ := c.points[c.points.length - 1]'(by cases c; simp at *; omega)
def chain.connects (c: chain) (x y: ℝ × ℝ) := c.first = x ∧ c.last = y
def chain.as_Set (c: chain): Set (ℝ × ℝ) := λ (p: ℝ × ℝ) => ∃ (n: Fin (c.points.length - 1)), p ∈ c.get_segment n

structure Polygon where
  underlying_chain: chain
  is_loop: underlying_chain.first = underlying_chain.last

def Polygon.as_Set (p: Polygon): Set (ℝ × ℝ) := p.underlying_chain.as_Set

theorem baby_Jordan (p: Polygon):
  ∃ A B, p.as_Setᶜ = A ∪ B ∧
  A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
  (∀ x ∈ A, ∀ y ∈ A, ∃ (c: chain), c.connects x y ∧ Disjoint c.as_Set p.as_Set) ∧
  (∀ x ∈ B, ∀ y ∈ B, ∃ (c: chain), c.connects x y ∧ Disjoint c.as_Set p.as_Set) ∧
  (∀ x ∈ A, ∀ y ∈ B, ∀ (c: chain), c.connects x y → Disjoint c.as_Set p.as_Set → False) := sorry


structure Jordan_curve where
  param: UnitAddCircle → ℝ × ℝ
  param_continuous: Continuous param
  param_injective: Function.Injective param

theorem Jordan_curve_theorem (jc: Jordan_curve):
  ∃ A B, (Set.range jc.param)ᶜ = A ∪ B ∧
  A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
  IsConnected A ∧ IsConnected B ∧ IsOpen A ∧ IsOpen B := sorry




#min_imports
