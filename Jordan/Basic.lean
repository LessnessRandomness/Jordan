import Mathlib
import ImportGraph.Imports


structure Chain where
  points: List (ℝ × ℝ)
  min_size: 2 ≤ points.length
  get_segment (n: Fin (points.length - 1)): Set (ℝ × ℝ) :=
    segment (𝕜 := ℝ × ℝ) (points[n.1]'(by omega)) (points[n.1 + 1]'(by omega))
  property_of_consecutive_segments:
    ∀ (n m: Fin (points.length - 1)), n.1 + 1 = m.1 →
    (get_segment n) ∩ (get_segment m) = { points[m.1]'(by omega) }
  nonconsecutive_segments_disjoint:
    ∀ (n m: Fin (points.length - 1)), n.1 + 1 < m.1 → Disjoint (get_segment n) (get_segment m)

def Chain.first (c: Chain): ℝ × ℝ := c.points[0]'(by cases c; simp at *; omega)
def Chain.last (c: Chain): ℝ × ℝ := c.points[c.points.length - 1]'(by cases c; simp at *; omega)
def Chain.connects (c: Chain) (x y: ℝ × ℝ) := c.first = x ∧ c.last = y
def Chain.as_Set (c: Chain): Set (ℝ × ℝ) := λ (p: ℝ × ℝ) => ∃ (n: Fin (c.points.length - 1)), p ∈ c.get_segment n

structure Polygon where
  chain: Chain
  can_be_closed: ∀ (n: Fin (chain.points.length - 1)), Disjoint (chain.get_segment n) (openSegment (𝕜 := ℝ × ℝ) chain.first chain.last)

def Polygon.as_Set (p: Polygon) := p.chain.as_Set ∪ segment (𝕜 := ℝ × ℝ) p.chain.first p.chain.last

theorem baby_Jordan (p: Polygon):
  ∃ A B, p.as_Setᶜ = A ∪ B ∧
  A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
  (∀ x ∈ A, ∀ y ∈ A, ∃ (c: Chain), c.connects x y ∧ Disjoint c.as_Set p.as_Set) ∧
  (∀ x ∈ B, ∀ y ∈ B, ∃ (c: Chain), c.connects x y ∧ Disjoint c.as_Set p.as_Set) ∧
  (∀ x ∈ A, ∀ y ∈ B, ∀ (c: Chain), c.connects x y → Disjoint c.as_Set p.as_Set → False) := sorry


structure Jordan_curve where
  param: UnitAddCircle → ℝ × ℝ
  param_continuous: Continuous param
  param_injective: Function.Injective param

theorem Jordan_curve_theorem (jc: Jordan_curve):
  ∃ A B, (Set.range jc.param)ᶜ = A ∪ B ∧
  A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
  IsConnected A ∧ IsConnected B ∧ IsOpen A ∧ IsOpen B := sorry




#min_imports
