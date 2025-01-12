import Mathlib
import ImportGraph.Imports

-- definition of Chain and Polygon

def get_segment (points: List (ℝ × ℝ)) (n: Fin (points.length - 1)): Set (ℝ × ℝ) :=
  segment (𝕜 := ℝ × ℝ) (points[n.1]'(by omega)) (points[n.1 + 1]'(by omega))

structure Chain where
  points: List (ℝ × ℝ)
  min_size: 2 ≤ points.length
  property_of_consecutive_segments: ∀ n m, n.1 + 1 = m.1 →
    (get_segment points n) ∩ (get_segment points m) = { points[m.1]'(by omega) }
  nonconsecutive_segments_disjoint:
    ∀ n m, n.1 + 1 < m.1 → Disjoint (get_segment points n) (get_segment points m)

def Chain.first (c: Chain): ℝ × ℝ := c.points[0]'(by cases c; simp at *; omega)
def Chain.last (c: Chain): ℝ × ℝ := c.points[c.points.length - 1]'(by cases c; simp at *; omega)
def Chain.connects (c: Chain) (x y: ℝ × ℝ): Prop := c.first = x ∧ c.last = y
def Chain.as_Set (c: Chain): Set (ℝ × ℝ) := λ p => ∃ n, p ∈ get_segment c.points n

structure Polygon extends Chain where
  chain: Chain
  can_be_closed: ∀ n, Disjoint (get_segment chain.points n) (openSegment (𝕜 := ℝ × ℝ) chain.first chain.last)

def Polygon.as_Set (p: Polygon) := p.chain.as_Set ∪ segment (𝕜 := ℝ × ℝ) p.chain.first p.chain.last

def example_of_chain: Chain :=
  Chain.mk [(1, 2), (3, 4)]
  (by simp)
  (by simp)
  (by simp)


--- place for useful stuff, sorried lemmas etc. (for now)

def Chain_has_distinct_points (c: Chain): c.points.Nodup := by
  sorry

noncomputable def delta (q r s: ℝ × ℝ): ℝ := Real.sign ((r.1 - q.1) * (s.2 - q.2) - (r.2 - q.2) * (s.1 - q.1))

noncomputable def right_cross (q r s: ℝ × ℝ): ℝ :=
  if (s.2 < r.2)
  then if (q.2 ≤ s.2) ∨ (r.2 < q.2) then 1 else delta q s r
  else if (q.2 ≤ r.2) ∨ (s.2 < q.2) then 1 else delta q r s

noncomputable def point_in_polygon (p: Polygon) (q: ℝ × ℝ): ℝ :=
  let ps := p.chain.points
  let one: Fin ps.length := ⟨1, by have H := p.chain.min_size; unfold ps; omega⟩
  (- ∏ (n: Fin (ps.length)), right_cross q (ps[n.1]'(n.2)) (ps[n.add one]'(by simp)))


--- statement of baby Jordan
theorem baby_Jordan (p: Polygon):
  ∃ A B, p.as_Setᶜ = A ∪ B ∧
  A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
  (∀ x ∈ A, ∀ y ∈ A, ∃ (c: Chain), c.connects x y ∧ Disjoint c.as_Set p.as_Set) ∧
  (∀ x ∈ B, ∀ y ∈ B, ∃ (c: Chain), c.connects x y ∧ Disjoint c.as_Set p.as_Set) ∧
  (∀ x ∈ A, ∀ y ∈ B, ∀ (c: Chain), c.connects x y → Disjoint c.as_Set p.as_Set → False) := sorry


--- statement of full Jordan
structure Jordan_curve where
  param: UnitAddCircle → ℝ × ℝ
  param_continuous: Continuous param
  param_injective: Function.Injective param

theorem Jordan_curve_theorem (jc: Jordan_curve):
  ∃ A B, (Set.range jc.param)ᶜ = A ∪ B ∧
  A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
  IsConnected A ∧ IsConnected B ∧ IsOpen A ∧ IsOpen B := sorry



#min_imports
