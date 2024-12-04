import Mathlib
import ImportGraph.Imports


structure Jordan_curve where
  param: UnitAddCircle → ℝ × ℝ
  param_continuous: Continuous param
  param_injective: Function.Injective param


noncomputable instance UnitAddCircle_LE: LE UnitAddCircle := by
  have equiv := @AddCircle.equivIco ℝ _ 1 _ 0 _
  constructor
  exact (λ x y => equiv.toFun x ≤ equiv.toFun y)

noncomputable instance UnitAddCircle_LT: LT UnitAddCircle := by
  have equiv := @AddCircle.equivIco ℝ _ 1 _ 0 _
  constructor
  exact (λ x y => equiv.toFun x < equiv.toFun y)

noncomputable instance UnitAddCircle_Preorder: Preorder UnitAddCircle := by
  constructor
  . intros a
    simp [UnitAddCircle_LE]
  . intros a b c H H0
    simp [UnitAddCircle_LE] at *
    exact Preorder.le_trans _ _ _ H H0
  . intros a b
    simp [UnitAddCircle_LE, UnitAddCircle_LT]
    intros H
    exact le_of_lt H


structure Polygon where
  jc: Jordan_curve
  size: ℕ
  min_size: 3 ≤ size
  times: Fin size → UnitAddCircle
  times_monotone: Monotone times
  start: times ⟨0, by omega⟩ = 0
  polygonal:
    ∀ (n: Fin size) (H: n.val + 1 < size),
    let n_add_1 := n.add ⟨1, by omega⟩
    jc.param '' Set.Ioo (times n) (times n_add_1) =
    openSegment (𝕜 := ℝ × ℝ) (jc.param (times n)) (jc.param (times n_add_1))
  closed: ∀ (t: UnitAddCircle),
    let n_last := ⟨size - 1, by omega⟩
    times n_last < t →
    jc.param '' (Set.Ioo (times n_last) t) =
    openSegment (𝕜 := ℝ × ℝ) (jc.param (times n_last)) (jc.param t)


structure chain where
  points: List (ℝ × ℝ)
  min_size: 2 ≤ points.length

def chain.first (c: chain): ℝ × ℝ := c.points[0]'(by cases c; simp at *; omega)
def chain.last (c: chain): ℝ × ℝ := c.points[c.points.length - 1]'(by cases c; simp at *; omega)

def chain.connects (c: chain) (x y: ℝ × ℝ) := c.first = x ∧ c.last = y

def chain.as_Set (c: chain): Set (ℝ × ℝ) :=
  λ (p: ℝ × ℝ) => ∃ (n: ℕ), ∀ (H: n + 1 < c.points.length), p ∈ Set.Icc (c.points[n]'(by omega)) (c.points[n + 1]'H)

theorem baby_Jordan (p: Polygon):
  let curve := Set.range p.jc.param
  ∃ A B, curveᶜ = A ∪ B ∧
  A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
  (∀ x ∈ A, ∀ y ∈ A, ∃ (c: chain), c.connects x y ∧ Disjoint c.as_Set curve) ∧
  (∀ x ∈ B, ∀ y ∈ B, ∃ (c: chain), c.connects x y ∧ Disjoint c.as_Set curve) ∧
  (∀ x ∈ A, ∀ y ∈ B, ∀ (c: chain), c.connects x y → Disjoint c.as_Set curve → False) := sorry



theorem Jordan_curve_theorem (jc: Jordan_curve):
  ∃ A B, (Set.range jc.param)ᶜ = A ∪ B ∧
  A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
  IsConnected A ∧ IsConnected B ∧ IsOpen A ∧ IsOpen B := sorry




#min_imports
