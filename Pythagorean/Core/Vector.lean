module

/-!
# 方法 2：向量（内积）法（不依赖 Mathlib）

在内积空间中，若 `⟪x, y⟫ = 0`，则展开
`‖x + y‖² = ⟪x + y, x + y⟫ = ⟪x, x⟫ + 2⟪x, y⟫ + ⟪y, y⟫`，
中间项为零，得到 `‖x + y‖² = ‖x‖² + ‖y‖²`。

核心库没有内积空间，这里自己定义一个最小的结构 `InnerSpace`
（对称、对第一个变量可加的内积）。本文件没有任何 `import`。
-/

@[expose] public section

namespace Pythagoras.Vector

universe u v

/-- 一个最小的“内积空间”结构：向量集合 `V` 带加法、零向量，
以及取值在交换环 `α` 中的对称、对第一个变量可加的内积 `⟪·, ·⟫`。 -/
class InnerSpace (α : Type u) (V : Type v) [Lean.Grind.CommRing α] [Add V] [Zero V] where
  /-- 内积 `⟪x, y⟫`。 -/
  inner : V → V → α
  /-- 对第一个变量可加。 -/
  inner_add_left : ∀ x y z : V, inner (x + y) z = inner x z + inner y z
  /-- 零向量与任何向量的内积为零。 -/
  inner_zero_left : ∀ z : V, inner 0 z = 0
  /-- 对称性。 -/
  inner_comm : ∀ x y : V, inner x y = inner y x

namespace InnerSpace

variable {α : Type u} {V : Type v} [Lean.Grind.CommRing α] [Add V] [Zero V] [InnerSpace α V]

/-- 范数平方 `‖x‖² = ⟪x, x⟫`。 -/
def normSq (x : V) : α := inner x x

theorem inner_add_right (x y z : V) : inner (α := α) x (y + z) = inner x y + inner x z := by
  rw [inner_comm, inner_add_left, inner_comm y, inner_comm z]

theorem inner_zero_right (x : V) : inner (α := α) x 0 = 0 := by
  rw [inner_comm, inner_zero_left]

end InnerSpace

open InnerSpace in
/-- **向量版勾股定理**：若 `⟪x, y⟫ = 0`，则 `‖x + y‖² = ‖x‖² + ‖y‖²`。 -/
theorem vector {α : Type u} {V : Type v} [Lean.Grind.CommRing α] [Add V] [Zero V]
    [InnerSpace α V] (x y : V) (h : inner (α := α) x y = 0) :
    normSq (α := α) (x + y) = normSq x + normSq y := by
  unfold normSq
  rw [inner_add_left, inner_add_right, inner_add_right, inner_comm y x, h]
  grind

/-! ## 具体例子：平面向量 -/

/-- 平面向量 `(x, y)`。 -/
structure Vec2 (α : Type u) where
  x : α
  y : α

namespace Vec2

variable {α : Type u} [Lean.Grind.CommRing α]

instance : Add (Vec2 α) := ⟨fun u v => ⟨u.x + v.x, u.y + v.y⟩⟩
instance : Zero (Vec2 α) := ⟨⟨0, 0⟩⟩

/-- 点积 `u · v = u.x v.x + u.y v.y`。 -/
def dot (u v : Vec2 α) : α := u.x * v.x + u.y * v.y

/-- 平面向量在点积下构成内积空间。 -/
instance : InnerSpace α (Vec2 α) where
  inner := dot
  inner_add_left := by
    intro a b c
    show (a.x + b.x) * c.x + (a.y + b.y) * c.y = (a.x * c.x + a.y * c.y) + (b.x * c.x + b.y * c.y)
    grind
  inner_zero_left := by
    intro c
    show (0 : α) * c.x + 0 * c.y = 0
    grind
  inner_comm := by
    intro a b
    show a.x * b.x + a.y * b.y = b.x * a.x + b.y * a.y
    grind

end Vec2

/-- 例：`(3, 0) ⊥ (0, 4)`，于是 `‖(3, 4)‖² = 9 + 16 = 25`。 -/
example : InnerSpace.normSq (α := Int) ((⟨3, 0⟩ : Vec2 Int) + ⟨0, 4⟩) = 25 :=
  (vector (α := Int) (⟨3, 0⟩ : Vec2 Int) ⟨0, 4⟩ (by decide)).trans (by decide)

end Pythagoras.Vector

end
