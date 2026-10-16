module

/-!
# 方法 4：三维空间（不依赖 Mathlib）

* `space`：三维中两个互相垂直的向量，和的长度平方等于各自长度平方之和；
* `box_diagonal`：长方体对角线——两次使用平面勾股定理。

本文件没有任何 `import`。
-/

@[expose] public section

namespace Pythagoras.Space3D

universe u

/-- **三维空间版勾股定理**：若 `(x₁, x₂, x₃) ⊥ (y₁, y₂, y₃)`（点积为零），
则它们之和的长度平方等于各自长度平方之和。 -/
theorem space {α : Type u} [Lean.Grind.CommRing α] (x₁ x₂ x₃ y₁ y₂ y₃ : α)
    (h : x₁ * y₁ + x₂ * y₂ + x₃ * y₃ = 0) :
    (x₁ + y₁) ^ 2 + (x₂ + y₂) ^ 2 + (x₃ + y₃) ^ 2
      = (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) + (y₁ ^ 2 + y₂ ^ 2 + y₃ ^ 2) := by
  grind

/-- **长方体对角线**：棱长为 `a, b, c` 的长方体，底面对角线 `e` 满足 `e² = a² + b²`，
体对角线 `d` 满足 `d² = e² + c²`，所以 `d² = a² + b² + c²`。 -/
theorem box_diagonal {α : Type u} [Lean.Grind.CommRing α] (a b c d e : α)
    (hface : e ^ 2 = a ^ 2 + b ^ 2) (hdiag : d ^ 2 = e ^ 2 + c ^ 2) :
    d ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  grind

/-- 例：`1² + 2² + 2² = 3²`。 -/
example : (1 : Int) ^ 2 + 2 ^ 2 + 2 ^ 2 = 3 ^ 2 := by decide

end Pythagoras.Space3D

end
