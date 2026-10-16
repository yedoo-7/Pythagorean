module

/-!
# 方法 1：坐标法（不依赖 Mathlib）

在平面直角坐标系中，把“`C` 处是直角”写成向量 `CA`、`CB` 的点积为零，
把距离的平方写成坐标差的平方和，勾股定理就变成一个代数恒等式，
由 Lean 核心库自带的 `grind`（含交换环求解器）直接完成证明。

核心库没有实数 `ℝ`，所以定理对**任意交换环** `α`（`Lean.Grind.CommRing`）陈述，
`Int`、`Rat` 以及任何库里的实数都适用。本文件没有任何 `import`。
-/

@[expose] public section

namespace Pythagoras.Coordinate

universe u

/-- **坐标版勾股定理**：设 `A = (a₁, a₂)`，`B = (b₁, b₂)`，`C = (c₁, c₂)`，
若 `CA ⊥ CB`（点积为零），则 `|AB|² = |AC|² + |BC|²`。 -/
theorem coord {α : Type u} [Lean.Grind.CommRing α] (a₁ a₂ b₁ b₂ c₁ c₂ : α)
    (hperp : (a₁ - c₁) * (b₁ - c₁) + (a₂ - c₂) * (b₂ - c₂) = 0) :
    (a₁ - b₁) ^ 2 + (a₂ - b₂) ^ 2
      = ((a₁ - c₁) ^ 2 + (a₂ - c₂) ^ 2) + ((b₁ - c₁) ^ 2 + (b₂ - c₂) ^ 2) := by
  grind

/-- **坐标版勾股定理及其逆定理**：`CA ⊥ CB` 当且仅当 `|AB|² = |AC|² + |BC|²`。
逆方向需要 `2` 不是零因子（`Int`、`Rat`、实数都满足）。 -/
theorem coord_iff {α : Type u} [Lean.Grind.CommRing α] [Lean.Grind.NoNatZeroDivisors α]
    (a₁ a₂ b₁ b₂ c₁ c₂ : α) :
    (a₁ - c₁) * (b₁ - c₁) + (a₂ - c₂) * (b₂ - c₂) = 0 ↔
      (a₁ - b₁) ^ 2 + (a₂ - b₂) ^ 2
        = ((a₁ - c₁) ^ 2 + (a₂ - c₂) ^ 2) + ((b₁ - c₁) ^ 2 + (b₂ - c₂) ^ 2) := by
  constructor <;> intro h <;> grind

/-- 整数坐标的特例。 -/
theorem coord_int (a₁ a₂ b₁ b₂ c₁ c₂ : Int)
    (hperp : (a₁ - c₁) * (b₁ - c₁) + (a₂ - c₂) * (b₂ - c₂) = 0) :
    (a₁ - b₁) ^ 2 + (a₂ - b₂) ^ 2
      = ((a₁ - c₁) ^ 2 + (a₂ - c₂) ^ 2) + ((b₁ - c₁) ^ 2 + (b₂ - c₂) ^ 2) :=
  coord a₁ a₂ b₁ b₂ c₁ c₂ hperp

/-- 例子：`3² + 4² = 5²`。 -/
example : (3 : Int) ^ 2 + 4 ^ 2 = 5 ^ 2 := by decide

end Pythagoras.Coordinate

end
