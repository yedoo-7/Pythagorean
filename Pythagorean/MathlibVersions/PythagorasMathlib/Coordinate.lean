module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# 方法 1（Mathlib 版）：实数坐标法

与核心库版本相同的思路，但坐标直接取实数 `ℝ`，证明用 Mathlib 的 `linear_combination`。
只导入实数的定义和 `linear_combination` 策略所需的最小模块。
-/

@[expose] public section

namespace PythagorasMathlib.Coordinate

/-- **坐标版勾股定理（实数坐标）**：若 `CA ⊥ CB`（点积为零），则 `|AB|² = |AC|² + |BC|²`。 -/
theorem coord (a₁ a₂ b₁ b₂ c₁ c₂ : ℝ)
    (hperp : (a₁ - c₁) * (b₁ - c₁) + (a₂ - c₂) * (b₂ - c₂) = 0) :
    (a₁ - b₁) ^ 2 + (a₂ - b₂) ^ 2
      = ((a₁ - c₁) ^ 2 + (a₂ - c₂) ^ 2) + ((b₁ - c₁) ^ 2 + (b₂ - c₂) ^ 2) := by
  linear_combination (-2 : ℝ) * hperp

/-- **逆定理**：若 `|AB|² = |AC|² + |BC|²`，则 `CA ⊥ CB`。 -/
theorem coord_converse (a₁ a₂ b₁ b₂ c₁ c₂ : ℝ)
    (h : (a₁ - b₁) ^ 2 + (a₂ - b₂) ^ 2
      = ((a₁ - c₁) ^ 2 + (a₂ - c₂) ^ 2) + ((b₁ - c₁) ^ 2 + (b₂ - c₂) ^ 2)) :
    (a₁ - c₁) * (b₁ - c₁) + (a₂ - c₂) * (b₂ - c₂) = 0 := by
  linear_combination (-1 / 2 : ℝ) * h

end PythagorasMathlib.Coordinate

end
