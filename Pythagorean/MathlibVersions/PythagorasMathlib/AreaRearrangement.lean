module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# 方法 7（Mathlib 版）：面积拼图法

边长为 `a + b` 的大正方形 = 边长为 `c` 的正方形 + 四个面积为 `ab/2` 的直角三角形。
由面积等式 `(a + b)² = c² + 4 · (ab/2)` 推出 `a² + b² = c²`（实数，`linear_combination`）。
只导入实数的定义和 `linear_combination` 策略。
-/

@[expose] public section

namespace PythagorasMathlib.AreaRearrangement

/-- **面积拼图法**：由 `(a + b)² = c² + 4 · (ab/2)` 推出 `a² + b² = c²`。 -/
theorem area_proof (a b c : ℝ) (harea : (a + b) ^ 2 = c ^ 2 + 4 * (a * b / 2)) :
    a ^ 2 + b ^ 2 = c ^ 2 := by
  linear_combination harea

end PythagorasMathlib.AreaRearrangement

end
