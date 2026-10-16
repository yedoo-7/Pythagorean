module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# 方法 8（Mathlib 版）：赵爽弦图

边长为 `c` 的正方形 = 四个面积为 `ab/2` 的直角三角形 + 边长为 `b - a` 的小正方形。
由面积等式 `c² = (b - a)² + 4 · (ab/2)` 推出 `a² + b² = c²`（实数，`linear_combination`）。
只导入实数的定义和 `linear_combination` 策略。
-/

@[expose] public section

namespace PythagorasMathlib.ZhaoShuang

/-- **赵爽弦图**：由 `c² = (b - a)² + 4 · (ab/2)` 推出 `a² + b² = c²`。 -/
theorem zhao_shuang (a b c : ℝ) (harea : c ^ 2 = (b - a) ^ 2 + 4 * (a * b / 2)) :
    a ^ 2 + b ^ 2 = c ^ 2 := by
  linear_combination -harea

end PythagorasMathlib.ZhaoShuang

end
