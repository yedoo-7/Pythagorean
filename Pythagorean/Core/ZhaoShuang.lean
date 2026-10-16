module

/-!
# 方法 8：赵爽弦图（不依赖 Mathlib）

三国时期赵爽的“弦图”：边长为 `c`（弦）的正方形，由四个直角边为 `a, b`
的直角三角形（总面积 `2ab`）和中间一个边长为 `b - a` 的小正方形拼成。
比较面积：`c² = (b - a)² + 2ab`，展开即得 `a² + b² = c²`。

与方法 7 一样，几何拼图作为面积等式的前提给出，Lean 检查代数推导部分。
本文件没有任何 `import`。
-/

@[expose] public section

namespace Pythagoras.ZhaoShuang

universe u

/-- **赵爽弦图**：由面积关系 `c² = (b - a)² + 2ab` 推出 `a² + b² = c²`。 -/
theorem zhao_shuang {α : Type u} [Lean.Grind.CommRing α] (a b c : α)
    (harea : c ^ 2 = (b - a) ^ 2 + 2 * (a * b)) :
    a ^ 2 + b ^ 2 = c ^ 2 := by
  grind

/-- 有理数上，三角形面积写成 `ab/2`：由 `c² = (b - a)² + 4 · (ab/2)` 推出 `a² + b² = c²`。 -/
theorem zhao_shuang_rat (a b c : Rat) (harea : c ^ 2 = (b - a) ^ 2 + 4 * (a * b / 2)) :
    a ^ 2 + b ^ 2 = c ^ 2 := by
  have h4 : 4 * (a * b / 2) = 2 * (a * b) := by grind
  rw [h4] at harea
  exact zhao_shuang a b c harea

end Pythagoras.ZhaoShuang

end
