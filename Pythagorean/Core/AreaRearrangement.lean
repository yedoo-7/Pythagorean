module

/-!
# 方法 7：面积拼图法（不依赖 Mathlib）

边长为 `a + b` 的大正方形，可以拼成：中间一个边长为 `c` 的正方形（斜边围成），
加上四个直角边为 `a, b` 的直角三角形（总面积 `4 · ab/2 = 2ab`）。
比较面积：`(a + b)² = c² + 2ab`，展开即得 `a² + b² = c²`。

几何拼图本身（“这些图形恰好拼成大正方形”）是作为面积等式的前提给出的，
Lean 检查的是从面积等式推出勾股定理的代数部分。本文件没有任何 `import`。
-/

@[expose] public section

namespace Pythagoras.AreaRearrangement

universe u

/-- **面积拼图法**：由面积关系 `(a + b)² = c² + 2ab` 推出 `a² + b² = c²`。 -/
theorem area_proof {α : Type u} [Lean.Grind.CommRing α] (a b c : α)
    (harea : (a + b) ^ 2 = c ^ 2 + 2 * (a * b)) :
    a ^ 2 + b ^ 2 = c ^ 2 := by
  grind

/-- 在有理数上，三角形面积直接写成 `ab/2`：由 `(a + b)² = c² + 4 · (ab/2)` 推出 `a² + b² = c²`。 -/
theorem area_proof_rat (a b c : Rat) (harea : (a + b) ^ 2 = c ^ 2 + 4 * (a * b / 2)) :
    a ^ 2 + b ^ 2 = c ^ 2 := by
  have h4 : 4 * (a * b / 2) = 2 * (a * b) := by grind
  rw [h4] at harea
  exact area_proof a b c harea

end Pythagoras.AreaRearrangement

end
