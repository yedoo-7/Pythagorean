module

public import Mathlib.Data.Complex.Basic

/-!
# 方法 5（Mathlib 版）：复数法

使用 Mathlib 的复数 `ℂ`，以及恒等式
`Complex.normSq_add : normSq (z + w) = normSq z + normSq w + 2 * (z * conj w).re`。
只导入 `Mathlib.Data.Complex.Basic`。
-/

@[expose] public section

namespace PythagorasMathlib.Complex

open _root_.Complex ComplexConjugate

/-- **复数版勾股定理**：若 `Re (z · w̄) = 0`（`z, w` 作为平面向量垂直），
则 `|z + w|² = |z|² + |w|²`。 -/
theorem complex (z w : ℂ) (h : (z * conj w).re = 0) :
    normSq (z + w) = normSq z + normSq w := by
  rw [normSq_add, h, mul_zero, add_zero]

/-- 例：`|3 + 4i|² = 25`。 -/
example : normSq (3 + 4 * I) = 25 := by
  rw [show (3 : ℂ) + 4 * I = (3 : ℝ) + (4 : ℝ) * I by push_cast; ring, normSq_add_mul_I]
  norm_num

end PythagorasMathlib.Complex

end
