module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# 方法 2（Mathlib 版）：向量（内积）法

使用 Mathlib 中真正的实内积空间 `InnerProductSpace ℝ F`（范数 `‖·‖` 取实数值），
直接调用 Mathlib 已有的勾股定理
`norm_add_sq_eq_norm_sq_add_norm_sq_real` 与
`norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero`。
只导入 `Mathlib.Analysis.InnerProductSpace.Basic`。
-/

@[expose] public section

namespace PythagorasMathlib.InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **向量版勾股定理**：若 `⟪x, y⟫ = 0`，则 `‖x + y‖² = ‖x‖² + ‖y‖²`。 -/
theorem vector (x y : F) (h : inner ℝ x y = 0) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  norm_add_sq_eq_norm_sq_add_norm_sq_real h

/-- **向量版勾股定理及逆定理**：`‖x + y‖² = ‖x‖² + ‖y‖²` 当且仅当 `⟪x, y⟫ = 0`。 -/
theorem vector_iff (x y : F) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ inner ℝ x y = 0 :=
  norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y

/-- 同一结论用 `^ 2` 写出。 -/
theorem vector_sq (x y : F) (h : inner ℝ x y = 0) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  simpa only [sq] using vector x y h

end PythagorasMathlib.InnerProduct

end
