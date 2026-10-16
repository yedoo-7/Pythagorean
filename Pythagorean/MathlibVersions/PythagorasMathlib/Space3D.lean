module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# 方法 4（Mathlib 版）：三维欧氏空间

在 Mathlib 的三维欧氏空间 `EuclideanSpace ℝ (Fin 3)` 中，
距离平方等于各坐标差的平方和（`EuclideanSpace.dist_sq_eq`，这本身就是 n 维勾股定理），
于是长方体对角线公式成立。另外给出三维中垂直向量的勾股定理。
只导入 `Mathlib.Analysis.InnerProductSpace.PiL2`。
-/

@[expose] public section

namespace PythagorasMathlib.Space3D

open Real

/-- **n 维距离公式（勾股定理的推广）**：`dist x y ^ 2 = ∑ᵢ (xᵢ - yᵢ)²`。 -/
theorem dist_sq {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    dist x y ^ 2 = ∑ i, (x i - y i) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [Real.dist_eq, sq_abs]

/-- **三维距离公式 / 长方体对角线**：`|xy|² = (x₀-y₀)² + (x₁-y₁)² + (x₂-y₂)²`。 -/
theorem box_diagonal (x y : EuclideanSpace ℝ (Fin 3)) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 := by
  rw [dist_sq, Fin.sum_univ_three]

/-- **三维空间中垂直向量的勾股定理**。 -/
theorem space (x y : EuclideanSpace ℝ (Fin 3)) (h : inner ℝ x y = 0) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  simpa only [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_real h

end PythagorasMathlib.Space3D

end
