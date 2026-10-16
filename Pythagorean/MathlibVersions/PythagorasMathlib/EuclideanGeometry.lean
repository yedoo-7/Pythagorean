module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

/-!
# 方法 3（Mathlib 版）：欧氏几何形式（真正的角 `∠ = π/2`）

在 Mathlib 的欧氏几何框架中（任意实内积空间上的仿射空间，例如平面 `ℝ²`），
点 `A, B, C` 之间的距离是 `dist`，`∠ A C B` 是真正的（无向）角，取值在 `[0, π]`。
Mathlib 已证明：`|AB|² = |AC|² + |BC|²` 当且仅当 `∠ A C B = π / 2`。
只导入 `Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle`。
-/

@[expose] public section

namespace PythagorasMathlib.EuclideanGeometry

open _root_.EuclideanGeometry Real

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **几何版勾股定理**：若 `∠ A C B = 90°`，则 `|AB|² = |AC|² + |BC|²`。 -/
theorem euclidean (A B C : P) (h : ∠ A C B = π / 2) :
    dist A B * dist A B = dist A C * dist A C + dist B C * dist B C :=
  (dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two A C B).mpr h

/-- **逆定理**：若 `|AB|² = |AC|² + |BC|²`，则 `∠ A C B = 90°`。 -/
theorem euclidean_converse (A B C : P)
    (h : dist A B * dist A B = dist A C * dist A C + dist B C * dist B C) :
    ∠ A C B = π / 2 :=
  (dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two A C B).mp h

/-- 勾股定理与逆定理合起来。 -/
theorem euclidean_iff (A B C : P) :
    dist A B * dist A B = dist A C * dist A C + dist B C * dist B C ↔ ∠ A C B = π / 2 :=
  dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two A C B

end PythagorasMathlib.EuclideanGeometry

end
