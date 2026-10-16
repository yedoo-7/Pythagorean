module

/-!
# 方法 3：平面几何形式（点、距离、直角）及逆定理（不依赖 Mathlib）

用平面上的点 `A, B, C` 表述：
* `distSq P Q` 是两点距离的平方；
* `IsRightAngle A C B` 表示 `∠ACB` 是直角，即向量 `CA` 与 `CB` 的点积为零
  （这与 `∠ACB = 90°` 等价，Mathlib 中也是这样刻画直角的）。

证明方法：把点拆成坐标，化为代数恒等式后用 `grind` 完成。
本文件没有任何 `import`。
-/

@[expose] public section

namespace Pythagoras.Euclidean

universe u

/-- 平面上的点 `(x, y)`，坐标取值在交换环 `α` 中。 -/
structure Point (α : Type u) where
  x : α
  y : α

variable {α : Type u} [Lean.Grind.CommRing α]

/-- 两点距离的平方 `|PQ|² = (P.x - Q.x)² + (P.y - Q.y)²`。 -/
def distSq (P Q : Point α) : α := (P.x - Q.x) * (P.x - Q.x) + (P.y - Q.y) * (P.y - Q.y)

/-- `∠ACB` 是直角：向量 `CA` 与 `CB` 垂直（点积为零）。 -/
def IsRightAngle (A C B : Point α) : Prop :=
  (A.x - C.x) * (B.x - C.x) + (A.y - C.y) * (B.y - C.y) = 0

/-- **几何版勾股定理**：若三角形 `ABC` 在 `C` 处为直角，则 `|AB|² = |AC|² + |BC|²`。 -/
theorem euclidean (A B C : Point α) (h : IsRightAngle A C B) :
    distSq A B = distSq A C + distSq B C := by
  simp only [IsRightAngle, distSq] at h ⊢
  grind

/-- **勾股定理的逆定理**：若 `|AB|² = |AC|² + |BC|²`，则 `C` 处是直角。
需要 `2` 不是零因子（`Int`、`Rat`、实数都满足）。 -/
theorem euclidean_converse [Lean.Grind.NoNatZeroDivisors α] (A B C : Point α)
    (h : distSq A B = distSq A C + distSq B C) :
    IsRightAngle A C B := by
  simp only [IsRightAngle, distSq] at h ⊢
  grind

/-- 勾股定理与逆定理合起来：`C` 处为直角 ⟺ `|AB|² = |AC|² + |BC|²`。 -/
theorem euclidean_iff [Lean.Grind.NoNatZeroDivisors α] (A B C : Point α) :
    IsRightAngle A C B ↔ distSq A B = distSq A C + distSq B C :=
  ⟨euclidean A B C, euclidean_converse A B C⟩

/-- 例：`A = (3, 0)`，`B = (0, 4)`，`C = (0, 0)`，`C` 处为直角。 -/
example : IsRightAngle (⟨3, 0⟩ : Point Int) ⟨0, 0⟩ ⟨0, 4⟩ := by
  unfold IsRightAngle
  decide

/-- 例：`|AB|² = 25`。 -/
example : distSq (⟨3, 0⟩ : Point Int) ⟨0, 4⟩ = 25 := by decide

-- 运行时计算：输出 25
#eval distSq (⟨3, 0⟩ : Point Int) ⟨0, 4⟩

-- 有理数坐标：输出 1/2
#eval distSq (⟨1/2, 0⟩ : Point Rat) ⟨0, 1/2⟩

end Pythagoras.Euclidean

end
