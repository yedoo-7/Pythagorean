# 勾股定理：按证明方法分类的文件目录

每一种证明方法都放在单独的 `.lean` 文件里，分成两套：

* **核心库版**（`RequestProject/Core/`）：不依赖 Mathlib，只用 Lean 4 自带的核心库，
  在根目录运行 `lake build` 即可编译。核心库没有实数，定理对任意交换环陈述（`Int`、`Rat`、实数都适用）。
* **Mathlib 版**（`MathlibVersions/PythagorasMathlib/`）：使用 Mathlib，但**不 `import Mathlib`**，
  每个文件只导入它实际用到的最小模块。这是一个独立的 Lake 子项目（固定 Mathlib 版本）。

| # | 证明方法 | 核心库版（无 import） | Mathlib 版 | Mathlib 版的导入 |
|---|---|---|---|---|
| 1 | 坐标法（含逆定理） | `Core/Coordinate.lean` | `Coordinate.lean` | `Mathlib.Data.Real.Basic`、`Mathlib.Tactic.LinearCombination` |
| 2 | 向量（内积）法 | `Core/Vector.lean` | `InnerProduct.lean` | `Mathlib.Analysis.InnerProductSpace.Basic` |
| 3 | 平面几何（点、距离、直角）及逆定理 | `Core/Euclidean.lean` | `EuclideanGeometry.lean`（真正的角 `∠ A C B = π/2`） | `Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle` |
| 4 | 三维空间 / 长方体对角线 | `Core/Space3D.lean` | `Space3D.lean`（`EuclideanSpace ℝ (Fin 3)`） | `Mathlib.Analysis.InnerProductSpace.PiL2` |
| 5 | 复数法 | `Core/Complex.lean` | `Complex.lean`（Mathlib 的 `ℂ`） | `Mathlib.Data.Complex.Basic` |
| 6 | n 个两两正交向量（归纳法） | `Core/OrthogonalSum.lean`（导入方法 2 的文件） | `OrthogonalSum.lean`（有限集求和） | `Mathlib.Analysis.InnerProductSpace.Basic` |
| 7 | 面积拼图法 | `Core/AreaRearrangement.lean` | `AreaRearrangement.lean` | `Mathlib.Data.Real.Basic`、`Mathlib.Tactic.LinearCombination` |
| 8 | 赵爽弦图 | `Core/ZhaoShuang.lean` | `ZhaoShuang.lean` | `Mathlib.Data.Real.Basic`、`Mathlib.Tactic.LinearCombination` |
| 附 | 勾股数、求斜边（应用，不是定理本身的证明） | `Core/Triples.lean` | `Triples.lean`（`c = √(a² + b²)`） | `Mathlib.Data.Real.Sqrt`、`Mathlib.Tactic.Ring` |

`RequestProject/Main.lean` 汇总导入全部核心库版文件。

说明：方法 7、8 中，“这些图形恰好拼成一个正方形”这一几何事实作为面积等式的前提给出，
Lean 检查的是由面积等式推出 \( a^2 + b^2 = c^2 \) 的部分。

## 如何编译

核心库版（无需 Mathlib）：

```
lake build
```

Mathlib 版（需要联网下载 Mathlib 及其预编译缓存）：

```
cd MathlibVersions
lake exe cache get
lake build
```

所有文件都没有 `sorry`，也没有新增 `axiom`。
