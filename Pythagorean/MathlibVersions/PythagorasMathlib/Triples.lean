module

public import Mathlib.Data.Real.Sqrt
public import Mathlib.Tactic.Ring

/-!
# 附（Mathlib 版）：勾股数与斜边公式 `c = √(a² + b²)`

* `triple_param`：勾股数公式（整数，`ring`）；
* `hypotenuse_eq_sqrt`：长度非负时，`c² = a² + b²` 当且仅当 `c = √(a² + b²)`（实数平方根）。
只导入实数平方根 `Mathlib.Data.Real.Sqrt` 和 `ring` 策略。
-/

@[expose] public section

namespace PythagorasMathlib.Triples

/-- **勾股数参数化**：`(m² - n², 2mn, m² + n²)` 满足勾股关系。 -/
theorem triple_param (m n : ℤ) :
    (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
  ring

/-- **斜边公式**：对 `c ≥ 0`，`c² = a² + b²` 当且仅当 `c = √(a² + b²)`。 -/
theorem hypotenuse_eq_sqrt (a b c : ℝ) (hc : 0 ≤ c) :
    c ^ 2 = a ^ 2 + b ^ 2 ↔ c = √(a ^ 2 + b ^ 2) := by
  rw [eq_comm (a := c), Real.sqrt_eq_iff_eq_sq (by positivity) hc, eq_comm]

/-- 例：直角边为 `3, 4` 时斜边为 `5`。 -/
example : √((3 : ℝ) ^ 2 + 4 ^ 2) = 5 := by
  rw [show (3 : ℝ) ^ 2 + 4 ^ 2 = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

end PythagorasMathlib.Triples

end
