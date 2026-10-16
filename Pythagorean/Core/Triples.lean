module

/-!
# 附：勾股数与求斜边（不依赖 Mathlib）

这一部分不是勾股定理本身的证明，而是相关的应用：
* `triple_param`：勾股数公式 `(m² - n²)² + (2mn)² = (m² + n²)²`；
* `hypotenuse_unique`：长度非负时斜边由两条直角边唯一确定（即 `c = √(a² + b²)`）；
* `hypotenuse?`：一个可运行的求整数斜边程序，及其正确性证明 `hypotenuse?_spec`。

本文件没有任何 `import`。
-/

@[expose] public section

namespace Pythagoras.Triples

universe u

/-- **勾股数参数化**：`(m² - n², 2mn, m² + n²)` 满足勾股关系。 -/
theorem triple_param {α : Type u} [Lean.Grind.CommRing α] (m n : α) :
    (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
  grind

/-- 例子：`m = 2, n = 1` 给出 `(3, 4, 5)`。 -/
example : ((2 : Int) ^ 2 - 1 ^ 2, 2 * 2 * 1, (2 : Int) ^ 2 + 1 ^ 2) = (3, 4, 5) := by decide

/-- **斜边唯一**：长度非负时，满足 `c² = a² + b²` 的 `c` 是唯一的。 -/
theorem hypotenuse_unique (a b c d : Rat) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hc2 : c ^ 2 = a ^ 2 + b ^ 2) (hd2 : d ^ 2 = a ^ 2 + b ^ 2) : c = d := by
  have h : (c - d) * (c + d) = 0 := by grind
  rcases Rat.mul_eq_zero.mp h with h | h <;> grind

/-- 在自然数中搜索斜边，即满足 `c² = a² + b²` 的 `c`（若存在）。 -/
def hypotenuse? (a b : Nat) : Option Nat :=
  (List.range (a + b + 1)).find? (fun c => c * c == a * a + b * b)

/-- 程序正确性：若 `hypotenuse? a b` 返回 `c`，则 `a² + b² = c²`。 -/
theorem hypotenuse?_spec (a b c : Nat) (h : hypotenuse? a b = some c) :
    a ^ 2 + b ^ 2 = c ^ 2 := by
  unfold hypotenuse? at h
  have := List.find?_some h
  simp only [beq_iff_eq] at this
  rw [Nat.pow_two, Nat.pow_two, Nat.pow_two, this]

example : hypotenuse? 3 4 = some 5 := by decide

-- 输出 some 5、some 13、none（2² + 3² = 13 不是完全平方）
#eval hypotenuse? 3 4
#eval hypotenuse? 5 12
#eval hypotenuse? 2 3

-- 列出所有 a < b ≤ 20 的整数勾股数 (a, b, c)
#eval Id.run do
  let mut out : Array (Nat × Nat × Nat) := #[]
  for a in [1:21] do
    for b in [a+1:21] do
      if let some c := hypotenuse? a b then
        out := out.push (a, b, c)
  return out

end Pythagoras.Triples

end
