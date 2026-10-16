module

/-!
# 方法 5：复数法（不依赖 Mathlib）

把平面向量看成复数 `z = re + im·i`。`z` 与 `w` 垂直等价于 `Re (z · w̄) = 0`，
而 `|z + w|² = |z|² + |w|² + 2 Re (z · w̄)`，于是得到勾股定理。

核心库没有复数，这里自己定义 `Cplx`。本文件没有任何 `import`。
-/

@[expose] public section

namespace Pythagoras.Complex

universe u

/-- 复数 `re + im·i`，实部和虚部取值在交换环 `α` 中。 -/
structure Cplx (α : Type u) where
  re : α
  im : α

namespace Cplx

variable {α : Type u} [Lean.Grind.CommRing α]

instance : Add (Cplx α) := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Mul (Cplx α) := ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

/-- 共轭复数。 -/
def conj (z : Cplx α) : Cplx α := ⟨z.re, -z.im⟩

/-- 模的平方 `|z|² = re² + im²`。 -/
def normSq (z : Cplx α) : α := z.re ^ 2 + z.im ^ 2

@[simp] theorem add_re (z w : Cplx α) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : Cplx α) : (z + w).im = z.im + w.im := rfl
@[simp] theorem mul_re (z w : Cplx α) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] theorem conj_re (z : Cplx α) : (conj z).re = z.re := rfl
@[simp] theorem conj_im (z : Cplx α) : (conj z).im = -z.im := rfl

/-- `|z + w|² = |z|² + |w|² + 2 Re (z · w̄)`。 -/
theorem normSq_add (z w : Cplx α) :
    normSq (z + w) = normSq z + normSq w + 2 * (z * conj w).re := by
  simp only [normSq, add_re, add_im, mul_re, conj_re, conj_im]
  grind

end Cplx

open Cplx in
/-- **复数版勾股定理**：若 `Re (z · w̄) = 0`（`z, w` 作为平面向量垂直），
则 `|z + w|² = |z|² + |w|²`。 -/
theorem complex {α : Type u} [Lean.Grind.CommRing α] (z w : Cplx α)
    (h : (z * conj w).re = 0) :
    normSq (z + w) = normSq z + normSq w := by
  rw [normSq_add, h]
  grind

/-- 例：`|3 + 4i|² = 25`。 -/
example : Cplx.normSq (⟨3, 4⟩ : Cplx Int) = 25 := by decide

end Pythagoras.Complex

end
