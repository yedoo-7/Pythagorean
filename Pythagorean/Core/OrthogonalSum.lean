module

public import Core.Vector

/-!
# 方法 6：n 个两两正交向量（不依赖 Mathlib）

把方法 2（向量法）推广到任意多个向量：若 `v₁, …, vₙ` 两两正交，则
`‖v₁ + ⋯ + vₙ‖² = ‖v₁‖² + ⋯ + ‖vₙ‖²`。证明方法：对列表长度做数学归纳。

本文件只导入同一项目中的方法 2 文件（为了复用其中的 `InnerSpace` 结构），不导入 Mathlib。
-/

@[expose] public section

namespace Pythagoras.OrthogonalSum

open Pythagoras.Vector Pythagoras.Vector.InnerSpace

universe u v

variable {α : Type u} {V : Type v} [Lean.Grind.CommRing α] [Add V] [Zero V] [InnerSpace α V]

/-- 向量列表的和 `v₁ + ⋯ + vₙ`。 -/
def vsum : List V → V
  | [] => 0
  | x :: l => x + vsum l

/-- 若 `x` 与列表中每个向量都正交，则 `x` 与它们的和正交。 -/
theorem inner_vsum_eq_zero (x : V) :
    ∀ l : List V, (∀ y ∈ l, inner (α := α) x y = 0) → inner (α := α) x (vsum l) = 0
  | [], _ => inner_zero_right x
  | y :: l, h => by
    rw [vsum, inner_add_right, h y (List.mem_cons_self ..),
      inner_vsum_eq_zero x l (fun z hz => h z (List.mem_cons_of_mem _ hz))]
    grind

/-- **n 个向量的勾股定理**：若列表 `l` 中的向量两两正交，
则 `‖v₁ + ⋯ + vₙ‖² = ‖v₁‖² + ⋯ + ‖vₙ‖²`。 -/
theorem vector_sum :
    ∀ l : List V, l.Pairwise (fun x y => inner (α := α) x y = 0) →
      normSq (α := α) (vsum l) = (l.map (normSq (α := α))).foldr (· + ·) 0
  | [], _ => by
    show inner (α := α) (0 : V) 0 = 0
    exact inner_zero_left 0
  | x :: l, h => by
    rw [List.pairwise_cons] at h
    have hx : inner (α := α) x (vsum l) = 0 := inner_vsum_eq_zero x l h.1
    have ih := vector_sum l h.2
    simp only [List.map_cons, List.foldr_cons]
    rw [← ih]
    unfold normSq
    rw [vsum, inner_add_left, inner_add_right, inner_add_right, inner_comm (vsum l) x, hx]
    grind

end Pythagoras.OrthogonalSum

end
