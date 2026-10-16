module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# 方法 6（Mathlib 版）：n 个两两正交向量

在实内积空间中，若有限族 `v i`（`i ∈ s`）两两正交，则
`‖∑ v i‖² = ∑ ‖v i‖²`。证明：对有限集 `s` 归纳，每一步用两个向量的勾股定理。
只导入 `Mathlib.Analysis.InnerProductSpace.Basic`。
-/

@[expose] public section

namespace PythagorasMathlib.OrthogonalSum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {ι : Type*}

/-- **n 个向量的勾股定理**：若 `s` 中下标不同的向量两两正交，
则 `‖∑ᵢ vᵢ‖² = ∑ᵢ ‖vᵢ‖²`。 -/
theorem vector_sum [DecidableEq ι] (v : ι → F) (s : Finset ι)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (v i) (v j) = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (v i) (v j) = 0 := fun i hi j hj hij =>
      h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have horth : inner ℝ (v a) (∑ i ∈ s, v i) = 0 := by
      rw [inner_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      exact h a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun hai => ha (hai ▸ hi))
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih hs]
    simpa only [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth

end PythagorasMathlib.OrthogonalSum

end
