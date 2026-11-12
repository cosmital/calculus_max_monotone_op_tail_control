import EndOfPaper.GaussianProductMeasure

/-!
Independence of actual disjoint finite coordinate groups, followed by their Euclidean realizations.
-/

open Set MeasureTheory ProbabilityTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_independent_coordinate_groups {Ω κ m n : Type*}
    [MeasurableSpace Ω] [Fintype m] [Fintype n] {μ : Measure Ω}
    (X : κ → Ω → ℝ) (hi : iIndepFun X μ) (hm : ∀ k, Measurable (X k))
    (s : m → κ) (t : n → κ) (hst : ∀ i j, s i ≠ t j) :
    IndepFun (fun ω i => X (s i) ω) (fun ω j => X (t j) ω) μ := by
  classical
  let S : Finset κ := Finset.univ.image s
  let T : Finset κ := Finset.univ.image t
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro k hkS hkT
    obtain ⟨i,_,hsi⟩ := Finset.mem_image.mp hkS
    obtain ⟨j,_,htj⟩ := Finset.mem_image.mp hkT
    exact hst i j (hsi.trans htj.symm)
  have hGroups := hi.indepFun_finset S T hST hm
  have hs (i : m) : s i ∈ S := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have ht (j : n) : t j ∈ T := Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  have hS : Measurable (fun z : S → ℝ => fun i : m => z ⟨s i,hs i⟩) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have hT : Measurable (fun z : T → ℝ => fun j : n => z ⟨t j,ht j⟩) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  simpa only [Function.comp_apply] using hGroups.comp hS hT

end ScalarMonotone.EndOfPaper
end
