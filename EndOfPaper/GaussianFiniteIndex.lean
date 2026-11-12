import EndOfPaper.GaussianOriginalLaw

/-!
Reindex the proved finite-dimensional statement over any finite set of actual independent standard Gaussian coordinates.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_lipschitz_copy_subgaussian_fintype {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X X' : Ω → EuclideanSpace ℝ ι} (hX : Measurable X)
    (hi : iIndepFun (fun i ω => X ω i) μ)
    (hm : ∀ i, Measurable (fun ω => X ω i))
    (hLaw : ∀ i, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    (hInd : IndepFun X X' μ) (hCopy : IdentDistrib X X' μ μ)
    {f : EuclideanSpace ℝ ι → ℝ} (hf : LipschitzWith 1 f) :
    HasSubgaussianMGF (fun ω => f (X ω)-f (X' ω)) 2 μ := by
  let e := Fintype.equivFin ι
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  have hUi (x : EuclideanSpace ℝ ι) (i : Fin (Fintype.card ι)) : U x i = x (e.symm i) := rfl
  have hiU : iIndepFun (fun i ω => U (X ω) i) μ := by
    simpa only [hUi] using iIndepFun.precomp e.symm.injective hi
  have hmU (i : Fin (Fintype.card ι)) : Measurable (fun ω => U (X ω) i) := by
    simpa only [hUi] using hm (e.symm i)
  have hLawU (i : Fin (Fintype.card ι)) :
      Measure.map (fun ω => U (X ω) i) μ = gaussianReal 0 1 := by
    simpa only [hUi] using hLaw (e.symm i)
  have hfU : LipschitzWith 1 (fun z => f (U.symm z)) := by
    simpa only [mul_one] using hf.comp U.symm.isometry.lipschitz
  have hh := gaussian_lipschitz_copy_subgaussian (U.continuous.measurable.comp hX) hiU hmU hLawU
    (hInd.comp U.continuous.measurable U.continuous.measurable)
    (hCopy.comp U.continuous.measurable) hfU
  simpa only [Function.comp_apply,U.symm_apply_apply] using hh

end ScalarMonotone.EndOfPaper
end
