import EndOfPaper.GaussianCopyTail
import EndOfPaper.QuantileTailCompletion
import EndOfPaper.SqrtLogProfile

/-!
The original whole maximally completed Gaussian input profile, proved from actual independent Gaussian coordinates and the actual copy law.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_profile_confidence_identity {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    2*Real.exp (-((2*sqrtLogScalar u)^2)/4) = u := by
  have hlogu : Real.log u ≤ 0 := by
    simpa only [Real.log_one] using Real.log_le_log hu.1 hu.2.le
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hSq : (2*sqrtLogScalar u)^2 = 4*(Real.log 2-Real.log u) := by
    unfold sqrtLogScalar
    nlinarith only [Real.sq_sqrt (sub_nonneg.mpr (hlogu.trans hlog2))]
  rw [hSq]
  have hExp : -(4*(Real.log 2-Real.log u))/4 = Real.log u-Real.log 2 := by ring
  rw [hExp,Real.exp_sub,Real.exp_log hu.1,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  ring

theorem gaussian_input_profile {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X X' : Ω → EuclideanSpace ℝ ι}
    (hX : Measurable X) (hX' : Measurable X')
    (hi : iIndepFun (fun i ω => X ω i) μ)
    (hLaw : ∀ i, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    (hInd : IndepFun X X' μ) (hCopy : IdentDistrib X X' μ μ) :
    ∀ f : EuclideanSpace ℝ ι → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (X ω)-f (X' ω)|) μ))
        (affineSqrtLogProfile 0 2 (by norm_num)).val := by
  intro f hf
  have hm (i : ι) : Measurable (fun ω => X ω i) :=
    (measurable_pi_apply i).comp ((EuclideanSpace.equiv ι ℝ).continuous.measurable.comp hX)
  have hMeas : Measurable (fun ω => |f (X ω)-f (X' ω)|) :=
    ((hf.continuous.measurable.comp hX).sub (hf.continuous.measurable.comp hX')).abs
  have hP := affine_sqrt_log_profile_properties (m := 0) (c := 2) (by norm_num) (by norm_num)
  apply tailQuantile_decLE_of_profile_selection_tail_bounds hMeas
    (affineSqrtLogProfile 0 2 (by norm_num)).property hP.1
    (sq := fun u => 2*sqrtLogScalar u)
  · intro u hu
    rw [hP.2.1 u hu]
    simp only [zero_add,mem_singleton_iff]
  · intro u hu
    have hWeak := gaussian_lipschitz_copy_weak_tail hX hi hm hLaw hInd hCopy hf
      (t := 2*sqrtLogScalar u) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    rw [gaussian_profile_confidence_identity hu] at hWeak
    have hSub : {ω | 2*sqrtLogScalar u < |f (X ω)-f (X' ω)|} ⊆
        {ω | 2*sqrtLogScalar u ≤ |f (X ω)-f (X' ω)|} := by
      intro ω hω
      change 2*sqrtLogScalar u < |f (X ω)-f (X' ω)| at hω
      exact hω.le
    exact (measureReal_mono hSub).trans hWeak

end ScalarMonotone.EndOfPaper
end
