import EndOfPaper.GaussianFiniteIndex

/-!
Both weak tails, with the exact exponent in the manuscript Gaussian input assertion.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem subgaussian_neg_mgf {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF Y c μ) :
    HasSubgaussianMGF (fun ω => -Y ω) c μ where
  integrable_exp_mul a := by simpa only [mul_neg,neg_mul] using h.integrable_exp_mul (-a)
  mgf_le a := by simpa only [mgf,mul_neg,neg_mul,neg_sq] using h.mgf_le (-a)

theorem gaussian_lipschitz_copy_weak_tail {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X X' : Ω → EuclideanSpace ℝ ι} (hX : Measurable X)
    (hi : iIndepFun (fun i ω => X ω i) μ)
    (hm : ∀ i, Measurable (fun ω => X ω i))
    (hLaw : ∀ i, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    (hInd : IndepFun X X' μ) (hCopy : IdentDistrib X X' μ μ)
    {f : EuclideanSpace ℝ ι → ℝ} (hf : LipschitzWith 1 f) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |f (X ω)-f (X' ω)|} ≤ 2*Real.exp (-(t^2)/4) := by
  have hSG := gaussian_lipschitz_copy_subgaussian_fintype hX hi hm hLaw hInd hCopy hf
  have hPos := hSG.measure_ge_le ht
  have hNeg := (subgaussian_neg_mgf hSG).measure_ge_le ht
  have hSet : {ω | t ≤ |f (X ω)-f (X' ω)|} ⊆
      {ω | t ≤ f (X ω)-f (X' ω)} ∪ {ω | t ≤ -(f (X ω)-f (X' ω))} := by
    intro ω hω
    change t ≤ |f (X ω)-f (X' ω)| at hω
    change t ≤ f (X ω)-f (X' ω) ∨ t ≤ -(f (X ω)-f (X' ω))
    exact le_abs.mp hω
  calc
    _ ≤ μ.real ({ω | t ≤ f (X ω)-f (X' ω)} ∪ {ω | t ≤ -(f (X ω)-f (X' ω))}) := measureReal_mono hSet
    _ ≤ μ.real {ω | t ≤ f (X ω)-f (X' ω)}+μ.real {ω | t ≤ -(f (X ω)-f (X' ω))} := measureReal_union_le _ _
    _ ≤ 2*Real.exp (-(t^2)/4) := by
      have hh := add_le_add hPos hNeg
      norm_num only [NNReal.coe_ofNat] at hh
      linarith only [hh]

end ScalarMonotone.EndOfPaper
end
