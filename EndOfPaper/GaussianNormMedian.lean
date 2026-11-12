import EndOfPaper.GaussianSquareChernoff
import EndOfPaper.IndependentCopyTails
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Weak Gaussian Euclidean norm tails and bounds for every actual median, including the exact normalized HS-norm constant in the manuscript.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_euclidean_norm_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → EuclideanSpace ℝ ι}
    (hi : iIndepFun (fun i ω => X ω i) μ) (hm : ∀ i, Measurable (fun ω => X ω i))
    (hLaw : ∀ i, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1) (hn : 0 < Fintype.card ι)
    {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | Real.sqrt (Fintype.card ι : ℝ)+s ≤ ‖X ω‖} ≤ Real.exp (-(s^2)/2) := by
  have hsq (ω : Ω) : ‖X ω‖^2 = ∑ i, (X ω i)^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs,sq_abs]
  apply (measureReal_mono (fun ω hω => ?_)).trans (gaussian_square_sum_norm_tail hi hm hLaw hn hs)
  have hh := (sq_le_sq₀ (add_nonneg (Real.sqrt_nonneg _) hs) (norm_nonneg (X ω))).mpr hω
  rwa [hsq ω] at hh

theorem gaussian_euclidean_norm_median {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → EuclideanSpace ℝ ι}
    (hi : iIndepFun (fun i ω => X ω i) μ) (hm : ∀ i, Measurable (fun ω => X ω i))
    (hLaw : ∀ i, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1) (hn : 0 < Fintype.card ι)
    {m : ℝ} (hmed : IsRealMedian (fun ω => ‖X ω‖) μ m) :
    m ≤ Real.sqrt (Fintype.card ι : ℝ)+Real.sqrt (2*Real.log 2) := by
  by_contra h
  have hgt := lt_of_not_ge h
  let s := m-Real.sqrt (Fintype.card ι : ℝ)
  have hs : 0 ≤ s := by dsimp only [s]; linarith [Real.sqrt_nonneg (2*Real.log 2)]
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hsSq : 2*Real.log 2 < s^2 := by
    have hrad := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlog.le)
    have hh : Real.sqrt (2*Real.log 2) < s := by dsimp only [s]; linarith only [hgt]
    nlinarith [Real.sqrt_nonneg (2*Real.log 2)]
  have he : Real.exp (-(s^2)/2) < (1/2 : ℝ) := by
    have harg : -(s^2)/2 < -Real.log (2 : ℝ) := by
      have hh : Real.log (2 : ℝ) < s^2/2 := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
        (by simpa only [mul_comm] using hsSq)
      simpa only [neg_div] using neg_lt_neg hh
    have hh := Real.exp_lt_exp.mpr harg
    rwa [Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 2),inv_eq_one_div] at hh
  have hb := gaussian_euclidean_norm_tail hi hm hLaw hn hs
  have heq : Real.sqrt (Fintype.card ι : ℝ)+s = m := by dsimp only [s]; ring
  rw [heq] at hb
  exact (not_lt_of_ge hmed.2) (hb.trans_lt he)

theorem realMedian_of_div_positive {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : Ω → ℝ} {c m : ℝ} (hm : IsRealMedian (fun ω => Y ω/c) μ m) (hc : 0 < c) :
    IsRealMedian Y μ (c*m) := by
  have hleft : {ω | Y ω ≤ c*m} = {ω | Y ω/c ≤ m} := by
    ext ω
    simp only [mem_setOf_eq,div_le_iff₀ hc,mul_comm m c]
  have hright : {ω | c*m ≤ Y ω} = {ω | m ≤ Y ω/c} := by
    ext ω
    simp only [mem_setOf_eq,le_div_iff₀ hc,mul_comm m c]
  exact ⟨by simpa only [hleft] using hm.1,by simpa only [hright] using hm.2⟩

theorem gaussian_euclidean_normalized_norm_median {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → EuclideanSpace ℝ ι}
    (hi : iIndepFun (fun i ω => X ω i) μ) (hm : ∀ i, Measurable (fun ω => X ω i))
    (hLaw : ∀ i, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1) (hn : 0 < Fintype.card ι)
    {m : ℝ} (hmed : IsRealMedian (fun ω => ‖X ω‖/Real.sqrt (Fintype.card ι : ℝ)) μ m) :
    m ≤ 1+Real.sqrt (2*Real.log 2/(Fintype.card ι : ℝ)) := by
  have hr : 0 < Real.sqrt (Fintype.card ι : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hmedAbs := realMedian_of_div_positive hmed hr
  have hb := gaussian_euclidean_norm_median hi hm hLaw hn hmedAbs
  rw [Real.sqrt_div (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)]
  apply (mul_le_mul_right hr).mp
  calc
    _ ≤ Real.sqrt (Fintype.card ι : ℝ)+Real.sqrt (2*Real.log 2) := by simpa only [mul_comm] using hb
    _ = _ := by field_simp [hr.ne'] <;> ring

end ScalarMonotone.EndOfPaper
end
