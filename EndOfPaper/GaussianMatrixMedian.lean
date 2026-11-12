import EndOfPaper.GaussianMatrixTail
import EndOfPaper.GaussianNormMedian
import EndOfPaper.GaussianMatrixNormalization

/-!
Every actual Gaussian matrix operator-norm median satisfies the sharp dimensional bound; square matrices have the exact normalization in the paper.
-/

open Set MeasureTheory ProbabilityTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem realMedian_le_of_gaussian_upper_tails {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : Ω → ℝ} {R t : ℝ}
    (hTail : ∀ s : ℝ, 0 ≤ s → μ.real {ω | R+s ≤ Y ω} ≤ Real.exp (-(s^2)/2))
    (hmed : IsRealMedian Y μ t) : t ≤ R+Real.sqrt (2*Real.log 2) := by
  by_contra h
  have hgt := lt_of_not_ge h
  let s := t-R
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
  have hb := hTail s hs
  have heq : R+s = t := by dsimp only [s]; ring
  rw [heq] at hb
  exact (not_lt_of_ge hmed.2) (hb.trans_lt he)

theorem gaussian_matrix_operator_norm_median {Ω m n : Type*}
    [MeasurableSpace Ω] [Fintype m] [Fintype n] [Nonempty m] [Nonempty n]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → HSMatrix m n}
    (hi : iIndepFun (fun i : m × n => fun ω => X ω i) μ)
    (hm : ∀ i : m × n, Measurable (fun ω => X ω i))
    (hLaw : ∀ i : m × n, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    {t : ℝ} (hmed : IsRealMedian (fun ω => ‖hsMatrixOp (X ω)‖) μ t) :
    t ≤ Real.sqrt (Fintype.card m : ℝ)+Real.sqrt (Fintype.card n : ℝ)+Real.sqrt (2*Real.log 2) :=
  realMedian_le_of_gaussian_upper_tails (fun s hs => gaussian_matrix_operator_norm_tail hi hm hLaw hs) hmed

theorem gaussian_square_matrix_normalized_operator_median {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {d : ℕ} (hd : 0 < d)
    {X : Ω → HSMatrix (Fin d) (Fin d)}
    (hi : iIndepFun (fun i : Fin d × Fin d => fun ω => X ω i) μ)
    (hm : ∀ i : Fin d × Fin d, Measurable (fun ω => X ω i))
    (hLaw : ∀ i : Fin d × Fin d, Measure.map (fun ω => X ω i) μ = gaussianReal 0 1)
    {t : ℝ} (hmed : IsRealMedian (fun ω => ‖hsMatrixOp (X ω)‖/Real.sqrt (2*(d : ℝ))) μ t) :
    t ≤ Real.sqrt 2+Real.sqrt (Real.log 2/(d : ℝ)) := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hr : 0 < Real.sqrt (2*(d : ℝ)) := Real.sqrt_pos.mpr (mul_pos (by norm_num) hdR)
  have hBound := gaussian_matrix_operator_norm_median hi hm hLaw (realMedian_of_div_positive hmed hr)
  simp only [Fintype.card_fin] at hBound
  apply (mul_le_mul_right hr).mp
  rw [gaussian_matrix_median_normalization hdR]
  simpa only [mul_comm] using hBound

end ScalarMonotone.EndOfPaper
end
