import EndOfPaper.QuantileDependenceCounterexample
import EndOfPaper.HardyVariational

/-!
The actual nonclosed exponential image at the completed zero
profile endpoint, with the entire probability domain retained.
-/

open Set MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem dirac_quantile_zero_fiber (c : ℝ) :
    tailQuantile (Measure.dirac c) 0 = Ici c := by
  ext x
  change (0 : ℝ) ∈ survival (Measure.dirac c) x ↔ c ≤ x
  rcases lt_trichotomy x c with h | rfl | h
  · simp [survival_dirac_left h, not_le_of_gt h]
  · simp [survival_dirac_at]
  · simp [survival_dirac_right h, h.le]

theorem dirac_quantile_one_fiber (c : ℝ) :
    tailQuantile (Measure.dirac c) 1 = Iic c := by
  ext x
  change (1 : ℝ) ∈ survival (Measure.dirac c) x ↔ x ≤ c
  rcases lt_trichotomy x c with h | rfl | h
  · simp [survival_dirac_left h, h.le]
  · simp [survival_dirac_at]
  · simp [survival_dirac_right h, not_le_of_gt h]

theorem exponential_zero_quantile_one :
    comp (ofFun Real.exp) (tailQuantile (Measure.dirac (0 : ℝ))) 1 = Ioc (0 : ℝ) 1 := by
  ext v
  change (∃ u, u ∈ tailQuantile (Measure.dirac (0 : ℝ)) 1 ∧ v ∈ ofFun Real.exp u) ↔ _
  rw [dirac_quantile_one_fiber]
  simp only [mem_Iic, ofFun, mem_singleton_iff, mem_Ioc]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨Real.exp_pos u, Real.exp_le_one_iff.mpr hu⟩
  · rintro ⟨hv0, hv1⟩
    exact ⟨Real.log v, Real.log_nonpos hv0.le hv1, (Real.exp_log hv0).symm⟩

theorem exponential_zero_quantile_not_maximal :
    ¬ MaximalDecreasing (comp (ofFun Real.exp) (tailQuantile (Measure.dirac (0 : ℝ)))) := by
  intro h
  have hc := decreasing_fiber_closed h 1
  rw [exponential_zero_quantile_one] at hc
  have hcl : (0 : ℝ) ∈ closure (Ioc (0 : ℝ) 1) := by
    rw [closure_Ioc (zero_ne_one : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl, zero_le_one⟩
  have hz : (0 : ℝ) ∈ Ioc (0 : ℝ) 1 := hc.closure_subset hcl
  exact (lt_irrefl (0 : ℝ)) hz.1

theorem geometric_exponential_boundary_counterexample :
    ∃ q : Operator, MaximalDecreasing q ∧ interior (dom q) = Ioo (0 : ℝ) 1 ∧
      (∀ p ∈ Ioo (0 : ℝ) 1, q p = {0}) ∧
      comp (ofFun Real.exp) q 1 = Ioc (0 : ℝ) 1 ∧
      ¬ MaximalDecreasing (comp (ofFun Real.exp) q) := by
  refine ⟨tailQuantile (Measure.dirac (0 : ℝ)), tailQuantile_maximal _,
    tailQuantile_domain_interior _, ?_, exponential_zero_quantile_one,
    exponential_zero_quantile_not_maximal⟩
  intro p hp
  exact tailQuantile_dirac_interior 0 hp

end ScalarMonotone.EndOfPaper
end
