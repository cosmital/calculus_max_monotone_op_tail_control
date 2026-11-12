import EndOfPaper.QuantileTailCompletion
import EndOfPaper.GeometricDilation
import EndOfPaper.EndpointSymmetry

/-!
An actual strict-tail multiplier gives the exact
completed probability dilation, retaining all endpoint and jump fibers.
-/

open Set Filter MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem quantile_tail_multiplier_dilation {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    {q : DecGraph} (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val p, 0 ≤ v)
    {c K : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) (hK : 1 ≤ K)
    (hcomp : DecLE (tailQuantile (Measure.map X μ))
      (completedDecreasingRestriction (Ioo (0 : ℝ) 1) (positiveInputDilation c q.val)))
    (htail : ∀ t : ℝ, 0 ≤ t → μ.real {ω | t < Y ω} ≤ K*μ.real {ω | t < X ω}) :
    DecLE (tailQuantile (Measure.map Y μ))
      (completedDecreasingRestriction (Ioo (0 : ℝ) 1) (positiveInputDilation (c/K) q.val)) := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hcK : c/K ∈ Ioc (0 : ℝ) 1 :=
    ⟨div_pos hc.1 hK0,(div_le_one hK0).mpr (hc.2.trans hK)⟩
  let D := completedProfileDilation 1 1 c q hqi (by norm_num) hc.1 (by simpa using hc.2)
  let R := completedProfileDilation 1 1 (c/K) q hqi (by norm_num) hcK.1 (by simpa using hcK.2)
  have hD := completedProfileDilation_properties (q := q) hqi
    (by norm_num : (0 : ℝ) < 1) hc.1 (by simpa using hc.2)
  have hR := completedProfileDilation_properties (q := q) hqi
    (by norm_num : (0 : ℝ) < 1) hcK.1 (by simpa using hcK.2)
  obtain ⟨τ,_hτm,hτ⟩ := exists_global_measurable_selection (Or.inr q.property.1) measurableSet_Ioo
    (fun p hp => interior_subset (show p ∈ interior (dom q.val) from by rwa [hqi]))
  have hRS : SelectionOn R.val (Ioo (0 : ℝ) 1) (fun p => τ ((c/K)*p)) := by
    intro p hp
    rw [hR.2 p hp]
    exact hτ _ (initial_dilation_mapsTo hcK.1 (by simpa using hcK.2) hp)
  change DecLE (tailQuantile (Measure.map Y μ)) R.val
  apply tailQuantile_decLE_of_profile_selection_tail_bounds hY R.property hR.1 hRS
  intro u hu
  have hscale : (1/K) ∈ Ioc (0 : ℝ) 1 :=
    ⟨one_div_pos.mpr hK0,(div_le_one hK0).mpr hK⟩
  have huK : u/K ∈ Ioo (0 : ℝ) 1 := by
    simpa only [one_div,mul_comm,div_eq_mul_inv,mul_one] using
      initial_dilation_mapsTo hscale.1 (by simpa using hscale.2) hu
  have hv : (c/K)*u ∈ Ioo (0 : ℝ) 1 :=
    initial_dilation_mapsTo hcK.1 (by simpa using hcK.2) hu
  have hτ0 : 0 ≤ τ ((c/K)*u) := hq0 _ hv _ (hτ _ hv)
  have hmem : τ ((c/K)*u) ∈ D.val (u/K) := by
    rw [hD.2 _ huK]
    have he : c*(u/K) = (c/K)*u := by ring
    rw [he]
    exact hτ _ hv
  have hbase := quantile_comparison_strict_tail hX hcomp hmem
  calc
    μ.real {ω | τ ((c/K)*u) < Y ω} ≤ K*μ.real {ω | τ ((c/K)*u) < X ω} := htail _ hτ0
    _ ≤ K*(u/K) := mul_le_mul_of_nonneg_left hbase hK0.le
    _ = u := by field_simp [hK0.ne']

end ScalarMonotone.EndOfPaper
end
