import EndOfPaper.ZeroRampScalar
import EndOfPaper.GeometricHardySelections
import EndOfPaper.GeometricHardyOrder
import EndOfPaper.NonnegativeExponentialFibers
import EndOfPaper.HardyBoundaryContinuity
import EndOfPaper.AggregationOperator
import EndOfPaper.GeometricHardyArithmetic

/-!
The full internal-zero example on the actual maximal profile:
exact logarithmic domain, arithmetic Hardy pieces, geometric
formula, left limit, zero continuation and closed jump interval.
-/

open Set Filter MeasureTheory
open scoped Interval ENNReal Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

def zeroRampOperator : Operator :=
  negOut (intervalCompletionI (Ioo (0 : ℝ) 1) (fun u => -zeroRamp u) (fun u => -zeroRamp u))

theorem zeroRampOperator_properties :
    MaximalDecreasing zeroRampOperator ∧
      interior (dom zeroRampOperator) = Ioo (0 : ℝ) 1 ∧
      dom zeroRampOperator ⊆ Icc (0 : ℝ) 1 ∧
      ∀ u ∈ Ioo (0 : ℝ) 1, zeroRampOperator u = {zeroRamp u} := by
  have hC := intervalCompletionI_properties isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.mpr (by norm_num : (0 : ℝ) < 1))
    (fun _ _ => le_rfl)
    (fun x _ y _ hxy => neg_le_neg (zeroRamp_antitone hxy.le))
    (fun u _ => ⟨zeroRamp_continuous.neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      zeroRamp_continuous.neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩)
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [zeroRampOperator,MaximalDecreasing,negOut_negOut] using hC.1
  · simpa only [zeroRampOperator,dom_negOut] using hC.2.1
  · simpa only [zeroRampOperator,dom_negOut,closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using hC.2.2.1
  · intro u hu
    ext v
    change -v ∈ intervalCompletionI (Ioo (0 : ℝ) 1)
      (fun u => -zeroRamp u) (fun u => -zeroRamp u) u ↔ v = zeroRamp u
    rw [hC.2.2.2.1 u hu,Icc_self]
    simp only [mem_singleton_iff,neg_inj]

def zeroRampProfile : DecGraph := ⟨zeroRampOperator,zeroRampOperator_properties.1⟩

theorem zeroRampProfile_selection : SelectionOn zeroRampProfile.val (Ioo (0 : ℝ) 1) zeroRamp := by
  intro u hu
  rw [show zeroRampProfile.val = zeroRampOperator from rfl,zeroRampOperator_properties.2.2.2 u hu]
  rfl

theorem zeroRampProfile_nonnegative :
    ∀ u ∈ Ioo (0 : ℝ) 1, ∀ v ∈ zeroRampProfile.val u, 0 ≤ v := by
  intro u hu v hv
  rw [show zeroRampProfile.val = zeroRampOperator from rfl,zeroRampOperator_properties.2.2.2 u hu] at hv
  rw [mem_singleton_iff.mp hv]
  exact zeroRamp_nonnegative u

theorem zeroRamp_positive_log_area :
    (∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (zeroRamp u)) 0)) = 0 := by
  calc
    _ = ∫⁻ _u in Ioo (0 : ℝ) 1, (0 : ℝ≥0∞) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      have hle : zeroRamp u ≤ 1 := max_le (by linarith [hu.1]) (by norm_num)
      rw [max_eq_right (Real.log_nonpos (zeroRamp_nonnegative u) hle),ENNReal.ofReal_zero]
    _ = 0 := by simp

theorem zeroRampProfile_nonzero :
    ¬ ∀ u ∈ Ioo (0 : ℝ) 1, ∀ v ∈ zeroRampProfile.val u, v = 0 := by
  intro hz
  have h := hz (1/4) (by norm_num) (zeroRamp (1/4)) (zeroRampProfile_selection (1/4) (by norm_num))
  norm_num [zeroRamp] at h

theorem zeroRamp_log_domain :
    interior (dom (logOp zeroRampProfile.val)) = Ioo (0 : ℝ) (1/2 : ℝ) ∧
      dom (logOp zeroRampProfile.val) ⊆ Icc (0 : ℝ) (1/2 : ℝ) := by
  have hq := zeroRampOperator_properties
  have hLd : dom (logOp zeroRampProfile.val) ⊆ Icc (0 : ℝ) 1 :=
    fun _ hx => hq.2.2.1 (logarithm_dom_subset hx)
  have hsub : dom (logOp zeroRampProfile.val) ⊆ Icc (0 : ℝ) (1/2 : ℝ) := by
    intro u hu
    refine ⟨(hLd hu).1,?_⟩
    by_contra hn
    have hhalf : (1/2 : ℝ) < u := lt_of_not_ge hn
    obtain ⟨w,hw⟩ := hu
    obtain ⟨x,hx0,hxu⟩ := exists_between (show max (1/2 : ℝ) 0 < u by simpa using hhalf)
    have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨(le_max_right _ _).trans_lt hx0,hxu.trans_le (hLd ⟨w,hw⟩).2⟩
    have hxhalf : (1/2 : ℝ) < x := (le_max_left _ _).trans_lt hx0
    have hz : zeroRamp x = 0 := max_eq_right (by linarith)
    have hle := Decreasing.le_of_lt zeroRampProfile.property.1
      (zeroRampProfile_selection x hxI) (logOp_mem_iff.mp hw) hxu
    rw [hz] at hle
    exact (not_le_of_gt (Real.exp_pos w)) hle
  refine ⟨?_,hsub⟩
  apply Set.Subset.antisymm
  · simpa only [interior_Icc] using interior_mono hsub
  · apply isOpen_Ioo.subset_interior_iff.mpr
    intro u hu
    have huI : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1,by linarith [hu.2]⟩
    have hpos : 0 < zeroRamp u := lt_of_lt_of_le (by linarith [hu.2] : 0 < 1-2*u) (le_max_left _ _)
    exact ⟨Real.log (zeroRamp u),logOp_mem_iff.mpr
      (by rw [Real.exp_log hpos]; exact zeroRampProfile_selection u huI)⟩

theorem zeroRamp_integral_before_half {p : ℝ} (hp : p ∈ Icc (0 : ℝ) (1/2 : ℝ)) :
    (∫ u in (0 : ℝ)..p, zeroRamp u) = p-p^2 := by
  have heq : (∫ u in (0 : ℝ)..p, zeroRamp u) = ∫ u in (0 : ℝ)..p, (1-2*u) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hp.1]
    intro u hu
    exact max_eq_left (by linarith [hu.2,hp.2])
  have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 p := intervalIntegrable_const
  have hl : IntervalIntegrable (fun u : ℝ => 2*u) volume 0 p :=
    (continuous_const.mul continuous_id).intervalIntegrable (0 : ℝ) p
  rw [heq,intervalIntegral.integral_sub hc hl,
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_id]
  norm_num [smul_eq_mul]
  <;> ring

theorem zeroRamp_integral_after_half {p : ℝ} (hp : (1/2 : ℝ) ≤ p) :
    (∫ u in (0 : ℝ)..p, zeroRamp u) = (1/4 : ℝ) := by
  have hz : (∫ u in (1/2 : ℝ)..p, zeroRamp u) = 0 := by
    calc
      _ = ∫ _u in (1/2 : ℝ)..p, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hp]
        intro u hu
        exact max_eq_right (by linarith [hu.1])
      _ = 0 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (show IntervalIntegrable zeroRamp volume (0 : ℝ) (1/2 : ℝ) from
      zeroRamp_continuous.intervalIntegrable (0 : ℝ) (1/2 : ℝ))
    (zeroRamp_continuous.intervalIntegrable (1/2 : ℝ) p)
  rw [zeroRamp_integral_before_half (show (1/2 : ℝ) ∈ Icc (0 : ℝ) (1/2 : ℝ) by norm_num),hz] at hadd
  norm_num at hadd
  exact hadd.symm

theorem zeroRamp_hardy_before_half {p : ℝ} (hp : p ∈ Ioc (0 : ℝ) (1/2 : ℝ)) :
    hardyScalar zeroRamp p = 1-p := by
  rw [hardyScalar,zeroRamp_integral_before_half ⟨hp.1.le,hp.2⟩]
  field_simp [hp.1.ne']
  <;> ring

theorem zeroRamp_hardy_after_half {p : ℝ} (hp : (1/2 : ℝ) ≤ p) :
    hardyScalar zeroRamp p = 1/(4*p) := by
  rw [hardyScalar,zeroRamp_integral_after_half hp]
  ring

theorem zeroRamp_hardy_fibers {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    hardyFamilyIntegral (Ioo (0 : ℝ) 1) zeroRampProfile.val p =
      {if p ≤ (1/2 : ℝ) then 1-p else 1/(4*p)} := by
  have hi : IntegrableOn zeroRamp (Ioo (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (zeroRamp_continuous.intervalIntegrable (0 : ℝ) 1)
  have hH := initial_profile_hardy_data (by norm_num : (0 : ℝ) < 1)
    zeroRampProfile.property zeroRampOperator_properties.2.1 zeroRampProfile_selection hi
  have he := hH.2.2.2.1 p hp
  rw [show interior (dom zeroRampProfile.val) = Ioo (0 : ℝ) 1 from
    zeroRampOperator_properties.2.1] at he
  rw [he]
  by_cases hph : p ≤ (1/2 : ℝ)
  · rw [if_pos hph,zeroRamp_hardy_before_half ⟨hp.1,hph⟩]
  · rw [if_neg hph,zeroRamp_hardy_after_half (le_of_not_ge hph)]

theorem zeroRamp_geometric_log_data :
    let G := geometricHardyTransform 1 zeroRampProfile
    MaximalDecreasing (logOp G) ∧ dom (logOp G) ⊆ Icc (0 : ℝ) (1/2 : ℝ) ∧
      ∀ p ∈ Ioo (0 : ℝ) (1/2 : ℝ),
        logOp G p = {hardyScalar (fun x => Real.log (1-2*x)) p} := by
  dsimp only
  have hqi := zeroRampOperator_properties.2.1
  have hP : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (zeroRamp x)) 0)) < ∞ := by
    rw [zeroRamp_positive_log_area]
    exact ENNReal.zero_lt_top
  obtain ⟨hL,_,hLz,hLp⟩ := logarithm_initial_domain (by norm_num : (0 : ℝ) < 1)
    zeroRampProfile.property hqi
    (positive_graph_value_of_nonzero zeroRampProfile_nonnegative zeroRampProfile_nonzero)
  have hsL : SelectionOn (logOp zeroRampProfile.val)
      (interior (dom (logOp zeroRampProfile.val))) (fun x => Real.log (1-2*x)) := by
    intro x hx
    rw [zeroRamp_log_domain.1] at hx
    have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1,by linarith [hx.2]⟩
    have hx0 : 0 < 1-2*x := by linarith [hx.2]
    apply logOp_mem_iff.mpr
    rw [Real.exp_log hx0]
    have he : zeroRamp x = 1-2*x := max_eq_left hx0.le
    rw [← he]
    exact zeroRampProfile_selection x hxI
  have hH := hardyFamilyIntegral_of_locally_integrable hL hLz hLp hsL
    (fun p _ => zeroRamp_log_affine_integrable p)
  have he : logOp (geometricHardyTransform 1 zeroRampProfile) =
      hardyFamilyIntegral (interior (dom (logOp zeroRampProfile.val))) (logOp zeroRampProfile.val) := by
    simpa only [logarithm_nonnegative_floor] using
      geometricHardyTransform_logarithm (by norm_num : (0 : ℝ) < 1) hqi
        zeroRampProfile_nonnegative zeroRampProfile_nonzero zeroRamp_continuous.measurable
        zeroRampProfile_selection hP
  rw [he]
  refine ⟨hH.1,?_,?_⟩
  · simpa only [zeroRamp_log_domain.1,closure_Ioo (by norm_num : (0 : ℝ) ≠ 1/2)] using hH.2.2.1
  · intro p hp
    exact hH.2.2.2.1 p (by rwa [zeroRamp_log_domain.1])

theorem zeroRamp_geometric_before_half {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) (1/2 : ℝ)) :
    geometricHardyTransform 1 zeroRampProfile p =
      {Real.exp (-1)*(1-2*p)^(-(1-2*p)/(2*p))} := by
  have hP : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (zeroRamp x)) 0)) < ∞ := by
    rw [zeroRamp_positive_log_area]
    exact ENNReal.zero_lt_top
  have hG := geometricHardyTransform_well_defined (by norm_num : (0 : ℝ) < 1)
    zeroRampOperator_properties.2.1 zeroRampProfile_nonnegative
    zeroRamp_continuous.measurable zeroRampProfile_selection hP
  have hpI : p ∈ Ioo (0 : ℝ) 1 := ⟨hp.1,by linarith [hp.2]⟩
  have hne : (geometricHardyTransform 1 zeroRampProfile p).Nonempty := by
    change p ∈ dom (geometricHardyTransform 1 zeroRampProfile)
    apply interior_subset
    rwa [hG.2.1]
  rw [nonnegative_log_singleton_fiber hG.1 hne (hG.2.2.1 p hpI)
    (zeroRamp_geometric_log_data.2.2 p hp),zeroRamp_geometric_prefix_formula hp]

theorem zeroRamp_geometric_jump :
    geometricHardyTransform 1 zeroRampProfile (1/2 : ℝ) = Icc (0 : ℝ) (Real.exp (-1)) := by
  have hP : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (zeroRamp x)) 0)) < ∞ := by
    rw [zeroRamp_positive_log_area]
    exact ENNReal.zero_lt_top
  have hG := geometricHardyTransform_well_defined (by norm_num : (0 : ℝ) < 1)
    zeroRampOperator_properties.2.1 zeroRampProfile_nonnegative
    zeroRamp_continuous.measurable zeroRampProfile_selection hP
  have hm : hardyScalar (fun x => Real.log (1-2*x)) (1/2 : ℝ) = -1 := by
    rw [hardyScalar,zeroRamp_log_half_integral]
    norm_num
  have ht : Tendsto (hardyScalar (fun x => Real.log (1-2*x)))
      (𝓝[<] (1/2 : ℝ)) (𝓝 (-1 : ℝ)) := by
    simpa only [hm] using hardyScalar_tendsto_left_of_intervalIntegrable
      (by norm_num : (0 : ℝ) < 1/2) (zeroRamp_log_affine_integrable (1/2 : ℝ))
  have hs : SelectionOn (logOp (geometricHardyTransform 1 zeroRampProfile))
      (Ioo (0 : ℝ) (1/2 : ℝ)) (hardyScalar (fun x => Real.log (1-2*x))) := by
    intro u hu
    rw [zeroRamp_geometric_log_data.2.2 u hu]
    rfl
  have hray := decreasing_right_boundary_fiber_of_tendsto
    (by norm_num : (0 : ℝ) < 1/2) zeroRamp_geometric_log_data.1
    zeroRamp_geometric_log_data.2.1 hs ht
  have hpI : (1/2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hne : (geometricHardyTransform 1 zeroRampProfile (1/2 : ℝ)).Nonempty := by
    change (1/2 : ℝ) ∈ dom (geometricHardyTransform 1 zeroRampProfile)
    apply interior_subset
    rwa [hG.2.1]
  exact nonnegative_log_upper_ray_fiber hG.1 hne (hG.2.2.1 (1/2) hpI) hray

theorem zeroRamp_geometric_after_half {p : ℝ} (hp : p ∈ Ioo (1/2 : ℝ) 1) :
    geometricHardyTransform 1 zeroRampProfile p = {0} := by
  have hP : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (zeroRamp x)) 0)) < ∞ := by
    rw [zeroRamp_positive_log_area]
    exact ENNReal.zero_lt_top
  have hG := geometricHardyTransform_well_defined (by norm_num : (0 : ℝ) < 1)
    zeroRampOperator_properties.2.1 zeroRampProfile_nonnegative
    zeroRamp_continuous.measurable zeroRampProfile_selection hP
  have hpI : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1],hp.2⟩
  have hne : (geometricHardyTransform 1 zeroRampProfile p).Nonempty := by
    change p ∈ dom (geometricHardyTransform 1 zeroRampProfile)
    apply interior_subset
    rwa [hG.2.1]
  apply nonnegative_log_empty_fiber hne (hG.2.2.1 p hpI)
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro v hv
  exact (not_le_of_gt hp.1) (zeroRamp_geometric_log_data.2.1 ⟨v,hv⟩).2

theorem zeroRamp_geometric_left_limit :
    Tendsto (fun p => Real.exp (hardyScalar (fun x => Real.log (1-2*x)) p))
      (𝓝[<] (1/2 : ℝ)) (𝓝 (Real.exp (-1))) := by
  have ht := hardyScalar_tendsto_left_of_intervalIntegrable
    (by norm_num : (0 : ℝ) < 1/2) (zeroRamp_log_affine_integrable (1/2 : ℝ))
  have hm : hardyScalar (fun x => Real.log (1-2*x)) (1/2 : ℝ) = -1 := by
    rw [hardyScalar,zeroRamp_log_half_integral]
    norm_num
  rw [hm] at ht
  exact Real.continuous_exp.continuousAt.tendsto.comp ht

theorem zeroRamp_geometric_graph_left_limit :
    Tendsto (fun p => sSup (geometricHardyTransform 1 zeroRampProfile p))
      (𝓝[<] (1/2 : ℝ)) (𝓝 (Real.exp (-1))) := by
  have he : (fun p => Real.exp (hardyScalar (fun x => Real.log (1-2*x)) p)) =ᶠ[𝓝[<] (1/2 : ℝ)]
      (fun p => sSup (geometricHardyTransform 1 zeroRampProfile p)) := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1/2)] with p hp
    rw [zeroRamp_geometric_before_half hp,csSup_singleton,zeroRamp_geometric_prefix_formula hp]
  exact zeroRamp_geometric_left_limit.congr' he

end ScalarMonotone.EndOfPaper
end
