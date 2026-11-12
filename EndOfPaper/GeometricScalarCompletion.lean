import EndOfPaper.GeometricHardyOrder
import EndOfPaper.GeometricHardySelections
import EndOfPaper.NonnegativeExponentialFibers
import EndOfPaper.ExtendedLogMean
import EndOfPaper.LogarithmicFiniteParts
import EndOfPaper.HardyBoundaryContinuity
import Mathlib.Data.EReal.Inv

/-!
The actual geometric Hardy transform equals the whole
maximal completion of its extended-log scalar expression.
Arbitrary selections, infinite negative area and jump fibers are included.
-/

open Set Filter MeasureTheory
open scoped Interval ENNReal Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem initial_profile_eq_completed_scalar {f : Operator} {B : ℝ}
    (hB : 0 < B) (hf : MaximalDecreasing f)
    (hfi : interior (dom f) = Ioo (0 : ℝ) B)
    {s : ℝ → ℝ} (hs : SelectionOn f (Ioo (0 : ℝ) B) s) :
    f = completedDecreasingRestriction (Ioo (0 : ℝ) B) (ofFun s) := by
  let R := restrictOperator (negOut (ofFun s)) (Ioo (0 : ℝ) B)
  have hRf : R ≤ negOut f := by
    intro x u hu
    change x ∈ Ioo (0 : ℝ) B ∧ -u = s x at hu
    change -u ∈ f x
    rw [hu.2]
    exact hs x hu.1
  have hR : Increasing R := by
    intro x u y v hu hv
    exact hf.1 (hRf x hu) (hRf y hv)
  have hRd : dom R = Ioo (0 : ℝ) B := by
    apply dom_restrictOperator
    intro x _
    exact ⟨-s x,by simp [negOut,ofFun]⟩
  have hne : (interior (dom f)).Nonempty := by
    rw [hfi]
    exact nonempty_Ioo.mpr hB
  have hd : dom (negOut f) ⊆ closure (Ioo (0 : ℝ) B) := by
    simpa only [dom_negOut,hfi] using decreasing_dom_subset_closure_interior hf hne
  have he := (unique_maximal_completion ordConnected_Ioo (nonempty_Ioo.mpr hB) hR hRd).unique
    ⟨hf,hRf,hd⟩
    ⟨completion_maximal ordConnected_Ioo (nonempty_Ioo.mpr hB) hR hRd,
      le_completion hR hRd,completion_dom_subset _ _⟩
  simpa only [negOut_negOut,completedDecreasingRestriction,R] using congrArg negOut he

theorem geometricPrefixValue_congr_ae {s t : ℝ → ℝ} {B p : ℝ}
    (he : s =ᵐ[volume.restrict (Ioo (0 : ℝ) B)] t) (hp : p ≤ B) :
    geometricPrefixValue s p = geometricPrefixValue t p := by
  have he' : s =ᵐ[volume.restrict (Ioo (0 : ℝ) p)] t :=
    ae_restrict_of_ae_restrict_of_subset
      (show Ioo (0 : ℝ) p ⊆ Ioo (0 : ℝ) B from fun x hx => ⟨hx.1,hx.2.trans_le hp⟩) he
  have hP : (∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (Real.log (s x))) =
      ∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (Real.log (t x)) :=
    lintegral_congr_ae (he'.fun_comp (fun v => ENNReal.ofReal (Real.log v)))
  have hN : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)) =
      ∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (t x) :=
    lintegral_congr_ae (he'.fun_comp negativeLogWithZero)
  simp only [geometricPrefixValue,extendedLogIntegral,hP,hN]

theorem raw_positive_log_prefix_finite {s : ℝ → ℝ} {B p : ℝ} (hm : Measurable s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    (hp : p ∈ Ioo (0 : ℝ) B) :
    (∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (Real.log (s x))) ≠ ∞ := by
  exact ne_of_lt (lt_of_le_of_lt (lintegral_mono (fun x =>
    ENNReal.ofReal_le_ofReal (le_max_left (Real.log (s x)) 0)))
    (positive_log_prefix_area_finite hm hP hp))

theorem geometric_log_hardy_scalar_data {q : DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hn : ¬ ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, v = 0)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    let J := interior (dom (logOp q.val))
    J ⊆ Ioo (0 : ℝ) B ∧
      dom (logOp (geometricHardyTransform B q)) ⊆ closure J ∧
      (∀ p ∈ J, logOp (geometricHardyTransform B q) p =
        {hardyScalar (fun x => Real.log (s x)) p}) ∧
      (∀ p ∈ J, IntervalIntegrable (fun x => Real.log (s x)) volume 0 p) := by
  dsimp only
  obtain ⟨hL,hLd,hLz,hLp⟩ := logarithm_initial_domain hB q.property hqi
    (positive_graph_value_of_nonzero hq0 hn)
  obtain ⟨hsel,hprefix⟩ := logarithmic_prefix_integrability hB q.property hqi hm hs hP
  have hH := hardyFamilyIntegral_of_locally_integrable hL hLz hLp hsel hprefix
  have he : logOp (geometricHardyTransform B q) =
      hardyFamilyIntegral (interior (dom (logOp q.val))) (logOp q.val) := by
    simpa only [logarithm_nonnegative_floor] using
      geometricHardyTransform_logarithm hB hqi hq0 hn hm hs hP
  refine ⟨?_,?_,?_,hprefix⟩
  · simpa only [interior_Icc] using interior_mono hLd
  · rw [he]
    exact hH.2.2.1
  · intro p hp
    rw [he]
    exact hH.2.2.2.1 p hp

theorem geometric_hardy_positive_interior_fiber {q : DecGraph} {B p : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hn : ¬ ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, v = 0)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    (hp : p ∈ interior (dom (logOp q.val))) :
    geometricHardyTransform B q p = {Real.exp (hardyScalar (fun x => Real.log (s x)) p)} := by
  have hD := geometric_log_hardy_scalar_data hB hqi hq0 hn hm hs hP
  have hG := geometricHardyTransform_well_defined hB hqi hq0 hm hs hP
  have hpI := hD.1 hp
  have hne : (geometricHardyTransform B q p).Nonempty := by
    change p ∈ dom (geometricHardyTransform B q)
    apply interior_subset
    rwa [hG.2.1]
  exact nonnegative_log_singleton_fiber hG.1 hne (hG.2.2.1 p hpI) (hD.2.2.1 p hp)

theorem geometric_hardy_zero_mem_outside_log_interior {q : DecGraph} {B p : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hn : ¬ ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, v = 0)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    (hp : p ∈ Ioo (0 : ℝ) B) (hpJ : p ∉ interior (dom (logOp q.val))) :
    0 ∈ geometricHardyTransform B q p := by
  have hG := geometricHardyTransform_well_defined hB hqi hq0 hm hs hP
  have hD := geometric_log_hardy_scalar_data hB hqi hq0 hn hm hs hP
  obtain ⟨hL,_,hLz,hLp⟩ := logarithm_initial_domain hB q.property hqi
    (positive_graph_value_of_nonzero hq0 hn)
  have hprefix := (decreasing_zero_inf_domain_geometry hL hLz hLp).2.2.2.1
  have hJ : interior (dom (logOp q.val)) ⊆ Iic p := by
    intro y hy
    by_contra hpy
    exact hpJ (hprefix y hy ⟨hp.1,lt_of_not_ge hpy⟩)
  have hclosed : IsClosed {x : ℝ | 0 ∈ geometricHardyTransform B q x} := by
    change IsClosed ((fun x : ℝ => (x,(0 : ℝ))) ⁻¹' graph (geometricHardyTransform B q))
    exact (decreasing_graph_closed hG.1).preimage (continuous_id.prodMk continuous_const)
  have hzero : Ioo p B ⊆ {x : ℝ | 0 ∈ geometricHardyTransform B q x} := by
    intro x hx
    have hxI : x ∈ Ioo (0 : ℝ) B := ⟨hp.1.trans hx.1,hx.2⟩
    have hlog : logOp (geometricHardyTransform B q) x = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro v hv
      have hxp := closure_minimal hJ isClosed_Iic (hD.2.1 ⟨v,hv⟩)
      exact (not_le_of_gt hx.1) hxp
    have hne : (geometricHardyTransform B q x).Nonempty := by
      change x ∈ dom (geometricHardyTransform B q)
      apply interior_subset
      rwa [hG.2.1]
    change 0 ∈ geometricHardyTransform B q x
    rw [nonnegative_log_empty_fiber hne (hG.2.2.1 x hxI) hlog]
    rfl
  apply closure_minimal hzero hclosed
  rw [closure_Ioo hp.2.ne]
  exact ⟨le_rfl,hp.2.le⟩

theorem geometric_hardy_finite_prefix_mem {q : DecGraph} {B p : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hn : ¬ ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, v = 0)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    (hp : p ∈ Ioo (0 : ℝ) B)
    (hN : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)) ≠ ∞) :
    geometricPrefixValue s p ∈ geometricHardyTransform B q p := by
  have hi := logarithm_prefix_integrable_of_finite_negative_area hq0 hm hs hP hp hN
  have hpos := positive_prefix_of_finite_negative_log_area
    (selection_antitoneOn q.property.1 hs) (fun x hx => hq0 x hx (s x) (hs x hx)) hp hN
  rw [geometricPrefixValue_of_integrable hp.1 hi hpos]
  have hG := geometricHardyTransform_well_defined hB hqi hq0 hm hs hP
  have hJ := prefix_log_domain_of_finite_negative_area hqi hq0 hs hp hN
  have ht := hardyScalar_tendsto_left_of_intervalIntegrable hp.1 hi
  have he := Real.continuous_exp.continuousAt.tendsto.comp ht
  have htPair : Tendsto (fun u : ℝ => (u,Real.exp (hardyScalar (fun x => Real.log (s x)) u)))
      (𝓝[<] p) (𝓝 (p,Real.exp (hardyScalar (fun x => Real.log (s x)) p))) :=
    (tendsto_id'.mpr nhdsWithin_le_nhds).prodMk_nhds he
  apply (decreasing_graph_closed hG.1).mem_of_tendsto htPair
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hp.1)] with u hup hu0
  change Real.exp (hardyScalar (fun x => Real.log (s x)) u) ∈ geometricHardyTransform B q u
  rw [geometric_hardy_positive_interior_fiber hB hqi hq0 hn hm hs hP (hJ ⟨hu0,hup⟩)]
  rfl

theorem geometric_hardy_scalar_selection_measurable {q : DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    SelectionOn (geometricHardyTransform B q) (Ioo (0 : ℝ) B) (geometricPrefixValue s) := by
  classical
  intro p hp
  have hPf := raw_positive_log_prefix_finite hm hP hp
  by_cases hz : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, v = 0
  · have hzero : ∀ x ∈ Ioo (0 : ℝ) p, s x = 0 := by
      intro x hx
      exact hz x ⟨hx.1,hx.2.trans hp.2⟩ (s x) (hs x ⟨hx.1,hx.2.trans hp.2⟩)
    have hN := negative_log_area_eq_top_of_zero_interval (le_refl (0 : ℝ)) hp.1 le_rfl hzero
    rw [geometricPrefixValue_of_negative_area_top hp.1 hPf hN,geometricHardyTransform_zero hz]
    have hne : (q.val p).Nonempty := by
      change p ∈ dom q.val
      apply interior_subset
      rwa [hqi]
    obtain ⟨v,hv⟩ := hne
    rwa [← hz p hp v hv]
  · by_cases hN : (∫⁻ x in Ioo (0 : ℝ) p, negativeLogWithZero (s x)) = ∞
    · rw [geometricPrefixValue_of_negative_area_top hp.1 hPf hN]
      apply geometric_hardy_zero_mem_outside_log_interior hB hqi hq0 hz hm hs hP hp
      intro hpJ
      have hD := geometric_log_hardy_scalar_data hB hqi hq0 hz hm hs hP
      have hpos : ∀ x ∈ Ioo (0 : ℝ) p, 0 < s x := by
        obtain ⟨w,hw⟩ := interior_subset hpJ
        intro x hx
        exact (Real.exp_pos w).trans_le (Decreasing.le_of_lt q.property.1
          (hs x ⟨hx.1,hx.2.trans hp.2⟩) (logOp_mem_iff.mp hw) hx.2)
      exact negative_log_area_finite_of_integrable hp.1 (hD.2.2.2 p hpJ) hpos hN
    · exact geometric_hardy_finite_prefix_mem hB hqi hq0 hz hm hs hP hp hN

theorem geometric_hardy_scalar_selection {q : DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    SelectionOn (geometricHardyTransform B q) (Ioo (0 : ℝ) B) (geometricPrefixValue s) := by
  obtain ⟨t,ht,hts,harea⟩ := measurable_selection_same_positive_log_area hqi hs
  have htP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (t x)) 0)) < ∞ := by
    rwa [harea]
  have hsel := geometric_hardy_scalar_selection_measurable hB hqi hq0 ht hts htP
  have he := decreasing_selections_ae_eq q.property.1 hs hts volume measurableSet_Ioo
  intro p hp
  rw [geometricPrefixValue_congr_ae he hp.2.le]
  exact hsel p hp

theorem geometric_hardy_scalar_completion {q : DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    geometricHardyTransform B q =
      completedDecreasingRestriction (Ioo (0 : ℝ) B) (ofFun (geometricPrefixValue s)) := by
  have hG := geometricHardyTransform_well_defined_any_selection hB hqi hq0 hs hP
  exact initial_profile_eq_completed_scalar hB hG.1 hG.2.1
    (geometric_hardy_scalar_selection hB hqi hq0 hs hP)

theorem extendedLogIntegral_defined_on_admissible_prefix {q : DecGraph} {B p : ℝ}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    (hp : p ∈ Ioo (0 : ℝ) B) :
    ∃ A : EReal, extendedLogIntegral s p = some A := by
  obtain ⟨t,ht,hts,harea⟩ := measurable_selection_same_positive_log_area hqi hs
  have htP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (t x)) 0)) < ∞ := by
    rwa [harea]
  have he := decreasing_selections_ae_eq q.property.1 hs hts volume measurableSet_Ioo
  have he' : s =ᵐ[volume.restrict (Ioo (0 : ℝ) p)] t :=
    ae_restrict_of_ae_restrict_of_subset
      (show Ioo (0 : ℝ) p ⊆ Ioo (0 : ℝ) B from fun x hx => ⟨hx.1,hx.2.trans hp.2⟩) he
  have hPeq : (∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (Real.log (s x))) =
      ∫⁻ x in Ioo (0 : ℝ) p, ENNReal.ofReal (Real.log (t x)) :=
    lintegral_congr_ae (he'.fun_comp (fun v => ENNReal.ofReal (Real.log v)))
  apply extendedLogIntegral_defined_of_finite_positive_area
  rw [hPeq]
  exact raw_positive_log_prefix_finite ht htP hp

theorem geometricPrefixValue_of_extended_integral {s : ℝ → ℝ} {p : ℝ} {A : EReal}
    (hA : extendedLogIntegral s p = some A) :
    geometricPrefixValue s p = (EReal.exp (A/(p : EReal))).toReal := by
  simp only [geometricPrefixValue,hA,div_eq_mul_inv,← EReal.coe_inv,EReal.exp_mul]

end ScalarMonotone.EndOfPaper
end
