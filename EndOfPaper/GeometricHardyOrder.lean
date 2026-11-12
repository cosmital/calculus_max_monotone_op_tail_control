import EndOfPaper.GeometricHardy

/-!
Whole geometric Hardy domination and order preservation,
including internal zeros and completed boundary fibers.
No global logarithmic integrability is imposed.
-/

open Set Filter MeasureTheory
open scoped Interval ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem logarithm_preserves_decLE {f g : Operator} (hfg : DecLE f g) :
    DecLE (logOp f) (logOp g) := by
  intro x u y v hu hv hyx
  exact Real.exp_le_exp.mp (hfg (logOp_mem_iff.mp hu) (logOp_mem_iff.mp hv) hyx)

/-- On completed nonnegative initial profiles, logarithmic order determines
the original whole-graph order, even if an interior fiber contains zero. -/
theorem logarithm_reflects_initial_decLE {f g : Operator} {B : ℝ}
    (hB : 0 < B) (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hfi : interior (dom f) = Ioo (0 : ℝ) B)
    (hgi : interior (dom g) = Ioo (0 : ℝ) B)
    (hg0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ g x, 0 ≤ v)
    (hlog : DecLE (logOp f) (logOp g)) : DecLE f g := by
  have hne : (Ioo (0 : ℝ) B).Nonempty := nonempty_Ioo.mpr hB
  have hfd : dom f ⊆ closure (Ioo (0 : ℝ) B) := by
    have hnf : (interior (dom f)).Nonempty := by rw [hfi]; exact hne
    simpa only [hfi] using decreasing_dom_subset_closure_interior hf hnf
  have hgd : dom g ⊆ closure (Ioo (0 : ℝ) B) := by
    have hng : (interior (dom g)).Nonempty := by rw [hgi]; exact hne
    simpa only [hgi] using decreasing_dom_subset_closure_interior hg hng
  have hfB : dom f ⊆ Icc (0 : ℝ) B := by simpa only [closure_Ioo hB.ne] using hfd
  have hgB : dom g ⊆ Icc (0 : ℝ) B := by simpa only [closure_Ioo hB.ne] using hgd
  have hlf := bounded_domain_logarithm_maximal hf hfB
  have hlg := bounded_domain_logarithm_maximal hg hgB
  have hIf : Ioo (0 : ℝ) B ⊆ dom f := by intro x hx; apply interior_subset; rwa [hfi]
  have hIg : Ioo (0 : ℝ) B ⊆ dom g := by intro x hx; apply interior_subset; rwa [hgi]
  apply decLE_of_initial_interior hf.1 hg.1 isOpen_Ioo ordConnected_Ioo hne
    (by rw [closure_Ioo hB.ne]; exact ⟨le_rfl,hB.le⟩) hfd
    (fun x hx => (hgB hx).1) hIf hIg
  intro x hx y hy hyx u hu v hv
  by_cases hu0 : 0 < u
  · have hul : Real.log u ∈ logOp f x := logOp_mem_iff.mpr
      (by simpa only [Real.exp_log hu0] using hu)
    obtain ⟨z,⟨w,hw⟩,hxz⟩ := (decLE_domains hlf hlg hlog).2
      (mem_lowerHull (show x ∈ dom (logOp f) from ⟨Real.log u,hul⟩))
    have hvw := Decreasing.le_of_lt hg.1 hv (logOp_mem_iff.mp hw) (hyx.trans_le hxz)
    have hv0 : 0 < v := (Real.exp_pos w).trans_le hvw
    have hvl : Real.log v ∈ logOp g y := logOp_mem_iff.mpr
      (by simpa only [Real.exp_log hv0] using hv)
    have h := Real.exp_le_exp.mpr (hlog hul hvl hyx)
    simpa only [Real.exp_log hu0,Real.exp_log hv0] using h
  · exact (le_of_not_gt hu0).trans (hg0 y hy v hv)

theorem nonzero_geometric_log_hardy_properties {q : DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hn : ¬ ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, v = 0)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hi : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    let L := logOp (nonnegativeFloorGraph q).val
    MaximalDecreasing (hardyFamilyIntegral (interior (dom L)) L) ∧
      DecLE L (hardyFamilyIntegral (interior (dom L)) L) := by
  classical
  dsimp only
  rw [logarithm_nonnegative_floor]
  push_neg at hn
  obtain ⟨a,ha,v,hv,hvn⟩ := hn
  have hvpos : 0 < v := lt_of_le_of_ne (hq0 a ha v hv) (Ne.symm hvn)
  obtain ⟨hL,_,hLz,hLp⟩ := logarithm_initial_domain hB q.property hqi ⟨a,ha,v,hv,hvpos⟩
  obtain ⟨hsel,hprefix⟩ := logarithmic_prefix_integrability hB q.property hqi hm hs hi
  exact ⟨(hardyFamilyIntegral_of_locally_integrable hL hLz hLp hsel hprefix).1,
    le_hardyFamilyIntegral_locally_integrable hL hLz hLp hsel hprefix⟩

theorem geometricHardyTransform_logarithm {q : DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hn : ¬ ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, v = 0)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hi : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    let L := logOp (nonnegativeFloorGraph q).val
    logOp (geometricHardyTransform B q) = hardyFamilyIntegral (interior (dom L)) L := by
  have hG := geometricHardyTransform_well_defined hB hqi hq0 hm hs hi
  have hH := nonzero_geometric_log_hardy_properties hB hqi hq0 hn hm hs hi
  rcases hG.2.2.2 with hz | ⟨hP,_⟩
  · exact (hn hz).elim
  · apply Eq.symm
    apply MaximalDecreasing.eq_of_le hH.1 (logOp_decreasing hG.1.1)
    intro x w hw
    exact logOp_mem_iff.mpr (raw_exponential_le_iff.mp hP.2.2.2 x w hw)

theorem le_geometricHardyTransform {q : DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hi : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    DecLE q.val (geometricHardyTransform B q) := by
  classical
  by_cases hz : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, v = 0
  · rw [geometricHardyTransform_zero hz]
    exact decLE_refl q.property.1
  · have hG := geometricHardyTransform_well_defined hB hqi hq0 hm hs hi
    apply logarithm_reflects_initial_decLE hB q.property hG.1 hqi hG.2.1 hG.2.2.1
    rw [geometricHardyTransform_logarithm hB hqi hq0 hz hm hs hi,
      ← logarithm_nonnegative_floor q]
    exact (nonzero_geometric_log_hardy_properties hB hqi hq0 hz hm hs hi).2


theorem positive_graph_value_of_nonzero {q : Operator} {B : ℝ}
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q x, 0 ≤ v)
    (hn : ¬ ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q x, v = 0) :
    ∃ a ∈ Ioo (0 : ℝ) B, ∃ v ∈ q a, 0 < v := by
  classical
  push_neg at hn
  obtain ⟨a,ha,v,hv,hvn⟩ := hn
  exact ⟨a,ha,v,hv,lt_of_le_of_ne (hq0 a ha v hv) (Ne.symm hvn)⟩

theorem geometricHardyTransform_mono {q r : DecGraph} {B : ℝ}
    (hB : 0 < B)
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hri : interior (dom r.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ r.val x, 0 ≤ v)
    {sq sr : ℝ → ℝ} (hqm : Measurable sq) (hrm : Measurable sr)
    (hqs : SelectionOn q.val (Ioo (0 : ℝ) B) sq)
    (hrs : SelectionOn r.val (Ioo (0 : ℝ) B) sr)
    (hqiL : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (sq x)) 0)) < ∞)
    (hriL : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (sr x)) 0)) < ∞)
    (hqr : DecLE q.val r.val) :
    DecLE (geometricHardyTransform B q) (geometricHardyTransform B r) := by
  classical
  have hGq := geometricHardyTransform_well_defined hB hqi hq0 hqm hqs hqiL
  have hGr := geometricHardyTransform_well_defined hB hri hr0 hrm hrs hriL
  by_cases hqz : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, v = 0
  · rw [geometricHardyTransform_zero hqz]
    exact decLE_trans q.property r.property hGr.1 hqr
      (le_geometricHardyTransform hB hri hr0 hrm hrs hriL)
  have hqp := positive_graph_value_of_nonzero hq0 hqz
  have hrz : ¬ ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ r.val x, v = 0 := by
    intro hrz
    obtain ⟨a,ha,v,hv,hvpos⟩ := hqp
    have hy : a/2 ∈ Ioo (0 : ℝ) B := ⟨by linarith [ha.1],by linarith [ha.1,ha.2]⟩
    have hyD : a/2 ∈ dom r.val := by apply interior_subset; rwa [hri]
    obtain ⟨w,hw⟩ := hyD
    have hw0 := hrz (a/2) hy w hw
    have hle := hqr hv hw (by linarith [ha.1] : a/2 < a)
    linarith
  have hrp := positive_graph_value_of_nonzero hr0 hrz
  obtain ⟨hLq,_,hzq,hpq⟩ := logarithm_initial_domain hB q.property hqi hqp
  obtain ⟨hLr,_,hzr,hpr⟩ := logarithm_initial_domain hB r.property hri hrp
  obtain ⟨hqsL,hqiP⟩ := logarithmic_prefix_integrability hB q.property hqi hqm hqs hqiL
  obtain ⟨hrsL,hriP⟩ := logarithmic_prefix_integrability hB r.property hri hrm hrs hriL
  apply logarithm_reflects_initial_decLE hB hGq.1 hGr.1 hGq.2.1 hGr.2.1 hGr.2.2.1
  rw [geometricHardyTransform_logarithm hB hqi hq0 hqz hqm hqs hqiL,
    geometricHardyTransform_logarithm hB hri hr0 hrz hrm hrs hriL,
    logarithm_nonnegative_floor q,logarithm_nonnegative_floor r]
  exact hardyFamilyIntegral_mono_locally_integrable hLq hLr hzq hpq hzr hpr
    hqsL hrsL hqiP hriP (logarithm_preserves_decLE hqr)


end ScalarMonotone.EndOfPaper
end
