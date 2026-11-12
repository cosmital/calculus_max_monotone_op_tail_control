import EndOfPaper.GeometricHardyOrder
import EndOfPaper.GeometricMeanJensen
import EndOfPaper.GeometricHardySelections

/-!
The manuscript-facing whole geometric/arithmetic Hardy
comparison and order preservation, with arbitrary selections.
Ordinary L1 is required only for the arithmetic upper bound.
-/

open Set Filter MeasureTheory
open scoped Interval ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem initial_profile_hardy_data {q : Operator} {B : ℝ}
    (hB : 0 < B) (hq : MaximalDecreasing q)
    (hqi : interior (dom q) = Ioo (0 : ℝ) B)
    {s : ℝ → ℝ} (hs : SelectionOn q (Ioo (0 : ℝ) B) s)
    (hi : IntegrableOn s (Ioo (0 : ℝ) B) volume) :
    let H := hardyFamilyIntegral (interior (dom q)) q
    MaximalDecreasing H ∧ interior (dom H) = Ioo (0 : ℝ) B ∧
      dom H ⊆ Icc (0 : ℝ) B ∧
      (∀ p ∈ Ioo (0 : ℝ) B, H p = {hardyScalar s p}) ∧ DecLE q H := by
  have hI : Ioo (0 : ℝ) B ⊆ dom q := by intro x hx; apply interior_subset; rwa [hqi]
  have hne : (interior (dom q)).Nonempty := by rw [hqi]; exact nonempty_Ioo.mpr hB
  have hqd : dom q ⊆ Icc (0 : ℝ) B := by
    simpa only [hqi,closure_Ioo hB.ne] using decreasing_dom_subset_closure_interior hq hne
  have hzero : (0 : ℝ) ∈ closure (dom q) := by
    apply closure_mono hI
    rw [closure_Ioo hB.ne]
    exact ⟨le_rfl,hB.le⟩
  have hz : IsGLB (dom q) 0 := by
    refine ⟨fun x hx => (hqd hx).1, ?_⟩
    intro b hb
    exact closure_minimal (show dom q ⊆ Ici b from hb) isClosed_Ici hzero
  have hp : ∃ a ∈ dom q, 0 < a :=
    ⟨B/2,hI ⟨by linarith,by linarith⟩,by linarith⟩
  have hs' : SelectionOn q (interior (dom q)) s := by rwa [hqi]
  have hi' : Integrable s (volume.restrict (interior (dom q))) := by rwa [hqi]
  have hH := hardyFamilyIntegral_of_integrable hq hz hp hs' hi'
  refine ⟨hH.1,hH.2.1.trans hqi,?_,?_,le_hardyFamilyIntegral hq hz hp hs' hi'⟩
  · simpa only [hqi,closure_Ioo hB.ne] using hH.2.2.1
  · intro p hpI
    exact hH.2.2.2.1 p (by rwa [hqi])

theorem initial_profile_hardy_nonnegative {q : Operator} {B : ℝ}
    (hB : 0 < B) (hq : MaximalDecreasing q)
    (hqi : interior (dom q) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q x, 0 ≤ v)
    {s : ℝ → ℝ} (hs : SelectionOn q (Ioo (0 : ℝ) B) s)
    (hi : IntegrableOn s (Ioo (0 : ℝ) B) volume) :
    ∀ p ∈ Ioo (0 : ℝ) B,
      ∀ v ∈ hardyFamilyIntegral (interior (dom q)) q p, 0 ≤ v := by
  have hH := initial_profile_hardy_data hB hq hqi hs hi
  intro p hp v hv
  rw [hH.2.2.2.1 p hp] at hv
  rw [mem_singleton_iff.mp hv]
  have hpi : IntervalIntegrable s volume 0 p :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hp.1.le).mpr
      (hi.mono_set (fun x hx => ⟨hx.1,hx.2.trans hp.2⟩))
  have h := hardyScalar_mono hp.1
    (show IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 p from intervalIntegrable_const) hpi
    (fun x hx => hq0 x ⟨hx.1,hx.2.trans hp.2⟩ (s x) (hs x ⟨hx.1,hx.2.trans hp.2⟩))
  simpa only [hardyScalar_const 0 hp.1.ne'] using h

theorem hardy_log_le_log_hardy {q : Operator} {B : ℝ}
    (hB : 0 < B) (hq : MaximalDecreasing q)
    (hqi : interior (dom q) = Ioo (0 : ℝ) B)
    (hpositive : ∃ a ∈ Ioo (0 : ℝ) B, ∃ v ∈ q a, 0 < v)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q (Ioo (0 : ℝ) B) s)
    (hi : IntegrableOn s (Ioo (0 : ℝ) B) volume)
    (hlogi : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    DecLE (hardyFamilyIntegral (interior (dom (logOp q))) (logOp q))
      (logOp (hardyFamilyIntegral (interior (dom q)) q)) := by
  obtain ⟨hL,hLd,hLz,hLp⟩ := logarithm_initial_domain hB hq hqi hpositive
  obtain ⟨hsel,hprefix⟩ := logarithmic_prefix_integrability hB hq hqi hm hs hlogi
  have hHL := hardyFamilyIntegral_of_locally_integrable hL hLz hLp hsel hprefix
  have hH := initial_profile_hardy_data hB hq hqi hs hi
  have hLI : interior (dom (logOp q)) ⊆ Ioo (0 : ℝ) B := by
    simpa only [interior_Icc] using interior_mono hLd
  have hJ (p : ℝ) (hp : p ∈ interior (dom (logOp q))) :
      Real.exp (hardyScalar (fun x => Real.log (s x)) p) ≤ hardyScalar s p := by
    have hpI := hLI hp
    have hpi : IntervalIntegrable s volume 0 p :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hpI.1.le).mpr
        (hi.mono_set (fun x hx => ⟨hx.1,hx.2.trans hpI.2⟩))
    obtain ⟨w,hw⟩ := interior_subset hp
    apply geometric_average_le_arithmetic hpI.1 hpi (hprefix p hp)
    intro x hx
    have hle := Decreasing.le_of_lt hq.1
      (hs x ⟨hx.1,hx.2.trans hpI.2⟩) (logOp_mem_iff.mp hw) hx.2
    exact (Real.exp_pos w).trans_le hle
  have hcoverL : interior (dom (logOp q)) ⊆
      dom (hardyFamilyIntegral (interior (dom (logOp q))) (logOp q)) := by
    intro p hp
    apply interior_subset
    rwa [hHL.2.1]
  have hcoverH : interior (dom (logOp q)) ⊆
      dom (logOp (hardyFamilyIntegral (interior (dom q)) q)) := by
    intro p hp
    have hpos := (Real.exp_pos (hardyScalar (fun x => Real.log (s x)) p)).trans_le (hJ p hp)
    refine ⟨Real.log (hardyScalar s p),logOp_mem_iff.mpr ?_⟩
    rw [Real.exp_log hpos,hH.2.2.2.1 p (hLI hp)]
    rfl
  have hne := (decreasing_zero_inf_domain_geometry hL hLz hLp).2.1
  apply decLE_of_initial_interior hHL.1.1 (logOp_decreasing hH.1.1)
    isOpen_interior (decreasing_zero_inf_domain_geometry hL hLz hLp).1 hne
    (zero_mem_closure_decreasing_domain_interior hL hLz hne) hHL.2.2.1
    (fun x hx => (hH.2.2.1 (logarithm_dom_subset hx)).1) hcoverL hcoverH
  intro p hp r hr hrp u hu v hv
  rw [hHL.2.2.2.1 p hp] at hu
  have hmp : hardyScalar s p ∈ hardyFamilyIntegral (interior (dom q)) q p := by
    rw [hH.2.2.2.1 p (hLI hp)]
    rfl
  have hle := Decreasing.le_of_lt hH.1.1 (logOp_mem_iff.mp hv) hmp hrp
  have hJp : Real.exp u ≤ hardyScalar s p := by
    rw [mem_singleton_iff.mp hu]
    exact hJ p hp
  exact Real.exp_le_exp.mp (hJp.trans hle)

theorem geometricHardyTransform_le_hardy {q : DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hi : IntegrableOn s (Ioo (0 : ℝ) B) volume)
    (hlogi : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    DecLE (geometricHardyTransform B q) (hardyFamilyIntegral (interior (dom q.val)) q.val) := by
  classical
  have hG := geometricHardyTransform_well_defined hB hqi hq0 hm hs hlogi
  have hH := initial_profile_hardy_data hB q.property hqi hs hi
  by_cases hz : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, v = 0
  · rw [geometricHardyTransform_zero hz]
    exact hH.2.2.2.2
  · apply logarithm_reflects_initial_decLE hB hG.1 hH.1 hG.2.1 hH.2.1
      (initial_profile_hardy_nonnegative hB q.property hqi hq0 hs hi)
    rw [geometricHardyTransform_logarithm hB hqi hq0 hz hm hs hlogi,
      logarithm_nonnegative_floor q]
    exact hardy_log_le_log_hardy hB q.property hqi (positive_graph_value_of_nonzero hq0 hz)
      hm hs hi hlogi


/-- The manuscript-facing comparison. Ordinary L1 is expressed by existence
of an integrable selection; no global measurability of the given selection
and no global logarithmic integrability are added. -/
theorem hardy_geometric_comparison {q : DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    DecLE q.val (geometricHardyTransform B q) ∧
      ((∃ u : ℝ → ℝ, SelectionOn q.val (Ioo (0 : ℝ) B) u ∧
          IntegrableOn u (Ioo (0 : ℝ) B) volume) →
        DecLE (geometricHardyTransform B q) (hardyFamilyIntegral (interior (dom q.val)) q.val)) := by
  obtain ⟨t,ht,hts,harea⟩ := measurable_selection_same_positive_log_area hqi hs
  have htP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (t x)) 0)) < ∞ := by
    rwa [harea]
  refine ⟨le_geometricHardyTransform hB hqi hq0 ht hts htP, ?_⟩
  rintro ⟨u,hus,hui⟩
  have he := decreasing_selections_ae_eq q.property.1 hus hts volume measurableSet_Ioo
  have hti : IntegrableOn t (Ioo (0 : ℝ) B) volume := hui.congr he
  exact geometricHardyTransform_le_hardy hB hqi hq0 ht hts hti htP

theorem geometric_hardy_order_preserving {q r : DecGraph} {B : ℝ} (hB : 0 < B)
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hri : interior (dom r.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hr0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ r.val x, 0 ≤ v)
    {sq sr : ℝ → ℝ} (hqs : SelectionOn q.val (Ioo (0 : ℝ) B) sq)
    (hrs : SelectionOn r.val (Ioo (0 : ℝ) B) sr)
    (hPq : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (sq x)) 0)) < ∞)
    (hPr : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (sr x)) 0)) < ∞)
    (hqr : DecLE q.val r.val) :
    DecLE (geometricHardyTransform B q) (geometricHardyTransform B r) := by
  obtain ⟨tq,htq,hstq,hqarea⟩ := measurable_selection_same_positive_log_area hqi hqs
  obtain ⟨tr,htr,hstr,hrarea⟩ := measurable_selection_same_positive_log_area hri hrs
  exact geometricHardyTransform_mono hB hqi hri hq0 hr0 htq htr hstq hstr
    (by rwa [hqarea]) (by rwa [hrarea]) hqr

end ScalarMonotone.EndOfPaper
end
