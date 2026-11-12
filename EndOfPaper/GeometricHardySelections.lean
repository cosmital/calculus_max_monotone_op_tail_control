import EndOfPaper.GeometricHardy

/-!
The arbitrary-selection manuscript convention for
geometric Hardy admissibility. A globally measurable
representative and the identical positive-log area are derived.
-/

open Set Filter MeasureTheory
open scoped Interval ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem measurable_selection_same_positive_log_area {q : DecGraph} {B : ℝ}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s) :
    ∃ t : ℝ → ℝ, Measurable t ∧ SelectionOn q.val (Ioo (0 : ℝ) B) t ∧
      (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (t x)) 0)) =
        ∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0) := by
  have hI : Ioo (0 : ℝ) B ⊆ dom q.val := by
    intro x hx
    apply interior_subset
    rwa [hqi]
  obtain ⟨t,ht,hts⟩ := exists_global_measurable_selection (Or.inr q.property.1) measurableSet_Ioo hI
  have he := decreasing_selections_ae_eq q.property.1 hs hts volume measurableSet_Ioo
  refine ⟨t,ht,hts,?_⟩
  exact lintegral_congr_ae (he.symm.fun_comp (fun y : ℝ => ENNReal.ofReal (max (Real.log y) 0)))

theorem geometric_hardy_extension_any_selection {q : DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    (hn : ¬ ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, v = 0)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hi : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    let L := logOp (q ⊔ DecGraph.constant 0).val
    ∃! g : Operator, MaximalDecreasing g ∧ interior (dom g) = Ioo (0 : ℝ) B ∧
      (∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ g x, 0 ≤ v) ∧
      comp (ofFun Real.exp) (hardyFamilyIntegral (interior (dom L)) L) ≤ g := by
  obtain ⟨t,ht,hts,harea⟩ := measurable_selection_same_positive_log_area hqi hs
  exact geometric_hardy_extension_of_nonzero hB q.property hqi hq0 hn ht hts (by rwa [harea])

theorem geometricHardyTransform_well_defined_any_selection {q : DecGraph} {B : ℝ}
    (hB : 0 < B) (hqi : interior (dom q.val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) B) s)
    (hi : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    MaximalDecreasing (geometricHardyTransform B q) ∧
      interior (dom (geometricHardyTransform B q)) = Ioo (0 : ℝ) B ∧
      (∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ geometricHardyTransform B q x, 0 ≤ v) ∧
      ((∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q.val x, v = 0) ∨
        (geometricHardyExtensionPredicate B q (geometricHardyTransform B q) ∧
          ∀ g, geometricHardyExtensionPredicate B q g → g = geometricHardyTransform B q)) := by
  obtain ⟨t,ht,hts,harea⟩ := measurable_selection_same_positive_log_area hqi hs
  exact geometricHardyTransform_well_defined hB hqi hq0 ht hts (by rwa [harea])

end ScalarMonotone.EndOfPaper
end
