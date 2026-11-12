import EndOfPaper.FamilyIntegral
import EndOfPaper.HardyScalar

/-!
Dilation endpoint integrability and scalar area identities for the Hardy
family construction. Affine substitution and ae selection equality discharge
endpoint integrability. Completion of the whole dilation-family operator is
a separate remaining proof obligation.
-/

open Set Filter MeasureTheory
open scoped Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem maximal_decreasing_interior_endpoints_mem {f : Operator}
    (hf : MaximalDecreasing f) {x : ℝ} (hx : x ∈ interior (dom f)) :
    sInf (f x) ∈ f x ∧ sSup (f x) ∈ f x := by
  have hxi : x ∈ interior (dom (negOut f)) := by simpa only [dom_negOut] using hx
  have he := maximal_interior_fiber_endpoints_mem hf hxi
  obtain ⟨hl, hu⟩ := decreasing_interior_neg_endpoints hf hx
  rw [hl, hu] at he
  exact ⟨by simpa only [negOut, mem_setOf_eq, neg_neg] using he.2,
    by simpa only [negOut, mem_setOf_eq, neg_neg] using he.1⟩

/-- Positive multiplication of the input preserves the decreasing relation;
this local statement needs no extra completion assumption. -/
theorem decreasing_input_mul {f : Operator} (hf : Decreasing f)
    {p : ℝ} (hp : 0 < p) : Decreasing (fun r => f (r*p)) := by
  apply increasing_iff_order.mpr
  intro r u s v hu hv hrs
  change -u ∈ f (r*p) at hu
  change -v ∈ f (s*p) at hv
  have h := Decreasing.le_of_lt hf hu hv (mul_lt_mul_of_pos_right hrs hp)
  linarith

/-- Dilation endpoint maps are integrable because they agree ae with the
chosen integrable scalar selection. No atomlessness of a parameter law is
postulated; here the actual averaging measure is Lebesgue measure in r. -/
theorem hardy_dilation_endpoints_integrable {f : Operator} (hf : MaximalDecreasing f)
    {I : Set ℝ} (hI : I ⊆ interior (dom f)) {s : ℝ → ℝ}
    (hs : SelectionOn f I s) {p : ℝ} (hp : 0 < p)
    (hmul : ∀ r ∈ Ioo (0 : ℝ) 1, r*p ∈ I)
    (hi : Integrable (fun r => s (r*p)) (volume.restrict (Ioo (0 : ℝ) 1))) :
    Integrable (fun r => sInf (f (r*p))) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
    Integrable (fun r => sSup (f (r*p))) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
    (fun r => sInf (f (r*p))) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      (fun r => s (r*p)) ∧
    (fun r => sSup (f (r*p))) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      (fun r => s (r*p)) := by
  let g : Operator := fun r => f (r*p)
  have hg : Decreasing g := decreasing_input_mul hf.1 hp
  have hsel : SelectionOn g (Ioo (0 : ℝ) 1) (fun r => s (r*p)) :=
    fun r hr => hs (r*p) (hmul r hr)
  have hl : SelectionOn g (Ioo (0 : ℝ) 1) (fun r => sInf (f (r*p))) :=
    fun r hr => (maximal_decreasing_interior_endpoints_mem hf (hI (hmul r hr))).1
  have hu : SelectionOn g (Ioo (0 : ℝ) 1) (fun r => sSup (f (r*p))) :=
    fun r hr => (maximal_decreasing_interior_endpoints_mem hf (hI (hmul r hr))).2
  have hel := decreasing_selections_ae_eq hg hl hsel volume measurableSet_Ioo
  have heu := decreasing_selections_ae_eq hg hu hsel volume measurableSet_Ioo
  exact ⟨hi.congr hel.symm, hi.congr heu.symm, hel, heu⟩

/-- Ordinary affine substitution supplies the integrability hypothesis above
and identifies both endpoint areas with the scalar Hardy value. -/
theorem hardy_dilation_endpoint_areas {f : Operator} (hf : MaximalDecreasing f)
    {I : Set ℝ} (hI : I ⊆ interior (dom f)) {s : ℝ → ℝ}
    (hs : SelectionOn f I s) {p : ℝ} (hp : 0 < p)
    (hmul : ∀ r ∈ Ioo (0 : ℝ) 1, r*p ∈ I)
    (hi : IntervalIntegrable s volume 0 p) :
    Integrable (fun r => sInf (f (r*p))) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
    Integrable (fun r => sSup (f (r*p))) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
    (∫ r in Ioo (0 : ℝ) 1, sInf (f (r*p))) = hardyScalar s p ∧
    (∫ r in Ioo (0 : ℝ) 1, sSup (f (r*p))) = hardyScalar s p := by
  have hd := hardyScalar_dilation_integrable hp hi
  have hdi : Integrable (fun r => s (r*p)) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hd
  obtain ⟨hl, hu, hel, heu⟩ := hardy_dilation_endpoints_integrable hf hI hs hp hmul hdi
  have harea : (∫ r in Ioo (0 : ℝ) 1, s (r*p)) = hardyScalar s p := by
    rw [hardyScalar_dilation s hp,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  exact ⟨hl, hu, (integral_congr_ae hel).trans harea, (integral_congr_ae heu).trans harea⟩

end ScalarMonotone.EndOfPaper
end
