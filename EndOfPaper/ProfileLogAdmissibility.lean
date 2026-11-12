import EndOfPaper.ProductLogAreas
import EndOfPaper.CommonPositivePrefix

/-!
The single product positive-log area yields every
individual area for arbitrary input selections. Measurable
representatives are derived and then transferred back almost surely.
-/

open Set Filter MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem nonzero_profiles_individual_log_areas {ι : Type*} [Fintype ι]
    {q : ι → Operator} {sq : ι → ℝ → ℝ} {B : ℝ} (hB : 0 < B)
    (hq : ∀ i, MaximalDecreasing (q i))
    (hq0 : ∀ i x, x ∈ Ioo (0 : ℝ) B → ∀ v ∈ q i x, 0 ≤ v)
    (hn : ∀ i, ¬ ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q i x, v = 0)
    (hsq : ∀ i, SelectionOn (q i) (Ioo (0 : ℝ) B) (sq i))
    (hP : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (∏ i, sq i x)) 0)) < ∞) :
    ∀ i, (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (sq i x)) 0)) < ∞ := by
  classical
  choose s hsm hss using fun i => exists_global_measurable_selection
    (Or.inr (hq i).1) measurableSet_Ioo (fun x hx => ⟨sq i x,hsq i x hx⟩)
  have he (i : ι) : s i =ᵐ[volume.restrict (Ioo (0 : ℝ) B)] sq i := by
    apply ae_selections_ae_eq (Or.inr (hq i).1) (volume.restrict (Ioo (0 : ℝ) B))
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact hss i x hx
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact hsq i x hx
  have heAll : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) B)), ∀ i, s i x = sq i x :=
    ae_all_iff.mpr he
  have heProd : (fun x => ∏ i, s i x) =ᵐ[volume.restrict (Ioo (0 : ℝ) B)]
      (fun x => ∏ i, sq i x) := by
    filter_upwards [heAll] with x hx
    simp only [hx]
  have hPs : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (∏ i, s i x)) 0)) < ∞ := by
    have heArea : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (∏ i, s i x)) 0)) =
        ∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (∏ i, sq i x)) 0) :=
      lintegral_congr_ae (heProd.fun_comp (fun y : ℝ => ENNReal.ofReal (max (Real.log y) 0)))
    rw [heArea]
    exact hP
  obtain ⟨b,hb,hb0⟩ := nonzero_profiles_common_positive_point hB hq hq0 hn hss
  have hPi := positive_log_areas_of_finite_product hsm
    (fun i => selection_antitoneOn (hq i).1 (hss i))
    (fun i x hx => hq0 i x hx (s i x) (hss i x hx)) hb hb0 hPs
  intro i
  have heArea : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s i x)) 0)) =
      ∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (sq i x)) 0) :=
    lintegral_congr_ae ((he i).fun_comp (fun y : ℝ => ENNReal.ofReal (max (Real.log y) 0)))
  rw [← heArea]
  exact hPi i

end ScalarMonotone.EndOfPaper
end
