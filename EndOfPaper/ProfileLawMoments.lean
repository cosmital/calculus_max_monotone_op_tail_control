import EndOfPaper.ProfileLawTails
import EndOfPaper.ZeroAtomLowerMoment
import EndOfPaper.ProfileLowerNorm

/-!
One fixed actual profile model gives every extended lower moment and the exact 2^(-1/r) norm bound.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper
section
variable {n : ℕ} {s : Option (Fin n) → ℝ → ℝ}
    (hs : ∀ i, AntitoneOn (s i) (Ioo (0 : ℝ) 1))

local notation "E" => PositiveProductPoint (positiveProfileChain s (Ioo (0 : ℝ) 1))

def positiveProfileProductMap (x : E) : ℝ := ∏ j, x.coords j

theorem positiveProfileProductMap_measurable :
    letI := positiveProfileChainMetric hs
    letI : MeasurableSpace E := borel E
    Measurable (positiveProfileProductMap (s := s)) := by
  letI := positiveProfileChainMetric hs
  letI : MeasurableSpace E := borel E
  exact Finset.measurable_prod _ (fun j _ => positiveProfilePoint_coordinate_measurable hs j)

theorem positiveProfileProductMap_zero : positiveProfileProductMap (s := s) positiveProfileHalfOrigin = 0 := by
  simp only [positiveProfileProductMap,Fintype.prod_option,positiveProfileHalfOrigin,Pi.zero_apply,zero_mul]

theorem positiveProfileProductMap_modulus (x y : E) :
    letI := positiveProfileChainMetric hs
    |positiveProfileProductMap x-positiveProfileProductMap y| =
      dist x y*(∏ i : Fin n, max (x.coords (some i)) (y.coords (some i))) := by
  letI := positiveProfileChainMetric hs
  exact (positiveChainMetric_product_identity (positiveProfileChain_properties hs).1
    (positiveProfileChain_properties hs).2.1 (positiveProfileChain_properties hs).2.2.1 x y).symm

theorem positiveProfileHalfLaw_product_moment (hsm : ∀ i, Measurable (s i))
    (h0 : ∀ j u, u ∈ Ioo (0 : ℝ) 1 → 0 ≤ s j u) {r : ℝ} (hr : 0 < r) :
    letI := positiveProfileChainMetric hs
    letI : MeasurableSpace E := borel E
    (∫⁻ x : E, ENNReal.ofReal (|positiveProfileProductMap x|^r) ∂positiveProfileHalfLaw hs) =
      (2 : ℝ≥0∞)⁻¹*(∫⁻ u, ENNReal.ofReal ((∏ j, s j u)^r) ∂unitUniform) := by
  letI := positiveProfileChainMetric hs
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  have hΦ := positiveProfileProductMap_measurable hs
  have hF : Measurable (fun x : E => ENNReal.ofReal (|positiveProfileProductMap x|^r)) :=
    (((Real.continuous_rpow_const hr.le).comp continuous_abs).measurable.comp hΦ).ennreal_ofReal
  have hF0 : ENNReal.ofReal (|positiveProfileProductMap (s := s) positiveProfileHalfOrigin|^r) = 0 := by
    rw [positiveProfileProductMap_zero]
    simp only [abs_zero,Real.zero_rpow hr.ne',ENNReal.ofReal_zero]
  change (∫⁻ x : E, _ ∂halfOriginMixture _ positiveProfileHalfOrigin) = _
  rw [halfOriginMixture_lintegral
    (Measure.map (positiveProfilePointSample s (Ioo (0 : ℝ) 1)) unitUniform)
    (positiveProfileHalfOrigin (s := s))
    (fun x : E => ENNReal.ofReal (|positiveProfileProductMap x|^r)) hF0]
  congr 1
  rw [lintegral_map hF (positiveProfilePointSample_measurable hs hsm measurableSet_Ioo)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  change ENNReal.ofReal (|(∏ j, positiveProfileSampleVector s (Ioo (0 : ℝ) 1) u j)|^r) = _
  rw [positiveProfileSampleVector_product h0 hu,
    abs_of_nonneg (Finset.prod_nonneg (fun j _ => h0 j u hu))]

theorem positiveProfileHalfLaw_lower_moment (hsm : ∀ i, Measurable (s i))
    (h0 : ∀ j u, u ∈ Ioo (0 : ℝ) 1 → 0 ≤ s j u) {r : ℝ} (hr : 0 < r) :
    letI := positiveProfileChainMetric hs
    letI : MeasurableSpace E := borel E
    (2 : ℝ≥0∞)⁻¹*(∫⁻ u, ENNReal.ofReal ((∏ j, s j u)^r) ∂unitUniform) ≤
      ∫⁻ z : E × E, ENNReal.ofReal
        (|positiveProfileProductMap z.1-positiveProfileProductMap z.2|^r)
        ∂((positiveProfileHalfLaw hs).prod (positiveProfileHalfLaw hs)) := by
  letI := positiveProfileChainMetric hs
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  let ν := positiveProfileHalfLaw hs
  letI : IsProbabilityMeasure ν := positiveProfileHalfLaw_probability hs hsm
  have hΦ := positiveProfileProductMap_measurable hs
  have hcopy := product_self_independent_copies ν
  have hzero : (1/2 : ℝ≥0∞) ≤ ν {x : E | positiveProfileProductMap x = 0} := by
    apply (halfOriginMixture_origin_mass _ (positiveProfileHalfOrigin (s := s))).trans
    apply measure_mono
    intro x hx
    have he : x = positiveProfileHalfOrigin := mem_singleton_iff.mp hx
    rw [he]
    exact positiveProfileProductMap_zero
  have hzeroPair : (1/2 : ℝ≥0∞) ≤ (ν.prod ν) {z : E × E | positiveProfileProductMap z.1 = 0} := by
    have he : (ν.prod ν) {z : E × E | positiveProfileProductMap z.1 = 0} =
        ν {x : E | positiveProfileProductMap x = 0} := by
      change (ν.prod ν) (Prod.fst ⁻¹' {x : E | positiveProfileProductMap x = 0}) = _
      rw [← Measure.map_apply measurable_fst (measurableSet_eq_fun hΦ measurable_const),
        Measure.map_fst_prod,measure_univ,one_smul]
    rwa [he]
  have hb := independent_copy_zero_atom_moment_lower (hΦ.comp measurable_fst) (hΦ.comp measurable_snd)
    (hcopy.1.comp hΦ hΦ) (hcopy.2.comp hΦ) hzeroPair hr
  have hF : Measurable (fun x : E => ENNReal.ofReal (|positiveProfileProductMap x|^r)) :=
    (((Real.continuous_rpow_const hr.le).comp continuous_abs).measurable.comp hΦ).ennreal_ofReal
  have hSingle : (∫⁻ z : E × E, ENNReal.ofReal (|positiveProfileProductMap z.1|^r) ∂(ν.prod ν)) =
      ∫⁻ x : E, ENNReal.ofReal (|positiveProfileProductMap x|^r) ∂ν := by
    rw [← lintegral_map hF measurable_fst,Measure.map_fst_prod,measure_univ,one_smul]
  calc
    _ = ∫⁻ x : E, ENNReal.ofReal (|positiveProfileProductMap x|^r) ∂ν :=
      (positiveProfileHalfLaw_product_moment hs hsm h0 hr).symm
    _ = ∫⁻ z : E × E, ENNReal.ofReal (|positiveProfileProductMap z.1|^r) ∂(ν.prod ν) := hSingle.symm
    _ ≤ _ := hb

theorem positiveProfileHalfLaw_lower_norm (hsm : ∀ i, Measurable (s i))
    (h0 : ∀ j u, u ∈ Ioo (0 : ℝ) 1 → 0 ≤ s j u) {r : ℝ} (hr : 0 < r) :
    letI := positiveProfileChainMetric hs
    letI : MeasurableSpace E := borel E
    ENNReal.ofReal ((2 : ℝ)^(-1/r))*
      eLpNorm (fun u => ∏ j, s j u) (ENNReal.ofReal r) unitUniform ≤
    eLpNorm (fun z : E × E => positiveProfileProductMap z.1-positiveProfileProductMap z.2)
      (ENNReal.ofReal r) ((positiveProfileHalfLaw hs).prod (positiveProfileHalfLaw hs)) := by
  letI := positiveProfileChainMetric hs
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  have hY0 : 0 ≤ᵐ[unitUniform] (fun u => ∏ j, s j u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact Finset.prod_nonneg (fun j _ => h0 j u hu)
  have hMoment := positiveProfileHalfLaw_lower_moment hs hsm h0 hr
  have hHalf : ENNReal.ofReal (1/2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
    rw [one_div,ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [← hHalf] at hMoment
  have hb := eLpNorm_ge_of_nonnegative_moment_bound
    (Eventually.of_forall (fun z : E × E => abs_nonneg (positiveProfileProductMap z.1-positiveProfileProductMap z.2)))
    hY0 hr (by norm_num : (0 : ℝ) ≤ 1/2) hMoment
  have hC : (1/2 : ℝ)^(r⁻¹) = (2 : ℝ)^(-1/r) := by
    rw [one_div,Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2),← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hNorm : eLpNorm (fun z : E × E => |positiveProfileProductMap z.1-positiveProfileProductMap z.2|)
      (ENNReal.ofReal r) ((positiveProfileHalfLaw hs).prod (positiveProfileHalfLaw hs)) =
    eLpNorm (fun z : E × E => positiveProfileProductMap z.1-positiveProfileProductMap z.2)
      (ENNReal.ofReal r) ((positiveProfileHalfLaw hs).prod (positiveProfileHalfLaw hs)) := by
    simpa only [Real.norm_eq_abs] using eLpNorm_norm (p := ENNReal.ofReal r)
      (μ := (positiveProfileHalfLaw hs).prod (positiveProfileHalfLaw hs))
      (fun z : E × E => positiveProfileProductMap z.1-positiveProfileProductMap z.2)
  simpa only [hC,hNorm] using hb

end
end ScalarMonotone.EndOfPaper
end
