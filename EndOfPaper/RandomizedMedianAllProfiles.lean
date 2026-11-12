import EndOfPaper.RandomizedCentering
import EndOfPaper.QuantileDependenceCounterexample

/-!
The sharper whole median profile with zero inputs retained when the individual areas have been derived.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem tailQuantile_le_nonnegative_profile_of_ae_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hzero : Y =ᵐ[μ] (fun _ => 0)) {q : Operator}
    (hq : MaximalDecreasing q) (hqi : interior (dom q) = Ioo (0 : ℝ) 1)
    {s : ℝ → ℝ} (hs : SelectionOn q (Ioo (0 : ℝ) 1) s)
    (hs0 : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ s x) :
    DecLE (tailQuantile (Measure.map Y μ)) q := by
  have hlaw : Measure.map Y μ = Measure.dirac (0 : ℝ) := by
    rw [Measure.map_congr hzero,Measure.map_const,measure_univ,one_smul]
  rw [hlaw]
  have hsel : SelectionOn (tailQuantile (Measure.dirac (0 : ℝ))) (Ioo (0 : ℝ) 1) (fun _ => 0) := by
    intro x hx
    rw [tailQuantile_dirac_interior 0 hx]
    rfl
  apply initial_decLE_of_selection_ae_le (by norm_num) (tailQuantile_maximal _) hq
    (tailQuantile_domain_interior _) hqi hsel hs
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact hs0 x hx

theorem randomized_lipschitz_median_with_individual_areas
    {n : ℕ} (hn : 0 < n) {Ω E F : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [MetricSpace F] [MeasurableSpace F] [OpensMeasurableSpace F]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z Z' : Ω → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (hindep : IndepFun Z Z' μ) (hident : IdentDistrib Z Z' μ μ)
    {qΔ : DecGraph} (hδdom : interior (dom qΔ.val) = Ioo (0 : ℝ) 1)
    (hδ0 : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, 0 ≤ v)
    (hδ : ∀ f : E → ℝ, LipschitzWith 1 f →
      DecLE (tailQuantile (Measure.map (fun ω => |f (Z ω)-f (Z' ω)|) μ)) qΔ.val)
    {Λ : Fin n → E → ℝ} (hΛm : ∀ i, Measurable (Λ i)) (hΛ0 : ∀ i z, 0 ≤ Λ i z)
    {q : Fin n → DecGraph} (hqdom : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ i p, p ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ (q i).val p, 0 ≤ v)
    (hQ : ∀ i, DecLE (tailQuantile (Measure.map (fun ω => Λ i (Z ω)) μ)) (q i).val)
    {sqΔ : ℝ → ℝ} (hsδ : SelectionOn qΔ.val (Ioo (0 : ℝ) 1) sqΔ)
    {sq : Fin n → ℝ → ℝ} (hsq : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) 1) (sq i))
    (hP : (∫⁻ p in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (max (Real.log (sqΔ p*(∏ i, sq i p))) 0)) < ∞)
    (hPi : ∀ i, (∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (sq i p)) 0)) < ∞)
    {Φ : E → F} (hΦ : Measurable Φ)
    (hmod : ∀ x y, dist (Φ x) (Φ y) ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
    {g : F → ℝ} (hg : LipschitzWith 1 g) {m : ℝ}
    (hm : IsRealMedian (fun ω => g (Φ (Z ω))) μ m) :
    let G := geometricFiniteProfileProduct q hqdom hq0 hsq hPi
    let hG := geometricFiniteProfileProduct_properties hqdom hq0 hsq hPi
    DecLE (tailQuantile (Measure.map (fun ω => |g (Φ (Z ω))-m|) μ))
      (completedDecreasingRestriction (Ioo (0 : ℝ) 1)
        (positiveInputDilation (1/6)
          (completedProfileProduct 1 qΔ G (by norm_num) hδdom hG.1 hδ0 hG.2.1).val)) := by
  classical
  let G := geometricFiniteProfileProduct q hqdom hq0 hsq hPi
  have hG := geometricFiniteProfileProduct_properties hqdom hq0 hsq hPi
  let P := completedProfileProduct 1 qΔ G (by norm_num) hδdom hG.1 hδ0 hG.2.1
  have hPD := (completedProfileProduct_domain (by norm_num) hδdom hG.1 hδ0 hG.2.1).1
  have hP0 := completedProfileProduct_nonnegative (by norm_num) hδdom hG.1 hδ0 hG.2.1
  let D := completedProfileDilation 1 1 (1/6) P hPD (by norm_num) (by norm_num) (by norm_num)
  have hD : interior (dom D.val) = Ioo (0 : ℝ) 1 ∧
      ∀ x ∈ Ioo (0 : ℝ) 1, D.val x = P.val ((1/6)*x) :=
    completedProfileDilation_properties hPD (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1/6) (by norm_num : (1/6 : ℝ)*1 ≤ 1)
  change DecLE (tailQuantile (Measure.map (fun ω => |g (Φ (Z ω))-m|) μ)) D.val
  by_cases hz : (∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0) ∨
      ∃ i, ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0
  · have hcopy := randomized_lipschitz_zero_input hZ hZ' hident hδ
      (fun p hp => interior_subset (show p ∈ interior (dom qΔ.val) from by rwa [hδdom]))
      hΛm hΛ0 (fun i p hp => interior_subset (show p ∈ interior (dom (q i).val) from by rwa [hqdom i]))
      hQ hmod hz hg
    have hhm : Measurable (fun x => g (Φ x)) := hg.continuous.measurable.comp hΦ
    have hzero := median_difference_zero_of_copy_zero (hhm.comp hZ) (hhm.comp hZ')
      (hindep.comp hhm hhm) (hident.comp hhm) hm hcopy
    obtain ⟨s,_,hs⟩ := exists_global_measurable_selection (Or.inr D.property.1) measurableSet_Ioo
      (fun x hx => interior_subset (show x ∈ interior (dom D.val) from by rwa [hD.1]))
    apply tailQuantile_le_nonnegative_profile_of_ae_zero hzero D.property hD.1 hs
    intro x hx
    have hvalue := hs x hx
    rw [hD.2 x hx] at hvalue
    apply hP0 ((1/6)*x) _ (s x) hvalue
    constructor <;> linarith [hx.1,hx.2]
  · have hnδ : ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0 := fun h => hz (Or.inl h)
    have hnq : ∀ i, ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0 :=
      fun i h => hz (Or.inr ⟨i,h⟩)
    exact randomized_lipschitz_median_sharper_bound hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0
      hqdom hq0 hQ hsδ hsq hP hΦ hmod hg hm hnδ hnq

end ScalarMonotone.EndOfPaper
end
