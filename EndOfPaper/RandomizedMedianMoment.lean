import EndOfPaper.RandomizedMomentBound
import EndOfPaper.IndependentCopyTails
import EndOfPaper.QuantileTailDilation
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
Actual median existence, both original zero-input
cases, every r>0 median moment bound and derived uncentered
MemLp from the original prescribed product moment.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem isRealMedian_of_tailQuantile_half {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {m : ℝ} (hm : m ∈ tailQuantile (Measure.map X μ) (1/2)) : IsRealMedian X μ m := by
  have hhi : (1/2 : ℝ) ≤ μ.real {ω | m ≤ X ω} := by
    simpa only [measureReal_def,Measure.map_apply hX measurableSet_Ici,preimage_setOf_eq] using hm.2
  have hstrict : μ.real {ω | m < X ω} ≤ (1/2 : ℝ) := by
    simpa only [measureReal_def,Measure.map_apply hX measurableSet_Ioi,preimage_setOf_eq] using hm.1
  have hcompl : {ω | m < X ω}ᶜ = {ω | X ω ≤ m} := by ext ω; simp
  have hsum := measureReal_add_measureReal_compl (μ := μ) (hX (measurableSet_Ioi (a := m)))
  change μ.real {ω | m < X ω}+μ.real {ω | m < X ω}ᶜ = μ.real univ at hsum
  rw [hcompl,measureReal_univ_eq_one] at hsum
  exact ⟨by linarith,hhi⟩

theorem exists_realMedian {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) :
    ∃ m : ℝ, IsRealMedian X μ m := by
  letI : IsProbabilityMeasure (Measure.map X μ) := isProbabilityMeasure_map hX.aemeasurable
  obtain ⟨m,hm⟩ := tailQuantile_fiber_nonempty (Measure.map X μ)
    (by norm_num : (1/2 : ℝ) ∈ Ioo (0 : ℝ) 1)
  exact ⟨m,isRealMedian_of_tailQuantile_half hX hm⟩

theorem median_difference_zero_of_copy_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X X' : Ω → ℝ}
    (hX : Measurable X) (hX' : Measurable X')
    (hi : IndepFun X X' μ) (he : IdentDistrib X X' μ μ)
    {m : ℝ} (hm : IsRealMedian X μ m)
    (hz : (fun ω => |X ω-X' ω|) =ᵐ[μ] (fun _ => 0)) :
    (fun ω => |X ω-m|) =ᵐ[μ] (fun _ => 0) := by
  have hsets : ∀ᵐ ω ∂μ, ω ∈ {ω | 0 < |X ω-X' ω|} ↔ ω ∈ (∅ : Set Ω) := by
    filter_upwards [hz] with ω hω
    change |X ω-X' ω| = 0 at hω
    simp only [mem_setOf_eq,hω,lt_self_iff_false,mem_empty_iff_false]
  have hmeasure : μ {ω | 0 < |X ω-X' ω|} = 0 := by
    calc
      μ {ω | 0 < |X ω-X' ω|} = μ (∅ : Set Ω) := measure_congr (hsets.mono (fun _ h => propext h))
      _ = 0 := measure_empty
  have hreal : μ.real {ω | 0 < |X ω-X' ω|} = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top μ _)).mpr hmeasure
  have htail := median_independent_copy_tail hX hX' hi he hm (le_refl (0 : ℝ))
  rw [hreal,mul_zero] at htail
  have hnonpos : ∀ᵐ ω ∂μ, |X ω-m| ≤ 0 :=
    ae_nonpositive_of_unit_interval_zero_tail_bounds (fun p hp => htail.trans hp.1.le)
  filter_upwards [hnonpos] with ω hω
  exact le_antisymm hω (abs_nonneg _)

section
variable {n : ℕ} (hn : 0 < n) {Ω E F : Type*} [MeasurableSpace Ω]
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
    {Φ : E → F} (hΦ : Measurable Φ)
    (hmod : ∀ x y, dist (Φ x) (Φ y) ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
include hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0 hqdom hq0 hQ hsδ hsq hP hΦ hmod

theorem randomized_lipschitz_median_geometric_bound {g : F → ℝ} (hg : LipschitzWith 1 g)
    {m : ℝ} (hm : IsRealMedian (fun ω => g (Φ (Z ω))) μ m)
    (hnδ : ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0)
    (hnq : ∀ i, ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0) :
    let P := randomizedInputProduct qΔ q hδdom hδ0 hqdom hq0
    DecLE (tailQuantile (Measure.map (fun ω => |g (Φ (Z ω))-m|) μ))
      (completedDecreasingRestriction (Ioo (0 : ℝ) 1)
        (positiveInputDilation (1/6) (geometricHardyTransform 1 P))) := by
  let P := randomizedInputProduct qΔ q hδdom hδ0 hqdom hq0
  have hProp := randomizedInputProduct_properties hδdom hδ0 hqdom hq0 hsδ hsq
  have hGP := geometricHardyTransform_well_defined_any_selection (q := P) (by norm_num) hProp.1 hProp.2.1 hProp.2.2 hP
  let G : DecGraph := ⟨geometricHardyTransform 1 P,hGP.1⟩
  have hcomp := randomized_lipschitz_geometric_bound hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0
    hqdom hq0 hQ hnδ hnq hsδ hsq hP hΦ hmod hg
  have hhm : Measurable (fun x => g (Φ x)) := hg.continuous.measurable.comp hΦ
  have hV := hhm.comp hZ
  have hV' := hhm.comp hZ'
  have htail : ∀ t : ℝ, 0 ≤ t → μ.real {ω | t < |g (Φ (Z ω))-m|} ≤
      2*μ.real {ω | t < |g (Φ (Z ω))-g (Φ (Z' ω))|} :=
    fun _ ht => median_independent_copy_tail hV hV' (hindep.comp hhm hhm) (hident.comp hhm) hm ht
  have hb := quantile_tail_multiplier_dilation ((hV.sub hV').abs) ((hV.sub_const m).abs)
    (q := G) hGP.2.1 hGP.2.2.1 (by norm_num : (1/3 : ℝ) ∈ Ioc (0 : ℝ) 1)
    (by norm_num : (1 : ℝ) ≤ 2) hcomp htail
  simpa only [show (1/3 : ℝ)/2 = 1/6 by norm_num] using hb

theorem randomized_lipschitz_median_moment_bound {g : F → ℝ} (hg : LipschitzWith 1 g)
    {m : ℝ} (hm : IsRealMedian (fun ω => g (Φ (Z ω))) μ m) {r : ℝ} (hr : 0 < r)
    (hY : MemLp (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform) :
    MemLp (fun ω => |g (Φ (Z ω))-m|) (ENNReal.ofReal r) μ ∧
      eLpNorm (fun ω => |g (Φ (Z ω))-m|) (ENNReal.ofReal r) μ ≤
        ENNReal.ofReal ((6*Real.exp 1)^(1/r))*
          eLpNorm (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform := by
  classical
  let σ := fun p => sqΔ p*(∏ i, sq i p)
  let Y := fun ω => |g (Φ (Z ω))-m|
  have hhm : Measurable (fun x => g (Φ x)) := hg.continuous.measurable.comp hΦ
  have hV := hhm.comp hZ
  have hV' := hhm.comp hZ'
  have hYm : Measurable Y := (hV.sub_const m).abs
  have hY0 : 0 ≤ᵐ[μ] Y := Eventually.of_forall (fun _ => abs_nonneg _)
  let P := randomizedInputProduct qΔ q hδdom hδ0 hqdom hq0
  have hProp := randomizedInputProduct_properties hδdom hδ0 hqdom hq0 hsδ hsq
  have hσ0 : 0 ≤ᵐ[unitUniform] σ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
    exact hProp.2.1 p hp (σ p) (hProp.2.2 p hp)
  by_cases hz : (∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0) ∨
      ∃ i, ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0
  · have hzero := randomized_lipschitz_zero_input hZ hZ' hident hδ
      (fun p hp => interior_subset (show p ∈ interior (dom qΔ.val) from by rwa [hδdom]))
      hΛm hΛ0 (fun i p hp => interior_subset (show p ∈ interior (dom (q i).val) from by rwa [hqdom i]))
      hQ hmod hz hg
    have hcenter := median_difference_zero_of_copy_zero hV hV' (hindep.comp hhm hhm) (hident.comp hhm) hm hzero
    have hNorm0 : eLpNorm Y (ENNReal.ofReal r) μ = 0 := by
      calc
        _ = eLpNorm (fun _ : Ω => (0 : ℝ)) (ENNReal.ofReal r) μ := eLpNorm_congr_ae hcenter
        _ = 0 := eLpNorm_zero'
    refine ⟨⟨hYm.aestronglyMeasurable,?_⟩,?_⟩
    · rw [hNorm0]; exact ENNReal.zero_lt_top
    · rw [hNorm0]; exact zero_le _
  · have hnδ : ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0 := fun h => hz (Or.inl h)
    have hnq : ∀ i, ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0 := fun i h => hz (Or.inr ⟨i,h⟩)
    have hBound := randomized_lipschitz_median_geometric_bound hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0
      hqdom hq0 hQ hsδ hsq hP hΦ hmod hg hm hnδ hnq
    have hMoment := geometric_quantile_moment_bound μ hYm hY0 (q := P) hProp.1 hProp.2.1 hProp.2.2
      hP (by norm_num : (1/6 : ℝ) ∈ Ioc (0 : ℝ) 1) hr hBound
    have hCeq : Real.exp 1/(1/6 : ℝ) = 6*Real.exp 1 := by ring
    rw [hCeq] at hMoment
    have hC : 0 ≤ 6*Real.exp 1 := by positivity
    refine ⟨memLp_of_nonnegative_moment_bound hYm hY0 hσ0 hr hC hMoment hY,?_⟩
    simpa only [one_div] using eLpNorm_le_of_nonnegative_moment_bound hY0 hσ0 hr hC hMoment

theorem randomized_lipschitz_value_memLp {g : F → ℝ} (hg : LipschitzWith 1 g)
    {r : ℝ} (hr : 0 < r)
    (hY : MemLp (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform) :
    MemLp (fun ω => g (Φ (Z ω))) (ENNReal.ofReal r) μ := by
  have hV : Measurable (fun ω => g (Φ (Z ω))) := (hg.continuous.measurable.comp hΦ).comp hZ
  obtain ⟨m,hm⟩ := exists_realMedian (μ := μ) hV
  obtain ⟨hMem,_⟩ := randomized_lipschitz_median_moment_bound hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0
    hqdom hq0 hQ hsδ hsq hP hΦ hmod hg hm hr hY
  have hSigned : MemLp (fun ω => g (Φ (Z ω))-m) (ENNReal.ofReal r) μ :=
    hMem.congr_norm (hV.sub_const m).aestronglyMeasurable
      (Eventually.of_forall (fun _ => by simp only [Real.norm_eq_abs,abs_abs]))
  have he : ((fun ω => g (Φ (Z ω))-m)+(fun _ => m) : Ω → ℝ) = (fun ω => g (Φ (Z ω))) := by
    funext ω
    exact sub_add_cancel _ _
  rw [← he]
  exact hSigned.add (memLp_const m)

end
end ScalarMonotone.EndOfPaper
end
