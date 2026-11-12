import EndOfPaper.RandomizedGeometricBound
import EndOfPaper.RandomizedProfileData
import EndOfPaper.UnequalProfileProduct
import EndOfPaper.OptimizedTailBudget

/-!
The sharper randomized whole graph bound and
optimized infimum over unequal probability levels. Arbitrary
selected jump values and equality in the probability budget are retained.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper
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
    (hnδ : ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0)
    (hnq : ∀ i, ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0)
    {sqΔ : ℝ → ℝ} (hsδ : SelectionOn qΔ.val (Ioo (0 : ℝ) 1) sqΔ)
    {sq : Fin n → ℝ → ℝ} (hsq : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) 1) (sq i))
    (hP : (∫⁻ p in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (max (Real.log (sqΔ p*(∏ i, sq i p))) 0)) < ∞)
    {Φ : E → F} (hΦ : Measurable Φ)
    (hmod : ∀ x y, dist (Φ x) (Φ y) ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))

include hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0 hqdom hq0 hQ hnδ hnq hsδ hsq hP hΦ hmod

theorem randomized_lipschitz_unequal_bound {g : F → ℝ} (hg : LipschitzWith 1 g)
    {α β : ℝ} (hα : α ∈ Ioc (0 : ℝ) 1) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hbudget : α+2*β ≤ 1) :
    let hPi := (randomized_individual_log_areas hδ0 hq0 hnδ hnq hsδ hsq hP).2
    let G := geometricFiniteProfileProduct q hqdom hq0 hsq hPi
    let hG := geometricFiniteProfileProduct_properties hqdom hq0 hsq hPi
    DecLE (tailQuantile (Measure.map (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) μ))
      (completedUnequalProfileProduct qΔ G hδdom hG.1 hδ0 hG.2.1 hα hβ).val := by
  classical
  dsimp only
  let hPi := (randomized_individual_log_areas hδ0 hq0 hnδ hnq hsδ hsq hP).2
  let G := geometricFiniteProfileProduct q hqdom hq0 hsq hPi
  have hG := geometricFiniteProfileProduct_properties hqdom hq0 hsq hPi
  let R := completedUnequalProfileProduct qΔ G hδdom hG.1 hδ0 hG.2.1 hα hβ
  have hR := completedUnequalProfileProduct_properties hδdom hG.1 hδ0 hG.2.1 hα hβ
  have hRS := completedUnequalProfileProduct_selection hδdom hG.1 hδ0 hG.2.1 hα hβ hsδ hG.2.2
  have hhm : Measurable (fun x => g (Φ x)) := hg.continuous.measurable.comp hΦ
  have hX : Measurable (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) :=
    ((hhm.comp hZ).sub (hhm.comp hZ')).abs
  have hscalar : ∀ x y, |g (Φ x)-g (Φ y)| ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)) := by
    intro x y
    exact (show |g (Φ x)-g (Φ y)| ≤ dist (Φ x) (Φ y) from by
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hg.dist_le_mul (Φ x) (Φ y)).trans (hmod x y)
  change DecLE (tailQuantile (Measure.map (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) μ)) R.val
  apply tailQuantile_decLE_of_profile_selection_tail_bounds hX R.property hR.1 hRS
  intro u hu
  have ha : α*u ∈ Ioo (0 : ℝ) 1 :=
    initial_dilation_mapsTo hα.1 (by simpa using hα.2) hu
  have hb : β*u ∈ Ioo (0 : ℝ) 1 :=
    initial_dilation_mapsTo hβ.1 (by simpa using hβ.2) hu
  have htwo := randomized_lipschitz_two_parameter hZ hZ' hindep hident qΔ.property hδdom hδ0 hδ
    hΛm hΛ0 (fun i => (q i).property) hqdom hq0 hQ hnδ hnq hsδ hsq hP hhm hscalar ha hb (hsδ _ ha)
  have htail : μ.real {ω | sqΔ (α*u)*(∏ i, geometricPrefixValue (sq i) (β*u)) <
      |g (Φ (Z ω))-g (Φ (Z' ω))|} ≤ α*u+2*(β*u) := by
    simpa only [mul_comm] using htwo
  have hbud : α*u+2*(β*u) ≤ u := by
    calc
      _ = (α+2*β)*u := by ring
      _ ≤ 1*u := mul_le_mul_of_nonneg_right hbudget hu.1.le
      _ = u := one_mul _
  exact htail.trans hbud

theorem randomized_lipschitz_optimized_at {g : F → ℝ} (hg : LipschitzWith 1 g)
    {p a b t : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (ha : 0 < a) (hb : 0 < b)
    (hbudget : a+2*b ≤ p) (ht : t ∈ qΔ.val a) :
    let hPi := (randomized_individual_log_areas hδ0 hq0 hnδ hnq hsδ hsq hP).2
    let G := geometricFiniteProfileProduct q hqdom hq0 hsq hPi
    ∀ v ∈ G.val b, sInf (tailQuantile (Measure.map (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) μ) p) ≤ t*v := by
  classical
  dsimp only
  let hPi := (randomized_individual_log_areas hδ0 hq0 hnδ hnq hsδ hsq hP).2
  let G := geometricFiniteProfileProduct q hqdom hq0 hsq hPi
  have hG := geometricFiniteProfileProduct_properties hqdom hq0 hsq hPi
  intro v hv
  have hα : a/p ∈ Ioc (0 : ℝ) 1 := ⟨div_pos ha hp.1,(div_le_one hp.1).mpr (by linarith)⟩
  have hβ : b/p ∈ Ioc (0 : ℝ) 1 := ⟨div_pos hb hp.1,(div_le_one hp.1).mpr (by linarith)⟩
  have hbud : a/p+2*(b/p) ≤ 1 := by
    calc
      _ = (a+2*b)/p := by ring
      _ ≤ 1 := (div_le_one hp.1).mpr hbudget
  let R := completedUnequalProfileProduct qΔ G hδdom hG.1 hδ0 hG.2.1 hα hβ
  have hRBound : DecLE (tailQuantile (Measure.map (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) μ)) R.val :=
    randomized_lipschitz_unequal_bound hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0
      hqdom hq0 hQ hnδ hnq hsδ hsq hP hΦ hmod hg hα hβ hbud
  have heA : (a/p)*p = a := div_mul_cancel₀ a hp.1.ne'
  have heB : (b/p)*p = b := div_mul_cancel₀ b hp.1.ne'
  have ht' : t ∈ qΔ.val ((a/p)*p) := by rwa [heA]
  have hv' : v ∈ G.val ((b/p)*p) := by rwa [heB]
  have hmem : t*v ∈ R.val p :=
    (completedUnequalProfileProduct_properties hδdom hG.1 hδ0 hG.2.1 hα hβ).2.2 p hp t ht' v hv'
  have hhm : Measurable (fun x => g (Φ x)) := hg.continuous.measurable.comp hΦ
  have hX : Measurable (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) :=
    ((hhm.comp hZ).sub (hhm.comp hZ')).abs
  letI : IsProbabilityMeasure (Measure.map (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) μ) :=
    isProbabilityMeasure_map hX.aemeasurable
  exact quantile_lower_endpoint_le_of_decLE _ R.property hRBound hp hmem

theorem randomized_lipschitz_two_parameter_geometric {g : F → ℝ} (hg : LipschitzWith 1 g)
    {a b t : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (ht : t ∈ qΔ.val a) :
    let hPi := (randomized_individual_log_areas hδ0 hq0 hnδ hnq hsδ hsq hP).2
    let G := geometricFiniteProfileProduct q hqdom hq0 hsq hPi
    ∀ v ∈ G.val b, μ.real {ω | t*v < |g (Φ (Z ω))-g (Φ (Z' ω))|} ≤ a+2*b := by
  classical
  dsimp only
  intro v hv
  by_cases hsmall : a+2*b < 1
  · have hp : a+2*b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ha.1,hb.1],hsmall⟩
    have hle := randomized_lipschitz_optimized_at hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0
      hqdom hq0 hQ hnδ hnq hsδ hsq hP hΦ hmod hg hp ha.1 hb.1 le_rfl ht v hv
    have hhm : Measurable (fun x => g (Φ x)) := hg.continuous.measurable.comp hΦ
    have hX : Measurable (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) :=
      ((hhm.comp hZ).sub (hhm.comp hZ')).abs
    letI : IsProbabilityMeasure (Measure.map (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) μ) :=
      isProbabilityMeasure_map hX.aemeasurable
    have hMin := quantile_lower_endpoint_isLeast
      (Measure.map (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) μ) hp
    have hbase : μ.real {ω | sInf (tailQuantile
        (Measure.map (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) μ) (a+2*b)) <
        |g (Φ (Z ω))-g (Φ (Z' ω))|} ≤ a+2*b := by
      simpa only [measureReal_def,Measure.map_apply hX measurableSet_Ioi,preimage_setOf_eq] using hMin.1.1
    exact (measureReal_mono (μ := μ) (fun ω hω => hle.trans_lt hω)).trans hbase
  · exact (measureReal_le_one (μ := μ)).trans (le_of_not_gt hsmall)

theorem randomized_lipschitz_optimized {g : F → ℝ} (hg : LipschitzWith 1 g)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    let hPi := (randomized_individual_log_areas hδ0 hq0 hnδ hnq hsδ hsq hP).2
    let G := geometricFiniteProfileProduct q hqdom hq0 hsq hPi
    ∀ γ : ℝ → ℝ, SelectionOn G.val (Ioo (0 : ℝ) 1) γ →
      sInf (tailQuantile (Measure.map (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) μ) p) ≤
        sInf (twoParameterThresholds (fun a b => sqΔ a*γ b) p) := by
  classical
  dsimp only
  intro γ hγ
  apply le_csInf (twoParameterThresholds_nonempty (fun a b => sqΔ a*γ b) hp.1)
  rintro t ⟨a,ha,b,hb,hbudget,rfl⟩
  have haI : a ∈ Ioo (0 : ℝ) 1 := ⟨ha,by linarith [hp.2]⟩
  have hbI : b ∈ Ioo (0 : ℝ) 1 := ⟨hb,by linarith [hp.2]⟩
  exact randomized_lipschitz_optimized_at hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0
    hqdom hq0 hQ hnδ hnq hsδ hsq hP hΦ hmod hg hp ha hb hbudget (hsδ a haI) (γ b) (hγ b hbI)

theorem randomized_lipschitz_sharper_bound {g : F → ℝ} (hg : LipschitzWith 1 g) :
    let hPi := (randomized_individual_log_areas hδ0 hq0 hnδ hnq hsδ hsq hP).2
    let G := geometricFiniteProfileProduct q hqdom hq0 hsq hPi
    let hG := geometricFiniteProfileProduct_properties hqdom hq0 hsq hPi
    DecLE (tailQuantile (Measure.map (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) μ))
      (completedDecreasingRestriction (Ioo (0 : ℝ) 1)
        (positiveInputDilation (1/3)
          (completedProfileProduct 1 qΔ G (by norm_num) hδdom hG.1 hδ0 hG.2.1).val)) := by
  dsimp only
  let hPi := (randomized_individual_log_areas hδ0 hq0 hnδ hnq hsδ hsq hP).2
  let G := geometricFiniteProfileProduct q hqdom hq0 hsq hPi
  have hG := geometricFiniteProfileProduct_properties hqdom hq0 hsq hPi
  have hc : (1/3 : ℝ) ∈ Ioc (0 : ℝ) 1 := by norm_num
  have he := completedUnequalProfileProduct_equal_dilation hδdom hG.1 hδ0 hG.2.1 hc hsδ hG.2.2
  rw [← he]
  exact randomized_lipschitz_unequal_bound hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0
    hqdom hq0 hQ hnδ hnq hsδ hsq hP hΦ hmod hg hc hc (by norm_num)

end
end ScalarMonotone.EndOfPaper
end
