import EndOfPaper.RandomizedUnequalBound
import EndOfPaper.RandomizedMedianMoment
import EndOfPaper.IndependentMeanJensen

/-!
The complete original centering remark: the sharper whole
median graph at probability u/6, both zero-input cases, every
r>0 median norm bound and the original mean-centered norm chain
with integrability derived for r>=1.
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
    {sqΔ : ℝ → ℝ} (hsδ : SelectionOn qΔ.val (Ioo (0 : ℝ) 1) sqΔ)
    {sq : Fin n → ℝ → ℝ} (hsq : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) 1) (sq i))
    (hP : (∫⁻ p in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (max (Real.log (sqΔ p*(∏ i, sq i p))) 0)) < ∞)
    {Φ : E → F} (hΦ : Measurable Φ)
    (hmod : ∀ x y, dist (Φ x) (Φ y) ≤ dist x y*(∏ i, max (Λ i x) (Λ i y)))
include hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0 hqdom hq0 hQ hsδ hsq hP hΦ hmod

theorem randomized_lipschitz_median_sharper_bound {g : F → ℝ} (hg : LipschitzWith 1 g)
    {m : ℝ} (hm : IsRealMedian (fun ω => g (Φ (Z ω))) μ m)
    (hnδ : ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0)
    (hnq : ∀ i, ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0) :
    let hPi := (randomized_individual_log_areas hδ0 hq0 hnδ hnq hsδ hsq hP).2
    let G := geometricFiniteProfileProduct q hqdom hq0 hsq hPi
    let hG := geometricFiniteProfileProduct_properties hqdom hq0 hsq hPi
    DecLE (tailQuantile (Measure.map (fun ω => |g (Φ (Z ω))-m|) μ))
      (completedDecreasingRestriction (Ioo (0 : ℝ) 1)
        (positiveInputDilation (1/6)
          (completedProfileProduct 1 qΔ G (by norm_num) hδdom hG.1 hδ0 hG.2.1).val)) := by
  let hPi := (randomized_individual_log_areas hδ0 hq0 hnδ hnq hsδ hsq hP).2
  let G := geometricFiniteProfileProduct q hqdom hq0 hsq hPi
  have hG := geometricFiniteProfileProduct_properties hqdom hq0 hsq hPi
  let P := completedProfileProduct 1 qΔ G (by norm_num) hδdom hG.1 hδ0 hG.2.1
  have hPD := (completedProfileProduct_domain (by norm_num) hδdom hG.1 hδ0 hG.2.1).1
  have hP0 := completedProfileProduct_nonnegative (by norm_num) hδdom hG.1 hδ0 hG.2.1
  have hcomp := randomized_lipschitz_sharper_bound hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0
    hqdom hq0 hQ hnδ hnq hsδ hsq hP hΦ hmod hg
  have hhm : Measurable (fun x => g (Φ x)) := hg.continuous.measurable.comp hΦ
  have hV := hhm.comp hZ
  have hV' := hhm.comp hZ'
  have htail : ∀ t : ℝ, 0 ≤ t → μ.real {ω | t < |g (Φ (Z ω))-m|} ≤
      2*μ.real {ω | t < |g (Φ (Z ω))-g (Φ (Z' ω))|} :=
    fun _ ht => median_independent_copy_tail hV hV' (hindep.comp hhm hhm) (hident.comp hhm) hm ht
  have hb := quantile_tail_multiplier_dilation ((hV.sub hV').abs) ((hV.sub_const m).abs)
    (q := P) hPD hP0 (by norm_num : (1/3 : ℝ) ∈ Ioc (0 : ℝ) 1)
    (by norm_num : (1 : ℝ) ≤ 2) hcomp htail
  simpa only [show (1/3 : ℝ)/2 = 1/6 by norm_num] using hb

theorem randomized_lipschitz_mean_moment_bound {g : F → ℝ} (hg : LipschitzWith 1 g)
    {r : ℝ} (hr : 1 ≤ r)
    (hY : MemLp (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform) :
    Integrable (fun ω => g (Φ (Z ω))) μ ∧
      MemLp (fun ω => g (Φ (Z ω))-∫ ω', g (Φ (Z ω')) ∂μ) (ENNReal.ofReal r) μ ∧
      eLpNorm (fun ω => g (Φ (Z ω))-∫ ω', g (Φ (Z ω')) ∂μ) (ENNReal.ofReal r) μ ≤
        eLpNorm (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) (ENNReal.ofReal r) μ ∧
      eLpNorm (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) (ENNReal.ofReal r) μ ≤
        ENNReal.ofReal ((3*Real.exp 1)^(1/r))*
          eLpNorm (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hValue := randomized_lipschitz_value_memLp hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0
    hqdom hq0 hQ hsδ hsq hP hΦ hmod hg hr0 hY
  obtain ⟨hGap,hBound⟩ := randomized_lipschitz_moment_bound hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0
    hqdom hq0 hQ hsδ hsq hP hΦ hmod hg hr0 hY
  have hhm : Measurable (fun x => g (Φ x)) := hg.continuous.measurable.comp hΦ
  have hMean := independent_copy_mean_norm (hhm.comp hZ) (hhm.comp hZ')
    (hindep.comp hhm hhm) (hident.comp hhm) hr hValue hGap
  have hp : 1 ≤ ENNReal.ofReal r := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr
  exact ⟨hValue.integrable hp,hMean.1,hMean.2,hBound⟩

theorem randomized_lipschitz_centering {g : F → ℝ} (hg : LipschitzWith 1 g) :
    (∀ (hnδ : ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0)
       (hnq : ∀ i, ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0)
       (m : ℝ), IsRealMedian (fun ω => g (Φ (Z ω))) μ m →
      let hPi := (randomized_individual_log_areas hδ0 hq0 hnδ hnq hsδ hsq hP).2
      let G := geometricFiniteProfileProduct q hqdom hq0 hsq hPi
      let hG := geometricFiniteProfileProduct_properties hqdom hq0 hsq hPi
      DecLE (tailQuantile (Measure.map (fun ω => |g (Φ (Z ω))-m|) μ))
        (completedDecreasingRestriction (Ioo (0 : ℝ) 1)
          (positiveInputDilation (1/6)
            (completedProfileProduct 1 qΔ G (by norm_num) hδdom hG.1 hδ0 hG.2.1).val))) ∧
    (∀ m : ℝ, IsRealMedian (fun ω => g (Φ (Z ω))) μ m →
      ((∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0) ∨
       ∃ i, ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0) →
      (fun ω => |g (Φ (Z ω))-m|) =ᵐ[μ] (fun _ => 0)) ∧
    (∀ m : ℝ, IsRealMedian (fun ω => g (Φ (Z ω))) μ m →
      ∀ r : ℝ, 0 < r → MemLp (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform →
      MemLp (fun ω => |g (Φ (Z ω))-m|) (ENNReal.ofReal r) μ ∧
        eLpNorm (fun ω => |g (Φ (Z ω))-m|) (ENNReal.ofReal r) μ ≤
          ENNReal.ofReal ((6*Real.exp 1)^(1/r))*
            eLpNorm (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform) ∧
    (∀ r : ℝ, 1 ≤ r → MemLp (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform →
      Integrable (fun ω => g (Φ (Z ω))) μ ∧
        MemLp (fun ω => g (Φ (Z ω))-∫ ω', g (Φ (Z ω')) ∂μ) (ENNReal.ofReal r) μ ∧
        eLpNorm (fun ω => g (Φ (Z ω))-∫ ω', g (Φ (Z ω')) ∂μ) (ENNReal.ofReal r) μ ≤
          eLpNorm (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) (ENNReal.ofReal r) μ ∧
        eLpNorm (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) (ENNReal.ofReal r) μ ≤
          ENNReal.ofReal ((3*Real.exp 1)^(1/r))*
            eLpNorm (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro hnδ hnq m hm
    exact randomized_lipschitz_median_sharper_bound hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0
      hqdom hq0 hQ hsδ hsq hP hΦ hmod hg hm hnδ hnq
  · intro m hm hz
    have hzero := randomized_lipschitz_zero_input hZ hZ' hident hδ
      (fun p hp => interior_subset (show p ∈ interior (dom qΔ.val) from by rwa [hδdom]))
      hΛm hΛ0 (fun i p hp => interior_subset (show p ∈ interior (dom (q i).val) from by rwa [hqdom i]))
      hQ hmod hz hg
    have hhm : Measurable (fun x => g (Φ x)) := hg.continuous.measurable.comp hΦ
    exact median_difference_zero_of_copy_zero (hhm.comp hZ) (hhm.comp hZ')
      (hindep.comp hhm hhm) (hident.comp hhm) hm hzero
  · intro m hm r hr hY
    exact randomized_lipschitz_median_moment_bound hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0
      hqdom hq0 hQ hsδ hsq hP hΦ hmod hg hm hr hY
  · intro r hr hY
    exact randomized_lipschitz_mean_moment_bound hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0
      hqdom hq0 hQ hsδ hsq hP hΦ hmod hg hr hY

theorem randomized_lipschitz_median_real_moment_bound {g : F → ℝ} (hg : LipschitzWith 1 g)
    {m : ℝ} (hm : IsRealMedian (fun ω => g (Φ (Z ω))) μ m) {r : ℝ} (hr : 0 < r)
    (hY : MemLp (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform) :
    MemLp (fun ω => |g (Φ (Z ω))-m|) (ENNReal.ofReal r) μ ∧
      (eLpNorm (fun ω => |g (Φ (Z ω))-m|) (ENNReal.ofReal r) μ).toReal ≤
        (6*Real.exp 1)^(1/r)*
          (eLpNorm (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform).toReal := by
  obtain ⟨hMem,hBound⟩ := randomized_lipschitz_median_moment_bound hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0
    hqdom hq0 hQ hsδ hsq hP hΦ hmod hg hm hr hY
  refine ⟨hMem,?_⟩
  have hFinite : ENNReal.ofReal ((6*Real.exp 1)^(1/r))*
      eLpNorm (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hY.eLpNorm_lt_top.ne
  have hReal := ENNReal.toReal_mono hFinite hBound
  have hConst : 0 ≤ (6*Real.exp 1)^(1/r) := by positivity
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hConst] using hReal

theorem randomized_lipschitz_mean_real_moment_bound {g : F → ℝ} (hg : LipschitzWith 1 g)
    {r : ℝ} (hr : 1 ≤ r)
    (hY : MemLp (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform) :
    Integrable (fun ω => g (Φ (Z ω))) μ ∧
      MemLp (fun ω => g (Φ (Z ω))-∫ ω', g (Φ (Z ω')) ∂μ) (ENNReal.ofReal r) μ ∧
      (eLpNorm (fun ω => g (Φ (Z ω))-∫ ω', g (Φ (Z ω')) ∂μ) (ENNReal.ofReal r) μ).toReal ≤
        (3*Real.exp 1)^(1/r)*
          (eLpNorm (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform).toReal := by
  obtain ⟨hI,hMem,hCompare,hBound⟩ := randomized_lipschitz_mean_moment_bound hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0
    hqdom hq0 hQ hsδ hsq hP hΦ hmod hg hr hY
  refine ⟨hI,hMem,?_⟩
  have hFinite : ENNReal.ofReal ((3*Real.exp 1)^(1/r))*
      eLpNorm (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hY.eLpNorm_lt_top.ne
  have hReal := ENNReal.toReal_mono hFinite (hCompare.trans hBound)
  have hConst : 0 ≤ (3*Real.exp 1)^(1/r) := by positivity
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hConst] using hReal

end
end ScalarMonotone.EndOfPaper
end
