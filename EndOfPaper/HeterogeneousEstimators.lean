import EndOfPaper.MedianHardy
import EndOfPaper.HardyDomination
import EndOfPaper.EstimatorScalar

/-!
Original-space median and normalized-sum estimation-error Hardy
bounds with arbitrary dependence. The concrete positive finite-mean
construction derives L1, preserves every input permutation and
has a fixed median bound and unbounded normalized-sum bound.
-/

open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem heterogeneous_estimators_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → (Fin 3 → ℝ)}
    (hm : Measurable X) (hi : ∀ i, Integrable (fun ω => X ω i) μ) (θ : ℝ)
    {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∃ a : Fin 3 → ℝ, ∃ m v : ℝ, 0 ≤ a ∧
      (∀ i, quantileHardy (Measure.map (fun ω => |X ω i-θ|) μ) p = {a i}) ∧
      quantileHardy (Measure.map (fun ω => |scalarMedian 1 (X ω)-θ|) μ) p = {m} ∧
      quantileHardy (Measure.map (fun ω => |meanThree (X ω)-θ|) μ) p = {v} ∧
      m ≤ min (a (Tuple.sort a 0)+a (Tuple.sort a 1)) ((∑ i, a i)/2) ∧
      v ≤ (∑ i, a i)/3 := by
  let E : Ω → (Fin 3 → ℝ) := fun ω i => |X ω i-θ|
  have hEm : Measurable E := measurable_pi_iff.mpr
    (fun i => ((measurable_pi_iff.mp hm i).sub measurable_const).abs)
  have hEi (i) : Integrable (fun ω => E ω i) μ := ((hi i).sub (integrable_const θ)).abs
  have hEn (ω) (i) : 0 ≤ E ω i := abs_nonneg _
  let ZMed : Ω → ℝ := fun ω => scalarMedian 1 (E ω)
  let YMed : Ω → ℝ := fun ω => |scalarMedian 1 (X ω)-θ|
  have hZMm : Measurable ZMed := (scalarMedian_continuous 1).measurable.comp hEm
  have hZMi : Integrable ZMed μ := aggregation_composition_integrable
    (median_aggregation_axioms 1) (scalarMedian_continuous 1).continuousOn μ hEm hEn hEi
  have hYMm : Measurable YMed :=
    (((scalarMedian_continuous 1).measurable.comp hm).sub measurable_const).abs
  have hdomM (ω) : YMed ω ≤ ZMed ω := median_error_domination 1 (X ω) θ
  have hYMi : Integrable YMed μ := hZMi.mono' hYMm.aestronglyMeasurable
    (Eventually.of_forall (fun ω => by simpa only [YMed, Real.norm_eq_abs, abs_abs] using hdomM ω))
  obtain ⟨a, b, ha, hMarg, hMed, hCut⟩ := hardy_tail_median_bound 1 μ hEm
    (Eventually.of_forall hEn) hEi hp
  obtain ⟨m, b', hmval, hbval, hmb⟩ :=
    quantileHardy_mono_values μ hYMm hZMm hYMi hZMi (Eventually.of_forall hdomM) hp
  have hbb : b' = b := Set.singleton_injective (hbval.symm.trans hMed)
  rw [hbb] at hmb
  have heCut : medianCutBound 1 a =
      min (a (Tuple.sort a 0)+a (Tuple.sort a 1)) ((∑ i, a i)/2) :=
    (median_transform_cut_formula 1 a ha).symm.trans (median_three_sharp_formula a ha)
  rw [heCut] at hCut
  let ZAvg : Ω → ℝ := fun ω => meanThree (E ω)
  let YAvg : Ω → ℝ := fun ω => |meanThree (X ω)-θ|
  have hZAm : Measurable ZAvg := meanThree_continuous.measurable.comp hEm
  have hZAi : Integrable ZAvg μ := aggregation_composition_integrable
    meanThree_aggregation_axioms meanThree_continuous.continuousOn μ hEm hEn hEi
  have hYAm : Measurable YAvg := ((meanThree_continuous.measurable.comp hm).sub measurable_const).abs
  have hdomA (ω) : YAvg ω ≤ ZAvg ω := meanThree_error_domination (X ω) θ
  have hYAi : Integrable YAvg μ := hZAi.mono' hYAm.aestronglyMeasurable
    (Eventually.of_forall (fun ω => by simpa only [YAvg, Real.norm_eq_abs, abs_abs] using hdomA ω))
  obtain ⟨a', c, ha', hMarg', hAvg, hMean⟩ := hardy_tail_aggregation_ae
    meanThree_aggregation_axioms meanThree_continuous.continuousOn μ hEm
    (Eventually.of_forall hEn) hEi hp
  have haa : a' = a := funext (fun i => Set.singleton_injective ((hMarg' i).symm.trans (hMarg i)))
  rw [haa, meanThree_sharp_transform ha] at hMean
  obtain ⟨v, c', hvval, hcval, hvc⟩ :=
    quantileHardy_mono_values μ hYAm hZAm hYAi hZAi (Eventually.of_forall hdomA) hp
  have hcc : c' = c := Set.singleton_injective (hcval.symm.trans hAvg)
  rw [hcc] at hvc
  exact ⟨a, m, v, ha, hMarg, hmval, hvval, hmb.trans hCut, hvc.trans hMean⟩

/-- The manuscript's positive finite nonnegative expectation supplies L1;
integrability is derived before any Hardy or expected-shortfall formula. -/
theorem integrable_positive_mean_of_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {Z : Ω → ℝ} (hm : Measurable Z) (hn : ∀ᵐ ω ∂μ, 0 ≤ Z ω)
    (hpos : 0 < ∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ)
    (hfin : (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ) < ∞) :
    Integrable Z μ ∧ 0 < ∫ ω, Z ω ∂μ := by
  refine ⟨⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hn).mpr hfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hn hm.aestronglyMeasurable]
  exact ENNReal.toReal_pos hpos.ne' hfin.ne

theorem normalized_sum_scale_unbounded {h : ℝ} (hh : 0 < h) (M : ℝ) :
    ∃ b : ℝ, 6 < b ∧ M < (b+3)/3*h := by
  let b := max 7 (3*M/h)+1
  have hb : 6 < b := by dsimp [b]; linarith [le_max_left (7 : ℝ) (3*M/h)]
  have he : 3*M/h < b := by dsimp [b]; linarith [le_max_right (7 : ℝ) (3*M/h)]
  have hp : 3*M < b*h := (div_lt_iff₀ hh).mp he
  have hM : M < b*h/3 := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
    (by simpa only [mul_comm] using hp)
  have hE : b*h/3+h = (b+3)/3*h := by ring
  exact ⟨b, hb, hM.trans ((lt_add_of_pos_right _ hh).trans_eq hE)⟩

/-- One fixed positive Hardy mean h works for every b>6. The construction
derives estimator L1, all marginal means and the actual errors, also after
every permutation. Its normalized-sum error is unbounded while the median
error stays 2h. The input mean hypotheses are genuinely extended-valued. -/
theorem heterogeneous_estimators_concrete {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hm : Measurable Z) (hn : ∀ᵐ ω ∂μ, 0 ≤ Z ω)
    (hpos : 0 < ∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ)
    (hfin : (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ) < ∞)
    (θ : ℝ) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∃ h : ℝ, 0 < h ∧ quantileHardy (Measure.map Z μ) p = {h} ∧
      (∀ b : ℝ, 6 < b →
        let X : Ω → (Fin 3 → ℝ) := fun ω => ![θ+Z ω, θ+2*Z ω, θ+b*Z ω]
        let a : Fin 3 → ℝ := ![h, 2*h, b*h]
        (∀ i, Measurable (fun ω => X ω i) ∧ Integrable (fun ω => X ω i) μ ∧
          quantileHardy (Measure.map (fun ω => |X ω i-θ|) μ) p = {a i}) ∧
        (∀ σ : Equiv.Perm (Fin 3),
          quantileHardy (Measure.map (fun ω => |scalarMedian 1 (fun i => X ω (σ i))-θ|) μ) p = {2*h} ∧
          quantileHardy (Measure.map (fun ω => |meanThree (fun i => X ω (σ i))-θ|) μ) p = {(b+3)/3*h}) ∧
        superadditiveTransform (scalarMedian 1) a = 3*h ∧
        meanThree a = (b+3)/3*h ∧ 3*h < (b+3)/3*h) ∧
      (∀ M : ℝ, ∃ b : ℝ, 6 < b ∧ M < (b+3)/3*h) := by
  obtain ⟨hZi, hmean⟩ := integrable_positive_mean_of_lintegral μ hm hn hpos hfin
  obtain ⟨h, hh, _, _, _, _, _⟩ := hardy_quantile_original_variational hm hZi hp
  have hhpos : 0 < h := hmean.trans_le (quantileHardy_mean_le μ hm hZi hp hh)
  refine ⟨h, hhpos, hh, ?_, normalized_sum_scale_unbounded hhpos⟩
  intro b hb
  have hb0 : 0 ≤ b := by linarith
  let X : Ω → (Fin 3 → ℝ) := fun ω => ![θ+Z ω, θ+2*Z ω, θ+b*Z ω]
  let a : Fin 3 → ℝ := ![h, 2*h, b*h]
  let c : Fin 3 → ℝ := ![1, 2, b]
  have hc (i) : 0 ≤ c i := by fin_cases i <;> simp [c] <;> linarith
  have hca (i) : a i = c i*h := by fin_cases i <;> simp [a, c]
  have hform (ω) (i) : X ω i-θ = c i*Z ω := by fin_cases i <;> simp [X, c] <;> ring
  have hXm (i) : Measurable (fun ω => X ω i) := by
    fin_cases i
    · exact measurable_const.add hm
    · exact measurable_const.add (measurable_const.mul hm)
    · exact measurable_const.add (measurable_const.mul hm)
  have hXi (i) : Integrable (fun ω => X ω i) μ := by
    fin_cases i
    · exact (integrable_const θ).add hZi
    · exact (integrable_const θ).add (hZi.const_mul 2)
    · exact (integrable_const θ).add (hZi.const_mul b)
  have hLaw (i) : Measure.map (fun ω => |X ω i-θ|) μ = Measure.map (fun ω => c i*Z ω) μ := by
    apply Measure.map_congr
    filter_upwards [hn] with ω hω
    rw [hform, abs_of_nonneg (mul_nonneg (hc i) hω)]
  have hMarg (i) : quantileHardy (Measure.map (fun ω => |X ω i-θ|) μ) p = {a i} := by
    rw [hLaw, hca]
    exact quantileHardy_smul_value μ hm hZi (hc i) hp hh
  have hMedLaw : Measure.map (fun ω => |scalarMedian 1 (X ω)-θ|) μ =
      Measure.map (fun ω => 2*Z ω) μ := by
    apply Measure.map_congr
    filter_upwards [hn] with ω hω
    have he : scalarMedian 1 (X ω) = θ+2*Z ω := median_three_scaled_exact hω (by linarith)
    rw [he, show θ+2*Z ω-θ = 2*Z ω from by ring,
      abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hω)]
  have hAvgLaw : Measure.map (fun ω => |meanThree (X ω)-θ|) μ =
      Measure.map (fun ω => (b+3)/3*Z ω) μ := by
    apply Measure.map_congr
    filter_upwards [hn] with ω hω
    have he : meanThree (X ω) = θ+(b+3)/3*Z ω := meanThree_scaled_exact _ _ _
    rw [he, show θ+(b+3)/3*Z ω-θ = (b+3)/3*Z ω from by ring,
      abs_of_nonneg (mul_nonneg (by positivity) hω)]
  have hMed : quantileHardy (Measure.map (fun ω => |scalarMedian 1 (X ω)-θ|) μ) p = {2*h} := by
    rw [hMedLaw]
    exact quantileHardy_smul_value μ hm hZi (by norm_num) hp hh
  have hAvg : quantileHardy (Measure.map (fun ω => |meanThree (X ω)-θ|) μ) p = {(b+3)/3*h} := by
    rw [hAvgLaw]
    exact quantileHardy_smul_value μ hm hZi (by positivity) hp hh
  refine ⟨fun i => ⟨hXm i, hXi i, hMarg i⟩, ?_,
    median_three_scale_bound hhpos.le (by linarith), ?_, ?_⟩
  · intro σ
    have hpm : (fun ω => |scalarMedian 1 (fun i => X ω (σ i))-θ|) =
        (fun ω => |scalarMedian 1 (X ω)-θ|) :=
      funext (fun ω => congrArg (fun t => |t-θ|) (scalarMedian_perm 1 (X ω) σ))
    have hpa : (fun ω => |meanThree (fun i => X ω (σ i))-θ|) =
        (fun ω => |meanThree (X ω)-θ|) :=
      funext (fun ω => congrArg (fun t => |t-θ|) (meanThree_perm (X ω) σ))
    rw [hpm, hpa]
    exact ⟨hMed, hAvg⟩
  · simpa only [zero_add] using meanThree_scaled_exact h b 0
  · have ht : 0 < (b-6)*h := mul_pos (by linarith) hhpos
    nlinarith

end ScalarMonotone.EndOfPaper
end
