import EndOfPaper.RandomizedGeometricBound
import EndOfPaper.ZeroRandomizedLipschitz
import EndOfPaper.GeometricMomentBound
import EndOfPaper.NonnegativeMomentNorm

/-!
The full original randomized Lipschitz theorem: the whole
completed graph comparison, both zero-profile cases and the actual
Lr and finite real-norm bounds for every real r>0.
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

theorem randomized_lipschitz_moment_bound {g : F → ℝ} (hg : LipschitzWith 1 g)
    {r : ℝ} (hr : 0 < r)
    (hY : MemLp (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform) :
    MemLp (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) (ENNReal.ofReal r) μ ∧
      eLpNorm (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) (ENNReal.ofReal r) μ ≤
        ENNReal.ofReal ((3*Real.exp 1)^(1/r))*
          eLpNorm (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform := by
  classical
  let σ := fun p => sqΔ p*(∏ i, sq i p)
  let X := fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|
  have hhm : Measurable (fun x => g (Φ x)) := hg.continuous.measurable.comp hΦ
  have hXm : Measurable X := ((hhm.comp hZ).sub (hhm.comp hZ')).abs
  have hX0 : 0 ≤ᵐ[μ] X := Eventually.of_forall (fun ω => abs_nonneg _)
  let P := randomizedInputProduct qΔ q hδdom hδ0 hqdom hq0
  have hProp := randomizedInputProduct_properties hδdom hδ0 hqdom hq0 hsδ hsq
  have hY0 : 0 ≤ᵐ[unitUniform] σ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
    exact hProp.2.1 p hp (σ p) (hProp.2.2 p hp)
  by_cases hz : (∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0) ∨
      ∃ i, ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0
  · have hzero := randomized_lipschitz_zero_input hZ hZ' hident hδ
      (fun p hp => interior_subset (show p ∈ interior (dom qΔ.val) from by rwa [hδdom]))
      hΛm hΛ0 (fun i p hp => interior_subset (show p ∈ interior (dom (q i).val) from by rwa [hqdom i]))
      hQ hmod hz hg
    have hNorm0 : eLpNorm X (ENNReal.ofReal r) μ = 0 := by
      calc
        _ = eLpNorm (fun _ : Ω => (0 : ℝ)) (ENNReal.ofReal r) μ := eLpNorm_congr_ae hzero
        _ = 0 := eLpNorm_zero'
    refine ⟨⟨hXm.aestronglyMeasurable,?_⟩,?_⟩
    · rw [hNorm0]
      exact ENNReal.zero_lt_top
    · rw [hNorm0]
      exact zero_le _
  · have hnδ : ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0 := fun h => hz (Or.inl h)
    have hnq : ∀ i, ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0 :=
      fun i h => hz (Or.inr ⟨i,h⟩)
    have hBound : DecLE (tailQuantile (Measure.map X μ))
        (completedDecreasingRestriction (Ioo (0 : ℝ) 1)
          (positiveInputDilation (1/3) (geometricHardyTransform 1 P))) :=
      randomized_lipschitz_geometric_bound hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0
        hqdom hq0 hQ hnδ hnq hsδ hsq hP hΦ hmod hg
    have hMoment := geometric_quantile_moment_bound μ hXm hX0 (q := P) hProp.1 hProp.2.1 hProp.2.2
      hP (by norm_num : (1/3 : ℝ) ∈ Ioc (0 : ℝ) 1) hr hBound
    have hCeq : Real.exp 1/(1/3 : ℝ) = 3*Real.exp 1 := by ring
    rw [hCeq] at hMoment
    have hC : 0 ≤ 3*Real.exp 1 := mul_nonneg (by norm_num) (Real.exp_pos 1).le
    refine ⟨memLp_of_nonnegative_moment_bound hXm hX0 hY0 hr hC hMoment hY,?_⟩
    simpa only [one_div] using eLpNorm_le_of_nonnegative_moment_bound hX0 hY0 hr hC hMoment

theorem randomized_lipschitz_real_moment_bound {g : F → ℝ} (hg : LipschitzWith 1 g)
    {r : ℝ} (hr : 0 < r)
    (hY : MemLp (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform) :
    MemLp (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) (ENNReal.ofReal r) μ ∧
      (eLpNorm (fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|) (ENNReal.ofReal r) μ).toReal ≤
        (3*Real.exp 1)^(1/r)*
          (eLpNorm (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform).toReal := by
  obtain ⟨hMem,hBound⟩ := randomized_lipschitz_moment_bound hn hZ hZ' hindep hident hδdom hδ0 hδ
    hΛm hΛ0 hqdom hq0 hQ hsδ hsq hP hΦ hmod hg hr hY
  refine ⟨hMem,?_⟩
  have hFinite : ENNReal.ofReal ((3*Real.exp 1)^(1/r))*
      eLpNorm (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hY.eLpNorm_lt_top.ne
  have hReal := ENNReal.toReal_mono hFinite hBound
  have hConst : 0 ≤ (3*Real.exp 1)^(1/r) := by positivity
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hConst] using hReal

theorem randomized_lipschitz_control {g : F → ℝ} (hg : LipschitzWith 1 g) :
    let P := randomizedInputProduct qΔ q hδdom hδ0 hqdom hq0
    let X := fun ω => |g (Φ (Z ω))-g (Φ (Z' ω))|
    ((¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0) ∧
        (∀ i, ¬ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0) →
      DecLE (tailQuantile (Measure.map X μ))
        (completedDecreasingRestriction (Ioo (0 : ℝ) 1)
          (positiveInputDilation (1/3) (geometricHardyTransform 1 P)))) ∧
    (((∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qΔ.val p, v = 0) ∨
        ∃ i, ∀ p ∈ Ioo (0 : ℝ) 1, ∀ v ∈ (q i).val p, v = 0) → X =ᵐ[μ] (fun _ => 0)) ∧
    (∀ r : ℝ, 0 < r → MemLp (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform →
      MemLp X (ENNReal.ofReal r) μ ∧ eLpNorm X (ENNReal.ofReal r) μ ≤
        ENNReal.ofReal ((3*Real.exp 1)^(1/r))*
          eLpNorm (fun p => sqΔ p*(∏ i, sq i p)) (ENNReal.ofReal r) unitUniform) := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · rintro ⟨hnδ,hnq⟩
    exact randomized_lipschitz_geometric_bound hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0
      hqdom hq0 hQ hnδ hnq hsδ hsq hP hΦ hmod hg
  · intro hz
    exact randomized_lipschitz_zero_input hZ hZ' hident hδ
      (fun p hp => interior_subset (show p ∈ interior (dom qΔ.val) from by rwa [hδdom]))
      hΛm hΛ0 (fun i p hp => interior_subset (show p ∈ interior (dom (q i).val) from by rwa [hqdom i]))
      hQ hmod hz hg
  · intro r hr hY
    exact randomized_lipschitz_moment_bound hn hZ hZ' hindep hident hδdom hδ0 hδ hΛm hΛ0
      hqdom hq0 hQ hsδ hsq hP hΦ hmod hg hr hY

end
end ScalarMonotone.EndOfPaper
end
