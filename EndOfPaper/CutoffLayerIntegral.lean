import EndOfPaper.Shortfall
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Exact cutoff layer integration and averaging on an arbitrary
original probability space. The resulting correction is the sum of
the two means divided by s; all integrability is derived or explicit.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem cutoff_interval_volume {s u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    volume {r : ℝ | r ∈ Ioo (0 : ℝ) s ∧ u ≤ r ∧ v ≤ s-r} =
      ENNReal.ofReal (max (s-u-v) 0) := by
  let A := Icc u (s-v)
  have hsub : A ⊆ Icc (0 : ℝ) s := by
    intro r hr
    exact ⟨hu.trans hr.1,hr.2.trans (sub_le_self s hv)⟩
  have hset : {r : ℝ | r ∈ Ioo (0 : ℝ) s ∧ u ≤ r ∧ v ≤ s-r} = A ∩ Ioo (0 : ℝ) s := by
    ext r
    constructor
    · rintro ⟨hr,hur,hvr⟩
      exact ⟨⟨hur,by linarith⟩,hr⟩
    · rintro ⟨hr,hrI⟩
      exact ⟨hrI,hr.1,by linarith [hr.2]⟩
  have hrest : (volume : Measure ℝ).restrict (Ioo (0 : ℝ) s) = volume.restrict (Icc (0 : ℝ) s) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc
  calc
    _ = (volume.restrict (Ioo (0 : ℝ) s)) A := by
      rw [Measure.restrict_apply (show MeasurableSet A from measurableSet_Icc),hset]
    _ = volume A := by
      rw [hrest,Measure.restrict_apply (show MeasurableSet A from measurableSet_Icc),inter_eq_left.mpr hsub]
    _ = ENNReal.ofReal ((s-v)-u) := by simp only [A,Real.volume_Icc]
    _ = _ := by
      rw [show (s-v)-u = s-u-v by ring]
      by_cases h : 0 ≤ s-u-v
      · rw [max_eq_left h]
      · rw [max_eq_right (le_of_not_ge h),ENNReal.ofReal_zero,
          ENNReal.ofReal_eq_zero.mpr (le_of_not_ge h)]

theorem cutoff_weighted_tail_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {D : Set Ω} (hD : MeasurableSet D)
    {u v : Ω → ℝ} (hu : ∀ ω, 0 ≤ u ω) (hv : ∀ ω, 0 ≤ v ω)
    (hui : Integrable u μ) (hvi : Integrable v μ) {s a : ℝ} (hs : 0 < s)
    (hweighted : (∫ ω, D.indicator (fun ω => max (s-u ω-v ω) 0) ω ∂μ) ≤ a*s) :
    μ.real D ≤ a+((∫ ω, u ω ∂μ)+(∫ ω, v ω ∂μ))/s := by
  classical
  have hWi : Integrable (fun ω => max (s-u ω-v ω) 0) μ :=
    (((integrable_const s).sub hui).sub hvi).pos_part
  have hWD := hWi.indicator hD
  have hconst : Integrable (D.indicator (fun _ : Ω => s)) μ := (integrable_const s).indicator hD
  have hpoint (ω : Ω) : D.indicator (fun _ : Ω => s) ω ≤
      D.indicator (fun ω => max (s-u ω-v ω) 0) ω+u ω+v ω := by
    by_cases hω : ω ∈ D
    · simp only [indicator_of_mem hω]
      linarith [le_max_left (s-u ω-v ω) 0]
    · simp only [indicator_of_not_mem hω,zero_add]
      exact add_nonneg (hu ω) (hv ω)
  have hbound := integral_mono_ae hconst ((hWD.add hui).add hvi) (Eventually.of_forall hpoint)
  have hsum : (∫ ω, D.indicator (fun ω => max (s-u ω-v ω) 0) ω+u ω+v ω ∂μ) =
      (∫ ω, D.indicator (fun ω => max (s-u ω-v ω) 0) ω ∂μ)+(∫ ω, u ω ∂μ)+(∫ ω, v ω ∂μ) := by
    calc
      _ = (∫ ω, D.indicator (fun ω => max (s-u ω-v ω) 0) ω+u ω ∂μ)+(∫ ω, v ω ∂μ) :=
        integral_add (hWD.add hui) hvi
      _ = _ := congrArg (fun z => z+(∫ ω, v ω ∂μ)) (integral_add hWD hui)
  rw [integral_indicator_const s hD,smul_eq_mul] at hbound
  change μ.real D*s ≤ ∫ ω, D.indicator (fun ω => max (s-u ω-v ω) 0) ω+u ω+v ω ∂μ at hbound
  rw [hsum] at hbound
  have hscaled : μ.real D*s ≤ a*s+(∫ ω, u ω ∂μ)+(∫ ω, v ω ∂μ) := by
    linarith
  calc
    μ.real D ≤ (a*s+(∫ ω, u ω ∂μ)+(∫ ω, v ω ∂μ))/s := (le_div_iff₀ hs).mpr hscaled
    _ = _ := by
      field_simp [hs.ne']
      <;> ring

theorem cutoff_layer_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {D : Set Ω} (hD : MeasurableSet D)
    {u v : Ω → ℝ} (hmu : Measurable u) (hmv : Measurable v)
    (hu : ∀ ω, 0 ≤ u ω) (hv : ∀ ω, 0 ≤ v ω) (s : ℝ) :
    IntegrableOn (fun r : ℝ => μ.real {ω | ω ∈ D ∧ u ω ≤ r ∧ v ω ≤ s-r}) (Ioo (0 : ℝ) s) volume ∧
      (∫ r in Ioo (0 : ℝ) s, μ.real {ω | ω ∈ D ∧ u ω ≤ r ∧ v ω ≤ s-r}) =
        ∫ ω, D.indicator (fun ω => max (s-u ω-v ω) 0) ω ∂μ := by
  classical
  let ρ := volume.restrict (Ioo (0 : ℝ) s)
  letI : IsFiniteMeasure ρ := by
    apply isFiniteMeasure_restrict.mpr
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  let F : ℝ × Ω → ℝ := fun z =>
    if z.2 ∈ D ∧ u z.2 ≤ z.1 ∧ v z.2 ≤ s-z.1 then 1 else 0
  have hcond : MeasurableSet {z : ℝ × Ω | z.2 ∈ D ∧ u z.2 ≤ z.1 ∧ v z.2 ≤ s-z.1} :=
    (hD.preimage measurable_snd).inter
      ((measurableSet_le (hmu.comp measurable_snd) measurable_fst).inter
        (measurableSet_le (hmv.comp measurable_snd) (measurable_const.sub measurable_fst)))
  have hFm : Measurable F := by
    dsimp only [F]
    exact Measurable.ite hcond measurable_const measurable_const
  have hnorm (z : ℝ × Ω) : ‖F z‖ ≤ (1 : ℝ) := by
    dsimp only [F]
    split_ifs <;> norm_num
  have hFi : Integrable F (ρ.prod μ) :=
    (show Integrable (fun _ : ℝ × Ω => (1 : ℝ)) (ρ.prod μ) from integrable_const 1).mono'
      hFm.aestronglyMeasurable (Eventually.of_forall hnorm)
  have hinnerΩ (r : ℝ) : (∫ ω, F (r,ω) ∂μ) = μ.real {ω | ω ∈ D ∧ u ω ≤ r ∧ v ω ≤ s-r} := by
    have hset : MeasurableSet {ω | ω ∈ D ∧ u ω ≤ r ∧ v ω ≤ s-r} :=
      hD.inter ((measurableSet_le hmu measurable_const).inter (measurableSet_le hmv measurable_const))
    have he : (fun ω => F (r,ω)) =
        ({ω | ω ∈ D ∧ u ω ≤ r ∧ v ω ≤ s-r}).indicator (fun _ : Ω => (1 : ℝ)) := by
      funext ω
      simp only [F,indicator_apply,mem_setOf_eq]
    rw [he,integral_indicator_const 1 hset,smul_eq_mul,mul_one]
  have hinnerρ (ω : Ω) : (∫ r, F (r,ω) ∂ρ) = D.indicator (fun ω => max (s-u ω-v ω) 0) ω := by
    by_cases hω : ω ∈ D
    · rw [indicator_of_mem hω]
      let S : Set ℝ := {r | u ω ≤ r ∧ v ω ≤ s-r}
      have hS : MeasurableSet S :=
        (measurableSet_le measurable_const measurable_id).inter
          (measurableSet_le measurable_const (measurable_const.sub measurable_id))
      have he : (fun r => F (r,ω)) = S.indicator (fun _ : ℝ => (1 : ℝ)) := by
        funext r
        simp only [F,hω,true_and,indicator_apply,S,mem_setOf_eq]
      rw [he,integral_indicator_const 1 hS,smul_eq_mul,mul_one]
      have hset : S ∩ Ioo (0 : ℝ) s =
          {r : ℝ | r ∈ Ioo (0 : ℝ) s ∧ u ω ≤ r ∧ v ω ≤ s-r} := by
        ext r
        simp only [S,mem_inter_iff,mem_setOf_eq]
        tauto
      change ((volume.restrict (Ioo (0 : ℝ) s)) S).toReal = max (s-u ω-v ω) 0
      rw [Measure.restrict_apply hS,hset,cutoff_interval_volume (hu ω) (hv ω),
        ENNReal.toReal_ofReal (le_max_right _ _)]
    · simp only [F,hω,false_and,if_false,integral_zero,indicator_of_not_mem hω]
  refine ⟨hFi.integral_prod_left.congr (Eventually.of_forall hinnerΩ),?_⟩
  calc
    _ = ∫ r, ∫ ω, F (r,ω) ∂μ ∂ρ := integral_congr_ae (Eventually.of_forall (fun r => (hinnerΩ r).symm))
    _ = ∫ ω, ∫ r, F (r,ω) ∂ρ ∂μ := integral_integral_swap (f := fun r ω => F (r,ω)) hFi
    _ = _ := integral_congr_ae (Eventually.of_forall hinnerρ)

theorem cutoff_averaging_tail_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {D : Set Ω} (hD : MeasurableSet D)
    {u v : Ω → ℝ} (hmu : Measurable u) (hmv : Measurable v)
    (hu : ∀ ω, 0 ≤ u ω) (hv : ∀ ω, 0 ≤ v ω)
    (hui : Integrable u μ) (hvi : Integrable v μ) {s a : ℝ} (hs : 0 < s)
    (hcut : ∀ r ∈ Ioo (0 : ℝ) s, μ.real {ω | ω ∈ D ∧ u ω ≤ r ∧ v ω ≤ s-r} ≤ a) :
    μ.real D ≤ a+((∫ ω, u ω ∂μ)+(∫ ω, v ω ∂μ))/s := by
  have hLayer := cutoff_layer_integral (μ := μ) hD hmu hmv hu hv s
  have hci : IntegrableOn (fun _ : ℝ => a) (Ioo (0 : ℝ) s) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hs.le).mp intervalIntegrable_const
  have hle := integral_mono_ae hLayer.1 hci (show ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) s)),
      μ.real {ω | ω ∈ D ∧ u ω ≤ r ∧ v ω ≤ s-r} ≤ a from by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact hcut r hr)
  have hconst : (∫ _r in Ioo (0 : ℝ) s, a) = a*s := by
    rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hs.le,intervalIntegral.integral_const]
    simp only [sub_zero,smul_eq_mul,mul_comm]
  apply cutoff_weighted_tail_bound hD hu hv hui hvi hs
  rw [← hLayer.2]
  exact hle.trans_eq hconst

end ScalarMonotone.EndOfPaper
end
