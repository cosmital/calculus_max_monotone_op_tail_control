import EndOfPaper.QuantileDependenceCounterexample
import EndOfPaper.QuantileTailCompletion
import EndOfPaper.NonnegativeMomentNorm
import EndOfPaper.HalfMixtureCopyTail

/-!
The literal completed unit profile and actual Bernoulli model: exact moments, norms, baseline, marginals, modulus and logarithmic admissibility.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

def unitQuantileProfile : DecGraph := ⟨tailQuantile (Measure.dirac (1 : ℝ)),tailQuantile_maximal _⟩

theorem unitQuantileProfile_value {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    unitQuantileProfile.val p = {1} := tailQuantile_dirac_interior 1 hp

theorem unitQuantileProfile_domain : interior (dom unitQuantileProfile.val) = Ioo (0 : ℝ) 1 :=
  tailQuantile_domain_interior (Measure.dirac (1 : ℝ))

theorem unitQuantileProfile_one_mem {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    (1 : ℝ) ∈ unitQuantileProfile.val p := by
  rw [unitQuantileProfile_value hp]
  rfl

theorem symmetricBernoulli_ae_unit_interval : ∀ᵐ x ∂symmetricBernoulli, x ∈ Icc (0 : ℝ) 1 := by
  apply ae_iff.mpr
  norm_num [symmetricBernoulli,Measure.add_apply,Measure.smul_apply,Measure.dirac_apply,Set.indicator]

theorem symmetricBernoulli_copy_moment {r : ℝ} (hr : 0 < r) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (|z.1-z.2|^r) ∂(symmetricBernoulli.prod symmetricBernoulli)) =
      ENNReal.ofReal (1/2 : ℝ) := by
  have hDiff : Continuous (fun z : ℝ × ℝ => z.1-z.2) := continuous_fst.sub continuous_snd
  have hF : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (|z.1-z.2|^r)) :=
    ((Real.continuous_rpow_const hr.le).comp hDiff.abs).measurable.ennreal_ofReal
  rw [lintegral_prod _ hF.aemeasurable]
  simp_rw [symmetricBernoulli,lintegral_add_measure,lintegral_smul_measure,lintegral_dirac,smul_eq_mul]
  simp only [sub_self,zero_sub,sub_zero,abs_neg,abs_zero,abs_one,Real.zero_rpow hr.ne',
    Real.one_rpow,ENNReal.ofReal_zero,ENNReal.ofReal_one,mul_zero,zero_mul,mul_one,one_mul,zero_add,add_zero,one_div]
  have hHalf : ENNReal.ofReal ((2 : ℝ)⁻¹) = (2 : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hHalf,← add_mul,ENNReal.inv_two_add_inv_two,one_mul]

theorem symmetricBernoulli_copy_norm {r : ℝ} (hr : 0 < r) :
    eLpNorm (fun z : ℝ × ℝ => z.1-z.2) (ENNReal.ofReal r)
      (symmetricBernoulli.prod symmetricBernoulli) = ENNReal.ofReal ((2 : ℝ)^(-1/r)) := by
  have hNN : 0 ≤ᵐ[symmetricBernoulli.prod symmetricBernoulli] (fun z : ℝ × ℝ => |z.1-z.2|) :=
    Eventually.of_forall (fun z => abs_nonneg _)
  have he : eLpNorm (fun z : ℝ × ℝ => z.1-z.2) (ENNReal.ofReal r)
      (symmetricBernoulli.prod symmetricBernoulli) =
    eLpNorm (fun z : ℝ × ℝ => |z.1-z.2|) (ENNReal.ofReal r)
      (symmetricBernoulli.prod symmetricBernoulli) := by
    simpa only [Real.norm_eq_abs] using (eLpNorm_norm (p := ENNReal.ofReal r)
      (μ := symmetricBernoulli.prod symmetricBernoulli) (fun z : ℝ × ℝ => z.1-z.2)).symm
  rw [he,eLpNorm_nonnegative_eq_moment hNN hr,symmetricBernoulli_copy_moment hr,
    ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (inv_nonneg.mpr hr.le)]
  congr 1
  rw [one_div,Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2),← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

theorem bernoulli_unit_profile_baseline (f : ℝ → ℝ) (hf : LipschitzWith 1 f) :
    DecLE (tailQuantile (Measure.map (fun z : ℝ × ℝ => |f z.1-f z.2|)
      (symmetricBernoulli.prod symmetricBernoulli))) unitQuantileProfile.val := by
  have hset : MeasurableSet {z : ℝ × ℝ | z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc (0 : ℝ) 1} :=
    (measurable_fst measurableSet_Icc).inter (measurable_snd measurableSet_Icc)
  have hPair : ∀ᵐ z : ℝ × ℝ ∂(symmetricBernoulli.prod symmetricBernoulli),
      z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc (0 : ℝ) 1 :=
    (Measure.ae_prod_iff_ae_ae hset).mpr (symmetricBernoulli_ae_unit_interval.mono
      (fun x hx => symmetricBernoulli_ae_unit_interval.mono (fun y hy => ⟨hx,hy⟩)))
  have hGap : ∀ᵐ z : ℝ × ℝ ∂(symmetricBernoulli.prod symmetricBernoulli), |f z.1-f z.2| ≤ 1 := by
    filter_upwards [hPair] with z hz
    have hLip : |f z.1-f z.2| ≤ |z.1-z.2| := by
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hf.dist_le_mul z.1 z.2
    exact hLip.trans (abs_le.mpr ⟨by linarith [hz.1.1,hz.2.2],by linarith [hz.2.1,hz.1.2]⟩)
  have hfm := hf.continuous.measurable
  apply tailQuantile_decLE_of_profile_selection_tail_bounds
    ((hfm.comp measurable_fst).sub (hfm.comp measurable_snd)).abs
    unitQuantileProfile.property unitQuantileProfile_domain (fun p hp => unitQuantileProfile_one_mem hp)
  intro p hp
  have hNull : (symmetricBernoulli.prod symmetricBernoulli) {z : ℝ × ℝ | 1 < |f z.1-f z.2|} = 0 := by
    simpa only [not_le] using ae_iff.mp hGap
  change ((symmetricBernoulli.prod symmetricBernoulli) {z : ℝ × ℝ | 1 < |f z.1-f z.2|}).toReal ≤ p
  rw [hNull,ENNReal.toReal_zero]
  exact hp.1.le

theorem unit_profile_constant_control {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    DecLE (tailQuantile (Measure.map (fun _ : Ω => (1 : ℝ)) μ)) unitQuantileProfile.val := by
  apply tailQuantile_decLE_of_profile_selection_tail_bounds measurable_const
    unitQuantileProfile.property unitQuantileProfile_domain (fun p hp => unitQuantileProfile_one_mem hp)
  intro p hp
  simp only [lt_self_iff_false,setOf_false,measureReal_empty]
  exact hp.1.le

theorem bernoulli_unit_profile_modulus (n : ℕ) (x y : ℝ) :
    dist x y ≤ dist x y*(∏ _i : Fin n, max (1 : ℝ) 1) := by simp

theorem unit_profile_log_area (n : ℕ) :
    (∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log ((1 : ℝ)*(∏ _i : Fin n, (1 : ℝ)))) 0)) < ∞ := by
  simp

end ScalarMonotone.EndOfPaper
end
