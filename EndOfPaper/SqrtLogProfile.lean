import EndOfPaper.SqrtLogHardy
import EndOfPaper.AffinePowerProfile

/-!
Actual completed square-root logarithmic profiles and their integrability.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

def sqrtLogScalar (x : ℝ) : ℝ := Real.sqrt (Real.log 2-Real.log x)

theorem sqrt_log_scalar_antitone : AntitoneOn sqrtLogScalar (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  exact Real.sqrt_le_sqrt (sub_le_sub_left (Real.log_le_log hx.1 hxy) _)

theorem sqrt_log_scalar_integrable : IntegrableOn sqrtLogScalar (Ioo (0 : ℝ) 1) volume :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    (sqrt_log_hardy_prefix zero_lt_one le_rfl).1

theorem positive_log_area_of_nonnegative_integrable {f : ℝ → ℝ} (hm : Measurable f)
    (h0 : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ f x) (hi : IntegrableOn f (Ioo (0 : ℝ) 1) volume) :
    (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (f x)) 0)) < ∞ := by
  have hi' : IntegrableOn (fun x => max (Real.log (f x)) 0) (Ioo (0 : ℝ) 1) volume := by
    apply hi.mono' ((hm.log.max measurable_const).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
    exact max_le (Real.log_le_self (h0 x hx)) (h0 x hx)
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun x => le_max_right (Real.log (f x)) 0))).mp
    hi'.hasFiniteIntegral

def affineSqrtLogProfile (m c : ℝ) (hc : 0 ≤ c) : DecGraph :=
  ⟨completedDecreasingRestriction (Ioo (0 : ℝ) 1) (ofFun (fun x => m+c*sqrtLogScalar x)),
    (antitone_scalar_completion_properties isOpen_Ioo ordConnected_Ioo
      (nonempty_Ioo.mpr zero_lt_one) (fun x hx y hy hxy =>
        add_le_add_left (mul_le_mul_of_nonneg_left (sqrt_log_scalar_antitone hx hy hxy) hc) m)).1⟩

theorem affine_sqrt_log_profile_properties {m c : ℝ} (hm : 0 ≤ m) (hc : 0 ≤ c) :
    let P := affineSqrtLogProfile m c hc
    interior (dom P.val) = Ioo (0 : ℝ) 1 ∧
    (∀ u ∈ Ioo (0 : ℝ) 1, P.val u = {m+c*sqrtLogScalar u}) ∧
    ∀ u ∈ Ioo (0 : ℝ) 1, ∀ v ∈ P.val u, 0 ≤ v := by
  dsimp only
  have hR := antitone_scalar_completion_properties isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.mpr zero_lt_one) (fun x hx y hy hxy =>
      add_le_add_left (mul_le_mul_of_nonneg_left (sqrt_log_scalar_antitone hx hy hxy) hc) m)
  have hcont : ContinuousOn (fun x => m+c*sqrtLogScalar x) (Ioo (0 : ℝ) 1) :=
    continuousOn_const.add (continuousOn_const.mul
      ((continuousOn_const.sub (continuousOn_id.log (fun x hx => hx.1.ne'))).sqrt))
  have hval (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
      (affineSqrtLogProfile m c hc).val u = {m+c*sqrtLogScalar u} :=
    fiber_of_continuous_selection (Or.inr (affineSqrtLogProfile m c hc).property) isOpen_Ioo
      (fun x hx => ⟨_,hR.2.2.2 x hx⟩) hR.2.2.2 hcont hu
  refine ⟨hR.2.1,hval,?_⟩
  intro u hu v hv
  rw [hval u hu] at hv
  rw [mem_singleton_iff.mp hv]
  exact add_nonneg hm (mul_nonneg hc (Real.sqrt_nonneg _))

theorem affine_sqrt_log_integrable (m c : ℝ) :
    IntegrableOn (fun x => m+c*sqrtLogScalar x) (Ioo (0 : ℝ) 1) volume :=
  (integrableOn_const.mpr (Or.inr (by simp))).add (sqrt_log_scalar_integrable.const_mul c)

theorem affine_sqrt_log_positive_log_area {m c : ℝ} (hm : 0 ≤ m) (hc : 0 ≤ c) :
    (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (m+c*sqrtLogScalar x)) 0)) < ∞ := by
  apply positive_log_area_of_nonnegative_integrable
  · unfold sqrtLogScalar
    fun_prop
  · exact fun x _ => add_nonneg hm (mul_nonneg hc (Real.sqrt_nonneg _))
  · exact affine_sqrt_log_integrable m c

end ScalarMonotone.EndOfPaper
end
