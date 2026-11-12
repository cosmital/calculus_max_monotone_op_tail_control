import EndOfPaper.AggregationOperator
import EndOfPaper.HardyIntegral
import EndOfPaper.LocalHardy
import EndOfPaper.Profiles

/-!
The actual completed Hardy power and exponential profiles on (0,infinity),
with exact inverse graphs, maximality, domains and whole-operator
regularized identities. The Hardy tail transform uses the actual
dilation-family integral and is well defined under local prefix L1.
-/

open Set Filter MeasureTheory
open scoped Topology Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

def positiveScalarGraph (q : ℝ → ℝ) : Operator := by
  classical
  exact fun p => if 0 < p then {q p} else ∅

theorem positiveScalarGraph_domain (q : ℝ → ℝ) : dom (positiveScalarGraph q) = Ioi 0 := by
  ext p
  by_cases hp : 0 < p <;> simp [dom, positiveScalarGraph, hp]

/-- Unbounded upper values force the entire boundary fiber at zero to be
empty. Interior singleton equalities alone would not establish this result. -/
theorem positiveScalarGraph_maximal {q : ℝ → ℝ} (hq : AntitoneOn q (Ioi 0))
    (hc : ContinuousOn q (Ioi 0)) (hu : ∀ M : ℝ, ∃ p : ℝ, 0 < p ∧ M < q p) :
    MaximalDecreasing (positiveScalarGraph q) := by
  let C := intervalCompletionI (Ioi 0) (fun p => -q p) (fun p => -q p)
  have hC := intervalCompletionI_properties isOpen_Ioi ordConnected_Ioi
    (show (Ioi (0 : ℝ)).Nonempty from ⟨1, by norm_num⟩)
    (fun _ _ => le_rfl)
    (fun x hx y hy hxy => neg_le_neg (hq hx hy hxy.le)) (fun p hp => by
      have ht := (hc.continuousAt (isOpen_Ioi.mem_nhds hp)).neg.tendsto
      exact ⟨ht.mono_left nhdsWithin_le_nhds, ht.mono_left nhdsWithin_le_nhds⟩)
  have hmax : MaximalDecreasing (negOut C) := by
    change MaximalIncreasing (negOut (negOut C))
    simpa only [negOut_negOut] using hC.1
  have he : negOut C = positiveScalarGraph q := by
    ext p v
    by_cases hp : 0 < p
    · change -v ∈ C p ↔ v ∈ positiveScalarGraph q p
      rw [show C p = Icc (-q p) (-q p) from hC.2.2.2.1 p hp]
      simp only [positiveScalarGraph, if_pos hp, mem_Icc, mem_singleton_iff]
      constructor
      · intro h
        linarith [h.1, h.2]
      · intro h
        subst v
        exact ⟨le_rfl, le_rfl⟩
    · simp only [positiveScalarGraph, if_neg hp, mem_empty_iff_false, iff_false]
      intro hv
      have hv' : -v ∈ C p := hv
      have hp0 : 0 ≤ p := by
        have ht := hC.2.2.1 (show p ∈ dom C from ⟨-v, hv'⟩)
        simpa only [closure_Ioi, mem_Ici] using ht
      have hpe : p = 0 := le_antisymm (le_of_not_gt hp) hp0
      subst p
      obtain ⟨y, hy, hqv⟩ := hu v
      have hgy : -q y ∈ intervalGraphOn (Ioi 0) (fun p => -q p) (fun p => -q p) y := by
        simp [intervalGraphOn, hy]
      have hb := (compatible_iff_bounds.mp hv'.2).2 hgy hy
      linarith
  rwa [he] at hmax

theorem positiveScalarGraph_affine_maximal {q : ℝ → ℝ} (hq : AntitoneOn q (Ioi 0))
    (hc : ContinuousOn q (Ioi 0)) (hu : ∀ M : ℝ, ∃ p : ℝ, 0 < p ∧ M < q p)
    {c : ℝ} (hc0 : 0 < c) (b : ℝ) :
    MaximalDecreasing (positiveScalarGraph (fun p => c*q p+b)) := by
  apply positiveScalarGraph_maximal
  · intro x hx y hy hxy
    exact add_le_add_right (mul_le_mul_of_nonneg_left (hq hx hy hxy) hc0.le) b
  · exact fun p hp =>
      (continuousWithinAt_const.mul (hc p hp)).add continuousWithinAt_const
  · intro M
    obtain ⟨p, hp, hq⟩ := hu ((M-b)/c)
    refine ⟨p, hp, ?_⟩
    have ht := (div_lt_iff₀ hc0).mp hq
    nlinarith

def powerQuantileProfile (κ C : ℝ) : ℝ → ℝ := fun p => C^(1/κ)*p^((-1 : ℝ)/κ)
def exponentialQuantileProfile (C : ℝ) : ℝ → ℝ := fun p => Real.log C-Real.log p

theorem powerQuantileProfile_maximal {κ C : ℝ} (hκ : 0 < κ) (hC : 0 < C) :
    MaximalDecreasing (positiveScalarGraph (powerQuantileProfile κ C)) := by
  have hq : AntitoneOn (fun p : ℝ => p^((-1 : ℝ)/κ)) (Ioi 0) :=
    Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (div_nonpos_of_nonpos_of_nonneg (by norm_num) hκ.le)
  have hc : ContinuousOn (fun p : ℝ => p^((-1 : ℝ)/κ)) (Ioi 0) := fun p hp =>
    (Real.continuousAt_rpow_const p _ (Or.inl hp.ne')).continuousWithinAt
  have hu : ∀ M : ℝ, ∃ p : ℝ, 0 < p ∧ M < p^((-1 : ℝ)/κ) := by
    intro M
    let z : ℝ := max (M+1) 1
    have hz : 0 < z := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    refine ⟨z^(-κ), Real.rpow_pos_of_pos hz _, ?_⟩
    have he : (-κ)*((-1 : ℝ)/κ) = 1 := by field_simp [hκ.ne'] <;> ring
    rw [← Real.rpow_mul hz.le, he, Real.rpow_one]
    have hm : M+1 ≤ z := le_max_left _ _
    linarith
  simpa only [powerQuantileProfile, add_zero] using
    positiveScalarGraph_affine_maximal hq hc hu (Real.rpow_pos_of_pos hC (1/κ)) 0

theorem exponentialQuantileProfile_maximal (C : ℝ) :
    MaximalDecreasing (positiveScalarGraph (exponentialQuantileProfile C)) := by
  have hq : AntitoneOn (fun p : ℝ => -Real.log p) (Ioi 0) := by
    intro x hx y hy hxy
    exact neg_le_neg (Real.strictMonoOn_log.monotoneOn hx hy hxy)
  have hc : ContinuousOn (fun p : ℝ => -Real.log p) (Ioi 0) := fun p hp =>
    (Real.continuousAt_log hp.ne').neg.continuousWithinAt
  have hu : ∀ M : ℝ, ∃ p : ℝ, 0 < p ∧ M < -Real.log p := by
    intro M
    refine ⟨Real.exp (-(M+1)), Real.exp_pos _, ?_⟩
    rw [Real.log_exp]
    linarith
  simpa only [exponentialQuantileProfile, one_mul, sub_eq_add_neg, add_comm] using
    positiveScalarGraph_affine_maximal hq hc hu (by norm_num : (0 : ℝ) < 1) (Real.log C)

theorem positiveScalarGraph_mem (q : ℝ → ℝ) (p t : ℝ) :
    t ∈ positiveScalarGraph q p ↔ 0 < p ∧ t = q p := by
  by_cases hp : 0 < p <;> simp [positiveScalarGraph, hp]

def powerProfile (κ C : ℝ) : Operator := fun t => {p | 0 < t ∧ p = C*t^(-κ)}
def exponentialProfile (C : ℝ) : Operator := ofFun (fun t => C*Real.exp (-t))

theorem power_profile_level_iff {κ C p t : ℝ} (hκ : 0 < κ) (hC : 0 < C)
    (hp : 0 < p) (ht : 0 < t) :
    p = C*t^(-κ) ↔ t = powerQuantileProfile κ C p := by
  have hprod : 0 < C*t^(-κ) := mul_pos hC (Real.rpow_pos_of_pos ht _)
  have hq : 0 < powerQuantileProfile κ C p :=
    mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hp _)
  have hlogp : Real.log (C*t^(-κ)) = Real.log C-κ*Real.log t := by
    rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos ht _).ne', Real.log_rpow ht]
    ring
  have hlogq : Real.log (powerQuantileProfile κ C p) =
      (Real.log C-Real.log p)/κ := by
    rw [powerQuantileProfile, Real.log_mul (Real.rpow_pos_of_pos hC _).ne'
      (Real.rpow_pos_of_pos hp _).ne', Real.log_rpow hC, Real.log_rpow hp]
    ring
  constructor
  · intro he
    have he' := congrArg Real.log he
    rw [hlogp] at he'
    apply Real.log_injOn_pos ht hq
    rw [hlogq]
    apply (eq_div_iff hκ.ne').mpr
    nlinarith
  · intro he
    have he' := congrArg Real.log he
    rw [hlogq] at he'
    have he'' := (eq_div_iff hκ.ne').mp he'
    apply Real.log_injOn_pos hp hprod
    rw [hlogp]
    nlinarith

theorem inverse_powerProfile {κ C : ℝ} (hκ : 0 < κ) (hC : 0 < C) :
    inverse (powerProfile κ C) = positiveScalarGraph (powerQuantileProfile κ C) := by
  ext p t
  change (0 < t ∧ p = C*t^(-κ)) ↔ _
  rw [positiveScalarGraph_mem]
  constructor
  · rintro ⟨ht, he⟩
    have hp : 0 < p := he ▸ mul_pos hC (Real.rpow_pos_of_pos ht _)
    exact ⟨hp, (power_profile_level_iff hκ hC hp ht).mp he⟩
  · rintro ⟨hp, he⟩
    have ht : 0 < t := he ▸
      mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hp _)
    exact ⟨ht, (power_profile_level_iff hκ hC hp ht).mpr he⟩

theorem inverse_exponentialProfile {C : ℝ} (hC : 0 < C) :
    inverse (exponentialProfile C) = positiveScalarGraph (exponentialQuantileProfile C) := by
  ext p t
  change p = C*Real.exp (-t) ↔ _
  rw [positiveScalarGraph_mem]
  constructor
  · intro he
    have hp : 0 < p := he ▸ mul_pos hC (Real.exp_pos _)
    have he' := congrArg Real.log he
    rw [Real.log_mul hC.ne' (Real.exp_ne_zero _), Real.log_exp] at he'
    exact ⟨hp, by dsimp [exponentialQuantileProfile]; linarith⟩
  · rintro ⟨hp, he⟩
    apply Real.log_injOn_pos hp (mul_pos hC (Real.exp_pos _))
    rw [Real.log_mul hC.ne' (Real.exp_ne_zero _), Real.log_exp]
    dsimp [exponentialQuantileProfile] at he
    linarith

theorem powerProfile_maximal {κ C : ℝ} (hκ : 0 < κ) (hC : 0 < C) :
    MaximalDecreasing (powerProfile κ C) := by
  have h := inverse_maximal_decreasing (powerQuantileProfile_maximal hκ hC)
  rwa [← inverse_powerProfile hκ hC, inverse_inverse] at h

theorem exponentialProfile_maximal {C : ℝ} (hC : 0 < C) :
    MaximalDecreasing (exponentialProfile C) := by
  have h := inverse_maximal_decreasing (exponentialQuantileProfile_maximal C)
  rwa [← inverse_exponentialProfile hC, inverse_inverse] at h


theorem positiveScalarGraph_hardy_unique {q : ℝ → ℝ}
    (hq : MaximalDecreasing (positiveScalarGraph q))
    (hi : ∀ p > 0, IntervalIntegrable q volume 0 p)
    {v : ℝ → ℝ} (hv : MaximalDecreasing (positiveScalarGraph v))
    (he : ∀ p > 0, v p = hardyScalar q p) :
    hardyFamilyIntegral (Ioi 0) (positiveScalarGraph q) = positiveScalarGraph v := by
  have h := hardyFamilyIntegral_well_defined hq isOpen_Ioi ordConnected_Ioi
    (show (Ioi (0 : ℝ)).Nonempty from ⟨1, by norm_num⟩)
    (by rw [positiveScalarGraph_domain, interior_Ioi]) (fun _ hp => hp)
    (fun c hc p hp => mul_pos hc.1 hp)
    (show SelectionOn (positiveScalarGraph q) (Ioi 0) q from
      fun p hp => (positiveScalarGraph_mem q p (q p)).mpr ⟨hp, rfl⟩) hi
  apply Eq.symm
  apply h.2.2.2.2 _ hv
  · rw [positiveScalarGraph_domain]
    exact subset_closure
  · intro p hp
    simp only [positiveScalarGraph, if_pos (show 0 < p from hp), he p hp]

theorem hardy_powerProfile_whole {κ C : ℝ} (hκ : 1 < κ) (hC : 0 < C) :
    hardyFamilyIntegral (Ioi 0) (inverse (powerProfile κ C)) =
      inverse (powerProfile κ (C*(κ/(κ-1))^κ)) := by
  have hk0 : 0 < κ := lt_trans zero_lt_one hκ
  have hK : 0 < κ/(κ-1) := div_pos hk0 (sub_pos.mpr hκ)
  have hC' : 0 < C*(κ/(κ-1))^κ := mul_pos hC (Real.rpow_pos_of_pos hK _)
  rw [inverse_powerProfile hk0 hC, inverse_powerProfile hk0 hC']
  apply positiveScalarGraph_hardy_unique (powerQuantileProfile_maximal hk0 hC)
  · intro p _
    exact (power_quantile_intervalIntegrable hκ).const_mul _
  · exact powerQuantileProfile_maximal hk0 hC'
  · intro p hp
    unfold powerQuantileProfile
    rw [hardyScalar_scaled_power_profile hκ hp]
    change (C*(κ/(κ-1))^κ)^(1/κ)*p^((-1 : ℝ)/κ) = _
    rw [Real.mul_rpow hC.le (Real.rpow_pos_of_pos hK _).le,
      ← Real.rpow_mul hK.le]
    have he : κ*(1/κ) = 1 := by field_simp [hk0.ne']
    rw [he, Real.rpow_one]

theorem hardy_exponentialProfile_whole {C : ℝ} (hC : 0 < C) :
    hardyFamilyIntegral (Ioi 0) (inverse (exponentialProfile C)) =
      inverse (exponentialProfile (C*Real.exp 1)) := by
  have hC' : 0 < C*Real.exp 1 := mul_pos hC (Real.exp_pos _)
  rw [inverse_exponentialProfile hC, inverse_exponentialProfile hC']
  apply positiveScalarGraph_hardy_unique (exponentialQuantileProfile_maximal C)
  · intro p _
    exact intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_log'
  · exact exponentialQuantileProfile_maximal _
  · intro p hp
    unfold exponentialQuantileProfile
    rw [hardyScalar_scaled_exponential_profile hp]
    change Real.log (C*Real.exp 1)-Real.log p = _
    rw [Real.log_mul hC.ne' (Real.exp_ne_zero _), Real.log_exp]
    ring

def hardyTailTransform (β : Operator) : Operator :=
  inverse (hardyFamilyIntegral (interior (dom (inverse β))) (inverse β))

theorem hardyTailTransform_well_defined {β : Operator} (hβ : MaximalDecreasing β)
    (hz : IsGLB (dom (inverse β)) 0) (hp : ∃ p ∈ dom (inverse β), 0 < p)
    {s : ℝ → ℝ} (hs : SelectionOn (inverse β) (interior (dom (inverse β))) s)
    (hi : ∀ p ∈ interior (dom (inverse β)), IntervalIntegrable s volume 0 p) :
    MaximalDecreasing (hardyTailTransform β) ∧
      inverse (hardyTailTransform β) =
        hardyFamilyIntegral (interior (dom (inverse β))) (inverse β) ∧
      interior (ran (hardyTailTransform β)) = interior (ran β) := by
  have h := hardyFamilyIntegral_of_locally_integrable
    (inverse_maximal_decreasing hβ) hz hp hs hi
  refine ⟨inverse_maximal_decreasing h.1, inverse_inverse _, ?_⟩
  simpa only [hardyTailTransform, ran_inverse, dom_inverse] using h.2.1

theorem hardyTailTransform_power {κ C : ℝ} (hκ : 1 < κ) (hC : 0 < C) :
    hardyTailTransform (powerProfile κ C) = powerProfile κ (C*(κ/(κ-1))^κ) := by
  unfold hardyTailTransform
  have hk0 := lt_trans zero_lt_one hκ
  rw [inverse_powerProfile hk0 hC, positiveScalarGraph_domain, interior_Ioi,
    ← inverse_powerProfile hk0 hC, hardy_powerProfile_whole hκ hC, inverse_inverse]

theorem hardyTailTransform_exponential {C : ℝ} (hC : 0 < C) :
    hardyTailTransform (exponentialProfile C) = exponentialProfile (C*Real.exp 1) := by
  unfold hardyTailTransform
  rw [inverse_exponentialProfile hC, positiveScalarGraph_domain, interior_Ioi,
    ← inverse_exponentialProfile hC, hardy_exponentialProfile_whole hC, inverse_inverse]

theorem powerProfile_outputScale (κ c C : ℝ) :
    outputScale c (powerProfile κ C) = powerProfile κ (c*C) := by
  ext t p
  constructor
  · rintro ⟨v, ⟨ht, rfl⟩, rfl⟩
    exact ⟨ht, by ring⟩
  · rintro ⟨ht, he⟩
    exact ⟨C*t^(-κ), ⟨ht, rfl⟩, by rw [he]; ring⟩

theorem exponentialProfile_outputScale (c C : ℝ) :
    outputScale c (exponentialProfile C) = exponentialProfile (c*C) := by
  ext t p
  constructor
  · rintro ⟨v, hv, rfl⟩
    change v = C*Real.exp (-t) at hv
    change c*v = (c*C)*Real.exp (-t)
    rw [hv]
    ring
  · intro he
    change p = (c*C)*Real.exp (-t) at he
    exact ⟨C*Real.exp (-t), rfl, by rw [he]; ring⟩

theorem hardy_regularized_profiles {κ C : ℝ} (hκ : 1 < κ) (hC : 0 < C) :
    hardyTailTransform (outputScale C (powerProfile κ 1)) =
      outputScale (C*(κ/(κ-1))^κ) (powerProfile κ 1) ∧
    hardyTailTransform (outputScale C (exponentialProfile 1)) =
      outputScale (C*Real.exp 1) (exponentialProfile 1) := by
  simp only [powerProfile_outputScale, exponentialProfile_outputScale, mul_one]
  exact ⟨hardyTailTransform_power hκ hC, hardyTailTransform_exponential hC⟩

theorem hardy_profile_identities {κ p : ℝ} (hκ : 1 < κ) (hp : 0 < p) :
    MaximalDecreasing (powerProfile κ 1) ∧ MaximalDecreasing (exponentialProfile 1) ∧
      interior (dom (inverse (powerProfile κ 1))) = Ioi 0 ∧
      interior (dom (inverse (exponentialProfile 1))) = Ioi 0 ∧
      hardyFamilyIntegral (Ioi 0) (inverse (powerProfile κ 1)) p =
        {(κ/(κ-1))*p^((-1 : ℝ)/κ)} ∧
      hardyFamilyIntegral (Ioi 0) (inverse (exponentialProfile 1)) p = {1-Real.log p} := by
  have hk0 : 0 < κ := lt_trans zero_lt_one hκ
  have hK : 0 < κ/(κ-1) := div_pos hk0 (sub_pos.mpr hκ)
  have hC' : 0 < (1 : ℝ)*(κ/(κ-1))^κ := by positivity
  refine ⟨powerProfile_maximal hk0 (by norm_num), exponentialProfile_maximal (by norm_num),
    ?_, ?_, ?_, ?_⟩
  · rw [inverse_powerProfile hk0 (by norm_num), positiveScalarGraph_domain, interior_Ioi]
  · rw [inverse_exponentialProfile (by norm_num), positiveScalarGraph_domain, interior_Ioi]
  · rw [hardy_powerProfile_whole hκ (by norm_num), inverse_powerProfile hk0 hC']
    simp only [positiveScalarGraph, if_pos hp, powerQuantileProfile, one_mul]
    rw [← Real.rpow_mul hK.le, show κ*(1/κ) = 1 by field_simp [hk0.ne'], Real.rpow_one]
  · rw [hardy_exponentialProfile_whole (by norm_num),
      inverse_exponentialProfile (show 0 < (1 : ℝ)*Real.exp 1 by positivity)]
    simp only [positiveScalarGraph, if_pos hp, exponentialQuantileProfile, one_mul, Real.log_exp]

end ScalarMonotone.EndOfPaper
end
