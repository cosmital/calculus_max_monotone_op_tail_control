import EndOfPaper.ComonotoneQuantiles
import EndOfPaper.HardyVariational

/-!
Explicit finite-valued monotone step profiles with arbitrary positive
scales. Measurability, finite ranges, nonnegativity, integrability and
interval areas are proved before identifying the actual completed Hardy
quantile values. Prescribed marginal averages and each included-step lower
bound are derived; the full Hardy sharpness band argument remains separate.
-/

open Set Filter MeasureTheory
open scoped BigOperators Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

def hardyInitialStep (s c u : ℝ) : ℝ := (Iic s).indicator (fun _ => c) u

theorem hardyInitialStep_measurable (s c : ℝ) : Measurable (hardyInitialStep s c) :=
  measurable_const.indicator measurableSet_Iic

theorem hardyInitialStep_nonnegative {c : ℝ} (hc : 0 ≤ c) (s u : ℝ) :
    0 ≤ hardyInitialStep s c u := by
  by_cases h : u ≤ s <;> simp [hardyInitialStep, Set.indicator, h, hc]

theorem hardyInitialStep_antitone {c : ℝ} (hc : 0 ≤ c) (s : ℝ) :
    Antitone (hardyInitialStep s c) := by
  intro x y hxy
  by_cases hy : y ≤ s
  · have hx : x ≤ s := hxy.trans hy
    simp [hardyInitialStep, Set.indicator, hx, hy]
  · by_cases hx : x ≤ s <;> simp [hardyInitialStep, Set.indicator, hx, hy, hc]

theorem hardyInitialStep_integrable (s c : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (hardyInitialStep s c) μ :=
  (integrable_const c).indicator measurableSet_Iic

theorem hardyInitialStep_intervalIntegrable (s c a b : ℝ) :
    IntervalIntegrable (hardyInitialStep s c) volume a b := by
  have hi : Integrable (fun _ : ℝ => c) (volume.restrict (Ι a b)) :=
    intervalIntegrable_iff.mp intervalIntegrable_const
  exact intervalIntegrable_iff.mpr (hi.indicator measurableSet_Iic)

theorem hardyInitialStep_integral (c : ℝ) {s p : ℝ} (hs : s ∈ Icc (0 : ℝ) p) :
    (∫ u in (0 : ℝ)..p, hardyInitialStep s c u) = s*c := by
  unfold hardyInitialStep
  change (∫ u in (0 : ℝ)..p, ({x : ℝ | x ≤ s}).indicator (fun _ => c) u) = s*c
  rw [intervalIntegral.integral_indicator hs, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]

def finiteStepProfile {m : ℕ} (b : ℝ) (c s : Fin m → ℝ) (u : ℝ) : ℝ :=
  b+∑ j, hardyInitialStep (s j) (c j) u

theorem finiteStepProfile_measurable {m : ℕ} (b : ℝ) (c s : Fin m → ℝ) :
    Measurable (finiteStepProfile b c s) :=
  measurable_const.add (Finset.measurable_sum Finset.univ
    (fun j _ => hardyInitialStep_measurable (s j) (c j)))

theorem finiteStepProfile_antitone {m : ℕ} (b : ℝ) {c : Fin m → ℝ}
    (hc : ∀ j, 0 ≤ c j) (s : Fin m → ℝ) : Antitone (finiteStepProfile b c s) := by
  intro x y hxy
  exact add_le_add_left (Finset.sum_le_sum
    (fun j _ => hardyInitialStep_antitone (hc j) (s j) hxy)) b

theorem finiteStepProfile_nonnegative {m : ℕ} {b : ℝ} (hb : 0 ≤ b)
    {c : Fin m → ℝ} (hc : ∀ j, 0 ≤ c j) (s : Fin m → ℝ) (u : ℝ) :
    0 ≤ finiteStepProfile b c s u :=
  add_nonneg hb (Finset.sum_nonneg (fun j _ => hardyInitialStep_nonnegative (hc j) (s j) u))

theorem finiteStepProfile_finite_range {m : ℕ} (b : ℝ) (c s : Fin m → ℝ) :
    (Set.range (finiteStepProfile b c s)).Finite := by
  classical
  let r : (Fin m → Bool) → ℝ := fun w => b+∑ j, if w j then c j else 0
  apply (Set.finite_range r).subset
  rintro _ ⟨u, rfl⟩
  refine ⟨(fun j => decide (u ≤ s j)), ?_⟩
  change b+(∑ j, if decide (u ≤ s j) then c j else 0) =
    b+∑ j, hardyInitialStep (s j) (c j) u
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : u ≤ s j <;> simp [hardyInitialStep, Set.indicator, hj]

theorem finiteStepProfile_integrable {m : ℕ} (b : ℝ) (c s : Fin m → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] : Integrable (finiteStepProfile b c s) μ :=
  (integrable_const b).add (integrable_finset_sum _
    (fun j _ => hardyInitialStep_integrable (s j) (c j) μ))

theorem finiteStepProfile_intervalIntegrable {m : ℕ} (b : ℝ) (c s : Fin m → ℝ)
    (a p : ℝ) : IntervalIntegrable (finiteStepProfile b c s) volume a p := by
  have hs : IntervalIntegrable (fun u => ∑ j, hardyInitialStep (s j) (c j) u) volume a p := by
    simpa only [← Finset.sum_apply] using
      IntervalIntegrable.sum Finset.univ (fun j _ => hardyInitialStep_intervalIntegrable (s j) (c j) a p)
  exact intervalIntegrable_const.add hs

theorem finiteStepProfile_integral {m : ℕ} (b : ℝ) (c : Fin m → ℝ)
    {s : Fin m → ℝ} {p : ℝ} (hs : ∀ j, s j ∈ Icc (0 : ℝ) p) :
    (∫ u in (0 : ℝ)..p, finiteStepProfile b c s u) = p*b+∑ j, s j*c j := by
  have hsum : IntervalIntegrable (fun u => ∑ j, hardyInitialStep (s j) (c j) u) volume 0 p := by
    simpa only [← Finset.sum_apply] using
      IntervalIntegrable.sum Finset.univ (fun j _ => hardyInitialStep_intervalIntegrable (s j) (c j) 0 p)
  unfold finiteStepProfile
  rw [intervalIntegral.integral_add intervalIntegrable_const hsum,
    intervalIntegral.integral_const,
    intervalIntegral.integral_finset_sum (fun j _ => hardyInitialStep_intervalIntegrable (s j) (c j) 0 p)]
  simp only [sub_zero, smul_eq_mul, hardyInitialStep_integral _ (hs _)]

theorem finiteStepProfile_hardy_quantile {m : ℕ} (b : ℝ) {c : Fin m → ℝ}
    (hc : ∀ j, 0 ≤ c j) {s : Fin m → ℝ} {p : ℝ} (hp : p ∈ Ioo 0 1)
    (hs : ∀ j, s j ∈ Icc (0 : ℝ) p) :
    hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map (finiteStepProfile b c s) unitUniform))))
      (tailQuantile (Measure.map (finiteStepProfile b c s) unitUniform)) p =
      {(p*b+∑ j, s j*c j)/p} := by
  have hq := finiteStepProfile_measurable b c s
  letI : IsProbabilityMeasure (Measure.map (finiteStepProfile b c s) unitUniform) :=
    isProbabilityMeasure_map hq.aemeasurable
  have hi : Integrable (fun x : ℝ => x) (Measure.map (finiteStepProfile b c s) unitUniform) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hq.aemeasurable).mpr
      (finiteStepProfile_integrable b c s unitUniform)
  have hsel := antitone_uniform_quantile_selection
    (show AntitoneOn (finiteStepProfile b c s) (Ioo 0 1) from
      fun _ _ _ _ hxy => finiteStepProfile_antitone b hc s hxy)
  rw [hardy_tailQuantile_fiber _ hi hq hsel hp, hardyScalar, finiteStepProfile_integral b c hs]

theorem finiteStepProfile_dominates_step {m : ℕ} {b : ℝ} (hb : 0 ≤ b)
    {c : Fin m → ℝ} (hc : ∀ j, 0 ≤ c j) (s : Fin m → ℝ)
    {j : Fin m} {u : ℝ} (hu : u ≤ s j) : c j ≤ finiteStepProfile b c s u := by
  have ht := Finset.single_le_sum
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin m))) => hardyInitialStep_nonnegative (hc k) (s k) u)
    (Finset.mem_univ j)
  have he : hardyInitialStep (s j) (c j) u = c j := by
    simp [hardyInitialStep, Set.indicator, hu]
  rw [he] at ht
  change c j ≤ b+∑ k, hardyInitialStep (s k) (c k) u
  linarith

/-- The exact finite-valued comonotone building block. All shape conditions
and the actual completed Hardy quantile value are conclusions. -/
theorem finite_steps_prescribed_hardy {m : ℕ} {p a : ℝ} (hp : p ∈ Ioo 0 1)
    {v s : Fin m → ℝ} (hv : ∀ j, 0 ≤ v j) (hva : (∑ j, v j) ≤ a)
    (hs : ∀ j, 0 < s j ∧ s j ≤ p) :
    ∃ q : ℝ → ℝ, Measurable q ∧ Antitone q ∧ (Set.range q).Finite ∧
      (∀ u, 0 ≤ q u) ∧
      hardyFamilyIntegral (interior (dom (tailQuantile (Measure.map q unitUniform))))
        (tailQuantile (Measure.map q unitUniform)) p = {a} ∧
      ∀ j u, u ≤ s j → p*v j/s j ≤ q u := by
  let b : ℝ := a-∑ j, v j
  let c : Fin m → ℝ := fun j => p*v j/s j
  have hb : 0 ≤ b := sub_nonneg.mpr hva
  have hc (j) : 0 ≤ c j := div_nonneg (mul_nonneg hp.1.le (hv j)) (hs j).1.le
  refine ⟨finiteStepProfile b c s, finiteStepProfile_measurable b c s,
    finiteStepProfile_antitone b hc s, finiteStepProfile_finite_range b c s,
    finiteStepProfile_nonnegative hb hc s, ?_, ?_⟩
  · rw [finiteStepProfile_hardy_quantile b hc hp (fun j => ⟨(hs j).1.le, (hs j).2⟩)]
    have hsum : (∑ j, s j*c j) = p*∑ j, v j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [c]
      field_simp [(hs j).1.ne'] <;> ring
    rw [hsum]
    congr 1
    dsimp [b]
    field_simp [hp.1.ne'] <;> ring
  · exact fun j u hu => finiteStepProfile_dominates_step hb hc s hu

end ScalarMonotone.EndOfPaper
end
