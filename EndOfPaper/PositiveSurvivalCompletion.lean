import EndOfPaper.HardyIntegral
import EndOfPaper.QuantileMoments
import EndOfPaper.InverseArea

/-!
The actual positive-half-line survival completion: maximality, exact zero fiber, nonnegative range, whole quantile fibers on (0,1), and exact zero inverse above one.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

def positiveSurvivalCompletion (ν : Measure ℝ) : Operator :=
  completedDecreasingRestriction (Ioi 0) (survival ν)

theorem positive_survival_properties (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    MaximalDecreasing (positiveSurvivalCompletion ν) ∧
      interior (dom (positiveSurvivalCompletion ν)) = Ioi 0 ∧
      dom (positiveSurvivalCompletion ν) ⊆ Ici 0 ∧
      ∀ t > 0, positiveSurvivalCompletion ν t = survival ν t := by
  have hd : Ioi (0 : ℝ) ⊆ dom (survival ν) := fun t _ => ⟨_,survival_lower_mem ν t⟩
  have hne : (Ioi (0 : ℝ)).Nonempty := ⟨1,by norm_num⟩
  have hdom := completedDecreasingRestriction_domain (survival_maximal ν)
    isOpen_Ioi ordConnected_Ioi hne hd
  refine ⟨completedDecreasingRestriction_maximal (survival_maximal ν)
    ordConnected_Ioi hne hd,hdom.1,?_,?_⟩
  · simpa only [closure_Ioi] using hdom.2
  · intro t ht
    exact completedDecreasingRestriction_value (survival_maximal ν) isOpen_Ioi hd ht

theorem positive_survival_zero (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    positiveSurvivalCompletion ν 0 = Ici (ν.real (Ioi 0)) := by
  ext p
  change (0 ∈ closure (Ioi (0 : ℝ)) ∧
    Compatible (restrictOperator (negOut (survival ν)) (Ioi 0)) 0 (-p)) ↔ _
  constructor
  · intro hp
    apply le_of_tendsto (survival_strict_tail_right_continuous ν 0)
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hv : -ν.real (Ioi y) ∈ restrictOperator (negOut (survival ν)) (Ioi 0) y :=
      ⟨hy,by simpa only [negOut,mem_setOf_eq,neg_neg] using survival_lower_mem ν y⟩
    have h := (compatible_iff_bounds.mp hp.2).2 hv hy
    linarith
  · intro hp
    refine ⟨by simp only [closure_Ioi,mem_Ici,le_refl],compatible_iff_bounds.mpr ⟨?_,?_⟩⟩
    · rintro y v ⟨hy,_⟩ hy0
      exact False.elim ((not_lt_of_ge hy.le) hy0)
    · rintro y v ⟨hy,hv⟩ _
      change -v ∈ survival ν y at hv
      have hle : ν.real (Ici y) ≤ ν.real (Ioi 0) :=
        measureReal_mono (by
          intro x hx
          change 0 < x
          exact lt_of_lt_of_le hy hx)
      have hvp : -v ≤ p := hv.2.trans (hle.trans hp)
      linarith only [hvp]

theorem positive_survival_nonnegative (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Nonnegative (positiveSurvivalCompletion ν) := by
  intro t p hp
  have ht : 0 ≤ t := (positive_survival_properties ν).2.2.1 ⟨p,hp⟩
  rcases eq_or_lt_of_le ht with he | ht
  · subst t
    rw [positive_survival_zero] at hp
    exact measureReal_nonneg.trans hp
  · rw [(positive_survival_properties ν).2.2.2 t ht] at hp
    exact measureReal_nonneg.trans hp.1

theorem nonnegative_law_quantile_nonnegative (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, 0 ≤ x) {p x : ℝ} (hp : p ∈ Ioo 0 1)
    (hx : x ∈ tailQuantile ν p) : 0 ≤ x := by
  by_contra hn
  have hx0 : x < 0 := lt_of_not_ge hn
  have hmass : ν (Ioi x) = ν univ := by
    apply measure_congr
    filter_upwards [hν] with y hy
    exact propext ⟨fun _ => mem_univ y,fun _ => hx0.trans_le hy⟩
  have hreal : ν.real (Ioi x) = 1 := by simp [measureReal_def,hmass]
  change ν.real (Ioi x) ≤ p ∧ p ≤ ν.real (Ici x) at hx
  rw [hreal] at hx
  exact (not_lt_of_ge hx.1) hp.2

theorem positive_survival_inverse_interior (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, 0 ≤ x) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    inverse (positiveSurvivalCompletion ν) p = tailQuantile ν p := by
  have hmass : ν (Ici (0 : ℝ)) = ν univ := by
    apply measure_congr
    filter_upwards [hν] with y hy
    exact propext ⟨fun _ => mem_univ y,fun _ => hy⟩
  have hreal : ν.real (Ici (0 : ℝ)) = 1 := by simp [measureReal_def,hmass]
  ext x
  by_cases hx : x = 0
  · subst x
    change p ∈ positiveSurvivalCompletion ν 0 ↔ p ∈ survival ν 0
    rw [positive_survival_zero]
    change ν.real (Ioi 0) ≤ p ↔ ν.real (Ioi 0) ≤ p ∧ p ≤ ν.real (Ici 0)
    rw [hreal]
    exact ⟨fun h => ⟨h,hp.2.le⟩,And.left⟩
  · constructor
    · intro h
      have ht := (positive_survival_properties ν).2.2.1 ⟨p,h⟩
      have ht0 : 0 < x := lt_of_le_of_ne ht (Ne.symm hx)
      change p ∈ survival ν x
      change p ∈ positiveSurvivalCompletion ν x at h
      rwa [(positive_survival_properties ν).2.2.2 x ht0] at h
    · intro h
      have ht := nonnegative_law_quantile_nonnegative ν hν hp h
      have ht0 : 0 < x := lt_of_le_of_ne ht (Ne.symm hx)
      change p ∈ positiveSurvivalCompletion ν x
      rw [(positive_survival_properties ν).2.2.2 x ht0]
      exact h

theorem positive_survival_inverse_above_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {p : ℝ} (hp : 1 < p) : inverse (positiveSurvivalCompletion ν) p = {0} := by
  ext x
  constructor
  · intro hx
    have ht := (positive_survival_properties ν).2.2.1 ⟨p,hx⟩
    by_contra hne
    have ht0 : 0 < x := lt_of_le_of_ne ht (Ne.symm hne)
    change p ∈ positiveSurvivalCompletion ν x at hx
    rw [(positive_survival_properties ν).2.2.2 x ht0] at hx
    have hle : p ≤ 1 := hx.2.trans measureReal_le_one
    linarith
  · intro hx
    have hx0 : x = 0 := hx
    subst x
    change p ∈ positiveSurvivalCompletion ν 0
    rw [positive_survival_zero]
    exact measureReal_le_one.trans hp.le

end ScalarMonotone.EndOfPaper
end
