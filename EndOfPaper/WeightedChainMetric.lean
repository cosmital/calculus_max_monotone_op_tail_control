import EndOfPaper.ChainMetricAlgebra
import Mathlib.Topology.MetricSpace.Basic

/-!
An actual weighted-chain metric, including all
triangle inequalities and separation. Instantiation and
measurability of the full lower random model remain separate.
-/

noncomputable section
namespace ScalarMonotone.EndOfPaper

def weightedChainDistance {α : Type*} (A P : α → ℝ) (x y : α) : ℝ :=
  |A x*P x-A y*P y|/max (P x) (P y)

theorem weightedChainDistance_self {α : Type*} (A P : α → ℝ) (x : α) :
    weightedChainDistance A P x x = 0 := by simp [weightedChainDistance]

theorem weightedChainDistance_comm {α : Type*} (A P : α → ℝ) (x y : α) :
    weightedChainDistance A P x y = weightedChainDistance A P y x := by
  simp only [weightedChainDistance,abs_sub_comm (A x*P x) (A y*P y),max_comm]

theorem weightedChainDistance_nonnegative {α : Type*} (A P : α → ℝ)
    (hP : ∀ x, 0 ≤ P x) (x y : α) : 0 ≤ weightedChainDistance A P x y :=
  div_nonneg (abs_nonneg _) ((hP x).trans (le_max_left _ _))

theorem weightedChainDistance_ordered {α : Type*} [LinearOrder α] {A P : α → ℝ}
    (hA : Monotone A) (hP : Monotone P) (hA0 : ∀ x, 0 ≤ A x) (hP0 : ∀ x, 0 ≤ P x)
    {x y : α} (hxy : x ≤ y) (hy : 0 < P y) :
    weightedChainDistance A P x y = orderedChainGap (A x) (P x) (A y) (P y) := by
  have hprod : A x*P x ≤ A y*P y := mul_le_mul (hA hxy) (hP hxy) (hP0 x) (hA0 y)
  rw [weightedChainDistance,max_eq_right (hP hxy),abs_of_nonpos (sub_nonpos.mpr hprod)]
  unfold orderedChainGap
  rw [neg_sub,sub_div,mul_div_cancel_right₀ _ hy.ne']

theorem weightedChainDistance_ordered_bounds {α : Type*} [LinearOrder α] {A P : α → ℝ}
    (hA : Monotone A) (hP : Monotone P) (hA0 : ∀ x, 0 ≤ A x) (hP0 : ∀ x, 0 ≤ P x)
    (hinj : Function.Injective (fun x => A x*P x))
    {x y z : α} (hxy : x ≤ y) (hyz : y ≤ z) :
    max (weightedChainDistance A P x y) (weightedChainDistance A P y z) ≤ weightedChainDistance A P x z ∧
      weightedChainDistance A P x z ≤ weightedChainDistance A P x y+weightedChainDistance A P y z := by
  by_cases hy0 : P y = 0
  · have hx0 : P x = 0 := le_antisymm ((hP hxy).trans_eq hy0) (hP0 x)
    have he : x = y := hinj (by simp only [hx0,hy0,mul_zero])
    subst x
    simp only [weightedChainDistance_self,zero_add]
    exact ⟨max_eq_right (weightedChainDistance_nonnegative A P hP0 y z) |>.le,le_rfl⟩
  · have hy : 0 < P y := lt_of_le_of_ne (hP0 y) (Ne.symm hy0)
    have hz : 0 < P z := hy.trans_le (hP hyz)
    rw [weightedChainDistance_ordered hA hP hA0 hP0 hxy hy,
      weightedChainDistance_ordered hA hP hA0 hP0 hyz hz,
      weightedChainDistance_ordered hA hP hA0 hP0 (hxy.trans hyz) hz]
    exact orderedChainGap_metric_bounds (hA0 x) (hA hxy) (hA hyz) (hP0 x) (hP hxy) hy (hP hyz)

theorem weightedChainDistance_triangle {α : Type*} [LinearOrder α] {A P : α → ℝ}
    (hA : Monotone A) (hP : Monotone P) (hA0 : ∀ x, 0 ≤ A x) (hP0 : ∀ x, 0 ≤ P x)
    (hinj : Function.Injective (fun x => A x*P x)) (x y z : α) :
    weightedChainDistance A P x z ≤ weightedChainDistance A P x y+weightedChainDistance A P y z := by
  have hxy0 := weightedChainDistance_nonnegative A P hP0 x y
  have hyz0 := weightedChainDistance_nonnegative A P hP0 y z
  have hsxy := weightedChainDistance_comm A P x y
  have hsyz := weightedChainDistance_comm A P y z
  have hsxz := weightedChainDistance_comm A P x z
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · exact (weightedChainDistance_ordered_bounds hA hP hA0 hP0 hinj hxy hyz).2
    · rcases le_total x z with hxz | hzx
      · have hb := (weightedChainDistance_ordered_bounds hA hP hA0 hP0 hinj hxz hzy).1
        have hl := (le_max_left (weightedChainDistance A P x z) (weightedChainDistance A P z y)).trans hb
        linarith
      · have hb := (weightedChainDistance_ordered_bounds hA hP hA0 hP0 hinj hzx hxy).1
        have hl := (le_max_left (weightedChainDistance A P z x) (weightedChainDistance A P x y)).trans hb
        linarith
  · rcases le_total x z with hxz | hzx
    · have hb := (weightedChainDistance_ordered_bounds hA hP hA0 hP0 hinj hyx hxz).1
      have hl := (le_max_right (weightedChainDistance A P y x) (weightedChainDistance A P x z)).trans hb
      linarith
    · rcases le_total y z with hyz | hzy
      · have hb := (weightedChainDistance_ordered_bounds hA hP hA0 hP0 hinj hyz hzx).1
        have hl := (le_max_right (weightedChainDistance A P y z) (weightedChainDistance A P z x)).trans hb
        linarith
      · have hb := (weightedChainDistance_ordered_bounds hA hP hA0 hP0 hinj hzy hyx).2
        linarith

theorem weightedChainDistance_eq_zero_iff {α : Type*} {A P : α → ℝ}
    (hP0 : ∀ x, 0 ≤ P x) (hinj : Function.Injective (fun x => A x*P x)) (x y : α) :
    weightedChainDistance A P x y = 0 ↔ x = y := by
  constructor
  · intro h
    change |A x*P x-A y*P y|/max (P x) (P y) = 0 at h
    rcases div_eq_zero_iff.mp h with hnum | hden
    · exact hinj (sub_eq_zero.mp (abs_eq_zero.mp hnum))
    · have hx : P x = 0 := le_antisymm ((le_max_left _ _).trans_eq hden) (hP0 x)
      have hy : P y = 0 := le_antisymm ((le_max_right _ _).trans_eq hden) (hP0 y)
      exact hinj (by simp only [hx,hy,mul_zero])
  · rintro rfl
    exact weightedChainDistance_self A P x

def weightedChainMetric {α : Type*} [LinearOrder α] (A P : α → ℝ)
    (hA : Monotone A) (hP : Monotone P) (hA0 : ∀ x, 0 ≤ A x) (hP0 : ∀ x, 0 ≤ P x)
    (hinj : Function.Injective (fun x => A x*P x)) : MetricSpace α where
  dist := weightedChainDistance A P
  dist_self := weightedChainDistance_self A P
  dist_comm := weightedChainDistance_comm A P
  dist_triangle := weightedChainDistance_triangle hA hP hA0 hP0 hinj
  eq_of_dist_eq_zero h := (weightedChainDistance_eq_zero_iff hP0 hinj _ _).mp h

end ScalarMonotone.EndOfPaper
end
