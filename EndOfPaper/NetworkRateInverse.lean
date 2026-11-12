import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Exact inversion of the two polynomial regimes in the depth tail rate.
-/

open Set
noncomputable section
namespace ScalarMonotone.EndOfPaper

def networkRateInverse (L : ℕ) (d t : ℝ) : ℝ :=
  min t (((Real.sqrt d)^L*t)^(((L+1 : ℕ) : ℝ))⁻¹)

def networkRatePower (L : ℕ) (d t : ℝ) : ℝ :=
  min (t^2) (d^((L : ℝ)/((L : ℝ)+1))*t^(2/((L : ℝ)+1)))

theorem nonnegative_min_square {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (min a b)^2 = min (a^2) (b^2) := by
  by_cases hab : a ≤ b
  · rw [min_eq_left hab,min_eq_left (by nlinarith)]
  · have hba : b ≤ a := le_of_not_ge hab
    rw [min_eq_right hba,min_eq_right (by nlinarith)]

theorem network_rate_root_square (L : ℕ) {d t : ℝ} (hd : 0 < d) (ht : 0 ≤ t) :
    (((Real.sqrt d)^L*t)^(((L+1 : ℕ) : ℝ))⁻¹)^2 =
      d^((L : ℝ)/((L : ℝ)+1))*t^(2/((L : ℝ)+1)) := by
  have hd0 := (Real.sqrt_pos.mpr hd).le
  have ha : 0 ≤ (Real.sqrt d)^L*t := mul_nonneg (pow_nonneg hd0 _) ht
  rw [← Real.rpow_natCast,← Real.rpow_mul ha,Real.mul_rpow (pow_nonneg hd0 _) ht,
    ← Real.rpow_natCast,← Real.rpow_mul hd0,Real.sqrt_eq_rpow,← Real.rpow_mul hd.le]
  push_cast
  have he1 : (1/2 : ℝ)*((L : ℝ)*(((L : ℝ)+1)⁻¹*2)) = (L : ℝ)/((L : ℝ)+1) := by ring
  have he2 : ((L : ℝ)+1)⁻¹*2 = 2/((L : ℝ)+1) := by ring
  rw [he1,he2]

theorem network_rate_inverse_properties (L : ℕ) {d t : ℝ} (hd : 0 < d) (ht : 0 ≤ t) :
    0 ≤ networkRateInverse L d t ∧ networkRateInverse L d t ≤ t ∧
    (networkRateInverse L d t)^(L+1)/(Real.sqrt d)^L ≤ t ∧
    (networkRateInverse L d t)^2 = networkRatePower L d t := by
  have hs0 := (Real.sqrt_pos.mpr hd).le
  have ha : 0 ≤ (Real.sqrt d)^L*t := mul_nonneg (pow_nonneg hs0 _) ht
  have hr0 : 0 ≤ ((Real.sqrt d)^L*t)^(((L+1 : ℕ) : ℝ))⁻¹ := Real.rpow_nonneg ha _
  have hmin0 : 0 ≤ networkRateInverse L d t := le_min ht hr0
  have hpower : (networkRateInverse L d t)^(L+1) ≤ (Real.sqrt d)^L*t := by
    have hh := pow_le_pow_left₀ hmin0 (min_le_right t
      (((Real.sqrt d)^L*t)^(((L+1 : ℕ) : ℝ))⁻¹)) (L+1)
    rwa [Real.rpow_inv_natCast_pow ha (Nat.succ_ne_zero L)] at hh
  refine ⟨hmin0,min_le_left _ _,?_,?_⟩
  · apply (div_le_iff₀ (pow_pos (Real.sqrt_pos.mpr hd) L)).mpr
    simpa only [mul_comm] using hpower
  · unfold networkRateInverse networkRatePower
    rw [nonnegative_min_square ht hr0,network_rate_root_square L hd ht]

end ScalarMonotone.EndOfPaper
end
