import EndOfPaper.NetworkRateInverse

/-!
Uniform polynomial growth in the two depth regimes.
-/

open Set
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem network_depth_polynomial_majorant (L : ℕ) {d M A s : ℝ}
    (hd : 0 < d) (hM : 0 ≤ M) (hA : 0 ≤ A) (hs : 0 ≤ s) :
    s*(M+A*s/Real.sqrt d)^L ≤
      (M+A)^L*max s (s^(L+1)/(Real.sqrt d)^L) := by
  have hr := Real.sqrt_pos.mpr hd
  have hb0 : 0 ≤ M+A*s/Real.sqrt d := add_nonneg hM (div_nonneg (mul_nonneg hA hs) hr.le)
  have hMA : 0 ≤ M+A := add_nonneg hM hA
  by_cases hsr : s ≤ Real.sqrt d
  · have hb : M+A*s/Real.sqrt d ≤ M+A := by
      have hh : s/Real.sqrt d ≤ 1 := (div_le_one hr).mpr hsr
      have hh' := mul_le_mul_of_nonneg_left hh hA
      rw [← mul_div_assoc,mul_one] at hh'
      exact add_le_add_left hh' M
    calc
      _ ≤ s*(M+A)^L := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hb L) hs
      _ ≤ _ := by
        rw [mul_comm s]
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) (pow_nonneg hMA L)
  · have hrs : Real.sqrt d ≤ s := le_of_not_ge hsr
    have hf : 1 ≤ s/Real.sqrt d := (one_le_div hr).mpr hrs
    have hb : M+A*s/Real.sqrt d ≤ (M+A)*(s/Real.sqrt d) := by
      have hh := mul_le_mul_of_nonneg_left hf hM
      rw [mul_one] at hh
      calc
        _ ≤ M*(s/Real.sqrt d)+A*(s/Real.sqrt d) := by rw [mul_div_assoc]; linarith only [hh]
        _ = _ := by ring
    calc
      _ ≤ s*((M+A)*(s/Real.sqrt d))^L :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hb L) hs
      _ = (M+A)^L*(s^(L+1)/(Real.sqrt d)^L) := by
        rw [mul_pow,div_pow,pow_succ]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (pow_nonneg hMA L)

theorem network_depth_at_rate_inverse (L : ℕ) {d M A t : ℝ}
    (hd : 0 < d) (hM : 0 ≤ M) (hA : 0 ≤ A) (ht : 0 ≤ t) :
    let s := networkRateInverse L d t
    s*(M+A*s/Real.sqrt d)^L ≤ (M+A)^L*t := by
  have hp := network_rate_inverse_properties L hd ht
  exact (network_depth_polynomial_majorant L hd hM hA hp.1).trans
    (mul_le_mul_of_nonneg_left (max_le hp.2.1 hp.2.2.1) (pow_nonneg (add_nonneg hM hA) L))

end ScalarMonotone.EndOfPaper
end
