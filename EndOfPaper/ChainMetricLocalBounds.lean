import EndOfPaper.ChainMetricAlgebra

/-!
Local chain-metric product and coordinate bounds
needed for continuity away from the origin. The full lower-model
Borel and probability construction remains separate.
-/

noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem orderedChainGap_product_identity (x y P Q : ℝ) (hQ : Q ≠ 0) :
    y*Q-x*P = Q*orderedChainGap x P y Q := by
  unfold orderedChainGap
  field_simp [hQ]

theorem orderedChainGap_le_right {x y P Q : ℝ}
    (hx : 0 ≤ x) (hP : 0 ≤ P) (hQ : 0 < Q) : orderedChainGap x P y Q ≤ y := by
  have hratio : 0 ≤ x*P/Q := div_nonneg (mul_nonneg hx hP) hQ.le
  unfold orderedChainGap
  linarith

theorem sub_le_orderedChainGap {x y P Q : ℝ}
    (hx : 0 ≤ x) (hPQ : P ≤ Q) (hQ : 0 < Q) : y-x ≤ orderedChainGap x P y Q := by
  have hratio : x*P/Q ≤ x := (div_le_iff₀ hQ).mpr (mul_le_mul_of_nonneg_left hPQ hx)
  unfold orderedChainGap
  linarith

theorem orderedChainGap_small_implies_ratio_bound {x y P Q : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hQ : 0 < Q)
    (hd : orderedChainGap x P y Q < x/2) : Q < 2*P := by
  have he := orderedChainGap_product_identity x y P Q hQ.ne'
  have hsmall := mul_lt_mul_of_pos_right hd hQ
  have horder := mul_le_mul_of_nonneg_right hxy hQ.le
  by_contra h
  have hbad := mul_le_mul_of_nonneg_left (le_of_not_gt h) hx.le
  nlinarith

theorem orderedChainGap_local_product_bound {x y P Q : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hP : 0 ≤ P) (hPQ : P ≤ Q) (hQ : 0 < Q)
    (hd : orderedChainGap x P y Q < x/2) :
    |y*Q-x*P| ≤ 2*P*orderedChainGap x P y Q := by
  have he := orderedChainGap_product_identity x y P Q hQ.ne'
  have hD := orderedChainGap_nonnegative hx.le hxy hP hPQ hQ
  have hNN : 0 ≤ y*Q-x*P := by rw [he]; exact mul_nonneg hQ.le hD
  rw [abs_of_nonneg hNN,he]
  exact mul_le_mul_of_nonneg_right (orderedChainGap_small_implies_ratio_bound hx hxy hQ hd).le hD

end ScalarMonotone.EndOfPaper
end
