import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
The ordered-triple identities and inequalities required
by the prescribed-profile lower metric. These are intermediate
algebraic results; the metric and random model are supplied in later modules.
-/

noncomputable section
namespace ScalarMonotone.EndOfPaper

def orderedChainGap (x P y Q : ℝ) : ℝ := y-x*P/Q

theorem orderedChainGap_nonnegative {x y P Q : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hP : 0 ≤ P) (hPQ : P ≤ Q) (hQ : 0 < Q) :
    0 ≤ orderedChainGap x P y Q := by
  unfold orderedChainGap
  have hprod : x*P ≤ x*Q := mul_le_mul_of_nonneg_left hPQ hx
  have hbound : x*P/Q ≤ x := (div_le_iff₀ hQ).mpr hprod
  linarith

theorem orderedChainGap_three_identities {x y z P Q R : ℝ} (hQ : Q ≠ 0) (hR : R ≠ 0) :
    orderedChainGap x P z R-orderedChainGap x P y Q = z-y+x*P*(1/Q-1/R) ∧
    orderedChainGap x P z R-orderedChainGap y Q z R = (Q/R)*orderedChainGap x P y Q ∧
    orderedChainGap x P y Q+orderedChainGap y Q z R-orderedChainGap x P z R =
      (1-Q/R)*orderedChainGap x P y Q := by
  unfold orderedChainGap
  constructor
  · ring
  constructor <;> field_simp [hQ,hR] <;> ring

theorem orderedChainGap_metric_bounds {x y z P Q R : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hP : 0 ≤ P) (hPQ : P ≤ Q) (hQ : 0 < Q) (hQR : Q ≤ R) :
    max (orderedChainGap x P y Q) (orderedChainGap y Q z R) ≤ orderedChainGap x P z R ∧
      orderedChainGap x P z R ≤ orderedChainGap x P y Q+orderedChainGap y Q z R := by
  have hR : 0 < R := hQ.trans_le hQR
  have hid := orderedChainGap_three_identities (x := x) (y := y) (z := z) (P := P) hQ.ne' hR.ne'
  have hgap := orderedChainGap_nonnegative hx hxy hP hPQ hQ
  have hratio : 0 ≤ Q/R := div_nonneg hQ.le hR.le
  have hratio1 : Q/R ≤ 1 := (div_le_one hR).mpr hQR
  have hrecip : 0 ≤ 1/Q-1/R := sub_nonneg.mpr (one_div_le_one_div_of_le hQ hQR)
  have hfirst : 0 ≤ z-y+x*P*(1/Q-1/R) :=
    add_nonneg (sub_nonneg.mpr hyz) (mul_nonneg (mul_nonneg hx hP) hrecip)
  have hsecond : 0 ≤ (Q/R)*orderedChainGap x P y Q := mul_nonneg hratio hgap
  have hthird : 0 ≤ (1-Q/R)*orderedChainGap x P y Q := mul_nonneg (sub_nonneg.mpr hratio1) hgap
  refine ⟨max_le (by linarith [hid.1]) (by linarith [hid.2.1]),?_⟩
  linarith [hid.2.2]

end ScalarMonotone.EndOfPaper
end
