import EndOfPaper.PositiveChainSpace
import EndOfPaper.ChainMetricLocalBounds

/-!
Exact origin distance, baseline maximum bound and product modulus for the fresh chain metric.
-/

open Set
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper
section
variable {n : ℕ} {C : Set (Option (Fin n) → ℝ)}
    (h0 : ∀ x ∈ C, ∀ i, 0 ≤ x i)
    (hp : ∀ x ∈ C, x = 0 ∨ ∀ i, 0 < x i)
    (hc : ∀ x ∈ C, ∀ y ∈ C, x ≤ y ∨ y ≤ x)

def positiveChainOrigin (hz : (0 : Option (Fin n) → ℝ) ∈ C) : PositiveProductPoint C :=
  ⟨0,hz⟩

theorem positiveChainMetric_product_identity (x y : PositiveProductPoint C) :
    letI := positiveChainMetric h0 hp hc
    dist x y * (∏ i : Fin n, max (x.coords (some i)) (y.coords (some i))) =
      |(∏ j, x.coords j)-(∏ j, y.coords j)| := by
  classical
  letI := positiveChainMetric h0 hp hc
  have hcomp : (fun i : Fin n => x.coords (some i)) ≤ (fun i => y.coords (some i)) ∨
      (fun i : Fin n => y.coords (some i)) ≤ (fun i => x.coords (some i)) := by
    rcases hc x.coords x.coords_mem y.coords y.coords_mem with h | h
    · exact Or.inl (fun i => h (some i))
    · exact Or.inr (fun i => h (some i))
  have hmax : (∏ i : Fin n, max (x.coords (some i)) (y.coords (some i))) =
      max (∏ i : Fin n, x.coords (some i)) (∏ i : Fin n, y.coords (some i)) :=
    product_max_of_comparable (fun i => h0 x.coords x.coords_mem (some i))
      (fun i => h0 y.coords y.coords_mem (some i)) hcomp
  rw [positiveChainMetric_distance h0 hp hc,hmax]
  by_cases hd : max (∏ i : Fin n, x.coords (some i)) (∏ i : Fin n, y.coords (some i)) = 0
  · have hx : (∏ i : Fin n, x.coords (some i)) = 0 :=
      le_antisymm ((le_max_left _ _).trans_eq hd)
        (Finset.prod_nonneg (fun i _ => h0 x.coords x.coords_mem (some i)))
    have hy : (∏ i : Fin n, y.coords (some i)) = 0 :=
      le_antisymm ((le_max_right _ _).trans_eq hd)
        (Finset.prod_nonneg (fun i _ => h0 y.coords y.coords_mem (some i)))
    simp only [Fintype.prod_option,hx,hy,mul_zero,sub_self,abs_zero,zero_div,zero_mul]
  · exact div_mul_cancel₀ _ hd

theorem positiveChainMetric_origin_distance
    (hz : (0 : Option (Fin n) → ℝ) ∈ C) (x : PositiveProductPoint C) :
    letI := positiveChainMetric h0 hp hc
    dist x (positiveChainOrigin hz) = x.coords none := by
  classical
  letI := positiveChainMetric h0 hp hc
  rcases hp x.coords x.coords_mem with hx | hx
  · have he : x = positiveChainOrigin hz := positiveProductPoint_ext hx
    subst x
    simp [positiveChainOrigin]
  · have hP : 0 < ∏ i : Fin n, x.coords (some i) := Finset.prod_pos (fun i _ => hx (some i))
    rw [positiveChainMetric_distance h0 hp hc]
    have hmax : (∏ i : Fin n, max (x.coords (some i)) ((positiveChainOrigin hz).coords (some i))) =
        ∏ i : Fin n, x.coords (some i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact max_eq_left (h0 x.coords x.coords_mem (some i))
    rw [hmax]
    simp only [Fintype.prod_option,positiveChainOrigin,Pi.zero_apply,zero_mul,sub_zero]
    rw [abs_of_nonneg (mul_nonneg (hx none).le hP.le),mul_div_cancel_right₀ _ hP.ne']

theorem positiveChainMetric_le_max_baseline (x y : PositiveProductPoint C) :
    letI := positiveChainMetric h0 hp hc
    dist x y ≤ max (x.coords none) (y.coords none) := by
  classical
  letI := positiveChainMetric h0 hp hc
  change weightedChainDistance (fun z : PositiveProductPoint C => z.coords none)
    (fun z => ∏ i : Fin n, z.coords (some i)) x y ≤ _
  have hxP : 0 ≤ ∏ i : Fin n, x.coords (some i) :=
    Finset.prod_nonneg (fun i _ => h0 x.coords x.coords_mem (some i))
  have hyP : 0 ≤ ∏ i : Fin n, y.coords (some i) :=
    Finset.prod_nonneg (fun i _ => h0 y.coords y.coords_mem (some i))
  have hxA := h0 x.coords x.coords_mem none
  have hyA := h0 y.coords y.coords_mem none
  rcases hc x.coords x.coords_mem y.coords y.coords_mem with hxy | hyx
  · have hP : (∏ i : Fin n, x.coords (some i)) ≤ ∏ i : Fin n, y.coords (some i) :=
      Finset.prod_le_prod (fun i _ => h0 x.coords x.coords_mem (some i)) (fun i _ => hxy (some i))
    have hAP := mul_le_mul (hxy none) hP hxP hyA
    unfold weightedChainDistance
    rw [max_eq_right hP,max_eq_right (hxy none),abs_of_nonpos (sub_nonpos.mpr hAP),neg_sub]
    by_cases hyz : (∏ i : Fin n, y.coords (some i)) = 0
    · simp only [hyz,div_zero]; exact hyA
    · apply (div_le_iff₀ (lt_of_le_of_ne hyP (Ne.symm hyz))).mpr
      have hNN := mul_nonneg hxA hxP
      linarith
  · have hP : (∏ i : Fin n, y.coords (some i)) ≤ ∏ i : Fin n, x.coords (some i) :=
      Finset.prod_le_prod (fun i _ => h0 y.coords y.coords_mem (some i)) (fun i _ => hyx (some i))
    have hAP := mul_le_mul (hyx none) hP hyP hxA
    unfold weightedChainDistance
    rw [max_eq_left hP,max_eq_left (hyx none),abs_of_nonneg (sub_nonneg.mpr hAP)]
    by_cases hxz : (∏ i : Fin n, x.coords (some i)) = 0
    · simp only [hxz,div_zero]; exact hxA
    · apply (div_le_iff₀ (lt_of_le_of_ne hxP (Ne.symm hxz))).mpr
      have hNN := mul_nonneg hyA hyP
      linarith

theorem positiveChainMetric_le_product_gap (x y : PositiveProductPoint C)
    (hx : 0 < ∏ i : Fin n, x.coords (some i)) :
    letI := positiveChainMetric h0 hp hc
    dist x y ≤ |(∏ j, x.coords j)-(∏ j, y.coords j)| / (∏ i : Fin n, x.coords (some i)) := by
  classical
  letI := positiveChainMetric h0 hp hc
  apply (le_div_iff₀ hx).mpr
  rw [← positiveChainMetric_product_identity h0 hp hc x y]
  apply mul_le_mul_of_nonneg_left _ dist_nonneg
  apply Finset.prod_le_prod (fun i _ => h0 x.coords x.coords_mem (some i))
  exact fun i _ => le_max_left _ _

end
end ScalarMonotone.EndOfPaper
end
