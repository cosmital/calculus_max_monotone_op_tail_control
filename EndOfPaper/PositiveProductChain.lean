import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
Strict product injectivity and coordinate-gap
estimates on comparable positive-or-zero finite coordinate
chains, derived from their actual coordinate order.
-/

open Set
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem positive_product_strict_of_coordinate_lt {ι : Type*} [Fintype ι]
    {x y : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 < y i)
    (hxy : x ≤ y) (hne : x ≠ y) : (∏ i, x i) < ∏ i, y i := by
  classical
  by_cases hpos : ∀ i, 0 < x i
  · have hstrict : ∃ i, x i < y i := by
      by_contra h
      apply hne
      funext i
      exact le_antisymm (hxy i) (le_of_not_gt (fun hi => h ⟨i,hi⟩))
    obtain ⟨i,hi⟩ := hstrict
    exact Finset.prod_lt_prod (fun j _ => hpos j) (fun j _ => hxy j) ⟨i,Finset.mem_univ i,hi⟩
  · obtain ⟨i,hi⟩ := not_forall.mp hpos
    have hi0 : x i = 0 := le_antisymm (le_of_not_gt hi) (hx i)
    have hp0 : (∏ j, x j) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi0
    rw [hp0]
    exact Finset.prod_pos (fun j _ => hy j)

theorem product_injective_on_positive_or_zero_chain {ι : Type*} [Fintype ι]
    {C : Set (ι → ℝ)} (h0 : ∀ x ∈ C, ∀ i, 0 ≤ x i)
    (hpos : ∀ x ∈ C, x = 0 ∨ ∀ i, 0 < x i)
    (hchain : ∀ x ∈ C, ∀ y ∈ C, x ≤ y ∨ y ≤ x) :
    Set.InjOn (fun x : ι → ℝ => ∏ i, x i) C := by
  intro x hx y hy he
  by_contra hne
  rcases hchain x hx y hy with hxy | hyx
  · rcases hpos y hy with hy0 | hyp
    · apply hne
      funext i
      have hi : x i ≤ 0 := by simpa only [hy0,Pi.zero_apply] using hxy i
      have hx0 : x i = 0 := le_antisymm hi (h0 x hx i)
      simpa only [hy0,Pi.zero_apply] using hx0
    · exact (ne_of_lt (positive_product_strict_of_coordinate_lt (h0 x hx) hyp hxy hne)) he
  · rcases hpos x hx with hx0 | hxp
    · apply hne
      funext i
      have hi : y i ≤ 0 := by simpa only [hx0,Pi.zero_apply] using hyx i
      have hy0 : y i = 0 := le_antisymm hi (h0 y hy i)
      simpa only [hx0,Pi.zero_apply] using hy0.symm
    · exact (ne_of_lt (positive_product_strict_of_coordinate_lt (h0 y hy) hxp hyx (Ne.symm hne))) he.symm

theorem product_max_of_comparable {ι : Type*} [Fintype ι] {x y : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) (hchain : x ≤ y ∨ y ≤ x) :
    (∏ i, max (x i) (y i)) = max (∏ i, x i) (∏ i, y i) := by
  rcases hchain with hxy | hyx
  · have hp : (∏ i, x i) ≤ ∏ i, y i := Finset.prod_le_prod (fun i _ => hx i) (fun i _ => hxy i)
    calc
      _ = ∏ i, y i := Finset.prod_congr rfl (fun i _ => max_eq_right (hxy i))
      _ = _ := (max_eq_right hp).symm
  · have hp : (∏ i, y i) ≤ ∏ i, x i := Finset.prod_le_prod (fun i _ => hy i) (fun i _ => hyx i)
    calc
      _ = ∏ i, x i := Finset.prod_congr rfl (fun i _ => max_eq_left (hyx i))
      _ = _ := (max_eq_left hp).symm

theorem coordinate_gap_mul_le_product_gap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {x y : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hchain : x ≤ y ∨ y ≤ x) (i : ι) :
    |x i-y i| * (∏ j ∈ Finset.univ.erase i, x j) ≤ |(∏ j, x j)-(∏ j, y j)| := by
  classical
  have hxp : x i*(∏ j ∈ Finset.univ.erase i, x j) = ∏ j, x j :=
    Finset.mul_prod_erase Finset.univ (fun j => x j) (Finset.mem_univ i)
  have hyp : y i*(∏ j ∈ Finset.univ.erase i, y j) = ∏ j, y j :=
    Finset.mul_prod_erase Finset.univ (fun j => y j) (Finset.mem_univ i)
  rcases hchain with hxy | hyx
  · have hp : (∏ j, x j) ≤ ∏ j, y j := Finset.prod_le_prod (fun j _ => hx j) (fun j _ => hxy j)
    have he : (∏ j ∈ Finset.univ.erase i, x j) ≤ ∏ j ∈ Finset.univ.erase i, y j :=
      Finset.prod_le_prod (fun j _ => hx j) (fun j _ => hxy j)
    have hm := mul_le_mul_of_nonneg_left he (hy i)
    rw [abs_of_nonpos (sub_nonpos.mpr (hxy i)),abs_of_nonpos (sub_nonpos.mpr hp)]
    simp only [neg_sub]
    nlinarith
  · have hp : (∏ j, y j) ≤ ∏ j, x j := Finset.prod_le_prod (fun j _ => hy j) (fun j _ => hyx j)
    have he : (∏ j ∈ Finset.univ.erase i, y j) ≤ ∏ j ∈ Finset.univ.erase i, x j :=
      Finset.prod_le_prod (fun j _ => hy j) (fun j _ => hyx j)
    have hm := mul_le_mul_of_nonneg_left he (hy i)
    rw [abs_of_nonneg (sub_nonneg.mpr (hyx i)),abs_of_nonneg (sub_nonneg.mpr hp)]
    nlinarith

end ScalarMonotone.EndOfPaper
end
