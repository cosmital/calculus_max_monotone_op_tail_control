import EndOfPaper.PositiveChainSpace
import EndOfPaper.ChainMetricLocalBounds
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
Local coordinate continuity away from the origin and global coordinate Borel measurability.
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

theorem positiveChainMetric_ordered_distance {x y : PositiveProductPoint C}
    (hxy : x.coords ≤ y.coords) (hyP : 0 < ∏ i : Fin n, y.coords (some i)) :
    letI := positiveChainMetric h0 hp hc
    dist x y = orderedChainGap (x.coords none) (∏ i : Fin n, x.coords (some i))
      (y.coords none) (∏ i : Fin n, y.coords (some i)) := by
  classical
  letI := positiveChainMetric h0 hp hc
  have hP : (∏ i : Fin n, x.coords (some i)) ≤ ∏ i : Fin n, y.coords (some i) :=
    Finset.prod_le_prod (fun i _ => h0 x.coords x.coords_mem (some i)) (fun i _ => hxy (some i))
  have hPx : 0 ≤ ∏ i : Fin n, x.coords (some i) :=
    Finset.prod_nonneg (fun i _ => h0 x.coords x.coords_mem (some i))
  have hprod := mul_le_mul (hxy none) hP hPx (h0 y.coords y.coords_mem none)
  change |x.coords none*(∏ i : Fin n, x.coords (some i))-
      y.coords none*(∏ i : Fin n, y.coords (some i))| /
    max (∏ i : Fin n, x.coords (some i)) (∏ i : Fin n, y.coords (some i)) = _
  rw [max_eq_right hP,abs_of_nonpos (sub_nonpos.mpr hprod),neg_sub]
  unfold orderedChainGap
  rw [sub_div,mul_div_cancel_right₀ _ hyP.ne']

theorem positiveChainMetric_local_weight_bound {x y : PositiveProductPoint C}
    (hx : ∀ j, 0 < x.coords j) :
    letI := positiveChainMetric h0 hp hc
    dist x y < x.coords none/2 →
      max (∏ i : Fin n, x.coords (some i)) (∏ i : Fin n, y.coords (some i)) <
        2*(∏ i : Fin n, x.coords (some i)) := by
  classical
  letI := positiveChainMetric h0 hp hc
  intro hd
  have hxP : 0 < ∏ i : Fin n, x.coords (some i) := Finset.prod_pos (fun i _ => hx (some i))
  rcases hc x.coords x.coords_mem y.coords y.coords_mem with hxy | hyx
  · have hP : (∏ i : Fin n, x.coords (some i)) ≤ ∏ i : Fin n, y.coords (some i) :=
      Finset.prod_le_prod (fun i _ => (hx (some i)).le) (fun i _ => hxy (some i))
    have hyP := hxP.trans_le hP
    rw [positiveChainMetric_ordered_distance h0 hp hc hxy hyP] at hd
    rw [max_eq_right hP]
    exact orderedChainGap_small_implies_ratio_bound (hx none) (hxy none) hyP hd
  · have hP : (∏ i : Fin n, y.coords (some i)) ≤ ∏ i : Fin n, x.coords (some i) :=
      Finset.prod_le_prod (fun i _ => h0 y.coords y.coords_mem (some i)) (fun i _ => hyx (some i))
    rw [max_eq_left hP]
    linarith

theorem positiveChainMetric_local_coordinate_bound {x y : PositiveProductPoint C}
    (hx : ∀ j, 0 < x.coords j) (j : Option (Fin n)) :
    letI := positiveChainMetric h0 hp hc
    dist x y < x.coords none/2 →
      |x.coords j-y.coords j| * (∏ k ∈ Finset.univ.erase j, x.coords k) ≤
        (2*(∏ i : Fin n, x.coords (some i)))*dist x y := by
  classical
  letI := positiveChainMetric h0 hp hc
  intro hd
  have hgap := coordinate_gap_mul_le_product_gap (fun k => (hx k).le)
    (h0 y.coords y.coords_mem) (hc x.coords x.coords_mem y.coords y.coords_mem) j
  have hmax := positiveChainMetric_local_weight_bound h0 hp hc hx hd
  have hxP : 0 < ∏ i : Fin n, x.coords (some i) := Finset.prod_pos (fun i _ => hx (some i))
  have hden : 0 < max (∏ i : Fin n, x.coords (some i)) (∏ i : Fin n, y.coords (some i)) :=
    hxP.trans_le (le_max_left _ _)
  have he : |(∏ k, x.coords k)-(∏ k, y.coords k)| =
      dist x y*max (∏ i : Fin n, x.coords (some i)) (∏ i : Fin n, y.coords (some i)) := by
    change _ = (|x.coords none*(∏ i : Fin n, x.coords (some i))-
        y.coords none*(∏ i : Fin n, y.coords (some i))| /
      max (∏ i : Fin n, x.coords (some i)) (∏ i : Fin n, y.coords (some i)))*_
    rw [div_mul_cancel₀ _ hden.ne']
    simp only [Fintype.prod_option]
  calc
    _ ≤ |(∏ k, x.coords k)-(∏ k, y.coords k)| := hgap
    _ = _ := he
    _ ≤ _ := by
      rw [mul_comm (2*_) (dist x y)]
      exact mul_le_mul_of_nonneg_left hmax.le dist_nonneg

theorem positiveChainMetric_coordinate_continuousAt {x : PositiveProductPoint C}
    (hx : ∀ j, 0 < x.coords j) (j : Option (Fin n)) :
    letI := positiveChainMetric h0 hp hc
    ContinuousAt (fun z : PositiveProductPoint C => z.coords j) x := by
  classical
  letI := positiveChainMetric h0 hp hc
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  let K := ∏ k ∈ Finset.univ.erase j, x.coords k
  let P := ∏ i : Fin n, x.coords (some i)
  have hK : 0 < K := Finset.prod_pos (fun k _ => hx k)
  have hP : 0 < P := Finset.prod_pos (fun i _ => hx (some i))
  have htwo : 0 < 2*P := mul_pos (by norm_num) hP
  refine ⟨min (x.coords none/2) (ε*K/(2*P)),
    lt_min (div_pos (hx none) (by norm_num)) (div_pos (mul_pos hε hK) htwo),?_⟩
  intro y hy
  have hd : dist x y < x.coords none/2 := by
    rw [dist_comm]
    exact hy.trans_le (min_le_left _ _)
  have hb := positiveChainMetric_local_coordinate_bound h0 hp hc hx j hd
  have hsmall : dist x y < ε*K/(2*P) := by
    rw [dist_comm]
    exact hy.trans_le (min_le_right _ _)
  have hmul : (2*P)*dist x y < ε*K := by
    have hm := (lt_div_iff₀ htwo).mp hsmall
    simpa only [mul_comm] using hm
  have hfinal : |x.coords j-y.coords j| < ε :=
    (mul_lt_mul_right hK).mp (hb.trans_lt hmul)
  simpa only [Real.dist_eq,abs_sub_comm] using hfinal

theorem positiveChainMetric_coordinate_measurable
    (hz : (0 : Option (Fin n) → ℝ) ∈ C) (j : Option (Fin n)) :
    letI := positiveChainMetric h0 hp hc
    @Measurable (PositiveProductPoint C) ℝ (borel (PositiveProductPoint C)) _
      (fun z => z.coords j) := by
  classical
  letI := positiveChainMetric h0 hp hc
  letI : MeasurableSpace (PositiveProductPoint C) := borel (PositiveProductPoint C)
  letI : BorelSpace (PositiveProductPoint C) := ⟨rfl⟩
  let o : PositiveProductPoint C := ⟨0,hz⟩
  apply measurable_of_continuousOn_compl_singleton o
  intro x hx
  rcases hp x.coords x.coords_mem with hx0 | hpos
  · have he : x = o := positiveProductPoint_ext hx0
    exact False.elim (hx (by simpa only [mem_singleton_iff] using he))
  · exact (positiveChainMetric_coordinate_continuousAt h0 hp hc hpos j).continuousWithinAt

end
end ScalarMonotone.EndOfPaper
end
