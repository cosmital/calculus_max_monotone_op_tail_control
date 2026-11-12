import EndOfPaper.PositiveChainGeometry
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
The ordinary coordinate subtype maps continuously and measurably into the fresh chain metric.
-/

open Set Filter
open scoped BigOperators Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper
section
variable {n : ℕ} {C : Set (Option (Fin n) → ℝ)}
    (h0 : ∀ x ∈ C, ∀ i, 0 ≤ x i)
    (hp : ∀ x ∈ C, x = 0 ∨ ∀ i, 0 < x i)
    (hc : ∀ x ∈ C, ∀ y ∈ C, x ≤ y ∨ y ≤ x)

def positiveChainFromSubtype (x : C) : PositiveProductPoint C := ⟨x.val,x.property⟩

theorem positiveChainMetric_fromSubtype_continuous :
    letI := positiveChainMetric h0 hp hc
    Continuous (positiveChainFromSubtype : C → PositiveProductPoint C) := by
  classical
  letI := positiveChainMetric h0 hp hc
  have hcoord (j : Option (Fin n)) : Continuous (fun x : C => x.val j) :=
    (continuous_apply j).comp continuous_subtype_val
  have hΦ : Continuous (fun x : C => ∏ j, x.val j) := by
    fun_prop
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  rcases hp x.val x.property with hx0 | hxpos
  · have hz : (0 : Option (Fin n) → ℝ) ∈ C := by rw [← hx0]; exact x.property
    have he : positiveChainFromSubtype x = positiveChainOrigin hz :=
      positiveProductPoint_ext hx0
    filter_upwards [(Metric.continuousAt_iff'.mp (hcoord none).continuousAt) ε hε] with y hy
    rw [he,positiveChainMetric_origin_distance h0 hp hc hz]
    have hxnone : x.val none = 0 := congrFun hx0 none
    simpa only [positiveChainFromSubtype,Real.dist_eq,hxnone,sub_zero,
      abs_of_nonneg (h0 y.val y.property none)] using hy
  · have hP : 0 < ∏ i : Fin n, x.val (some i) := Finset.prod_pos (fun i _ => hxpos (some i))
    filter_upwards [(Metric.continuousAt_iff'.mp hΦ.continuousAt)
      (ε*(∏ i : Fin n, x.val (some i))) (mul_pos hε hP)] with y hy
    have hb := positiveChainMetric_le_product_gap h0 hp hc
      (positiveChainFromSubtype x) (positiveChainFromSubtype y) hP
    rw [dist_comm] at hb
    apply hb.trans_lt
    apply (div_lt_iff₀ hP).mpr
    simpa only [positiveChainFromSubtype,Real.dist_eq,abs_sub_comm] using hy

theorem positiveChainMetric_fromSubtype_measurable :
    letI := positiveChainMetric h0 hp hc
    @Measurable C (PositiveProductPoint C) _ (borel (PositiveProductPoint C))
      positiveChainFromSubtype := by
  letI := positiveChainMetric h0 hp hc
  letI : MeasurableSpace (PositiveProductPoint C) := borel (PositiveProductPoint C)
  letI : BorelSpace (PositiveProductPoint C) := ⟨rfl⟩
  exact (positiveChainMetric_fromSubtype_continuous h0 hp hc).measurable

end
end ScalarMonotone.EndOfPaper
end
