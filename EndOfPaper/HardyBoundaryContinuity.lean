import EndOfPaper.LocalHardy
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Continuity of finite-prefix Hardy means and the actual
completed right endpoint ray. Only prefix L1 is imposed.
-/

open Set Filter MeasureTheory
open scoped Interval Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem hardyScalar_tendsto_left_of_intervalIntegrable {f : ℝ → ℝ} {p : ℝ}
    (hp : 0 < p) (hi : IntervalIntegrable f volume 0 p) :
    Tendsto (hardyScalar f) (𝓝[<] p) (𝓝 (hardyScalar f p)) := by
  have hC := intervalIntegral.continuousOn_primitive_interval' hi
    (show (0 : ℝ) ∈ uIcc (0 : ℝ) p from left_mem_uIcc)
  have hc := hC p right_mem_uIcc
  rw [uIcc_of_le hp.le] at hc
  have hmem : Icc (0 : ℝ) p ∈ 𝓝[<] p := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hp)] with x hx hx0
    exact ⟨hx0.le,hx.le⟩
  have hfilter : 𝓝[<] p ≤ 𝓝[Icc (0 : ℝ) p] p :=
    le_inf nhdsWithin_le_nhds (Filter.le_principal_iff.mpr hmem)
  have hInt := hc.mono_left hfilter
  have hId : Tendsto (fun x : ℝ => x) (𝓝[<] p) (𝓝 p) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [hardyScalar] using hInt.div hId hp.ne'

theorem decreasing_right_boundary_fiber_of_tendsto {f : Operator} {b m : ℝ}
    (hb : 0 < b) (hf : MaximalDecreasing f) (hdom : dom f ⊆ Icc (0 : ℝ) b)
    {s : ℝ → ℝ} (hs : SelectionOn f (Ioo (0 : ℝ) b) s)
    (ht : Tendsto s (𝓝[<] b) (𝓝 m)) : f b = Iic m := by
  ext u
  constructor
  · intro hu
    have he : ∀ᶠ x in 𝓝[<] b, u ≤ s x := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hb)] with x hx hx0
      exact Decreasing.le_of_lt hf.1 (hs x ⟨hx0,hx⟩) hu hx
    exact isClosed_Ici.mem_of_tendsto ht he
  · intro hu
    change u ≤ m at hu
    apply (maximalDecreasing_iff_compatible.mp hf).2
    intro y v hv
    have hy : y ≤ b := (hdom ⟨v,hv⟩).2
    by_cases heq : y = b
    · rw [heq]
      simp
    · have hyb : y < b := lt_of_le_of_ne hy heq
      have he : ∀ᶠ x in 𝓝[<] b, s x ≤ v := by
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (max_lt hb hyb))] with x hx hxlo
        have hx0 : 0 < x := (le_max_left 0 y).trans_lt hxlo
        have hyx : y < x := (le_max_right 0 y).trans_lt hxlo
        exact Decreasing.le_of_lt hf.1 hv (hs x ⟨hx0,hx⟩) hyx
      have hmv : m ≤ v := isClosed_Iic.mem_of_tendsto ht he
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hy) (sub_nonpos.mpr (hu.trans hmv))

end ScalarMonotone.EndOfPaper
end
