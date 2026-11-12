import MonotoneOperators.Survival
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Exact affine uniform segment laws and their two-way mixture.
Measurable quantile maps preserve the exact splitting identity,
including arbitrary atoms in the resulting marginal laws.
-/

open Set MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem affine_uniform_segment {b c : ℝ} (hc : 0 < c) :
    ENNReal.ofReal c • Measure.map (fun u : ℝ => b+c*u) unitUniform =
      volume.restrict (Ioo b (b+c)) := by
  have hm : Measurable (fun u : ℝ => b+c*u) := by fun_prop
  have hpre : (fun u : ℝ => b+c*u) ⁻¹' Ioo b (b+c) = Ioo 0 1 := by
    ext u
    constructor
    · intro hu
      change b < b+c*u ∧ b+c*u < b+c at hu
      constructor <;> nlinarith
    · intro hu
      change b < b+c*u ∧ b+c*u < b+c
      constructor <;> nlinarith [hu.1, hu.2]
  have htotal : ENNReal.ofReal c • Measure.map (fun u : ℝ => b+c*u) volume =
      (volume : Measure ℝ) := by
    have hmul := Real.smul_map_volume_mul_left hc.ne'
    rw [abs_of_pos hc] at hmul
    calc
      ENNReal.ofReal c • Measure.map (fun u : ℝ => b+c*u) volume =
          Measure.map (fun u : ℝ => b+u)
            (ENNReal.ofReal c • Measure.map (fun u : ℝ => c*u) volume) := by
        rw [Measure.map_smul, Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = volume := by rw [hmul, map_add_left_eq_self]
  calc
    ENNReal.ofReal c • Measure.map (fun u : ℝ => b+c*u) unitUniform =
        (ENNReal.ofReal c • Measure.map (fun u : ℝ => b+c*u) volume).restrict
          (Ioo b (b+c)) := by
      rw [Measure.restrict_smul, Measure.restrict_map hm measurableSet_Ioo, hpre]
      rfl
    _ = volume.restrict (Ioo b (b+c)) := by rw [htotal]

theorem uniform_split {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ENNReal.ofReal p • Measure.map (fun u : ℝ => p*u) unitUniform +
      ENNReal.ofReal (1-p) • Measure.map (fun u : ℝ => p+(1-p)*u) unitUniform =
        unitUniform := by
  have hleft := affine_uniform_segment (b := 0) hp.1
  have hright := affine_uniform_segment (b := p) (by linarith [hp.2] : 0 < 1-p)
  simp only [zero_add] at hleft
  have hend : p+(1-p) = 1 := by ring
  rw [hleft, hright, hend]
  change volume.restrict (Ioo 0 p) + volume.restrict (Ioo p 1) =
    volume.restrict (Ioo 0 1)
  rw [restrict_Ioo_eq_restrict_Ioc, restrict_Ioo_eq_restrict_Ioc,
    restrict_Ioo_eq_restrict_Ioc]
  rw [← Measure.restrict_union (by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy.1) measurableSet_Ioc]
  congr 1
  ext x
  constructor
  · rintro (hx | hx)
    · exact ⟨hx.1, hx.2.trans hp.2.le⟩
    · exact ⟨hp.1.trans hx.1, hx.2⟩
  · intro hx
    by_cases hxp : x ≤ p
    · exact Or.inl ⟨hx.1, hxp⟩
    · exact Or.inr ⟨lt_of_not_ge hxp, hx.2⟩

theorem quantile_law_split {p : ℝ} (hp : p ∈ Ioo 0 1)
    {q : ℝ → ℝ} (hq : Measurable q) :
    ENNReal.ofReal p • Measure.map (fun u : ℝ => q (p*u)) unitUniform +
      ENNReal.ofReal (1-p) • Measure.map (fun u : ℝ => q (p+(1-p)*u)) unitUniform =
        Measure.map q unitUniform := by
  change ENNReal.ofReal p • Measure.map (q ∘ (fun u : ℝ => p*u)) unitUniform +
    ENNReal.ofReal (1-p) • Measure.map (q ∘ (fun u : ℝ => p+(1-p)*u)) unitUniform = _
  rw [← Measure.map_map hq (by fun_prop), ← Measure.map_map hq (by fun_prop)]
  calc
    _ = Measure.map q (ENNReal.ofReal p • Measure.map (fun u : ℝ => p*u) unitUniform +
        ENNReal.ofReal (1-p) • Measure.map (fun u : ℝ => p+(1-p)*u) unitUniform) := by
      rw [Measure.map_add _ _ hq, Measure.map_smul, Measure.map_smul]
    _ = Measure.map q unitUniform := by rw [uniform_split hp]

end ScalarMonotone.EndOfPaper
end
