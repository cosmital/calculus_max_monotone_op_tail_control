import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
Actual positive-density CDF primitives, for the one-dimensional transport proof of the Gaussian midpoint integral inequality.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

def positiveDensityCDF (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ t in Iic (0 : ℝ), f t)+(∫ t in (0 : ℝ)..x, f t)

theorem positive_density_cdf_eq_Iic {f : ℝ → ℝ} (hi : Integrable f volume) (x : ℝ) :
    positiveDensityCDF f x = ∫ t in Iic x, f t := by
  have hh := intervalIntegral.integral_Iic_sub_Iic
    (a := (0 : ℝ)) (b := x) hi.integrableOn hi.integrableOn
  unfold positiveDensityCDF
  rw [← hh]
  ring

theorem positive_density_cdf_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (positiveDensityCDF f) (f x) x := by
  exact (hf.integral_hasStrictDerivAt 0 x).hasDerivAt.const_add _

theorem positive_density_cdf_hasStrictDerivAt {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasStrictDerivAt (positiveDensityCDF f) (f x) x :=
  (hf.integral_hasStrictDerivAt 0 x).const_add _

theorem positive_density_cdf_strictMono {f : ℝ → ℝ} (hf : Continuous f) (hp : ∀ x, 0 < f x) :
    StrictMono (positiveDensityCDF f) :=
  strictMono_of_hasDerivAt_pos (positive_density_cdf_hasDerivAt hf) hp

theorem positive_density_cdf_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (positiveDensityCDF f) :=
  continuous_iff_continuousAt.mpr (fun x => (positive_density_cdf_hasDerivAt hf x).continuousAt)

theorem positive_density_cdf_atBot {f : ℝ → ℝ} (hi : Integrable f volume) :
    Tendsto (positiveDensityCDF f) atBot (𝓝 0) := by
  have hh := intervalIntegral_tendsto_integral_Iic (0 : ℝ) hi.integrableOn tendsto_id
  have hlim : Tendsto (fun x : ℝ => (∫ t in Iic (0 : ℝ), f t)-(∫ t in x..0, f t)) atBot
      (𝓝 ((∫ t in Iic (0 : ℝ), f t)-(∫ t in Iic (0 : ℝ), f t))) := tendsto_const_nhds.sub hh
  have he (x : ℝ) : positiveDensityCDF f x = (∫ t in Iic (0 : ℝ), f t)-(∫ t in x..0, f t) := by
    unfold positiveDensityCDF
    rw [intervalIntegral.integral_symm 0 x]
    ring
  simpa only [← he,sub_self] using hlim

theorem positive_density_cdf_atTop {f : ℝ → ℝ} (hi : Integrable f volume) :
    Tendsto (positiveDensityCDF f) atTop (𝓝 (∫ t : ℝ, f t)) := by
  have hh := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hi.integrableOn tendsto_id
  have hlim : Tendsto (positiveDensityCDF f) atTop
      (𝓝 ((∫ t in Iic (0 : ℝ), f t)+(∫ t in Ioi (0 : ℝ), f t))) := tendsto_const_nhds.add hh
  rwa [intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn] at hlim

theorem positive_density_cdf_mem {f : ℝ → ℝ} (hf : Continuous f) (hp : ∀ x, 0 < f x)
    (hi : Integrable f volume) (x : ℝ) :
    positiveDensityCDF f x ∈ Ioo (0 : ℝ) (∫ t : ℝ, f t) := by
  have hs := positive_density_cdf_strictMono hf hp
  have hlow (a : ℝ) : 0 ≤ positiveDensityCDF f a :=
    le_of_tendsto (positive_density_cdf_atBot hi)
      ((eventually_le_atBot a).mono (fun _ hy => hs.monotone hy))
  have hupp (a : ℝ) : positiveDensityCDF f a ≤ ∫ t : ℝ, f t :=
    ge_of_tendsto (positive_density_cdf_atTop hi)
      ((eventually_ge_atTop a).mono (fun _ hy => hs.monotone hy))
  exact ⟨(hlow (x-1)).trans_lt (hs (by linarith)),(hs (lt_add_one x)).trans_le (hupp (x+1))⟩

theorem positive_density_cdf_range {f : ℝ → ℝ} (hf : Continuous f) (hp : ∀ x, 0 < f x)
    (hi : Integrable f volume) :
    range (positiveDensityCDF f) = Ioo (0 : ℝ) (∫ t : ℝ, f t) := by
  ext u
  constructor
  · rintro ⟨x,rfl⟩
    exact positive_density_cdf_mem hf hp hi x
  · intro hu
    have hl : ∃ x, positiveDensityCDF f x ≤ u := by
      have hh := (positive_density_cdf_atBot hi).eventually (gt_mem_nhds hu.1)
      obtain ⟨x,hx⟩ := hh.exists
      exact ⟨x,hx.le⟩
    have hr : ∃ x, u ≤ positiveDensityCDF f x := by
      have hh := (positive_density_cdf_atTop hi).eventually (lt_mem_nhds hu.2)
      obtain ⟨x,hx⟩ := hh.exists
      exact ⟨x,hx.le⟩
    exact mem_range_of_exists_le_of_exists_ge (positive_density_cdf_continuous hf) hl hr

theorem positive_density_mass_positive {f : ℝ → ℝ} (hf : Continuous f) (hp : ∀ x, 0 < f x)
    (hi : Integrable f volume) : 0 < ∫ t : ℝ, f t :=
  (positive_density_cdf_mem hf hp hi 0).1.trans (positive_density_cdf_mem hf hp hi 0).2

end ScalarMonotone.EndOfPaper
end
