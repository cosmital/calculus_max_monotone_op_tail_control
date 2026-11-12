import EndOfPaper.PositiveDensityCDF
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
The actual monotone CDF transport between positive continuous probability densities, including the inverse derivative and exact density ratio.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

def densityTransport (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  Function.invFun (positiveDensityCDF g) (positiveDensityCDF f x)

section
variable {f g : ℝ → ℝ} (hf : Continuous f) (hfp : ∀ x, 0 < f x) (hfi : Integrable f volume)
    (hfmass : (∫ x : ℝ, f x) = 1) (hg : Continuous g) (hgp : ∀ x, 0 < g x)
    (hgi : Integrable g volume) (hgmass : (∫ x : ℝ, g x) = 1)
include hf hfp hfi hfmass hg hgp hgi hgmass

theorem density_transport_cdf (x : ℝ) :
    positiveDensityCDF g (densityTransport f g x) = positiveDensityCDF f x := by
  have hu : positiveDensityCDF f x ∈ Ioo (0 : ℝ) 1 := by
    simpa only [hfmass] using positive_density_cdf_mem hf hfp hfi x
  have hex : ∃ y, positiveDensityCDF g y = positiveDensityCDF f x := by
    change positiveDensityCDF f x ∈ range (positiveDensityCDF g)
    rwa [positive_density_cdf_range hg hgp hgi,hgmass]
  exact Function.invFun_eq hex

theorem density_transport_hasStrictDerivAt (x : ℝ) :
    HasStrictDerivAt (densityTransport f g) (f x/g (densityTransport f g x)) x := by
  have hleft : ∀ y, Function.invFun (positiveDensityCDF g) (positiveDensityCDF g y) = y :=
    Function.leftInverse_invFun (positive_density_cdf_strictMono hg hgp).injective
  have hInv := (positive_density_cdf_hasStrictDerivAt hg (densityTransport f g x)).to_local_left_inverse
    (hgp (densityTransport f g x)).ne' (Eventually.of_forall hleft)
  rw [density_transport_cdf hf hfp hfi hfmass hg hgp hgi hgmass x] at hInv
  have hComp := hInv.comp x (positive_density_cdf_hasStrictDerivAt hf x)
  simpa only [densityTransport,Function.comp_def,div_eq_mul_inv,mul_comm] using hComp

theorem density_transport_continuous : Continuous (densityTransport f g) :=
  continuous_iff_continuousAt.mpr (fun x =>
    (density_transport_hasStrictDerivAt hf hfp hfi hfmass hg hgp hgi hgmass x).continuousAt)

theorem density_transport_strictMono : StrictMono (densityTransport f g) :=
  strictMono_of_hasDerivAt_pos
    (fun x => (density_transport_hasStrictDerivAt hf hfp hfi hfmass hg hgp hgi hgmass x).hasDerivAt)
    (fun x => div_pos (hfp x) (hgp _))

theorem density_transport_surjective : Function.Surjective (densityTransport f g) := by
  intro y
  have hu : positiveDensityCDF g y ∈ Ioo (0 : ℝ) 1 := by
    simpa only [hgmass] using positive_density_cdf_mem hg hgp hgi y
  have hex : ∃ x, positiveDensityCDF f x = positiveDensityCDF g y := by
    change positiveDensityCDF g y ∈ range (positiveDensityCDF f)
    rwa [positive_density_cdf_range hf hfp hfi,hfmass]
  obtain ⟨x,hx⟩ := hex
  refine ⟨x,?_⟩
  unfold densityTransport
  rw [hx]
  exact Function.leftInverse_invFun (positive_density_cdf_strictMono hg hgp).injective y

end
end ScalarMonotone.EndOfPaper
end
