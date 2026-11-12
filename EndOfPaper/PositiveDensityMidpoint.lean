import EndOfPaper.PositiveDensityTransport
import Mathlib.MeasureTheory.Function.Jacobian

/-!
The actual midpoint of the identity and monotone density transport, with positive Jacobian, full range and genuine change of variables.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

def densityMidpointTransport (f g : ℝ → ℝ) (x : ℝ) : ℝ := (x+densityTransport f g x)/2
def densityMidpointJacobian (f g : ℝ → ℝ) (x : ℝ) : ℝ := (1+f x/g (densityTransport f g x))/2

section
variable {f g : ℝ → ℝ} (hf : Continuous f) (hfp : ∀ x, 0 < f x) (hfi : Integrable f volume)
    (hfmass : (∫ x : ℝ, f x) = 1) (hg : Continuous g) (hgp : ∀ x, 0 < g x)
    (hgi : Integrable g volume) (hgmass : (∫ x : ℝ, g x) = 1)
include hf hfp hfi hfmass hg hgp hgi hgmass

theorem density_midpoint_hasStrictDerivAt (x : ℝ) :
    HasStrictDerivAt (densityMidpointTransport f g) (densityMidpointJacobian f g x) x :=
  ((hasStrictDerivAt_id x).add
    (density_transport_hasStrictDerivAt hf hfp hfi hfmass hg hgp hgi hgmass x)).div_const 2

theorem density_midpoint_jacobian_positive (x : ℝ) : 0 < densityMidpointJacobian f g x :=
  div_pos (add_pos (by norm_num) (div_pos (hfp x) (hgp _))) (by norm_num)

theorem density_midpoint_continuous : Continuous (densityMidpointTransport f g) :=
  continuous_iff_continuousAt.mpr (fun x =>
    (density_midpoint_hasStrictDerivAt hf hfp hfi hfmass hg hgp hgi hgmass x).continuousAt)

theorem density_midpoint_strictMono : StrictMono (densityMidpointTransport f g) :=
  strictMono_of_hasDerivAt_pos
    (fun x => (density_midpoint_hasStrictDerivAt hf hfp hfi hfmass hg hgp hgi hgmass x).hasDerivAt)
    (density_midpoint_jacobian_positive hf hfp hfi hfmass hg hgp hgi hgmass)

theorem density_midpoint_atTop : Tendsto (densityMidpointTransport f g) atTop atTop := by
  have hT := density_transport_strictMono hf hfp hfi hfmass hg hgp hgi hgmass
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (max 0 (2*b-densityTransport f g 0))] with x hx
  have hx0 : 0 ≤ x := (le_max_left _ _).trans hx
  have hxb : 2*b-densityTransport f g 0 ≤ x := (le_max_right _ _).trans hx
  have hh := hT.monotone hx0
  change b ≤ (x+densityTransport f g x)/2
  linarith only [hxb,hh]

theorem density_midpoint_atBot : Tendsto (densityMidpointTransport f g) atBot atBot := by
  have hT := density_transport_strictMono hf hfp hfi hfmass hg hgp hgi hgmass
  apply tendsto_atBot.2
  intro b
  filter_upwards [eventually_le_atBot (min 0 (2*b-densityTransport f g 0))] with x hx
  have hx0 : x ≤ 0 := hx.trans (min_le_left _ _)
  have hxb : x ≤ 2*b-densityTransport f g 0 := hx.trans (min_le_right _ _)
  have hh := hT.monotone hx0
  change (x+densityTransport f g x)/2 ≤ b
  linarith only [hxb,hh]

theorem density_midpoint_surjective : Function.Surjective (densityMidpointTransport f g) := by
  intro y
  have hl : ∃ x, densityMidpointTransport f g x ≤ y :=
    ((density_midpoint_atBot hf hfp hfi hfmass hg hgp hgi hgmass).eventually (eventually_le_atBot y)).exists
  have hr : ∃ x, y ≤ densityMidpointTransport f g x :=
    ((density_midpoint_atTop hf hfp hfi hfmass hg hgp hgi hgmass).eventually (eventually_ge_atTop y)).exists
  exact mem_range_of_exists_le_of_exists_ge
    (density_midpoint_continuous hf hfp hfi hfmass hg hgp hgi hgmass) hl hr

theorem density_midpoint_change_variables (H : ℝ → ℝ) :
    (∫ y : ℝ, H y) = ∫ x : ℝ, densityMidpointJacobian f g x*H (densityMidpointTransport f g x) := by
  have hSurj := density_midpoint_surjective hf hfp hfi hfmass hg hgp hgi hgmass
  have hImage : densityMidpointTransport f g '' (univ : Set ℝ) = univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨x,hx⟩ := hSurj y
      exact ⟨x,mem_univ x,hx⟩
  have hPos := density_midpoint_jacobian_positive hf hfp hfi hfmass hg hgp hgi hgmass
  have hh := integral_image_eq_integral_abs_deriv_smul (s := (univ : Set ℝ)) MeasurableSet.univ
    (fun x _ => (density_midpoint_hasStrictDerivAt hf hfp hfi hfmass hg hgp hgi hgmass x).hasDerivAt.hasDerivWithinAt)
    (density_midpoint_strictMono hf hfp hfi hfmass hg hgp hgi hgmass).injective.injOn H
  simpa only [hImage,Measure.restrict_univ,abs_of_pos (hPos _),smul_eq_mul] using hh

theorem density_midpoint_pullback_integrable {H : ℝ → ℝ} (hH : Integrable H volume) :
    Integrable (fun x : ℝ => densityMidpointJacobian f g x*H (densityMidpointTransport f g x)) volume := by
  have hSurj := density_midpoint_surjective hf hfp hfi hfmass hg hgp hgi hgmass
  have hImage : densityMidpointTransport f g '' (univ : Set ℝ) = univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨x,hx⟩ := hSurj y
      exact ⟨x,mem_univ x,hx⟩
  have hPos := density_midpoint_jacobian_positive hf hfp hfi hfmass hg hgp hgi hgmass
  have hh := integrableOn_image_iff_integrableOn_abs_deriv_smul (s := (univ : Set ℝ)) MeasurableSet.univ
    (fun x _ => (density_midpoint_hasStrictDerivAt hf hfp hfi hfmass hg hgp hgi hgmass x).hasDerivAt.hasDerivWithinAt)
    (density_midpoint_strictMono hf hfp hfi hfmass hg hgp hgi hgmass).injective.injOn H
  simp only [hImage,IntegrableOn,Measure.restrict_univ,abs_of_pos (hPos _),smul_eq_mul] at hh
  exact hh.mp hH

end
end ScalarMonotone.EndOfPaper
end
