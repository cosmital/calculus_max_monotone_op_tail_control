import EndOfPaper.MaxMedianControlProfile
import EndOfPaper.InitialProfileAffine
import EndOfPaper.GeometricScalarCompletion
import EndOfPaper.RandomizedProfileData

/-!
Exact u/12 geometric dilation and whole scalar/output completion and finite-product congruence bridges.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem half_affine_geometric_network_level {q : DecGraph}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ t ∈ q.val x, 0 ≤ t)
    {s : ℝ → ℝ} (hsm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    (hP : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞)
    {m c u : ℝ} (hm : 0 ≤ m) (hc : 0 ≤ c) (hu : u ∈ Ioo (0 : ℝ) 1) :
    geometricPrefixValue (fun x => m+c*s (x/2)) (u/6) =
      geometricPrefixValue (fun x => m+c*s x) (u/12) := by
  let r := completedProfileAffine 1 m c q (by norm_num) hqi hc
  have hr0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ t ∈ r.val x, 0 ≤ t :=
    completedProfileAffine_nonnegative (by norm_num) hqi hm hc hq0
  have hrs : SelectionOn r.val (Ioo (0 : ℝ) 1) (fun x => m+c*s x) :=
    completedProfileAffine_selection (by norm_num) hqi hc hs
  have hrP := positive_log_area_affine_finite hsm (fun x hx => hq0 x hx _ (hs x hx)) hP hm hc
  have he := geometricPrefixValue_positive_dilation hr0 (by fun_prop) hrs hrP
    (by norm_num : (0 : ℝ) < 1/2) (by linarith [hu.1] : 0 < u/6)
    (show (1/2)*(u/6) ∈ Ioo (0 : ℝ) 1 by constructor <;> linarith [hu.1,hu.2])
  have hfn : (fun x : ℝ => m+c*s ((1/2)*x)) = (fun x => m+c*s (x/2)) := by
    funext x
    have hx : (1/2 : ℝ)*x = x/2 := by ring
    rw [hx]
  have harg : (1/2 : ℝ)*(u/6) = u/12 := by ring
  change geometricPrefixValue (fun x => m+c*s ((1/2)*x)) (u/6) =
    geometricPrefixValue (fun x => m+c*s x) ((1/2)*(u/6)) at he
  rw [hfn,harg] at he
  exact he

theorem positive_output_initial_scalar_completion {q : DecGraph}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    {s : ℝ → ℝ} (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    {c : ℝ} (hc : 0 < c) :
    outputScale c q.val = completedDecreasingRestriction (Ioo (0 : ℝ) 1)
      (ofFun (fun x => c*s x)) := by
  apply initial_profile_eq_completed_scalar (by norm_num)
    (outputScale_maximal_decreasing hc q.property)
  · rw [dom_outputScale]
    exact hqi
  · intro x hx
    exact ⟨s x,hs x hx,rfl⟩

theorem geometric_product_dilation_selection {ι : Type*} [Fintype ι]
    {qδ : DecGraph} (hδdom : interior (dom qδ.val) = Ioo (0 : ℝ) 1)
    (hδ0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ qδ.val x, 0 ≤ v)
    {q : ι → DecGraph} (hqdom : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ i x, x ∈ Ioo (0 : ℝ) 1 → ∀ v ∈ (q i).val x, 0 ≤ v)
    {sδ : ℝ → ℝ} (hsδ : SelectionOn qδ.val (Ioo (0 : ℝ) 1) sδ)
    {s : ι → ℝ → ℝ} (hs : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) 1) (s i))
    (hPi : ∀ i, (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (max (Real.log (s i x)) 0)) < ∞)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    let G := geometricFiniteProfileProduct q hqdom hq0 hs hPi
    let hG := geometricFiniteProfileProduct_properties hqdom hq0 hs hPi
    let P := completedProfileProduct 1 qδ G (by norm_num) hδdom hG.1 hδ0 hG.2.1
    let hPD := (completedProfileProduct_domain (by norm_num) hδdom hG.1 hδ0 hG.2.1).1
    let D := completedProfileDilation 1 1 c P hPD (by norm_num) hc (by simpa only [mul_one] using hc1)
    SelectionOn D.val (Ioo (0 : ℝ) 1)
      (fun x => sδ (c*x)*(∏ i, geometricPrefixValue (s i) (c*x))) := by
  let G := geometricFiniteProfileProduct q hqdom hq0 hs hPi
  have hG := geometricFiniteProfileProduct_properties hqdom hq0 hs hPi
  let P := completedProfileProduct 1 qδ G (by norm_num) hδdom hG.1 hδ0 hG.2.1
  have hPD := (completedProfileProduct_domain (by norm_num) hδdom hG.1 hδ0 hG.2.1).1
  let D := completedProfileDilation 1 1 c P hPD (by norm_num) hc (by simpa only [mul_one] using hc1)
  have hD : ∀ x ∈ Ioo (0 : ℝ) 1, D.val x = P.val (c*x) :=
    (completedProfileDilation_properties hPD (by norm_num : (0 : ℝ) < 1) hc
      (by simpa only [mul_one] using hc1)).2
  have hsP : SelectionOn P.val (Ioo (0 : ℝ) 1)
      (fun x => sδ x*(∏ i, geometricPrefixValue (s i) x)) :=
    completedProfileProduct_selection (by norm_num) hδdom hG.1 hδ0 hG.2.1 hsδ hG.2.2
  change SelectionOn D.val (Ioo (0 : ℝ) 1)
    (fun x => sδ (c*x)*(∏ i, geometricPrefixValue (s i) (c*x)))
  intro x hx
  rw [hD x hx]
  exact hsP (c*x) (initial_dilation_mapsTo hc (by simpa only [mul_one] using hc1) hx)

theorem interiorFiniteProfileProduct_congr_on {ι : Type*} [Fintype ι]
    {B : ℝ} {f g : ι → Operator}
    (h : ∀ i x, x ∈ Ioo (0 : ℝ) B → f i x = g i x) :
    interiorFiniteProfileProduct B f = interiorFiniteProfileProduct B g := by
  funext x
  ext v
  constructor
  · rintro ⟨hx,a,ha,hv⟩
    exact ⟨hx,a,fun i => by rw [← h i x hx]; exact ha i,hv⟩
  · rintro ⟨hx,a,ha,hv⟩
    exact ⟨hx,a,fun i => by rw [h i x hx]; exact ha i,hv⟩

end ScalarMonotone.EndOfPaper
end
