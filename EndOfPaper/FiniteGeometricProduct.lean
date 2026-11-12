import EndOfPaper.GeometricProduct
import EndOfPaper.FiniteProfileProduct

/-!
Finite geometric-prefix multiplicativity and the whole
geometric Hardy finite-product law for the literal completed
interior products. Zeros and infinite negative-log area are retained.
-/

open Set Filter MeasureTheory
open scoped ENNReal BigOperators Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem positive_log_area_finset_prod_finite {ι : Type*} {s : ι → ℝ → ℝ} {B : ℝ}
    (hm : ∀ i, Measurable (s i)) (hs0 : ∀ i x, x ∈ Ioo (0 : ℝ) B → 0 ≤ s i x)
    (hP : ∀ i, (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s i x)) 0)) < ∞)
    (S : Finset ι) :
    (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (∏ i ∈ S, s i x)) 0)) < ∞ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Real.log_one,max_self,ENNReal.ofReal_zero,lintegral_zero]; exact ENNReal.zero_lt_top
  | @insert i S hi ih =>
      have hprodM : Measurable (fun x => ∏ j ∈ S, s j x) := by fun_prop
      have hprod0 : ∀ x ∈ Ioo (0 : ℝ) B, 0 ≤ ∏ j ∈ S, s j x :=
        fun x hx => Finset.prod_nonneg (fun j _ => hs0 j x hx)
      simpa only [Finset.prod_insert hi] using
        positive_log_area_mul_finite (hm i) hprodM (hs0 i) hprod0 (hP i) ih

theorem geometricPrefixValue_one {p : ℝ} (hp : 0 < p) :
    geometricPrefixValue (fun _ : ℝ => 1) p = 1 := by
  have hi : IntervalIntegrable (fun _x : ℝ => Real.log 1) volume 0 p := intervalIntegrable_const
  rw [geometricPrefixValue_of_integrable hp hi (fun _ _ => zero_lt_one)]
  simp only [Real.log_one,hardyScalar,intervalIntegral.integral_zero,zero_div,Real.exp_zero]

theorem geometricPrefixValue_finset_prod {ι : Type*} {q : ι → DecGraph}
    {s : ι → ℝ → ℝ} {B p : ℝ} (hB : 0 < B)
    (hqi : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ i x, x ∈ Ioo (0 : ℝ) B → ∀ v ∈ (q i).val x, 0 ≤ v)
    (hm : ∀ i, Measurable (s i)) (hs : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) B) (s i))
    (hP : ∀ i, (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s i x)) 0)) < ∞)
    (hp : p ∈ Ioo (0 : ℝ) B) (S : Finset ι) :
    geometricPrefixValue (fun x => ∏ i ∈ S, s i x) p = ∏ i ∈ S, geometricPrefixValue (s i) p := by
  classical
  have hs0 : ∀ i x, x ∈ Ioo (0 : ℝ) B → 0 ≤ s i x :=
    fun i x hx => hq0 i x hx (s i x) (hs i x hx)
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using geometricPrefixValue_one hp.1
  | @insert i S hi ih =>
      have hprodM : Measurable (fun x => ∏ j ∈ S, s j x) := by fun_prop
      have hprod0 : ∀ x ∈ Ioo (0 : ℝ) B, 0 ≤ ∏ j ∈ S, s j x :=
        fun x hx => Finset.prod_nonneg (fun j _ => hs0 j x hx)
      let qS : DecGraph := completedFiniteProfileProduct B (fun j : S => q j) hB
        (fun j => hqi j) (fun j => hq0 j)
      have hQS0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ qS.val x, 0 ≤ v :=
        completedFiniteProfileProduct_nonnegative hB (fun j : S => hqi j) (fun j => hq0 j)
      have hQSel : SelectionOn qS.val (Ioo (0 : ℝ) B) (fun x => ∏ j ∈ S, s j x) := by
        have hsel := completedFiniteProfileProduct_selection hB (fun j : S => hqi j)
          (fun j => hq0 j) (fun j => hs j)
        intro x hx
        have he : (∏ j : S, s j x) = ∏ j ∈ S, s j x := Finset.prod_coe_sort S (fun j => s j x)
        change (∏ j ∈ S, s j x) ∈ qS.val x
        rw [← he]
        exact hsel x hx
      have he := geometricPrefixValue_mul (hq0 i) hQS0 (hm i) hprodM (hs i) hQSel (hP i)
        (positive_log_area_finset_prod_finite hm hs0 hP S) hp
      simpa only [Finset.prod_insert hi,ih] using he

theorem geometricPrefixValue_finite_product {ι : Type*} [Fintype ι]
    {q : ι → DecGraph} {s : ι → ℝ → ℝ} {B p : ℝ} (hB : 0 < B)
    (hqi : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ i x, x ∈ Ioo (0 : ℝ) B → ∀ v ∈ (q i).val x, 0 ≤ v)
    (hs : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) B) (s i))
    (hPi : ∀ i, (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s i x)) 0)) < ∞)
    (hp : p ∈ Ioo (0 : ℝ) B) :
    geometricPrefixValue (fun x => ∏ i, s i x) p = ∏ i, geometricPrefixValue (s i) p := by
  classical
  choose t hmt hts harea using fun i => measurable_selection_same_positive_log_area (hqi i) (hs i)
  have hPt (i : ι) : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (t i x)) 0)) < ∞ := by
    rw [harea i]
    exact hPi i
  have he (i : ι) : t i =ᵐ[volume.restrict (Ioo (0 : ℝ) B)] s i :=
    decreasing_selections_ae_eq (q i).property.1 (hts i) (hs i) volume measurableSet_Ioo
  have heAll : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) B)), ∀ i, t i x = s i x := ae_all_iff.mpr he
  have heProd : (fun x => ∏ i, t i x) =ᵐ[volume.restrict (Ioo (0 : ℝ) B)] (fun x => ∏ i, s i x) := by
    filter_upwards [heAll] with x hx
    simp only [hx]
  calc
    _ = geometricPrefixValue (fun x => ∏ i, t i x) p :=
      (geometricPrefixValue_congr_ae heProd hp.2.le).symm
    _ = ∏ i, geometricPrefixValue (t i) p :=
      geometricPrefixValue_finset_prod hB hqi hq0 hmt hts hPt hp Finset.univ
    _ = _ := Finset.prod_congr rfl (fun i _ => geometricPrefixValue_congr_ae (he i) hp.2.le)

theorem geometric_hardy_finite_product {ι : Type*} [Fintype ι]
    {q : ι → DecGraph} {B : ℝ} (hB : 0 < B)
    (hqi : ∀ i, interior (dom (q i).val) = Ioo (0 : ℝ) B)
    (hq0 : ∀ i x, x ∈ Ioo (0 : ℝ) B → ∀ v ∈ (q i).val x, 0 ≤ v)
    {s : ι → ℝ → ℝ} (hs : ∀ i, SelectionOn (q i).val (Ioo (0 : ℝ) B) (s i))
    (hPi : ∀ i, (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s i x)) 0)) < ∞) :
    let P := completedFiniteProfileProduct B q hB hqi hq0
    let hGi := fun i => geometricHardyTransform_well_defined_any_selection hB (hqi i) (hq0 i) (hs i) (hPi i)
    let G : ι → DecGraph := fun i => ⟨geometricHardyTransform B (q i),(hGi i).1⟩
    geometricHardyTransform B P =
      (completedFiniteProfileProduct B G hB (fun i => (hGi i).2.1) (fun i => (hGi i).2.2.1)).val := by
  classical
  dsimp only
  choose t hmt hts harea using fun i => measurable_selection_same_positive_log_area (hqi i) (hs i)
  have hPt (i : ι) : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (t i x)) 0)) < ∞ := by
    rw [harea i]
    exact hPi i
  let P := completedFiniteProfileProduct B q hB hqi hq0
  have hPD : interior (dom P.val) = Ioo (0 : ℝ) B := (completedFiniteProfileProduct_domain hB hqi hq0).1
  have hP0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ P.val x, 0 ≤ v :=
    completedFiniteProfileProduct_nonnegative hB hqi hq0
  have hsP : SelectionOn P.val (Ioo (0 : ℝ) B) (fun x => ∏ i, t i x) :=
    completedFiniteProfileProduct_selection hB hqi hq0 hts
  have hPP := positive_log_area_finset_prod_finite hmt
    (fun i x hx => hq0 i x hx (t i x) (hts i x hx)) hPt Finset.univ
  have hMP : Measurable (fun x => ∏ i, t i x) := by fun_prop
  have hGP := geometricHardyTransform_well_defined hB hPD hP0 hMP hsP hPP
  have hphiP := geometric_hardy_scalar_selection hB hPD hP0 hsP hPP
  have hGi := fun i => geometricHardyTransform_well_defined hB (hqi i) (hq0 i) (hmt i) (hts i) (hPt i)
  let G : ι → DecGraph := fun i => ⟨geometricHardyTransform B (q i),(hGi i).1⟩
  let outP := completedFiniteProfileProduct B G hB (fun i => (hGi i).2.1) (fun i => (hGi i).2.2.1)
  have houtD : interior (dom outP.val) = Ioo (0 : ℝ) B :=
    (completedFiniteProfileProduct_domain hB (fun i => (hGi i).2.1) (fun i => (hGi i).2.2.1)).1
  have hphiG (i : ι) : SelectionOn (G i).val (Ioo (0 : ℝ) B) (geometricPrefixValue (t i)) :=
    geometric_hardy_scalar_selection hB (hqi i) (hq0 i) (hts i) (hPt i)
  have hphiOut : SelectionOn outP.val (Ioo (0 : ℝ) B)
      (fun x => ∏ i, geometricPrefixValue (t i) x) :=
    completedFiniteProfileProduct_selection hB (fun i => (hGi i).2.1)
      (fun i => (hGi i).2.2.1) hphiG
  have he : geometricPrefixValue (fun x => ∏ i, t i x) =ᵐ[volume.restrict (Ioo (0 : ℝ) B)]
      (fun x => ∏ i, geometricPrefixValue (t i) x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact geometricPrefixValue_finset_prod hB hqi hq0 hmt hts hPt hx Finset.univ
  change geometricHardyTransform B P = outP.val
  exact initial_profile_eq_of_selection_ae_eq hB hGP.1 outP.property hGP.2.1 houtD hphiP hphiOut he

end ScalarMonotone.EndOfPaper
end
