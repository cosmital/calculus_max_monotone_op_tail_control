import EndOfPaper.HardyIntegral
import MonotoneOperators.Sums
import MonotoneOperators.OrderGeometry

/-!
Whole-operator Hardy calculus (prop:hardycalculus). Addition and positive
scaling are equalities of completed graphs. Order preservation includes
different initial averaging intervals and all boundary fibers; domain
inclusion and boundary comparison are derived from the original graph order.
-/

open Set Filter MeasureTheory
open scoped Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem decreasing_dom_subset_closure_interior {f : Operator} (hf : MaximalDecreasing f)
    (hne : (interior (dom f)).Nonempty) : dom f ⊆ closure (interior (dom f)) := by
  have hconv : Convex ℝ (dom f) := (decreasing_dom_ordConnected hf).convex
  have he := hconv.closure_interior_eq_closure_of_nonempty_interior hne
  rw [he]
  exact subset_closure

theorem zero_mem_closure_decreasing_domain_interior {f : Operator}
    (hf : MaximalDecreasing f) (hz : IsGLB (dom f) 0)
    (hne : (interior (dom f)).Nonempty) : 0 ∈ closure (interior (dom f)) := by
  have hconv : Convex ℝ (dom f) := (decreasing_dom_ordConnected hf).convex
  rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne]
  exact hz.mem_closure (hne.mono interior_subset)

theorem Ioo_between_closure_subset_open_interval {I : Set ℝ} (hI : IsOpen I)
    (hord : I.OrdConnected) (hne : I.Nonempty) {x y : ℝ}
    (hy : y ∈ closure I) (hx : x ∈ closure I) : Ioo y x ⊆ I := by
  have hconv : Convex ℝ I := hord.convex
  have hi : interior (closure I) = I := by
    simpa only [hI.interior_eq] using
      hconv.interior_closure_eq_interior_of_nonempty_interior
        (by simpa only [hI.interior_eq] using hne)
  have hs : Ioo y x ⊆ closure I := fun z hz =>
    hord.convex.closure.ordConnected.out hy hx ⟨hz.1.le, hz.2.le⟩
  have hs' : Ioo y x ⊆ interior (closure I) := isOpen_Ioo.subset_interior_iff.mpr hs
  simpa only [hi] using hs'

/-- Interior separated comparison extends to every boundary fiber of the
graphs. The two operators may have different upper domain endpoints. -/
theorem decLE_of_initial_interior {f g : Operator} (hf : Decreasing f) (hg : Decreasing g)
    {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) (hne : I.Nonempty)
    (hz : 0 ∈ closure I) (hfd : dom f ⊆ closure I) (hgd : dom g ⊆ Ici 0)
    (hIf : I ⊆ dom f) (hIg : I ⊆ dom g)
    (hsep : ∀ p ∈ I, ∀ q ∈ I, q < p →
      ∀ u ∈ f p, ∀ v ∈ g q, u ≤ v) : DecLE f g := by
  intro x u y v hu hv hyx
  have hx : x ∈ closure I := hfd ⟨u, hu⟩
  have hy0 : 0 ≤ y := hgd ⟨v, hv⟩
  have hy : y ∈ closure I := hord.convex.closure.ordConnected.out hz hx ⟨hy0, hyx.le⟩
  have hbetween := Ioo_between_closure_subset_open_interval hI hord hne hy hx
  obtain ⟨p, hyp, hpx⟩ := exists_between hyx
  obtain ⟨q, hyq, hqp⟩ := exists_between hyp
  have hp : p ∈ I := hbetween ⟨hyp, hpx⟩
  have hq : q ∈ I := hbetween ⟨hyq, hqp.trans hpx⟩
  obtain ⟨up, hup⟩ := hIf hp
  obtain ⟨vq, hvq⟩ := hIg hq
  exact (Decreasing.le_of_lt hf hup hu hpx).trans
    ((hsep p hp q hq hqp up hup vq hvq).trans (Decreasing.le_of_lt hg hv hvq hyq))

theorem decreasing_initial_domain_inclusion {f g : Operator}
    (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hzf : IsGLB (dom f) 0) (hpf : ∃ a ∈ dom f, 0 < a)
    (hzg : IsGLB (dom g) 0) (hfg : DecLE f g) :
    interior (dom f) ⊆ interior (dom g) := by
  have hp0 := (decreasing_zero_inf_domain_geometry hf hzf hpf).2.2.1
  have hd := (decLE_domains hf hg hfg).2
  intro p hp
  obtain ⟨a, b, ⟨hap, hpb⟩, hab⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (isOpen_interior.mem_nhds hp)
  let x := (p+b)/2
  have hpx : p < x := by dsimp [x]; linarith
  have hxI : x ∈ interior (dom f) := hab ⟨hap.trans hpx, by dsimp [x]; linarith⟩
  obtain ⟨y, hy, hxy⟩ := hd (mem_lowerHull (interior_subset hxI))
  obtain ⟨z, hz, _, hzp⟩ := hzg.exists_between (hp0 p hp)
  have hs : Ioo z y ⊆ dom g := fun t ht =>
    (decreasing_dom_ordConnected hg).out hz hy ⟨ht.1.le, ht.2.le⟩
  exact isOpen_Ioo.subset_interior_iff.mpr hs ⟨hzp, hpx.trans_le hxy⟩

theorem hardyScalar_le_of_decLE {f g : Operator} (hfg : DecLE f g)
    {If Ig : Set ℝ} {sf sg : ℝ → ℝ} (hsf : SelectionOn f If sf) (hsg : SelectionOn g Ig sg)
    (hscaleF : ∀ c ∈ Ioc (0 : ℝ) 1, ∀ p ∈ If, c*p ∈ If)
    (hscaleG : ∀ c ∈ Ioc (0 : ℝ) 1, ∀ p ∈ Ig, c*p ∈ Ig)
    {p q : ℝ} (hp : p ∈ If) (hq : q ∈ Ig) (hp0 : 0 < p) (hq0 : 0 < q) (hqp : q < p)
    (hiF : IntervalIntegrable sf volume 0 p) (hiG : IntervalIntegrable sg volume 0 q) :
    hardyScalar sf p ≤ hardyScalar sg q := by
  rw [hardyScalar_dilation sf hp0, hardyScalar_dilation sg hq0]
  apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0 : ℝ) ≤ 1)
    (hardyScalar_dilation_integrable hp0 hiF) (hardyScalar_dilation_integrable hq0 hiG)
  intro r hr
  exact hfg (hsf _ (hscaleF r ⟨hr.1, hr.2.le⟩ p hp))
    (hsg _ (hscaleG r ⟨hr.1, hr.2.le⟩ q hq)) (mul_lt_mul_of_pos_left hqp hr.1)

theorem graph_value_le_hardyScalar {f : Operator} (hf : Decreasing f)
    {I : Set ℝ} {s : ℝ → ℝ} (hs : SelectionOn f I s)
    (hscale : ∀ c ∈ Ioc (0 : ℝ) 1, ∀ p ∈ I, c*p ∈ I)
    {p q u : ℝ} (hu : u ∈ f p) (hq : q ∈ I) (hq0 : 0 < q) (hqp : q < p)
    (hi : IntervalIntegrable s volume 0 q) : u ≤ hardyScalar s q := by
  have hc : (∫ r in (0 : ℝ)..1, u) = u := by simp
  rw [← hc, hardyScalar_dilation s hq0]
  apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0 : ℝ) ≤ 1)
    intervalIntegrable_const (hardyScalar_dilation_integrable hq0 hi)
  intro r hr
  exact Decreasing.le_of_lt hf (hs _ (hscale r ⟨hr.1, hr.2.le⟩ q hq)) hu
    ((mul_lt_of_lt_one_left hq0 hr.2).trans hqp)

/-- Whole-operator Hardy order preservation, including different initial
averaging intervals and all their boundary fibers. -/
theorem hardyFamilyIntegral_mono {f g : Operator}
    (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hzf : IsGLB (dom f) 0) (hpf : ∃ a ∈ dom f, 0 < a)
    (hzg : IsGLB (dom g) 0) (hpg : ∃ a ∈ dom g, 0 < a)
    {sf sg : ℝ → ℝ} (hsf : SelectionOn f (interior (dom f)) sf)
    (hsg : SelectionOn g (interior (dom g)) sg)
    (hiF : Integrable sf (volume.restrict (interior (dom f))))
    (hiG : Integrable sg (volume.restrict (interior (dom g))))
    (hfg : DecLE f g) :
    DecLE (hardyFamilyIntegral (interior (dom f)) f)
      (hardyFamilyIntegral (interior (dom g)) g) := by
  obtain ⟨hordF, hneF, hposF, hprefixF, hscaleF⟩ := decreasing_zero_inf_domain_geometry hf hzf hpf
  obtain ⟨_, _, hposG, hprefixG, hscaleG⟩ := decreasing_zero_inf_domain_geometry hg hzg hpg
  have hsub := decreasing_initial_domain_inclusion hf hg hzf hpf hzg hfg
  have hHF := hardyFamilyIntegral_of_integrable hf hzf hpf hsf hiF
  have hHG := hardyFamilyIntegral_of_integrable hg hzg hpg hsg hiG
  have hclosedG : closure (interior (dom g)) ⊆ Ici (0 : ℝ) :=
    closure_minimal (fun _ hx => hzg.1 (interior_subset hx)) isClosed_Ici
  have hcoverF : interior (dom f) ⊆ dom (hardyFamilyIntegral (interior (dom f)) f) := by
    intro p hp
    refine ⟨hardyScalar sf p, ?_⟩
    rw [hHF.2.2.2.1 p hp]
    exact mem_singleton _
  have hcoverG : interior (dom f) ⊆ dom (hardyFamilyIntegral (interior (dom g)) g) := by
    intro p hp
    refine ⟨hardyScalar sg p, ?_⟩
    rw [hHG.2.2.2.1 p (hsub hp)]
    exact mem_singleton _
  have hlocalF (p) (hp : p ∈ interior (dom f)) : IntervalIntegrable sf volume 0 p :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (hposF p hp).le).mpr
      (IntegrableOn.mono_set hiF (hprefixF p hp))
  have hlocalG (p) (hp : p ∈ interior (dom g)) : IntervalIntegrable sg volume 0 p :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (hposG p hp).le).mpr
      (IntegrableOn.mono_set hiG (hprefixG p hp))
  apply decLE_of_initial_interior hHF.1.1 hHG.1.1 isOpen_interior hordF hneF
    (zero_mem_closure_decreasing_domain_interior hf hzf hneF) hHF.2.2.1
    (fun y hy => hclosedG (hHG.2.2.1 hy)) hcoverF hcoverG
  intro p hp q hq hqp u hu v hv
  rw [hHF.2.2.2.1 p hp] at hu
  rw [hHG.2.2.2.1 q (hsub hq)] at hv
  rw [mem_singleton_iff.mp hu, mem_singleton_iff.mp hv]
  exact hardyScalar_le_of_decLE hfg hsf hsg hscaleF hscaleG hp (hsub hq)
    (hposF p hp) (hposG q (hsub hq)) hqp (hlocalF p hp) (hlocalG q (hsub hq))

theorem le_hardyFamilyIntegral {f : Operator} (hf : MaximalDecreasing f)
    (hz : IsGLB (dom f) 0) (hp : ∃ a ∈ dom f, 0 < a)
    {s : ℝ → ℝ} (hs : SelectionOn f (interior (dom f)) s)
    (hi : Integrable s (volume.restrict (interior (dom f)))) :
    DecLE f (hardyFamilyIntegral (interior (dom f)) f) := by
  obtain ⟨hord, hne, hpos, hprefix, hscale⟩ := decreasing_zero_inf_domain_geometry hf hz hp
  have hH := hardyFamilyIntegral_of_integrable hf hz hp hs hi
  have hclosed : closure (interior (dom f)) ⊆ Ici (0 : ℝ) :=
    closure_minimal (fun _ hx => hz.1 (interior_subset hx)) isClosed_Ici
  have hcover : interior (dom f) ⊆ dom (hardyFamilyIntegral (interior (dom f)) f) := by
    intro p hp
    refine ⟨hardyScalar s p, ?_⟩
    rw [hH.2.2.2.1 p hp]
    exact mem_singleton _
  have hlocal (p) (hp : p ∈ interior (dom f)) : IntervalIntegrable s volume 0 p :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (hpos p hp).le).mpr
      (IntegrableOn.mono_set hi (hprefix p hp))
  apply decLE_of_initial_interior hf.1 hH.1.1 isOpen_interior hord hne
    (zero_mem_closure_decreasing_domain_interior hf hz hne)
    (decreasing_dom_subset_closure_interior hf hne)
    (fun y hy => hclosed (hH.2.2.1 hy)) interior_subset hcover
  intro p hp q hq hqp u hu v hv
  rw [hH.2.2.2.1 q hq] at hv
  rw [mem_singleton_iff.mp hv]
  exact graph_value_le_hardyScalar hf.1 hs hscale hu hq (hpos q hq) hqp (hlocal q hq)


theorem add_fiber_singleton {f g : Operator} {p a b : ℝ}
    (hf : f p = {a}) (hg : g p = {b}) : add f g p = {a+b} := by
  ext w
  simp [ScalarMonotone.add, hf, hg]

theorem outputScale_fiber_singleton (c : ℝ) {f : Operator} {p a : ℝ}
    (hf : f p = {a}) : outputScale c f p = {c*a} := by
  ext w
  simp [outputScale, hf]

/-- Addition commutes with the entire completed Hardy operator. The equality
at boundary fibers follows from maximality and uniqueness, not scalar equality
alone. -/
theorem hardyFamilyIntegral_add {f g : Operator}
    (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hz : IsGLB (dom f) 0) (hp : ∃ a ∈ dom f, 0 < a)
    (heq : interior (dom g) = interior (dom f))
    {sf sg : ℝ → ℝ} (hsf : SelectionOn f (interior (dom f)) sf)
    (hsg : SelectionOn g (interior (dom g)) sg)
    (hiF : Integrable sf (volume.restrict (interior (dom f))))
    (hiG : Integrable sg (volume.restrict (interior (dom g)))) :
    hardyFamilyIntegral (interior (dom (add f g))) (add f g) =
      add (hardyFamilyIntegral (interior (dom f)) f)
        (hardyFamilyIntegral (interior (dom g)) g) := by
  obtain ⟨hord, hne, hpos, hprefix, hscale⟩ := decreasing_zero_inf_domain_geometry hf hz hp
  have hdG : interior (dom f) ⊆ interior (dom g) := by
    intro p hp
    rw [heq]
    exact hp
  have hsgI : SelectionOn g (interior (dom f)) sg := fun p hp => hsg p (hdG hp)
  have hiGI : Integrable sg (volume.restrict (interior (dom f))) := by simpa only [heq] using hiG
  have hlocalF (p) (hp : p ∈ interior (dom f)) : IntervalIntegrable sf volume 0 p :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (hpos p hp).le).mpr
      (IntegrableOn.mono_set hiF (hprefix p hp))
  have hlocalG (p) (hp : p ∈ interior (dom f)) : IntervalIntegrable sg volume 0 p :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (hpos p hp).le).mpr
      (IntegrableOn.mono_set hiGI (hprefix p hp))
  have hHF := hardyFamilyIntegral_of_integrable hf hz hp hsf hiF
  have hHG := hardyFamilyIntegral_well_defined hg isOpen_interior hord hne hdG hpos hscale hsgI hlocalG
  obtain ⟨p, hpI⟩ := hne
  have hne : (interior (dom f)).Nonempty := ⟨p, hpI⟩
  have hsum : MaximalDecreasing (add f g) := add_maximal_decreasing hf hg
    ⟨p, interior_subset hpI, interior_subset (hdG hpI)⟩
  have hsumI : interior (dom (add f g)) = interior (dom f) := by
    rw [dom_add, interior_inter, heq, inter_self]
  have hdsum : interior (dom f) ⊆ interior (dom (add f g)) := by
    intro p hp
    rw [hsumI]
    exact hp
  have hsSum : SelectionOn (add f g) (interior (dom f)) (fun x => sf x+sg x) :=
    fun p hp => ⟨sf p, hsf p hp, sg p, hsgI p hp, rfl⟩
  have hHSum := hardyFamilyIntegral_well_defined hsum isOpen_interior hord hne hdsum hpos hscale
    hsSum (fun p hp => (hlocalF p hp).add (hlocalG p hp))
  have hpF : p ∈ dom (hardyFamilyIntegral (interior (dom f)) f) := by
    apply interior_subset
    rw [hHF.2.1]
    exact hpI
  have hpG : p ∈ dom (hardyFamilyIntegral (interior (dom f)) g) := by
    apply interior_subset
    rw [hHG.2.1]
    exact hpI
  have hRmax := add_maximal_decreasing hHF.1 hHG.1 ⟨p, hpF, hpG⟩
  have hRdom : dom (add (hardyFamilyIntegral (interior (dom f)) f)
      (hardyFamilyIntegral (interior (dom f)) g)) ⊆ closure (interior (dom f)) := by
    intro x hx
    rw [dom_add] at hx
    exact hHF.2.2.1 hx.1
  have hRvalues : ∀ p ∈ interior (dom f),
      add (hardyFamilyIntegral (interior (dom f)) f)
        (hardyFamilyIntegral (interior (dom f)) g) p = {hardyScalar (fun x => sf x+sg x) p} := by
    intro p hp
    rw [add_fiber_singleton (hHF.2.2.2.1 p hp) (hHG.2.2.2.1 p hp),
      hardyScalar_add (hlocalF p hp) (hlocalG p hp)]
  have hR := hHSum.2.2.2.2 _ hRmax hRdom hRvalues
  rw [hsumI, heq]
  exact hR.symm

theorem hardyFamilyIntegral_outputScale {f : Operator} (hf : MaximalDecreasing f)
    (hz : IsGLB (dom f) 0) (hp : ∃ a ∈ dom f, 0 < a)
    {s : ℝ → ℝ} (hs : SelectionOn f (interior (dom f)) s)
    (hi : Integrable s (volume.restrict (interior (dom f)))) {c : ℝ} (hc : 0 < c) :
    hardyFamilyIntegral (interior (dom (outputScale c f))) (outputScale c f) =
      outputScale c (hardyFamilyIntegral (interior (dom f)) f) := by
  obtain ⟨hord, hne, hpos, hprefix, hscale⟩ := decreasing_zero_inf_domain_geometry hf hz hp
  have hlocal (p) (hp : p ∈ interior (dom f)) : IntervalIntegrable s volume 0 p :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (hpos p hp).le).mpr
      (IntegrableOn.mono_set hi (hprefix p hp))
  have hHF := hardyFamilyIntegral_of_integrable hf hz hp hs hi
  have hscaled := outputScale_maximal_decreasing hc hf
  have hdscaled : interior (dom f) ⊆ interior (dom (outputScale c f)) := by
    simpa only [dom_outputScale] using (Subset.rfl : interior (dom f) ⊆ interior (dom f))
  have hsScaled : SelectionOn (outputScale c f) (interior (dom f)) (fun x => c*s x) :=
    fun p hp => ⟨s p, hs p hp, rfl⟩
  have hHScaled := hardyFamilyIntegral_well_defined hscaled isOpen_interior hord hne hdscaled
    hpos hscale hsScaled (fun p hp => (hlocal p hp).const_mul c)
  have hRmax := outputScale_maximal_decreasing hc hHF.1
  have hRdom : dom (outputScale c (hardyFamilyIntegral (interior (dom f)) f)) ⊆
      closure (interior (dom f)) := by
    simpa only [dom_outputScale] using hHF.2.2.1
  have hRvalues : ∀ p ∈ interior (dom f),
      outputScale c (hardyFamilyIntegral (interior (dom f)) f) p = {hardyScalar (fun x => c*s x) p} := by
    intro p hp
    rw [outputScale_fiber_singleton c (hHF.2.2.2.1 p hp), hardyScalar_smul]
  have hR := hHScaled.2.2.2.2 _ hRmax hRdom hRvalues
  simpa only [dom_outputScale] using hR.symm


/-- All conclusions of prop:hardycalculus. Addition uses the common interior;
the order implication explicitly retains different averaging intervals. -/
theorem hardyFamilyIntegral_calculus {f g : Operator}
    (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hzf : IsGLB (dom f) 0) (hpf : ∃ a ∈ dom f, 0 < a)
    (hzg : IsGLB (dom g) 0) (hpg : ∃ a ∈ dom g, 0 < a)
    {sf sg : ℝ → ℝ} (hsf : SelectionOn f (interior (dom f)) sf)
    (hsg : SelectionOn g (interior (dom g)) sg)
    (hiF : Integrable sf (volume.restrict (interior (dom f))))
    (hiG : Integrable sg (volume.restrict (interior (dom g)))) :
    DecLE f (hardyFamilyIntegral (interior (dom f)) f) ∧
      (DecLE f g → DecLE (hardyFamilyIntegral (interior (dom f)) f)
        (hardyFamilyIntegral (interior (dom g)) g)) ∧
      (interior (dom g) = interior (dom f) →
        hardyFamilyIntegral (interior (dom (add f g))) (add f g) =
          add (hardyFamilyIntegral (interior (dom f)) f)
            (hardyFamilyIntegral (interior (dom g)) g)) ∧
      ∀ c : ℝ, 0 < c →
        hardyFamilyIntegral (interior (dom (outputScale c f))) (outputScale c f) =
          outputScale c (hardyFamilyIntegral (interior (dom f)) f) :=
  ⟨le_hardyFamilyIntegral hf hzf hpf hsf hiF,
   fun hfg => hardyFamilyIntegral_mono hf hg hzf hpf hzg hpg hsf hsg hiF hiG hfg,
   fun heq => hardyFamilyIntegral_add hf hg hzf hpf heq hsf hsg hiF hiG,
   fun c hc => hardyFamilyIntegral_outputScale hf hzf hpf hsf hiF hc⟩

end ScalarMonotone.EndOfPaper
end
