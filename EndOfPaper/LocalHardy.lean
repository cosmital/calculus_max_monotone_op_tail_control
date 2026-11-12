import EndOfPaper.HardyCalculus

/-!
Every Hardy property under prefix integrability alone. The completed
operator is maximal and unique, retains all boundary fibers, commutes
with sums and positive scaling, preserves order on different initial
intervals, and preserves convex and concave scalar selections.
-/

open Set Filter MeasureTheory
open scoped Interval
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem hardyFamilyIntegral_of_locally_integrable {f : Operator} (hf : MaximalDecreasing f)
    (hzero : IsGLB (dom f) 0) (hpositive : ∃ a ∈ dom f, 0 < a)
    {s : ℝ → ℝ} (hs : SelectionOn f (interior (dom f)) s)
    (hsi : ∀ p ∈ interior (dom f), IntervalIntegrable s volume 0 p) :
    let I := interior (dom f)
    MaximalDecreasing (hardyFamilyIntegral I f) ∧
      interior (dom (hardyFamilyIntegral I f)) = I ∧
      dom (hardyFamilyIntegral I f) ⊆ closure I ∧
      (∀ p ∈ I, hardyFamilyIntegral I f p = {hardyScalar s p}) ∧
      ∀ g : Operator, MaximalDecreasing g → dom g ⊆ closure I →
        (∀ p ∈ I, g p = {hardyScalar s p}) → g = hardyFamilyIntegral I f := by
  obtain ⟨hord, hne, hpos, hprefix, hscale⟩ :=
    decreasing_zero_inf_domain_geometry hf hzero hpositive
  apply hardyFamilyIntegral_well_defined hf isOpen_interior hord hne Subset.rfl hpos hscale hs
  exact hsi

theorem hardyFamilyIntegral_mono_locally_integrable {f g : Operator}
    (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hzf : IsGLB (dom f) 0) (hpf : ∃ a ∈ dom f, 0 < a)
    (hzg : IsGLB (dom g) 0) (hpg : ∃ a ∈ dom g, 0 < a)
    {sf sg : ℝ → ℝ} (hsf : SelectionOn f (interior (dom f)) sf)
    (hsg : SelectionOn g (interior (dom g)) sg)
    (hiF : ∀ p ∈ interior (dom f), IntervalIntegrable sf volume 0 p)
    (hiG : ∀ p ∈ interior (dom g), IntervalIntegrable sg volume 0 p)
    (hfg : DecLE f g) :
    DecLE (hardyFamilyIntegral (interior (dom f)) f)
      (hardyFamilyIntegral (interior (dom g)) g) := by
  obtain ⟨hordF, hneF, hposF, hprefixF, hscaleF⟩ := decreasing_zero_inf_domain_geometry hf hzf hpf
  obtain ⟨_, _, hposG, hprefixG, hscaleG⟩ := decreasing_zero_inf_domain_geometry hg hzg hpg
  have hsub := decreasing_initial_domain_inclusion hf hg hzf hpf hzg hfg
  have hHF := hardyFamilyIntegral_of_locally_integrable hf hzf hpf hsf hiF
  have hHG := hardyFamilyIntegral_of_locally_integrable hg hzg hpg hsg hiG
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
  have hlocalF := hiF
  have hlocalG := hiG
  apply decLE_of_initial_interior hHF.1.1 hHG.1.1 isOpen_interior hordF hneF
    (zero_mem_closure_decreasing_domain_interior hf hzf hneF) hHF.2.2.1
    (fun y hy => hclosedG (hHG.2.2.1 hy)) hcoverF hcoverG
  intro p hp q hq hqp u hu v hv
  rw [hHF.2.2.2.1 p hp] at hu
  rw [hHG.2.2.2.1 q (hsub hq)] at hv
  rw [mem_singleton_iff.mp hu, mem_singleton_iff.mp hv]
  exact hardyScalar_le_of_decLE hfg hsf hsg hscaleF hscaleG hp (hsub hq)
    (hposF p hp) (hposG q (hsub hq)) hqp (hlocalF p hp) (hlocalG q (hsub hq))

theorem le_hardyFamilyIntegral_locally_integrable {f : Operator} (hf : MaximalDecreasing f)
    (hz : IsGLB (dom f) 0) (hp : ∃ a ∈ dom f, 0 < a)
    {s : ℝ → ℝ} (hs : SelectionOn f (interior (dom f)) s)
    (hi : ∀ p ∈ interior (dom f), IntervalIntegrable s volume 0 p) :
    DecLE f (hardyFamilyIntegral (interior (dom f)) f) := by
  obtain ⟨hord, hne, hpos, hprefix, hscale⟩ := decreasing_zero_inf_domain_geometry hf hz hp
  have hH := hardyFamilyIntegral_of_locally_integrable hf hz hp hs hi
  have hclosed : closure (interior (dom f)) ⊆ Ici (0 : ℝ) :=
    closure_minimal (fun _ hx => hz.1 (interior_subset hx)) isClosed_Ici
  have hcover : interior (dom f) ⊆ dom (hardyFamilyIntegral (interior (dom f)) f) := by
    intro p hp
    refine ⟨hardyScalar s p, ?_⟩
    rw [hH.2.2.2.1 p hp]
    exact mem_singleton _
  have hlocal := hi
  apply decLE_of_initial_interior hf.1 hH.1.1 isOpen_interior hord hne
    (zero_mem_closure_decreasing_domain_interior hf hz hne)
    (decreasing_dom_subset_closure_interior hf hne)
    (fun y hy => hclosed (hH.2.2.1 hy)) interior_subset hcover
  intro p hp q hq hqp u hu v hv
  rw [hH.2.2.2.1 q hq] at hv
  rw [mem_singleton_iff.mp hv]
  exact graph_value_le_hardyScalar hf.1 hs hscale hu hq (hpos q hq) hqp (hlocal q hq)

theorem hardyFamilyIntegral_add_locally_integrable {f g : Operator}
    (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hz : IsGLB (dom f) 0) (hp : ∃ a ∈ dom f, 0 < a)
    (heq : interior (dom g) = interior (dom f))
    {sf sg : ℝ → ℝ} (hsf : SelectionOn f (interior (dom f)) sf)
    (hsg : SelectionOn g (interior (dom g)) sg)
    (hiF : ∀ p ∈ interior (dom f), IntervalIntegrable sf volume 0 p)
    (hiG : ∀ p ∈ interior (dom g), IntervalIntegrable sg volume 0 p) :
    hardyFamilyIntegral (interior (dom (add f g))) (add f g) =
      add (hardyFamilyIntegral (interior (dom f)) f)
        (hardyFamilyIntegral (interior (dom g)) g) := by
  obtain ⟨hord, hne, hpos, hprefix, hscale⟩ := decreasing_zero_inf_domain_geometry hf hz hp
  have hdG : interior (dom f) ⊆ interior (dom g) := by
    intro p hp
    rw [heq]
    exact hp
  have hsgI : SelectionOn g (interior (dom f)) sg := fun p hp => hsg p (hdG hp)
  have hlocalF := hiF
  have hlocalG (p) (hp : p ∈ interior (dom f)) : IntervalIntegrable sg volume 0 p := hiG p (hdG hp)
  have hHF := hardyFamilyIntegral_of_locally_integrable hf hz hp hsf hiF
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

theorem hardyFamilyIntegral_outputScale_locally_integrable {f : Operator} (hf : MaximalDecreasing f)
    (hz : IsGLB (dom f) 0) (hp : ∃ a ∈ dom f, 0 < a)
    {s : ℝ → ℝ} (hs : SelectionOn f (interior (dom f)) s)
    (hi : ∀ p ∈ interior (dom f), IntervalIntegrable s volume 0 p) {c : ℝ} (hc : 0 < c) :
    hardyFamilyIntegral (interior (dom (outputScale c f))) (outputScale c f) =
      outputScale c (hardyFamilyIntegral (interior (dom f)) f) := by
  obtain ⟨hord, hne, hpos, hprefix, hscale⟩ := decreasing_zero_inf_domain_geometry hf hz hp
  have hlocal := hi
  have hHF := hardyFamilyIntegral_of_locally_integrable hf hz hp hs hi
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

theorem hardyFamilyIntegral_calculus_locally_integrable {f g : Operator}
    (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hzf : IsGLB (dom f) 0) (hpf : ∃ a ∈ dom f, 0 < a)
    (hzg : IsGLB (dom g) 0) (hpg : ∃ a ∈ dom g, 0 < a)
    {sf sg : ℝ → ℝ} (hsf : SelectionOn f (interior (dom f)) sf)
    (hsg : SelectionOn g (interior (dom g)) sg)
    (hiF : ∀ p ∈ interior (dom f), IntervalIntegrable sf volume 0 p)
    (hiG : ∀ p ∈ interior (dom g), IntervalIntegrable sg volume 0 p) :
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
  ⟨le_hardyFamilyIntegral_locally_integrable hf hzf hpf hsf hiF,
   fun hfg => hardyFamilyIntegral_mono_locally_integrable hf hg hzf hpf hzg hpg hsf hsg hiF hiG hfg,
   fun heq => hardyFamilyIntegral_add_locally_integrable hf hg hzf hpf heq hsf hsg hiF hiG,
   fun c hc => hardyFamilyIntegral_outputScale_locally_integrable hf hzf hpf hsf hiF hc⟩

theorem hardyFamilyIntegral_preserves_convexity_locally_integrable {f : Operator} (hf : MaximalDecreasing f)
    (hzero : IsGLB (dom f) 0) (hpositive : ∃ a ∈ dom f, 0 < a)
    {s : ℝ → ℝ} (hs : SelectionOn f (interior (dom f)) s)
    (hsi : ∀ p ∈ interior (dom f), IntervalIntegrable s volume 0 p)
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (interior (dom f)) φ)
    (hφsel : SelectionOn f (interior (dom f)) φ) :
    ∃ ψ : ℝ → ℝ,
      ConvexOn ℝ (interior (dom (hardyFamilyIntegral (interior (dom f)) f))) ψ ∧
      SelectionOn (hardyFamilyIntegral (interior (dom f)) f)
        (interior (dom (hardyFamilyIntegral (interior (dom f)) f))) ψ := by
  obtain ⟨_, _, hpos, hprefix, hscale⟩ := decreasing_zero_inf_domain_geometry hf hzero hpositive
  have hi (p) (hp : p ∈ interior (dom f)) : IntervalIntegrable φ volume 0 p := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (hpos p hp).le).mpr
    have hlocal : Integrable s (volume.restrict (Ioo 0 p)) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (hpos p hp).le).mp (hsi p hp)
    exact hlocal.congr (decreasing_selections_ae_eq hf.1
      (fun x hx => hs x (hprefix p hp hx))
      (fun x hx => hφsel x (hprefix p hp hx)) volume measurableSet_Ioo)
  obtain ⟨_, hd, _, hv, _⟩ :=
    hardyFamilyIntegral_of_locally_integrable hf hzero hpositive hφsel hi
  refine ⟨hardyScalar φ, ?_, ?_⟩
  · rw [hd]
    exact hardyScalar_convexOn_initial hφ hpos hscale hi
  · intro p hp
    have hpI : p ∈ interior (dom f) := by simpa only [hd] using hp
    rw [hv p hpI]
    exact mem_singleton _

theorem hardyFamilyIntegral_preserves_concavity_locally_integrable {f : Operator} (hf : MaximalDecreasing f)
    (hzero : IsGLB (dom f) 0) (hpositive : ∃ a ∈ dom f, 0 < a)
    {s : ℝ → ℝ} (hs : SelectionOn f (interior (dom f)) s)
    (hsi : ∀ p ∈ interior (dom f), IntervalIntegrable s volume 0 p)
    {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ (interior (dom f)) φ)
    (hφsel : SelectionOn f (interior (dom f)) φ) :
    ∃ ψ : ℝ → ℝ,
      ConcaveOn ℝ (interior (dom (hardyFamilyIntegral (interior (dom f)) f))) ψ ∧
      SelectionOn (hardyFamilyIntegral (interior (dom f)) f)
        (interior (dom (hardyFamilyIntegral (interior (dom f)) f))) ψ := by
  obtain ⟨_, _, hpos, hprefix, hscale⟩ := decreasing_zero_inf_domain_geometry hf hzero hpositive
  have hi (p) (hp : p ∈ interior (dom f)) : IntervalIntegrable φ volume 0 p := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (hpos p hp).le).mpr
    have hlocal : Integrable s (volume.restrict (Ioo 0 p)) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (hpos p hp).le).mp (hsi p hp)
    exact hlocal.congr (decreasing_selections_ae_eq hf.1
      (fun x hx => hs x (hprefix p hp hx))
      (fun x hx => hφsel x (hprefix p hp hx)) volume measurableSet_Ioo)
  obtain ⟨_, hd, _, hv, _⟩ :=
    hardyFamilyIntegral_of_locally_integrable hf hzero hpositive hφsel hi
  refine ⟨hardyScalar φ, ?_, ?_⟩
  · rw [hd]
    exact hardyScalar_concaveOn_initial hφ hpos hscale hi
  · intro p hp
    have hpI : p ∈ interior (dom f) := by simpa only [hd] using hp
    rw [hv p hpI]
    exact mem_singleton _

end ScalarMonotone.EndOfPaper
end
