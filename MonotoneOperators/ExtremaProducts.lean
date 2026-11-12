import MonotoneOperators.ExtremaActive
import MonotoneOperators.ExtremaIntervalProducts
import MonotoneOperators.ExtremaInversionIdentities

/-!
# Products and finite extrema

Only the fixed factor has nonnegative range. The varying factors may take
negative values. Maximality of each individual product suffices; maximality
of the product with the extremum follows from the resulting graph equality.
The proof retains domain endpoints and justifies the restriction to active
fibers before using interval multiplication.
-/

open Set

namespace ScalarMonotone

noncomputable section

theorem intervalInf_reindex {ι κ : Type*} (e : ι → κ)
    (he : Function.Surjective e) (I : κ → Set ℝ) :
    intervalInf (fun i => I (e i)) = intervalInf I := by
  unfold intervalInf
  rw [he.iUnion_comp (fun i => upperHull (I i)),
    he.iInter_comp (fun i => lowerHull (I i))]

theorem intervalSup_reindex {ι κ : Type*} (e : ι → κ)
    (he : Function.Surjective e) (I : κ → Set ℝ) :
    intervalSup (fun i => I (e i)) = intervalSup I := by
  unfold intervalSup
  rw [he.iUnion_comp (fun i => lowerHull (I i)),
    he.iInter_comp (fun i => upperHull (I i))]

variable {ι : Type*} [Finite ι] [Nonempty ι]

theorem inc_mul_iInf (f : ι → IncGraph) (h : IncGraph)
    (h₀ : ran h.val ⊆ Ici 0)
    (hmul : ∀ i, MaximalIncreasing (mul h.val (f i).val)) :
    mul h.val (⨅ i, f i).val =
      (⨅ i, (⟨mul h.val (f i).val, hmul i⟩ : IncGraph)).val := by
  classical
  let g : ι → IncGraph := fun i => ⟨mul h.val (f i).val, hmul i⟩
  have hmeet : ∀ i, (dom h.val ∩ dom (f i).val).Nonempty := by
    intro i
    obtain ⟨x, u, hu⟩ := maximal_nonempty (hmul i)
    exact ⟨x, (dom_mul h.val (f i).val).subset ⟨u, hu⟩⟩
  have hdom : dom (⨅ i, g i).val = dom (mul h.val (⨅ i, f i).val) := by
    rw [IncGraph.dom_iInf, dom_mul, IncGraph.dom_iInf]
    simp only [g, dom_mul]
    exact intervalSup_inter (dom h.val) (fun i => dom (f i).val)
      (dom_ordConnected h.property) (fun i => dom_ordConnected (f i).property) hmeet
  funext x
  by_cases hx : x ∈ dom (mul h.val (⨅ i, f i).val)
  · have hxg : x ∈ dom (⨅ i, g i).val := hdom.symm ▸ hx
    obtain ⟨hxh, hxf⟩ := (dom_mul h.val (⨅ i, f i).val).subset hx
    obtain ⟨u, hu⟩ := hxf
    obtain ⟨i, hi⟩ := IncGraph.mem_iInf_imp_exists f hu
    letI : Nonempty {i // x ∈ dom (f i).val} := ⟨⟨i, ⟨u, hi⟩⟩⟩
    change setMul (h.val x) ((⨅ i, f i).val x) = (⨅ i, g i).val x
    rw [IncGraph.fiber_iInf_active f ⟨u, hu⟩, IncGraph.fiber_iInf_active g hxg]
    let e : {i // x ∈ dom (f i).val} → {i // x ∈ dom (g i).val} :=
      fun i => ⟨i.val, (dom_mul h.val (f i.val).val).symm.subset ⟨hxh, i.property⟩⟩
    have he : Function.Surjective e := by
      intro j
      refine ⟨⟨j.val, ((dom_mul h.val (f j.val).val).subset j.property).2⟩, ?_⟩
      exact Subtype.ext rfl
    rw [setMul_intervalInf (h.val x)
      (fun i : {i // x ∈ dom (f i).val} => (f i.val).val x)
      (fun i => i.property) (fun u hu => h₀ ⟨x, hu⟩)
      (maximal_fiber_ordConnected h.property x)]
    exact intervalInf_reindex e he (fun j => (g j.val).val x)
  · have hxg : x ∉ dom (⨅ i, g i).val := by simpa only [hdom] using hx
    exact (not_nonempty_iff_eq_empty.mp hx).trans
      (not_nonempty_iff_eq_empty.mp hxg).symm

theorem inc_mul_iSup (f : ι → IncGraph) (h : IncGraph)
    (h₀ : ran h.val ⊆ Ici 0)
    (hmul : ∀ i, MaximalIncreasing (mul h.val (f i).val)) :
    mul h.val (⨆ i, f i).val =
      (⨆ i, (⟨mul h.val (f i).val, hmul i⟩ : IncGraph)).val := by
  classical
  let g : ι → IncGraph := fun i => ⟨mul h.val (f i).val, hmul i⟩
  have hmeet : ∀ i, (dom h.val ∩ dom (f i).val).Nonempty := by
    intro i
    obtain ⟨x, u, hu⟩ := maximal_nonempty (hmul i)
    exact ⟨x, (dom_mul h.val (f i).val).subset ⟨u, hu⟩⟩
  have hdom : dom (⨆ i, g i).val = dom (mul h.val (⨆ i, f i).val) := by
    rw [IncGraph.dom_iSup, dom_mul, IncGraph.dom_iSup]
    simp only [g, dom_mul]
    exact intervalInf_inter (dom h.val) (fun i => dom (f i).val)
      (dom_ordConnected h.property) (fun i => dom_ordConnected (f i).property) hmeet
  funext x
  by_cases hx : x ∈ dom (mul h.val (⨆ i, f i).val)
  · have hxg : x ∈ dom (⨆ i, g i).val := hdom.symm ▸ hx
    obtain ⟨hxh, hxf⟩ := (dom_mul h.val (⨆ i, f i).val).subset hx
    obtain ⟨u, hu⟩ := hxf
    obtain ⟨i, hi⟩ := IncGraph.mem_iSup_imp_exists f hu
    letI : Nonempty {i // x ∈ dom (f i).val} := ⟨⟨i, ⟨u, hi⟩⟩⟩
    change setMul (h.val x) ((⨆ i, f i).val x) = (⨆ i, g i).val x
    rw [IncGraph.fiber_iSup_active f ⟨u, hu⟩, IncGraph.fiber_iSup_active g hxg]
    let e : {i // x ∈ dom (f i).val} → {i // x ∈ dom (g i).val} :=
      fun i => ⟨i.val, (dom_mul h.val (f i.val).val).symm.subset ⟨hxh, i.property⟩⟩
    have he : Function.Surjective e := by
      intro j
      refine ⟨⟨j.val, ((dom_mul h.val (f j.val).val).subset j.property).2⟩, ?_⟩
      exact Subtype.ext rfl
    rw [setMul_intervalSup (h.val x)
      (fun i : {i // x ∈ dom (f i).val} => (f i.val).val x)
      (fun i => i.property) (fun u hu => h₀ ⟨x, hu⟩)
      (maximal_fiber_ordConnected h.property x)]
    exact intervalSup_reindex e he (fun j => (g j.val).val x)
  · have hxg : x ∉ dom (⨆ i, g i).val := by simpa only [hdom] using hx
    exact (not_nonempty_iff_eq_empty.mp hx).trans
      (not_nonempty_iff_eq_empty.mp hxg).symm

theorem dec_mul_iInf (f : ι → DecGraph) (h : DecGraph)
    (h₀ : ran h.val ⊆ Ici 0)
    (hmul : ∀ i, MaximalDecreasing (mul h.val (f i).val)) :
    mul h.val (⨅ i, f i).val =
      (⨅ i, (⟨mul h.val (f i).val, hmul i⟩ : DecGraph)).val := by
  let g : ι → DecGraph := fun i => ⟨mul h.val (f i).val, hmul i⟩
  have hr₀ : ran h.reflect.val ⊆ Ici 0 := by
    simpa only [DecGraph.reflect, ran_reflect] using h₀
  have hi := inc_mul_iInf (fun i => (f i).reflect) h.reflect hr₀
    (fun i => reflect_maximal_iff.mpr (hmul i))
  have he : mul h.reflect.val (⨅ i, (f i).reflect).val =
      (⨅ i, (g i).reflect).val := hi
  rw [← DecGraph.reflect_iInf, ← DecGraph.reflect_iInf] at he
  change ScalarMonotone.reflect (mul h.val (⨅ i, f i).val) =
    ScalarMonotone.reflect (⨅ i, g i).val at he
  have hr := congrArg ScalarMonotone.reflect he
  simpa only [ScalarMonotone.reflect_reflect] using hr

theorem dec_mul_iSup (f : ι → DecGraph) (h : DecGraph)
    (h₀ : ran h.val ⊆ Ici 0)
    (hmul : ∀ i, MaximalDecreasing (mul h.val (f i).val)) :
    mul h.val (⨆ i, f i).val =
      (⨆ i, (⟨mul h.val (f i).val, hmul i⟩ : DecGraph)).val := by
  let g : ι → DecGraph := fun i => ⟨mul h.val (f i).val, hmul i⟩
  have hr₀ : ran h.reflect.val ⊆ Ici 0 := by
    simpa only [DecGraph.reflect, ran_reflect] using h₀
  have hi := inc_mul_iSup (fun i => (f i).reflect) h.reflect hr₀
    (fun i => reflect_maximal_iff.mpr (hmul i))
  have he : mul h.reflect.val (⨆ i, (f i).reflect).val =
      (⨆ i, (g i).reflect).val := hi
  rw [← DecGraph.reflect_iSup, ← DecGraph.reflect_iSup] at he
  change ScalarMonotone.reflect (mul h.val (⨆ i, f i).val) =
    ScalarMonotone.reflect (⨆ i, g i).val at he
  have hr := congrArg ScalarMonotone.reflect he
  simpa only [ScalarMonotone.reflect_reflect] using hr

theorem inc_parallelMul_iInf (f : ι → IncGraph) (h : IncGraph)
    (h₀ : dom h.val ⊆ Ici 0)
    (hp : ∀ i, MaximalIncreasing (parallelMul h.val (f i).val)) :
    parallelMul h.val (⨅ i, f i).val =
      (⨅ i, (⟨parallelMul h.val (f i).val, hp i⟩ : IncGraph)).val := by
  let g : ι → IncGraph := fun i => ⟨parallelMul h.val (f i).val, hp i⟩
  have hq : ∀ i, MaximalIncreasing (mul h.inv.val (f i).inv.val) :=
    fun i => inverse_maximal (hp i)
  have hi := inc_mul_iSup (fun i => (f i).inv) h.inv
    (by simpa only [IncGraph.inv, ran_inverse] using h₀) hq
  apply operator_inverse_injective
  change mul (inverse h.val) (inverse (⨅ i, f i).val) = inverse (⨅ i, g i).val
  rw [inc_inverse_iInf_val, inc_inverse_iInf_val]
  exact hi

theorem inc_parallelMul_iSup (f : ι → IncGraph) (h : IncGraph)
    (h₀ : dom h.val ⊆ Ici 0)
    (hp : ∀ i, MaximalIncreasing (parallelMul h.val (f i).val)) :
    parallelMul h.val (⨆ i, f i).val =
      (⨆ i, (⟨parallelMul h.val (f i).val, hp i⟩ : IncGraph)).val := by
  let g : ι → IncGraph := fun i => ⟨parallelMul h.val (f i).val, hp i⟩
  have hq : ∀ i, MaximalIncreasing (mul h.inv.val (f i).inv.val) :=
    fun i => inverse_maximal (hp i)
  have hi := inc_mul_iInf (fun i => (f i).inv) h.inv
    (by simpa only [IncGraph.inv, ran_inverse] using h₀) hq
  apply operator_inverse_injective
  change mul (inverse h.val) (inverse (⨆ i, f i).val) = inverse (⨆ i, g i).val
  rw [inc_inverse_iSup_val, inc_inverse_iSup_val]
  exact hi

theorem dec_parallelMul_iInf (f : ι → DecGraph) (h : DecGraph)
    (h₀ : dom h.val ⊆ Ici 0)
    (hp : ∀ i, MaximalDecreasing (parallelMul h.val (f i).val)) :
    parallelMul h.val (⨅ i, f i).val =
      (⨅ i, (⟨parallelMul h.val (f i).val, hp i⟩ : DecGraph)).val := by
  let g : ι → DecGraph := fun i => ⟨parallelMul h.val (f i).val, hp i⟩
  have hq : ∀ i, MaximalDecreasing (mul h.inv.val (f i).inv.val) :=
    fun i => inverse_maximal_decreasing (hp i)
  have hi := dec_mul_iInf (fun i => (f i).inv) h.inv
    (by simpa only [DecGraph.inv, ran_inverse] using h₀) hq
  apply operator_inverse_injective
  change mul (inverse h.val) (inverse (⨅ i, f i).val) = inverse (⨅ i, g i).val
  rw [dec_inverse_iInf_val, dec_inverse_iInf_val]
  exact hi

theorem dec_parallelMul_iSup (f : ι → DecGraph) (h : DecGraph)
    (h₀ : dom h.val ⊆ Ici 0)
    (hp : ∀ i, MaximalDecreasing (parallelMul h.val (f i).val)) :
    parallelMul h.val (⨆ i, f i).val =
      (⨆ i, (⟨parallelMul h.val (f i).val, hp i⟩ : DecGraph)).val := by
  let g : ι → DecGraph := fun i => ⟨parallelMul h.val (f i).val, hp i⟩
  have hq : ∀ i, MaximalDecreasing (mul h.inv.val (f i).inv.val) :=
    fun i => inverse_maximal_decreasing (hp i)
  have hi := dec_mul_iSup (fun i => (f i).inv) h.inv
    (by simpa only [DecGraph.inv, ran_inverse] using h₀) hq
  apply operator_inverse_injective
  change mul (inverse h.val) (inverse (⨆ i, f i).val) = inverse (⨆ i, g i).val
  rw [dec_inverse_iSup_val, dec_inverse_iSup_val]
  exact hi

end

end ScalarMonotone
