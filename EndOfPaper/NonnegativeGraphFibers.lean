import EndOfPaper.LocalHardy
import MonotoneOperators.Interface

/-!
Order and topology foundations for the geometric Hardy
construction. Positive parts determine nonnegative completed
initial graphs, including zero and endpoint fibers.
-/

open Set
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem zero_mem_of_equal_positive_parts {A B : Set ℝ}
    (hA : A.OrdConnected) (hBc : IsClosed B) (hBne : B.Nonempty)
    (hB0 : B ⊆ Ici 0) (hpos : ∀ x > 0, x ∈ A ↔ x ∈ B) (hzero : 0 ∈ A) :
    0 ∈ B := by
  obtain ⟨b, hb⟩ := hBne
  by_cases hbzero : b = 0
  · simpa only [hbzero] using hb
  · have hbpos : 0 < b := lt_of_le_of_ne (hB0 hb) (Ne.symm hbzero)
    have hbA : b ∈ A := (hpos b hbpos).mpr hb
    have hsmall : Ioo (0 : ℝ) b ⊆ B := by
      intro x hx
      exact (hpos x hx.1).mp (hA.out hzero hbA ⟨hx.1.le, hx.2.le⟩)
    have hcl : (0 : ℝ) ∈ closure (Ioo (0 : ℝ) b) := by
      rw [closure_Ioo hbpos.ne]
      exact ⟨le_rfl, hbpos.le⟩
    exact hBc.closure_subset ((closure_mono hsmall) hcl)

theorem nonnegative_closed_intervals_eq {A B : Set ℝ}
    (hAc : IsClosed A) (hBc : IsClosed B) (hA : A.OrdConnected) (hB : B.OrdConnected)
    (hAne : A.Nonempty) (hBne : B.Nonempty) (hA0 : A ⊆ Ici 0) (hB0 : B ⊆ Ici 0)
    (hpos : ∀ x > 0, x ∈ A ↔ x ∈ B) : A = B := by
  ext x
  by_cases hxpos : 0 < x
  · exact hpos x hxpos
  · by_cases hxneg : x < 0
    · constructor
      · intro hx
        exact (not_le_of_gt hxneg (hA0 hx)).elim
      · intro hx
        exact (not_le_of_gt hxneg (hB0 hx)).elim
    · have hxzero : x = 0 := le_antisymm (le_of_not_gt hxpos) (le_of_not_gt hxneg)
      subst x
      exact ⟨zero_mem_of_equal_positive_parts hA hBc hBne hB0 hpos,
        zero_mem_of_equal_positive_parts hB hAc hAne hA0 (fun x hx => (hpos x hx).symm)⟩

theorem maximal_decreasing_bounded_dom_range {f : Operator} {B : ℝ}
    (hf : MaximalDecreasing f) (hdom : dom f ⊆ Icc (0 : ℝ) B) : ran f = univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro t
  obtain ⟨x, hx⟩ := minty_surjective (f := negOut f) hf (B-t+1)
  obtain ⟨y, hy⟩ := minty_surjective (f := negOut f) hf (-t-1)
  have hx' : x-(B-t+1) ∈ f x := by simpa only [negOut, mem_setOf_eq, neg_sub] using hx
  have hy' : y-(-t-1) ∈ f y := by simpa only [negOut, mem_setOf_eq, neg_sub] using hy
  have hxb := (hdom ⟨_, hx'⟩).2
  have hy0 := (hdom ⟨_, hy'⟩).1
  exact (decreasing_ran_ordConnected hf).out ⟨x, hx'⟩ ⟨y, hy'⟩
    ⟨by linarith, by linarith⟩

theorem nonnegative_initial_graph_eq_of_log_eq {f g : Operator} {B : ℝ}
    (hB : 0 < B) (hf : MaximalDecreasing f) (hg : MaximalDecreasing g)
    (hfi : interior (dom f) = Ioo (0 : ℝ) B)
    (hgi : interior (dom g) = Ioo (0 : ℝ) B)
    (hf0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ u ∈ f x, 0 ≤ u)
    (hg0 : ∀ x ∈ Ioo (0 : ℝ) B, ∀ u ∈ g x, 0 ≤ u)
    (hlog : ∀ x ∈ Ioo (0 : ℝ) B, logOp f x = logOp g x) : f = g := by
  have hIf : Ioo (0 : ℝ) B ⊆ dom f := by
    intro x hx
    apply interior_subset
    rwa [hfi]
  have hIg : Ioo (0 : ℝ) B ⊆ dom g := by
    intro x hx
    apply interior_subset
    rwa [hgi]
  have hfib (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) B) : f x = g x := by
    apply nonnegative_closed_intervals_eq (decreasing_fiber_closed hf x)
      (decreasing_fiber_closed hg x) (decreasing_fiber_ordConnected hf x)
      (decreasing_fiber_ordConnected hg x) (hIf hx) (hIg hx)
      (fun u hu => hf0 x hx u hu) (fun u hu => hg0 x hx u hu)
    intro u hu
    have he : Real.log u ∈ logOp f x ↔ Real.log u ∈ logOp g x := by rw [hlog x hx]
    simpa only [logOp_mem_iff, Real.exp_log hu] using he
  have hne : (Ioo (0 : ℝ) B).Nonempty := nonempty_Ioo.mpr hB
  have hfd : dom f ⊆ closure (Ioo (0 : ℝ) B) := by
    have hi : (interior (dom f)).Nonempty := by rw [hfi]; exact hne
    simpa only [hfi] using decreasing_dom_subset_closure_interior hf hi
  have hgd : dom g ⊆ closure (Ioo (0 : ℝ) B) := by
    have hi : (interior (dom g)).Nonempty := by rw [hgi]; exact hne
    simpa only [hgi] using decreasing_dom_subset_closure_interior hg hi
  let R := restrictOperator f (Ioo (0 : ℝ) B)
  have hR : Decreasing R := by
    intro x u y v hu hv
    exact hf.1 hu.2 hv.2
  have hdR : dom R = Ioo (0 : ℝ) B := dom_restrictOperator hIf
  obtain ⟨F, hF, huniq⟩ := unique_maximal_decreasing_completion ordConnected_Ioo hne hR hdR
  have hRf : R ≤ f := fun x u hu => hu.2
  have hRg : R ≤ g := by
    intro x u hu
    exact (hfib x hu.1) ▸ hu.2
  exact (huniq f ⟨hf, hRf, hfd⟩).trans (huniq g ⟨hg, hRg, hgd⟩).symm

end ScalarMonotone.EndOfPaper
end
