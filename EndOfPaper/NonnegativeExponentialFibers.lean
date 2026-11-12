import EndOfPaper.NonnegativeGraphFibers

/-!
Exact nonnegative exponential fibers. A logarithmic upper
ray gives the entire closed interval from zero to its exponential
endpoint; an empty logarithmic fiber gives the zero singleton.
-/

open Set
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem nonnegative_log_singleton_fiber {g : Operator} {x a : ℝ}
    (hg : MaximalDecreasing g) (hne : (g x).Nonempty) (hz : g x ⊆ Ici 0)
    (hl : logOp g x = {a}) : g x = {Real.exp a} := by
  apply nonnegative_closed_intervals_eq (decreasing_fiber_closed hg x) isClosed_singleton
    (decreasing_fiber_ordConnected hg x) ordConnected_singleton hne (singleton_nonempty _)
    hz (by intro u hu; rw [mem_singleton_iff.mp hu]; exact (Real.exp_pos a).le)
  intro u hu
  have he : u ∈ g x ↔ Real.log u ∈ logOp g x := by simp only [logOp_mem_iff,Real.exp_log hu]
  rw [he,hl]
  simp only [mem_singleton_iff]
  constructor
  · intro h
    rw [← Real.exp_log hu,h]
  · intro h
    rw [h,Real.log_exp]

theorem nonnegative_log_empty_fiber {g : Operator} {x : ℝ}
    (hne : (g x).Nonempty) (hz : g x ⊆ Ici 0) (hl : logOp g x = ∅) : g x = {0} := by
  have hzero {v : ℝ} (hv : v ∈ g x) : v = 0 := by
    have hv0 := hz hv
    by_contra hn
    have hvpos : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hn)
    have hw : Real.log v ∈ logOp g x := logOp_mem_iff.mpr
      (by simpa only [Real.exp_log hvpos] using hv)
    rw [hl] at hw
    exact hw
  apply Set.Subset.antisymm (fun v hv => hzero hv)
  intro v hv
  obtain ⟨u,hu⟩ := hne
  rw [mem_singleton_iff.mp hv,← hzero hu]
  exact hu

theorem nonnegative_log_upper_ray_fiber {g : Operator} {x a : ℝ}
    (hg : MaximalDecreasing g) (hne : (g x).Nonempty) (hz : g x ⊆ Ici 0)
    (hl : logOp g x = Iic a) : g x = Icc (0 : ℝ) (Real.exp a) := by
  apply nonnegative_closed_intervals_eq (decreasing_fiber_closed hg x) isClosed_Icc
    (decreasing_fiber_ordConnected hg x) ordConnected_Icc hne
    (nonempty_Icc.mpr (Real.exp_pos a).le) hz (fun _ hu => hu.1)
  intro u hu
  have he : u ∈ g x ↔ Real.log u ∈ logOp g x := by simp only [logOp_mem_iff,Real.exp_log hu]
  rw [he,hl]
  simp only [mem_Iic,mem_Icc,hu.le,true_and]
  exact Real.log_le_iff_le_exp hu

end ScalarMonotone.EndOfPaper
end
