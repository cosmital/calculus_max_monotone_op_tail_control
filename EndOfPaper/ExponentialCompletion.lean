import EndOfPaper.NonnegativeGraphFibers

/-!
The nonnegative exponential graph completion on the
half-line and finite initial intervals, including every endpoint
point of the raw exponential and exact whole-graph uniqueness.
-/

open Set Filter MeasureTheory
open scoped Interval ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

/-- Change the input by logarithm, retaining its strictly positive domain. -/
def logarithmicInputGraph (f : Operator) : Operator := fun x =>
  if 0 < x then f (Real.log x) else ∅

theorem logarithmicInputGraph_decreasing {f : Operator} (hf : Decreasing f) :
    Decreasing (logarithmicInputGraph f) := by
  classical
  apply increasing_iff_order.mpr
  intro x u y v hu hv hxy
  change -u ∈ logarithmicInputGraph f x at hu
  change -v ∈ logarithmicInputGraph f y at hv
  have hx : 0 < x := by
    by_contra hn
    simpa only [logarithmicInputGraph, if_neg hn, mem_empty_iff_false] using hu
  have hy : 0 < y := hx.trans hxy
  have hu' : -u ∈ f (Real.log x) := by simpa only [logarithmicInputGraph, if_pos hx] using hu
  have hv' : -v ∈ f (Real.log y) := by simpa only [logarithmicInputGraph, if_pos hy] using hv
  have hlog := Real.strictMonoOn_log hx hy hxy
  have h := Decreasing.le_of_lt hf hu' hv' hlog
  linarith

theorem logarithmicInputGraph_dom {f : Operator} (hf : dom f = univ) :
    dom (logarithmicInputGraph f) = Ioi (0 : ℝ) := by
  classical
  ext x
  constructor
  · rintro ⟨u, hu⟩
    change 0 < x
    by_contra hn
    simpa only [logarithmicInputGraph, if_neg hn, mem_empty_iff_false] using hu
  · intro hx
    change 0 < x at hx
    have he : Real.log x ∈ dom f := by rw [hf]; trivial
    obtain ⟨u, hu⟩ := he
    exact ⟨u, by simpa only [logarithmicInputGraph, if_pos hx] using hu⟩

/-- Completing the logarithmically reparametrized inverse gives the missing
zero fiber of an exponential graph. No scalar endpoint convention is imposed. -/
theorem nonnegative_exponential_completion {f : Operator} {B : ℝ}
    (hf : MaximalDecreasing f) (hdom : dom f ⊆ Icc (0 : ℝ) B)
    (hz : IsGLB (dom f) 0) :
    ∃ g : Operator, MaximalDecreasing g ∧ Nonnegative g ∧
      Ioi (0 : ℝ) ⊆ dom g ∧ dom g ⊆ Ici (0 : ℝ) ∧
      ∀ x v, 0 < v → (v ∈ g x ↔ Real.log v ∈ f x) := by
  classical
  let a := inverse f
  have ha : MaximalDecreasing a := inverse_maximal_decreasing hf
  have had : dom a = univ := maximal_decreasing_bounded_dom_range hf hdom
  have hR : Decreasing (logarithmicInputGraph a) := logarithmicInputGraph_decreasing ha.1
  have hRd : dom (logarithmicInputGraph a) = Ioi (0 : ℝ) := logarithmicInputGraph_dom had
  obtain ⟨H, ⟨hH, hRH, hHd⟩, _⟩ := unique_maximal_decreasing_completion
    ordConnected_Ioi (show (Ioi (0 : ℝ)).Nonempty from ⟨1, by norm_num⟩) hR hRd
  have hHd' : dom H ⊆ Ici (0 : ℝ) := by simpa only [closure_Ioi] using hHd
  let T : Operator := fun w => H (Real.exp w)
  have hT : Decreasing T := by
    apply increasing_iff_order.mpr
    intro x u y v hu hv hxy
    change -u ∈ H (Real.exp x) at hu
    change -v ∈ H (Real.exp y) at hv
    have h := Decreasing.le_of_lt hH.1 hu hv (Real.exp_lt_exp.mpr hxy)
    linarith
  have haT : a ≤ T := by
    intro w p hp
    apply hRH (Real.exp w)
    simpa only [logarithmicInputGraph, if_pos (Real.exp_pos w), Real.log_exp] using hp
  have hEq : a = T := MaximalDecreasing.eq_of_le ha hT haT
  have hHpos (v : ℝ) (hv : 0 < v) : H v = a (Real.log v) := by
    have h := congrFun hEq (Real.log v)
    simpa only [T, Real.exp_log hv] using h.symm
  have hHbounds {v p : ℝ} (hv : 0 < v) (hp : p ∈ H v) : p ∈ Icc (0 : ℝ) B := by
    rw [hHpos v hv] at hp
    exact hdom ⟨Real.log v, hp⟩
  have hHone : (H 1).Nonempty := by
    rw [hHpos 1 (by norm_num)]
    have h : Real.log 1 ∈ dom a := by rw [had]; trivial
    exact h
  have hH0 : Nonnegative H := by
    intro v p hp
    have hv : 0 ≤ v := hHd' ⟨p, hp⟩
    rcases lt_or_eq_of_le hv with hvpos | hvzero
    · exact (hHbounds hvpos hp).1
    · subst v
      obtain ⟨r, hr⟩ := hHone
      have hr0 := (hHbounds (by norm_num : (0 : ℝ) < 1) hr).1
      have hle := Decreasing.le_of_lt hH.1 hp hr (by norm_num : (0 : ℝ) < 1)
      exact hr0.trans hle
  have hHray {p : ℝ} (hp : B ≤ p) : p ∈ H 0 := by
    by_contra hn
    obtain ⟨y, v, hv, hbad⟩ := (maximalDecreasing_iff_positive_witness.mp hH).2 0 p hn
    have hy : 0 ≤ y := hHd' ⟨v, hv⟩
    rcases lt_or_eq_of_le hy with hypos | hyzero
    · have hvB := (hHbounds hypos hv).2
      have hh : (0-y)*(p-v) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      exact (not_lt_of_ge hh) hbad
    · rw [← hyzero] at hbad
      norm_num at hbad
  refine ⟨inverse H, inverse_maximal_decreasing hH, ?_, ?_, ?_, ?_⟩
  · intro x v hv
    exact hHd' ⟨x, hv⟩
  · intro p hp
    by_cases hBp : B ≤ p
    · exact ⟨0, hHray hBp⟩
    · have hx : ∃ x ∈ dom f, x < p := by
        by_contra hn
        have hl : p ∈ lowerBounds (dom f) := by
          intro x hx
          exact le_of_not_gt (fun h => hn ⟨x, hx, h⟩)
        have h := hz.2 hl
        exact (not_le_of_gt hp) h
      obtain ⟨x, ⟨w, hw⟩, hxp⟩ := hx
      have hxH : x ∈ H (Real.exp w) := by
        rw [hHpos _ (Real.exp_pos w), Real.log_exp]
        exact hw
      have hBH : B ∈ H 0 := hHray le_rfl
      exact (decreasing_ran_ordConnected hH).out ⟨Real.exp w, hxH⟩ ⟨0, hBH⟩
        ⟨hxp.le, le_of_not_ge hBp⟩
  · rintro x ⟨v, hv⟩
    exact hH0 hv
  · intro x v hv
    change x ∈ H v ↔ Real.log v ∈ f x
    rw [hHpos v hv]
    rfl


/-- Restrict the completed nonnegative exponential to a finite initial interval.
The resulting graph retains every point of the raw exponential, including
points at the two endpoints, rather than merely agreeing on scalar interiors. -/
theorem initial_exponential_completion_exists {f : Operator} {B : ℝ}
    (hB : 0 < B) (hf : MaximalDecreasing f) (hdom : dom f ⊆ Icc (0 : ℝ) B)
    (hz : IsGLB (dom f) 0) :
    ∃ g : Operator, MaximalDecreasing g ∧
      interior (dom g) = Ioo (0 : ℝ) B ∧
      (∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ g x, 0 ≤ v) ∧
      (∀ x w, w ∈ f x → Real.exp w ∈ g x) := by
  classical
  obtain ⟨G, hG, hG0, hGd, _, hGpos⟩ := nonnegative_exponential_completion hf hdom hz
  have hIG : Ioo (0 : ℝ) B ⊆ dom G := fun _ hx => hGd hx.1
  let R := restrictOperator G (Ioo (0 : ℝ) B)
  have hR : Decreasing R := by
    intro x u y v hu hv
    exact hG.1 hu.2 hv.2
  obtain ⟨g, ⟨hg, hRg, hgd⟩, _⟩ := unique_maximal_decreasing_completion
    ordConnected_Ioo (nonempty_Ioo.mpr hB) hR (dom_restrictOperator hIG)
  have hgd' : dom g ⊆ Icc (0 : ℝ) B := by simpa only [closure_Ioo hB.ne] using hgd
  have hIg : Ioo (0 : ℝ) B ⊆ dom g := by
    intro x hx
    obtain ⟨v, hv⟩ := hIG hx
    exact ⟨v, hRg x ⟨hx, hv⟩⟩
  have hgi : interior (dom g) = Ioo (0 : ℝ) B := by
    apply Subset.antisymm
    · simpa only [interior_Icc] using interior_mono hgd'
    · exact interior_maximal hIg isOpen_Ioo
  have hGg : restrictOperator G (Ioo (0 : ℝ) B) ≤ g := hRg
  have hEq : ∀ x ∈ Ioo (0 : ℝ) B, G x = g x := by
    intro x hx
    apply Set.Subset.antisymm (fun v hv => hGg x ⟨hx, hv⟩)
    intro v hv
    by_contra hn
    obtain ⟨y, w, hw, hbad⟩ := (maximalDecreasing_iff_positive_witness.mp hG).2 x v hn
    have hxy : x ≠ y := by intro he; rw [he] at hbad; norm_num at hbad
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · let r := (x + min y B)/2
      have hxsmall : x < min y B := lt_min hlt hx.2
      have hxr : x < r := by dsimp [r]; linarith
      have hry : r < y := by have := min_le_left y B; dsimp [r]; linarith
      have hrB : r < B := by have := min_le_right y B; dsimp [r]; linarith
      have hr : r ∈ Ioo (0 : ℝ) B := ⟨hx.1.trans hxr, hrB⟩
      obtain ⟨z, hz⟩ := hIG hr
      have hzg := hGg r ⟨hr, hz⟩
      have hzv := Decreasing.le_of_lt hg.1 hv hzg hxr
      have hwz := Decreasing.le_of_lt hG.1 hz hw hry
      have hh : (x-y)*(v-w) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      exact (not_lt_of_ge hh) hbad
    · let r := (max y 0 + x)/2
      have hxlarge : max y 0 < x := max_lt hgt hx.1
      have hyr : y < r := by have := le_max_left y 0; dsimp [r]; linarith
      have hrx : r < x := by dsimp [r]; linarith
      have hr0 : 0 < r := by have := le_max_right y 0; dsimp [r]; linarith
      have hr : r ∈ Ioo (0 : ℝ) B := ⟨hr0, hrx.trans hx.2⟩
      obtain ⟨z, hz⟩ := hIG hr
      have hzg := hGg r ⟨hr, hz⟩
      have hvz := Decreasing.le_of_lt hg.1 hzg hv hrx
      have hzw := Decreasing.le_of_lt hG.1 hw hz hyr
      have hh : (x-y)*(v-w) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      exact (not_lt_of_ge hh) hbad
  refine ⟨g, hg, hgi, ?_, ?_⟩
  · intro x hx v hv
    exact hG0 ((hEq x hx).symm ▸ hv)
  · intro x w hw
    have hx := hdom ⟨w, hw⟩
    have hu : Real.exp w ∈ G x := (hGpos x (Real.exp w) (Real.exp_pos w)).mpr
      (by simpa only [Real.log_exp] using hw)
    apply (maximalDecreasing_iff_compatible.mp hg).2
    intro y v hv
    have hy := hgd' ⟨v, hv⟩
    rcases lt_trichotomy x y with hxy | hxy | hyx
    · let r := (x+y)/2
      have hxr : x < r := by dsimp [r]; linarith
      have hry : r < y := by dsimp [r]; linarith
      have hr : r ∈ Ioo (0 : ℝ) B := ⟨by linarith [hx.1], by linarith [hy.2]⟩
      obtain ⟨z, hz⟩ := hIG hr
      have hzv := Decreasing.le_of_lt hg.1 (hGg r ⟨hr,hz⟩) hv hry
      have hzu := Decreasing.le_of_lt hG.1 hu hz hxr
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    · rw [hxy]
      simp
    · let r := (x+y)/2
      have hyr : y < r := by dsimp [r]; linarith
      have hrx : r < x := by dsimp [r]; linarith
      have hr : r ∈ Ioo (0 : ℝ) B := ⟨by linarith [hy.1], by linarith [hx.2]⟩
      obtain ⟨z, hz⟩ := hIG hr
      have hvz := Decreasing.le_of_lt hg.1 hv (hGg r ⟨hr,hz⟩) hyr
      have huz := Decreasing.le_of_lt hG.1 hz hu hrx
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

theorem initial_exponential_completion_unique {f g₁ g₂ : Operator} {B : ℝ}
    (hB : 0 < B) (hf : MaximalDecreasing f)
    (hg₁ : MaximalDecreasing g₁) (hg₂ : MaximalDecreasing g₂)
    (hi₁ : interior (dom g₁) = Ioo (0 : ℝ) B)
    (hi₂ : interior (dom g₂) = Ioo (0 : ℝ) B)
    (hz₁ : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ g₁ x, 0 ≤ v)
    (hz₂ : ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ g₂ x, 0 ≤ v)
    (he₁ : ∀ x w, w ∈ f x → Real.exp w ∈ g₁ x)
    (he₂ : ∀ x w, w ∈ f x → Real.exp w ∈ g₂ x) : g₁ = g₂ := by
  have hf₁ : f ≤ logOp g₁ := by
    intro x w hw
    exact (logOp_mem_iff).mpr (he₁ x w hw)
  have hf₂ : f ≤ logOp g₂ := by
    intro x w hw
    exact (logOp_mem_iff).mpr (he₂ x w hw)
  have hlog₁ := MaximalDecreasing.eq_of_le hf (logOp_decreasing hg₁.1) hf₁
  have hlog₂ := MaximalDecreasing.eq_of_le hf (logOp_decreasing hg₂.1) hf₂
  apply nonnegative_initial_graph_eq_of_log_eq hB hg₁ hg₂ hi₁ hi₂ hz₁ hz₂
  intro x _
  rw [← hlog₁, ← hlog₂]

theorem unique_initial_exponential_completion {f : Operator} {B : ℝ}
    (hB : 0 < B) (hf : MaximalDecreasing f) (hdom : dom f ⊆ Icc (0 : ℝ) B)
    (hz : IsGLB (dom f) 0) :
    ∃! g : Operator, MaximalDecreasing g ∧
      interior (dom g) = Ioo (0 : ℝ) B ∧
      (∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ g x, 0 ≤ v) ∧
      (∀ x w, w ∈ f x → Real.exp w ∈ g x) := by
  obtain ⟨g, hg, hgi, hg0, hge⟩ := initial_exponential_completion_exists hB hf hdom hz
  refine ⟨g, ⟨hg,hgi,hg0,hge⟩, ?_⟩
  rintro g' ⟨hg',hgi',hg0',hge'⟩
  exact initial_exponential_completion_unique hB hf hg' hg hgi' hgi hg0' hg0 hge' hge


end ScalarMonotone.EndOfPaper
end
