import EndOfPaper.NonnegativeGraphFibers
import MonotoneOperators.ExtremaExamples
import MonotoneOperators.ExtremaFinite

/-!
The actual lattice zero floor, logarithmic initial-domain
geometry and prefix log L1 derived from finite positive-log
area alone, without global log integrability or endpoint signs.
-/

open Set Filter MeasureTheory
open scoped Interval ENNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

/-- The actual lattice supremum with the global zero graph. -/
def nonnegativeFloorGraph (q : DecGraph) : DecGraph := q ⊔ DecGraph.constant 0

theorem nonnegativeFloorGraph_resolvent (q : DecGraph) (s : ℝ) :
    (nonnegativeFloorGraph q).J s = max (q.J s) s := by
  have hzero : (DecGraph.constant 0).J s = s := by
    have h := (DecGraph.mem_iff_J (DecGraph.constant 0)).mp
      (show (0 : ℝ) ∈ (DecGraph.constant 0).val s from rfl)
    simpa only [sub_zero] using h
  simpa only [nonnegativeFloorGraph, DecGraph.J_sup, hzero]

theorem nonnegativeFloorGraph_nonnegative (q : DecGraph) :
    Nonnegative (nonnegativeFloorGraph q).val := by
  intro x u hu
  have h := (DecGraph.mem_iff_J (nonnegativeFloorGraph q)).mp hu
  rw [nonnegativeFloorGraph_resolvent] at h
  have hm := le_max_right (q.J (x-u)) (x-u)
  rw [h] at hm
  linarith

theorem nonnegativeFloorGraph_positive_fibers (q : DecGraph) {x u : ℝ} (hu : 0 < u) :
    u ∈ (nonnegativeFloorGraph q).val x ↔ u ∈ q.val x := by
  classical
  rw [DecGraph.mem_iff_J, DecGraph.mem_iff_J, nonnegativeFloorGraph_resolvent]
  constructor
  · intro h
    have hle : q.J (x-u) ≤ x := (le_max_left (q.J (x-u)) (x-u)).trans_eq h
    have hge : x ≤ q.J (x-u) := by
      by_contra hn
      have hlt : max (q.J (x-u)) (x-u) < x := max_lt (lt_of_not_ge hn) (by linarith)
      rw [h] at hlt
      exact (lt_irrefl x) hlt
    exact le_antisymm hle hge
  · intro h
    rw [h, max_eq_left (by linarith : x-u ≤ x)]

theorem logarithm_nonnegative_floor (q : DecGraph) :
    logOp (nonnegativeFloorGraph q).val = logOp q.val := by
  ext x w
  simp only [logOp_mem_iff, nonnegativeFloorGraph_positive_fibers q (Real.exp_pos w)]

/-- Bounded input domain suffices here: the positive part is taken by the
literal lattice supremum, so no global sign is imposed on the original graph. -/
theorem bounded_domain_logarithm_maximal {q : Operator} {B : ℝ}
    (hq : MaximalDecreasing q) (hdom : dom q ⊆ Icc (0 : ℝ) B) :
    MaximalDecreasing (logOp q) := by
  let Q : DecGraph := ⟨q,hq⟩
  have hr : (1 : ℝ) ∈ ran q := by rw [maximal_decreasing_bounded_dom_range hq hdom]; trivial
  obtain ⟨x,hx⟩ := hr
  have hpos : ∃ c ∈ ran (nonnegativeFloorGraph Q).val, 0 < c := by
    refine ⟨1, ⟨x, ?_⟩, by norm_num⟩
    exact (nonnegativeFloorGraph_positive_fibers Q (by norm_num : (0 : ℝ) < 1)).mpr hx
  have h := logOp_maximal_decreasing (nonnegativeFloorGraph Q).property
    (nonnegativeFloorGraph_nonnegative Q) hpos
  rwa [logarithm_nonnegative_floor Q] at h

theorem logarithm_dom_subset {q : Operator} : dom (logOp q) ⊆ dom q := by
  rintro x ⟨w,hw⟩
  exact ⟨Real.exp w, logOp_mem_iff.mp hw⟩

theorem positive_initial_interval_in_log_dom {q : Operator} {a v : ℝ}
    (hq : MaximalDecreasing q) {B : ℝ} (hqi : interior (dom q) = Ioo (0 : ℝ) B)
    (ha : a ∈ Ioo (0 : ℝ) B) (hv : v ∈ q a) (hvpos : 0 < v) :
    Ioo (0 : ℝ) a ⊆ dom (logOp q) := by
  intro x hx
  have hxi : x ∈ interior (dom q) := by rw [hqi]; exact ⟨hx.1,hx.2.trans ha.2⟩
  obtain ⟨u,hu⟩ := interior_subset hxi
  have hvu := Decreasing.le_of_lt hq.1 hu hv hx.2
  have hu0 := hvpos.trans_le hvu
  exact ⟨Real.log u, logOp_mem_iff.mpr (by simpa only [Real.exp_log hu0] using hu)⟩

theorem logarithm_initial_domain {q : Operator} {B : ℝ}
    (hB : 0 < B) (hq : MaximalDecreasing q)
    (hqi : interior (dom q) = Ioo (0 : ℝ) B)
    (hpositive : ∃ a ∈ Ioo (0 : ℝ) B, ∃ v ∈ q a, 0 < v) :
    MaximalDecreasing (logOp q) ∧ dom (logOp q) ⊆ Icc (0 : ℝ) B ∧
      IsGLB (dom (logOp q)) 0 ∧ ∃ a ∈ dom (logOp q), 0 < a := by
  classical
  have hne : (interior (dom q)).Nonempty := by rw [hqi]; exact nonempty_Ioo.mpr hB
  have hqd : dom q ⊆ Icc (0 : ℝ) B := by
    simpa only [hqi,closure_Ioo hB.ne] using decreasing_dom_subset_closure_interior hq hne
  have hld : dom (logOp q) ⊆ Icc (0 : ℝ) B := logarithm_dom_subset.trans hqd
  obtain ⟨a,ha,v,hv,hvpos⟩ := hpositive
  have hprefix := positive_initial_interval_in_log_dom hq hqi ha hv hvpos
  have hzero : IsGLB (dom (logOp q)) 0 := by
    refine ⟨fun x hx => (hld hx).1, ?_⟩
    intro b hb
    by_contra hn
    have hb0 : 0 < b := lt_of_not_ge hn
    let x := min a b / 2
    have hx0 : 0 < x := div_pos (lt_min ha.1 hb0) (by norm_num)
    have hxa : x < a := by have := min_le_left a b; dsimp [x]; linarith [ha.1]
    have hxb : x < b := by have := min_le_right a b; dsimp [x]; linarith
    exact (not_le_of_gt hxb) (hb (hprefix ⟨hx0,hxa⟩))
  refine ⟨bounded_domain_logarithm_maximal hq hqd,hld,hzero,?_⟩
  exact ⟨a/2,hprefix ⟨by linarith [ha.1],by linarith [ha.1]⟩,by linarith [ha.1]⟩


open Filter MeasureTheory
open scoped Interval ENNReal

theorem positive_log_integrable_of_lintegral {s : ℝ → ℝ} {B : ℝ}
    (hs : Measurable s)
    (hi : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    IntegrableOn (fun x => max (Real.log (s x)) 0) (Ioo (0 : ℝ) B) volume := by
  have hm : Measurable (fun x => max (Real.log (s x)) 0) := by fun_prop
  exact (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => le_max_right (Real.log (s x)) 0))).mp hi.ne

/-- Only the positive logarithmic part is assumed integrable. Monotonicity
supplies the lower bound on each smaller interval where a positive value exists. -/
theorem logarithmic_prefix_integrable_of_positive_part {q : Operator} {B p : ℝ}
    (hq : Decreasing q) (hp : 0 < p) (hpB : p ≤ B)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q (Ioo (0 : ℝ) B) s)
    (hi : IntegrableOn (fun x => max (Real.log (s x)) 0) (Ioo (0 : ℝ) B) volume)
    (hpl : p ∈ dom (logOp q)) : IntervalIntegrable (fun x => Real.log (s x)) volume 0 p := by
  obtain ⟨w,hw⟩ := hpl
  have hbound (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) p) : w ≤ Real.log (s x) := by
    have hxB : x ∈ Ioo (0 : ℝ) B := ⟨hx.1,hx.2.trans_le hpB⟩
    have hle := Decreasing.le_of_lt hq (hs x hxB) (logOp_mem_iff.mp hw) hx.2
    have h := Real.log_le_log (Real.exp_pos w) hle
    simpa only [Real.log_exp] using h
  have hplus : IntegrableOn (fun x => max (Real.log (s x)) 0) (Ioo (0 : ℝ) p) volume :=
    hi.mono_set (fun x hx => ⟨hx.1,hx.2.trans_le hpB⟩)
  have hc : IntegrableOn (fun _ : ℝ => |w|) (Ioo (0 : ℝ) p) volume :=
    integrableOn_const.mpr (Or.inr (by simp))
  have hlogm : Measurable (fun x => Real.log (s x)) := by fun_prop
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hp.le).mpr
  apply (hplus.add hc).mono' hlogm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs]
  change |Real.log (s x)| ≤ max (Real.log (s x)) 0 + |w|
  have hlow := hbound x hx
  rcases le_total 0 (Real.log (s x)) with hpos | hneg
  · rw [abs_of_nonneg hpos, max_eq_left hpos]
    linarith [abs_nonneg w]
  · rw [abs_of_nonpos hneg, max_eq_right hneg]
    linarith [neg_le_abs w]

theorem logarithmic_selection_on_interior {q : Operator} {B : ℝ}
    (hq : MaximalDecreasing q) (hqd : dom q ⊆ Icc (0 : ℝ) B)
    {s : ℝ → ℝ} (hs : SelectionOn q (Ioo (0 : ℝ) B) s) :
    SelectionOn (logOp q) (interior (dom (logOp q))) (fun x => Real.log (s x)) := by
  intro p hp
  have hld : dom (logOp q) ⊆ Icc (0 : ℝ) B := logarithm_dom_subset.trans hqd
  have hpI : p ∈ Ioo (0 : ℝ) B := by
    simpa only [interior_Icc] using interior_mono hld hp
  obtain ⟨a,b,⟨hap,hpb⟩,hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (isOpen_interior.mem_nhds hp)
  let y := (p+b)/2
  have hpy : p < y := by dsimp [y]; linarith
  have hyb : y < b := by dsimp [y]; linarith
  have hy : y ∈ dom (logOp q) := interior_subset (hab ⟨hap.trans hpy,hyb⟩)
  obtain ⟨w,hw⟩ := hy
  have hle := Decreasing.le_of_lt hq.1 (hs p hpI) (logOp_mem_iff.mp hw) hpy
  have hspos := (Real.exp_pos w).trans_le hle
  exact logOp_mem_iff.mpr (by simpa only [Real.exp_log hspos] using hs p hpI)

theorem logarithmic_prefix_integrability {q : Operator} {B : ℝ}
    (hB : 0 < B) (hq : MaximalDecreasing q)
    (hqi : interior (dom q) = Ioo (0 : ℝ) B)
    {s : ℝ → ℝ} (hm : Measurable s) (hs : SelectionOn q (Ioo (0 : ℝ) B) s)
    (hi : (∫⁻ x in Ioo (0 : ℝ) B, ENNReal.ofReal (max (Real.log (s x)) 0)) < ∞) :
    SelectionOn (logOp q) (interior (dom (logOp q))) (fun x => Real.log (s x)) ∧
      ∀ p ∈ interior (dom (logOp q)), IntervalIntegrable (fun x => Real.log (s x)) volume 0 p := by
  have hne : (interior (dom q)).Nonempty := by rw [hqi]; exact nonempty_Ioo.mpr hB
  have hqd : dom q ⊆ Icc (0 : ℝ) B := by
    simpa only [hqi,closure_Ioo hB.ne] using decreasing_dom_subset_closure_interior hq hne
  have hld : dom (logOp q) ⊆ Icc (0 : ℝ) B := logarithm_dom_subset.trans hqd
  refine ⟨logarithmic_selection_on_interior hq hqd hs, ?_⟩
  intro p hp
  have hpI : p ∈ Ioo (0 : ℝ) B := by
    simpa only [interior_Icc] using interior_mono hld hp
  exact logarithmic_prefix_integrable_of_positive_part hq.1 hpI.1 hpI.2.le hm hs
    (positive_log_integrable_of_lintegral hm hi) (interior_subset hp)


end ScalarMonotone.EndOfPaper
end
