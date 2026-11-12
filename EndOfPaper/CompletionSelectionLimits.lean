import EndOfPaper.FamilyIntegral
import MonotoneOperators.CompletionLimits

/-!
Completion formulas for arbitrary open intervals (def:completedrestriction).
Interior limits are finite and attained; boundary-ray formulas retain their
extended endpoint values. Exact restrictions and uniqueness are supplied by
ScalarIntegration and MonotoneOperators.Completion.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace ScalarMonotone.EndOfPaper

/-- Interior one-sided limits for every open interval, including either
half-line and the whole real line. The finite endpoint values are attained. -/
theorem scalar_completion_interior_limits {φ : ℝ → ℝ} {I : Set ℝ}
    (hφ : MonotoneOn φ I) (hord : I.OrdConnected) (hopen : IsOpen I) (hne : I.Nonempty) :
    let C := completion I (restrictOperator (ofFun φ) I)
    MaximalIncreasing C ∧ dom C ⊆ closure I ∧
      ∀ x ∈ I,
        Tendsto φ (𝓝[<] x) (𝓝 (sInf (C x))) ∧
        Tendsto φ (𝓝[>] x) (𝓝 (sSup (C x))) ∧
        C x = Icc (sInf (C x)) (sSup (C x)) := by
  let g := restrictOperator (ofFun φ) I
  let C := completion I g
  have hg : Increasing g := by
    apply increasing_iff_order.mpr
    intro x u y v hu hv hxy
    have hu' : u = φ x := hu.2
    have hv' : v = φ y := hv.2
    simpa only [hu', hv'] using hφ hu.1 hv.1 hxy.le
  have hgd : dom g = I := dom_restrictOperator (fun x _ => ⟨φ x, rfl⟩)
  have hC : MaximalIncreasing C := completion_maximal hord hne hg hgd
  have hsel : SelectionOn C I φ := fun x hx => le_completion hg hgd x ⟨hx, rfl⟩
  have hCd : I ⊆ dom C := fun x hx => ⟨φ x, hsel x hx⟩
  refine ⟨hC, completion_dom_subset I g, ?_⟩
  intro x hx
  exact ⟨selection_tendsto_left hC hopen hCd hsel hx,
    selection_tendsto_right hC hopen hCd hsel hx,
    maximal_interior_fiber_eq_Icc hC (hopen.subset_interior_iff.mpr hCd hx)⟩

theorem completion_Ioo_left_extended (φ : ℝ → ℝ) {a b : ℝ} (hab : a < b) :
    completion (Ioo a b) (restrictOperator (ofFun φ) (Ioo a b)) a =
      {u : ℝ | (u : EReal) ≤ upperEndpoint (restrictOperator (ofFun φ) (Ioo a b)) a} := by
  have hcl : a ∈ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact ⟨le_rfl, hab.le⟩
  rw [completion_fiber_eq]
  ext u
  simp only [mem_setOf_eq, hcl, lowerEndpoint_Ioo_left_bot, bot_le, true_and]

theorem completion_Ioo_right_extended (φ : ℝ → ℝ) {a b : ℝ} (hab : a < b) :
    completion (Ioo a b) (restrictOperator (ofFun φ) (Ioo a b)) b =
      {u : ℝ | lowerEndpoint (restrictOperator (ofFun φ) (Ioo a b)) b ≤ (u : EReal)} := by
  have hcl : b ∈ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact ⟨hab.le, le_rfl⟩
  rw [completion_fiber_eq]
  ext u
  simp only [mem_setOf_eq, hcl, upperEndpoint_Ioo_right_top, le_top, true_and, and_true]

theorem completion_Ioi_left_extended (φ : ℝ → ℝ) (a : ℝ) :
    completion (Ioi a) (restrictOperator (ofFun φ) (Ioi a)) a =
      {u : ℝ | (u : EReal) ≤ upperEndpoint (restrictOperator (ofFun φ) (Ioi a)) a} := by
  have hcl : a ∈ closure (Ioi a) := by
    rw [closure_Ioi]
    change a ≤ a
    exact le_rfl
  rw [completion_fiber_eq]
  ext u
  simp only [mem_setOf_eq, hcl, lowerEndpoint_Ioi_left_bot, bot_le, true_and]

theorem completion_Iio_right_extended (φ : ℝ → ℝ) (b : ℝ) :
    completion (Iio b) (restrictOperator (ofFun φ) (Iio b)) b =
      {u : ℝ | lowerEndpoint (restrictOperator (ofFun φ) (Iio b)) b ≤ (u : EReal)} := by
  have hcl : b ∈ closure (Iio b) := by
    rw [closure_Iio]
    change b ≤ b
    exact le_rfl
  rw [completion_fiber_eq]
  ext u
  simp only [mem_setOf_eq, hcl, upperEndpoint_Iio_right_top, le_top, true_and, and_true]

end ScalarMonotone.EndOfPaper
end
