import EndOfPaper.PowerProfileMajorants
import EndOfPaper.GeometricPrefixLower

/-!
The displayed power-network majorant as an actual completed profile.
-/

open Set Filter MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem affine_geometricPrefix_power_majorant {q : DecGraph}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hsm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    {A α : ℝ} (hA : 0 < A) (hα : 0 < α)
    (hQ : DecLE q.val (affinePowerProfile 0 A α hA.le hα).val)
    {m c : ℝ} (hm : 0 ≤ m) (hc : 0 ≤ c) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    geometricPrefixValue (fun x => m+c*s x) u ≤ Real.exp α*(m+c*A*u^(-α)) := by
  have hrdom := (completedProfileAffine_domain (m := m) (by norm_num) hqi hc).1
  have hr0 := completedProfileAffine_nonnegative (by norm_num) hqi hm hc hq0
  have hrs := completedProfileAffine_selection (m := m) (by norm_num) hqi hc hs
  have hrP := positive_log_area_affine_finite hsm (fun x hx => hq0 x hx _ (hs x hx))
    (positive_log_area_of_power_control hq0 hs hA hα hQ) hm hc
  exact affine_geometric_power_majorant hqi hq0 hsm hs hA hα hQ hm hc hu
    (geometric_hardy_scalar_selection (by norm_num) hrdom hr0 hrs hrP u hu)

theorem negative_power_division {u c α : ℝ} (hu : 0 < u) (hc : 0 < c) :
    (u/c)^(-α) = (c/u)^α := by
  rw [Real.rpow_def_of_pos (div_pos hu hc),Real.rpow_def_of_pos (div_pos hc hu),
    Real.log_div hu.ne' hc.ne',Real.log_div hc.ne' hu.ne']
  congr 1
  ring

def powerNetworkBound {L : ℕ} (D A α : ℝ) (m κ : Fin L → ℝ) (u : ℝ) : ℝ :=
  D*A*Real.exp (α*(L : ℝ))*(6/u)^α *
    ∏ i, (m i+κ i*A*(12/u)^α)

theorem power_network_bound_nonnegative {L : ℕ} {D A α : ℝ} {m κ : Fin L → ℝ}
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hm : ∀ i, 0 ≤ m i) (hκ : ∀ i, 0 ≤ κ i)
    {u : ℝ} (hu : 0 < u) : 0 ≤ powerNetworkBound D A α m κ u := by
  apply mul_nonneg
  · exact mul_nonneg (mul_nonneg (mul_nonneg hD hA) (Real.exp_pos _).le)
      (Real.rpow_nonneg (div_nonneg (by norm_num) hu.le) _)
  · exact Finset.prod_nonneg (fun i _ => add_nonneg (hm i)
      (mul_nonneg (mul_nonneg (hκ i) hA) (Real.rpow_nonneg (div_nonneg (by norm_num) hu.le) _)))

theorem power_network_bound_antitone {L : ℕ} {D A α : ℝ} {m κ : Fin L → ℝ}
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hα : 0 < α)
    (hm : ∀ i, 0 ≤ m i) (hκ : ∀ i, 0 ≤ κ i) :
    AntitoneOn (powerNetworkBound D A α m κ) (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hratio (c : ℝ) (hc : 0 ≤ c) : (c/y)^α ≤ (c/x)^α :=
    Real.rpow_le_rpow (div_nonneg hc hy.1.le)
      (div_le_div_of_nonneg_left hc hx.1 hxy) hα.le
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (hratio 6 (by norm_num))
      (mul_nonneg (mul_nonneg hD hA) (Real.exp_pos _).le)
  · apply Finset.prod_le_prod
    · intro i _
      exact add_nonneg (hm i) (mul_nonneg (mul_nonneg (hκ i) hA)
        (Real.rpow_nonneg (div_nonneg (by norm_num) hy.1.le) _))
    · intro i _
      exact add_le_add_left (mul_le_mul_of_nonneg_left (hratio 12 (by norm_num))
        (mul_nonneg (hκ i) hA)) _
  · exact Finset.prod_nonneg (fun i _ => add_nonneg (hm i)
      (mul_nonneg (mul_nonneg (hκ i) hA) (Real.rpow_nonneg (div_nonneg (by norm_num) hy.1.le) _)))
  · exact mul_nonneg (mul_nonneg (mul_nonneg hD hA) (Real.exp_pos _).le)
      (Real.rpow_nonneg (div_nonneg (by norm_num) hx.1.le) _)

theorem power_network_bound_continuous {L : ℕ} (D A α : ℝ) (m κ : Fin L → ℝ) :
    ContinuousOn (powerNetworkBound D A α m κ) (Ioo (0 : ℝ) 1) := by
  have hr (c : ℝ) (hc : 0 < c) : ContinuousOn (fun u : ℝ => (c/u)^α) (Ioo (0 : ℝ) 1) :=
    (continuousOn_const.div continuousOn_id (fun u hu => hu.1.ne')).rpow_const
      (fun u hu => Or.inl (div_pos hc hu.1).ne')
  exact (continuousOn_const.mul (hr 6 (by norm_num))).mul
    (continuousOn_finset_prod _ (fun i _ => continuousOn_const.add
      (continuousOn_const.mul (hr 12 (by norm_num)))))

def powerNetworkProfile {L : ℕ} (D A α : ℝ) (m κ : Fin L → ℝ)
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hα : 0 < α)
    (hm : ∀ i, 0 ≤ m i) (hκ : ∀ i, 0 ≤ κ i) : DecGraph :=
  ⟨completedDecreasingRestriction (Ioo (0 : ℝ) 1) (ofFun (powerNetworkBound D A α m κ)),
    (antitone_scalar_completion_properties isOpen_Ioo ordConnected_Ioo
      (nonempty_Ioo.mpr zero_lt_one) (power_network_bound_antitone hD hA hα hm hκ)).1⟩

theorem power_network_profile_properties {L : ℕ} {D A α : ℝ} {m κ : Fin L → ℝ}
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hα : 0 < α)
    (hm : ∀ i, 0 ≤ m i) (hκ : ∀ i, 0 ≤ κ i) :
    let P := powerNetworkProfile D A α m κ hD hA hα hm hκ
    interior (dom P.val) = Ioo (0 : ℝ) 1 ∧
    SelectionOn P.val (Ioo (0 : ℝ) 1) (powerNetworkBound D A α m κ) ∧
    ∀ u ∈ Ioo (0 : ℝ) 1, P.val u = {powerNetworkBound D A α m κ u} := by
  dsimp only
  have hR := antitone_scalar_completion_properties isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.mpr zero_lt_one) (power_network_bound_antitone hD hA hα hm hκ)
  refine ⟨hR.2.1,hR.2.2.2,?_⟩
  intro u hu
  exact fiber_of_continuous_selection (Or.inr (powerNetworkProfile D A α m κ hD hA hα hm hκ).property)
    isOpen_Ioo (fun x hx => ⟨_,hR.2.2.2 x hx⟩) hR.2.2.2
    (power_network_bound_continuous D A α m κ) hu

theorem power_network_bound_collect {L : ℕ} (D A α : ℝ) (m κ : Fin L → ℝ) (u : ℝ) :
    D*(A*(6/u)^α)*(∏ i, Real.exp α*(m i+κ i*A*(12/u)^α)) =
      powerNetworkBound D A α m κ u := by
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← Real.exp_nat_mul]
  unfold powerNetworkBound
  rw [mul_comm (L : ℝ) α]
  ring

theorem power_network_selection_bound {L : ℕ} {q : DecGraph}
    (hqi : interior (dom q.val) = Ioo (0 : ℝ) 1)
    (hq0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ v ∈ q.val x, 0 ≤ v)
    {s : ℝ → ℝ} (hsm : Measurable s) (hs : SelectionOn q.val (Ioo (0 : ℝ) 1) s)
    {D A α : ℝ} (hD : 0 ≤ D) (hA : 0 < A) (hα : 0 < α)
    (hQ : DecLE q.val (affinePowerProfile 0 A α hA.le hα).val)
    {m κ : Fin L → ℝ} (hm : ∀ i, 0 ≤ m i) (hκ : ∀ i, 0 ≤ κ i)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    D*s (u/6)*(∏ i, geometricPrefixValue (fun x => m i+κ i*s x) (u/12)) ≤
      powerNetworkBound D A α m κ u := by
  have hu6 : u/6 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have hu12 : u/12 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have hsB : s (u/6) ≤ A*(6/u)^α := by
    have hh := power_control_value_bound hA hα hQ _ hu6 _ (hs _ hu6)
    rwa [negative_power_division hu.1 (by norm_num)] at hh
  have hGB (i : Fin L) : geometricPrefixValue (fun x => m i+κ i*s x) (u/12) ≤
      Real.exp α*(m i+κ i*A*(12/u)^α) := by
    have hh := affine_geometricPrefix_power_majorant hqi hq0 hsm hs hA hα hQ (hm i) (hκ i) hu12
    rwa [negative_power_division hu.1 (by norm_num)] at hh
  rw [← power_network_bound_collect]
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left hsB hD
  · exact Finset.prod_le_prod (fun i _ => geometricPrefixValue_nonnegative _ _) (fun i _ => hGB i)
  · exact Finset.prod_nonneg (fun i _ => geometricPrefixValue_nonnegative _ _)
  · exact mul_nonneg hD (mul_nonneg hA.le (Real.rpow_nonneg (div_nonneg (by norm_num) hu.1.le) _))

end ScalarMonotone.EndOfPaper
end
