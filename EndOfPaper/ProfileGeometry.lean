import EndOfPaper.CompletedProfiles
import EndOfPaper.LocalHardy

/-!
The general-profile range and inverse substitution correspondences.
Initial interval geometry includes finite and infinite upper endpoints.
Both substitution domains are open convex upper intervals, and the
logarithmic substitution has no imposed positive lower endpoint.
-/

open Set Filter MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem inverse_selection_singleton_of_strictAnti {α : Operator} {a q : ℝ → ℝ}
    (ha : ∀ x ∈ dom α, α x = {a x}) (hm : StrictAntiOn a (dom α))
    {I : Set ℝ} (hq : SelectionOn (inverse α) I q) {p : ℝ} (hp : p ∈ I) :
    inverse α p = {q p} ∧ q p ∈ dom α ∧ a (q p) = p := by
  have hqp : p ∈ α (q p) := hq p hp
  have hdq : q p ∈ dom α := ⟨p, hqp⟩
  have heq : a (q p) = p := (mem_singleton_iff.mp ((ha _ hdq) ▸ hqp)).symm
  refine ⟨?_, hdq, heq⟩
  ext x
  constructor
  · intro hx
    have hdx : x ∈ dom α := ⟨p, hx⟩
    have hex : a x = p := (mem_singleton_iff.mp ((ha _ hdx) ▸ hx)).symm
    exact mem_singleton_iff.mpr (((hm.eq_iff_eq hdx hdq).mp (hex.trans heq.symm)).symm)
  · intro hx
    rw [mem_singleton_iff.mp hx]
    exact hq p hp

theorem profile_range_initial_geometry {α : Operator} (hα : MaximalDecreasing α)
    (ho : IsOpen (ran α)) (hz : IsGLB (ran α) 0)
    (hp : ∃ p ∈ ran α, 0 < p) :
    (ran α).OrdConnected ∧ (ran α).Nonempty ∧
      (∀ p ∈ ran α, 0 < p) ∧ (∀ p ∈ ran α, Ioo 0 p ⊆ ran α) ∧
      (∀ c ∈ Ioc (0 : ℝ) 1, ∀ p ∈ ran α, c*p ∈ ran α) := by
  simpa only [dom_inverse, ho.interior_eq] using
    decreasing_zero_inf_domain_geometry (inverse_maximal_decreasing hα) hz hp

theorem positive_initial_le_mem {I : Set ℝ}
    (hprefix : ∀ p ∈ I, Ioo 0 p ⊆ I) {p t : ℝ}
    (hp : p ∈ I) (ht : 0 < t) (htp : t ≤ p) : t ∈ I := by
  rcases lt_or_eq_of_le htp with h | rfl
  · exact hprefix p hp ⟨ht, h⟩
  · exact hp

theorem power_transform_strictMono {a : ℝ → ℝ} {D : Set ℝ} {κ : ℝ}
    (hm : StrictAntiOn a D) (ha : ∀ x ∈ D, 0 < a x) (hκ : 0 < κ) :
    StrictMonoOn (fun x => (a x)^((-1 : ℝ)/κ)) D := by
  intro x hx y hy hxy
  exact Real.rpow_lt_rpow_of_neg (ha y hy) (hm hx hy hxy)
    (div_neg_of_neg_of_pos (by norm_num) hκ)

theorem logarithmic_transform_strictMono {a : ℝ → ℝ} {D : Set ℝ}
    (hm : StrictAntiOn a D) (ha : ∀ x ∈ D, 0 < a x) :
    StrictMonoOn (fun x => -Real.log (a x)) D := by
  intro x hx y hy hxy
  exact neg_lt_neg (Real.log_lt_log (ha y hy) (hm hx hy hxy))

def powerSubstitutionDomain (I : Set ℝ) (κ : ℝ) : Set ℝ :=
  {y | 0 < y ∧ y^(-κ) ∈ I}

def exponentialSubstitutionDomain (I : Set ℝ) : Set ℝ :=
  {y | Real.exp (-y) ∈ I}

theorem powerSubstitutionDomain_geometry {I : Set ℝ} {κ : ℝ}
    (ho : IsOpen I) (hprefix : ∀ p ∈ I, Ioo 0 p ⊆ I) (hκ : 0 < κ) :
    IsOpen (powerSubstitutionDomain I κ) ∧ Convex ℝ (powerSubstitutionDomain I κ) ∧
      ∀ x ∈ powerSubstitutionDomain I κ, Ici x ⊆ powerSubstitutionDomain I κ := by
  have hup : ∀ x ∈ powerSubstitutionDomain I κ, Ici x ⊆ powerSubstitutionDomain I κ := by
    intro x hx y hxy
    have hy : 0 < y := hx.1.trans_le hxy
    exact ⟨hy, positive_initial_le_mem hprefix hx.2 (Real.rpow_pos_of_pos hy _)
      (Real.rpow_le_rpow_of_nonpos hx.1 hxy (neg_nonpos.mpr hκ.le))⟩
  have hc : ContinuousOn (fun y : ℝ => y^(-κ)) (Ioi 0) := fun y hy =>
    (Real.continuousAt_rpow_const y (-κ) (Or.inl hy.ne')).continuousWithinAt
  refine ⟨?_, ?_, hup⟩
  · exact hc.isOpen_inter_preimage isOpen_Ioi ho
  · exact (ordConnected_def.mpr (fun x hx y hy z hz => hup x hx hz.1)).convex

theorem exponentialSubstitutionDomain_geometry {I : Set ℝ}
    (ho : IsOpen I) (hprefix : ∀ p ∈ I, Ioo 0 p ⊆ I) :
    IsOpen (exponentialSubstitutionDomain I) ∧ Convex ℝ (exponentialSubstitutionDomain I) ∧
      ∀ x ∈ exponentialSubstitutionDomain I, Ici x ⊆ exponentialSubstitutionDomain I := by
  have hup : ∀ x ∈ exponentialSubstitutionDomain I, Ici x ⊆ exponentialSubstitutionDomain I := by
    intro x hx y hxy
    exact positive_initial_le_mem hprefix hx (Real.exp_pos _)
      (Real.exp_le_exp.mpr (neg_le_neg hxy))
  refine ⟨ho.preimage (Real.continuous_exp.comp continuous_neg), ?_, hup⟩
  exact (ordConnected_def.mpr (fun x hx y hy z hz => hup x hx hz.1)).convex

theorem powerSubstitutionDomain_point {I : Set ℝ} {κ p : ℝ}
    (hκ : 0 < κ) (hp : 0 < p) (hpI : p ∈ I) :
    p^((-1 : ℝ)/κ) ∈ powerSubstitutionDomain I κ := by
  refine ⟨Real.rpow_pos_of_pos hp _, ?_⟩
  rw [← Real.rpow_mul hp.le, show ((-1 : ℝ)/κ)*(-κ) = 1 by field_simp,
    Real.rpow_one]
  exact hpI

theorem exponentialSubstitutionDomain_point {I : Set ℝ} {p : ℝ}
    (hp : 0 < p) (hpI : p ∈ I) : -Real.log p ∈ exponentialSubstitutionDomain I := by
  change Real.exp (-(-Real.log p)) ∈ I
  simpa only [neg_neg, Real.exp_log hp] using hpI

end ScalarMonotone.EndOfPaper
end
