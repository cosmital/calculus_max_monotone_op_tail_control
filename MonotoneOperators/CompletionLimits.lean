import MonotoneOperators.Completion

/-!
# One-sided limits and completed fibers

The extended endpoints from the graph calculus are exactly the analytic
one-sided limits. Extended-real limits also cover divergence at finite
domain endpoints. Finite limits produce the prescribed outward rays.
-/

open Set Filter
open scoped Topology

namespace ScalarMonotone

theorem lowerEndpoint_restrict_ofFun (φ : ℝ → ℝ) (I : Set ℝ) (x : ℝ) :
    lowerEndpoint (restrictOperator (ofFun φ) I) x =
      sSup ((fun y => (φ y : EReal)) '' (I ∩ Iio x)) := by
  apply le_antisymm
  · apply iSup_le
    intro y
    apply iSup_le
    intro hyx
    apply iSup_le
    intro v
    apply iSup_le
    rintro ⟨hyI, hv⟩
    change v = φ y at hv
    subst v
    exact le_sSup ⟨y, ⟨hyI, hyx⟩, rfl⟩
  · apply sSup_le
    rintro v ⟨y, ⟨hyI, hyx⟩, rfl⟩
    exact le_iSup_of_le y (le_iSup_of_le hyx
      (le_iSup_of_le (φ y) (le_iSup_of_le ⟨hyI, rfl⟩ le_rfl)))

theorem upperEndpoint_restrict_ofFun (φ : ℝ → ℝ) (I : Set ℝ) (x : ℝ) :
    upperEndpoint (restrictOperator (ofFun φ) I) x =
      sInf ((fun y => (φ y : EReal)) '' (I ∩ Ioi x)) := by
  apply le_antisymm
  · apply le_sInf
    rintro v ⟨y, ⟨hyI, hyx⟩, rfl⟩
    exact iInf_le_of_le y (iInf_le_of_le hyx
      (iInf_le_of_le (φ y) (iInf_le_of_le ⟨hyI, rfl⟩ le_rfl)))
  · apply le_iInf
    intro y
    apply le_iInf
    intro hyx
    apply le_iInf
    intro v
    apply le_iInf
    rintro ⟨hyI, hv⟩
    change v = φ y at hv
    subst v
    exact sInf_le ⟨y, ⟨hyI, hyx⟩, rfl⟩

private theorem monotoneOn_ereal {φ : ℝ → ℝ} {I : Set ℝ} (hφ : MonotoneOn φ I) :
    MonotoneOn (fun y => (φ y : EReal)) I :=
  fun _ hx _ hy hxy => EReal.coe_le_coe_iff.mpr (hφ hx hy hxy)

theorem upperEndpoint_Ioo_left (φ : ℝ → ℝ) (a b : ℝ) :
    upperEndpoint (restrictOperator (ofFun φ) (Ioo a b)) a =
      sInf ((fun y => (φ y : EReal)) '' Ioo a b) := by
  rw [upperEndpoint_restrict_ofFun]
  rw [inter_eq_left.mpr (show Ioo a b ⊆ Ioi a from fun _ hy => hy.1)]

theorem lowerEndpoint_Ioo_right (φ : ℝ → ℝ) (a b : ℝ) :
    lowerEndpoint (restrictOperator (ofFun φ) (Ioo a b)) b =
      sSup ((fun y => (φ y : EReal)) '' Ioo a b) := by
  rw [lowerEndpoint_restrict_ofFun]
  rw [inter_eq_left.mpr (show Ioo a b ⊆ Iio b from fun _ hy => hy.2)]

/-- At the left endpoint, the upper graph endpoint is the inward right limit. -/
theorem tendsto_upperEndpoint_Ioo_left {φ : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hφ : MonotoneOn φ (Ioo a b)) :
    Tendsto (fun y => (φ y : EReal)) (𝓝[>] a)
      (𝓝 (upperEndpoint (restrictOperator (ofFun φ) (Ioo a b)) a)) := by
  rw [upperEndpoint_Ioo_left]
  exact MonotoneOn.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.mpr hab)
    (monotoneOn_ereal hφ) ⟨⊥, fun _ _ => bot_le⟩

/-- At the right endpoint, the lower graph endpoint is the inward left limit. -/
theorem tendsto_lowerEndpoint_Ioo_right {φ : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hφ : MonotoneOn φ (Ioo a b)) :
    Tendsto (fun y => (φ y : EReal)) (𝓝[<] b)
      (𝓝 (lowerEndpoint (restrictOperator (ofFun φ) (Ioo a b)) b)) := by
  rw [lowerEndpoint_Ioo_right]
  exact MonotoneOn.tendsto_nhdsWithin_Ioo_left (nonempty_Ioo.mpr hab)
    (monotoneOn_ereal hφ) ⟨⊤, fun _ _ => le_top⟩

theorem tendsto_upperEndpoint_Ioi {φ : ℝ → ℝ} {a : ℝ}
    (hφ : MonotoneOn φ (Ioi a)) :
    Tendsto (fun y => (φ y : EReal)) (𝓝[>] a)
      (𝓝 (upperEndpoint (restrictOperator (ofFun φ) (Ioi a)) a)) := by
  rw [upperEndpoint_restrict_ofFun, inter_self]
  exact (monotoneOn_ereal hφ).tendsto_nhdsGT ⟨⊥, fun _ _ => bot_le⟩

theorem tendsto_lowerEndpoint_Iio {φ : ℝ → ℝ} {b : ℝ}
    (hφ : MonotoneOn φ (Iio b)) :
    Tendsto (fun y => (φ y : EReal)) (𝓝[<] b)
      (𝓝 (lowerEndpoint (restrictOperator (ofFun φ) (Iio b)) b)) := by
  rw [lowerEndpoint_restrict_ofFun, inter_self]
  exact (monotoneOn_ereal hφ).tendsto_nhdsLT ⟨⊤, fun _ _ => le_top⟩

theorem tendsto_lowerEndpoint_Ioo_interior {φ : ℝ → ℝ} {a b x : ℝ}
    (hφ : MonotoneOn φ (Ioo a b)) (hx : x ∈ Ioo a b) :
    Tendsto (fun y => (φ y : EReal)) (𝓝[<] x)
      (𝓝 (lowerEndpoint (restrictOperator (ofFun φ) (Ioo a b)) x)) := by
  rw [lowerEndpoint_restrict_ofFun]
  have hset : Ioo a b ∩ Iio x = Ioo a x := by
    ext y
    constructor
    · rintro ⟨hy, hyx⟩
      exact ⟨hy.1, hyx⟩
    · rintro ⟨hay, hyx⟩
      exact ⟨⟨hay, hyx.trans hx.2⟩, hyx⟩
  rw [hset]
  exact MonotoneOn.tendsto_nhdsWithin_Ioo_left (nonempty_Ioo.mpr hx.1)
    ((monotoneOn_ereal hφ).mono (fun _ hy => ⟨hy.1, hy.2.trans hx.2⟩))
    ⟨⊤, fun _ _ => le_top⟩

theorem tendsto_upperEndpoint_Ioo_interior {φ : ℝ → ℝ} {a b x : ℝ}
    (hφ : MonotoneOn φ (Ioo a b)) (hx : x ∈ Ioo a b) :
    Tendsto (fun y => (φ y : EReal)) (𝓝[>] x)
      (𝓝 (upperEndpoint (restrictOperator (ofFun φ) (Ioo a b)) x)) := by
  rw [upperEndpoint_restrict_ofFun]
  have hset : Ioo a b ∩ Ioi x = Ioo x b := by
    ext y
    constructor
    · rintro ⟨hy, hxy⟩
      exact ⟨hxy, hy.2⟩
    · rintro ⟨hxy, hyb⟩
      exact ⟨⟨hx.1.trans hxy, hyb⟩, hxy⟩
  rw [hset]
  exact MonotoneOn.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.mpr hx.2)
    ((monotoneOn_ereal hφ).mono (fun _ hy => ⟨hx.1.trans hy.1, hy.2⟩))
    ⟨⊥, fun _ _ => bot_le⟩

theorem lowerEndpoint_Ioo_left_bot (φ : ℝ → ℝ) (a b : ℝ) :
    lowerEndpoint (restrictOperator (ofFun φ) (Ioo a b)) a = ⊥ := by
  rw [lowerEndpoint_restrict_ofFun]
  have he : Ioo a b ∩ Iio a = ∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    rintro y ⟨hy, hya⟩
    exact lt_asymm hy.1 hya
  simp [he]

theorem upperEndpoint_Ioo_right_top (φ : ℝ → ℝ) (a b : ℝ) :
    upperEndpoint (restrictOperator (ofFun φ) (Ioo a b)) b = ⊤ := by
  rw [upperEndpoint_restrict_ofFun]
  have he : Ioo a b ∩ Ioi b = ∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    rintro y ⟨hy, hby⟩
    exact lt_asymm hy.2 hby
  simp [he]

theorem completion_Ioo_left_of_finite_limit {φ : ℝ → ℝ} {a b l : ℝ}
    (hab : a < b) (hφ : MonotoneOn φ (Ioo a b))
    (hl : Tendsto φ (𝓝[>] a) (𝓝 l)) :
    completion (Ioo a b) (restrictOperator (ofFun φ) (Ioo a b)) a = Iic l := by
  apply completion_left_ray
  · rw [closure_Ioo hab.ne]
    exact ⟨le_rfl, hab.le⟩
  · exact lowerEndpoint_Ioo_left_bot φ a b
  · exact tendsto_nhds_unique (tendsto_upperEndpoint_Ioo_left hab hφ)
      (EReal.tendsto_coe.mpr hl)

theorem completion_Ioo_right_of_finite_limit {φ : ℝ → ℝ} {a b r : ℝ}
    (hab : a < b) (hφ : MonotoneOn φ (Ioo a b))
    (hr : Tendsto φ (𝓝[<] b) (𝓝 r)) :
    completion (Ioo a b) (restrictOperator (ofFun φ) (Ioo a b)) b = Ici r := by
  apply completion_right_ray
  · rw [closure_Ioo hab.ne]
    exact ⟨hab.le, le_rfl⟩
  · exact tendsto_nhds_unique (tendsto_lowerEndpoint_Ioo_right hab hφ)
      (EReal.tendsto_coe.mpr hr)
  · exact upperEndpoint_Ioo_right_top φ a b

private theorem ereal_tendsto_bot {α : Type*} {l : Filter α} {φ : α → ℝ}
    (h : Tendsto φ l atBot) : Tendsto (fun x => (φ x : EReal)) l (𝓝 ⊥) := by
  rw [EReal.tendsto_nhds_bot_iff_real]
  intro r
  exact (h.eventually (eventually_lt_atBot r)).mono
    (fun _ hx => EReal.coe_lt_coe_iff.mpr hx)

private theorem ereal_tendsto_top {α : Type*} {l : Filter α} {φ : α → ℝ}
    (h : Tendsto φ l atTop) : Tendsto (fun x => (φ x : EReal)) l (𝓝 ⊤) := by
  rw [EReal.tendsto_nhds_top_iff_real]
  intro r
  exact (h.eventually (eventually_gt_atTop r)).mono
    (fun _ hx => EReal.coe_lt_coe_iff.mpr hx)

theorem completion_Ioo_left_of_infinite_limit {φ : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hφ : MonotoneOn φ (Ioo a b))
    (hl : Tendsto φ (𝓝[>] a) atBot) :
    completion (Ioo a b) (restrictOperator (ofFun φ) (Ioo a b)) a = ∅ := by
  apply completion_empty_of_upper_bot
  exact tendsto_nhds_unique (tendsto_upperEndpoint_Ioo_left hab hφ) (ereal_tendsto_bot hl)

theorem completion_Ioo_right_of_infinite_limit {φ : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hφ : MonotoneOn φ (Ioo a b))
    (hr : Tendsto φ (𝓝[<] b) atTop) :
    completion (Ioo a b) (restrictOperator (ofFun φ) (Ioo a b)) b = ∅ := by
  apply completion_empty_of_lower_top
  exact tendsto_nhds_unique (tendsto_lowerEndpoint_Ioo_right hab hφ) (ereal_tendsto_top hr)

/-- At an interior jump, the completion fills exactly the interval between its one-sided limits. -/
theorem completion_Ioo_interior_of_limits {φ : ℝ → ℝ} {a b x l r : ℝ}
    (hφ : MonotoneOn φ (Ioo a b)) (hx : x ∈ Ioo a b)
    (hl : Tendsto φ (𝓝[<] x) (𝓝 l)) (hr : Tendsto φ (𝓝[>] x) (𝓝 r)) :
    completion (Ioo a b) (restrictOperator (ofFun φ) (Ioo a b)) x = Icc l r := by
  have hL : lowerEndpoint (restrictOperator (ofFun φ) (Ioo a b)) x = (l : EReal) :=
    tendsto_nhds_unique (tendsto_lowerEndpoint_Ioo_interior hφ hx) (EReal.tendsto_coe.mpr hl)
  have hR : upperEndpoint (restrictOperator (ofFun φ) (Ioo a b)) x = (r : EReal) :=
    tendsto_nhds_unique (tendsto_upperEndpoint_Ioo_interior hφ hx) (EReal.tendsto_coe.mpr hr)
  rw [completion_fiber_eq]
  ext u
  simp [subset_closure hx, hL, hR, EReal.coe_le_coe_iff]

/-- The two finite interior limits exist, and the completed fiber fills the jump. -/
theorem completion_Ioo_interior_limits {φ : ℝ → ℝ} {a b x : ℝ}
    (hφ : MonotoneOn φ (Ioo a b)) (hx : x ∈ Ioo a b) :
    ∃ l r : ℝ, Tendsto φ (𝓝[<] x) (𝓝 l) ∧ Tendsto φ (𝓝[>] x) (𝓝 r) ∧
      completion (Ioo a b) (restrictOperator (ofFun φ) (Ioo a b)) x = Icc l r := by
  have hleft : Ioo a x ⊆ Ioo a b := fun _ hy => ⟨hy.1, hy.2.trans hx.2⟩
  have hright : Ioo x b ⊆ Ioo a b := fun _ hy => ⟨hx.1.trans hy.1, hy.2⟩
  have hBleft : BddAbove (φ '' Ioo a x) := by
    refine ⟨φ x, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    exact hφ (hleft hy) hx hy.2.le
  have hBright : BddBelow (φ '' Ioo x b) := by
    refine ⟨φ x, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    exact hφ hx (hright hy) hy.1.le
  have hl : Tendsto φ (𝓝[<] x) (𝓝 (sSup (φ '' Ioo a x))) :=
    MonotoneOn.tendsto_nhdsWithin_Ioo_left (nonempty_Ioo.mpr hx.1) (hφ.mono hleft) hBleft
  have hr : Tendsto φ (𝓝[>] x) (𝓝 (sInf (φ '' Ioo x b))) :=
    MonotoneOn.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.mpr hx.2) (hφ.mono hright) hBright
  exact ⟨_, _, hl, hr, completion_Ioo_interior_of_limits hφ hx hl hr⟩

theorem lowerEndpoint_Ioi_left_bot (φ : ℝ → ℝ) (a : ℝ) :
    lowerEndpoint (restrictOperator (ofFun φ) (Ioi a)) a = ⊥ := by
  rw [lowerEndpoint_restrict_ofFun]
  have he : Ioi a ∩ Iio a = ∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    rintro y ⟨hay, hya⟩
    change a < y at hay
    change y < a at hya
    exact lt_asymm hay hya
  simp [he]

theorem upperEndpoint_Iio_right_top (φ : ℝ → ℝ) (b : ℝ) :
    upperEndpoint (restrictOperator (ofFun φ) (Iio b)) b = ⊤ := by
  rw [upperEndpoint_restrict_ofFun]
  have he : Iio b ∩ Ioi b = ∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    rintro y ⟨hyb, hby⟩
    change y < b at hyb
    change b < y at hby
    exact lt_asymm hyb hby
  simp [he]

theorem completion_Ioi_left_of_finite_limit {φ : ℝ → ℝ} {a l : ℝ}
    (hφ : MonotoneOn φ (Ioi a)) (hl : Tendsto φ (𝓝[>] a) (𝓝 l)) :
    completion (Ioi a) (restrictOperator (ofFun φ) (Ioi a)) a = Iic l := by
  apply completion_left_ray
  · rw [closure_Ioi]
    change a ≤ a
    exact le_rfl
  · exact lowerEndpoint_Ioi_left_bot φ a
  · exact tendsto_nhds_unique (tendsto_upperEndpoint_Ioi hφ) (EReal.tendsto_coe.mpr hl)

theorem completion_Iio_right_of_finite_limit {φ : ℝ → ℝ} {b r : ℝ}
    (hφ : MonotoneOn φ (Iio b)) (hr : Tendsto φ (𝓝[<] b) (𝓝 r)) :
    completion (Iio b) (restrictOperator (ofFun φ) (Iio b)) b = Ici r := by
  apply completion_right_ray
  · rw [closure_Iio]
    change b ≤ b
    exact le_rfl
  · exact tendsto_nhds_unique (tendsto_lowerEndpoint_Iio hφ) (EReal.tendsto_coe.mpr hr)
  · exact upperEndpoint_Iio_right_top φ b

theorem completion_Ioi_left_of_infinite_limit {φ : ℝ → ℝ} {a : ℝ}
    (hφ : MonotoneOn φ (Ioi a)) (hl : Tendsto φ (𝓝[>] a) atBot) :
    completion (Ioi a) (restrictOperator (ofFun φ) (Ioi a)) a = ∅ := by
  apply completion_empty_of_upper_bot
  exact tendsto_nhds_unique (tendsto_upperEndpoint_Ioi hφ) (ereal_tendsto_bot hl)

theorem completion_Iio_right_of_infinite_limit {φ : ℝ → ℝ} {b : ℝ}
    (hφ : MonotoneOn φ (Iio b)) (hr : Tendsto φ (𝓝[<] b) atTop) :
    completion (Iio b) (restrictOperator (ofFun φ) (Iio b)) b = ∅ := by
  apply completion_empty_of_lower_top
  exact tendsto_nhds_unique (tendsto_lowerEndpoint_Iio hφ) (ereal_tendsto_top hr)

end ScalarMonotone
