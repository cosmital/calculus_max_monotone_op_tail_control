import MonotoneOperators.ExtremaComplete
import MonotoneOperators.OrderGeometry

/-! # The odd lattice median and its resolvents at every positive scale -/

open Set

namespace ScalarMonotone

abbrev Majority (r : ℕ) := {I : Finset (Fin (2*r+1)) // I.card = r+1}

instance majority_nonempty (r : ℕ) : Nonempty (Majority r) := by
  obtain ⟨I, _, hcard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin (2*r+1)))) (n := r+1) (by simp; omega)
  exact ⟨⟨I, hcard⟩⟩

instance majority_members_nonempty {r : ℕ} (I : Majority r) :
    Nonempty {i // i ∈ I.val} := by
  obtain ⟨i, hi⟩ := Finset.card_pos.1 (show 0 < I.val.card by rw [I.property]; omega)
  exact ⟨⟨i, hi⟩⟩

theorem majority_intersects {r : ℕ} (I J : Majority r) :
    ∃ i, i ∈ I.val ∧ i ∈ J.val := by
  have hu : (I.val ∪ J.val).card ≤ 2*r+1 := by
    simpa using Finset.card_le_card (Finset.subset_univ (I.val ∪ J.val))
  have he := Finset.card_union_add_card_inter I.val J.val
  have hi := I.property
  have hj := J.property
  have hn : 0 < (I.val ∩ J.val).card := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.1 hn
  exact ⟨i, (Finset.mem_inter.1 hi).1, (Finset.mem_inter.1 hi).2⟩

noncomputable def latticeMedianInfSup {L : Type*} [ConditionallyCompleteLattice L]
    (r : ℕ) (A : Fin (2*r+1) → L) : L :=
  ⨅ I : Majority r, ⨆ i : {i // i ∈ I.val}, A i.val

noncomputable def latticeMedianSupInf {L : Type*} [ConditionallyCompleteLattice L]
    (r : ℕ) (A : Fin (2*r+1) → L) : L :=
  ⨆ I : Majority r, ⨅ i : {i // i ∈ I.val}, A i.val

/-- The scalar odd median's two order-statistic descriptions agree. -/
theorem scalar_median_minmax_eq_maxmin (r : ℕ) (q : Fin (2*r+1) → ℝ) :
    latticeMedianInfSup r q = latticeMedianSupInf r q := by
  classical
  have hle : latticeMedianSupInf r q ≤ latticeMedianInfSup r q := by
    apply le_ciInf
    intro J
    apply ciSup_le
    intro I
    obtain ⟨i, hi, hj⟩ := majority_intersects I J
    exact (ciInf_le (finite_range (fun j : {j // j ∈ I.val} => q j.val)).bddBelow
      ⟨i, hi⟩).trans (le_ciSup
        (finite_range (fun j : {j // j ∈ J.val} => q j.val)).bddAbove ⟨i, hj⟩)
  apply le_antisymm _ hle
  by_contra hn
  have hlt := lt_of_not_ge hn
  obtain ⟨t, hlo, hhi⟩ := exists_between hlt
  let S : Finset (Fin (2*r+1)) := Finset.univ.filter (fun i => q i ≤ t)
  by_cases hs : r+1 ≤ S.card
  · obtain ⟨I, hIS, hIcard⟩ := Finset.exists_subset_card_eq hs
    let J : Majority r := ⟨I, hIcard⟩
    letI : Nonempty {i // i ∈ J.val} := majority_members_nonempty J
    have hsup : (⨆ i : {i // i ∈ J.val}, q i.val) ≤ t := by
      apply ciSup_le
      intro i
      exact (Finset.mem_filter.1 (hIS i.property)).2
    have hupper : latticeMedianInfSup r q ≤ t :=
      (ciInf_le (finite_range (fun K : Majority r =>
        ⨆ i : {i // i ∈ K.val}, q i.val)).bddBelow J).trans hsup
    exact (not_le_of_gt hhi) hupper
  · have hlarge : r+1 ≤ (Finset.univ \ S).card := by
      have he := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
      have he' : (Finset.univ \ S).card + S.card = 2*r+1 := by simpa using he
      omega
    obtain ⟨I, hIS, hIcard⟩ := Finset.exists_subset_card_eq hlarge
    let J : Majority r := ⟨I, hIcard⟩
    letI : Nonempty {i // i ∈ J.val} := majority_members_nonempty J
    have hgt : ∀ i ∈ I, t < q i := by
      intro i hi
      have hn := (Finset.mem_sdiff.1 (hIS hi)).2
      exact lt_of_not_ge (by simpa [S] using hn)
    have hne : I.Nonempty := Finset.card_pos.1 (by rw [hIcard]; omega)
    obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image I q hne
    have hlow : q i ≤ latticeMedianSupInf r q := by
      have hinner : q i ≤ ⨅ j : {j // j ∈ J.val}, q j.val :=
        le_ciInf (fun j => hmin j.val j.property)
      exact hinner.trans (le_ciSup (finite_range (fun K : Majority r =>
        ⨅ j : {j // j ∈ K.val}, q j.val)).bddAbove J)
    exact (not_le_of_gt ((hgt i hi).trans_le hlow)) hlo.le

noncomputable def scalarMedian (r : ℕ) (q : Fin (2*r+1) → ℝ) : ℝ :=
  latticeMedianInfSup r q

theorem latticeMedian_majority_bounds {L : Type*} [ConditionallyCompleteLattice L]
    (r : ℕ) (A : Fin (2*r+1) → L) {l h : L}
    (heq : latticeMedianInfSup r A = latticeMedianSupInf r A)
    (hm : ∃ I : Majority r, ∀ i ∈ I.val, l ≤ A i ∧ A i ≤ h) :
    l ≤ latticeMedianInfSup r A ∧ latticeMedianInfSup r A ≤ h := by
  obtain ⟨I, hI⟩ := hm
  constructor
  · rw [heq]
    exact (le_ciInf (fun i : {i // i ∈ I.val} => (hI i.val i.property).1)).trans
      (le_ciSup (finite_range (fun J : Majority r =>
        ⨅ i : {i // i ∈ J.val}, A i.val)).bddAbove I)
  · exact (ciInf_le (finite_range (fun J : Majority r =>
      ⨆ i : {i // i ∈ J.val}, A i.val)).bddBelow I).trans
      (ciSup_le (fun i : {i // i ∈ I.val} => (hI i.val i.property).2))

theorem scalarMedian_majority (r : ℕ) (q : Fin (2*r+1) → ℝ) {l h : ℝ}
    (hm : ∃ I : Majority r, ∀ i ∈ I.val, l ≤ q i ∧ q i ≤ h) :
    l ≤ scalarMedian r q ∧ scalarMedian r q ≤ h :=
  latticeMedian_majority_bounds r q (scalar_median_minmax_eq_maxmin r q) hm

theorem IncGraph.J_latticeMedianInfSup (r : ℕ) (A : Fin (2*r+1) → IncGraph) (s : ℝ) :
    (latticeMedianInfSup r A).J s = latticeMedianSupInf r (fun i => (A i).J s) := by
  unfold latticeMedianInfSup latticeMedianSupInf
  rw [IncGraph.J_iInf _ (finite_range _).bddBelow]
  congr 1
  funext I
  exact IncGraph.J_iSup _ (finite_range _).bddAbove s

theorem IncGraph.J_latticeMedianSupInf (r : ℕ) (A : Fin (2*r+1) → IncGraph) (s : ℝ) :
    (latticeMedianSupInf r A).J s = latticeMedianInfSup r (fun i => (A i).J s) := by
  unfold latticeMedianInfSup latticeMedianSupInf
  rw [IncGraph.J_iSup _ (finite_range _).bddAbove]
  congr 1
  funext I
  exact IncGraph.J_iInf _ (finite_range _).bddBelow s

theorem DecGraph.J_latticeMedianInfSup (r : ℕ) (A : Fin (2*r+1) → DecGraph) (s : ℝ) :
    (latticeMedianInfSup r A).J s = latticeMedianInfSup r (fun i => (A i).J s) := by
  unfold latticeMedianInfSup
  rw [DecGraph.J_iInf _ (finite_range _).bddBelow]
  congr 1
  funext I
  exact DecGraph.J_iSup _ (finite_range _).bddAbove s

theorem DecGraph.J_latticeMedianSupInf (r : ℕ) (A : Fin (2*r+1) → DecGraph) (s : ℝ) :
    (latticeMedianSupInf r A).J s = latticeMedianSupInf r (fun i => (A i).J s) := by
  unfold latticeMedianSupInf
  rw [DecGraph.J_iSup _ (finite_range _).bddAbove]
  congr 1
  funext I
  exact DecGraph.J_iInf _ (finite_range _).bddBelow s

theorem inc_lattice_median (r : ℕ) (A : Fin (2*r+1) → IncGraph) :
    latticeMedianInfSup r A = latticeMedianSupInf r A := by
  apply IncGraph.J_injective
  funext s
  rw [IncGraph.J_latticeMedianInfSup, IncGraph.J_latticeMedianSupInf]
  exact (scalar_median_minmax_eq_maxmin r _).symm

theorem dec_lattice_median (r : ℕ) (A : Fin (2*r+1) → DecGraph) :
    latticeMedianInfSup r A = latticeMedianSupInf r A := by
  apply DecGraph.J_injective
  funext s
  rw [DecGraph.J_latticeMedianInfSup, DecGraph.J_latticeMedianSupInf]
  exact scalar_median_minmax_eq_maxmin r _

theorem orderIso_latticeMedian {L K : Type*} [ConditionallyCompleteLattice L]
    [ConditionallyCompleteLattice K] (e : L ≃o K) (r : ℕ) (A : Fin (2*r+1) → L) :
    e (latticeMedianInfSup r A) = latticeMedianInfSup r (fun i => e (A i)) := by
  unfold latticeMedianInfSup
  rw [e.map_ciInf (finite_range _).bddBelow]
  congr 1
  funext I
  exact e.map_ciSup (finite_range _).bddAbove

theorem inc_lattice_median_resolvent_scale (r : ℕ) (A : Fin (2*r+1) → IncGraph)
    (c : ℝ) (hc : 0 < c) (s : ℝ) :
    (IncGraph.scaleOrderIso c hc (latticeMedianInfSup r A)).J s =
      scalarMedian r (fun i => (IncGraph.scaleOrderIso c hc (A i)).J s) := by
  rw [orderIso_latticeMedian, IncGraph.J_latticeMedianInfSup]
  exact (scalar_median_minmax_eq_maxmin r _).symm

theorem dec_lattice_median_resolvent_scale (r : ℕ) (A : Fin (2*r+1) → DecGraph)
    (c : ℝ) (hc : 0 < c) (s : ℝ) :
    (DecGraph.scaleOrderIso c hc (latticeMedianInfSup r A)).J s =
      scalarMedian r (fun i => (DecGraph.scaleOrderIso c hc (A i)).J s) := by
  rw [orderIso_latticeMedian, DecGraph.J_latticeMedianInfSup]
  rfl

theorem inc_lattice_median_majority (r : ℕ) (A : Fin (2*r+1) → IncGraph) {l h : IncGraph}
    (hm : ∃ I : Majority r, ∀ i ∈ I.val, l ≤ A i ∧ A i ≤ h) :
    l ≤ latticeMedianInfSup r A ∧ latticeMedianInfSup r A ≤ h :=
  latticeMedian_majority_bounds r A (inc_lattice_median r A) hm

theorem dec_lattice_median_majority (r : ℕ) (A : Fin (2*r+1) → DecGraph) {l h : DecGraph}
    (hm : ∃ I : Majority r, ∀ i ∈ I.val, l ≤ A i ∧ A i ≤ h) :
    l ≤ latticeMedianInfSup r A ∧ latticeMedianInfSup r A ≤ h :=
  latticeMedian_majority_bounds r A (dec_lattice_median r A) hm

end ScalarMonotone
