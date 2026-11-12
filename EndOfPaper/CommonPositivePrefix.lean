import EndOfPaper.GeometricHardyOrder
import Mathlib.Data.Finset.Max

/-!
Construct a common positive point for a finite family
of nonzero nonnegative decreasing profiles, using arbitrary
selections and retaining jump fibers.
-/

open Set Filter MeasureTheory
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem finite_antitone_common_positive_point {ι : Type*} [Fintype ι]
    {s : ι → ℝ → ℝ} {B : ℝ} (hB : 0 < B)
    (hanti : ∀ i, AntitoneOn (s i) (Ioo (0 : ℝ) B))
    (hpos : ∀ i, ∃ a ∈ Ioo (0 : ℝ) B, 0 < s i a) :
    ∃ b ∈ Ioo (0 : ℝ) B, ∀ i, 0 < s i b := by
  classical
  choose a hai hpa using hpos
  let A : Finset ℝ := insert B (Finset.univ.image a)
  have hA : A.Nonempty := Finset.insert_nonempty _ _
  have hm0 : 0 < A.min' hA := by
    apply (Finset.lt_min'_iff A hA).mpr
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hB
    · obtain ⟨i,_hi,rfl⟩ := Finset.mem_image.mp hy
      exact (hai i).1
  have hmB : A.min' hA ≤ B := Finset.min'_le A B (Finset.mem_insert_self _ _)
  let b := A.min' hA/2
  have hb : b ∈ Ioo (0 : ℝ) B := ⟨by dsimp [b]; linarith,by dsimp [b]; linarith⟩
  refine ⟨b,hb,?_⟩
  intro i
  have hmai : A.min' hA ≤ a i := Finset.min'_le A (a i)
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))
  exact (hpa i).trans_le (hanti i hb (hai i) (by dsimp [b]; linarith))

theorem nonzero_profiles_common_positive_point {ι : Type*} [Fintype ι]
    {q : ι → Operator} {s : ι → ℝ → ℝ} {B : ℝ} (hB : 0 < B)
    (hq : ∀ i, MaximalDecreasing (q i))
    (hq0 : ∀ i x, x ∈ Ioo (0 : ℝ) B → ∀ v ∈ q i x, 0 ≤ v)
    (hn : ∀ i, ¬ ∀ x ∈ Ioo (0 : ℝ) B, ∀ v ∈ q i x, v = 0)
    (hs : ∀ i, SelectionOn (q i) (Ioo (0 : ℝ) B) (s i)) :
    ∃ b ∈ Ioo (0 : ℝ) B, ∀ i, 0 < s i b := by
  apply finite_antitone_common_positive_point hB
    (fun i => selection_antitoneOn (hq i).1 (hs i))
  intro i
  obtain ⟨a,ha,v,hv,hv0⟩ := positive_graph_value_of_nonzero (hq0 i) (hn i)
  have ha2 : a/2 ∈ Ioo (0 : ℝ) B := ⟨by linarith [ha.1],by linarith [ha.1,ha.2]⟩
  refine ⟨a/2,ha2,?_⟩
  exact hv0.trans_le (Decreasing.le_of_lt (hq i).1 (hs i (a/2) ha2) hv (by linarith [ha.1]))

end ScalarMonotone.EndOfPaper
end
