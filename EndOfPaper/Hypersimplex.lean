import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic

/-!
Exact hypersimplex extreme points, binary convex hull and finite decomposition.
This supplies an ingredient of Proposition prop:mediantransform; the final
median-transform assembly is separate.
-/

open Set
open scoped BigOperators

noncomputable section
namespace ScalarMonotone.EndOfPaper

def hypersimplex (n k : ℕ) : Set (Fin n → ℝ) :=
  Icc 0 1 ∩ {x | ∑ i, x i = (k : ℝ)}

def hypersimplexVertices (n k : ℕ) : Set (Fin n → ℝ) :=
  {x | x ∈ hypersimplex n k ∧ ∀ i, x i = 0 ∨ x i = 1}

theorem hypersimplex_convex (n k : ℕ) : Convex ℝ (hypersimplex n k) := by
  apply (convex_Icc 0 1).inter
  intro x hx y hy a b ha hb hab
  change ∑ i, (a * x i + b * y i) = (k : ℝ)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx, hy,
    ← add_mul, hab, one_mul]

theorem hypersimplex_compact (n k : ℕ) : IsCompact (hypersimplex n k) := by
  apply isCompact_Icc.inter_right
  exact isClosed_eq (continuous_finset_sum _ (fun i _ => continuous_apply i)) continuous_const

theorem hypersimplexVertices_finite (n k : ℕ) : (hypersimplexVertices n k).Finite := by
  classical
  apply (finite_range (fun b : Fin n → Bool => fun i => if b i then (1 : ℝ) else 0)).subset
  intro x hx
  refine ⟨fun i => decide (x i = 1), ?_⟩
  funext i
  rcases hx.2 i with hi | hi <;> simp [hi]

theorem hypersimplex_second_fractional {n k : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ hypersimplex n k) {i : Fin n} (hi : 0 < x i ∧ x i < 1) :
    ∃ j, j ≠ i ∧ 0 < x j ∧ x j < 1 := by
  classical
  by_contra hn
  have hbinary : ∀ j ∈ Finset.univ.erase i, x j = 0 ∨ x j = 1 := by
    intro j hj
    by_cases h0 : x j = 0
    · exact Or.inl h0
    by_cases h1 : x j = 1
    · exact Or.inr h1
    exact False.elim (hn ⟨j, (Finset.mem_erase.mp hj).1,
      lt_of_le_of_ne (hx.1.1 j) (Ne.symm h0), lt_of_le_of_ne (hx.1.2 j) h1⟩)
  let S := (Finset.univ.erase i).filter (fun j => x j = 1)
  have hones : (∑ j ∈ Finset.univ.erase i, x j) = (S.card : ℝ) := by
    calc
      _ = ∑ j ∈ Finset.univ.erase i, if x j = 1 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rcases hbinary j hj with h | h <;> simp [h]
      _ = _ := by simp [S]
  have hsum := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n))) x
    (Finset.mem_univ i)
  rw [hones, hx.2] at hsum
  have hlo : S.card < k := by exact_mod_cast (show (S.card : ℝ) < (k : ℝ) by linarith [hi.1])
  have hhi : k < S.card + 1 := by
    exact_mod_cast (show (k : ℝ) < (S.card : ℝ) + 1 by linarith [hi.2])
  omega

theorem hypersimplex_extremePoints_subset_vertices (n k : ℕ) :
    (hypersimplex n k).extremePoints ℝ ⊆ hypersimplexVertices n k := by
  classical
  intro x hxe
  have hx := hxe.1
  refine ⟨hx, fun i => ?_⟩
  by_cases h0 : x i = 0
  · exact Or.inl h0
  by_cases h1 : x i = 1
  · exact Or.inr h1
  have hi : 0 < x i ∧ x i < 1 :=
    ⟨lt_of_le_of_ne (hx.1.1 i) (Ne.symm h0), lt_of_le_of_ne (hx.1.2 i) h1⟩
  obtain ⟨j, hji, hj⟩ := hypersimplex_second_fractional hx hi
  let δ := min (min (x i) (1-x i)) (min (x j) (1-x j))
  have hδ : 0 < δ := lt_min (lt_min hi.1 (sub_pos.mpr hi.2))
    (lt_min hj.1 (sub_pos.mpr hj.2))
  have hδi₀ : δ ≤ x i := (min_le_left _ _).trans (min_le_left _ _)
  have hδi₁ : δ ≤ 1-x i := (min_le_left _ _).trans (min_le_right _ _)
  have hδj₀ : δ ≤ x j := (min_le_right _ _).trans (min_le_left _ _)
  have hδj₁ : δ ≤ 1-x j := (min_le_right _ _).trans (min_le_right _ _)
  let y : Fin n → ℝ := x + Pi.single i δ - Pi.single j δ
  let z : Fin n → ℝ := x - Pi.single i δ + Pi.single j δ
  have hcoords (l : Fin n) : 0 ≤ y l ∧ y l ≤ 1 ∧ 0 ≤ z l ∧ z l ≤ 1 := by
    by_cases hli : l = i
    · subst l
      have hb : 0 ≤ x i+δ ∧ x i+δ ≤ 1 ∧ 0 ≤ x i-δ ∧ x i-δ ≤ 1 := by
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hx.1.1 i, hx.1.2 i]
      simpa [y, z, Pi.single_apply, hji, Ne.symm hji] using hb
    by_cases hlj : l = j
    · subst l
      have hb : 0 ≤ x j-δ ∧ x j-δ ≤ 1 ∧ 0 ≤ x j+δ ∧ x j+δ ≤ 1 := by
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hx.1.1 j, hx.1.2 j]
      simpa [y, z, Pi.single_apply, hji, Ne.symm hji] using hb
    simpa [y, z, Pi.single_apply, hli, Ne.symm hli, hlj, Ne.symm hlj] using
      (show 0 ≤ x l ∧ x l ≤ 1 ∧ 0 ≤ x l ∧ x l ≤ 1 from
        ⟨hx.1.1 l, hx.1.2 l, hx.1.1 l, hx.1.2 l⟩)
  have hsingle (l : Fin n) : (∑ m, (Pi.single l δ : Fin n → ℝ) m) = δ := by
    simp [Pi.single_apply]
  have hy : y ∈ hypersimplex n k := by
    refine ⟨⟨fun l => (hcoords l).1, fun l => (hcoords l).2.1⟩, ?_⟩
    change (∑ l, ((x l + (Pi.single i δ : Fin n → ℝ) l) - (Pi.single j δ : Fin n → ℝ) l)) = (k : ℝ)
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsingle, hsingle, hx.2]
    ring
  have hz : z ∈ hypersimplex n k := by
    refine ⟨⟨fun l => (hcoords l).2.2.1, fun l => (hcoords l).2.2.2⟩, ?_⟩
    change (∑ l, ((x l - (Pi.single i δ : Fin n → ℝ) l) + (Pi.single j δ : Fin n → ℝ) l)) = (k : ℝ)
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsingle, hsingle, hx.2]
    ring
  have hseg : x ∈ openSegment ℝ y z := by
    refine ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    ext l
    change (1/2 : ℝ) * (x l + (Pi.single i δ : Fin n → ℝ) l - (Pi.single j δ : Fin n → ℝ) l) +
      (1/2 : ℝ) * (x l - (Pi.single i δ : Fin n → ℝ) l + (Pi.single j δ : Fin n → ℝ) l) = x l
    ring
  have heq : y = x := (hxe.2 hy hz hseg).1
  have heqi := congrFun heq i
  have heqi' : x i+δ = x i := by
    simpa [y, Pi.single_apply, hji, Ne.symm hji] using heqi
  exact False.elim (by linarith)

/-- Every binary point of the integer cube-slice is extreme. -/
theorem hypersimplex_vertices_subset_extremePoints (n k : ℕ) :
    hypersimplexVertices n k ⊆ (hypersimplex n k).extremePoints ℝ := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro y hy z hz hseg
  obtain ⟨a, b, ha, hb, hab, he⟩ := hseg
  have hyz : ∀ i, y i = x i ∧ z i = x i := by
    intro i
    have hi := congrFun he i
    change a * y i + b * z i = x i at hi
    have hy₀ : 0 ≤ y i := hy.1.1 i
    have hy₁ : y i ≤ 1 := hy.1.2 i
    have hz₀ : 0 ≤ z i := hz.1.1 i
    have hz₁ : z i ≤ 1 := hz.1.2 i
    rcases hx.2 i with h | h
    · rw [h] at hi ⊢
      constructor <;> nlinarith [mul_nonneg ha.le hy₀, mul_nonneg hb.le hz₀]
    · rw [h] at hi ⊢
      have hya := mul_nonneg ha.le (sub_nonneg.mpr hy₁)
      have hzb := mul_nonneg hb.le (sub_nonneg.mpr hz₁)
      have hzero : a * (1-y i) + b * (1-z i) = 0 := by nlinarith
      have hya0 : a * (1-y i) = 0 := le_antisymm (by linarith) hya
      have hzb0 : b * (1-z i) = 0 := le_antisymm (by linarith) hzb
      have hyi := (mul_eq_zero.mp hya0).resolve_left ha.ne'
      have hzi := (mul_eq_zero.mp hzb0).resolve_left hb.ne'
      constructor <;> linarith
  exact ⟨funext (fun i => (hyz i).1), funext (fun i => (hyz i).2)⟩

theorem hypersimplex_extremePoints_eq_vertices (n k : ℕ) :
    (hypersimplex n k).extremePoints ℝ = hypersimplexVertices n k :=
  subset_antisymm (hypersimplex_extremePoints_subset_vertices n k)
    (hypersimplex_vertices_subset_extremePoints n k)

/-- Integer-coordinate slice of the cube is the convex hull of its binary vertices. -/
theorem hypersimplex_eq_convexHull_vertices (n k : ℕ) :
    hypersimplex n k = convexHull ℝ (hypersimplexVertices n k) := by
  have hc := hypersimplex_convex n k
  have hcompact := hypersimplex_compact n k
  have hclosed := (hypersimplexVertices_finite n k).isCompact_convexHull.isClosed
  apply subset_antisymm
  · rw [← closure_convexHull_extremePoints hcompact hc]
    exact closure_minimal (convexHull_mono (hypersimplex_extremePoints_subset_vertices n k)) hclosed
  · exact convexHull_min (fun _ hx => hx.1) hc

/-- The manuscript-facing zero-one convex-hull identity, with no vertex choices hidden. -/
theorem hypersimplex_eq_convexHull_binary (n k : ℕ) :
    {x : Fin n → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i = (k : ℝ)} =
      convexHull ℝ {x : Fin n → ℝ | (∀ i, x i = 0 ∨ x i = 1) ∧ ∑ i, x i = (k : ℝ)} := by
  have hH : {x : Fin n → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i = (k : ℝ)} =
      hypersimplex n k := by
    ext x
    simp [hypersimplex, Pi.le_def, forall_and]
  have hV : {x : Fin n → ℝ | (∀ i, x i = 0 ∨ x i = 1) ∧ ∑ i, x i = (k : ℝ)} =
      hypersimplexVertices n k := by
    ext x
    constructor
    · rintro ⟨hb, hs⟩
      refine ⟨⟨⟨?_, ?_⟩, hs⟩, hb⟩
      · intro i
        rcases hb i with h | h <;> simp [h]
      · intro i
        rcases hb i with h | h <;> simp [h]
    · rintro ⟨hx, hb⟩
      exact ⟨hb, hx.2⟩
  rw [hH, hV]
  exact hypersimplex_eq_convexHull_vertices n k

theorem hypersimplex_finite_decomposition {n k : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ hypersimplex n k) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (v : ι → Fin n → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      (∀ i j, v i j = 0 ∨ v i j = 1) ∧ (∀ i, ∑ j, v i j = (k : ℝ)) ∧
      ∑ i, w i • v i = x := by
  have hh : x ∈ convexHull ℝ (hypersimplexVertices n k) :=
    (hypersimplex_eq_convexHull_vertices n k).subset hx
  obtain ⟨ι, hι, w, v, hw, hws, hv, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hh
  letI := hι
  exact ⟨ι, hι, w, v, hw, hws, fun i => (hv i).2, fun i => (hv i).1.2, hsum⟩

end ScalarMonotone.EndOfPaper
end
