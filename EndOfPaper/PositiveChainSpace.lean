import EndOfPaper.WeightedChainMetric
import EndOfPaper.PositiveProductChain
import Mathlib.Order.Basic

/-!
A fresh point type and literal metric for positive-or-zero
coordinate chains. Coordinate order and metric hypotheses are
derived; no Euclidean topology is inherited. The full lower
random model and its measurability remain separate obligations.
-/

open Set
open scoped BigOperators
noncomputable section
namespace ScalarMonotone.EndOfPaper

structure PositiveProductPoint {ι : Type*} (C : Set (ι → ℝ)) where
  coords : ι → ℝ
  coords_mem : coords ∈ C

theorem positiveProductPoint_ext {ι : Type*} {C : Set (ι → ℝ)}
    {x y : PositiveProductPoint C} (h : x.coords = y.coords) : x = y := by
  cases x
  cases y
  cases h
  rfl

theorem positiveProductPoint_product_injective {ι : Type*} [Fintype ι] {C : Set (ι → ℝ)}
    (h0 : ∀ x ∈ C, ∀ i, 0 ≤ x i) (hp : ∀ x ∈ C, x = 0 ∨ ∀ i, 0 < x i)
    (hc : ∀ x ∈ C, ∀ y ∈ C, x ≤ y ∨ y ≤ x) :
    Function.Injective (fun x : PositiveProductPoint C => ∏ i, x.coords i) := by
  intro x y h
  apply positiveProductPoint_ext
  exact (product_injective_on_positive_or_zero_chain h0 hp hc) x.coords_mem y.coords_mem h

def positiveProductPointLinearOrder {ι : Type*} [Fintype ι] {C : Set (ι → ℝ)}
    (h0 : ∀ x ∈ C, ∀ i, 0 ≤ x i) (hp : ∀ x ∈ C, x = 0 ∨ ∀ i, 0 < x i)
    (hc : ∀ x ∈ C, ∀ y ∈ C, x ≤ y ∨ y ≤ x) : LinearOrder (PositiveProductPoint C) :=
  LinearOrder.lift' (fun x : PositiveProductPoint C => ∏ i, x.coords i)
    (positiveProductPoint_product_injective h0 hp hc)

theorem positiveProductPoint_coordinate_monotone {ι : Type*} [Fintype ι] {C : Set (ι → ℝ)}
    (h0 : ∀ x ∈ C, ∀ i, 0 ≤ x i) (hp : ∀ x ∈ C, x = 0 ∨ ∀ i, 0 < x i)
    (hc : ∀ x ∈ C, ∀ y ∈ C, x ≤ y ∨ y ≤ x) (i : ι) :
    letI := positiveProductPointLinearOrder h0 hp hc
    Monotone (fun x : PositiveProductPoint C => x.coords i) := by
  letI := positiveProductPointLinearOrder h0 hp hc
  intro x y hxy
  change (∏ j, x.coords j) ≤ ∏ j, y.coords j at hxy
  rcases hc x.coords x.coords_mem y.coords y.coords_mem with hcoords | hcoords
  · exact hcoords i
  · have hprod : (∏ j, y.coords j) ≤ ∏ j, x.coords j :=
      Finset.prod_le_prod (fun j _ => h0 y.coords y.coords_mem j) (fun j _ => hcoords j)
    have he : x.coords = y.coords :=
      (product_injective_on_positive_or_zero_chain h0 hp hc) x.coords_mem y.coords_mem (le_antisymm hxy hprod)
    exact (congrFun he i).le

def positiveChainMetric {n : ℕ} {C : Set (Option (Fin n) → ℝ)}
    (h0 : ∀ x ∈ C, ∀ i, 0 ≤ x i) (hp : ∀ x ∈ C, x = 0 ∨ ∀ i, 0 < x i)
    (hc : ∀ x ∈ C, ∀ y ∈ C, x ≤ y ∨ y ≤ x) : MetricSpace (PositiveProductPoint C) := by
  classical
  letI := positiveProductPointLinearOrder h0 hp hc
  let A := fun x : PositiveProductPoint C => x.coords none
  let P := fun x : PositiveProductPoint C => ∏ i : Fin n, x.coords (some i)
  have hcoord (i : Option (Fin n)) : Monotone (fun x : PositiveProductPoint C => x.coords i) :=
    positiveProductPoint_coordinate_monotone h0 hp hc i
  have hA : Monotone A := hcoord none
  have hP : Monotone P := by
    intro x y hxy
    change (∏ i : Fin n, x.coords (some i)) ≤ ∏ i : Fin n, y.coords (some i)
    exact Finset.prod_le_prod (fun i _ => h0 x.coords x.coords_mem (some i))
      (fun i _ => hcoord (some i) hxy)
  have hA0 (x : PositiveProductPoint C) : 0 ≤ A x := h0 x.coords x.coords_mem none
  have hP0 (x : PositiveProductPoint C) : 0 ≤ P x :=
    Finset.prod_nonneg (fun i _ => h0 x.coords x.coords_mem (some i))
  have hinj : Function.Injective (fun x => A x*P x) := by
    intro x y he
    apply positiveProductPoint_product_injective h0 hp hc
    simpa only [A,P,Fintype.prod_option] using he
  exact weightedChainMetric A P hA hP hA0 hP0 hinj

theorem positiveChainMetric_distance {n : ℕ} {C : Set (Option (Fin n) → ℝ)}
    (h0 : ∀ x ∈ C, ∀ i, 0 ≤ x i) (hp : ∀ x ∈ C, x = 0 ∨ ∀ i, 0 < x i)
    (hc : ∀ x ∈ C, ∀ y ∈ C, x ≤ y ∨ y ≤ x) (x y : PositiveProductPoint C) :
    letI := positiveChainMetric h0 hp hc
    dist x y = |(∏ j, x.coords j)-(∏ j, y.coords j)| /
      (∏ i : Fin n, max (x.coords (some i)) (y.coords (some i))) := by
  classical
  letI := positiveChainMetric h0 hp hc
  have hcomp : (fun i : Fin n => x.coords (some i)) ≤ (fun i => y.coords (some i)) ∨
      (fun i : Fin n => y.coords (some i)) ≤ (fun i => x.coords (some i)) := by
    rcases hc x.coords x.coords_mem y.coords y.coords_mem with h | h
    · exact Or.inl (fun i => h (some i))
    · exact Or.inr (fun i => h (some i))
  have hmax : (∏ i : Fin n, max (x.coords (some i)) (y.coords (some i))) =
      max (∏ i : Fin n, x.coords (some i)) (∏ i : Fin n, y.coords (some i)) := product_max_of_comparable
    (fun i : Fin n => h0 x.coords x.coords_mem (some i))
    (fun i : Fin n => h0 y.coords y.coords_mem (some i)) hcomp
  change |x.coords none*(∏ i, x.coords (some i))-y.coords none*(∏ i, y.coords (some i))| /
    max (∏ i, x.coords (some i)) (∏ i, y.coords (some i)) = _
  rw [hmax]
  simp only [Fintype.prod_option]

end ScalarMonotone.EndOfPaper
end
