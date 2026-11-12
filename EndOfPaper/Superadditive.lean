import Mathlib

/-!
# The finite-decomposition superadditive transformation

Source: equation `superadditivetransform` and its elementary properties.
Finite families are represented by lists. Empty lists are allowed internally;
`sharpValues_nonempty_family` proves that this does not change the definition
when F(0)=0. No continuity hypothesis is needed for these algebraic properties.

Current compilation and audit evidence is recorded in docs/CODEX_PROGRESS.md.
-/

open Set
noncomputable section
namespace ScalarMonotone.EndOfPaper

abbrev CoordinateVector (n : ℕ) := Fin n → ℝ

def coordinateMass {n : ℕ} (x : CoordinateVector n) : ℝ := ∑ i, x i

/-- The algebraic assumptions of the manuscript, with nonnegativity of the
codomain stated explicitly rather than encoded in a subtype. -/
structure AggregationAxioms {n : ℕ} (F : CoordinateVector n → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ x → 0 ≤ F x
  mono : ∀ {x y}, 0 ≤ x → x ≤ y → F x ≤ F y
  homogeneous : ∀ (c : ℝ), 0 ≤ c → ∀ x, 0 ≤ x → F (c • x) = c * F x

def AdmissibleDecomposition {n : ℕ} (a : CoordinateVector n)
    (v : List (CoordinateVector n)) : Prop :=
  (∀ x ∈ v, 0 ≤ x) ∧ v.sum ≤ a

def sharpValues {n : ℕ} (F : CoordinateVector n → ℝ)
    (a : CoordinateVector n) : Set ℝ :=
  {z | ∃ v : List (CoordinateVector n), AdmissibleDecomposition a v ∧
    z = (v.map F).sum}

/-- This is used only on the nonnegative cone; boundedness is proved below. -/
def superadditiveTransform {n : ℕ} (F : CoordinateVector n → ℝ)
    (a : CoordinateVector n) : ℝ := sSup (sharpValues F a)

@[simp] theorem coordinateMass_zero (n : ℕ) :
    coordinateMass (0 : CoordinateVector n) = 0 := by simp [coordinateMass]

@[simp] theorem coordinateMass_add {n : ℕ} (x y : CoordinateVector n) :
    coordinateMass (x+y) = coordinateMass x + coordinateMass y := by
  simp [coordinateMass, Finset.sum_add_distrib]

@[simp] theorem coordinateMass_smul {n : ℕ} (c : ℝ) (x : CoordinateVector n) :
    coordinateMass (c • x) = c * coordinateMass x := by
  simp [coordinateMass, Finset.mul_sum]

theorem coordinateMass_nonneg {n : ℕ} {x : CoordinateVector n} (hx : 0 ≤ x) :
    0 ≤ coordinateMass x := Finset.sum_nonneg fun i _ => hx i

theorem coordinateMass_mono {n : ℕ} {x y : CoordinateVector n} (h : x ≤ y) :
    coordinateMass x ≤ coordinateMass y := Finset.sum_le_sum fun i _ => h i

theorem coordinate_le_mass {n : ℕ} {x : CoordinateVector n} (hx : 0 ≤ x) (i : Fin n) :
    x i ≤ coordinateMass x :=
  Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)

theorem vectorList_sum_nonneg {n : ℕ} (v : List (CoordinateVector n))
    (hv : ∀ x ∈ v, 0 ≤ x) : 0 ≤ v.sum := by
  revert hv
  induction v with
  | nil => intro hv; simp
  | cons x v ih =>
    intro hv
    have hx : 0 ≤ x := hv x (by simp)
    have hv' : ∀ y ∈ v, 0 ≤ y := fun y hy => hv y (by simp [hy])
    simpa only [List.sum_cons] using add_nonneg hx (ih hv')

@[simp] theorem coordinateMass_list_sum {n : ℕ} (v : List (CoordinateVector n)) :
    coordinateMass v.sum = (v.map coordinateMass).sum := by
  induction v with
  | nil => simp
  | cons x v ih => simp [ih]

@[simp] theorem vectorList_sum_smul {n : ℕ} (v : List (CoordinateVector n)) (c : ℝ) :
    (v.map (fun x => c • x)).sum = c • v.sum := by
  induction v with
  | nil => simp
  | cons x v ih => simp [ih, smul_add]

theorem aggregation_zero {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) : F 0 = 0 := by
  simpa using hF.homogeneous 0 le_rfl 0 le_rfl

theorem aggregation_linear_bound {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) {x : CoordinateVector n} (hx : 0 ≤ x) :
    F x ≤ F (fun _ => 1) * coordinateMass x := by
  have he : x ≤ coordinateMass x • (fun _ : Fin n => (1 : ℝ)) := by
    intro i
    simpa using coordinate_le_mass hx i
  calc
    F x ≤ F (coordinateMass x • (fun _ : Fin n => (1 : ℝ))) := hF.mono hx he
    _ = coordinateMass x * F (fun _ => 1) :=
      hF.homogeneous _ (coordinateMass_nonneg hx) _ (fun _ => zero_le_one)
    _ = _ := mul_comm _ _

theorem decomposition_linear_bound {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (v : List (CoordinateVector n))
    (hv : ∀ x ∈ v, 0 ≤ x) :
    (v.map F).sum ≤ F (fun _ => 1) * coordinateMass v.sum := by
  revert hv
  induction v with
  | nil => intro hv; simp
  | cons x v ih =>
    intro hv
    have hx := hv x (by simp)
    have hv' : ∀ y ∈ v, 0 ≤ y := fun y hy => hv y (by simp [hy])
    have h₁ := aggregation_linear_bound hF hx
    have h₂ := ih hv'
    simp only [List.map_cons, List.sum_cons, coordinateMass_add]
    nlinarith

/-- Appending a zero vector enforces the manuscript's m >= 1 convention. -/
theorem sharpValues_nonempty_family {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (a : CoordinateVector n) (z : ℝ) :
    z ∈ sharpValues F a ↔ ∃ v : List (CoordinateVector n), v ≠ [] ∧
      AdmissibleDecomposition a v ∧ z = (v.map F).sum := by
  constructor
  · rintro ⟨v, hv, he⟩
    refine ⟨v ++ [0], by simp, ⟨?_, ?_⟩, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hv.1 x hx
      · have hzero : x = 0 := by simpa using hx
        simp [hzero]
    · simpa using hv.2
    · simpa [aggregation_zero hF] using he
  · rintro ⟨v, _, hv, he⟩
    exact ⟨v, hv, he⟩

theorem sharpValues_nonempty {n : ℕ} (F : CoordinateVector n → ℝ)
    {a : CoordinateVector n} (ha : 0 ≤ a) : (sharpValues F a).Nonempty := by
  refine ⟨0, [], ⟨by simp, ?_⟩, by simp⟩
  simpa using ha

theorem sharpValues_bddAbove {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (a : CoordinateVector n) :
    BddAbove (sharpValues F a) := by
  refine ⟨F (fun _ => 1) * coordinateMass a, ?_⟩
  rintro z ⟨v, hv, rfl⟩
  exact (decomposition_linear_bound hF v hv.1).trans
    (mul_le_mul_of_nonneg_left (coordinateMass_mono hv.2)
      (hF.nonneg _ (fun _ => zero_le_one)))

theorem le_superadditiveTransform {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) {a : CoordinateVector n} (ha : 0 ≤ a) :
    F a ≤ superadditiveTransform F a := by
  apply le_csSup (sharpValues_bddAbove hF a)
  exact ⟨[a], ⟨by simpa, by simp⟩, by simp⟩

theorem superadditiveTransform_nonneg {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) {a : CoordinateVector n} (ha : 0 ≤ a) :
    0 ≤ superadditiveTransform F a :=
  (hF.nonneg _ ha).trans (le_superadditiveTransform hF ha)

theorem superadditiveTransform_linear_bound {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) {a : CoordinateVector n} (ha : 0 ≤ a) :
    superadditiveTransform F a ≤ F (fun _ => 1) * coordinateMass a := by
  apply csSup_le (sharpValues_nonempty F ha)
  rintro z ⟨v, hv, rfl⟩
  exact (decomposition_linear_bound hF v hv.1).trans
    (mul_le_mul_of_nonneg_left (coordinateMass_mono hv.2)
      (hF.nonneg _ (fun _ => zero_le_one)))

@[simp] theorem superadditiveTransform_zero {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) : superadditiveTransform F 0 = 0 := by
  apply le_antisymm
  · simpa using superadditiveTransform_linear_bound hF (a := 0) le_rfl
  · exact superadditiveTransform_nonneg hF le_rfl

theorem superadditiveTransform_mono {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) {a b : CoordinateVector n}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    superadditiveTransform F a ≤ superadditiveTransform F b := by
  apply csSup_le_csSup (sharpValues_bddAbove hF b) (sharpValues_nonempty F ha)
  rintro z ⟨v, hv, he⟩
  exact ⟨v, ⟨hv.1, hv.2.trans hab⟩, he⟩

theorem sharpValues_add {n : ℕ} {F : CoordinateVector n → ℝ}
    {a b : CoordinateVector n} {u v : ℝ}
    (hu : u ∈ sharpValues F a) (hv : v ∈ sharpValues F b) :
    u+v ∈ sharpValues F (a+b) := by
  obtain ⟨xs, hxs, rfl⟩ := hu
  obtain ⟨ys, hys, rfl⟩ := hv
  refine ⟨xs ++ ys, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hxs.1 x hx
    · exact hys.1 x hx
  · simpa using add_le_add hxs.2 hys.2
  · simp

theorem superadditiveTransform_superadditive {n : ℕ}
    {F : CoordinateVector n → ℝ} (hF : AggregationAxioms F)
    {a b : CoordinateVector n} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    superadditiveTransform F a + superadditiveTransform F b ≤
      superadditiveTransform F (a+b) := by
  have h : superadditiveTransform F a ≤
      superadditiveTransform F (a+b)-superadditiveTransform F b := by
    apply csSup_le (sharpValues_nonempty F ha)
    intro u hu
    have hh : superadditiveTransform F b ≤ superadditiveTransform F (a+b)-u := by
      apply csSup_le (sharpValues_nonempty F hb)
      intro v hv
      have hle := le_csSup (sharpValues_bddAbove hF (a+b)) (sharpValues_add hu hv)
      change u+v ≤ superadditiveTransform F (a+b) at hle
      linarith
    linarith
  linarith

/-- Sum evaluation commutes with positive scaling of a decomposition. -/
theorem aggregation_list_smul {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (v : List (CoordinateVector n)) (c : ℝ)
    (hc : 0 ≤ c) (hv : ∀ x ∈ v, 0 ≤ x) :
    ((v.map (fun x => c • x)).map F).sum = c * (v.map F).sum := by
  revert hv
  induction v with
  | nil => intro hv; simp
  | cons x v ih =>
    intro hv
    have hx := hv x (by simp)
    have hv' : ∀ y ∈ v, 0 ≤ y := fun y hy => hv y (by simp [hy])
    simp only [List.map_cons, List.sum_cons, hF.homogeneous c hc x hx, ih hv', mul_add]

/-- One direction of scaling, using the inverse-scaled decomposition. -/
theorem superadditiveTransform_smul_le {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) {a : CoordinateVector n} (ha : 0 ≤ a)
    {c : ℝ} (hc : 0 < c) :
    superadditiveTransform F (c • a) ≤ c * superadditiveTransform F a := by
  have hca : 0 ≤ c • a := fun i => mul_nonneg hc.le (ha i)
  apply csSup_le (sharpValues_nonempty F hca)
  rintro z ⟨v, hv, rfl⟩
  let w := v.map (fun x => c⁻¹ • x)
  have hw : AdmissibleDecomposition a w := by
    constructor
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact fun i => mul_nonneg (inv_nonneg.mpr hc.le) (hv.1 y hy i)
    · change (v.map (fun x => c⁻¹ • x)).sum ≤ a
      rw [vectorList_sum_smul]
      intro i
      have hi := mul_le_mul_of_nonneg_left (hv.2 i) (inv_nonneg.mpr hc.le)
      simpa [mul_assoc, hc.ne'] using hi
  have hle := le_csSup (sharpValues_bddAbove hF a)
    (show (w.map F).sum ∈ sharpValues F a from ⟨w, hw, rfl⟩)
  have he : (w.map F).sum = c⁻¹ * (v.map F).sum :=
    aggregation_list_smul hF v c⁻¹ (inv_nonneg.mpr hc.le) hv.1
  rw [he] at hle
  have hh := mul_le_mul_of_nonneg_left hle hc.le
  simpa [mul_assoc, hc.ne'] using hh

theorem superadditiveTransform_smul {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) {a : CoordinateVector n} (ha : 0 ≤ a)
    {c : ℝ} (hc : 0 ≤ c) :
    superadditiveTransform F (c • a) = c * superadditiveTransform F a := by
  rcases hc.eq_or_lt with hzero | hpos
  · simp [← hzero, superadditiveTransform_zero hF]
  · apply le_antisymm (superadditiveTransform_smul_le hF ha hpos)
    have hca : 0 ≤ c • a := fun i => mul_nonneg hc (ha i)
    have h := superadditiveTransform_smul_le hF hca (inv_pos.mpr hpos)
    have h' : superadditiveTransform F a ≤ c⁻¹ * superadditiveTransform F (c • a) := by
      simpa [smul_smul, hpos.ne'] using h
    have hh := mul_le_mul_of_nonneg_left h' hc
    simpa [mul_assoc, hpos.ne'] using hh

/-- No regularity hypothesis on a competing superadditive majorant is needed. -/
theorem superadditiveTransform_le_majorant {n : ℕ} {F G : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F)
    (hFG : ∀ x, 0 ≤ x → F x ≤ G x)
    (hG : ∀ x y, 0 ≤ x → 0 ≤ y → G x+G y ≤ G (x+y))
    {a : CoordinateVector n} (ha : 0 ≤ a) :
    superadditiveTransform F a ≤ G a := by
  have hG0 : ∀ x, 0 ≤ x → 0 ≤ G x := fun x hx => (hF.nonneg x hx).trans (hFG x hx)
  have hlist : ∀ v : List (CoordinateVector n), (∀ x ∈ v, 0 ≤ x) →
      (v.map F).sum ≤ G v.sum := by
    intro v
    induction v with
    | nil => intro hv; simpa using hG0 0 le_rfl
    | cons x v ih =>
      intro hv
      have hx := hv x (by simp)
      have hv' : ∀ y ∈ v, 0 ≤ y := fun y hy => hv y (by simp [hy])
      simpa only [List.map_cons, List.sum_cons] using
        (add_le_add (hFG x hx) (ih hv')).trans (hG x v.sum hx (vectorList_sum_nonneg v hv'))
  apply csSup_le (sharpValues_nonempty F ha)
  rintro z ⟨v, hv, rfl⟩
  have hs := vectorList_sum_nonneg v hv.1
  have hd : 0 ≤ a-v.sum := sub_nonneg.mpr hv.2
  have hg := hG v.sum (a-v.sum) hs hd
  have he : v.sum+(a-v.sum) = a := by abel
  rw [he] at hg
  have hnon := hG0 (a-v.sum) hd
  have hl := hlist v hv.1
  linarith

/-- In particular, an already-superadditive aggregation is unchanged. -/
theorem superadditiveTransform_eq_self {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F)
    (hadd : ∀ x y, 0 ≤ x → 0 ≤ y → F x+F y ≤ F (x+y))
    {a : CoordinateVector n} (ha : 0 ≤ a) :
    superadditiveTransform F a = F a :=
  le_antisymm (superadditiveTransform_le_majorant hF (fun _ _ => le_rfl) hadd ha)
    (le_superadditiveTransform hF ha)

/-- Positive homogeneity and superadditivity give concavity on the cone. -/
theorem superadditiveTransform_concaveOn {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) :
    ConcaveOn ℝ {a : CoordinateVector n | 0 ≤ a} (superadditiveTransform F) := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab i
    exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
  · intro x hx y hy a b ha hb hab
    have hax : 0 ≤ a • x := fun i => mul_nonneg ha (hx i)
    have hby : 0 ≤ b • y := fun i => mul_nonneg hb (hy i)
    have h := superadditiveTransform_superadditive hF hax hby
    rw [superadditiveTransform_smul hF hx ha,
      superadditiveTransform_smul hF hy hb] at h
    simpa only [smul_eq_mul] using h

/-- Algebraic finite-step version of the aggregation-area bound. -/
theorem aggregation_step_bound {n : ℕ} {F : CoordinateVector n → ℝ}
    (hF : AggregationAxioms F) (v : List (CoordinateVector n))
    (hv : ∀ x ∈ v, 0 ≤ x) :
    (v.map F).sum ≤ superadditiveTransform F v.sum := by
  exact le_csSup (sharpValues_bddAbove hF _)
    ⟨v, ⟨hv, le_rfl⟩, rfl⟩


/-- The same decomposition bound indexed by a finite set. -/
theorem aggregation_finset_bound {n : ℕ} {ι : Type*} [DecidableEq ι]
    {F : CoordinateVector n → ℝ} (hF : AggregationAxioms F)
    (s : Finset ι) (v : ι → CoordinateVector n) (hv : ∀ i ∈ s, 0 ≤ v i) :
    (∑ i ∈ s, F (v i)) ≤ superadditiveTransform F (∑ i ∈ s, v i) := by
  revert hv
  induction s using Finset.induction_on with
  | empty => intro hv; simp [superadditiveTransform_zero hF]
  | @insert i s hi ih =>
    intro hv
    have hvi : 0 ≤ v i := hv i (Finset.mem_insert_self i s)
    have hvs : ∀ j ∈ s, 0 ≤ v j := fun j hj => hv j (Finset.mem_insert_of_mem hj)
    have hsum : 0 ≤ ∑ j ∈ s, v j := Finset.sum_nonneg hvs
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (add_le_add (le_superadditiveTransform hF hvi) (ih hvs)).trans
      (superadditiveTransform_superadditive hF hvi hsum)

/-- An axis vector written without depending on a normed-space convention. -/
def coordinateAxis {n : ℕ} (i : Fin n) (t : ℝ) : CoordinateVector n :=
  fun j => if j = i then t else 0

theorem coordinateAxis_nonneg {n : ℕ} (i : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ coordinateAxis i t := by
  intro j
  by_cases h : j = i <;> simp [coordinateAxis, h, ht]

@[simp] theorem sum_coordinateAxis {n : ℕ} (a : CoordinateVector n) :
    (∑ i, coordinateAxis i (a i)) = a := by
  funext j
  simp [Finset.sum_apply, coordinateAxis]

/-- The algebraic core of the l^q example: every aggregation bounded by l^1
and agreeing with l^1 on coordinate axes has l^1 as its transformation.
Instantiation with particular norm implementations is a separate obligation. -/
theorem superadditiveTransform_eq_mass_of_axes {n : ℕ}
    {F : CoordinateVector n → ℝ} (hF : AggregationAxioms F)
    (hbound : ∀ x, 0 ≤ x → F x ≤ coordinateMass x)
    (haxis : ∀ (i : Fin n) (t : ℝ), 0 ≤ t → F (coordinateAxis i t) = t)
    {a : CoordinateVector n} (ha : 0 ≤ a) :
    superadditiveTransform F a = coordinateMass a := by
  apply le_antisymm
  · exact superadditiveTransform_le_majorant hF hbound
      (fun x y _ _ => by simp) ha
  · have h := aggregation_finset_bound hF Finset.univ
      (fun i => coordinateAxis i (a i)) (fun i _ => coordinateAxis_nonneg i (ha i))
    simp only [sum_coordinateAxis] at h
    have he : (∑ i, F (coordinateAxis i (a i))) = coordinateMass a := by
      apply Finset.sum_congr rfl
      intro i _
      exact haxis i (a i) (ha i)
    rw [he] at h
    exact h

/-- The zero aggregation is an actual degeneracy in a formula that divides
by F-sharp(1): it cannot be handled by silently assuming a positive scale. -/
theorem aggregation_eq_zero_of_one_eq_zero {n : ℕ}
    {F : CoordinateVector n → ℝ} (hF : AggregationAxioms F)
    (hzero : F (fun _ => 1) = 0) {a : CoordinateVector n} (ha : 0 ≤ a) :
    F a = 0 := by
  have h := aggregation_linear_bound hF ha
  rw [hzero, zero_mul] at h
  exact le_antisymm h (hF.nonneg a ha)


/-- On the cone, concavity plus positive homogeneity implies superadditivity. -/
theorem homogeneous_concave_superadditive {n : ℕ}
    {G : CoordinateVector n → ℝ}
    (hG : ConcaveOn ℝ {x : CoordinateVector n | 0 ≤ x} G)
    (hh : ∀ (c : ℝ), 0 ≤ c → ∀ x, 0 ≤ x → G (c • x) = c*G x)
    (x y : CoordinateVector n) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    G x+G y ≤ G (x+y) := by
  have h := hG.2 hx hy (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)+1/2 = 1)
  have he : (1/2 : ℝ) • x + (1/2 : ℝ) • y = (1/2 : ℝ) • (x+y) := by
    rw [smul_add]
  rw [he, hh (1/2) (by norm_num) (x+y) (add_nonneg hx hy)] at h
  simp only [smul_eq_mul] at h
  linarith

/-- The least positively homogeneous concave majorant property. -/
theorem superadditiveTransform_le_concave_majorant {n : ℕ}
    {F G : CoordinateVector n → ℝ} (hF : AggregationAxioms F)
    (hFG : ∀ x, 0 ≤ x → F x ≤ G x)
    (hG : ConcaveOn ℝ {x : CoordinateVector n | 0 ≤ x} G)
    (hh : ∀ (c : ℝ), 0 ≤ c → ∀ x, 0 ≤ x → G (c • x) = c*G x)
    {a : CoordinateVector n} (ha : 0 ≤ a) :
    superadditiveTransform F a ≤ G a :=
  superadditiveTransform_le_majorant hF hFG
    (homogeneous_concave_superadditive hG hh) ha

end ScalarMonotone.EndOfPaper

end -- noncomputable section
