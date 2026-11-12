import Mathlib

/-!
# Scalar set-valued operators: definitions

All graph coordinates are real. `Increasing` refers to a relation, not to
mathlib's single-valued `Monotone`. Maximality includes monotonicity.
-/

open Set

namespace ScalarMonotone

abbrev Operator := ℝ → Set ℝ

def graph (f : Operator) : Set (ℝ × ℝ) := {p | p.2 ∈ f p.1}
def dom (f : Operator) : Set ℝ := {x | (f x).Nonempty}
def ran (f : Operator) : Set ℝ := {u | ∃ x, u ∈ f x}
def inverse (f : Operator) : Operator := fun u => {x | u ∈ f x}
def negOut (f : Operator) : Operator := fun x => {u | -u ∈ f x}
def reflect (f : Operator) : Operator := fun x => f (-x)
def ofFun (f : ℝ → ℝ) : Operator := fun x => {f x}
def identity : Operator := ofFun id

def Increasing (f : Operator) : Prop :=
  ∀ ⦃x u y v : ℝ⦄, u ∈ f x → v ∈ f y → 0 ≤ (x - y) * (u - v)

def Compatible (f : Operator) (x u : ℝ) : Prop :=
  ∀ ⦃y v : ℝ⦄, v ∈ f y → 0 ≤ (x - y) * (u - v)

def MaximalIncreasing (f : Operator) : Prop :=
  Increasing f ∧ ∀ ⦃x u : ℝ⦄, Compatible f x u → u ∈ f x

def Decreasing (f : Operator) : Prop := Increasing (negOut f)
def MaximalDecreasing (f : Operator) : Prop := MaximalIncreasing (negOut f)

def add (f g : Operator) : Operator := fun x =>
  {w | ∃ u ∈ f x, ∃ v ∈ g x, w = u + v}
def mul (f g : Operator) : Operator := fun x =>
  {w | ∃ u ∈ f x, ∃ v ∈ g x, w = u * v}
def comp (g f : Operator) : Operator := fun x =>
  {v | ∃ u ∈ f x, v ∈ g u}
def parallelAdd (f g : Operator) : Operator := inverse (add (inverse f) (inverse g))
def parallelMul (f g : Operator) : Operator := inverse (mul (inverse f) (inverse g))

def setAdd (A B : Set ℝ) : Set ℝ := {w | ∃ a ∈ A, ∃ b ∈ B, w = a + b}
def setMul (A B : Set ℝ) : Set ℝ := {w | ∃ a ∈ A, ∃ b ∈ B, w = a * b}

def Nonnegative (f : Operator) : Prop := ∀ ⦃x u⦄, u ∈ f x → 0 ≤ u
def SingleValued (f : Operator) : Prop := ∀ x, (f x).Subsingleton
def NoRectangle (f g : Operator) : Prop :=
  ∀ z, (inverse f z).Subsingleton ∨ (g z).Subsingleton

def logOp (f : Operator) : Operator := fun x =>
  {t | ∃ u ∈ f x, 0 < u ∧ Real.log u = t}

end ScalarMonotone
