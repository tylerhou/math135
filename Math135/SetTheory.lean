import Mathlib.Tactic

namespace SetTheory

class Signature where
  (Set : Type)
  ElementOf : Set -> Set -> Prop

infix:50 " ∈ " => Signature.ElementOf
@[simp] def NotElementOf [S : Signature] (x y : Signature.Set) :=
  ¬ (Signature.ElementOf x y)
infix:40 " ∉ " => NotElementOf


def Nonempty [S : Signature] A := ∃ x, x ∈ A
def Subset [S : Signature] A B := ∀ x, x ∈ A → x ∈ B

infix:50 " ⊆ " => Subset

class ZF extends Signature where
  (extensionality : ∀ A B , (∀ x, x ∈ A ↔ x ∈ B) → A = B)

  (empty : Set)
  (empty_prop : ∀ x, x ∉ empty)

  (pair : Set -> Set -> Set)
  (pair_prop : ∀ A B, (∀ x, x ∈ (pair A B) ↔ (x = A ∨ x = B)))

  (union : Set -> Set)
  (union_prop : ∀ A, (∀ x, x ∈ (union A) ↔ (∃ y, x ∈ y ∧ y ∈ A)))

  (power : Set -> Set)
  (power_prop : ∀ A, (∀ x, x ∈ (power A) ↔ x ⊆ A))

  (comp : Set -> (Set -> Prop) -> Set)
  (comp_prop : ∀ A P, (∀ x, x ∈ (comp A P) ↔ x ∈ A ∧ P x))

variable [ZF : ZF]

-- Utilities
def IsSingleton A := ∃ x, A = ZF.pair x x
theorem singleton_prop : ∀ x, IsSingleton (ZF.pair x x) := by
  intro x
  simp [IsSingleton]
  use x

def union₂ (A B) := ZF.union (ZF.pair A B)
infix:100 " ∪ " => union₂

theorem russell : ¬(∃ S, ∀ A, A ∈ S) := by
  intro ⟨S, hS⟩
  let X := ZF.comp S (fun x ↦ x ∉ x);
  have hX : ∀ x, x ∈ X ↔ x ∉ x := by
    . intro x
      simp [X, ZF.comp_prop, hS x]
  have h := hX X
  tauto

end SetTheory
