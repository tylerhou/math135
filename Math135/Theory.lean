class SetTheory where
  (Set : Type)
  ElementOf : Set -> Set -> Prop

infix:50 " ∈ " => SetTheory.ElementOf
infix:40 " ∉ " => (fun x y => ¬ (SetTheory.ElementOf x y))


def nonempty [S : SetTheory] A := ∃ x, x ∈ A
def subset [S : SetTheory] A B := ∀ x, x ∈ A → x ∈ B

infix:50 " ⊆ " => subset

class ZF extends SetTheory where
  (extensionality : ∀ A B , (∀ x, x ∈ A ↔ x ∈ B) → A = B)

  (empty : Set)
  (empty_prop : ∀ x, x ∉ empty)

  (pair : Set -> Set -> Set)
  (pair_prop : ∀ A B, (∀ x, x ∈ (pair A B) ↔ (x = A ∨ x = B)))

  (union : Set -> Set)
  (union_prop : ∀ A, (∀ x, x ∈ (union A) ↔ (∃ y, x ∈ y ∧ y ∈ A)))
