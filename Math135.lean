-- This module serves as the root of the `Math135` library.
-- Import modules here that should be built as part of the library.
import Math135.Basic

namespace Set
  -- Basic definitions and theorems from
  -- https://edwardwibowo.com/blog/formalizing-axiomatic-set-theory-in-lean/
  axiom Set : Type

  axiom ElementOf : Set -> Set -> Prop
  infix:50 " ∈ " => ElementOf
  infix:40 " ∉ " => (fun x y => ¬ (ElementOf x y))

  def Nonempty A := ∃ x, x ∈ A
  def SubsetOf A B := ∀ x, x ∈ A → x ∈ B

  axiom extensionality : ∀ A B , (∀ x, x ∈ A ↔ x ∈ B) → A = B

  axiom empty : ∃ Z, ∀ x, x ∉ Z
  noncomputable def Empty := Classical.choose empty
  theorem Empty.Defn : ∀ x, x ∉ Empty := Classical.choose_spec empty

  axiom pairing : ∀ A B, ∃ S, (∀ x, x ∈ S ↔ (x = A ∨ x = B))
  noncomputable def Pair A B := Classical.choose (pairing A B)
  theorem Pair.Defn A B : ∀ x, x ∈ Pair A B ↔ (x = A ∨ x = B) :=
    Classical.choose_spec (pairing A B)

  axiom union : ∀ A , ∃ S, (∀ x, x ∈ S ↔ (∃ y, x ∈ y ∧ y ∈ A))
  noncomputable def Union A := Classical.choose (union A)
  theorem Union.Defn A : (∀ x, x ∈ Union A ↔ (∃ y, x ∈ y ∧ y ∈ A)) :=
    Classical.choose_spec (union A)


 noncomputable def union₂ (A B) := Union (Pair A B)
 theorem Union₂.Prop : ∀ (A B), (∀ x,
  (x ∈ (union₂ A B)) ↔ (x ∈ A ∨ x ∈ B)) := by
  intro A B x
  constructor
  . intro h
    rw [union₂, Union.Defn] at h
    rcases h with ⟨y, l, r⟩
    rw [Pair.Defn] at r
    rcases r with (h | h)
    . rw [h] at l
      exact Or.inl l
    . rw [h] at l
      exact Or.inr l
  . intro h
    rcases h with (h | h)
    . rw [union₂, Union.Defn]
      exists A
      have g : A ∈ Pair A B := by
        rw [Pair.Defn]
        exact Or.inl rfl
      exact ⟨h, g⟩
    . rw [union₂, Union.Defn]
      exists B
      have g : B ∈ Pair A B := by
        rw [Pair.Defn]
        exact Or.inr rfl
      exact ⟨h, g⟩
end Set
