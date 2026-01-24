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

  def Nonempty (A : Set) : Prop := ∃ (x : Set), x ∈ A
  def SubsetOf (A B : Set) : Prop := ∀ (x : Set), x ∈ A → x ∈ B

  axiom extensionality : ∀ (A B : Set), (∀ (x : Set), x ∈ A ↔ x ∈ B) → A = B

  axiom empty : ∃ (Z : Set), ∀ (x : Set), x ∉ Z
  noncomputable def Empty : Set := Classical.choose empty
  theorem Empty.Defn : ∀ (x : Set), x ∉ Empty := Classical.choose_spec empty

  axiom pairing : ∀ (A B : Set), ∃ (S : Set), (∀ (x : Set), x ∈ S ↔ (x = A ∨ x = B))
  noncomputable def Pair (A B : Set) : Set := Classical.choose (pairing A B)
  theorem Pair.Defn (A B : Set) : (∀ (x : Set), x ∈ Pair A B ↔ (x = A ∨ x = B)) :=
    Classical.choose_spec (pairing A B)

  axiom union : ∀ (A : Set), ∃ (S : Set), (∀ (x : Set), x ∈ S ↔ (∃ (y : Set), x ∈ y ∧ y ∈ A))
  noncomputable def Union (A : Set) : Set := Classical.choose (union A)
  theorem Union.Defn (A : Set) : (∀ (x : Set), x ∈ Union A ↔ (∃ (y : Set), x ∈ y ∧ y ∈ A)) :=
    Classical.choose_spec (union A)


  -- Homework assigned on Fri Jan 23.
  -- I did ask an LLM about syntax / Lean standard library questions.
  -- I hand-wrote all code below. https://gemini.google.com/share/46deb4590f01
  theorem union₂ :
    ∀ (A B : Set), ∃ (S : Set), (∀ (x : Set), x ∈ S ↔ (x ∈ A ∨ x ∈ B)) :=
    (fun (A B : Set) =>
      let P := Pair A B
      Exists.intro (Union P) (fun x => Iff.trans
        -- x ∈ (Union P) ↔ (∃ y, x ∈ y ∧ y ∈ P)
        (Union.Defn P x)
        -- (∃ y, x ∈ y ∧ y ∈ P) ↔ (x ∈ A ∨ x ∈ B)
        (Iff.intro
          -- (∃ y, x ∈ y ∧ y ∈ P) → (x ∈ A ∨ x ∈ B)
          (fun (ey : ∃ y, x ∈ y ∧ y ∈ P) =>
            Exists.elim ey (fun y and =>
              let or := (Pair.Defn A B y).mp and.right
              Or.elim or
                (fun eq_A => Or.inl (Eq.subst eq_A and.left))
                (fun eq_B => Or.inr (Eq.subst eq_B and.left))
            )
          )
          -- (∃ y, x ∈ y ∧ y ∈ P) ← (x ∈ A ∨ x ∈ B)
          (fun or => Or.elim or
            (fun in_A => Exists.intro A (
              And.intro in_A ((Pair.Defn A B A).mpr (Or.inl (Eq.refl A)))
            ))
            (fun in_B => Exists.intro B (
              And.intro in_B ((Pair.Defn A B B).mpr (Or.inr (Eq.refl B)))
            ))
          )
        )
      )
    )
end Set
