-- This module serves as the root of the `Math135` library.
-- Import modules here that should be built as part of the library.
import Mathlib.Tactic

import Math135.Basic

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

variable [ZF : ZF]

def union₂ (A B) := ZF.union (ZF.pair A B)
infix:100 " ∪ " => union₂

theorem union₂_prop : ∀ A B, ∀ x, (x ∈ (A ∪ B)) ↔ (x ∈ A ∨ x ∈ B) := by
  intro A B x
  simp only [union₂, ZF.union_prop, ZF.pair_prop]
  constructor
  . rintro ⟨y, hy, rfl | rfl⟩ <;> . simp [*]
  . rintro (h | h)
    . exact ⟨A, h, Or.inl rfl⟩
    . exact ⟨B, h, Or.inr rfl⟩
