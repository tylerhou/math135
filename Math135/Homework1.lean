import Mathlib.Tactic
import Math135.Theory

variable [ZF : ZF]

def union₂ (A B) := ZF.union (ZF.pair A B)
infix:100 " ∪ " => union₂

theorem union₂_prop : ∀ A B, ∀ x, (x ∈ (A ∪ B)) ↔ (x ∈ A ∨ x ∈ B) := by
  intro A B x
  simp only [union₂, ZF.union_prop, ZF.pair_prop]
  constructor
  . rintro ⟨y, hy, rfl | rfl⟩ <;> simp [*]
  . rintro (h | h)
    . exact ⟨A, h, Or.inl rfl⟩
    . exact ⟨B, h, Or.inr rfl⟩
