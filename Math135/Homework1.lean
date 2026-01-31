import Mathlib.Tactic
import Math135.SetTheory

open SetTheory

variable [ZF : ZF]

theorem union₂_prop : ∀ A B, ∀ x, (x ∈ (A ∪ B)) ↔ (x ∈ A ∨ x ∈ B) := by
  intro A B x
  simp only [union₂, ZF.union_prop, ZF.pair_prop]
  constructor
  . rintro ⟨y, hy, rfl | rfl⟩ <;> simp [*]
  . rintro (h | h)
    . exact ⟨A, h, Or.inl rfl⟩
    . exact ⟨B, h, Or.inr rfl⟩

theorem Enderton.«2.3» : ∀ A, ∀ x, x ∈ A → x ⊆ ZF.union A := by
  intro A x h q hq
  simp only [ZF.union_prop]
  use x

theorem Enderton.«2.4» : ∀ A B, A ⊆ B → ZF.union A ⊆ ZF.union B := by
  intro A B h x
  simp only [ZF.union_prop]
  rintro ⟨y, hA⟩
  . unfold SetTheory.Subset at h
    have hB : y ∈ B := h y hA.right
    use y
    exact ⟨hA.left, hB⟩

theorem Enderton.«2.8» : ¬ (∃ S, ∀ x, (IsSingleton x → x ∈ S)) := by
  intro ⟨S, hS⟩
  apply russell ⟨ZF.union S, fun x ↦ ?_⟩
  simp only [ZF.union_prop]
  use ZF.pair x x
  exact ⟨by simp [ZF.pair_prop], hS _ (singleton_prop x)⟩
