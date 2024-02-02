import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Prime

theorem problem3 (k : ℕ) (S: Set ℕ) (fins : Finite S) (hS : ∀ p : ℕ, p ∈ S → (Prime p ∧ Odd p)) :
 1 = 1 := rfl
