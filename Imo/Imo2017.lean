-- theorem problem2 (f : ℝ → ℝ)
--  (h : ∀ x y, (f (f x)*(f y)) + f (x + y) = (f (x*y)))
--  : f 0 = 0 :=
import Mathlib.Tactic

abbrev SolutionSpace := ℝ → ℝ

@[simp]
def constraint (f : SolutionSpace) : Prop :=
  ∀ x y, f (f x * f y) + f (x + y) = f (x * y)

def SolutionSet : Set SolutionSpace := {fun x ↦ 0, fun x ↦ x - 1, fun x ↦ 1 - x}

lemma zero_case (h : f 0 = 0) (hcf : constraint f) : f = fun x ↦ 0 := by
  funext x
  have := hcf x 0
  simpa [h] using this

variable (g : SolutionSpace) (hcg : constraint g) (hzg : g 0 ≠ 0)

lemma zero_apply : g ( g (0) ^ 2) = 0 := by
  have := hcg 0 0
  simp at this
  convert this
  ring

lemma c_eq_one_if_fc_zero (c : ℝ) (h : g c = 0) : c = 1 := by
  by_contra hh
  have c_minus_one_ne_zero : c - 1 ≠ 0 := by
    intro hc_one
    apply hh
    calc c = c - 1 + 1 := by ring
    _ = 1 := by simp [hc_one]
  have h' := hcg (c/(c-1)) c
  have h'' : g 0 = 0 := by calc
    _ = g 0 + g (c/(c-1) + c) - g (c/(c-1) + c) := by simp
    _ = g 0 + g (c/(c-1) + c) - g (c/(c-1) * c) := by
      congr
      field_simp [c_minus_one_ne_zero]
      ring
    _ = g 0 + g (c/(c-1) + c) - (g (g (c / (c - 1)) * g c) + g (c / (c - 1) + c)) := by rw [h']
    _ = g 0 - g (g (c / (c - 1)) * g c) := by simp
    _ = g 0 - g (0) := by congr; simp [h]
    _ = 0 := by simp
  apply hzg
  assumption

lemma zero_mapsto_abs_one : g 0 = 1 ∨ g 0 = -1 := by
  have h := zero_apply g hcg
  have h': g 0 ^ 2 = 1 := c_eq_one_if_fc_zero g hcg hzg (g 0 ^ 2) h
  exact sq_eq_one_iff.mp h'

lemma one_mapsto_zero : g 1 = 0 := by
  have h': g 0 ^ 2 = 1 := by
    rcases zero_mapsto_abs_one g hcg hzg with h' | h'
    rw [h']; simp
    rw [h']; simp
  calc
     g 1 = g (g 0 ^ 2) := by congr; ring; simp [h']
      _ = 0 := zero_apply g hcg
  done

lemma const_symm (hf : constraint f) : constraint (- f) := by
  dsimp [constraint]
  intro x y
  simp
  dsimp [constraint] at hf
  replace hf := hf x y
  rw [← hf]; clear * -
  ring

example : ∀ f : SolutionSpace, constraint f ↔ f ∈ SolutionSet := by
  intro f
  constructor
  intro h
  simp at h
  by_cases h0 : f 0 = 0
  have h' : f = fun x ↦ 0 := zero_case h0 h
  simp [h', SolutionSet]
  have h'' : f ( f (0) ^ 2) = 0 := zero_apply f h
