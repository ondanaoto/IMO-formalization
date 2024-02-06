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

example : ∀ f : SolutionSpace, constraint f ↔ f ∈ SolutionSet := by
  intro f
  constructor
  intro h
  simp at h
  by_cases h0 : f 0 = 0
  have h' : f = fun x ↦ 0 := zero_case h0 h
  simp [h', SolutionSet]
  have h'' : f ( f (0) ^ 2) = 0 := zero_apply f h
  
