import Mathlib.Tactic

abbrev SolutionSpace := ℝ → ℝ

@[simp]
def constraint (f : SolutionSpace) : Prop :=
  ∀ x y, f (f x * f y) + f (x + y) = f (x * y)

def SolutionSet : Set SolutionSpace := {fun _ ↦ 0, fun x ↦ x - 1, fun x ↦ 1 - x}

/-! ## `f 0 = 0` の場合 -/
section
variable {f : SolutionSpace} (h : f 0 = 0)

/-- `f 0 = 0` の場合は， `∀ x, f x = 0`. -/
lemma zero_case (hcf : constraint f) : f = fun x ↦ 0 := by
  funext x
  have := hcf x 0
  simpa [h] using this
end

/-!
## `f 0 ≠ 0` の場合
-/
section
variable {f : SolutionSpace} (hcf : constraint f) (hzf : f 0 ≠ 0)

lemma zero_apply : f ( f (0) ^ 2 ) = 0 := by
  have := hcf 0 0
  simp at this
  convert this
  ring

/-- `f c = 0` ならば， `c = 1`. -/
lemma one_of_zero_f (hc : f c = 0) : c = 1 := by
  contrapose hzf ; simp
  
  have that := hcf (c / (c - 1)) c
  simp [hc] at that
  suffices c / (c - 1) + c = c / (c - 1) * c from by
    rw [this] at that
    simpa using that
  clear that hc

  have : c - 1 ≠ 0 := by 
    contrapose hzf
    simp_all
    linarith
  field_simp
  ring

/-- `f 0 = ± 1` -/
lemma f_zero_pm : f 0 = 1 ∨ f 0 = -1 := by
  set c := f 0 with hc
  have lem := zero_apply hcf
  rw [← hc] at lem
  replace lem := one_of_zero_f (by assumption) (by assumption) lem
  exact sq_eq_one_iff.mp lem

/-- `f 1 = 0` -/
lemma f_one_eq_zero : f 1 = 0 := by
  have := f_zero_pm hcf (by assumption)
  replace : (f 0) ^ 2 = 1 := by 
    rcases this with h | h
    all_goals
      rw [h]
      simp_arith
  have lem := zero_apply hcf
  rwa [this] at lem

lemma const_symm (hf : constraint f) : constraint (- f) := by
  dsimp [constraint]
  intro x y
  simp
  dsimp [constraint] at hf
  replace hf := hf x y
  rw [← hf]; clear * -
  ring

end

/-- 主定理 -/
theorem main : ∀ f : SolutionSpace, constraint f ↔ f ∈ SolutionSet := by
  intro f
  constructor
  focus
    intro h
    simp at h
    by_cases h0 : f 0 = 0
    · have h' : f = fun x ↦ 0 := zero_case h0 h
      simp [h', SolutionSet]
    · have h'' : f ( f (0) ^ 2 ) = 0 := zero_apply h
      sorry
  focus
    sorry
